"""
app.py  -  학습도우미 기능팀 통합 앱 (파일 하나)
=====================================================================
탭 2개
  🧭 진로·진학     : 대입 정보 API(대학알리미·입학정원) + 생기부 방향 지도(활동 기록 시각화)
  ⏱️ 타이머·게시판  : 공부 타이머 + 공부 시간 순위 + 꿀팁 게시판

실행:   streamlit run app.py          (이 파일 하나와 requirements.txt 만 있으면 돼요)

로그인
---------------------------------------------------------------------
  학번 + 이름을 한 번만 입력하면 두 탭이 같이 로그인돼요. 학번·이름은 저장하지 않고,
  salt 를 섞은 해시값만 DB 에 둡니다. (형식만 검사해요. 실제 재학생 확인은 메인 앱 로그인의 몫이에요)
  메인 앱에 붙일 때는 아래 ID_SESSION_KEYS 를 메인 앱이 로그인 정보를 담는 session_state 키로 맞추고,
  메인 앱에서 page_career() / page_timer_board() 를 부르면 됩니다. (이 파일의 login 화면은 안 나와요)

Secrets (Manage app → Settings → Secrets, 코드에 직접 적지 마세요)
---------------------------------------------------------------------
  DATA_GO_KR_KEY    = "공공데이터포털 인증키"
  APP_SALT          = "아무 긴 문자열"        # 한 번 정하면 바꾸지 마세요 (STUDY_SALT/CAREER_SALT 도 인식)
  STUDY_ADMIN_CODES = "10101:김철수"          # 게시판 관리자 (학번:이름, 여러 명이면 쉼표) - 관리자는 API 연결 상태도 볼 수 있어요
  APP_DB_PATH       = "study_app.db"          # (선택) DB 파일 위치
  APP_URL_LOGIN     = "1"                     # (선택) 메인 앱이 ?sid=학번&name=이름 으로 넘겨주는 로그인을 허용

개인정보 원칙
---------------------------------------------------------------------
  - 학번·이름은 저장하지 않습니다. 해시값만 둡니다.
  - 활동 기록은 본인만 볼 수 있습니다. (관리자 화면에도 나오지 않아요)
  - 게시판과 순위에는 실명 대신 자동 닉네임만 보입니다.
"""
from __future__ import annotations

import base64
import hashlib
import html
import json
import math
import os
import re
import sqlite3
import time
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from datetime import date, datetime, timedelta, timezone
from urllib import parse as urlparse
from urllib import request as urlrequest

import streamlit as st

# =====================================================================
# 0. 설정
# =====================================================================
# TODO(메인팀과 맞출 곳): 메인 앱 로그인이 정보를 담아두는 session_state 키들.
# 여러 개면 순서대로 값을 합쳐서(예: 학번:이름) 한 사람으로 구분합니다.
ID_SESSION_KEYS = ["student_id", "student_name"]

KST = timezone(timedelta(hours=9))
TRACKS = ["선택 안 함", "인문", "사회", "자연", "공학", "의약", "예체능", "교육"]
MAX_SESSION_SEC = 5 * 3600          # 타이머 1회 최대 인정 시간
MIN_SESSION_SEC = 30                # 너무 짧은 기록은 버림
RANK_LIMIT = 10                     # 랭킹 표시 인원
REPORT_HIDE_THRESHOLD = 3           # 서로 다른 학생 N명이 신고하면 자동 숨김
POST_LIMIT_PER_HOUR = 5
POST_CATEGORIES = ["공부 꿀팁", "학습 정보", "질문"]
REPORT_REASONS = ["욕설·비방", "개인정보 노출", "광고·스팸", "부적절한 내용", "기타"]
BANNED_WORDS: list[str] = []        # 학교 기준에 맞게 채워 넣으세요 (포함되면 등록 거부)

ADJECTIVES = ["졸린", "신난", "느긋한", "반짝이는", "씩씩한", "포근한", "용감한", "엉뚱한"]
ANIMALS = [("판다", "🐼"), ("여우", "🦊"), ("고양이", "🐱"), ("토끼", "🐰"),
           ("곰", "🐻"), ("펭귄", "🐧"), ("수달", "🦦"), ("햄스터", "🐹")]


def _cfg(name: str, default: str = "") -> str:
    """환경변수 -> st.secrets 순으로 설정값을 찾는다."""
    v = os.environ.get(name)
    if isinstance(v, str) and v:
        return v
    try:
        s = st.secrets.get(name)
        if isinstance(s, str) and s:
            return s
    except Exception:
        pass
    return default


def _db_path() -> str:
    return _cfg("APP_DB_PATH") or _cfg("STUDY_DB_PATH") or _cfg("CAREER_DB_PATH") or "study_app.db"


def _salt() -> str:
    return _cfg("APP_SALT") or _cfg("STUDY_SALT") or _cfg("CAREER_SALT") or "change-me-please"


# =====================================================================
# 1. 대입 정보 API 연결 설정  (여기만 채우면 됩니다)
# =====================================================================
# 각 사이트 API를 받으면 아래 항목 하나를 복사해서 값을 채우세요.
#   url            : API 주소 (비워두면 이 소스는 꺼진 상태)
#   key_env        : API 키를 담은 환경변수 이름 / key_param : 키를 보내는 파라미터 이름
#   query_param    : 검색어를 보내는 파라미터 이름
#   fixed_params   : 항상 같이 보내는 값들
#   format         : "json" 또는 "xml" (xml이면 item_tag 지정)
#   list_path      : JSON 응답에서 결과 목록이 있는 경로
#   title_fields / summary_fields / link_fields : 결과 한 건에서 꺼낼 필드 이름(앞에 있는 것 우선)
SOURCES = [
    {   # 한국대학교육협의회 대학알리미 - 대학 기본 정보 (대학 이름으로 검색)
        # 인증키는 환경변수/secrets 의 DATA_GO_KR_KEY 에 넣습니다 (코드에 적지 마세요)
        "name": "대학알리미 대학 기본 정보",
        "home_url": "https://www.academyinfo.go.kr",
        "url": "https://apis.data.go.kr/B340014/BasicInformationService_2/getComparisonUniversitySearchList",
        "key_env": "DATA_GO_KR_KEY",
        "key_param": "serviceKey",
        "query_param": "schlKrnNm",                 # 학교 한글명
        "fixed_params": {"pageNo": "1", "numOfRows": "5", "svyYr": "2024"},   # svyYr: 공시년도
        "format": "xml",
        "item_tag": "item",
        "title_fields": ["schlFullNm", "schlKrnNm"],
        # 예) 국립 · 강원 · 대학교 · 본교
        "summary_template": "{estbDivNm} · {znNm} · {schlKndNm} · {clgcpDivNm}",
        "link_fields": [],
        # 학교번호(schlId)로 그 학교의 대학알리미 공시 페이지로 바로 연결해요
        "link_template": "https://m.academyinfo.go.kr/pubinfo/pubinfo0020/list.do?schlId={schlId}",
        "link_label": "대학알리미에서 공시 보기",
        "max_items": 5,
    },
    {   # 전국대학별입학정원정보표준데이터 (대학 단위 입학정원과 계열별 정원. 학과별 정보는 없어요)
        # 같은 DATA_GO_KR_KEY 를 씁니다. CRTR_YR(기준연도)는 새 자료가 올라오면 바꿔주세요.
        "name": "대학별 입학정원",
        "home_url": "https://www.data.go.kr/data/15107731/standard.do",
        "url": "https://api.data.go.kr/openapi/tn_pubr_public_univ_mtcltn_api",
        "key_env": "DATA_GO_KR_KEY",
        "key_param": "serviceKey",
        "query_param": "SCHL_NM",                   # 학교명
        "fixed_params": {"pageNo": "1", "numOfRows": "5", "type": "xml", "CRTR_YR": "2025"},
        "format": "xml",
        "item_tag": "item",
        "title_fields": ["SCHL_NM"],
        # 값이 없거나 0인 계열은 자동으로 빠집니다. 예) 사립 · 경상북도 · 전문대학 · 본교 · 입학정원 516명 · 인문 24 · 사회 110 ...
        "summary_template": ("{FNDN_SE_NM} · {CTPV_NM} · {SCHL_SE_NM} · {MAIN_BRAN_SCHL_SE_NM} · "
                             "입학정원 {MTCLTN_CNT}명 · 인문 {ACAY_AFIL_MTCLTN_CNT} · 사회 {SOCTY_AFIL_MTCLTN_CNT} · "
                             "교육 {EDU_AFIL_MTCLTN_CNT} · 공학 {ENGR_AFIL_MTCLTN_CNT} · 자연 {SCIEN_AFIL_MTCLTN_CNT} · "
                             "의약 {MDSN_AFIL_MTCLTN_CNT} · 예체능 {ARTAPHY_AFIL_MTCLTN_CNT}"),
        # 계열별 정원 막대그래프용 (앱의 희망 계열 이름 -> API 필드). 진로·진학 지도에서 '내 계열'을 강조해요.
        "detail_total": "MTCLTN_CNT",
        "detail_fields": {"인문": "ACAY_AFIL_MTCLTN_CNT", "사회": "SOCTY_AFIL_MTCLTN_CNT",
                          "교육": "EDU_AFIL_MTCLTN_CNT", "공학": "ENGR_AFIL_MTCLTN_CNT",
                          "자연": "SCIEN_AFIL_MTCLTN_CNT", "의약": "MDSN_AFIL_MTCLTN_CNT",
                          "예체능": "ARTAPHY_AFIL_MTCLTN_CNT"},
        "link_fields": [],
        "max_items": 5,
    },
    {   # 빈 템플릿: url 을 채우면 자동으로 켜집니다.
        "name": "대학 정보 (직접 추가)",
        "home_url": "https://www.academyinfo.go.kr",
        "url": "",
        "key_env": "UNIV_API_KEY",
        "key_param": "serviceKey",
        "query_param": "q",
        "fixed_params": {},
        "format": "json",
        "list_path": [],
        "title_fields": ["title"],
        "summary_fields": ["summary"],
        "link_fields": ["url"],
        "max_items": 5,
    },
]

# API 연결 전에도, 연결 후에도 보여줄 원문 사이트 바로가기
LINKS = [("어디가", "https://www.adiga.kr"), ("커리어넷", "https://www.career.go.kr"),
         ("전공맵", "https://www.majormap.net"), ("대학알리미", "https://www.academyinfo.go.kr")]


# =====================================================================
# 2. 디자인 (토스 느낌 + 귀엽게)
# =====================================================================
CSS = """
<style>
.stApp{background:#F4F6FA;}
.block-container{max-width:560px;padding-top:1.2rem;padding-bottom:4rem;}
.ct-card{background:#fff;border-radius:22px;padding:20px;box-shadow:0 2px 14px rgba(25,31,40,.06);margin-bottom:14px;}
.ct-hero{background:linear-gradient(135deg,#3182F6 0%,#5BA0FF 100%);color:#fff;border-radius:26px;padding:24px;margin-bottom:14px;}
.ct-hero .big{font-size:34px;font-weight:800;line-height:1.1;}
.ct-hero .sub{opacity:.92;font-size:14px;margin-bottom:6px;}
.ct-bar{height:10px;background:#E8EBF0;border-radius:6px;overflow:hidden;margin:8px 0 4px;}
.ct-bar>div{height:100%;background:#3182F6;border-radius:6px;}
.ct-hero .ct-bar{background:rgba(255,255,255,.3);}
.ct-hero .ct-bar>div{background:#fff;}
.ct-chip{display:inline-block;padding:3px 10px;border-radius:99px;font-size:12px;font-weight:700;background:#EAF2FF;color:#3182F6;}
.ct-chip.red{background:#FFEEEF;color:#F04452;}
.ct-chip.mint{background:#E3FBF8;color:#00A99D;}
.ct-chip.gray{background:#F2F4F6;color:#6B7684;}
.ct-muted{color:#8B95A1;font-size:13px;}
.ct-title{font-size:18px;font-weight:800;color:#191F28;}
.ct-row{display:flex;justify-content:space-between;align-items:center;gap:8px;}
.ct-prio{display:flex;gap:10px;align-items:center;padding:5px 0;font-size:14px;}
.ct-prio b{width:22px;height:22px;border-radius:8px;background:#EAF2FF;color:#3182F6;display:flex;align-items:center;justify-content:center;font-size:12px;}
.ct-days{display:flex;gap:6px;justify-content:space-between;margin-top:10px;}
.ct-day{flex:1;text-align:center;font-size:12px;color:#8B95A1;}
.ct-day i{display:block;margin:4px auto 0;width:28px;height:28px;border-radius:50%;background:#E8EBF0;line-height:28px;font-style:normal;}
.ct-day.on i{background:#3182F6;color:#fff;}
.ct-timer{font-size:52px;font-weight:800;text-align:center;color:#191F28;letter-spacing:1px;padding:14px 0;font-variant-numeric:tabular-nums;}
.ct-rank{display:flex;align-items:center;gap:10px;padding:10px 4px;border-bottom:1px solid #F0F1F3;}
.ct-rank.me{background:#EAF2FF;border-radius:14px;padding:10px 12px;}
.ct-rank .no{width:30px;text-align:center;font-weight:800;}
.ct-rank .nm{flex:1;font-weight:600;}
.ct-post-title{font-size:16px;font-weight:700;margin:6px 0;color:#191F28;}
.ct-post-body{white-space:pre-wrap;font-size:14px;line-height:1.6;color:#333D4B;}
.ct-src{font-weight:800;margin:14px 0 6px;color:#191F28;}
.ct-item{padding:10px 0;border-bottom:1px solid #F0F1F3;}
.ct-item:last-child{border-bottom:none;}
div.stButton>button,div[data-testid="stFormSubmitButton"]>button{border-radius:14px;font-weight:700;}
.ct-card{background:#fff;border-radius:22px;padding:20px;box-shadow:0 2px 14px rgba(25,31,40,.06);margin-bottom:14px;}
.ct-hero{background:linear-gradient(135deg,#3182F6 0%,#5BA0FF 100%);color:#fff;border-radius:26px;padding:24px;margin-bottom:14px;}
.ct-hero .big{font-size:34px;font-weight:800;line-height:1.1;}
.ct-hero .sub{opacity:.92;font-size:14px;margin-bottom:6px;}
.ct-bar{height:10px;background:#E8EBF0;border-radius:6px;overflow:hidden;margin:8px 0 4px;}
.ct-bar>div{height:100%;background:#3182F6;border-radius:6px;}
.ct-chip{display:inline-block;padding:3px 10px;border-radius:99px;font-size:12px;font-weight:700;background:#EAF2FF;color:#3182F6;}
.ct-chip.mint{background:#E3FBF8;color:#00A99D;}
.ct-chip.gray{background:#F2F4F6;color:#6B7684;}
.ct-muted{color:#8B95A1;font-size:13px;}
.ct-title{font-size:18px;font-weight:800;color:#191F28;}
.ct-row{display:flex;justify-content:space-between;align-items:center;gap:8px;}
.ct-post-body{white-space:pre-wrap;font-size:14px;line-height:1.6;color:#333D4B;}
.ct-src{font-weight:800;margin:14px 0 6px;color:#191F28;}
.ct-item{padding:10px 0;border-bottom:1px solid #F0F1F3;}
.ct-item:last-child{border-bottom:none;}
.ct-top{display:flex;gap:18px;align-items:center;}
.ct-donut{width:104px;height:104px;border-radius:50%;display:flex;align-items:center;justify-content:center;flex:none;}
.ct-donut>div{width:76px;height:76px;border-radius:50%;background:#fff;display:flex;align-items:center;justify-content:center;font-weight:800;font-size:20px;color:#191F28;}
.ct-hb{display:flex;align-items:center;gap:8px;padding:5px 0;font-size:14px;}
.ct-hb .nm{width:96px;flex:none;font-weight:600;color:#333D4B;}
.ct-hb .tr{flex:1;height:12px;background:#F2F4F6;border-radius:8px;overflow:hidden;}
.ct-hb .tr>i{display:block;height:100%;border-radius:8px;}
.ct-hb .ct{width:28px;text-align:right;font-weight:700;color:#4E5968;}
.ct-tiles{display:grid;grid-template-columns:repeat(5,1fr);gap:8px;margin-top:10px;}
.ct-tile{border-radius:14px;padding:10px 4px;text-align:center;background:#EAF2FF;color:#3182F6;}
.ct-tile b{display:block;font-size:20px;line-height:1.2;}
.ct-tile span{font-size:11px;font-weight:600;}
.ct-tile.empty{background:#fff;border:1.5px dashed #D1D6DB;color:#B0B8C1;}
.ct-months{display:flex;align-items:flex-end;gap:4px;height:116px;margin-top:10px;}
.ct-mcol{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:flex-end;height:100%;}
.ct-mcol .n{font-size:10px;color:#6B7684;height:14px;}
.ct-mcol .st{width:100%;max-width:26px;display:flex;flex-direction:column;justify-content:flex-end;}
.ct-mcol .st i{display:block;width:100%;}
.ct-mcol .lb{font-size:10px;color:#8B95A1;margin-top:4px;white-space:nowrap;}
.ct-legend{display:flex;gap:12px;font-size:12px;color:#6B7684;margin-top:8px;}
.ct-legend i{display:inline-block;width:10px;height:10px;border-radius:3px;margin-right:4px;vertical-align:-1px;}
.ct-flow{display:flex;gap:0;overflow-x:auto;padding:8px 0 4px;}
.ct-node{flex:1 0 62px;text-align:center;position:relative;font-size:11px;color:#4E5968;}
.ct-node:before{content:"";position:absolute;top:9px;left:-50%;width:100%;height:3px;background:#D1D6DB;}
.ct-node:first-child:before{display:none;}
.ct-node i{display:block;position:relative;width:16px;height:16px;border-radius:50%;margin:1px auto 6px;border:3px solid #fff;box-shadow:0 0 0 2px currentColor;background:currentColor;}
.ct-node b{display:block;font-size:11px;color:#191F28;}
</style>
"""


def _esc(x) -> str:
    return html.escape(str(x), quote=True)


def _card(inner_html: str) -> None:
    st.markdown(f'<div class="ct-card">{inner_html}</div>', unsafe_allow_html=True)


def _bar(pct: int) -> str:
    return f'<div class="ct-bar"><div style="width:{max(0, min(100, pct))}%"></div></div>'


# =====================================================================
# 3. 시간 / 포맷 도우미
# =====================================================================
def _now() -> datetime:
    return datetime.now(KST)


def _today() -> date:
    return _now().date()


def _fmt_clock(sec: int) -> str:
    h, r = divmod(int(sec), 3600)
    m, s = divmod(r, 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


def _fmt_dur(sec: int) -> str:
    h, m = int(sec) // 3600, (int(sec) % 3600) // 60
    return f"{h}시간 {m}분" if h else f"{m}분"


def _ago(ts: float) -> str:
    d = time.time() - ts
    if d < 60:
        return "방금 전"
    if d < 3600:
        return f"{int(d // 60)}분 전"
    if d < 86400:
        return f"{int(d // 3600)}시간 전"
    return f"{int(d // 86400)}일 전"


def _dday_text(d: int) -> str:
    return "D-DAY" if d == 0 else f"D-{d}"


# =====================================================================
# 3. DB (사용자·타이머·게시판·활동 기록이 한 파일에 들어가요)
# =====================================================================
_SCHEMA = """
CREATE TABLE IF NOT EXISTS users(
  uid TEXT PRIMARY KEY, nickname TEXT, avatar TEXT,
  track TEXT DEFAULT '', major TEXT DEFAULT '', target_univ TEXT DEFAULT '',
  show_rank INTEGER DEFAULT 1, created_at REAL);
CREATE TABLE IF NOT EXISTS sessions(
  id INTEGER PRIMARY KEY AUTOINCREMENT, uid TEXT, start_ts REAL, end_ts REAL,
  seconds INTEGER DEFAULT 0, day TEXT);
CREATE TABLE IF NOT EXISTS posts(
  id INTEGER PRIMARY KEY AUTOINCREMENT, uid TEXT, category TEXT, title TEXT, body TEXT,
  created_at REAL, hidden INTEGER DEFAULT 0, deleted INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS post_likes(post_id INTEGER, uid TEXT, PRIMARY KEY(post_id, uid));
CREATE TABLE IF NOT EXISTS post_reports(post_id INTEGER, uid TEXT, reason TEXT, PRIMARY KEY(post_id, uid));
CREATE TABLE IF NOT EXISTS activities(
  id INTEGER PRIMARY KEY AUTOINCREMENT, uid TEXT, act_date TEXT, act_type TEXT, title TEXT,
  content TEXT DEFAULT '', role TEXT DEFAULT '', reflection TEXT DEFAULT '', minutes INTEGER,
  subjects TEXT DEFAULT '[]', careers TEXT DEFAULT '[]', created_at REAL);
CREATE INDEX IF NOT EXISTS idx_activities_uid ON activities(uid, act_date);
CREATE INDEX IF NOT EXISTS idx_sessions_day ON sessions(day);
"""
_inited_paths: set = set()


@contextmanager
def _db():
    path = _db_path()
    con = sqlite3.connect(path, timeout=10)
    con.row_factory = sqlite3.Row
    if path not in _inited_paths:
        con.executescript(_SCHEMA)
        _inited_paths.add(path)
    try:
        yield con
        con.commit()
    finally:
        con.close()


# =====================================================================
# 4. 사용자 / 로그인 (학번+이름 -> 해시)
# =====================================================================
def hash_uid(identity: str) -> str:
    """학번·이름 같은 식별값은 저장하지 않고, salt를 섞은 해시만 사용한다."""
    return hashlib.sha256(f"{_salt()}:{str(identity).strip()}".encode("utf-8")).hexdigest()[:32]


def ensure_user(uid: str) -> dict:
    with _db() as con:
        row = con.execute("SELECT * FROM users WHERE uid=?", (uid,)).fetchone()
        if row:
            return dict(row)
        n = int(uid[:8], 16)
        adj = ADJECTIVES[n % len(ADJECTIVES)]
        animal, emoji = ANIMALS[(n // 7) % len(ANIMALS)]
        nick = f"{adj} {animal}{n % 90 + 10}"
        con.execute("INSERT INTO users(uid,nickname,avatar,created_at) VALUES(?,?,?,?)",
                    (uid, nick, emoji, time.time()))
        return dict(con.execute("SELECT * FROM users WHERE uid=?", (uid,)).fetchone())


get_profile = ensure_user      # 진로 탭이 쓰는 이름 (희망 계열·학과·목표 대학도 같은 사용자 표에 저장해요)


_PHONE_RE = re.compile(r"01[016789][-\s.]?\d{3,4}[-\s.]?\d{4}")
_EMAIL_RE = re.compile(r"[\w.+-]+@[\w-]+\.[\w.]+")


def _has_pii(text: str) -> bool:
    return bool(_PHONE_RE.search(text) or _EMAIL_RE.search(text))


def _has_banned(text: str) -> bool:
    return any(w and w in text for w in BANNED_WORDS)


def update_nickname(uid: str, nickname: str) -> tuple[bool, str]:
    nickname = nickname.strip()
    if not 2 <= len(nickname) <= 12:
        return False, "닉네임은 2~12자로 정해주세요."
    if _has_pii(nickname) or _has_banned(nickname):
        return False, "사용할 수 없는 닉네임이에요."
    with _db() as con:
        con.execute("UPDATE users SET nickname=? WHERE uid=?", (nickname, uid))
    return True, "닉네임을 바꿨어요."


def update_profile(uid: str, track: str, major: str, univ: str) -> None:
    with _db() as con:
        con.execute("UPDATE users SET track=?, major=?, target_univ=? WHERE uid=?",
                    (track[:20] if track in TRACKS[1:] else "", major.strip()[:40], univ.strip()[:40], uid))


def set_show_rank(uid: str, show: bool) -> None:
    with _db() as con:
        con.execute("UPDATE users SET show_rank=? WHERE uid=?", (1 if show else 0, uid))


def _identity():
    """메인 앱이 session_state 에 담아둔 값들을 합쳐 한 사람의 식별값으로 쓴다."""
    parts = []
    for k in ID_SESSION_KEYS:
        v = st.session_state.get(k)
        if not isinstance(v, (str, int)) or not str(v).strip():
            return None
        parts.append(str(v).strip())
    return ":".join(parts) if parts else None


STUDENT_ID_RE = re.compile(r"^[1-3](0[1-9]|[1-9]\d)(0[1-9]|[1-9]\d)$")   # 학년(1~3) + 반(2자리) + 번호(2자리)
NAME_RE = re.compile(r"^[가-힣]{2,5}$")


def check_login_input(student_id, name):
    """단독 실행 로그인 입력 검사. 문제가 없으면 None, 있으면 안내 문구를 돌려준다.
    (형식만 확인해요. 실제 재학생인지는 메인 앱 로그인이 확인하는 부분이에요.)"""
    if not STUDENT_ID_RE.match(str(student_id).strip()):
        return "학번을 숫자 5자리로 다시 입력해 주세요. 첫 숫자는 학년(1~3)이에요. 예: 20301"
    if not NAME_RE.match(str(name).strip()):
        return "이름은 한글 2~5자로 입력해 주세요."
    return None


def _query_param(name: str) -> str:
    try:
        v = st.query_params.get(name, "")
        if isinstance(v, (list, tuple)):
            v = v[0] if v else ""
        return str(v or "").strip()
    except Exception:
        return ""


def _login_from_url() -> None:
    """APP_URL_LOGIN=1 일 때만: 메인 앱이 주소(?sid=학번&name=이름)로 넘겨준 값으로 로그인한다.
    ※ 주소를 아는 사람은 누구나 그 학번으로 들어올 수 있어요. 메인 앱 로그인(학번+이름)과 같은 수준이에요.
       더 안전하게 하려면 Firebase 로그인 토큰을 서버에서 검증하는 방식으로 바꿔야 해요."""
    if (_cfg("APP_URL_LOGIN") or _cfg("CAREER_URL_LOGIN")) != "1" or _identity() or len(ID_SESSION_KEYS) != 2:
        return
    sid, nm = _query_param("sid"), _query_param("name")
    if sid and nm and check_login_input(sid, nm) is None:
        st.session_state[ID_SESSION_KEYS[0]] = sid
        st.session_state[ID_SESSION_KEYS[1]] = nm


def _login_gate():
    """로그인한 사용자(없으면 None). 관리자 여부(is_admin)도 같이 알려준다."""
    ident = _identity()
    if not ident:
        return None
    user = ensure_user(hash_uid(ident))
    admins = [c.strip() for c in _cfg("STUDY_ADMIN_CODES").split(",") if c.strip()]
    user["is_admin"] = ident in admins
    return user


def _flash(msg: str) -> None:
    st.session_state["sf_flash"] = msg


def _show_flash() -> None:
    msg = st.session_state.pop("sf_flash", None)
    if msg:
        st.toast(msg)

def _page_start():
    """각 탭의 시작: 스타일, 로그인 확인, 알림 토스트."""
    st.markdown(CSS, unsafe_allow_html=True)
    _login_from_url()
    user = _login_gate()
    if not user:
        st.info("로그인하면 사용할 수 있어요 🙂")
        return None
    st.session_state["ct_dev_mode"] = bool(user["is_admin"]) or _cfg("APP_DEV") == "1"   # 관리자에게만 API 연결 상태를 보여줘요
    _show_flash()
    return user


# =====================================================================
# 7. 타이머 / 랭킹 로직
# =====================================================================
def active_session(uid: str):
    with _db() as con:
        row = con.execute("SELECT * FROM sessions WHERE uid=? AND end_ts IS NULL ORDER BY id DESC LIMIT 1",
                          (uid,)).fetchone()
    return dict(row) if row else None


def start_session(uid: str) -> bool:
    if active_session(uid):
        return False
    with _db() as con:
        con.execute("INSERT INTO sessions(uid,start_ts,day) VALUES(?,?,?)",
                    (uid, time.time(), _today().isoformat()))
    return True


def stop_session(uid: str) -> int:
    row = active_session(uid)
    if not row:
        return 0
    now = time.time()
    sec = min(int(now - row["start_ts"]), MAX_SESSION_SEC)
    with _db() as con:
        if sec < MIN_SESSION_SEC:
            con.execute("DELETE FROM sessions WHERE id=?", (row["id"],))
            return 0
        con.execute("UPDATE sessions SET end_ts=?, seconds=? WHERE id=?", (now, sec, row["id"]))
    return sec


def totals(start_day: date, end_day: date) -> dict:
    """기간 내 학생별 공부 시간(초). 진행 중인 세션도 현재까지 반영."""
    now = time.time()
    with _db() as con:
        rows = con.execute(
            "SELECT s.uid, s.start_ts, s.end_ts, s.seconds, u.nickname, u.avatar, u.show_rank "
            "FROM sessions s JOIN users u ON u.uid=s.uid WHERE s.day>=? AND s.day<=?",
            (start_day.isoformat(), end_day.isoformat())).fetchall()
    out: dict = {}
    for r in rows:
        sec = r["seconds"] if r["end_ts"] else min(int(now - r["start_ts"]), MAX_SESSION_SEC)
        e = out.setdefault(r["uid"], {"uid": r["uid"], "sec": 0, "nickname": r["nickname"],
                                      "avatar": r["avatar"], "show": bool(r["show_rank"])})
        e["sec"] += max(sec, 0)
    return out


def ranking(start_day: date, end_day: date, uid: str) -> dict:
    tot = totals(start_day, end_day)
    public = sorted((e for e in tot.values() if e["show"]), key=lambda e: -e["sec"])
    me_sec = tot[uid]["sec"] if uid in tot else 0
    my_rank = next((i + 1 for i, e in enumerate(public) if e["uid"] == uid), None)
    return {"top": public[:RANK_LIMIT], "my_rank": my_rank, "my_sec": me_sec, "count": len(public)}


# =====================================================================
# 8. 게시판 로직
# =====================================================================
def create_post(uid: str, category: str, title: str, body: str) -> tuple[bool, str]:
    title, body = title.strip(), body.strip()
    if category not in POST_CATEGORIES:
        return False, "카테고리를 골라주세요."
    if not 2 <= len(title) <= 40:
        return False, "제목은 2~40자로 써주세요."
    if not 5 <= len(body) <= 1000:
        return False, "내용은 5~1000자로 써주세요."
    if _has_pii(title + body):
        return False, "전화번호·이메일 같은 개인정보는 올릴 수 없어요."
    if _has_banned(title + body):
        return False, "사용할 수 없는 표현이 들어 있어요."
    with _db() as con:
        recent = con.execute("SELECT COUNT(*) FROM posts WHERE uid=? AND created_at>?",
                             (uid, time.time() - 3600)).fetchone()[0]
        if recent >= POST_LIMIT_PER_HOUR:
            return False, "한 시간에 올릴 수 있는 글 수를 넘었어요. 잠시 후 다시 해주세요."
        con.execute("INSERT INTO posts(uid,category,title,body,created_at) VALUES(?,?,?,?,?)",
                    (uid, category, title, body, time.time()))
    return True, "글을 올렸어요!"


def list_posts(uid: str, category: str | None = None, sort: str = "최신", limit: int = 30) -> list[dict]:
    order = "likes DESC, p.created_at DESC" if sort == "인기" else "p.created_at DESC"
    sql = ("SELECT p.*, u.nickname, u.avatar, "
           "(SELECT COUNT(*) FROM post_likes l WHERE l.post_id=p.id) AS likes, "
           "(SELECT COUNT(*) FROM post_likes l WHERE l.post_id=p.id AND l.uid=?) AS liked "
           "FROM posts p JOIN users u ON u.uid=p.uid WHERE p.hidden=0 AND p.deleted=0 ")
    args: list = [uid]
    if category and category != "전체":
        sql += "AND p.category=? "
        args.append(category)
    sql += f"ORDER BY {order} LIMIT ?"
    args.append(limit)
    with _db() as con:
        return [dict(r) for r in con.execute(sql, args)]


def toggle_like(uid: str, post_id: int) -> None:
    with _db() as con:
        if con.execute("SELECT 1 FROM post_likes WHERE post_id=? AND uid=?", (post_id, uid)).fetchone():
            con.execute("DELETE FROM post_likes WHERE post_id=? AND uid=?", (post_id, uid))
        else:
            con.execute("INSERT INTO post_likes(post_id,uid) VALUES(?,?)", (post_id, uid))


def report_post(uid: str, post_id: int, reason: str) -> str:
    with _db() as con:
        post = con.execute("SELECT uid FROM posts WHERE id=?", (post_id,)).fetchone()
        if not post or post["uid"] == uid:
            return "신고할 수 없는 글이에요."
        con.execute("INSERT OR IGNORE INTO post_reports(post_id,uid,reason) VALUES(?,?,?)",
                    (post_id, uid, reason))
        n = con.execute("SELECT COUNT(*) FROM post_reports WHERE post_id=?", (post_id,)).fetchone()[0]
        if n >= REPORT_HIDE_THRESHOLD:
            con.execute("UPDATE posts SET hidden=1 WHERE id=?", (post_id,))
    return "신고가 접수됐어요. 확인 후 조치할게요."


def delete_post(uid: str, post_id: int, is_admin: bool = False) -> None:
    with _db() as con:
        if is_admin:
            con.execute("UPDATE posts SET deleted=1 WHERE id=?", (post_id,))
        else:
            con.execute("UPDATE posts SET deleted=1 WHERE id=? AND uid=?", (post_id, uid))


def hidden_posts() -> list[dict]:
    with _db() as con:
        return [dict(r) for r in con.execute(
            "SELECT p.*, u.nickname, "
            "(SELECT COUNT(*) FROM post_reports r WHERE r.post_id=p.id) AS reports "
            "FROM posts p JOIN users u ON u.uid=p.uid WHERE p.hidden=1 AND p.deleted=0 ORDER BY p.created_at DESC")]


def restore_post(post_id: int) -> None:
    with _db() as con:
        con.execute("UPDATE posts SET hidden=0 WHERE id=?", (post_id,))
        con.execute("DELETE FROM post_reports WHERE post_id=?", (post_id,))


# =====================================================================
# 5. 대입 정보 조회 (API 어댑터)
# =====================================================================
_CACHE: dict = {}
_CACHE_TTL = 3600
_TAG_RE = re.compile(r"<[^>]+>")


def _dig(obj, path):
    for k in path:
        if isinstance(obj, dict):
            obj = obj.get(k)
        elif isinstance(obj, list) and isinstance(k, int) and 0 <= k < len(obj):
            obj = obj[k]
        else:
            return None
    return obj


def _norm_key(k) -> str:
    """SCHL_NM, schlNm, schl_nm 처럼 쓰는 방식이 달라도 같은 이름으로 본다."""
    return re.sub(r"[^a-z0-9]", "", str(k).lower())


def _get(item: dict, name: str):
    if not isinstance(item, dict):
        return None
    if name in item:
        return item[name]
    want = _norm_key(name)
    for k, v in item.items():
        if _norm_key(k) == want:
            return v
    return None


def _pick(item: dict, fields: list[str]) -> str:
    for f in fields:
        v = _get(item, f)
        if v not in (None, ""):
            return _TAG_RE.sub("", str(v)).strip()
    return ""


def _xml_items(text: str, tag: str) -> list[dict]:
    root = ET.fromstring(text)
    return [{c.tag: (c.text or "").strip() for c in el} for el in root.iter(tag)]


def _parse_items(text: str, src: dict) -> list[dict]:
    if src.get("format", "json") == "xml":
        raw = _xml_items(text, src.get("item_tag", "item"))
    else:
        node = _dig(json.loads(text), src.get("list_path", []))
        raw = node if isinstance(node, list) else ([node] if isinstance(node, dict) else [])
    home = src.get("home_url", "")
    out = []
    for it in raw[: src.get("max_items", 5)]:
        title = _pick(it, src.get("title_fields", ["title"]))
        if not title:
            continue
        link = _pick(it, src.get("link_fields", []))
        if not link and src.get("link_template"):
            names = re.findall(r"\{(\w+)\}", src["link_template"])
            vals = {nm: _pick(it, [nm]) for nm in names}
            if names and all(vals.values()):
                link = re.sub(r"\{(\w+)\}", lambda m: urlparse.quote(vals[m.group(1)], safe=""), src["link_template"])
        if src.get("summary_template"):
            # 여러 항목을 한 줄로 합친다. '·' 로 나눈 조각 중 값이 비었거나 0인 항목이 들어 있는 조각은 뺀다.
            vals = []
            for p in (x.strip() for x in src["summary_template"].split("·")):
                names = re.findall(r"\{(\w+)\}", p)
                got = [_TAG_RE.sub("", str(_get(it, nm) or "")).strip() for nm in names]
                if names and any(g in ("", "0") for g in got):
                    continue
                vals.append(re.sub(r"\{(\w+)\}",
                                   lambda m: _TAG_RE.sub("", str(_get(it, m.group(1)) or "")).strip(), p))
            summary = " · ".join(v for v in vals if v)
        else:
            summary = _pick(it, src.get("summary_fields", []))
        entry = {"title": title[:80],
                 "summary": summary[:160],   # 요약 일부만 (원문은 출처에서)
                 "url": link if link.startswith(("http://", "https://")) else home,
                 "link_label": src.get("link_label", "")}
        if src.get("detail_fields"):
            entry["detail"] = {k: _to_int(_get(it, f)) for k, f in src["detail_fields"].items()}
            entry["total"] = _to_int(_get(it, src.get("detail_total", "")))
        out.append(entry)
    return out


def _to_int(v) -> int:
    try:
        return max(0, int(float(str(v).replace(",", "").strip())))
    except (TypeError, ValueError):
        return 0


def track_share(detail: dict, total: int, track: str):
    """희망 계열의 정원과 전체 대비 비율. 값이 없으면 None."""
    n = (detail or {}).get(track, 0)
    if not n or not total:
        return None
    return n, round(n * 100 / total)


def fetch_source(src: dict, key: str, query: str) -> dict:
    res = {"source": src["name"], "home": src.get("home_url", ""), "status": "ok", "items": [], "reason": ""}
    if not src.get("url"):
        res["status"] = "off"
        return res
    if src.get("key_param") and not key:
        res["status"] = "no_key"
        res["reason"] = f"인증키가 비어 있어요 ({src.get('key_env', '')})"
        return res
    params = dict(src.get("fixed_params", {}))
    params[src["query_param"]] = query
    if src.get("key_param"):
        # 공공데이터포털의 '인코딩 키'(%2B 등이 들어 있는 키)를 그대로 넣어도 두 번 인코딩되지 않게 풀어준다
        params[src["key_param"]] = urlparse.unquote(key)
    url = src["url"] + ("&" if "?" in src["url"] else "?") + urlparse.urlencode(params)
    try:
        req = urlrequest.Request(url, headers={"User-Agent": "study-helper/1.0"})
        with urlrequest.urlopen(req, timeout=6) as r:
            text = r.read().decode(src.get("encoding", "utf-8"), "replace")
        if src.get("format") == "xml":
            # 공공데이터포털은 키 오류 같은 문제도 XML 로 돌려준다 (resultCode 00 이 정상)
            root = ET.fromstring(text)
            code = root.findtext(".//resultCode")
            if code is not None and code.strip() not in ("00", "0", "000"):
                res["status"] = "error"
                res["reason"] = f"resultCode {code.strip()} {(root.findtext('.//resultMsg') or '').strip()}"[:80]
                return res
            # 키가 등록되지 않았거나 승인 전일 때 게이트웨이가 돌려주는 형식
            gate = root.findtext(".//returnAuthMsg") or root.findtext(".//errMsg")
            if gate and root.find(".//item") is None:
                res["status"] = "error"
                res["reason"] = f"게이트웨이 응답: {gate.strip()}"[:80]
                return res
        res["items"] = _parse_items(text, src)
    except urlrequest.HTTPError as e:      # 키가 담긴 주소가 화면에 나오지 않도록 내용은 숨긴다
        res["status"], res["items"], res["reason"] = "error", [], f"HTTP {e.code}"
    except urlrequest.URLError:
        res["status"], res["items"], res["reason"] = "error", [], "서버에 접속하지 못했어요(시간 초과 포함)"
    except Exception:
        res["status"], res["items"], res["reason"] = "error", [], "응답을 읽지 못했어요"
    return res


def search_all(query: str, sources: list[dict] | None = None) -> list[dict]:
    q = query.strip()[:60]
    if not q:
        return []
    sources = SOURCES if sources is None else sources
    jobs = [(s, _cfg(s.get("key_env", "")) if s.get("key_env") else "") for s in sources]   # 키는 메인 스레드에서 읽기

    def run(job):
        s, key = job
        ck = (s["name"], q)
        hit = _CACHE.get(ck)
        if hit and time.time() - hit[0] < _CACHE_TTL:
            return hit[1]
        r = fetch_source(s, key, q)
        if r["status"] == "ok":
            _CACHE[ck] = (time.time(), r)
        return r

    if not jobs:
        return []
    with ThreadPoolExecutor(max_workers=len(jobs)) as ex:
        return list(ex.map(run, jobs))


# =====================================================================
# 6. 희망 진로와 교과를 잇는 기준 (활동을 '이어서 보는' 데에만 써요)
#   ※ 대학·학과마다 다릅니다. 팀에서 공식 자료를 보고 자유롭게 고쳐 쓰세요.
# =====================================================================
LEVELS = {"핵심": 1.3, "중요": 1.15, "참고": 1.0}
LEVEL_ORDER = ["핵심", "중요", "참고"]

# 과목 이름에 아래 글자가 들어 있으면 그 분류로 본다 (분류에 없으면 '참고' 취급)
SUBJECT_GROUPS = {
    "수학": ["수학", "미적분", "기하", "확률", "대수"],
    "과학": ["과학", "물리", "화학", "생명", "지구"],
    "국어": ["국어", "문학", "독서", "화법", "언어"],
    "영어": ["영어"],
    "사회": ["사회", "역사", "한국사", "세계사", "동아시아사", "지리", "윤리", "경제", "정치"],
}

# 계열별 '시험 과목 분류' 우선순위 (희망 계열에서 비중이 큰 과목일수록 시험 우선순위가 올라가요)
TRACK_GROUP_LEVEL = {
    "공학": {"수학": "핵심", "과학": "핵심", "영어": "중요"},
    "자연": {"수학": "핵심", "과학": "핵심", "영어": "중요"},
    "의약": {"과학": "핵심", "수학": "중요", "영어": "중요"},
    "인문": {"국어": "핵심", "영어": "핵심", "사회": "중요"},
    "사회": {"국어": "핵심", "영어": "핵심", "수학": "중요", "사회": "중요"},
    "교육": {},
    "예체능": {"국어": "중요", "영어": "중요"},
}

# 계열별 일반 선택과목 가이드: (과목, 단계, 이유)
# ※ 대학·학과·학년도마다 다릅니다. 팀에서 공식 자료로 확인해 고쳐 쓰세요.
TRACK_ELECTIVES = {
    "공학": [("미적분Ⅱ", "핵심", "공학 전공 수학의 바탕이 되는 과목이에요"),
           ("물리학", "핵심", "공학 전공의 기초 과학 과목이에요"),
           ("기하", "중요", "공간·벡터 개념이 전공 수학과 물리에서 자주 쓰여요"),
           ("화학", "중요", "재료·에너지 분야에서 기초가 돼요")],
    "자연": [("미적분Ⅱ", "핵심", "자연과학 전공 수학의 바탕이 돼요"),
           ("희망 학과와 가까운 과학 과목(물리학·화학·생명과학·지구과학)", "핵심",
            "전공과 가장 가까운 과학 과목을 깊게 배워두면 좋아요"),
           ("기하", "중요", "수학 심화 개념을 넓혀줘요")],
    "의약": [("생명과학", "핵심", "의약 계열에서 자주 필요한 과학 과목이에요"),
           ("화학", "핵심", "의약 계열에서 자주 필요한 과학 과목이에요"),
           ("미적분Ⅱ", "중요", "일부 대학은 수학 선택과목을 지정해요"),
           ("물리학", "참고", "대학에 따라 포함돼요")],
    "인문": [("문학", "핵심", "국어·인문 계열 학업의 바탕이에요"),
           ("영어Ⅱ", "핵심", "인문 계열에서 영어 독해력이 꾸준히 쓰여요"),
           ("독서와 작문", "중요", "읽고 쓰는 힘을 키워줘요"),
           ("사회·역사 탐구 과목", "중요", "인문사회 전공의 배경지식이 돼요")],
    "사회": [("영어Ⅱ", "핵심", "사회 계열에서 영어 독해력이 꾸준히 쓰여요"),
           ("사회·경제 탐구 과목(경제, 정치와 법, 사회와 문화 등)", "핵심", "전공과 가까운 사회 과목이에요"),
           ("확률과 통계", "중요", "사회과학 전공에서 통계를 자주 써요"),
           ("문학", "중요", "국어 역량의 바탕이에요")],
    "교육": [("희망 교과와 이어지는 심화 과목", "핵심", "교과교육 전공은 희망 교과와의 연결이 중요해요"),
           ("국어·영어·수학 기본 과목", "중요", "교직의 기초 학력이에요")],
    "예체능": [("전공과 이어지는 실기·이론 과목", "핵심", "전공과 직접 이어지는 과목이에요"),
            ("국어·영어", "중요", "기본 학업 역량이에요")],
}

# 학과 이름에 키워드가 들어 있으면: (키워드들, 계열 힌트, 분류별 우선순위, 추가 선택과목)
MAJOR_RULES = [
    (("영어", "영문"), "인문", {"영어": "핵심"},
     [("영어 독해와 작문", "핵심", "영어 관련 학과는 읽기·쓰기 역량이 바탕이에요"),
      ("영어 발표와 토론", "중요", "말하기 역량을 키워줘요")]),
    (("국어", "국문", "문예"), "인문", {"국어": "핵심"},
     [("문학", "핵심", "국어 관련 학과의 바탕이에요"), ("독서와 작문", "핵심", "읽고 쓰는 힘을 키워줘요")]),
    (("수학", "통계", "수리"), "자연", {"수학": "핵심"},
     [("미적분Ⅱ", "핵심", "수학 계열의 바탕이에요"), ("확률과 통계", "중요", "통계·데이터 분야에서 쓰여요")]),
    (("컴퓨터", "소프트웨어", "인공지능", "ai", "데이터"), "공학", {"수학": "핵심"},
     [("정보", "핵심", "컴퓨터 계열의 기초 과목이에요"), ("미적분Ⅱ", "핵심", "알고리즘·AI의 수학적 바탕이에요")]),
    (("전기", "전자", "반도체", "물리학", "기계", "항공", "로봇"), "공학", {"수학": "핵심", "과학": "핵심"},
     [("물리학", "핵심", "전기·전자·기계 분야는 물리 개념을 많이 써요")]),
    (("화학", "화공", "신소재", "재료"), "공학", {"과학": "핵심"},
     [("화학", "핵심", "화학·재료 분야의 바탕이에요")]),
    (("생명", "바이오", "의학", "의예", "약학", "간호", "치의", "수의", "한의"), "의약", {"과학": "핵심"},
     [("생명과학", "핵심", "생명·의약 분야의 바탕이에요")]),
    (("경제", "경영", "무역", "회계"), "사회", {"수학": "중요"},
     [("확률과 통계", "핵심", "경제·경영 계열은 통계를 많이 써요"), ("경제", "중요", "전공 배경지식이 돼요")]),
]

def subject_group(name: str):
    for g, kws in SUBJECT_GROUPS.items():
        if any(k in name for k in kws):
            return g
    return None


def resolve_guide(track: str, major: str) -> dict:
    """희망 계열·학과로 선택과목 가이드와 과목 분류별 우선순위를 만든다."""
    m = (major or "").strip().lower()
    matched = [r for r in MAJOR_RULES if any(k in m for k in r[0])]
    eff = track if track in TRACK_ELECTIVES else (matched[0][1] if matched else "")
    levels = dict(TRACK_GROUP_LEVEL.get(eff, {}))
    for r in matched:
        for g, lv in r[2].items():            # 학과 규칙이 더 높은 단계면 그걸 따른다
            if g not in levels or LEVEL_ORDER.index(lv) < LEVEL_ORDER.index(levels[g]):
                levels[g] = lv
    merged: dict = {}
    for subj, lv, why in [*TRACK_ELECTIVES.get(eff, []), *[e for r in matched for e in r[3]]]:
        if subj not in merged or LEVEL_ORDER.index(lv) < LEVEL_ORDER.index(merged[subj][0]):
            merged[subj] = (lv, why)
    items = sorted(({"subject": s, "level": v[0], "reason": v[1]} for s, v in merged.items()),
                   key=lambda x: LEVEL_ORDER.index(x["level"]))
    return {"track": eff, "group_levels": levels, "items": items}


# =====================================================================
# 7. 활동 기록 + 생기부 방향 정리 로직
#   원칙: 학생이 직접 적은 기록을 '정리해서 보여주기'까지만 한다.
#         생활기록부 평가, 합격 가능성, 좋고 나쁨은 판단하지 않는다.
# =====================================================================
ACTIVITY_TYPES = ["교과 발표", "수행평가", "특강", "동아리", "독서", "탐구", "대회", "진로 활동", "봉사", "기타"]
ACTIVITY_SUBJECTS = ["국어", "수학", "영어", "사회", "과학", "정보", "예체능", "기타"]
CAREER_TAGS = ["공학", "컴퓨터·AI", "자연과학", "의약·보건", "인문·언어", "사회·경영", "교육", "미디어", "예체능",
               "환경", "기타"]
TRACK_TO_TAG = {"공학": "공학", "자연": "자연과학", "의약": "의약·보건", "인문": "인문·언어", "사회": "사회·경영",
                "교육": "교육", "예체능": "예체능"}
# 희망 학과 이름에 아래 글자가 들어 있으면 그 진로 태그와 연결해서 본다 (팀에서 자유롭게 고쳐 쓰세요)
MAJOR_TAG_KEYWORDS = {
    "공학": ("공학", "전기", "전자", "기계", "반도체", "항공", "로봇", "신소재", "화공", "건축", "토목"),
    "컴퓨터·AI": ("컴퓨터", "소프트웨어", "인공지능", "ai", "데이터", "정보"),
    "자연과학": ("물리", "화학", "수학", "통계", "지구", "천문", "생명과학"),
    "의약·보건": ("의학", "의예", "약학", "간호", "치의", "수의", "한의", "보건", "생명"),
    "인문·언어": ("영어", "영문", "국어", "국문", "문예", "언어", "문학", "철학", "사학", "역사"),
    "사회·경영": ("경제", "경영", "무역", "회계", "행정", "법학", "정치", "사회", "심리"),
    "교육": ("교육", "사범", "교사"),
    "미디어": ("미디어", "방송", "언론", "신문", "영상", "광고"),
    "환경": ("환경", "에너지", "기후"),
}
MAX_ACTIVITIES = 300


def goal_tags(track: str, major: str) -> list[str]:
    """희망 계열·학과에서 '이어서 볼 진로 태그'를 뽑는다."""
    tags = []
    t = TRACK_TO_TAG.get(track)
    if t:
        tags.append(t)
    m = (major or "").lower()
    for tag, kws in MAJOR_TAG_KEYWORDS.items():
        if tag not in tags and any(k in m for k in kws):
            tags.append(tag)
    return tags


def goal_subject_groups(track: str, major: str) -> set:
    """희망 계열·학과에서 '이어서 볼 교과 분류'(국어·수학·과학 …)를 뽑는다."""
    g = resolve_guide(track, major)
    groups = {k for k, lv in g["group_levels"].items() if lv in ("핵심", "중요")}
    for it in g["items"]:
        if it["level"] != "참고":
            grp = subject_group(it["subject"])
            if grp:
                groups.add(grp)
            if "정보" in it["subject"]:
                groups.add("정보")
    return groups


def add_activity(uid: str, act_date, act_type: str, title: str, content: str = "", role: str = "",
                 reflection: str = "", minutes=None, subjects=None, careers=None) -> tuple[bool, str]:
    title, content, role, reflection = title.strip(), content.strip(), role.strip(), reflection.strip()
    try:
        d = date.fromisoformat(str(act_date))
    except ValueError:
        return False, "날짜를 확인해주세요."
    if d > _today():
        return False, "아직 오지 않은 날짜는 기록할 수 없어요."
    if act_type not in ACTIVITY_TYPES:
        return False, "활동 유형을 골라주세요."
    if not 2 <= len(title) <= 40:
        return False, "제목은 2~40자로 써주세요."
    if len(content) > 500 or len(reflection) > 500:
        return False, "내용과 느낀 점은 각각 500자까지 쓸 수 있어요."
    if len(role) > 40:
        return False, "역할은 40자까지 쓸 수 있어요."
    try:
        minutes = int(minutes) if minutes not in (None, "") else None
    except (TypeError, ValueError):
        minutes = None
    if minutes is not None and not 0 < minutes <= 1440:
        minutes = None
    subs = [s for s in (subjects or []) if s in ACTIVITY_SUBJECTS]
    cars = [c for c in (careers or []) if c in CAREER_TAGS]
    with _db() as con:
        if con.execute("SELECT COUNT(*) FROM activities WHERE uid=?", (uid,)).fetchone()[0] >= MAX_ACTIVITIES:
            return False, "기록은 300개까지 저장할 수 있어요. 오래된 기록을 정리해주세요."
        con.execute("INSERT INTO activities(uid,act_date,act_type,title,content,role,reflection,minutes,"
                    "subjects,careers,created_at) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                    (uid, d.isoformat(), act_type, title, content, role, reflection, minutes,
                     json.dumps(subs, ensure_ascii=False), json.dumps(cars, ensure_ascii=False), time.time()))
    return True, "활동을 기록했어요!"


def list_activities(uid: str) -> list[dict]:
    with _db() as con:
        rows = con.execute("SELECT * FROM activities WHERE uid=? ORDER BY act_date DESC, id DESC", (uid,)).fetchall()
    out = []
    for r in rows:
        a = dict(r)
        a["subjects"] = json.loads(a["subjects"] or "[]")
        a["careers"] = json.loads(a["careers"] or "[]")
        out.append(a)
    return out


def delete_activity(uid: str, activity_id: int) -> None:
    with _db() as con:
        con.execute("DELETE FROM activities WHERE id=? AND uid=?", (activity_id, uid))


VIEW_KINDS = ["전체", "활동 유형", "진로", "교과"]
_VIEW_ORDER = {"활동 유형": ACTIVITY_TYPES, "진로": CAREER_TAGS, "교과": ACTIVITY_SUBJECTS}


def _act_values(a: dict, kind: str) -> list:
    return {"활동 유형": [a["act_type"]], "진로": a["careers"], "교과": a["subjects"]}.get(kind, [])


def category_counts(acts: list[dict], kind: str) -> dict:
    """분류(활동 유형·진로·교과)별 기록 수. 기록이 있는 분류만, 정해진 순서대로."""
    cnt = Counter(v for a in acts for v in _act_values(a, kind))
    return {v: cnt[v] for v in _VIEW_ORDER.get(kind, []) if cnt[v]}


def filter_activities(acts: list[dict], kind: str = "전체", value=None, order: str = "최신순") -> list[dict]:
    """고른 분류의 기록만 날짜순으로 정렬해서 돌려준다. kind 가 '전체'이면 모두."""
    out = [a for a in acts if kind == "전체" or value in _act_values(a, kind)]
    return sorted(out, key=lambda a: (a["act_date"], a["id"]), reverse=(order != "오래된순"))


def guidance_summary(uid: str, track: str, major: str) -> dict:
    """기록한 활동을 희망 계열·학과와 이어서 '정리'한다. 평가나 판단은 하지 않는다."""
    acts = list_activities(uid)
    tags = goal_tags(track, major)
    groups = goal_subject_groups(track, major)
    linked = []
    for a in acts:
        hs = [s for s in a["subjects"] if s in groups]
        ht = [c for c in a["careers"] if c in tags]
        if hs or ht:
            linked.append({**a, "hit_subjects": hs, "hit_tags": ht})
    by_type = Counter(a["act_type"] for a in acts)
    by_subject = Counter(s for a in acts for s in a["subjects"])
    by_career = Counter(c for a in acts for c in a["careers"])
    flows: dict = {}
    for tag, _n in by_career.most_common(3):
        seq = sorted((a for a in acts if tag in a["careers"]), key=lambda a: (a["act_date"], a["id"]))
        flows[tag] = seq
    return {
        "total": len(acts),
        "minutes_total": sum(a["minutes"] or 0 for a in acts),
        "by_type": {t: by_type[t] for t in ACTIVITY_TYPES if by_type[t]},
        "by_subject": dict(by_subject.most_common()),
        "by_career": dict(by_career.most_common()),
        "empty_types": [t for t in ACTIVITY_TYPES if t != "기타" and not by_type[t]],
        "goal_tags": tags,
        "goal_groups": sorted(groups),
        "linked": linked,
        "linked_subjects": dict(Counter(s for a in linked for s in a["hit_subjects"]).most_common()),
        "linked_tags": dict(Counter(c for a in linked for c in a["hit_tags"]).most_common()),
        "flows": flows,
    }


# =====================================================================
# 8. 화면
# =====================================================================
TAG_COLORS = {"공학": "#3182F6", "컴퓨터·AI": "#06B6D4", "자연과학": "#65A30D", "의약·보건": "#F04452",
              "인문·언어": "#F59E0B", "사회·경영": "#7C3AED", "교육": "#14B8A6", "미디어": "#EC4899",
              "예체능": "#F97316", "환경": "#16A34A", "기타": "#8B95A1"}
BLUE, GRAY = "#3182F6", "#D1D6DB"


def activity_months(acts: list[dict], linked_ids: set, today: date | None = None, n: int = 12) -> list[dict]:
    """최근 n개월(이번 달 포함)의 월별 활동 수. 희망 진로와 이어진 것과 아닌 것을 나눠서 센다."""
    today = today or _today()
    keys = []
    y, m = today.year, today.month
    for _ in range(n):
        keys.append((y, m))
        m -= 1
        if m == 0:
            y, m = y - 1, 12
    keys.reverse()
    out = {k: {"label": f"{k[1]}월", "key": f"{k[0]}-{k[1]:02d}", "linked": 0, "other": 0} for k in keys}
    for a in acts:
        try:
            d = date.fromisoformat(a["act_date"])
        except ValueError:
            continue
        slot = out.get((d.year, d.month))
        if slot:
            slot["linked" if a["id"] in linked_ids else "other"] += 1
    return [out[k] for k in keys]


def _school_name(title: str) -> str:
    """'국립강릉원주대학교 _ 본교' 처럼 붙은 구분 표시를 떼고 학교 이름만 남긴다."""
    return re.split(r"\s+_\s+", str(title))[0].strip()


def school_search_url(title: str) -> str:
    """API가 학교별 페이지 주소를 주지 않아서, '학교이름 입학처' 검색 결과로 연결한다."""
    name = _school_name(title)
    return "https://search.naver.com/search.naver?" + urlparse.urlencode({"query": f"{name} 입학처"})


def _svg_img(svg: str, alt: str) -> str:
    """SVG 그림을 <img> 로 감싸서 화면에 넣는다 (st.markdown 안에서도 안정적으로 보이게)."""
    b64 = base64.b64encode(svg.encode("utf-8")).decode("ascii")
    return (f'<img alt="{_esc(alt)}" style="width:100%;height:auto;display:block;" '
            f'src="data:image/svg+xml;base64,{b64}">')


_SVG_FONT = "Pretendard, 'Noto Sans KR', 'Apple SD Gothic Neo', 'Malgun Gothic', sans-serif"


def direction_map_svg(S: dict, center_label: str):
    """가운데는 내 희망 진로, 둘레는 이어서 보는 영역(진로 태그·교과). 활동이 많을수록 원이 크고 선이 굵어요.
    평가가 아니라 '어디에 활동이 모여 있는지'를 보여줄 뿐이에요. 목표가 없으면 None."""
    nodes = [(t, S["linked_tags"].get(t, 0), TAG_COLORS.get(t, BLUE)) for t in S["goal_tags"]]
    subs = sorted(((g, S["linked_subjects"].get(g, 0)) for g in S["goal_groups"]), key=lambda x: (-x[1], x[0]))
    nodes += [(f"{g} 교과", c, "#6366F1") for g, c in subs[: max(0, 8 - len(nodes))]]
    if not nodes:
        return None
    other = S["total"] - len(S["linked"])
    if other > 0:
        nodes.append(("그 밖의 활동", other, "#B0B8C1"))
    W = H = 360
    cx = cy = 180
    R = 112
    n = len(nodes)
    edges, circles, labels = "", "", ""
    for i, (name, c, color) in enumerate(nodes):
        ang = -math.pi / 2 + 2 * math.pi * i / n
        x, y = cx + R * math.cos(ang), cy + R * math.sin(ang)
        r = 20 + min(14, c * 3) if c else 18
        if c:
            edges += (f'<line x1="{cx}" y1="{cy}" x2="{x:.1f}" y2="{y:.1f}" stroke="{color}" '
                      f'stroke-width="{2 + min(6, c * 1.2):.1f}" stroke-linecap="round" opacity="0.55"/>')
            circles += (f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{color}"/>'
                        f'<text x="{x:.1f}" y="{y + 5:.1f}" text-anchor="middle" font-size="15" font-weight="800" '
                        f'fill="#fff">{c}</text>')
        else:
            edges += (f'<line x1="{cx}" y1="{cy}" x2="{x:.1f}" y2="{y:.1f}" stroke="#D5DAE1" '
                      f'stroke-width="2" stroke-dasharray="4 5" stroke-linecap="round"/>')
            circles += (f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="#fff" stroke="#C5CBD3" '
                        f'stroke-width="2" stroke-dasharray="4 4"/>'
                        f'<text x="{x:.1f}" y="{y + 5:.1f}" text-anchor="middle" font-size="14" '
                        f'font-weight="700" fill="#B0B8C1">0</text>')
        labels += (f'<text x="{x:.1f}" y="{y + r + 15:.1f}" text-anchor="middle" font-size="12" font-weight="700" '
                   f'fill="#333D4B" stroke="#fff" stroke-width="4" paint-order="stroke">{html.escape(name)}</text>')
    short = html.escape((center_label or "희망 진로")[:9])
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="{_SVG_FONT}">'
           f'<defs><linearGradient id="g" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#3182F6"/>'
           f'<stop offset="1" stop-color="#5BA0FF"/></linearGradient></defs>'
           f'<rect width="{W}" height="{H}" rx="20" fill="#F7F9FC"/>'
           f'{edges}'
           f'<circle cx="{cx}" cy="{cy}" r="48" fill="url(#g)"/>'
           f'<text x="{cx}" y="{cy - 2}" text-anchor="middle" font-size="14" font-weight="800" fill="#fff">{short}</text>'
           f'<text x="{cx}" y="{cy + 16}" text-anchor="middle" font-size="11" fill="#fff" opacity="0.92">'
           f'이어진 활동 {len(S["linked"])}개</text>'
           f'{circles}{labels}</svg>')
    return svg


def _donut_html(pct: int, color: str = BLUE) -> str:
    pct = max(0, min(100, int(pct)))
    return (f'<div class="ct-donut" style="background:conic-gradient({color} {pct * 3.6:.0f}deg,#E8EBF0 0);">'
            f'<div>{pct}%</div></div>')


def _hbars_html(counts: dict, highlight=(), colors: dict | None = None) -> str:
    """가로 막대. 희망 진로에 해당하는 항목에는 '내 희망' 표시를 붙여요."""
    if not counts:
        return ""
    mx = max(counts.values()) or 1
    rows = ""
    for name, v in counts.items():
        color = (colors or {}).get(name, BLUE)
        star = "⭐ " if name in highlight else ""
        rows += (f'<div class="ct-hb"><div class="nm">{star}{_esc(name)}</div>'
                 f'<div class="tr"><i style="width:{max(6, round(v * 100 / mx))}%;background:{color};"></i></div>'
                 f'<div class="ct">{v}</div></div>')
    return rows


def _tiles_html(by_type: dict) -> str:
    cells = ""
    for t in ACTIVITY_TYPES:
        n = by_type.get(t, 0)
        cells += (f'<div class="ct-tile"><b>{n}</b><span>{_esc(t)}</span></div>' if n else
                  f'<div class="ct-tile empty"><b>0</b><span>{_esc(t)}</span></div>')
    return f'<div class="ct-tiles">{cells}</div>'


def _months_html(months: list[dict]) -> str:
    mx = max((m["linked"] + m["other"] for m in months), default=0) or 1
    cols = ""
    for m in months:
        tot = m["linked"] + m["other"]
        h_l = round(m["linked"] * 70 / mx)
        h_o = round(m["other"] * 70 / mx)
        cols += (f'<div class="ct-mcol"><div class="n">{tot or ""}</div><div class="st">'
                 f'<i style="height:{h_o}px;background:{GRAY};border-radius:4px 4px 0 0;"></i>'
                 f'<i style="height:{h_l}px;background:{BLUE};{"border-radius:4px 4px 0 0;" if not h_o else ""}"></i>'
                 f'</div><div class="lb">{_esc(m["label"])}</div></div>')
    return (f'<div class="ct-months">{cols}</div><div class="ct-legend">'
            f'<span><i style="background:{BLUE};"></i>희망 진로와 이어진 활동</span>'
            f'<span><i style="background:{GRAY};"></i>그 밖의 활동</span></div>')


def _flow_html(seq: list[dict], color: str) -> str:
    nodes = ""
    for a in seq[-5:]:
        d = date.fromisoformat(a["act_date"])
        nodes += (f'<div class="ct-node" style="color:{color};"><i></i><b>{d.month}/{d.day}</b>'
                  f'<span style="color:#4E5968;">{_esc(a["act_type"])}</span><br>'
                  f'<span style="color:#8B95A1;">{_esc(a["title"][:8])}</span></div>')
    return f'<div class="ct-flow">{nodes}</div>'


def _guidance_tab(user: dict) -> None:
    uid = user["uid"]
    track, major = user["track"], user["major"]
    goal = " ".join(x for x in [major, track and f"({track} 계열)"] if x) or "희망 진로"
    S = guidance_summary(uid, track, major)

    acts = list_activities(uid)

    # --- 방향 지도 (시각화) ---
    if S["total"] == 0:
        st.info("아직 기록한 활동이 없어요. 아래에서 발표, 특강, 탐구 같은 활동을 하나씩 적어보세요.")
    else:
        linked_n = len(S["linked"])
        pct = round(linked_n * 100 / S["total"])
        hours = f' · 활동 시간 {_fmt_dur(S["minutes_total"] * 60)}' if S["minutes_total"] else ""
        if S["goal_tags"] or S["goal_groups"]:
            basis = (f'진로 {_esc(" · ".join(S["goal_tags"]) or "-")} / 교과 {_esc(" · ".join(S["goal_groups"]) or "-")}'
                     f' 기준으로 이어서 봤어요')
        else:
            basis = "위의 '내 목표 설정'에 희망 계열이나 학과를 저장하면 기록과 이어서 보여드려요"
        _card(f'<div class="ct-top">{_donut_html(pct)}<div>'
              f'<div class="ct-muted">{_esc(goal)}와 이어진 활동</div>'
              f'<div class="ct-title" style="font-size:24px;">{linked_n}개 <span class="ct-muted">/ 전체 {S["total"]}개</span></div>'
              f'<div class="ct-muted" style="margin-top:4px;">{basis}{hours}</div></div></div>')

        mp = direction_map_svg(S, major or (track and f"{track} 계열") or "")
        if mp:
            _card('<div class="ct-title">나의 방향 지도</div>'
                  '<div class="ct-muted">가운데는 내 희망 진로, 둘레는 이어서 보는 영역이에요. '
                  '원이 크고 선이 굵을수록 그 영역의 활동이 많아요. 남보라색은 교과, 점선 원은 아직 기록이 없는 영역이에요.</div>'
                  + _svg_img(mp, "희망 진로와 활동이 이어진 방향 지도"))
        if S["by_career"]:
            _card(f'<div class="ct-title">진로 영역 지도</div><div class="ct-muted">기록에 단 진로 태그별 활동 수예요.{" ⭐는 내 희망 진로예요." if S["goal_tags"] else ""}</div>'
                  f'<div style="margin-top:8px;">{_hbars_html(S["by_career"], S["goal_tags"], TAG_COLORS)}</div>')
        if S["by_subject"]:
            _card(f'<div class="ct-title">교과 균형</div><div class="ct-muted">관련 교과별 활동 수예요.{" ⭐는 희망 진로와 이어서 보는 교과예요." if S["goal_groups"] else ""}</div>'
                  f'<div style="margin-top:8px;">{_hbars_html(S["by_subject"], S["goal_groups"])}</div>')
        _card(f'<div class="ct-title">활동 유형 지도</div>'
              f'<div class="ct-muted">파란 칸은 기록이 있는 유형, 점선 칸은 아직 기록이 없는 유형이에요.</div>'
              f'{_tiles_html(S["by_type"])}')
        _card(f'<div class="ct-title">월별 활동</div><div class="ct-muted">최근 12개월 동안의 기록이에요.</div>'
              f'{_months_html(activity_months(acts, {x["id"] for x in S["linked"]}))}')

        if S["flows"]:
            fl = ""
            for tag, seq in S["flows"].items():
                fl += (f'<div class="ct-item"><div class="ct-row"><b>{_esc(tag)}</b>'
                       f'<span class="ct-chip">{len(seq)}개</span></div>'
                       f'{_flow_html(seq, TAG_COLORS.get(tag, BLUE))}</div>')
            _card(f'<div class="ct-title">관심 흐름</div>'
                  f'<div class="ct-muted">같은 진로 태그를 단 활동을 날짜순으로 이어봤어요. (최근 5개)</div>{fl}')

        if S["linked"]:
            li = "".join(
                f'<div class="ct-item"><div class="ct-row"><b>{_esc(a["title"])}</b>'
                f'<span class="ct-chip mint">{_esc(a["act_type"])}</span></div>'
                f'<div class="ct-muted">{_esc(a["act_date"])} · '
                f'{_esc(" · ".join(a["hit_tags"] + a["hit_subjects"]))}</div></div>' for a in S["linked"][:8])
            _card(f'<div class="ct-title">희망 진로와 이어진 활동</div>{li}')

    st.caption("🔒 기록은 나만 볼 수 있어요. 앱은 적어둔 활동을 정리해서 보여줄 뿐, 생활기록부 평가나 합격 가능성은 "
               "판단하지 않아요. 실제 기재 여부와 방향은 담임·교과 선생님과 상의하세요.")

    # --- 활동 기록 추가 ---
    with st.expander("✏️ 활동 기록하기", expanded=S["total"] == 0):
        with st.form("ga_form", clear_on_submit=True):
            c1, c2 = st.columns(2)
            a_date = c1.date_input("날짜", value=_today(), max_value=_today(), key="ga_date")
            a_type = c2.selectbox("활동 유형", ACTIVITY_TYPES, key="ga_type")
            a_title = st.text_input("제목", max_chars=40, placeholder="예: 수학 주제 발표", key="ga_title")
            a_content = st.text_area("내용", max_chars=500, height=100,
                                     placeholder="예: 함수의 실생활 활용을 조사해서 발표했어요", key="ga_content")
            c3, c4 = st.columns(2)
            a_role = c3.text_input("역할 (선택)", max_chars=40, placeholder="예: 발표자", key="ga_role")
            a_min = c4.number_input("활동 시간(분, 선택)", min_value=0, max_value=1440, step=10, value=0, key="ga_min")
            a_refl = st.text_area("느낀 점 (선택)", max_chars=500, height=80, key="ga_refl")
            a_subj = st.multiselect("관련 교과", ACTIVITY_SUBJECTS, key="ga_subj")
            a_car = st.multiselect("관련 진로", CAREER_TAGS, key="ga_car")
            if st.form_submit_button("기록 저장", use_container_width=True):
                ok, msg = add_activity(uid, a_date, a_type, a_title, a_content, a_role, a_refl,
                                       a_min or None, a_subj, a_car)
                if ok:
                    _flash(msg)
                    st.rerun()
                else:
                    st.warning(msg)

    # --- 기록 모아보기: 분류를 누르면 그 분류의 기록만 정렬해서 보여준다 ---
    if acts:
        st.markdown('<div class="ct-title" style="margin:14px 0 2px;">📂 기록 모아보기</div>'
                    '<div class="ct-muted">보고 싶은 분류를 누르면 그 기록만 모아서 보여줘요.</div>',
                    unsafe_allow_html=True)
        kind = st.radio("분류 기준", VIEW_KINDS, horizontal=True, key="ct_view_kind",
                        label_visibility="collapsed")
        value = None
        if kind != "전체":
            counts = category_counts(acts, kind)
            opts = list(counts)
            vkey = f"ct_view_val_{kind}"
            if st.session_state.get(vkey) not in opts:      # 기록을 지워서 사라진 분류가 남아 있으면 초기화
                st.session_state.pop(vkey, None)
            if opts:
                value = st.radio(kind, opts, horizontal=True, key=vkey, label_visibility="collapsed",
                                 format_func=lambda v: f"{v} {counts[v]}")
            else:
                st.info(f"'{kind}' 기준으로 정리된 기록이 아직 없어요. 기록할 때 {kind}를 골라주세요.")
        order = st.radio("정렬", ["최신순", "오래된순"], horizontal=True, key="ct_view_order")
        shown = filter_activities(acts, kind, value, order) if (kind == "전체" or value) else []
        title = value if value else ("전체" if kind == "전체" else kind)
        st.markdown(f'<div class="ct-muted" style="margin:6px 0;">{_esc(title)} · {len(shown)}개 · {order}</div>',
                    unsafe_allow_html=True)
        for a in shown:
            tags = " · ".join(a["subjects"] + a["careers"])
            st.markdown(
                f'<div class="ct-row"><b>{_esc(a["title"])}</b><span class="ct-chip gray">{_esc(a["act_type"])}</span></div>'
                f'<div class="ct-muted">{_esc(a["act_date"])}{" · " + _esc(tags) if tags else ""}</div>',
                unsafe_allow_html=True)
            for label, key in (("내용", "content"), ("역할", "role"), ("느낀 점", "reflection")):
                if a[key]:
                    st.markdown(f'<div class="ct-post-body"><b>{label}</b> {_esc(a[key])}</div>',
                                unsafe_allow_html=True)
            if st.button("🗑 삭제", key=f"ga_del_{a['id']}"):
                delete_activity(uid, a["id"])
                st.rerun()
            st.divider()

def _enroll_html(it: dict, track: str) -> str:
    """계열별 입학정원 막대. 희망 계열은 '내 희망'으로 표시해요."""
    detail, total = it["detail"], it["total"]
    rows = ""
    for name, n in detail.items():
        if not n:
            continue
        pct = round(n * 100 / total) if total else 0
        chip = ' <span class="ct-chip">내 희망</span>' if name == track else ""
        rows += (f'<div class="ct-item"><div class="ct-row"><span><b>{_esc(name)}</b>{chip}</span>'
                 f'<span class="ct-muted">{n}명 · {pct}%</span></div>{_bar(pct)}</div>')
    return rows


def _univ_block(user: dict, S: dict) -> None:
    """① 대학 정보(API) → ② 희망 계열로 이어 보기. 연결 고리는 '희망 계열'이에요."""
    track, major, target = user["track"], user["major"], user["target_univ"]
    goal = " ".join(x for x in [target, major or (track and f"{track} 계열")] if x) or "희망 진로"
    st.markdown(f'<div class="ct-title" style="margin:8px 0;">{_esc(goal)}</div>', unsafe_allow_html=True)

    with st.form("ct_career_form"):
        q = st.text_input("대학 이름으로 찾아보기", value="", placeholder=target or "예: 서울대학교")
        go = st.form_submit_button("🔍 찾아보기", use_container_width=True)
    if go and (q.strip() or target):
        st.session_state["ct_career"] = (q.strip() or target, search_all(q.strip() or target))
    elif "ct_career" not in st.session_state and target:
        st.session_state["ct_career"] = (target, search_all(target))

    last = st.session_state.get("ct_career")
    shares = []
    searched: set = set()
    if last:
        query, results = last
        st.markdown(f'<div class="ct-muted">“{_esc(query)}” 검색 결과</div>', unsafe_allow_html=True)
        shown = False
        for r in results:
            if r["status"] == "off":
                continue
            shown = True
            body = ""
            if r["status"] == "ok" and r["items"]:
                for it in r["items"]:
                    summ = f'<div class="ct-muted">{_esc(it["summary"])}</div>' if it["summary"] else ""
                    links = []
                    if it["url"] and it["url"] != r.get("home"):
                        links.append(f'<a href="{_esc(it["url"])}" target="_blank" rel="noopener">'
                                     f'{_esc(it.get("link_label") or "원문 보기")} ↗</a>')
                    if _school_name(it["title"]) not in searched:
                        # 같은 학교는 한 번만: 학교 이름 + 입학처 검색 결과로 연결
                        searched.add(_school_name(it["title"]))
                        links.append(f'<a href="{_esc(school_search_url(it["title"]))}" target="_blank" rel="noopener">'
                                     f'🔎 {_esc(_school_name(it["title"]))} 입학처 검색 ↗</a>')
                    link = ('<div style="margin-top:4px;display:flex;gap:14px;flex-wrap:wrap;">' + "".join(links) + '</div>'
                            if links else "")
                    if it.get("detail") and any(it["detail"].values()):
                        body += (f'<div class="ct-item"><b>{_esc(it["title"])}</b>'
                                 f'<div class="ct-muted">입학정원 {it["total"]}명 · 계열별 정원</div>'
                                 f'{_enroll_html(it, track)}{link}</div>')
                        sh = track_share(it["detail"], it["total"], track)
                        if sh:
                            shares.append((it["title"], sh))
                    else:
                        body += f'<div class="ct-item"><b>{_esc(it["title"])}</b>{summ}{link}</div>'
            elif r["status"] == "ok":
                body = '<div class="ct-muted">관련 결과가 없어요.</div>'
            elif r["status"] == "no_key":
                body = '<div class="ct-muted">API 연결을 준비 중이에요.</div>'
            else:
                body = '<div class="ct-muted">지금은 불러오지 못했어요. 잠시 후 다시 시도해주세요.</div>'
            if r["status"] in ("no_key", "error") and st.session_state.get("ct_dev_mode"):
                why = r.get("reason", "")
                if r["status"] == "no_key":
                    why += " → 앱 설정(Manage app → Settings → Secrets)에 DATA_GO_KR_KEY 를 추가하세요."
                body += f'<div class="ct-muted" style="margin-top:6px;">🔧 확인용: {_esc(why)}</div>'
            _card(f'<div class="ct-src">📚 {_esc(r["source"])}</div>{body}')
        if not shown:
            _card('<div class="ct-muted">아직 연결된 정보 사이트가 없어요. 아래 바로가기로 직접 확인해보세요.</div>')
        st.caption("정보는 각 사이트 기준이에요. 정확한 내용은 꼭 원문에서 확인하세요.")
    else:
        st.info("위에서 대학 이름을 검색하거나, '내 목표 설정'에 목표 대학을 저장해보세요.")

    # --- 연결 카드: 같은 '계열'로 대학 정보와 내 기록을 한 줄에 놓는다 ---
    if track and track != TRACKS[0]:
        if shares:
            left = (f'{_esc(shares[0][0])} {_esc(track)} 계열 정원 <b>{shares[0][1][0]}명</b> '
                    f'(전체의 {shares[0][1][1]}%)')
        elif last:
            left = f'검색한 대학의 {_esc(track)} 계열 정원 정보를 찾지 못했어요'
        else:
            left = f'{_esc(track)} 계열 정원 정보는 대학을 검색하면 나와요'
        right = f'{_esc(track)} 계열과 이어진 내 활동 <b>{len(S["linked"])}개</b> (전체 기록 {S["total"]}개)'
        _card(f'<div class="ct-title">대학 정보와 내 기록 이어 보기</div>'
              f'<div class="ct-item"><div class="ct-muted">대학</div><div>{left}</div></div>'
              f'<div class="ct-item"><div class="ct-muted">나</div><div>{right}</div></div>')

    st.markdown('<div class="ct-muted" style="margin-top:10px;">사이트 첫 화면으로 가기 (학교별 페이지는 위 검색 결과의 링크예요)</div>',
                unsafe_allow_html=True)
    lc = st.columns(len(LINKS))
    for c, (name, url) in zip(lc, LINKS):
        c.link_button(name, url, use_container_width=True)


def _pathway_tab(user: dict) -> None:
    """진로·진학 지도: 대학 정보 + 내 활동 정리를 한 탭에서."""
    S = guidance_summary(user["uid"], user["track"], user["major"])
    _univ_block(user, S)
    st.divider()
    st.markdown('<div class="ct-title" style="margin:4px 0 8px;">🧭 나의 생기부 방향 정리</div>',
                unsafe_allow_html=True)
    _guidance_tab(user)


def page_career() -> None:
    """진로·진학 탭 전체."""
    user = _page_start()
    if not user:
        return
    uid = user["uid"]
    st.markdown('<div class="ct-title" style="margin:4px 0 12px;">🧭 진로·진학 지도</div>', unsafe_allow_html=True)
    with st.expander("내 목표 설정", expanded=not user["major"]):
        with st.form("ct_profile"):
            idx = TRACKS.index(user["track"]) if user["track"] in TRACKS else 0
            track = st.selectbox("희망 계열", TRACKS, index=idx)
            major = st.text_input("희망 학과", value=user["major"], placeholder="예: 영어교육과")
            univ = st.text_input("목표 대학 (선택)", value=user["target_univ"])
            if st.form_submit_button("저장", use_container_width=True):
                update_profile(uid, "" if track == TRACKS[0] else track, major, univ)
                _flash("목표를 저장했어요.")
                st.rerun()
    _pathway_tab(user)


# =====================================================================
# 12. 페이지 3 : 타이머 + 순위 + 게시판
# =====================================================================
def _render_live(start_ts: float) -> None:
    def body():
        el = min(int(time.time() - start_ts), MAX_SESSION_SEC)
        st.markdown(f'<div class="ct-timer">{_fmt_clock(el)}</div>', unsafe_allow_html=True)
    if hasattr(st, "fragment"):
        st.fragment(run_every=1)(body)()
    else:
        body()


def _rank_row(no, e, me: bool) -> str:
    medal = {1: "🥇", 2: "🥈", 3: "🥉"}.get(no, str(no))
    cls = "ct-rank me" if me else "ct-rank"
    who = f'{_esc(e["avatar"])} {_esc(e["nickname"])}' + (" (나)" if me else "")
    return (f'<div class="{cls}"><div class="no">{medal}</div><div class="nm">{who}</div>'
            f'<div class="ct-muted">{_fmt_dur(e["sec"])}</div></div>')


def _timer_tab(user: dict) -> None:
    uid, today = user["uid"], _today()
    act = active_session(uid)
    st.markdown('<div class="ct-card">', unsafe_allow_html=True)
    if act:
        _render_live(act["start_ts"])
        if st.button("⏹ 공부 끝내기", type="primary", use_container_width=True, key="sf_stop"):
            sec = stop_session(uid)
            _flash(f"{_fmt_dur(sec)} 기록했어요, 수고했어요! 🎉" if sec else "너무 짧아서 기록하지 않았어요.")
            st.rerun()
    else:
        st.markdown('<div class="ct-timer">00:00:00</div>', unsafe_allow_html=True)
        if st.button("▶ 공부 시작", type="primary", use_container_width=True, key="sf_start"):
            start_session(uid)
            st.rerun()
    st.markdown('</div>', unsafe_allow_html=True)

    mine = totals(today, today).get(uid, {"sec": 0})["sec"]
    st.markdown(f'<div class="ct-muted" style="text-align:center;">오늘 공부한 시간 · '
                f'<b>{_fmt_dur(mine)}</b></div>', unsafe_allow_html=True)

    st.markdown('<div class="ct-title" style="margin:16px 0 6px;">🏆 공부 시간 순위</div>', unsafe_allow_html=True)
    period = st.radio("기간", ["오늘", "이번 주"], horizontal=True, label_visibility="collapsed", key="sf_period")
    start = today if period == "오늘" else today - timedelta(days=today.weekday())
    rk = ranking(start, today, uid)
    if not rk["top"]:
        st.caption("아직 기록이 없어요. 첫 번째 주인공이 되어보세요!")
    else:
        rows = "".join(_rank_row(i + 1, e, e["uid"] == uid) for i, e in enumerate(rk["top"]))
        if user["show_rank"] and rk["my_rank"] and rk["my_rank"] > RANK_LIMIT:
            rows += _rank_row(rk["my_rank"], {"avatar": user["avatar"], "nickname": user["nickname"],
                                              "sec": rk["my_sec"]}, True)
        _card(rows)
    show = st.toggle("내 닉네임을 순위에 공개", value=bool(user["show_rank"]), key="sf_show_rank")
    if show != bool(user["show_rank"]):
        set_show_rank(uid, show)
        st.rerun()

    with st.expander("닉네임 바꾸기"):
        new = st.text_input("새 닉네임 (2~12자)", value=user["nickname"], key="sf_nick")
        if st.button("변경", key="sf_nick_btn"):
            ok, msg = update_nickname(uid, new)
            _flash(msg)
            if ok:
                st.rerun()


def _board_tab(user: dict) -> None:
    uid = user["uid"]
    st.caption("🔒 실명 대신 닉네임으로만 보여요. 개인정보·비방은 올리지 말아주세요.")

    with st.expander("✏️ 글쓰기"):
        with st.form("sf_post_form", clear_on_submit=True):
            cat = st.selectbox("카테고리", POST_CATEGORIES)
            title = st.text_input("제목", max_chars=40)
            body = st.text_area("내용", max_chars=1000, height=140)
            if st.form_submit_button("올리기", use_container_width=True):
                ok, msg = create_post(uid, cat, title, body)
                if ok:
                    _flash(msg)
                    st.rerun()
                else:
                    st.warning(msg)

    c1, c2 = st.columns([3, 2])
    cat_f = c1.selectbox("보기", ["전체"] + POST_CATEGORIES, label_visibility="collapsed", key="sf_cat_f")
    sort = c2.selectbox("정렬", ["최신", "인기"], label_visibility="collapsed", key="sf_sort")

    posts = list_posts(uid, cat_f, sort)
    if not posts:
        st.caption("아직 글이 없어요. 첫 꿀팁을 남겨보세요 🍯")
    for p in posts:
        with st.container(border=True):
            st.markdown(
                f'<div class="ct-row"><span>{_esc(p["avatar"])} <b>{_esc(p["nickname"])}</b> '
                f'<span class="ct-muted">· {_ago(p["created_at"])}</span></span>'
                f'<span class="ct-chip">{_esc(p["category"])}</span></div>'
                f'<div class="ct-post-title">{_esc(p["title"])}</div>', unsafe_allow_html=True)
            with st.expander("내용 보기"):
                st.markdown(f'<div class="ct-post-body">{_esc(p["body"])}</div>', unsafe_allow_html=True)
            a, b, c = st.columns(3)
            if a.button(f'{"❤️" if p["liked"] else "🤍"} {p["likes"]}', key=f"like_{p['id']}"):
                toggle_like(uid, p["id"])
                st.rerun()
            if p["uid"] == uid:
                if b.button("🗑 삭제", key=f"delp_{p['id']}"):
                    delete_post(uid, p["id"])
                    st.rerun()
            else:
                box = c.popover("🚩 신고") if hasattr(st, "popover") else c.expander("🚩 신고")
                with box:
                    reason = st.selectbox("사유", REPORT_REASONS, key=f"rr_{p['id']}")
                    if st.button("신고하기", key=f"rb_{p['id']}"):
                        _flash(report_post(uid, p["id"], reason))
                        st.rerun()
            if user["is_admin"] and p["uid"] != uid:
                if st.button("🛡️ 관리자 삭제", key=f"adel_{p['id']}"):
                    delete_post(uid, p["id"], is_admin=True)
                    st.rerun()

    if user["is_admin"]:
        with st.expander("🛡️ 관리자: 신고로 숨겨진 글"):
            hp = hidden_posts()
            if not hp:
                st.caption("숨겨진 글이 없어요.")
            for p in hp:
                st.markdown(f'**{_esc(p["title"])}** · 신고 {p["reports"]}건 · {_esc(p["nickname"])}')
                st.markdown(f'<div class="ct-post-body">{_esc(p["body"])}</div>', unsafe_allow_html=True)
                x, y = st.columns(2)
                if x.button("복구", key=f"rest_{p['id']}"):
                    restore_post(p["id"])
                    st.rerun()
                if y.button("삭제", key=f"hdel_{p['id']}"):
                    delete_post(user["uid"], p["id"], is_admin=True)
                    st.rerun()


def page_timer_board() -> None:
    user = _page_start()
    if not user:
        return
    t1, t2 = st.tabs(["⏱️ 공부 타이머", "📝 꿀팁 게시판"])
    with t1:
        _timer_tab(user)
    with t2:
        _board_tab(user)


# =====================================================================
# 9. 앱 시작 (로그인 화면 + 탭 2개)
# =====================================================================
# 새 기능(예: 내신 대시보드)을 붙이려면 아래 목록에 (탭 이름, 그리는 함수) 한 줄을 더하세요.
TABS = [
    ("🧭 진로·진학", page_career),
    ("⏱️ 타이머·게시판", page_timer_board),
]


def _login_screen() -> None:
    st.markdown('<div style="font-size:30px;font-weight:800;margin:24px 0 4px;">학습도우미</div>'
                '<div style="color:#8B95A1;margin-bottom:12px;">학번과 이름을 한 번만 입력하면 돼요.</div>',
                unsafe_allow_html=True)
    with st.form("app_login"):
        if len(ID_SESSION_KEYS) == 2:
            sid = st.text_input("학번", placeholder="예: 20301", max_chars=5)
            nm = st.text_input("이름", placeholder="실명을 입력해 주세요", max_chars=5)
            if st.form_submit_button("시작하기", use_container_width=True):
                err = check_login_input(sid, nm)
                if err:
                    st.error(err)
                else:
                    st.session_state[ID_SESSION_KEYS[0]] = sid.strip()
                    st.session_state[ID_SESSION_KEYS[1]] = nm.strip()
                    st.rerun()
        else:
            vals = [st.text_input(k, key=f"app_login_{k}") for k in ID_SESSION_KEYS]
            if st.form_submit_button("시작하기", use_container_width=True):
                if all(v.strip() for v in vals):
                    for k, v in zip(ID_SESSION_KEYS, vals):
                        st.session_state[k] = v.strip()
                    st.rerun()
                else:
                    st.error("값을 입력해 주세요.")
    st.caption("학번은 화면에 보이지 않아요. 기록을 나눠 저장하는 데만 쓰고, 원문은 저장하지 않아요.")


def _logout() -> None:
    for k in ID_SESSION_KEYS:
        st.session_state.pop(k, None)
    st.rerun()


def main() -> None:
    st.set_page_config(page_title="학습도우미", page_icon="📚", layout="centered")
    st.markdown(CSS, unsafe_allow_html=True)
    _login_from_url()
    if not _identity():
        _login_screen()
        return
    tabs = st.tabs([name for name, _ in TABS])
    for tab, (_, render) in zip(tabs, TABS):
        with tab:
            render()
    if st.button("이 기기에서 로그아웃", key="app_logout"):
        _logout()


if __name__ == "__main__":
    main()
