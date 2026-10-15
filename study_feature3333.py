"""
study_feature.py  -  기능팀(학습 도우미) 모듈
=====================================================================
페이지는 딱 3장입니다.
  1) page_study()        : 내신 대시보드 (시험/학습 관리, 자동 재배치, 습관 트래커)
  2) page_career()       : 진로·대입 연계 (궁금한 걸 입력 -> 여러 사이트 API에서 즉시 조회)
  3) page_timer_board()  : 공부 타이머 + 공부 시간 순위 + 꿀팁 게시판

메인팀 앱에 붙이는 법 (Streamlit 기준)
---------------------------------------------------------------------
1. 이 파일을 메인팀 앱 폴더에 그대로 복사합니다.
2. 아래 'STUDENT_CODE_SESSION_KEY' 한 줄만 메인팀이 학생증 코드를 저장해두는
   st.session_state 키 이름으로 맞춥니다. (기본값: "student_code")
3. 메인팀 앱에서:
       import study_feature as sf
       sf.page_study()          # 또는 sf.page_career() / sf.page_timer_board()
   또는 st.navigation 을 쓰신다면 sf.PAGES 를 그대로 쓰면 됩니다.
4. 혼자 테스트:   STUDY_DEV=1 streamlit run study_feature.py

환경변수 / st.secrets (코드에 직접 적지 마세요)
---------------------------------------------------------------------
  STUDY_SALT         학생증 코드 해시용 비밀 문자열 (꼭 바꾸세요, 한 번 정하면 바꾸지 마세요)
  STUDY_ADMIN_CODES  게시판 관리자 학생증 코드들 (쉼표로 구분)
  STUDY_DB_PATH      DB 파일 위치 (기본 study_feature.db)
  DATA_GO_KR_KEY     공공데이터포털에서 받은 인증키 (아래 SOURCES 의 key_env 이름과 같아야 함)

개인정보 원칙
---------------------------------------------------------------------
  - 학생증 코드는 저장하지 않습니다. salt를 섞은 해시값만 DB에 둡니다.
  - 게시판/랭킹에는 실명 대신 자동 생성 닉네임만 보입니다.
  - 랭킹 공개는 학생이 직접 끌 수 있습니다.
"""
from __future__ import annotations

import hashlib
import html
import json
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
# TODO(메인팀과 맞출 곳): 메인팀 로그인이 학생증 코드를 담아두는 session_state 키
STUDENT_CODE_SESSION_KEY = "student_code"

KST = timezone(timedelta(hours=9))
MAX_SESSION_SEC = 5 * 3600          # 타이머 1회 최대 인정 시간
MIN_SESSION_SEC = 30                # 너무 짧은 기록은 버림
RANK_LIMIT = 10                     # 랭킹 표시 인원
REPORT_HIDE_THRESHOLD = 3           # 서로 다른 학생 N명이 신고하면 자동 숨김
POST_LIMIT_PER_HOUR = 5
CATEGORIES = {"개념 정리": 1.0, "교과서": 1.0, "문제집": 1.2, "오답": 1.0, "심화": 0.8}
TRACKS = ["선택 안 함", "인문", "사회", "자연", "공학", "의약", "예체능", "교육"]
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
    return _cfg("STUDY_DB_PATH", "study_feature.db")


def _salt() -> str:
    return _cfg("STUDY_SALT", "change-me-please")


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
        "link_fields": [],                          # 학교별 링크가 없어서 대학알리미 홈으로 연결
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

# 대학 이름 검색 API만 연결된 동안은 비워둡니다. 학과·전형 API가 연결되면 예: ["선택과목", "수시 전형"]
QUICK_QUERIES: list[str] = []

# =====================================================================
# 2. 디자인 (토스 느낌 + 귀엽게)
# =====================================================================
CSS = """
<style>
.stApp{background:#F4F6FA;}
.block-container{max-width:560px;padding-top:1.2rem;padding-bottom:4rem;}
.sf-card{background:#fff;border-radius:22px;padding:20px;box-shadow:0 2px 14px rgba(25,31,40,.06);margin-bottom:14px;}
.sf-hero{background:linear-gradient(135deg,#3182F6 0%,#5BA0FF 100%);color:#fff;border-radius:26px;padding:24px;margin-bottom:14px;}
.sf-hero .big{font-size:34px;font-weight:800;line-height:1.1;}
.sf-hero .sub{opacity:.92;font-size:14px;margin-bottom:6px;}
.sf-bar{height:10px;background:#E8EBF0;border-radius:6px;overflow:hidden;margin:8px 0 4px;}
.sf-bar>div{height:100%;background:#3182F6;border-radius:6px;}
.sf-hero .sf-bar{background:rgba(255,255,255,.3);}
.sf-hero .sf-bar>div{background:#fff;}
.sf-chip{display:inline-block;padding:3px 10px;border-radius:99px;font-size:12px;font-weight:700;background:#EAF2FF;color:#3182F6;}
.sf-chip.red{background:#FFEEEF;color:#F04452;}
.sf-chip.mint{background:#E3FBF8;color:#00A99D;}
.sf-chip.gray{background:#F2F4F6;color:#6B7684;}
.sf-muted{color:#8B95A1;font-size:13px;}
.sf-title{font-size:18px;font-weight:800;color:#191F28;}
.sf-row{display:flex;justify-content:space-between;align-items:center;gap:8px;}
.sf-prio{display:flex;gap:10px;align-items:center;padding:5px 0;font-size:14px;}
.sf-prio b{width:22px;height:22px;border-radius:8px;background:#EAF2FF;color:#3182F6;display:flex;align-items:center;justify-content:center;font-size:12px;}
.sf-days{display:flex;gap:6px;justify-content:space-between;margin-top:10px;}
.sf-day{flex:1;text-align:center;font-size:12px;color:#8B95A1;}
.sf-day i{display:block;margin:4px auto 0;width:28px;height:28px;border-radius:50%;background:#E8EBF0;line-height:28px;font-style:normal;}
.sf-day.on i{background:#3182F6;color:#fff;}
.sf-timer{font-size:52px;font-weight:800;text-align:center;color:#191F28;letter-spacing:1px;padding:14px 0;font-variant-numeric:tabular-nums;}
.sf-rank{display:flex;align-items:center;gap:10px;padding:10px 4px;border-bottom:1px solid #F0F1F3;}
.sf-rank.me{background:#EAF2FF;border-radius:14px;padding:10px 12px;}
.sf-rank .no{width:30px;text-align:center;font-weight:800;}
.sf-rank .nm{flex:1;font-weight:600;}
.sf-post-title{font-size:16px;font-weight:700;margin:6px 0;color:#191F28;}
.sf-post-body{white-space:pre-wrap;font-size:14px;line-height:1.6;color:#333D4B;}
.sf-src{font-weight:800;margin:14px 0 6px;color:#191F28;}
.sf-item{padding:10px 0;border-bottom:1px solid #F0F1F3;}
.sf-item:last-child{border-bottom:none;}
div.stButton>button,div[data-testid="stFormSubmitButton"]>button{border-radius:14px;font-weight:700;}
</style>
"""


def _esc(x) -> str:
    return html.escape(str(x), quote=True)


def _card(inner_html: str) -> None:
    st.markdown(f'<div class="sf-card">{inner_html}</div>', unsafe_allow_html=True)


def _bar(pct: int) -> str:
    return f'<div class="sf-bar"><div style="width:{max(0, min(100, pct))}%"></div></div>'


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
# 4. DB
# =====================================================================
_SCHEMA = """
CREATE TABLE IF NOT EXISTS users(
  uid TEXT PRIMARY KEY, nickname TEXT, avatar TEXT,
  track TEXT DEFAULT '', major TEXT DEFAULT '', target_univ TEXT DEFAULT '',
  show_rank INTEGER DEFAULT 1, created_at REAL);
CREATE TABLE IF NOT EXISTS exams(
  id INTEGER PRIMARY KEY AUTOINCREMENT, uid TEXT, subject TEXT, exam_date TEXT);
CREATE TABLE IF NOT EXISTS units(
  id INTEGER PRIMARY KEY AUTOINCREMENT, exam_id INTEGER, uid TEXT, title TEXT,
  category TEXT, weight REAL DEFAULT 1, done INTEGER DEFAULT 0, done_date TEXT,
  confused INTEGER DEFAULT 0, planned_date TEXT);
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
CREATE INDEX IF NOT EXISTS idx_units_exam ON units(exam_id);
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
# 5. 사용자 / 로그인 (학생증 코드 -> 해시)
# =====================================================================
def hash_uid(code: str) -> str:
    """학생증 코드는 저장하지 않고, salt를 섞은 해시만 사용한다."""
    return hashlib.sha256(f"{_salt()}:{str(code).strip()}".encode("utf-8")).hexdigest()[:32]


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
                    (track[:20], major.strip()[:40], univ.strip()[:40], uid))


def set_show_rank(uid: str, show: bool) -> None:
    with _db() as con:
        con.execute("UPDATE users SET show_rank=? WHERE uid=?", (1 if show else 0, uid))


def _current_student_code():
    code = st.session_state.get(STUDENT_CODE_SESSION_KEY)
    return str(code).strip() if isinstance(code, (str, int)) and str(code).strip() else None


def _dev_login() -> None:
    """STUDY_DEV=1 일 때만, 혼자 테스트할 수 있게 코드를 직접 입력하는 칸을 보여준다."""
    if _cfg("STUDY_DEV") == "1" and not _current_student_code():
        code = st.text_input("개발용 학생 코드 입력", key="sf_dev_code")
        if code.strip():
            st.session_state[STUDENT_CODE_SESSION_KEY] = code.strip()
            st.rerun()


def _login_gate():
    code = _current_student_code()
    if not code:
        st.info("학생증 코드로 로그인하면 사용할 수 있어요 🙂")
        return None
    user = ensure_user(hash_uid(code))
    admins = [c.strip() for c in _cfg("STUDY_ADMIN_CODES").split(",") if c.strip()]
    user["is_admin"] = code in admins
    return user


def _flash(msg: str) -> None:
    st.session_state["sf_flash"] = msg


def _show_flash() -> None:
    msg = st.session_state.pop("sf_flash", None)
    if msg:
        st.toast(msg)


def _page_start():
    st.markdown(CSS, unsafe_allow_html=True)
    user = _login_gate()
    if user:
        _show_flash()
    return user


# =====================================================================
# 6. 내신 대시보드 로직
# =====================================================================
def add_exam(uid: str, subject: str, exam_date: date, titles: list[str], category: str) -> int:
    with _db() as con:
        cur = con.execute("INSERT INTO exams(uid,subject,exam_date) VALUES(?,?,?)",
                          (uid, subject.strip()[:20], exam_date.isoformat()))
        exam_id = cur.lastrowid
    if titles:
        add_units(uid, exam_id, titles, category)
    return exam_id


def add_units(uid: str, exam_id: int, titles: list[str], category: str,
              start: date | None = None) -> int:
    """학습 항목들을 오늘부터 시험 전날까지 고르게 날짜별로 배분해서 등록한다."""
    start = start or _today()
    titles = [t.strip()[:60] for t in titles if t.strip()][:200]
    if not titles:
        return 0
    with _db() as con:
        ex = con.execute("SELECT exam_date FROM exams WHERE id=? AND uid=?", (exam_id, uid)).fetchone()
        if not ex:
            return 0
        last = date.fromisoformat(ex["exam_date"]) - timedelta(days=1)
        days = max((last - start).days + 1, 1)
        n = len(titles)
        weight = CATEGORIES.get(category, 1.0)
        for i, t in enumerate(titles):
            planned = start + timedelta(days=(i * days) // n)
            con.execute("INSERT INTO units(exam_id,uid,title,category,weight,planned_date) VALUES(?,?,?,?,?,?)",
                        (exam_id, uid, t, category, weight, planned.isoformat()))
    return len(titles)


def reschedule(uid: str, today: date | None = None) -> int:
    """미완료(밀린) 학습을 남은 날짜 중 가장 여유 있는 날로 자동 재배치한다."""
    today = today or _today()
    moved = 0
    with _db() as con:
        exams = con.execute("SELECT * FROM exams WHERE uid=? AND exam_date>=?",
                            (uid, today.isoformat())).fetchall()
        for ex in exams:
            last = max(date.fromisoformat(ex["exam_date"]) - timedelta(days=1), today)
            days = [(today + timedelta(days=i)).isoformat() for i in range((last - today).days + 1)]
            counts = {d: 0 for d in days}
            overdue = []
            rows = con.execute("SELECT id, planned_date FROM units WHERE exam_id=? AND done=0 ORDER BY id",
                               (ex["id"],)).fetchall()
            for u in rows:
                p = u["planned_date"]
                if p is None or p < today.isoformat():
                    overdue.append(u["id"])
                elif p in counts:
                    counts[p] += 1
            for unit_id in overdue:
                target = min(counts, key=lambda k: (counts[k], k))
                counts[target] += 1
                con.execute("UPDATE units SET planned_date=? WHERE id=?", (target, unit_id))
                moved += 1
    return moved


def exam_progress(units: list[dict]) -> int:
    total = sum(u["weight"] for u in units)
    done = sum(u["weight"] for u in units if u["done"])
    return round(100 * done / total) if total else 0


def load_exams(uid: str, today: date | None = None) -> list[dict]:
    today = today or _today()
    with _db() as con:
        exams = [dict(r) for r in con.execute(
            "SELECT * FROM exams WHERE uid=? AND exam_date>=? ORDER BY exam_date, id",
            (uid, today.isoformat()))]
        for ex in exams:
            ex["units"] = [dict(r) for r in con.execute(
                "SELECT * FROM units WHERE exam_id=? ORDER BY id", (ex["id"],))]
    for ex in exams:
        ex["dday"] = (date.fromisoformat(ex["exam_date"]) - today).days
        ex["progress"] = exam_progress(ex["units"])
    return exams


def top_priorities(units: list[dict], n: int = 3) -> list[dict]:
    """'지금 가장 부족한 것': 헷갈린 횟수 많은 순 -> 계획일 빠른 순 -> 비중 큰 순."""
    undone = [u for u in units if not u["done"]]
    undone.sort(key=lambda u: (-u["confused"], u["planned_date"] or "9999", -u["weight"]))
    return undone[:n]


def set_unit_done(uid: str, unit_id: int, done: bool, today: date | None = None) -> None:
    today = today or _today()
    with _db() as con:
        con.execute("UPDATE units SET done=?, done_date=? WHERE id=? AND uid=?",
                    (1 if done else 0, today.isoformat() if done else None, unit_id, uid))


def mark_confused(uid: str, unit_id: int) -> None:
    """'다시 헷갈려요': 완료를 취소하고, 다음 재배치 때 남은 일정에 다시 들어간다."""
    with _db() as con:
        con.execute("UPDATE units SET done=0, done_date=NULL, confused=confused+1, planned_date=NULL "
                    "WHERE id=? AND uid=?", (unit_id, uid))


def delete_exam(uid: str, exam_id: int) -> None:
    with _db() as con:
        con.execute("DELETE FROM units WHERE exam_id=? AND uid=?", (exam_id, uid))
        con.execute("DELETE FROM exams WHERE id=? AND uid=?", (exam_id, uid))


def study_days(uid: str) -> set:
    with _db() as con:
        a = con.execute("SELECT DISTINCT day FROM sessions WHERE uid=? AND seconds>=600", (uid,)).fetchall()
        b = con.execute("SELECT DISTINCT done_date FROM units WHERE uid=? AND done_date IS NOT NULL", (uid,)).fetchall()
    return {r[0] for r in a} | {r[0] for r in b}


def streak(days: set, today: date) -> int:
    d = today if today.isoformat() in days else today - timedelta(days=1)
    n = 0
    while d.isoformat() in days:
        n += 1
        d -= timedelta(days=1)
    return n


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
# 9. 대입 정보 조회 (API 어댑터)
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
        out.append({"title": title[:80],
                    "summary": summary[:160],   # 요약 일부만 (원문은 출처에서)
                    "url": link if link.startswith(("http://", "https://")) else home})
    return out


def fetch_source(src: dict, key: str, query: str) -> dict:
    res = {"source": src["name"], "home": src.get("home_url", ""), "status": "ok", "items": []}
    if not src.get("url"):
        res["status"] = "off"
        return res
    if src.get("key_param") and not key:
        res["status"] = "no_key"
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
            code = ET.fromstring(text).findtext(".//resultCode")
            if code is not None and code.strip() not in ("00", "0", "000"):
                res["status"] = "error"
                return res
        res["items"] = _parse_items(text, src)
    except Exception:           # 키가 담긴 주소가 화면에 나오지 않도록 내용은 숨긴다
        res["status"] = "error"
        res["items"] = []
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
# 9-2. 선택과목 · 시험 우선순위 (규칙 기반 - AI 없이 계산해요)
# =====================================================================
# 우선순위 단계: 점수 계산에 곱해지는 '권장 비중'이기도 하다
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

# 대학·학과별 공식 자료를 팀이 직접 입력하는 곳. 비워두면 '계열 일반 기준'만 보여줘요.
# 예시 (실제 대학 입학처 자료를 확인한 뒤 채우세요):
# {"univ": "OO대학교", "major": "전기", "year": "2028학년도", "source": "https://입학처-주소",
#  "recommend": [("미적분Ⅱ", "핵심", "모집단위 안내 자료에 권장 과목으로 적혀 있어요"),
#                ("물리학", "핵심", "모집단위 안내 자료에 권장 과목으로 적혀 있어요")]}
UNIV_GUIDE: list[dict] = []


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


def lookup_univ_guide(univ: str, major: str):
    """팀이 입력한 대학·학과 공식 자료(UNIV_GUIDE)에서 맞는 것을 찾는다."""
    u, m = (univ or "").strip(), (major or "").strip()
    if not u:
        return None
    for g in UNIV_GUIDE:
        gu, gm = g.get("univ", ""), g.get("major", "")
        if gu and (gu in u or u in gu) and (not gm or (m and (gm in m or m in gm))):
            items = sorted(({"subject": s, "level": lv, "reason": why} for s, lv, why in g["recommend"]),
                           key=lambda x: LEVEL_ORDER.index(x["level"]))
            return {"year": g.get("year", ""), "source": g.get("source", ""), "items": items}
    return None


def exam_urgency(dday: int) -> float:
    return 3.0 if dday <= 3 else 2.0 if dday <= 7 else 1.5 if dday <= 14 else 1.0


def rank_exams(exams: list[dict], group_levels: dict) -> list[dict]:
    """시험 우선순위 = 임박도 × (남은 학습량) × 희망 계열 비중 × (헷갈림 가산).
    점수가 높을수록 지금 먼저 챙길 시험이에요."""
    out = []
    for ex in exams:
        g = subject_group(ex["subject"])
        level = group_levels.get(g, "참고") if g else "참고"
        remaining = 1 - ex["progress"] / 100
        confused = sum(u["confused"] for u in ex["units"])
        score = (exam_urgency(ex["dday"]) * (0.3 + 0.7 * remaining) * LEVELS[level]
                 * (1 + 0.05 * min(confused, 4)))
        reasons = [f"시험까지 {_dday_text(ex['dday'])}"]
        if not ex["units"]:
            reasons.append("시험 범위를 아직 등록하지 않았어요")
        elif ex["progress"] >= 100:
            reasons.append("범위를 모두 마쳤어요")
        else:
            reasons.append(f"진행률 {ex['progress']}%")
        if group_levels and level != "참고":
            reasons.append(f"희망 계열에서 {level} 과목")
        if confused:
            reasons.append(f"헷갈린 개념 {confused}회")
        out.append({"exam_id": ex["id"], "subject": ex["subject"], "dday": ex["dday"],
                    "progress": ex["progress"], "level": level, "score": round(score, 3), "reasons": reasons})
    out.sort(key=lambda r: (-r["score"], r["dday"], r["subject"]))
    return out


# =====================================================================
# 9-3. 활동 기록 + 진로진학 지도 로직
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
# 10. 페이지 1 : 내신 대시보드
# =====================================================================
def page_study() -> None:
    user = _page_start()
    if not user:
        return
    uid, today = user["uid"], _today()
    reschedule(uid, today)
    exams = load_exams(uid, today)

    st.markdown(f'<div class="sf-title" style="margin:4px 0 12px;">{_esc(user["avatar"])} '
                f'{_esc(user["nickname"])}님, 오늘도 한 걸음!</div>', unsafe_allow_html=True)

    # --- 히어로: 가장 가까운 시험 ---
    if exams:
        ex = exams[0]
        left = sum(1 for u in ex["units"] if not u["done"])
        st.markdown(
            f'<div class="sf-hero"><div class="sub">{_esc(ex["subject"])} 시험까지</div>'
            f'<div class="big">{_dday_text(ex["dday"])}</div>{_bar(ex["progress"])}'
            f'<div class="sub">학습 진행률 {ex["progress"]}% · 남은 학습 {left}개</div></div>',
            unsafe_allow_html=True)
    else:
        st.markdown('<div class="sf-hero"><div class="big">시험을 등록해볼까요?</div>'
                    '<div class="sub">아래 \'시험 추가\'에서 과목과 날짜만 넣으면 시작돼요.</div></div>',
                    unsafe_allow_html=True)

    # --- 습관 트래커 ---
    days = study_days(uid)
    dots = ""
    for i in range(6, -1, -1):
        d = today - timedelta(days=i)
        on = " on" if d.isoformat() in days else ""
        dots += f'<div class="sf-day{on}">{"월화수목금토일"[d.weekday()]}<i>{"✓" if on else ""}</i></div>'
    s = streak(days, today)
    _card(f'<div class="sf-row"><div class="sf-title">공부 습관</div>'
          f'<span class="sf-chip mint">{s}일 연속 🔥</span></div><div class="sf-days">{dots}</div>')

    # --- 오늘의 학습 ---
    st.markdown('<div class="sf-title" style="margin:6px 0;">오늘의 학습</div>', unsafe_allow_html=True)
    todo = [(ex, u) for ex in exams for u in ex["units"]
            if not u["done"] and (u["planned_date"] or "") <= today.isoformat()]
    if not exams:
        st.caption("시험을 등록하면 오늘 할 학습이 여기에 나와요.")
    elif not todo:
        st.success("오늘 할 학습을 모두 끝냈어요 🎉")
    for ex, u in todo[:8]:
        label = f'{ex["subject"]} · {u["title"]}  ({u["category"]})'
        if st.checkbox(label, value=False, key=f"today_{u['id']}"):
            set_unit_done(uid, u["id"], True, today)
            st.rerun()
    if len(todo) > 8:
        st.caption(f"외 {len(todo) - 8}개는 내일 이후로 이어져요.")

    # --- 과목(시험)별 카드 ---
    for ex in exams:
        with st.container(border=True):
            st.markdown(
                f'<div class="sf-row"><div class="sf-title">{_esc(ex["subject"])}</div>'
                f'<span class="sf-chip red">{_dday_text(ex["dday"])}</span></div>{_bar(ex["progress"])}'
                f'<div class="sf-muted">학습 진행률 {ex["progress"]}%</div>', unsafe_allow_html=True)
            pri = top_priorities(ex["units"])
            if pri:
                rows = "".join(f'<div class="sf-prio"><b>{i + 1}</b><div>{_esc(u["title"])}'
                               f'{" · 헷갈림 " + str(u["confused"]) + "회" if u["confused"] else ""}</div></div>'
                               for i, u in enumerate(pri))
                st.markdown(f'<div class="sf-muted" style="margin-top:8px;">지금 가장 부족한 것</div>{rows}',
                            unsafe_allow_html=True)
            elif ex["units"]:
                st.success("이 시험 범위를 모두 마쳤어요!")
            with st.expander(f"전체 학습 항목 ({len(ex['units'])})"):
                for u in ex["units"]:
                    c1, c2 = st.columns([5, 2])
                    with c1:
                        checked = st.checkbox(f'{u["title"]}  ({u["category"]})', value=bool(u["done"]),
                                              key=f"unit_{u['id']}")
                        if checked != bool(u["done"]):
                            set_unit_done(uid, u["id"], checked, today)
                            st.rerun()
                    with c2:
                        if u["done"] and st.button("🤔 헷갈려요", key=f"conf_{u['id']}"):
                            mark_confused(uid, u["id"])
                            _flash("다시 볼 수 있게 남은 일정에 넣어뒀어요.")
                            st.rerun()
                if st.button("이 시험 삭제", key=f"del_exam_{ex['id']}"):
                    delete_exam(uid, ex["id"])
                    st.rerun()

    # --- 시험 추가 ---
    with st.expander("＋ 시험 추가"):
        with st.form("sf_add_exam", clear_on_submit=True):
            subject = st.text_input("과목", placeholder="예: 수학")
            exam_date = st.date_input("시험 날짜", value=today + timedelta(days=14), min_value=today)
            category = st.selectbox("학습 종류", list(CATEGORIES))
            lines = st.text_area("시험 범위 (한 줄에 하나씩, 오늘부터 시험 전날까지 자동 배분돼요)",
                                 placeholder="1단원 지수와 로그\n2단원 삼각함수\n3단원 수열")
            if st.form_submit_button("등록하기", use_container_width=True):
                if not subject.strip():
                    st.warning("과목을 입력해주세요.")
                else:
                    add_exam(uid, subject, exam_date, lines.splitlines(), category)
                    _flash("시험을 등록했어요!")
                    st.rerun()


# =====================================================================
# 11. 페이지 2 : 진로·대입 연계
# =====================================================================
def page_career() -> None:
    user = _page_start()
    if not user:
        return
    uid = user["uid"]

    st.markdown('<div class="sf-title" style="margin:4px 0 12px;">🎯 진로·대입 알아보기</div>',
                unsafe_allow_html=True)

    with st.expander("내 목표 설정", expanded=not user["major"]):
        with st.form("sf_profile"):
            idx = TRACKS.index(user["track"]) if user["track"] in TRACKS else 0
            track = st.selectbox("희망 계열", TRACKS, index=idx)
            major = st.text_input("희망 학과", value=user["major"], placeholder="예: 전기전자공학과")
            univ = st.text_input("목표 대학 (선택)", value=user["target_univ"])
            if st.form_submit_button("저장", use_container_width=True):
                update_profile(uid, "" if track == TRACKS[0] else track, major, univ)
                _flash("목표를 저장했어요.")
                st.rerun()

    t_elec, t_exam, t_guide, t_search = st.tabs(["📚 선택과목", "🎯 시험 우선순위", "🧭 진로진학 지도", "🔍 대학 찾기"])
    with t_elec:
        _elective_tab(user)
    with t_exam:
        _exam_tab(user)
    with t_guide:
        _guidance_tab(user)
    with t_search:
        _career_search_tab(user)


def _level_chip(level: str) -> str:
    cls = {"핵심": "", "중요": " mint", "참고": " gray"}.get(level, " gray")
    return f'<span class="sf-chip{cls}">{_esc(level)}</span>'


def _guide_items_html(items: list[dict]) -> str:
    return "".join(
        f'<div class="sf-item"><div class="sf-row"><b>{_esc(it["subject"])}</b>{_level_chip(it["level"])}</div>'
        f'<div class="sf-muted">{_esc(it["reason"])}</div></div>' for it in items)


def _elective_tab(user: dict) -> None:
    track, major, univ = user["track"], user["major"], user["target_univ"]
    guide = resolve_guide(track, major)
    uni = lookup_univ_guide(univ, major)
    if not guide["items"] and not uni:
        st.info("위의 '내 목표 설정'에 희망 계열이나 학과를 저장하면 추천 선택과목이 나와요.")
        return
    name = " ".join(x for x in [univ, major or guide["track"]] if x)
    st.markdown(f'<div class="sf-title" style="margin:8px 0;">{_esc(name)} 선택과목 가이드</div>',
                unsafe_allow_html=True)
    if uni:
        link = (f'<a href="{_esc(uni["source"])}" target="_blank" rel="noopener">출처 보기 ↗</a>'
                if uni["source"].startswith(("http://", "https://")) else "")
        _card(f'<div class="sf-row"><div class="sf-src" style="margin:0;">대학 공식 자료</div>'
              f'<span class="sf-chip mint">{_esc(uni["year"])}</span></div>'
              f'{_guide_items_html(uni["items"])}{link}')
    if guide["items"]:
        _card(f'<div class="sf-row"><div class="sf-src" style="margin:0;">계열 일반 기준</div>'
              f'<span class="sf-chip gray">{_esc(guide["track"] or "학과 기준")}</span></div>'
              f'<div class="sf-muted">많은 대학이 공통으로 중요하게 보는 과목을 모았어요.</div>'
              f'{_guide_items_html(guide["items"])}')
    if not uni:
        st.caption("목표 대학의 공식 자료가 아직 없어요. 대학마다 다르니 꼭 입학처 자료로 확인하세요.")
    st.caption("선택과목 요건은 대학·학과·학년도마다 달라요. 지원하려는 대학의 입학처 안내와 어디가에서 꼭 확인하세요.")
    lc = st.columns(len(LINKS))
    for c, (lname, url) in zip(lc, LINKS):
        c.link_button(f"{lname} ↗", url, use_container_width=True)   # 라벨을 달리해 다른 탭의 버튼과 겹치지 않게


def _exam_tab(user: dict) -> None:
    exams = load_exams(user["uid"])
    if not exams:
        st.info("내신 페이지에서 시험을 등록하면 어떤 과목부터 챙길지 알려드려요.")
        return
    levels = resolve_guide(user["track"], user["major"])["group_levels"]
    ranked = rank_exams(exams, levels)
    top = ranked[0]
    st.markdown(
        f'<div class="sf-hero"><div class="sub">지금 우선순위 1위</div><div class="big">{_esc(top["subject"])}</div>'
        f'<div class="sub" style="margin-top:8px;">{_esc(" · ".join(top["reasons"]))}</div></div>',
        unsafe_allow_html=True)
    for i, r in enumerate(ranked, start=1):
        _card(f'<div class="sf-row"><div class="sf-title">{i}. {_esc(r["subject"])}</div>'
              f'<span class="sf-chip red">{_dday_text(r["dday"])}</span></div>{_bar(r["progress"])}'
              f'<div class="sf-muted">{_esc(" · ".join(r["reasons"]))}</div>')
    st.caption("시험이 가까울수록, 남은 범위가 많을수록, 희망 계열에서 비중이 큰 과목일수록 우선순위가 높아져요. "
               "선생님 공지와 내 상황에 맞게 참고로만 써주세요.")


def _count_line(d: dict) -> str:
    return " · ".join(f"{k} {v}" for k, v in d.items())


def _guidance_tab(user: dict) -> None:
    uid = user["uid"]
    track, major = user["track"], user["major"]
    goal = " ".join(x for x in [major, track and f"({track} 계열)"] if x) or "희망 진로"
    S = guidance_summary(uid, track, major)

    # --- 방향 정리 ---
    if S["total"] == 0:
        st.info("아직 기록한 활동이 없어요. 아래에서 발표, 특강, 탐구 같은 활동을 하나씩 적어보세요.")
    else:
        linked_n = len(S["linked"])
        hours = f' · 활동 시간 {_fmt_dur(S["minutes_total"] * 60)}' if S["minutes_total"] else ""
        st.markdown(
            f'<div class="sf-hero"><div class="sub">{_esc(goal)}와 이어진 활동</div>'
            f'<div class="big">{linked_n}개</div>'
            f'<div class="sub" style="margin-top:6px;">전체 기록 {S["total"]}개{hours}</div></div>',
            unsafe_allow_html=True)

        rows = ""
        if S["goal_tags"] or S["goal_groups"]:
            rows += (f'<div class="sf-item"><div class="sf-muted">희망 진로와 연결해서 보는 기준</div>'
                     f'<div>진로 {_esc(" · ".join(S["goal_tags"]) or "-")} / 교과 {_esc(" · ".join(S["goal_groups"]) or "-")}</div></div>')
        else:
            rows += ('<div class="sf-item"><div class="sf-muted">위의 \'내 목표 설정\'에 희망 계열이나 학과를 저장하면 '
                     '기록과 이어서 정리해드려요.</div></div>')
        if S["linked_tags"] or S["linked_subjects"]:
            area = dict(S["linked_tags"])
            for k, v in S["linked_subjects"].items():
                area[k + " 교과"] = v
            rows += (f'<div class="sf-item"><div class="sf-muted">이어진 활동의 영역</div>'
                     f'<div>{_esc(_count_line(area))}</div></div>')
        rows += (f'<div class="sf-item"><div class="sf-muted">활동 유형별 기록</div>'
                 f'<div>{_esc(_count_line(S["by_type"]))}</div></div>')
        if S["empty_types"]:
            rows += (f'<div class="sf-item"><div class="sf-muted">아직 기록이 없는 유형</div>'
                     f'<div>{_esc(" · ".join(S["empty_types"]))}</div></div>')
        _card(f'<div class="sf-title">나의 활동 정리</div>{rows}')

        if S["flows"]:
            fl = ""
            for tag, seq in S["flows"].items():
                chain = " → ".join(
                    f'{date.fromisoformat(a["act_date"]).month}/{date.fromisoformat(a["act_date"]).day} '
                    f'{a["act_type"]}·{a["title"][:12]}' for a in seq[-5:])
                fl += (f'<div class="sf-item"><div class="sf-row"><b>{_esc(tag)}</b>'
                       f'<span class="sf-chip">{len(seq)}개</span></div><div class="sf-muted">{_esc(chain)}</div></div>')
            _card(f'<div class="sf-title">관심 흐름</div><div class="sf-muted">같은 진로 태그를 단 활동을 날짜순으로 이어봤어요.</div>{fl}')

        if S["linked"]:
            li = "".join(
                f'<div class="sf-item"><div class="sf-row"><b>{_esc(a["title"])}</b>'
                f'<span class="sf-chip mint">{_esc(a["act_type"])}</span></div>'
                f'<div class="sf-muted">{_esc(a["act_date"])} · '
                f'{_esc(" · ".join(a["hit_tags"] + a["hit_subjects"]))}</div></div>' for a in S["linked"][:8])
            _card(f'<div class="sf-title">희망 진로와 이어진 활동</div>{li}')

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

    # --- 기록 목록 ---
    acts = list_activities(uid)
    if acts:
        with st.expander(f"전체 기록 보기 ({len(acts)})"):
            for a in acts:
                tags = " · ".join(a["subjects"] + a["careers"])
                st.markdown(
                    f'<div class="sf-row"><b>{_esc(a["title"])}</b><span class="sf-chip gray">{_esc(a["act_type"])}</span></div>'
                    f'<div class="sf-muted">{_esc(a["act_date"])}{" · " + _esc(tags) if tags else ""}</div>',
                    unsafe_allow_html=True)
                for label, key in (("내용", "content"), ("역할", "role"), ("느낀 점", "reflection")):
                    if a[key]:
                        st.markdown(f'<div class="sf-post-body"><b>{label}</b> {_esc(a[key])}</div>',
                                    unsafe_allow_html=True)
                if st.button("🗑 삭제", key=f"ga_del_{a['id']}"):
                    delete_activity(uid, a["id"])
                    st.rerun()
                st.divider()


def _career_search_tab(user: dict) -> None:
    with st.form("sf_career_form"):
        q = st.text_input("궁금한 대학 이름을 입력해보세요", placeholder="예: 서울대학교")
        go = st.form_submit_button("🔍 찾아보기", use_container_width=True)
    if go and q.strip():
        st.session_state["sf_career"] = (q.strip(), search_all(q))

    quick = []
    if user["target_univ"]:
        quick.append((f"🏫 {user['target_univ'][:10]}", user["target_univ"]))
    quick += [(qq, f"{user['major']} {qq}".strip()) for qq in QUICK_QUERIES]
    if quick:
        cols = st.columns(len(quick))
        for j, (label, qtext) in enumerate(quick):
            if cols[j].button(label, key=f"sf_q_{j}"):
                st.session_state["sf_career"] = (qtext, search_all(qtext))

    last = st.session_state.get("sf_career")
    if last:
        query, results = last
        st.markdown(f'<div class="sf-muted">“{_esc(query)}” 검색 결과</div>', unsafe_allow_html=True)
        shown = False
        for r in results:
            if r["status"] == "off":
                continue
            shown = True
            body = ""
            if r["status"] == "ok" and r["items"]:
                for it in r["items"]:
                    summ = f'<div class="sf-muted">{_esc(it["summary"])}</div>' if it["summary"] else ""
                    link = (f'<a href="{_esc(it["url"])}" target="_blank" rel="noopener">원문 보기 ↗</a>'
                            if it["url"] else "")
                    body += f'<div class="sf-item"><b>{_esc(it["title"])}</b>{summ}{link}</div>'
            elif r["status"] == "ok":
                body = '<div class="sf-muted">관련 결과가 없어요.</div>'
            elif r["status"] == "no_key":
                body = '<div class="sf-muted">API 연결을 준비 중이에요.</div>'
            else:
                body = '<div class="sf-muted">지금은 불러오지 못했어요. 잠시 후 다시 시도해주세요.</div>'
            _card(f'<div class="sf-src">📚 {_esc(r["source"])}</div>{body}')
        if not shown:
            _card('<div class="sf-muted">아직 연결된 정보 사이트가 없어요. 아래 바로가기로 직접 확인해보세요.</div>')
        st.caption("정보는 각 사이트 기준이에요. 정확한 내용은 꼭 원문에서 확인하세요.")

    st.markdown('<div class="sf-muted" style="margin-top:10px;">원문 사이트 바로가기</div>', unsafe_allow_html=True)
    lc = st.columns(len(LINKS))
    for c, (name, url) in zip(lc, LINKS):
        c.link_button(name, url, use_container_width=True)


# =====================================================================
# 12. 페이지 3 : 타이머 + 순위 + 게시판
# =====================================================================
def _render_live(start_ts: float) -> None:
    def body():
        el = min(int(time.time() - start_ts), MAX_SESSION_SEC)
        st.markdown(f'<div class="sf-timer">{_fmt_clock(el)}</div>', unsafe_allow_html=True)
    if hasattr(st, "fragment"):
        st.fragment(run_every=1)(body)()
    else:
        body()


def _rank_row(no, e, me: bool) -> str:
    medal = {1: "🥇", 2: "🥈", 3: "🥉"}.get(no, str(no))
    cls = "sf-rank me" if me else "sf-rank"
    who = f'{_esc(e["avatar"])} {_esc(e["nickname"])}' + (" (나)" if me else "")
    return (f'<div class="{cls}"><div class="no">{medal}</div><div class="nm">{who}</div>'
            f'<div class="sf-muted">{_fmt_dur(e["sec"])}</div></div>')


def _timer_tab(user: dict) -> None:
    uid, today = user["uid"], _today()
    act = active_session(uid)
    st.markdown('<div class="sf-card">', unsafe_allow_html=True)
    if act:
        _render_live(act["start_ts"])
        if st.button("⏹ 공부 끝내기", type="primary", use_container_width=True, key="sf_stop"):
            sec = stop_session(uid)
            _flash(f"{_fmt_dur(sec)} 기록했어요, 수고했어요! 🎉" if sec else "너무 짧아서 기록하지 않았어요.")
            st.rerun()
    else:
        st.markdown('<div class="sf-timer">00:00:00</div>', unsafe_allow_html=True)
        if st.button("▶ 공부 시작", type="primary", use_container_width=True, key="sf_start"):
            start_session(uid)
            st.rerun()
    st.markdown('</div>', unsafe_allow_html=True)

    mine = totals(today, today).get(uid, {"sec": 0})["sec"]
    st.markdown(f'<div class="sf-muted" style="text-align:center;">오늘 공부한 시간 · '
                f'<b>{_fmt_dur(mine)}</b></div>', unsafe_allow_html=True)

    st.markdown('<div class="sf-title" style="margin:16px 0 6px;">🏆 공부 시간 순위</div>', unsafe_allow_html=True)
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
                f'<div class="sf-row"><span>{_esc(p["avatar"])} <b>{_esc(p["nickname"])}</b> '
                f'<span class="sf-muted">· {_ago(p["created_at"])}</span></span>'
                f'<span class="sf-chip">{_esc(p["category"])}</span></div>'
                f'<div class="sf-post-title">{_esc(p["title"])}</div>', unsafe_allow_html=True)
            with st.expander("내용 보기"):
                st.markdown(f'<div class="sf-post-body">{_esc(p["body"])}</div>', unsafe_allow_html=True)
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
                st.markdown(f'<div class="sf-post-body">{_esc(p["body"])}</div>', unsafe_allow_html=True)
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
# 13. 3장 묶음 / 단독 실행
# =====================================================================
PAGES = {"내신": page_study, "진로·대입": page_career, "타이머·게시판": page_timer_board}


def run_standalone() -> None:
    """혼자 확인용. 메인팀 앱에 붙일 때는 쓰지 않아도 됩니다."""
    st.set_page_config(page_title="학습 도우미", page_icon="📚", layout="centered")
    _dev_login()
    tabs = st.tabs(["📚 내신", "🎯 진로·대입", "⏱️ 타이머·게시판"])
    for tab, fn in zip(tabs, PAGES.values()):
        with tab:
            fn()


if __name__ == "__main__":
    run_standalone()
