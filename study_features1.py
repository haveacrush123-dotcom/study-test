"""
기능팀(학습개선) 모듈 - study_features.py
=========================================
메인팀 앱에 이 파일을 그대로 넣고, 아래 두 줄만 호출하면 됩니다.

    from study_features import render_study_features
    render_study_features(student_code=st.session_state["student_code"])

- 3개 페이지: ① 내신 대시보드  ② 진로·대입  ③ 공부 타이머 + 게시판
- st.set_page_config 는 여기서 호출하지 않음 (메인팀이 관리)
- 학생증 코드는 저장/표시하지 않고, 해시(익명 ID)로만 사용
- 필요 패키지: streamlit>=1.37, pandas, requests
- secrets.toml 필요: FEATURE_SALT, DATA_GO_KR_KEY
"""

import hashlib
import hmac
import html
import sqlite3
import time
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta
from urllib.parse import unquote

import pandas as pd
import requests
import streamlit as st

DB_PATH = "feature_team.db"
PRIMARY = "#3182F6"  # 토스 블루

# ──────────────────────────────────────────────
# 0. 공통: 디자인(CSS), DB, 익명 ID
# ──────────────────────────────────────────────
CSS = f"""
<style>
@import url('https://cdn.jsdelivr.net/gh/orioncactus/pretendard@v1.3.9/dist/web/static/pretendard.css');
.ft-scope, .ft-scope * {{ font-family: 'Pretendard', sans-serif; }}
.ft-card {{
  background: #fff; border-radius: 20px; padding: 18px 20px; margin-bottom: 12px;
  box-shadow: 0 2px 10px rgba(0,0,0,.05);
}}
.ft-hero {{
  background: {PRIMARY}; color: #fff; border-radius: 24px; padding: 22px 24px; margin-bottom: 14px;
}}
.ft-hero small {{ opacity: .85; }}
.ft-hero h2 {{ margin: 4px 0 0 0; color: #fff; }}
.ft-title {{ font-size: 1.05rem; font-weight: 700; margin-bottom: 4px; color: #191F28; }}
.ft-sub {{ color: #6B7684; font-size: .88rem; }}
.ft-dday {{ font-size: 1.6rem; font-weight: 800; color: {PRIMARY}; }}
.ft-dday.urgent {{ color: #F04452; }}
.ft-chip {{
  display: inline-block; background: #E8F3FF; color: {PRIMARY};
  border-radius: 999px; padding: 2px 10px; font-size: .78rem; font-weight: 600; margin-right: 4px;
}}
.ft-me {{ border: 2px solid {PRIMARY}; }}
div.stButton > button {{ border-radius: 14px; font-weight: 600; }}
</style>
"""


def _inject_css():
    st.markdown(CSS, unsafe_allow_html=True)


def _esc(text) -> str:
    """사용자 입력을 HTML에 넣기 전 반드시 이스케이프 (게시판 XSS 방지)"""
    return html.escape(str(text))


def _db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def _init_db():
    with _db() as c:
        c.executescript(
            """
            CREATE TABLE IF NOT EXISTS exams (
                uid TEXT, subject TEXT, exam_date TEXT, scope TEXT,
                importance INTEGER, progress INTEGER
            );
            CREATE TABLE IF NOT EXISTS sessions (
                uid TEXT, start_ts REAL, end_ts REAL
            );
            CREATE TABLE IF NOT EXISTS posts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                uid TEXT, nickname TEXT, category TEXT, title TEXT, body TEXT,
                created TEXT, likes INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS likes (post_id INTEGER, uid TEXT, UNIQUE(post_id, uid));
            """
        )


ANIMALS = ["토끼", "고양이", "강아지", "펭귄", "수달", "판다", "여우", "곰", "다람쥐", "오리"]
ADJ = ["졸린", "열공하는", "배고픈", "씩씩한", "느긋한", "반짝이는", "용감한", "꾸준한", "엉뚱한", "든든한"]


def _anon_id(student_code: str) -> str:
    """학생증 코드 -> 익명 해시 ID. 원본 코드는 어디에도 저장하지 않는다.
    솔트는 st.secrets['FEATURE_SALT'] 에 설정 (없으면 기본값 - 배포 전 꼭 교체)."""
    salt = st.secrets.get("FEATURE_SALT", "change-me-before-deploy")
    return hmac.new(str(salt).encode(), str(student_code).encode(), hashlib.sha256).hexdigest()[:16]


def _nickname(uid: str) -> str:
    """해시 기반 자동 닉네임 (실명 노출 방지). 같은 학생은 항상 같은 닉네임."""
    n = int(uid, 16)
    return f"{ADJ[n % len(ADJ)]} {ANIMALS[(n // 10) % len(ANIMALS)]}#{uid[:3]}"


def _fmt_hm(seconds: float) -> str:
    seconds = int(seconds)
    return f"{seconds // 3600}시간 {seconds % 3600 // 60:02d}분"


# ──────────────────────────────────────────────
# 1. 내신 대시보드
# ──────────────────────────────────────────────
def page_dashboard(uid: str):
    with _db() as c:
        df = pd.read_sql("SELECT subject, exam_date, scope, importance, progress FROM exams WHERE uid=?", c, params=(uid,))

    today = date.today()
    if not df.empty:
        df["exam_date"] = pd.to_datetime(df["exam_date"]).dt.date
        df["dday"] = df["exam_date"].apply(lambda d: (d - today).days)
        upcoming = df[df["dday"] >= 0].copy()
        # 우선순위 = 중요도 x 임박도 x 남은 진도 (높을수록 먼저 공부)
        upcoming["priority"] = upcoming.apply(
            lambda r: r["importance"] * (1 / max(r["dday"], 1)) * (100 - r["progress"]) / 100, axis=1
        )
        if not upcoming.empty:
            top = upcoming.sort_values("priority", ascending=False).iloc[0]
            st.markdown(
                f"""<div class="ft-hero"><small>오늘 가장 먼저 챙길 과목</small>
                <h2>{_esc(top['subject'])} · D-{top['dday']}</h2>
                <small>중요도 {top['importance']}/5 · 진도 {top['progress']}%</small></div>""",
                unsafe_allow_html=True,
            )
            for _, r in upcoming.sort_values("dday").iterrows():
                urgent = "urgent" if r["dday"] <= 7 else ""
                st.markdown(
                    f"""<div class="ft-card">
                    <div style="display:flex;justify-content:space-between;align-items:center">
                      <div><div class="ft-title">{_esc(r['subject'])}</div>
                      <div class="ft-sub">{r['exam_date']} · 범위: {_esc(r['scope'] or '미입력')}</div>
                      <span class="ft-chip">중요도 {'★' * int(r['importance'])}</span></div>
                      <div class="ft-dday {urgent}">D-{r['dday']}</div></div></div>""",
                    unsafe_allow_html=True,
                )
                st.progress(int(r["progress"]) / 100, text=f"진도 {r['progress']}%")
    else:
        st.info("아직 등록된 시험이 없어요. 아래에서 추가해 보세요 ✏️")

    with st.expander("시험 일정 추가·수정", expanded=df.empty):
        base = df[["subject", "exam_date", "scope", "importance", "progress"]] if not df.empty else pd.DataFrame(
            {"subject": [], "exam_date": [], "scope": [], "importance": [], "progress": []}
        )
        edited = st.data_editor(
            base,
            num_rows="dynamic",
            use_container_width=True,
            column_config={
                "subject": st.column_config.TextColumn("과목", required=True),
                "exam_date": st.column_config.DateColumn("시험일", required=True),
                "scope": st.column_config.TextColumn("시험 범위"),
                "importance": st.column_config.NumberColumn("중요도(1~5)", min_value=1, max_value=5, step=1, default=3),
                "progress": st.column_config.NumberColumn("진도(%)", min_value=0, max_value=100, step=5, default=0),
            },
            key="exam_editor",
        )
        if st.button("저장하기", type="primary"):
            clean = edited.dropna(subset=["subject", "exam_date"])
            with _db() as c:
                c.execute("DELETE FROM exams WHERE uid=?", (uid,))
                for _, r in clean.iterrows():
                    c.execute(
                        "INSERT INTO exams VALUES (?,?,?,?,?,?)",
                        (uid, str(r["subject"]), str(pd.to_datetime(r["exam_date"]).date()), str(r.get("scope") or ""),
                         int(r.get("importance") or 3), int(r.get("progress") or 0)),
                    )
            st.success("저장했어요!")
            st.rerun()


# ──────────────────────────────────────────────
# 2. 진로·대입 연계
# ──────────────────────────────────────────────
# 공공데이터포털(data.go.kr) API 2종. 인증키는 코드에 쓰지 않고 .streamlit/secrets.toml 에 둔다:
#     DATA_GO_KR_KEY = "발급받은 일반 인증키"   (인코딩된 값/디코딩된 값 둘 다 가능)
API_QUOTA = {
    "name": "전국대학별 입학정원",
    "url": "https://api.data.go.kr/openapi/tn_pubr_public_univ_mtcltn_api",
}
API_BASIC = {
    "name": "대학알리미 대학 기본정보",
    "base": "https://apis.data.go.kr/B340014/BasicInformationService_2",
    # TODO: 활용신청 상세페이지에 적힌 '오퍼레이션(상세기능) 이름'으로 교체하세요. 예) "/getXxxxx"
    "operation": "",
}

QUICK_LINKS = [
    ("대입정보포털 어디가", "https://www.adiga.kr"),
    ("한국대학교육협의회", "https://www.kcue.or.kr"),
]

# 응답 필드명이 API마다 달라서, 학교 이름이 들어있을 법한 키를 넓게 찾는다.
NAME_KEYS = ["schoolName", "schlNm", "univNm", "대학교명", "학교명", "학교", "대학명", "SCHOOL_NAME"]


def _service_key() -> str:
    # 이미 URL 인코딩된 키(%2B 등)가 들어와도 requests 가 한 번 더 인코딩하지 않도록 풀어서 사용
    return unquote(str(st.secrets.get("DATA_GO_KR_KEY", "")))


def _school_name(rec: dict) -> str:
    for k in NAME_KEYS:
        if rec.get(k):
            return str(rec[k]).strip()
    for v in rec.values():  # 못 찾으면 '대'로 끝나는 첫 값
        if isinstance(v, str) and v.strip().endswith(("대학교", "대학", "대")):
            return v.strip()
    return ""


@st.cache_data(ttl=86400, show_spinner=False)
def _fetch_quota(key: str) -> list[dict]:
    """API 1 (JSON). 전체를 페이지 단위로 받아 하루 캐시 -> 서버 호출 최소화"""
    rows, page = [], 1
    while page <= 10:
        r = requests.get(
            API_QUOTA["url"],
            params={"serviceKey": key, "pageNo": page, "numOfRows": 100, "type": "json"},
            timeout=10,
        )
        r.raise_for_status()
        body = r.json()["response"]["body"]
        items = body.get("items") or []
        if isinstance(items, dict):
            items = items.get("item", [])
        if isinstance(items, dict):
            items = [items]
        rows += items
        if not items or page * 100 >= int(body.get("totalCount") or 0):
            break
        page += 1
    return rows


@st.cache_data(ttl=86400, show_spinner=False)
def _fetch_basic(key: str) -> list[dict]:
    """API 2 (XML). <item> 안의 자식 태그를 그대로 dict 로 변환"""
    if not API_BASIC["operation"]:
        return []
    rows, page = [], 1
    while page <= 10:
        r = requests.get(
            API_BASIC["base"] + API_BASIC["operation"],
            params={"serviceKey": key, "pageNo": page, "numOfRows": 100},
            timeout=10,
        )
        r.raise_for_status()
        items = [{c.tag: (c.text or "").strip() for c in it} for it in ET.fromstring(r.content).iter("item")]
        rows += items
        if len(items) < 100:
            break
        page += 1
    return rows


def _match(query: str, rows: list[dict]) -> list[dict]:
    """질문에 학교 이름(서울대학교 / 서울대 등)이 들어 있는 레코드만 고른다"""
    q = query.replace(" ", "")
    out = []
    for r in rows:
        name = _school_name(r).replace(" ", "")
        if len(name) < 2:
            continue
        variants = {name, name.replace("대학교", "대"), name.replace("대학교", "")}
        if any(len(v) >= 2 and v in q for v in variants):
            out.append(r)
    return out


def _record_card(title: str, rec: dict):
    quota = [(k, v) for k, v in rec.items() if "정원" in k or "quota" in k.lower()]
    chips = "".join(f'<span class="ft-chip">{_esc(k)} {_esc(v)}</span>' for k, v in quota[:4])
    st.markdown(
        f'<div class="ft-card"><div class="ft-title">{_esc(title)}</div>{chips}</div>',
        unsafe_allow_html=True,
    )
    with st.expander("전체 항목 보기"):
        st.dataframe(pd.DataFrame(rec.items(), columns=["항목", "값"]), hide_index=True, use_container_width=True)


def page_career(uid: str):
    st.markdown(
        '<div class="ft-hero"><small>진로·대입</small><h2>궁금한 대학을 물어보세요</h2></div>',
        unsafe_allow_html=True,
    )
    q = st.text_input("질문 입력", placeholder="예) 서울대학교 입학정원 알려줘", label_visibility="collapsed")

    key = _service_key()
    if q:
        if not key:
            st.warning("API 인증키가 설정되지 않았어요. (secrets.toml 의 DATA_GO_KR_KEY)")
        else:
            found_any = False
            for api, fetch in ((API_QUOTA, _fetch_quota), (API_BASIC, _fetch_basic)):
                try:
                    with st.spinner(f"{api['name']}에서 찾는 중…"):
                        hits = _match(q, fetch(key))
                except Exception as e:  # 예외 메시지에 URL(=키)이 섞일 수 있어 종류만 표시
                    st.caption(f"⚠️ {api['name']} 연결 실패 ({type(e).__name__}). 잠시 후 다시 시도해 주세요.")
                    continue
                for rec in hits[:5]:
                    found_any = True
                    _record_card(f"{_school_name(rec)} · {api['name']}", rec)
            if not found_any:
                st.info("일치하는 대학을 못 찾았어요. 대학 이름을 정확히 적어볼까요? (예: 연세대학교)")

    st.markdown("##### 바로가기")
    for label, url in QUICK_LINKS:
        st.markdown(f'<div class="ft-card"><a href="{url}" target="_blank">{_esc(label)} ↗</a></div>', unsafe_allow_html=True)


# ──────────────────────────────────────────────
# 3. 공부 타이머 + 랭킹 + 게시판
# ──────────────────────────────────────────────
def _active_session(uid: str):
    with _db() as c:
        return c.execute("SELECT rowid, start_ts FROM sessions WHERE uid=? AND end_ts IS NULL", (uid,)).fetchone()


def _total_seconds(since: datetime) -> pd.DataFrame:
    """since 이후 학생별 누적 공부 시간 (진행 중인 세션 포함)"""
    s = since.timestamp()
    now = time.time()
    with _db() as c:
        rows = c.execute("SELECT uid, start_ts, COALESCE(end_ts, ?) AS e FROM sessions WHERE e > ?", (now, s)).fetchall()
    tot: dict[str, float] = {}
    for r in rows:
        tot[r["uid"]] = tot.get(r["uid"], 0) + (r["e"] - max(r["start_ts"], s))
    return pd.DataFrame(sorted(tot.items(), key=lambda x: -x[1]), columns=["uid", "sec"])


def _timer_body(uid: str):
    act = _active_session(uid)
    today0 = datetime.combine(date.today(), datetime.min.time())
    mine = _total_seconds(today0)
    mine_sec = float(mine.loc[mine.uid == uid, "sec"].sum()) if not mine.empty else 0.0

    st.markdown(
        f'<div class="ft-hero"><small>오늘 공부한 시간</small><h2>{_fmt_hm(mine_sec)}</h2>'
        f'<small>{"공부 중이에요 🔥" if act else "시작 버튼을 눌러보세요"}</small></div>',
        unsafe_allow_html=True,
    )
    if act:
        if st.button("⏹ 공부 끝", use_container_width=True, type="primary"):
            with _db() as c:
                c.execute("UPDATE sessions SET end_ts=? WHERE uid=? AND end_ts IS NULL", (time.time(), uid))
            st.rerun()
    else:
        if st.button("▶ 공부 시작", use_container_width=True, type="primary"):
            with _db() as c:
                c.execute("INSERT INTO sessions (uid, start_ts, end_ts) VALUES (?,?,NULL)", (uid, time.time()))
            st.rerun()


# 1초마다 화면 갱신 (st.fragment 미지원 버전에서는 수동 새로고침)
if hasattr(st, "fragment"):
    _timer_fragment = st.fragment(run_every=1)(_timer_body)
else:  # pragma: no cover
    _timer_fragment = _timer_body


def _ranking_tab(uid: str):
    period = st.radio("기간", ["오늘", "이번 주"], horizontal=True, label_visibility="collapsed")
    now = datetime.now()
    since = datetime.combine(date.today(), datetime.min.time())
    if period == "이번 주":
        since -= timedelta(days=now.weekday())
    df = _total_seconds(since)
    if df.empty:
        st.info("아직 기록이 없어요. 첫 번째 주인공이 되어 보세요!")
        return
    for i, r in enumerate(df.head(20).itertuples(), start=1):
        medal = {1: "🥇", 2: "🥈", 3: "🥉"}.get(i, f"{i}")
        me = "ft-me" if r.uid == uid else ""
        st.markdown(
            f'<div class="ft-card {me}"><div style="display:flex;justify-content:space-between">'
            f'<div class="ft-title">{medal} {_esc(_nickname(r.uid))}{" (나)" if r.uid == uid else ""}</div>'
            f'<div class="ft-dday" style="font-size:1.1rem">{_fmt_hm(r.sec)}</div></div></div>',
            unsafe_allow_html=True,
        )


CATEGORIES = ["공부 꿀팁", "과목별 정보", "질문", "자유"]


def _board_tab(uid: str):
    nick = _nickname(uid)
    st.caption(f"게시판에서는 실명 대신 **{nick}** 으로 표시돼요. (학생증 코드는 저장·공개되지 않아요)")

    with st.expander("✏️ 글쓰기"):
        cat = st.selectbox("분류", CATEGORIES)
        title = st.text_input("제목", max_chars=40)
        body = st.text_area("내용", max_chars=1000, height=120)
        st.caption("실명·연락처·SNS 계정 등 개인정보는 쓰지 말아주세요.")
        if st.button("올리기", type="primary"):
            if len(title.strip()) < 2 or len(body.strip()) < 5:
                st.error("제목과 내용을 조금 더 써주세요.")
            else:
                with _db() as c:
                    c.execute(
                        "INSERT INTO posts (uid, nickname, category, title, body, created) VALUES (?,?,?,?,?,?)",
                        (uid, nick, cat, title.strip(), body.strip(), datetime.now().strftime("%m/%d %H:%M")),
                    )
                st.rerun()

    filt = st.radio("분류 보기", ["전체"] + CATEGORIES, horizontal=True, label_visibility="collapsed")
    with _db() as c:
        q = "SELECT * FROM posts" + ("" if filt == "전체" else " WHERE category=?") + " ORDER BY id DESC LIMIT 30"
        posts = c.execute(q, () if filt == "전체" else (filt,)).fetchall()

    for p in posts:
        st.markdown(
            f'<div class="ft-card"><span class="ft-chip">{_esc(p["category"])}</span>'
            f'<div class="ft-title">{_esc(p["title"])}</div>'
            f'<div class="ft-sub">{_esc(p["nickname"])} · {_esc(p["created"])}</div>'
            f'<div style="margin-top:8px;white-space:pre-wrap">{_esc(p["body"])}</div></div>',
            unsafe_allow_html=True,
        )
        c1, c2, _ = st.columns([1, 1, 4])
        if c1.button(f"👍 {p['likes']}", key=f"like_{p['id']}"):
            with _db() as c:
                try:
                    c.execute("INSERT INTO likes VALUES (?,?)", (p["id"], uid))
                    c.execute("UPDATE posts SET likes=likes+1 WHERE id=?", (p["id"],))
                except sqlite3.IntegrityError:
                    pass  # 이미 좋아요 누름
            st.rerun()
        if p["uid"] == uid and c2.button("삭제", key=f"del_{p['id']}"):  # 본인 글만 삭제
            with _db() as c:
                c.execute("DELETE FROM posts WHERE id=? AND uid=?", (p["id"], uid))
            st.rerun()


def page_study(uid: str):
    t1, t2, t3 = st.tabs(["⏱ 타이머", "🏆 랭킹", "💬 꿀팁 게시판"])
    with t1:
        _timer_fragment(uid)
    with t2:
        _ranking_tab(uid)
    with t3:
        _board_tab(uid)


# ──────────────────────────────────────────────
# 메인팀이 호출하는 진입점
# ──────────────────────────────────────────────
PAGES = {"📚 내신": page_dashboard, "🎓 진로·대입": page_career, "⏱ 공부": page_study}


def render_study_features(student_code: str):
    _init_db()
    _inject_css()
    uid = _anon_id(student_code)
    st.markdown('<div class="ft-scope">', unsafe_allow_html=True)
    choice = st.radio("메뉴", list(PAGES), horizontal=True, label_visibility="collapsed", key="ft_nav")
    PAGES[choice](uid)
    st.markdown("</div>", unsafe_allow_html=True)


# 단독 테스트: streamlit run study_features.py
if __name__ == "__main__":
    st.set_page_config(page_title="학습개선 기능 테스트", page_icon="📚", layout="centered")
    render_study_features(student_code=st.session_state.get("student_code", "TEST-0001"))
