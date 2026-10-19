"""
career_map.py - "진로·대입" 탭 통합판 (대입 정보 API + 활동 기록·진로 지도)
=====================================================================
study_feature.py 의 page_career 를 대체하는 애드온입니다. study_feature.py 는 수정하지 않고,
앱의 메인 파일을 아래 4줄로 만들면 됩니다.

    import study_feature as sf
    import career_map
    sf.PAGES["진로·대입"] = career_map.page_career_map
    sf.run_standalone()

메인팀 앱에 붙일 때는 호출 쪽에서 `career_map.page_career_map()` 만 부르면 됩니다.

[두 기능을 잇는 연결고리 = 내 목표(희망 계열·학과·대학)]
  1) 대학·학과 조회  : 목표 대학/학과를 API 로 알아본다
  2) 활동 기록       : 내가 한 활동을 1분 만에 적는다 (제목 + 태그 + 3단계 100자)
  3) 내 지도         : 내 활동을 '목표 계열 / 목표 학과 단어'와 견주어 부족한 부분을 보여준다
  4) AI 정리         : 목표 + 활동을 한 덩어리 프롬프트로 만들어 외부 AI 에 붙여 쓴다

* 분석은 태그·단어 일치만 보는 단순 규칙입니다. 입시 평가 기준이 아니라 '방향 점검용'입니다.
* 활동 기록은 본인 해시 uid 로만 저장·조회됩니다 (관리자도 개별 기록은 볼 수 없게 만들었습니다).
"""

from __future__ import annotations

import re
import time
from contextlib import contextmanager

import streamlit as st

import study_feature as sf

# ---------------------------------------------------------------------
# 0. 설정 / 데이터 정의
# ---------------------------------------------------------------------
FIELD_LIMIT = 100       # 3단계 칸 글자 수
MAX_ACTIVITIES = 60     # 학생 1명당 저장 가능한 활동 수

TAGS = {
    "ai": "AI·디지털", "inquiry": "탐구·연구", "career": "진로탐색", "fusion": "융합·창의",
    "lead": "리더십·협업", "humanity": "인문·사회", "science": "과학·기술", "art": "예술·체육",
}
STEPS = [
    ("step1", "탐구 계기·동기", "무엇이 이 활동을 시작하게 했나요?"),
    ("step2", "핵심 문제 해결", "어떤 문제를 어떻게 해결했나요?"),
    ("step3", "배운 점 및 확장", "무엇을 배웠고, 이후 어떻게 이어갔나요?"),
]
EXPANSION_WORDS = ["심화", "추가로", "이어서", "발전시켜", "확장", "후속", "더 나아가", "자발적으로"]

# 계열별로 '이런 태그의 활동이 있으면 균형 있다'고 보는 기준 (제가 임의로 정한 참고용 매핑 - 팀에서 조정하세요)
TRACK_TAGS = {
    "인문": ["humanity", "inquiry", "fusion", "lead"],
    "사회": ["humanity", "lead", "inquiry", "career"],
    "자연": ["science", "inquiry", "fusion", "ai"],
    "공학": ["science", "ai", "fusion", "inquiry"],
    "의약": ["science", "inquiry", "career", "lead"],
    "예체능": ["art", "fusion", "lead", "career"],
    "교육": ["humanity", "lead", "career", "inquiry"],
}
# 목표 학과 단어가 활동에 나왔는지 볼 때, 계열별로 같이 보는 일반 단어 (단순 포함 검사)
TRACK_WORDS = {
    "인문": ["문학", "철학", "역사", "언어", "글쓰기", "독서"],
    "사회": ["경제", "정치", "법", "사회", "정책", "통계", "토론"],
    "자연": ["실험", "가설", "분석", "데이터", "화학", "물리", "생명"],
    "공학": ["코딩", "프로그래밍", "회로", "로봇", "설계", "알고리즘", "센서", "제작"],
    "의약": ["건강", "질병", "의료", "생명", "간호", "약"],
    "예체능": ["디자인", "음악", "미술", "운동", "공연", "작품"],
    "교육": ["교육", "학습", "멘토링", "수업", "가르"],
}
SUGGEST = {
    "ai": "수업 내용을 AI·코딩 도구로 분석하거나 직접 만들어 보는 활동",
    "inquiry": "교과 개념 하나를 골라 가설을 세우고 조사·실험으로 확인해 보는 활동",
    "career": "희망 직업이나 학과 교육과정을 조사하고, 인터뷰·후기로 정리해 보는 활동",
    "fusion": "서로 다른 두 과목의 개념을 엮어서 하나의 문제를 풀어 보는 활동",
    "lead": "스터디·동아리에서 역할을 맡아 목표를 정하고 팀을 이끌어 보는 활동",
    "humanity": "사회·인문 이슈 하나를 골라 자료를 읽고, 근거를 들어 내 의견을 써 보는 활동",
    "science": "배운 과학 원리를 실생활 문제에 적용해 보는 활동",
    "art": "표현·신체 활동을 꾸준히 하고 과정을 기록해 보는 활동",
}

# ---------------------------------------------------------------------
# 1. DB (study_feature 의 DB 파일을 그대로 쓰고 테이블만 추가)
# ---------------------------------------------------------------------
_DDL = """
CREATE TABLE IF NOT EXISTS career_activities(
  id INTEGER PRIMARY KEY AUTOINCREMENT, uid TEXT, year INTEGER, title TEXT, tags TEXT,
  step1 TEXT, step2 TEXT, step3 TEXT, created_at REAL);
CREATE INDEX IF NOT EXISTS idx_ca_uid ON career_activities(uid);
"""
_ready: set = set()


@contextmanager
def _db():
    with sf._db() as con:
        path = sf._db_path()
        if path not in _ready:
            con.executescript(_DDL)
            _ready.add(path)
        yield con


def add_activity(uid: str, year: int, title: str, tags: list[str], s1: str, s2: str, s3: str) -> tuple[bool, str]:
    title = title.strip()[:60]
    s1, s2, s3 = (x.strip()[:FIELD_LIMIT] for x in (s1, s2, s3))
    if len(title) < 2:
        return False, "활동 이름을 두 글자 이상 적어주세요."
    if sf._has_pii(" ".join([title, s1, s2, s3])):
        return False, "전화번호·이메일 같은 개인정보는 적지 말아주세요."
    with _db() as con:
        n = con.execute("SELECT COUNT(*) FROM career_activities WHERE uid=?", (uid,)).fetchone()[0]
        if n >= MAX_ACTIVITIES:
            return False, f"활동은 최대 {MAX_ACTIVITIES}개까지 저장할 수 있어요. 오래된 기록을 정리해 주세요."
        con.execute(
            "INSERT INTO career_activities(uid,year,title,tags,step1,step2,step3,created_at) VALUES(?,?,?,?,?,?,?,?)",
            (uid, int(year), title, ",".join(t for t in tags if t in TAGS), s1, s2, s3, time.time()),
        )
    return True, ""


def list_activities(uid: str) -> list[dict]:
    with _db() as con:
        rows = con.execute("SELECT * FROM career_activities WHERE uid=? ORDER BY year, id", (uid,)).fetchall()
    out = []
    for r in rows:
        d = dict(r)
        d["tags"] = [t for t in (d["tags"] or "").split(",") if t in TAGS]
        d["text"] = " ".join([d["title"], d["step1"] or "", d["step2"] or "", d["step3"] or ""])
        out.append(d)
    return out


def delete_activity(uid: str, act_id: int) -> None:
    with _db() as con:  # uid 조건 때문에 본인 기록만 지울 수 있다
        con.execute("DELETE FROM career_activities WHERE id=? AND uid=?", (act_id, uid))


# ---------------------------------------------------------------------
# 2. 분석 (목표 <-> 활동 연결)
# ---------------------------------------------------------------------
def _keywords(track: str, major: str) -> list[str]:
    words: list[str] = []
    for w in re.split(r"[\s,·/]+", major or ""):
        core = re.sub(r"(공학과|공학부|공학|학과|학부|전공|과)$", "", w)  # 전기전자공학과 -> 전기전자
        if len(core) >= 2:
            words.append(core)
    words += TRACK_WORDS.get(track, [])
    return list(dict.fromkeys(words))


def analyze(acts: list[dict], track: str, major: str) -> dict:
    counts = {t: 0 for t in TAGS}
    for a in acts:
        for t in a["tags"]:
            counts[t] += 1
    target = TRACK_TAGS.get(track, [])
    words = _keywords(track, major)
    return {
        "total": len(acts),
        "counts": counts,
        "target": target,
        "missing": [t for t in target if counts[t] == 0],
        "words": words,
        "hits": [a for a in acts if words and any(w in a["text"] for w in words)],
        "expansion": sum(1 for a in acts if any(k in (a["step3"] or "") for k in EXPANSION_WORDS)),
        "by_year": [sum(1 for a in acts if a["year"] == y) for y in (1, 2, 3)],
    }


def build_prompt(acts: list[dict], user: dict) -> str:
    if not acts:
        return ""
    goal = [f"희망 계열: {user['track'] or '미정'}", f"희망 학과: {user['major'] or '미정'}"]
    if user.get("target_univ"):
        goal.append(f"목표 대학: {user['target_univ']}")
    lines = [
        "다음은 한 고등학생이 직접 기록한 학습·진로 활동이야.",
        "목표: " + " / ".join(goal),
        "",
    ]
    for i, a in enumerate(acts, 1):
        tags = ", ".join(TAGS[t] for t in a["tags"])
        lines.append(f"[활동 {i}] {a['year']}학년 · {a['title']}" + (f" ({tags})" if tags else ""))
        lines.append(f"- 탐구 계기: {a['step1'] or '-'}")
        lines.append(f"- 문제 해결: {a['step2'] or '-'}")
        lines.append(f"- 배운 점/확장: {a['step3'] or '-'}")
        lines.append("")
    lines += [
        "아래를 도와줘.",
        "1. 활동들을 관통하는 관심사와 성장 흐름을 3문장으로 정리해줘.",
        "2. 목표 학과 관점에서 이미 보여준 점과 부족한 점을 나눠서 알려줘.",
        "3. 앞으로 해볼 만한 활동(탐구·독서·실천)을 3가지, 실행 방법과 함께 제안해줘.",
        "4. 기록에 없는 활동을 만들어내거나 사실을 과장하지 말아줘.",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------
# 3. 화면
# ---------------------------------------------------------------------
def _goal_card(user: dict) -> None:
    uid = user["uid"]
    goal = " · ".join(x for x in (user["track"], user["major"], user["target_univ"]) if x)
    sf._card(
        '<div class="sf-muted">내 목표</div>'
        f'<div class="sf-title">{sf._esc(goal) if goal else "아직 목표를 정하지 않았어요"}</div>'
        '<div class="sf-muted" style="margin-top:4px;">목표를 정하면 [내 지도]가 목표에 맞춰 활동을 점검해 줘요.</div>'
    )
    with st.expander("목표 설정·수정", expanded=not user["major"]):
        with st.form("cm_goal"):
            idx = sf.TRACKS.index(user["track"]) if user["track"] in sf.TRACKS else 0
            track = st.selectbox("희망 계열", sf.TRACKS, index=idx)
            major = st.text_input("희망 학과", value=user["major"], placeholder="예: 전기전자공학과")
            univ = st.text_input("목표 대학 (선택)", value=user["target_univ"])
            if st.form_submit_button("저장", use_container_width=True):
                sf.update_profile(uid, "" if track == sf.TRACKS[0] else track, major, univ)
                sf._flash("목표를 저장했어요.")
                st.rerun()


def _render_results(query: str, results: list[dict]) -> None:
    st.markdown(f'<div class="sf-muted">“{sf._esc(query)}” 검색 결과</div>', unsafe_allow_html=True)
    shown = False
    for r in results:
        if r["status"] == "off":
            continue
        shown = True
        body = ""
        if r["status"] == "ok" and r["items"]:
            for it in r["items"]:
                summ = f'<div class="sf-muted">{sf._esc(it["summary"])}</div>' if it["summary"] else ""
                link = (f'<a href="{sf._esc(it["url"])}" target="_blank" rel="noopener">원문 보기 ↗</a>'
                        if it["url"] else "")
                body += f'<div class="sf-item"><b>{sf._esc(it["title"])}</b>{summ}{link}</div>'
        elif r["status"] == "ok":
            body = '<div class="sf-muted">관련 결과가 없어요.</div>'
        elif r["status"] == "no_key":
            body = '<div class="sf-muted">API 연결을 준비 중이에요.</div>'
        else:
            body = '<div class="sf-muted">지금은 불러오지 못했어요. 잠시 후 다시 시도해주세요.</div>'
        sf._card(f'<div class="sf-src">📚 {sf._esc(r["source"])}</div>{body}')
    if not shown:
        sf._card('<div class="sf-muted">아직 연결된 정보 사이트가 없어요. 아래 바로가기로 직접 확인해보세요.</div>')
    st.caption("정보는 각 사이트 기준이에요. 정확한 내용은 꼭 원문에서 확인하세요.")


def _tab_search(user: dict) -> None:
    with st.form("cm_search"):
        q = st.text_input("궁금한 대학 이름을 입력해보세요", placeholder="예: 서울대학교")
        go = st.form_submit_button("🔍 찾아보기", use_container_width=True)
    if go and q.strip():
        st.session_state["cm_last"] = (q.strip(), sf.search_all(q))
    if user["target_univ"] and st.button(f"🏫 {user['target_univ'][:12]} 바로 찾기", key="cm_quick"):
        st.session_state["cm_last"] = (user["target_univ"], sf.search_all(user["target_univ"]))
    last = st.session_state.get("cm_last")
    if last:
        _render_results(*last)
        st.info("알아본 학과와 내 활동이 얼마나 이어지는지는 [🗺️ 내 지도]에서 볼 수 있어요.")
    st.markdown('<div class="sf-muted" style="margin-top:10px;">원문 사이트 바로가기</div>', unsafe_allow_html=True)
    cols = st.columns(len(sf.LINKS))
    for c, (name, url) in zip(cols, sf.LINKS):
        c.link_button(name, url, use_container_width=True)


def _tab_record(user: dict) -> None:
    uid = user["uid"]
    with st.form("cm_record", clear_on_submit=True):
        st.markdown('<div class="sf-title">1분 기록</div>', unsafe_allow_html=True)
        year = st.radio("학년", [1, 2, 3], horizontal=True, format_func=lambda y: f"{y}학년")
        title = st.text_input("활동 이름", max_chars=60, placeholder="예: 교내 코딩 동아리 미니 프로젝트")
        tags = st.multiselect("태그 (여러 개 가능)", list(TAGS), format_func=TAGS.get)
        vals = {}
        for key, label, ph in STEPS:
            vals[key] = st.text_area(label, max_chars=FIELD_LIMIT, height=70, placeholder=ph)
        st.caption("실명·연락처 등 개인정보는 적지 마세요.")
        if st.form_submit_button("기록하기", use_container_width=True, type="primary"):
            ok, msg = add_activity(uid, year, title, tags, vals["step1"], vals["step2"], vals["step3"])
            if ok:
                sf._flash("활동을 기록했어요.")
                st.rerun()
            else:
                st.error(msg)

    acts = list_activities(uid)
    st.markdown(f'<div class="sf-muted">지금까지의 기록 ({len(acts)})</div>', unsafe_allow_html=True)
    for a in reversed(acts):
        chips = " ".join(f'<span class="sf-chip">{sf._esc(TAGS[t])}</span>' for t in a["tags"])
        steps = "".join(
            f'<div class="sf-muted"><b>{label}</b> {sf._esc(a[key] or "-")}</div>' for key, label, _ in STEPS
        )
        sf._card(f'<div class="sf-row"><div class="sf-post-title">{sf._esc(a["title"])}</div>'
                 f'<span class="sf-chip mint">{a["year"]}학년</span></div>{chips}{steps}')
        if st.button("삭제", key=f"cm_del_{a['id']}"):
            delete_activity(uid, a["id"])
            st.rerun()


def _tab_map(user: dict) -> None:
    acts = list_activities(user["uid"])
    if not acts:
        sf._card('<div class="sf-title">아직 그릴 지도가 없어요</div>'
                 '<div class="sf-muted">먼저 [📝 활동 기록]에서 활동을 몇 개 남겨보세요.</div>')
        return
    a = analyze(acts, user["track"], user["major"])
    total = a["total"]

    if user["track"] or user["major"]:
        pct = round(len(a["hits"]) / total * 100)
        goal = " · ".join(x for x in (user["track"], user["major"]) if x)
        st.markdown(
            f'<div class="sf-hero"><div class="sub">{sf._esc(goal)}와(과) 이어진 활동</div>'
            f'<div class="big">{len(a["hits"])}/{total}건</div>{sf._bar(pct)}'
            f'<div class="sub">활동 글에 목표 학과·계열 관련 단어가 들어간 비율이에요.</div></div>',
            unsafe_allow_html=True)
    else:
        st.info("[내 목표]에서 희망 계열과 학과를 정하면, 목표와 활동을 견주어 볼 수 있어요.")

    if a["target"]:
        rows = ""
        mx = max(1, *(a["counts"][t] for t in a["target"]))
        for t in a["target"]:
            n = a["counts"][t]
            chip = f'<span class="sf-chip">{n}건</span>' if n else '<span class="sf-chip red">비어있어요</span>'
            rows += (f'<div class="sf-row" style="margin-top:10px;"><span>{sf._esc(TAGS[t])}</span>{chip}</div>'
                     f'{sf._bar(round(n / mx * 100))}')
        sf._card(f'<div class="sf-title">{sf._esc(user["track"])} 계열 활동 균형</div>'
                 f'<div class="sf-muted">이 계열에서 자주 쓰는 태그 기준이에요.</div>{rows}')
        if a["missing"]:
            tips = "".join(
                f'<div class="sf-item"><b>{sf._esc(TAGS[t])}</b>'
                f'<div class="sf-muted">{sf._esc(SUGGEST[t])}</div></div>' for t in a["missing"][:3])
            sf._card(f'<div class="sf-title">다음에 해보면 좋은 방향</div>{tips}')
    elif user["track"] == "":
        st.caption("희망 계열을 정하면 계열별 활동 균형을 보여줘요.")

    exp_pct = round(a["expansion"] / total * 100)
    yr = " · ".join(f"{i + 1}학년 {n}건" for i, n in enumerate(a["by_year"]))
    sf._card('<div class="sf-title">이어가는 힘</div>'
             f'<div class="sf-muted">‘심화·확장·후속’처럼 이전 활동을 발전시킨 비율</div>'
             f'<div class="sf-title" style="color:#3182F6;">{exp_pct}%</div>{sf._bar(exp_pct)}'
             f'<div class="sf-muted">{a["expansion"]}건 · {yr}</div>')

    if a["hits"]:
        names = ", ".join(sf._esc(h["title"]) for h in a["hits"][:5])
        st.caption(f"목표와 이어진 활동: {names}")
    st.caption("단어·태그 일치만 보는 단순 분석이에요. 입시 평가 기준이 아니라 방향을 점검하는 참고용이에요.")


def _tab_ai(user: dict) -> None:
    acts = list_activities(user["uid"])
    if not acts:
        sf._card('<div class="sf-muted">활동을 먼저 기록하면 AI에게 물어볼 정리 글을 만들어 드려요.</div>')
        return
    picked = st.multiselect(
        "포함할 활동", [a["id"] for a in acts], default=[a["id"] for a in acts],
        format_func=lambda i: next(f"{x['year']}학년 · {x['title']}" for x in acts if x["id"] == i))
    prompt = build_prompt([a for a in acts if a["id"] in picked], user)
    if prompt:
        st.markdown('<div class="sf-title">AI에게 붙여넣을 질문</div>', unsafe_allow_html=True)
        st.code(prompt, language=None)  # 오른쪽 위 복사 버튼으로 복사
        st.caption("복사해서 사용하는 AI에 붙여넣으세요. 학교생활기록부는 선생님이 작성하는 문서라, "
                   "이 결과는 활동을 정리하고 방향을 잡는 참고용으로만 쓰는 걸 권해요.")


def page_career_map() -> None:
    user = sf._page_start()
    if not user:
        return
    st.markdown('<div class="sf-title" style="margin:4px 0 12px;">🎯 진로·대입</div>', unsafe_allow_html=True)
    _goal_card(user)
    t1, t2, t3, t4 = st.tabs(["🔎 대학·학과", "📝 활동 기록", "🗺️ 내 지도", "✨ AI 정리"])
    with t1:
        _tab_search(user)
    with t2:
        _tab_record(user)
    with t3:
        _tab_map(user)
    with t4:
        _tab_ai(user)
