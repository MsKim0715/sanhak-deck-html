/* ==========================================================
   산학 프로젝트 · 인터랙티브 웹 프레젠테이션 — 동작
   1) 화면 맞춤        : 16:9 무대 축소/확대, 세로·좁은 화면은 한 줄 흐름(reflow)
   2) 슬라이드 상태    : inactive → entering → active → exiting (중복 입력 방지)
   3) 탐색             : 키보드 · 버튼 · 휠 · 스와이프 · 목록 · 번호+Enter · 주소 #번호
   4) 아키텍처 흐름     : 다이어그램의 화살표(svg)를 읽어 데이터 패킷이 순서대로 이동
   5) 단계 하이라이트   : data-pipeline 안의 data-step 을 차례로 강조
   6) Hero · 영상 · 접근성 · 애니메이션 정지
   외부 라이브러리 없이 동작합니다.
   ========================================================== */
(() => {
'use strict';

const CONFIG = {
  wheelThreshold: 40,   // 휠 이동량 누적 기준(px)
  wheelQuiet: 220,      // 휠 관성이 멈췄다고 볼 시간(ms)
  swipe: 50,            // 스와이프 최소 거리(px)
  flowSpeed: 220,       // 데이터 패킷 속도(px/s)
  flowDwell: 160,       // 상자에서 다음 화살표로 넘어가기 전 머무는 시간(ms)
  flowRest: 1100,       // 한 바퀴 끝난 뒤 쉬는 시간(ms)
  stepTime: 650,        // 단계 하이라이트 한 칸 시간(ms)
  stepRest: 1000,       // 단계 하이라이트 한 바퀴 뒤 쉬는 시간(ms)
  videoAutoplay: true,  // 영상 슬라이드에서 자동 재생(음소거)
  explore: true,        // [초안] 다이어그램 상자를 누르면 그 상자를 지나는 흐름만 보기
  transition: 'slide',  // 'slide' = 방향에 따라 밀려 들어옴 · 'fade' = 제자리 페이드만
  lightbox: true,       // 스크린샷을 누르면 크게 보기
  tilt: true,           // 스크린샷에 마우스를 올리면 살짝 기울기
  glow: true,           // 마우스를 따라다니는 은은한 빛
  reflowWidth: 900,     // 이보다 좁거나 세로 화면이면 한 줄 흐름 배치
  reflowDesign: 640,    // 한 줄 흐름 배치의 기준 너비(px)
};

const root    = document.documentElement;
const body    = document.body;
const deck    = document.getElementById('deck');
const slides  = [...deck.querySelectorAll(':scope > .slide')];
const total   = slides.length;
const pad     = (n) => String(n).padStart(2, '0');
const ms      = (name, fallback) => {
  const v = getComputedStyle(root).getPropertyValue(name).trim();
  return v.endsWith('ms') ? parseFloat(v) : v.endsWith('s') ? parseFloat(v) * 1000 : fallback;
};
const reduceMQ = matchMedia('(prefers-reduced-motion: reduce)');
let motionOff  = false;
const motionOK = () => !motionOff && !reduceMQ.matches;

/* ── 1) 화면 맞춤 ─────────────────────────────────── */
let reflow = false;
function fit() {
  const w = innerWidth, h = innerHeight;
  const nextReflow = w < CONFIG.reflowWidth || (w < h && w < 1100);
  if (nextReflow !== reflow) { reflow = nextReflow; body.classList.toggle('is-reflow', reflow); }
  if (reflow) {
    root.style.setProperty('--z', (w / CONFIG.reflowDesign).toFixed(4));
    fitWide();
  } else {
    deck.style.setProperty('--scale', Math.min(w / 1920, h / 1080));
    document.querySelectorAll('[data-fit-zoom]').forEach((el) => { el.style.zoom = ''; el.removeAttribute('data-fit-zoom'); });
  }
}
// 한 줄 흐름에서 고정 너비 다이어그램은 통째로 줄여서 맞춤
function fitWide() {
  const avail = CONFIG.reflowDesign - 64;
  document.querySelectorAll('[data-flow-host]').forEach((el) => {
    const w = parseFloat(el.style.width) || el.offsetWidth;
    if (w > avail) { el.style.zoom = (avail / w).toFixed(4); el.setAttribute('data-fit-zoom', ''); }
  });
}

/* ── 4) 아키텍처 흐름 ───────────────────────────────── */
const SVGNS = 'http://www.w3.org/2000/svg';
const near = (p, q, d = 6) => Math.abs(p.x - q.x) <= d && Math.abs(p.y - q.y) <= d;
const px = (v) => parseFloat(v) || 0;

function findHosts(scope) {
  return [...scope.querySelectorAll('div')].filter((el) => {
    if (el.style.position !== 'relative') return false;
    const svgs = [...el.children].filter((c) => c.tagName.toLowerCase() === 'svg' && c.style.position === 'absolute' && c.querySelector(':scope > path'));
    return svgs.length >= 2 || (el.dataset.flow === 'ripple' && svgs.length >= 1);
  });
}

class FlowDiagram {
  constructor(host) {
    this.host = host;
    this.ripple = host.dataset.flow === 'ripple';
    this.once = host.dataset.play === 'once';
    this.delay = +host.dataset.delay || 0;
    this.cycle = +host.dataset.cycle || 0;   // 같은 장의 다른 다이어그램이 끝난 뒤에 시작하도록 지연(ms)   // 한 번만 재생하고 멈춤 (장에 다시 들어오면 다시 재생)   // BEFORE(기각안): 화면 하나의 변경이 결합된 페이지 · 테스트로 줄줄이 번짐
    this.segments = this.readSegments();
    this.cards = this.readCards();
    this.orient();
    this.classify();
    this.schedule();
    this.draw();
    this.lastT = 0;
  }
  readSegments() {
    const segs = [];
    [...this.host.children].forEach((svg) => {
      if (svg.tagName.toLowerCase() !== 'svg' || svg.style.position !== 'absolute') return;
      const path = svg.querySelector(':scope > path');
      if (!path) return;
      const m = (path.getAttribute('d') || '').match(/M\s*([-\d.]+)[ ,]+([-\d.]+)\s*L\s*([-\d.]+)[ ,]+([-\d.]+)/i);
      if (!m) return;
      const ox = px(svg.style.left), oy = px(svg.style.top);
      const dash = svg.style.strokeDasharray && svg.style.strokeDasharray !== 'none';
      segs.push({
        a: { x: ox + +m[1], y: oy + +m[2] }, b: { x: ox + +m[3], y: oy + +m[4] },
        marked: path.hasAttribute('marker-end'), dashed: !!dash,
        forced: svg.dataset.kind || null,   // 선마다 흐름 종류를 직접 지정 (예: data-kind="ripple" = 변경 전파)
      });
    });
    // T자 분기: 표시 없는 선의 중간에 다른 선이 붙어 있으면 그 지점에서 나눔
    let changed = true;
    while (changed) {
      changed = false;
      for (const s of segs) {
        if (s.marked) continue;
        for (const o of segs) {
          if (o === s) continue;
          for (const p of [o.a, o.b]) {
            if (near(p, s.a, 8) || near(p, s.b, 8)) continue;
            if (onSegment(p, s)) {
              segs.push({ a: { ...p }, b: { ...s.b }, marked: false, dashed: s.dashed, forced: s.forced });
              s.b = { ...p };
              changed = true; break;
            }
          }
          if (changed) break;
        }
        if (changed) break;
      }
    }
    return segs;
  }
  readCards() {
    return [...this.host.children].filter((el) => {
      if (el.tagName.toLowerCase() !== 'div' || el.style.position !== 'absolute') return false;
      if (!el.style.height || !el.style.width) return false;
      const cs = getComputedStyle(el);
      return parseFloat(cs.borderTopWidth) > 0;
    }).map((el) => ({ el, x: px(el.style.left), y: px(el.style.top), w: px(el.style.width), h: px(el.style.height) }));
  }
  cardAt(p) {
    let best = null, bestD = 16;
    for (const c of this.cards) {
      const dx = Math.max(c.x - p.x, 0, p.x - (c.x + c.w));
      const dy = Math.max(c.y - p.y, 0, p.y - (c.y + c.h));
      const d = Math.hypot(dx, dy);
      if (d <= bestD) { best = c; bestD = d; }
    }
    return best;
  }
  // 화살표가 없는 연결선은 이웃한 화살표를 보고 방향을 정함
  // 1순위: 이미 방향이 정해진 선의 "끝"에 붙어 있으면 거기서 출발 (흐름을 위에서부터 따라감)
  // 2순위: 정해진 선의 "시작"에 붙어 있으면 거기로 도착 — 반대쪽 끝이 상자에 닿은 선을 먼저 처리해 T자 분기에서 방향이 뒤집히지 않게 함
  orient() {
    const known = new Set(this.segments.filter((s) => s.marked));
    const unknown = () => this.segments.filter((s) => !known.has(s));
    const flip = (s) => { [s.a, s.b] = [s.b, s.a]; };
    const fromEnd = () => {
      for (const s of unknown()) for (const k of known) {
        if (near(s.a, k.b)) { known.add(s); return true; }
        if (near(s.b, k.b)) { flip(s); known.add(s); return true; }
      }
      return false;
    };
    const toStart = () => {
      const cands = [];
      for (const s of unknown()) for (const k of known) {
        if (near(s.b, k.a)) cands.push({ s, swap: false, card: !!this.cardAt(s.a) });
        else if (near(s.a, k.a)) cands.push({ s, swap: true, card: !!this.cardAt(s.b) });
      }
      if (!cands.length) return false;
      const c = cands.find((x) => x.card) || cands[0];
      if (c.swap) flip(c.s);
      known.add(c.s);
      return true;
    };
    while (fromEnd() || toStart()) { /* 반복 */ }
  }
  // 점선(구현 · 위임)과 그 연장선은 다른 종류의 흐름으로 표시
  classify() {
    if (this.ripple) { this.segments.forEach((s) => { s.kind = 'ripple'; }); return; }
    if (this.segments.some((s) => s.forced)) {   // 지정된 종류는 그 선과 이어지는 앞뒤 선까지 같은 종류로
      this.segments.forEach((s) => { s.kind = s.forced || (s.dashed ? 'impl' : 'call'); });
      return;
    }
    this.segments.forEach((s) => { s.kind = s.dashed ? 'impl' : 'call'; });
    let progress = true;
    while (progress) {
      progress = false;
      for (const s of this.segments) {
        if (s.kind === 'impl') continue;
        if (this.segments.some((o) => o.kind === 'impl' && (near(s.a, o.b) || near(s.a, o.a)))) { s.kind = 'impl'; progress = true; }
      }
    }
  }
  // 이어지는 화살표끼리 순서를 계산 (앞 화살표가 끝나야 다음 화살표 출발)
  schedule() {
    const S = this.segments;
    S.forEach((s) => { s.target = this.cardAt(s.b); });   // 도착 상자를 먼저 모두 정해야 앞뒤 관계를 바르게 계산
    S.forEach((s) => {
      s.len = Math.hypot(s.b.x - s.a.x, s.b.y - s.a.y);
      s.dur = Math.max(450, (s.len / CONFIG.flowSpeed) * 1000);
      s.preds = S.filter((p) => p !== s && (near(s.a, p.b, 8) || (p.target && p.target === this.cardAt(s.a))));
    });
    const memo = new Map();
    const startOf = (s, depth = 0) => {
      if (memo.has(s)) return memo.get(s);
      if (depth > 40) return 0;
      let st = 0;
      for (const p of s.preds) {
        const via = near(s.a, p.b, 8) ? 0 : CONFIG.flowDwell;
        st = Math.max(st, startOf(p, depth + 1) + p.dur + via);
      }
      memo.set(s, st);
      return st;
    };
    S.forEach((s) => { s.start = startOf(s); s.end = s.start + s.dur; });
    // 다시 계산: s.fixed 가 있으면 그 시각 이전에는 출발하지 않음
    const calc = () => {
      const m = new Map();
      const st = (s, depth = 0) => {
        if (m.has(s)) return m.get(s);
        if (depth > 40) return 0;
        let v = s.fixed ?? 0;
        for (const p of s.preds) v = Math.max(v, st(p, depth + 1) + p.dur + (near(s.a, p.b, 8) ? 0 : CONFIG.flowDwell));
        m.set(s, v); return v;
      };
      S.forEach((s) => { s.start = st(s); s.end = s.start + s.dur; });
    };
    // 곁가지 입력(앞단 없이 따로 시작하는 화살표)은 본 흐름이 같은 상자에 도착하는 순간에 맞춰 도착시킴
    // → 루프 첫 순간에는 시작 상자만 밝고, 다른 상자가 미리 강조되지 않음
    const main = S[0] && this.cardAt(S[0].a);
    const side = S.filter((s) => !s.preds.length && this.cardAt(s.a) !== main);
    side.forEach((s) => {
      const arr = S.filter((o) => o !== s && o.target && o.target === s.target && !side.includes(o)).map((o) => o.end);
      const inMain = new Set(S.filter((o) => !o.preds.length && !side.includes(o)));
      for (let grow = true; grow;) { grow = false; S.forEach((o) => { if (!inMain.has(o) && o.preds.some((p) => inMain.has(p))) { inMain.add(o); grow = true; } }); }
      const mainEnd = Math.max(0, ...[...inMain].map((o) => o.end));
      s.fixed = arr.length ? Math.max(0, Math.max(...arr) - s.dur) : mainEnd + CONFIG.flowDwell;
    });
    if (side.length) calc();
    // data-sync="sources": 출발 상자별로 차례로 재생 (위 상자의 화살표가 모두 도착한 뒤 다음 상자 출발)
    if (this.host.dataset.sync === 'sources') {
      const srcs = [...new Set(S.map((s) => this.cardAt(s.a)).filter(Boolean))].sort((p, q) => p.y - q.y || p.x - q.x);
      let at = 0;
      srcs.forEach((c) => {
        const grp = S.filter((s) => this.cardAt(s.a) === c);
        grp.forEach((s) => { s.fixed = at; });
        calc();
        at = Math.max(...grp.map((s) => s.end)) + CONFIG.flowDwell;
      });
    }
    // 변경 전파(ripple) · data-sync="rows": 같은 줄의 상자들은 동시에 도착 → 위 줄부터 한 줄씩 번지는 모습
    if (this.ripple || this.host.dataset.sync === 'rows') {
      const rows = [...new Set(S.filter((s) => s.target).map((s) => s.target.y))].sort((p, q) => p - q);
      rows.forEach((y) => {
        const row = S.filter((s) => s.target && s.target.y === y);
        const end = Math.max(...row.map((s) => s.end));
        row.forEach((s) => { s.fixed = end - s.dur; });
        calc();
      });
    }
    this.period = Math.max(...S.map((s) => s.end), 0) + CONFIG.flowRest;
    S.forEach((s) => { s.source = this.cardAt(s.a); s.succs = []; });
    S.forEach((s) => s.preds.forEach((p) => p.succs.push(s)));
    this.focusCard = null; this.rel = null;
  }
  // [탐색] 이 상자로 들어오는 앞단 흐름 + 이 상자에서 나가는 뒷단 흐름
  related(card) {
    const up = new Set(), down = new Set();
    const goUp = (s) => { if (up.has(s)) return; up.add(s); s.preds.forEach(goUp); };
    const goDown = (s) => { if (down.has(s)) return; down.add(s); s.succs.forEach(goDown); };
    this.segments.filter((s) => s.target === card).forEach(goUp);
    this.segments.filter((s) => s.source === card).forEach(goDown);
    return { all: new Set([...up, ...down]), up, down };
  }
  focus(card) {
    this.focusCard = card;
    this.rel = card ? this.related(card) : null;
    const cards = new Set(card ? [card] : []);
    if (this.rel) this.rel.all.forEach((s) => { if (s.source) cards.add(s.source); if (s.target) cards.add(s.target); });
    this.cards.forEach((c) => {
      c.dim.style.opacity = card && !cards.has(c) ? 0.66 : 0;
      c.el.setAttribute('aria-pressed', String(c === card));
    });
    if (this.labels) this.labels.forEach((l) => { l.style.opacity = card ? 0.35 : ''; });
    if (!this.running || this.done) this.renderStatic();
  }
  isOn(s) { return !this.rel || this.rel.all.has(s); }
  draw() {
    const w = px(this.host.style.width), h = px(this.host.style.height);
    const layer = document.createElementNS(SVGNS, 'svg');
    layer.setAttribute('class', 'flow-layer');
    layer.setAttribute('width', w); layer.setAttribute('height', h);
    layer.setAttribute('viewBox', `0 0 ${w} ${h}`);
    layer.setAttribute('aria-hidden', 'true');
    this.segments.forEach((s) => {
      const line = document.createElementNS(SVGNS, 'path');
      line.setAttribute('d', `M ${s.a.x} ${s.a.y} L ${s.b.x} ${s.b.y}`);
      line.setAttribute('class', `flow-trace flow-trace--${s.kind}`);
      const halo = document.createElementNS(SVGNS, 'circle');
      halo.setAttribute('r', 14); halo.setAttribute('class', `flow-halo--${s.kind}`); halo.style.opacity = 0;
      const dot = document.createElementNS(SVGNS, 'circle');
      dot.setAttribute('r', 6); dot.setAttribute('class', `flow-packet--${s.kind}`); dot.style.opacity = 0;
      layer.append(line, halo, dot);
      Object.assign(s, { line, halo, dot });
    });
    // 도착 강조는 상자 자체가 아니라 오버레이 위에 테두리를 그려서 표시
    // (상자 요소에 애니메이션을 걸면 장을 오갈 때 상자가 그려지지 않는 브라우저 문제가 있어 피함)
    this.cards.forEach((c) => {   // [탐색] 관련 없는 상자를 어둡게 덮는 판
      const dim = document.createElementNS(SVGNS, 'rect');
      dim.setAttribute('x', c.x - 1); dim.setAttribute('y', c.y - 1);
      dim.setAttribute('width', c.w + 2); dim.setAttribute('height', c.h + 2);
      dim.setAttribute('class', 'flow-dim'); dim.style.opacity = 0;
      layer.appendChild(dim); c.dim = dim;
    });
    this.cards.forEach((c) => {
      const ring = document.createElementNS(SVGNS, 'rect');
      ring.setAttribute('x', c.x - 3); ring.setAttribute('y', c.y - 3);
      ring.setAttribute('width', c.w + 6); ring.setAttribute('height', c.h + 6);
      ring.setAttribute('rx', 6); ring.setAttribute('class', 'flow-ring');
      ring.style.opacity = 0;
      layer.appendChild(ring);
      c.ring = ring; c.hit = -1e9;
    });
    if (this.segments.some((s) => s.kind === 'ripple')) {   // 변경이 닿은 상자 오른쪽 위에 "수정" 표시 (한 바퀴 동안 유지 → 고칠 곳이 몇 군데인지 보임)
      const targets = new Set(this.segments.filter((s) => s.kind === 'ripple').map((s) => s.target).filter(Boolean));
      targets.forEach((c) => {
        const g = document.createElementNS(SVGNS, 'g');
        g.setAttribute('class', 'flow-tag');
        g.setAttribute('transform', `translate(${c.x + c.w - 46} ${c.y - 12})`);
        const r = document.createElementNS(SVGNS, 'rect');
        r.setAttribute('width', 52); r.setAttribute('height', 24); r.setAttribute('rx', 12);
        const tx = document.createElementNS(SVGNS, 'text');
        tx.setAttribute('x', 26); tx.setAttribute('y', 17); tx.setAttribute('text-anchor', 'middle');
        tx.textContent = '수정';
        g.append(r, tx); layer.appendChild(g); c.tag = g;
      });
    }
    this.host.appendChild(layer);
    this.layer = layer;
    if (this.segments.some((s) => s.kind === 'impl') && this.segments.some((s) => s.kind === 'call')) {
      const lg = document.createElement('div');
      lg.className = 'flow-legend';
      lg.innerHTML = '<span><i style="background:var(--accent)"></i>호출 흐름</span><span><i style="background:var(--sand)"></i>구현 · 위임</span>';
      this.host.appendChild(lg);
    }
    this.renderStatic();
  }
  renderStatic() {   // 정지 상태: 경로만 옅게 보여 방향을 알 수 있게 (탐색 중이면 고른 흐름만 진하게)
    this.segments.forEach((s) => {
      s.line.style.opacity = this.rel ? (this.rel.all.has(s) ? 0.9 : 0) : 0.35;
      s.dot.style.opacity = 0; s.halo.style.opacity = 0;
    });
    this.cards.forEach((c) => { c.ring.style.opacity = c === this.focusCard ? 0.9 : 0; });
  }
  // 한 번 재생이 끝난 뒤의 모습: 경로는 옅게 남기고, 변경 전파(ripple)의 '수정' 표시는 그대로 둠
  finish() {
    this.segments.forEach((s) => { s.line.style.opacity = this.rel ? (this.rel.all.has(s) ? 0.9 : 0) : 0.35; s.dot.style.opacity = 0; s.halo.style.opacity = 0; });
    this.cards.forEach((c) => { c.ring.style.opacity = c === this.focusCard ? 0.9 : 0; });
  }
  reset() {
    this.done = false;
    this.segments.forEach((s) => { s.line.style.opacity = 0; s.dot.style.opacity = 0; s.halo.style.opacity = 0; });
    this.cards.forEach((c) => { c.hit = -1e9; c.ring.style.opacity = 0; c.tagOn = false; if (c.tag) c.tag.classList.remove('is-on'); });
    this.lastT = 0;
  }
  frame(elapsed) {
    let t;
    if (this.cycle) {   // 같은 장의 다이어그램끼리 한 주기를 나눠 씀: 앞 다이어그램이 끝나면 다음 다이어그램 재생 → 함께 처음부터 반복
      t = (elapsed % this.cycle) - this.delay;
      if (t < 0) { if (!this.idle) { this.reset(); this.idle = true; } return; }
      this.idle = false;
    } else {
      elapsed -= this.delay;
      if (elapsed < 0) return;
      if (this.once) {
        if (this.done) return;
        if (elapsed >= this.period - CONFIG.flowRest + 900) { this.done = true; this.finish(); return; }
      }
      t = elapsed % this.period;
    }
    const wrapped = t < this.lastT;
    for (const s of this.segments) {
      let o = 0, trace = 0;
      if (t >= s.start && t < s.end) {
        const k = (t - s.start) / s.dur;
        const e = k < 0.5 ? 2 * k * k : 1 - Math.pow(-2 * k + 2, 2) / 2;   // easeInOutQuad
        const x = s.a.x + (s.b.x - s.a.x) * e, y = s.a.y + (s.b.y - s.a.y) * e;
        s.dot.setAttribute('cx', x); s.dot.setAttribute('cy', y);
        s.halo.setAttribute('cx', x); s.halo.setAttribute('cy', y);
        o = k < 0.12 ? k / 0.12 : k > 0.88 ? (1 - k) / 0.12 : 1;
        trace = 0.65;
      } else if (t >= s.end) {
        trace = Math.max(0, 0.65 - (t - s.end) / 900);   // 지나간 경로는 서서히 사라짐
      }
      if (!this.isOn(s)) { o = 0; trace = 0; }
      else if (this.rel) trace = Math.max(trace, 0.3);   // 탐색 중: 고른 흐름의 경로는 계속 보이게
      s.dot.style.opacity = o; s.halo.style.opacity = o * 0.3; s.line.style.opacity = trace;
      // 도착한 상자를 살짝 강조
      if (!wrapped && this.isOn(s) && this.lastT < s.end && t >= s.end && s.target) { s.target.hit = t; s.target.ring.setAttribute('data-kind', s.kind); }
    }
    this.cards.forEach((c) => { if (!c.tag) return; if (wrapped) c.tagOn = false; else if (t - c.hit >= 0 && t - c.hit < 1e8) c.tagOn = true; c.tag.classList.toggle('is-on', !!c.tagOn); });
    for (const c of this.cards) {   // 도착한 상자 테두리: 0.7초 동안 올라왔다 사라짐
      const d = wrapped ? 1e9 : t - c.hit;
      c.ring.style.opacity = c === this.focusCard ? 0.9 : d >= 0 && d < 700 ? (d < 200 ? d / 200 : 1 - (d - 200) / 500) * 0.9 : 0;
    }
    this.lastT = t;
  }
}
function onSegment(p, s) {
  const minX = Math.min(s.a.x, s.b.x) - 2.5, maxX = Math.max(s.a.x, s.b.x) + 2.5;
  const minY = Math.min(s.a.y, s.b.y) - 2.5, maxY = Math.max(s.a.y, s.b.y) + 2.5;
  if (p.x < minX || p.x > maxX || p.y < minY || p.y > maxY) return false;
  const cross = Math.abs((s.b.x - s.a.x) * (p.y - s.a.y) - (s.b.y - s.a.y) * (p.x - s.a.x));
  return cross / (Math.hypot(s.b.x - s.a.x, s.b.y - s.a.y) || 1) < 2.5;
}

/* ── 5) 단계 하이라이트 ───────────────────────────── */
class Pipeline {
  constructor(el) {
    this.steps = [...el.querySelectorAll('[data-step]')];
    this.arrows = [...el.querySelectorAll('[data-step-arrow]')];
    this.period = this.steps.length * CONFIG.stepTime + CONFIG.stepRest;
    this.once = el.dataset.play === 'once';
    this.last = -2;
  }
  frame(elapsed) {
    // 기본은 반복 · data-play="once" 이면 한 번만 진행하고 모든 단계를 '지나감' 상태로 둠 (장에 다시 들어오면 다시 재생)
    const idx = this.once ? Math.min(Math.floor(elapsed / CONFIG.stepTime), this.steps.length)
                          : Math.floor((elapsed % this.period) / CONFIG.stepTime);
    if (idx === this.last) return;
    this.last = idx;
    this.steps.forEach((s, i) => { s.classList.toggle('is-lit', i === idx); s.classList.toggle('is-passed', i < idx); });
    this.arrows.forEach((a, i) => a.classList.toggle('is-passed', i < idx));
  }
  reset() { this.last = -2; this.steps.forEach((s) => s.classList.remove('is-lit', 'is-passed')); this.arrows.forEach((a) => a.classList.remove('is-passed')); }
}

/* 슬라이드별 반복 애니메이션 묶음 */
const loops = new Map();   // slide → { flows, pipes, t0 }
function loopsFor(slide) {
  if (!loops.has(slide)) {
    const flows = findHosts(slide).filter((h) => h.dataset.flow !== 'off').map((h) => (h._flow = new FlowDiagram(h)));
    const pipes = [...slide.querySelectorAll('[data-pipeline]')].map((p) => new Pipeline(p));
    loops.set(slide, { flows, pipes, t0: 0, running: false });
    const live = flows.filter((f) => !f.ripple);
    if (CONFIG.explore && live.length) setupExplore(slide, live);
  }
  return loops.get(slide);
}

/* ── [초안] 다이어그램 탐색: 상자를 누르면 그 상자를 지나는 흐름만 남김 ──
   PPT에서는 미리 정한 애니메이션만 재생되지만, 여기서는 발표 중 질문이 나오면
   그 자리에서 원하는 구성요소를 눌러 앞단·뒷단 흐름을 바로 보여 줄 수 있습니다. */
const cardName = (el) => (el.querySelector('b')?.textContent || el.textContent).trim().replace(/\s+/g, ' ');
function setupExplore(slide, flows) {
  const main = slide.querySelector('main');
  const chip = document.createElement('div');
  chip.className = 'explore-chip';
  chip.setAttribute('aria-live', 'polite');
  const idle = '<i></i>다이어그램의 상자를 누르면, 그 상자를 지나는 흐름만 볼 수 있어요';
  chip.innerHTML = idle;
  // 본문(main)은 장 전환 때 옆으로 움직이므로, 안내 칩은 슬라이드 바탕에 고정하고 페이드만 적용
  (main.parentElement || slide).appendChild(chip);
  const clear = () => { flows.forEach((f) => f.focus(null)); chip.innerHTML = idle; chip.classList.remove('is-on'); };
  const pick = (flow, card) => {
    if (flow.focusCard === card) { clear(); return; }
    flows.forEach((f) => f !== flow && f.focus(null));
    flow.focus(card);
    const linked = new Set();
    flow.rel.all.forEach((sg) => { if (sg.source) linked.add(sg.source); if (sg.target) linked.add(sg.target); });
    linked.delete(card);
    chip.innerHTML = `<i></i><b>${cardName(card.el)}</b> 기준 흐름 · 연결된 구성요소 ${linked.size}개<span>다시 누르거나 Esc로 해제</span>`;
    chip.classList.add('is-on');
  };
  flows.forEach((flow) => {
    flow.labels = [...flow.host.children].filter((el) => el.tagName === 'DIV' && !flow.cards.some((c) => c.el === el) && el.className !== 'flow-legend');
    flow.cards.forEach((card) => {
      const el = card.el;
      el.setAttribute('data-flow-card', '');
      el.setAttribute('tabindex', '0');
      el.setAttribute('role', 'button');
      el.setAttribute('aria-pressed', 'false');
      el.setAttribute('aria-label', `${cardName(el)} 흐름 보기`);
      el.addEventListener('click', (e) => { e.stopPropagation(); pick(flow, card); });
      el.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); e.stopPropagation(); pick(flow, card); } });
    });
    flow.host.addEventListener('click', () => { if (flow.focusCard) clear(); });
  });
  slide._exploreClear = clear;
}
let rafId = 0;
function tick(now) {
  rafId = 0;
  let any = false;
  loops.forEach((L) => {
    if (!L.running) return;
    any = true;
    const e = now - L.t0;
    L.flows.forEach((f) => f.frame(e));
    L.pipes.forEach((p) => p.frame(e));
  });
  if (any) rafId = requestAnimationFrame(tick);
}
function startLoops(slide) {
  const L = loopsFor(slide);
  if (!L.flows.length && !L.pipes.length) return;
  if (!motionOK()) { L.flows.forEach((f) => f.renderStatic()); L.pipes.forEach((p) => p.reset()); L.running = false; return; }
  L.t0 = performance.now(); L.running = true;
  L.flows.forEach((f) => f.reset());
  if (!rafId) rafId = requestAnimationFrame(tick);
}
function stopLoops(slide) {
  const L = loops.get(slide);
  if (!L) return;
  slide._exploreClear?.();
  L.running = false;
  L.flows.forEach((f) => f.reset());
  L.pipes.forEach((p) => p.reset());
}

/* ── 2) 슬라이드 상태 · 이동 ───────────────────────── */
let current = -1, dest = -1, busy = false, queued = null, timers = [];
const later = (fn, t) => { const id = setTimeout(fn, t); timers.push(id); return id; };

function setState(slide, state) {
  slide.dataset.state = state;
  const hidden = state === 'inactive' || state === 'exiting';
  slide.inert = hidden;
  slide.setAttribute('aria-hidden', hidden ? 'true' : 'false');
}

function go(index, opts = {}) {
  if (lb) return;   // 크게 보기 중에는 장을 넘기지 않음 (휠 · 스와이프 포함)
  index = Math.max(0, Math.min(total - 1, index));
  if (busy) { if (queued === null && index !== dest) queued = index; return; }   // 전환 중 입력은 한 번만 보관, 나머지는 무시
  if (index === current) return;
  busy = true; dest = index;
  deck.dataset.dir = index > current ? 'next' : 'prev';   // 들어오고 나가는 방향
  const instant = opts.instant || !motionOK();
  const out = instant ? 0 : ms('--fade-out', 450);
  const inn = instant ? 0 : Math.max(ms('--fade-in', 700), CONFIG.transition === 'slide' ? ms('--move-in', 800) : 0);
  const prev = slides[current];

  const enter = () => {
    current = index;
    const next = slides[index];
    setState(next, 'entering');
    onEnter(next);
    updateHud();
    later(() => {
      setState(next, 'active');
      busy = false;
      if (queued !== null) { const q = queued; queued = null; if (q !== current) go(q); }
    }, inn);
  };

  if (prev) {
    setState(prev, 'exiting');
    onLeave(prev);
    later(() => { setState(prev, 'inactive'); enter(); }, out);
  } else {
    enter();
  }
}
// 전환 중이면 도착할 장을 기준으로 한 칸만 예약 (연타해도 여러 장을 건너뛰지 않음)
const base = () => (busy ? dest : current);
const next = () => go(base() + 1);
const prev = () => go(base() - 1);

function onEnter(slide) {
  if (reflow) slide.scrollTop = 0;
  startLoops(slide);
  slide.querySelectorAll('.player video').forEach((v) => {
    v.currentTime = 0;
    if (CONFIG.videoAutoplay && motionOK()) later(() => { if (slides[current] === slide) v.play().catch(() => {}); }, 600);
  });
}
function onLeave(slide) {
  stopLoops(slide);
  slide.querySelectorAll('.zoomable').forEach((im) => { im.style.transform = ''; im.classList.remove('is-tilting'); });
  slide.querySelectorAll('video').forEach((v) => v.pause());
}

/* HUD · 진행률 · 스크린 리더 안내 */
const $ = (id) => document.getElementById(id);
function updateHud() {
  const s = slides[current];
  $('pageNow').textContent = pad(current + 1);
  $('hudProject').textContent = s.dataset.project || '';
  $('progress').style.width = ((current + 1) / total) * 100 + '%';
  $('prev').disabled = current === 0;
  $('next').disabled = current === total - 1;
  $('live').textContent = `${current + 1} / ${total} — ${s.dataset.title}`;
  document.title = `${pad(current + 1)} · ${s.dataset.title} — 산학 프로젝트`;
  if (location.hash !== '#' + (current + 1)) history.replaceState(null, '', '#' + (current + 1));
  indexButtons.forEach((b, i) => b.setAttribute('aria-current', i === current ? 'true' : 'false'));
}

/* ── 3) 입력 ──────────────────────────────────────── */
let typed = '';
document.addEventListener('keydown', (e) => {
  if (lb && lb.player) {   // 영상 크게 보기: Esc = 닫기, Space = 재생 / 일시정지 (방향키는 재생 위치 막대가 처리)
    if (e.key === 'Escape') { e.preventDefault(); closeLightbox(); }
    else if (e.key === ' ' && !(e.target.closest && e.target.closest('button, .player__track'))) { e.preventDefault(); lb.toggle(); }
    return;
  }
  if (lb) { if (['Escape', 'Enter', ' ', 'ArrowLeft', 'ArrowRight', 'PageUp', 'PageDown'].includes(e.key)) { e.preventDefault(); closeLightbox(); } return; }
  if (!indexEl.hidden) {
    if (e.key === 'Escape' || e.key === 'g' || e.key === 'G') { e.preventDefault(); closeIndex(); }
    if (e.key === 'Tab') trapFocus(e);
    return;
  }
  if (e.target.closest && e.target.closest('.player__track')) return;
  if (e.altKey || e.ctrlKey || e.metaKey) return;
  const k = e.key;
  if (k === 'Escape' && slides[current]?._exploreClear) { slides[current]._exploreClear(); return; }
  if ((k === 'Enter' || k === ' ') && e.target.closest && e.target.closest('[data-flow-card], [data-nav-go]')) return;
  if (['ArrowRight', 'PageDown', ' '].includes(k) || (k === 'ArrowDown' && !reflow)) { e.preventDefault(); next(); }
  else if (['ArrowLeft', 'PageUp'].includes(k) || (k === 'ArrowUp' && !reflow)) { e.preventDefault(); prev(); }
  else if (k === 'Home') { e.preventDefault(); go(0); }
  else if (k === 'End') { e.preventDefault(); go(total - 1); }
  else if (k === 'g' || k === 'G') { e.preventDefault(); openIndex(); }
  else if (k === 'p' || k === 'P') { e.preventDefault(); toggleMotion(); }
  else if (k === 'f' || k === 'F') {
    if (document.fullscreenElement) document.exitFullscreen(); else root.requestFullscreen?.().catch(() => {});
  }
  else if (/^[0-9]$/.test(k)) { typed = (typed + k).slice(-3); }
  else if (k === 'Enter' && typed) { go(parseInt(typed, 10) - 1); typed = ''; }
});

/* 왼쪽 목차: 항목을 누르면 그 섹션의 첫 장으로 이동
   각 장에서 강조된 목차 항목(=현재 섹션)을 읽어, 섹션마다 처음 나오는 장을 목적지로 삼음 */
(() => {
  const navOf = (s) => s.querySelector(':scope aside nav, :scope > div > aside nav');
  const activeIdx = (nav) => [...nav.children].findIndex((d) => d.hasAttribute('style'));
  const firstOf = [];
  slides.forEach((s, i) => {
    const nav = navOf(s); if (!nav) return;
    const a = activeIdx(nav);
    if (a >= 0 && firstOf[a] === undefined) firstOf[a] = i;
  });
  slides.forEach((s) => {
    const nav = navOf(s); if (!nav) return;
    [...nav.children].forEach((item, j) => {
      const to = firstOf[j]; if (to === undefined) return;
      item.dataset.navGo = to;
      item.setAttribute('role', 'link');
      item.tabIndex = 0;
      item.setAttribute('aria-label', `${item.textContent.replace(/\s+/g, ' ').trim()} 섹션으로 이동 (${to + 1}장)`);
      const jump = (e) => { e.preventDefault(); e.stopPropagation(); go(to); };
      item.addEventListener('click', jump);
      item.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') jump(e); });
    });
  });
})();

$('next').addEventListener('click', next);
$('prev').addEventListener('click', prev);
$('pageTotal').textContent = pad(total);

// 휠: 관성 스크롤이 멈출 때까지 한 번만 이동
let wheelAcc = 0, wheelLocked = false, wheelTimer = 0;
addEventListener('wheel', (e) => {
  if (e.ctrlKey || !indexEl.hidden) return;
  if (e.target.closest && e.target.closest('.index')) return;
  if (reflow) {   // 한 줄 흐름: 장 안에서 먼저 스크롤, 끝에 닿았을 때만 이동
    const s = slides[current];
    const atTop = s.scrollTop <= 0, atBottom = s.scrollTop + s.clientHeight >= s.scrollHeight - 2;
    if ((e.deltaY > 0 && !atBottom) || (e.deltaY < 0 && !atTop)) return;
  }
  clearTimeout(wheelTimer);
  wheelTimer = setTimeout(() => { wheelLocked = false; wheelAcc = 0; }, CONFIG.wheelQuiet);
  if (wheelLocked) return;
  wheelAcc += Math.abs(e.deltaY) > Math.abs(e.deltaX) ? e.deltaY : e.deltaX;
  if (Math.abs(wheelAcc) >= CONFIG.wheelThreshold) {
    wheelLocked = true;
    (wheelAcc > 0 ? next : prev)();
    wheelAcc = 0;
  }
}, { passive: true });

// 터치: 좌우 스와이프 (넓은 화면에서는 위아래도)
let touch = null;
addEventListener('touchstart', (e) => {
  body.classList.add('is-touch');
  if (e.touches.length !== 1 || e.target.closest('.player__track, .index')) { touch = null; return; }
  touch = { x: e.touches[0].clientX, y: e.touches[0].clientY, t: Date.now() };
}, { passive: true });
addEventListener('touchend', (e) => {
  if (!touch) return;
  const dx = e.changedTouches[0].clientX - touch.x, dy = e.changedTouches[0].clientY - touch.y;
  const quick = Date.now() - touch.t < 800;
  touch = null;
  if (!quick) return;
  if (Math.abs(dx) > CONFIG.swipe && Math.abs(dx) > Math.abs(dy) * 1.4) (dx < 0 ? next : prev)();
  else if (!reflow && Math.abs(dy) > CONFIG.swipe * 1.4 && Math.abs(dy) > Math.abs(dx) * 1.4) (dy < 0 ? next : prev)();
}, { passive: true });

addEventListener('hashchange', () => {
  const n = parseInt(location.hash.slice(1), 10);
  if (Number.isFinite(n) && n - 1 !== current) go(n - 1);
});
addEventListener('resize', fit);

/* 슬라이드 목록 */
const indexEl = $('index');
const indexList = $('indexList');
const indexButtons = slides.map((s, i) => {
  const li = document.createElement('li');
  const b = document.createElement('button');
  b.type = 'button';
  const chap = s.dataset.kind === 'chapter';
  b.innerHTML = `<span class="n">${pad(i + 1)}</span><span class="${chap ? 'chap' : ''}">${s.dataset.title}<small>${s.dataset.project || ''}</small></span>`;
  b.addEventListener('click', () => { closeIndex(); go(i); });
  li.appendChild(b); indexList.appendChild(li);
  return b;
});
let lastFocus = null;
function openIndex() {
  lastFocus = document.activeElement;
  indexEl.hidden = false;
  (indexButtons[current] || indexButtons[0]).focus();
  indexButtons[current]?.scrollIntoView({ block: 'center' });
}
function closeIndex() { indexEl.hidden = true; (lastFocus || $('openIndex')).focus?.(); }
function trapFocus(e) {
  const f = [...indexEl.querySelectorAll('button')];
  const first = f[0], last = f[f.length - 1];
  if (e.shiftKey && document.activeElement === first) { e.preventDefault(); last.focus(); }
  else if (!e.shiftKey && document.activeElement === last) { e.preventDefault(); first.focus(); }
}
$('openIndex').addEventListener('click', openIndex);
$('closeIndex').addEventListener('click', closeIndex);
indexEl.addEventListener('click', (e) => { if (e.target === indexEl) closeIndex(); });

/* 애니메이션 정지 · 재개 */
function toggleMotion(force) {
  motionOff = typeof force === 'boolean' ? force : !motionOff;
  body.classList.toggle('is-motion-off', motionOff);
  $('motion').setAttribute('aria-pressed', String(motionOff));
  $('motion').setAttribute('aria-label', motionOff ? '애니메이션 다시 재생' : '애니메이션 일시정지');
  const s = slides[current];
  if (!s) return;
  if (motionOff) { const L = loops.get(s); if (L) { L.running = false; L.flows.forEach((f) => f.renderStatic()); } s.querySelectorAll('video').forEach((v) => v.pause()); }
  else { startLoops(s); }
}
$('motion').addEventListener('click', () => toggleMotion());
reduceMQ.addEventListener?.('change', () => { const s = slides[current]; if (s) { stopLoops(s); startLoops(s); } });

/* 표지 Hero: 마우스에 따라 사진이 아주 조금 움직임 */
let parallaxRaf = 0;
addEventListener('pointermove', (e) => {
  if (reflow || !motionOK() || e.pointerType === 'touch') return;
  const hero = slides[current]?.querySelector('[data-hero] img');
  if (!hero || parallaxRaf) return;
  parallaxRaf = requestAnimationFrame(() => {
    parallaxRaf = 0;
    hero.style.setProperty('--px', ((e.clientX / innerWidth - 0.5) * -18).toFixed(1) + 'px');
    hero.style.setProperty('--py', ((e.clientY / innerHeight - 0.5) * -12).toFixed(1) + 'px');
  });
});

/* ── 7) 웹에서만 되는 움직임 ───────────────────────────
   · 스크린샷 크게 보기 (누른 자리에서 화면 가득 커졌다가 제자리로)
   · 스크린샷 기울기 (마우스 위치를 따라 살짝 3D로 기울어짐)
   · 마우스를 따라다니는 빛, 챕터 배경 숫자 패럴랙스 */
if (CONFIG.transition === 'fade') body.classList.add('is-fade-only');
const zoomables = [...deck.querySelectorAll('main img')].filter((im) => !im.closest('[data-diag], [data-hero], .player'));
if (CONFIG.lightbox || CONFIG.tilt) zoomables.forEach((im) => im.classList.add('zoomable'));

let lb = null;
function fitRect(nw, nh) {
  const mw = innerWidth * 0.92, mh = innerHeight * 0.84;
  const k = Math.min(mw / nw, mh / nh, 1);   // 원본보다 크게 늘리지 않음 (흐려짐 방지)
  const w = nw * k, h = nh * k;
  return { left: (innerWidth - w) / 2, top: (innerHeight - h) / 2 - innerHeight * 0.02, width: w, height: h };
}
const rectOf = (el) => { const r = el.getBoundingClientRect(); return { left: r.left, top: r.top, width: r.width, height: r.height }; };
const px4 = (r) => ({ left: r.left + 'px', top: r.top + 'px', width: r.width + 'px', height: r.height + 'px' });
function openLightbox(img) {
  if (lb) return;
  img.style.transform = ''; img.classList.remove('is-tilting');
  const from = rectOf(img);
  const to = fitRect(img.naturalWidth || from.width, img.naturalHeight || from.height);
  const wrap = document.createElement('div');
  wrap.className = 'lightbox'; wrap.setAttribute('role', 'dialog'); wrap.setAttribute('aria-label', img.alt || '이미지 크게 보기');
  wrap.innerHTML = '<div class="lightbox__bg"></div><img class="lightbox__img" alt=""><p class="lightbox__cap"></p>';
  const big = wrap.querySelector('.lightbox__img');
  big.src = img.currentSrc || img.src; big.alt = img.alt;
  Object.assign(big.style, px4(from));
  wrap.querySelector('.lightbox__cap').textContent = img.alt || '';
  document.body.appendChild(wrap);
  img.style.visibility = 'hidden';
  const dur = motionOK() ? 560 : 0;
  big.animate([px4(from), px4(to)], { duration: dur, easing: 'cubic-bezier(0.16, 1, 0.3, 1)', fill: 'forwards' });
  wrap.querySelector('.lightbox__bg').animate([{ opacity: 0 }, { opacity: 1 }], { duration: dur * 0.8, fill: 'forwards' });
  wrap.querySelector('.lightbox__cap').animate([{ opacity: 0 }, { opacity: 1 }], { duration: dur, delay: dur * 0.5, fill: 'forwards' });
  wrap.addEventListener('click', closeLightbox);
  lb = { wrap, big, img, to };
}
// 영상: 복사본을 만들지 않고 플레이어를 그대로 화면 위로 옮겨 키움 → 재생이 끊기지 않고, 재생 · 탐색 버튼도 그대로 사용
function openVideoBox(player, toggle) {
  if (lb) return;
  const video = player.querySelector('video');
  const from = rectOf(player);
  const nw = video.videoWidth || 16, nh = video.videoHeight || 9;
  const k = Math.min((innerWidth * 0.92) / nw, (innerHeight * 0.84) / nh);   // 영상은 화면에 맞춰 키움
  const to = { left: (innerWidth - nw * k) / 2, top: (innerHeight - nh * k) / 2, width: nw * k, height: nh * k };
  const wrap = document.createElement('div');
  wrap.className = 'lightbox lightbox--video'; wrap.setAttribute('role', 'dialog'); wrap.setAttribute('aria-label', '영상 크게 보기');
  wrap.innerHTML = '<div class="lightbox__bg"></div>';
  document.body.appendChild(wrap);
  const holder = document.createElement('div');   // 원래 자리를 지키는 빈 칸 (닫을 때 이 자리로 돌아옴)
  const css = player.style.cssText;
  holder.style.cssText = css;
  const playing = !video.paused;
  player.replaceWith(holder);
  wrap.appendChild(player);
  if (playing && video.paused) video.play().catch(() => {});
  player.classList.add('is-zoomed');
  Object.assign(player.style, px4(from));
  const dur = motionOK() ? 560 : 0;
  player.animate([px4(from), px4(to)], { duration: dur, easing: 'cubic-bezier(0.16, 1, 0.3, 1)', fill: 'forwards' });
  wrap.querySelector('.lightbox__bg').animate([{ opacity: 0 }, { opacity: 1 }], { duration: dur * 0.8, fill: 'forwards' });
  wrap.addEventListener('click', (e) => { if (!e.target.closest('.player')) closeLightbox(); });   // 영상 밖을 누르면 닫힘
  lb = { wrap, player, holder, css, to, toggle };
}
function closeVideoBox() {
  const { wrap, player, holder, css, to } = lb;
  const video = player.querySelector('video');
  const dur = motionOK() ? 420 : 0;
  const a = player.animate([px4(to), px4(rectOf(holder))], { duration: dur, easing: 'cubic-bezier(0.4, 0, 0.2, 1)', fill: 'forwards' });
  wrap.querySelector('.lightbox__bg').animate([{ opacity: 1 }, { opacity: 0 }], { duration: dur, fill: 'forwards' });
  const done = () => {
    const playing = !video.paused;
    player.getAnimations().forEach((x) => x.cancel());
    player.classList.remove('is-zoomed');
    player.style.cssText = css;
    holder.replaceWith(player);
    if (playing && video.paused) video.play().catch(() => {});
    wrap.remove(); lb = null;
  };
  if (!dur) { done(); return; }
  let finished = false;
  const once = () => { if (!finished) { finished = true; done(); } };
  a.onfinish = once;
  setTimeout(once, dur + 100);   // 애니메이션 종료 이벤트가 오지 않아도(탭 전환 등) 제자리로 복구
}
function closeLightbox() {
  if (!lb || lb.closing) return;
  lb.closing = true;
  if (lb.player) { closeVideoBox(); return; }
  const { wrap, big, img, to } = lb;
  const back = rectOf(img);
  const dur = motionOK() ? 420 : 0;
  big.animate([px4(to), px4(back)], { duration: dur, easing: 'cubic-bezier(0.4, 0, 0.2, 1)', fill: 'forwards' });
  const a = wrap.querySelector('.lightbox__bg').animate([{ opacity: 1 }, { opacity: 0 }], { duration: dur, fill: 'forwards' });
  wrap.querySelector('.lightbox__cap').style.display = 'none';
  const done = () => { img.style.visibility = ''; wrap.remove(); lb = null; };
  if (dur) a.onfinish = done; else done();
}
if (CONFIG.lightbox) zoomables.forEach((im) => {
  im.setAttribute('tabindex', '0');
  im.setAttribute('role', 'button');
  im.addEventListener('click', (e) => { e.stopPropagation(); openLightbox(im); });
  im.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); e.stopPropagation(); openLightbox(im); } });
});
if (CONFIG.tilt) zoomables.forEach((im) => {
  im.addEventListener('pointermove', (e) => {
    if (reflow || !motionOK() || e.pointerType === 'touch') return;
    const r = im.getBoundingClientRect();
    const x = (e.clientX - r.left) / r.width - 0.5, y = (e.clientY - r.top) / r.height - 0.5;
    im.classList.add('is-tilting');
    im.style.transform = `perspective(1200px) rotateX(${(-y * 5).toFixed(2)}deg) rotateY(${(x * 6).toFixed(2)}deg) scale(1.02)`;
  });
  im.addEventListener('pointerleave', () => { im.classList.remove('is-tilting'); im.style.transform = ''; });
});

const glow = document.createElement('div');
glow.className = 'glow'; glow.setAttribute('aria-hidden', 'true');
if (CONFIG.glow) document.body.appendChild(glow);
let glowRaf = 0, lastPointer = null;
addEventListener('pointermove', (e) => {
  if (e.pointerType === 'touch') return;
  lastPointer = e;
  if (glowRaf) return;
  glowRaf = requestAnimationFrame(() => {
    glowRaf = 0;
    const p = lastPointer;
    body.classList.add('has-pointer');
    glow.style.setProperty('--mx', p.clientX + 'px');
    glow.style.setProperty('--my', p.clientY + 'px');
    // 챕터 배경 숫자: 마우스 반대쪽으로 천천히
    const ghost = slides[current]?.querySelector('.chapter__ghost');
    if (ghost && motionOK() && !reflow) {
      ghost.style.setProperty('--gx', ((p.clientX / innerWidth - 0.5) * -60).toFixed(1) + 'px');
      ghost.style.setProperty('--gy', ((p.clientY / innerHeight - 0.5) * -40).toFixed(1) + 'px');
    }
  });
});
document.addEventListener('pointerleave', () => body.classList.remove('has-pointer'));

/* ── 6) 영상 플레이어 ─────────────────────────────── */
document.querySelectorAll('.player').forEach((player) => {
  const video = player.querySelector('video');
  const track = player.querySelector('.player__track');
  const fill  = player.querySelector('.player__fill');
  const knob  = player.querySelector('.player__knob');
  const cur   = player.querySelector('.player__current');
  const dur   = player.querySelector('.player__duration');
  const fmt = (sec) => { const s = Math.max(0, Math.floor(sec || 0)); return pad(Math.floor(s / 60)) + ':' + pad(s % 60); };
  const toggle = () => (video.paused ? video.play().catch(() => {}) : video.pause());
  const render = () => {
    const r = video.duration ? video.currentTime / video.duration : 0;
    fill.style.width = knob.style.left = r * 100 + '%';
    cur.textContent = fmt(video.currentTime);
  };
  video.addEventListener('timeupdate', render);
  video.addEventListener('loadedmetadata', () => { dur.textContent = fmt(video.duration); render(); });
  video.addEventListener('play',  () => player.classList.add('is-playing'));
  video.addEventListener('pause', () => player.classList.remove('is-playing'));
  // 영상을 누르면 크게 보기 (이미지와 같은 동작) · 크게 본 상태에서 누르면 재생 / 일시정지
  const zoomed = () => lb && lb.player === player;
  video.addEventListener('click', (e) => {
    e.stopPropagation();
    if (!CONFIG.lightbox || zoomed()) toggle(); else openVideoBox(player, toggle);
  });
  const zoomBtn = player.querySelector('.player__zoom');
  if (zoomBtn && !CONFIG.lightbox) zoomBtn.hidden = true;
  zoomBtn?.addEventListener('click', (e) => { e.stopPropagation(); if (zoomed()) closeLightbox(); else openVideoBox(player, toggle); });
  player.querySelector('.player__big').addEventListener('click', toggle);
  player.querySelector('.player__toggle').addEventListener('click', toggle);
  const seek = (e) => {
    const rect = track.getBoundingClientRect();
    const r = Math.min(1, Math.max(0, (e.clientX - rect.left) / rect.width));
    if (video.duration) video.currentTime = r * video.duration;
    render();
  };
  track.addEventListener('pointerdown', (e) => { track.setPointerCapture(e.pointerId); track.dataset.drag = '1'; seek(e); });
  track.addEventListener('pointermove', (e) => { if (track.dataset.drag) seek(e); });
  track.addEventListener('pointerup', () => { delete track.dataset.drag; });
  track.addEventListener('keydown', (e) => {
    if (e.key === 'ArrowRight') video.currentTime += 5;
    if (e.key === 'ArrowLeft')  video.currentTime -= 5;
  });
});

/* ── 시작 ─────────────────────────────────────────── */
slides.forEach((s) => { setState(s, 'inactive'); findHosts(s).forEach((h) => h.setAttribute('data-flow-host', '')); });
fit();
const start = () => {
  const n = parseInt(location.hash.slice(1), 10);
  go(Number.isFinite(n) ? n - 1 : 0, { instant: false });
};
(document.fonts?.ready ?? Promise.resolve()).then(start, start);

// 디버그 · 테스트용
window.deckState = () => ({ current, busy, queued, states: slides.map((s) => s.dataset.state) });
})();
