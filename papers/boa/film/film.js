// Fast Coalgebraic Bisimilarity Minimization: the video: the film's scripts in one file, made by tools/web.py.

// ==== ../src/engine.js ====
// A small deterministic animation engine: every visual property is a function of time, so any frame can be
// rendered by seek(t). Scenes are built once; seek() applies the values. No CSS transitions, no timers.
'use strict';

const W = 1920, H = 1080;

// ---- palette (one meaning per colour, used the same way in every scene) -----------------------------------
// Three rooms: 'paper' (the film's: a cream page, ink type), 'warm' (a warm dark room, cream type) and 'night' (the
// first cut's cold navy). ?theme=NAME picks one; scenes only ever use the names below, so they follow.
const THEMES = {
  night: { bg: '#0a0d13', ink: '#e9edf3', code: '#d5dce7', dim: '#7d889b', faint: '#39424f', line: '#232b38', key: '#8493aa',
    pat: '#f6c356', bind: '#5ed3f3', good: '#62d69a', bad: '#ff6f61', outer: '#b8a6ff', panel: '#111722',
    glow1: '#172033', glow2: '#1a1730', dots: 'rgba(255,255,255,0.055)', vignette: 'rgba(0,0,0,0.42)', track: 'rgba(255,255,255,0.05)' },
  warm: { bg: '#17120e', ink: '#f7f0e4', code: '#e8dece', dim: '#a89a8b', faint: '#51463b', line: '#352c23', key: '#b5a696',
    pat: '#f8c24e', bind: '#72d2e6', good: '#78d69a', bad: '#ff7d68', outer: '#c6b2ff', panel: '#201912',
    glow1: '#3a2819', glow2: '#2e1c22', dots: 'rgba(255,236,210,0.05)', vignette: 'rgba(8,4,0,0.38)', track: 'rgba(255,236,210,0.06)' },
  paper: { bg: '#f3ebdd', ink: '#2b231b', code: '#3d3329', dim: '#6c5f50', faint: '#c9bba7', line: '#d8cab5', key: '#857767',
    pat: '#b56a00', bind: '#0d7d9b', good: '#1d8c50', bad: '#cc4430', outer: '#6a4fd4', panel: '#e9decb',
    glow1: '#fbf6ec', glow2: '#eadcc6', dots: 'rgba(70,45,20,0.07)', vignette: 'rgba(110,80,40,0.12)', track: 'rgba(70,45,20,0.08)' },
};
const THEME = (typeof location !== 'undefined' && new URLSearchParams(location.search).get('theme')) || 'paper';
// ---- palette (one meaning per colour, used the same way in every scene) -----------------------------------
// ink/code: program text; dim/faint: what is not talked about; key: keywords; pat: patterns and clauses, what is
// assumed; bind: binders, the question marks; good: a call that matches; bad: a refutation; outer: a name in scope
const C = Object.assign({}, THEMES[THEME] || THEMES.paper);

// ---- easing -------------------------------------------------------------------------------------------------
const E = {
  lin: t => t,
  in: t => t * t * t,
  out: t => 1 - Math.pow(1 - t, 3),
  out5: t => 1 - Math.pow(1 - t, 5),
  io: t => (t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2),
  io5: t => (t < 0.5 ? 16 * t ** 5 : 1 - Math.pow(-2 * t + 2, 5) / 2),
  back: t => { const c1 = 1.4, c3 = c1 + 1; return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2); },
  pop: t => 1 - Math.exp(-7 * t) * Math.cos(10 * t),
};
const clamp = (v, a = 0, b = 1) => Math.max(a, Math.min(b, v));
const lerp = (a, b, t) => a + (b - a) * t;

function parseColor(c) {
  if (Array.isArray(c)) return c;
  if (c[0] === '#') {
    const h = c.length === 4 ? c.slice(1).split('').map(x => x + x).join('') : c.slice(1);
    return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16), h.length === 8 ? parseInt(h.slice(6, 8), 16) / 255 : 1];
  }
  const m = c.match(/rgba?\(([^)]+)\)/);
  const p = m[1].split(',').map(Number);
  return [p[0], p[1], p[2], p.length > 3 ? p[3] : 1];
}
const rgba = a => `rgba(${a[0].toFixed(1)},${a[1].toFixed(1)},${a[2].toFixed(1)},${a[3].toFixed(3)})`;
const alpha = (c, a) => { const p = parseColor(c); return rgba([p[0], p[1], p[2], a]); };
const COLOR_PROPS = new Set(['color', 'bg', 'stroke', 'fill', 'border']);

// ---- timeline -----------------------------------------------------------------------------------------------
const DEFAULTS = { x: 0, y: 0, s: 1, sx: 1, sy: 1, r: 0, o: 1, blur: 0 };

class Timeline {
  constructor() { this.els = new Map(); }
  _rec(el) {
    let r = this.els.get(el);
    if (!r) { r = { props: {}, texts: [], custom: {} }; this.els.set(el, r); }
    return r;
  }
  _key(el, prop, key) {
    const r = this._rec(el);
    if (!r.props[prop] && COLOR_PROPS.has(prop)) {
      // a colour starts from what the element has now
      const css = { color: 'color', bg: 'backgroundColor', border: 'borderColor', stroke: 'stroke', fill: 'fill' }[prop];
      const cur = el.style[css];
      r.init = r.init || {};
      r.init[prop] = cur && /^(#|rgb)/.test(cur) ? parseColor(cur) : null;
    }
    (r.props[prop] = r.props[prop] || []).push(key);
    r.sorted = false;
  }
  set(el, props, at = 0) { for (const p in props) this._key(el, p, { t: at, d: 0, to: props[p] }); return this; }
  to(el, props, at, dur = 0.6, ease = E.out) { for (const p in props) this._key(el, p, { t: at, d: dur, to: props[p], ease }); return this; }
  fromTo(el, from, to, at, dur = 0.6, ease = E.out) { for (const p in to) this._key(el, p, { t: at, d: dur, from: from[p], to: to[p], ease }); return this; }
  text(el, str, at) { this._rec(el).texts.push({ t: at, str }); this._rec(el).sorted = false; return this; }
  // a custom numeric property with its own way of being applied: fn(el, value)
  custom(el, name, fn, initial = 0) { const r = this._rec(el); r.custom[name] = { fn, initial }; return this; }

  _value(keys, t, prop, initial) {
    const isColor = COLOR_PROPS.has(prop);
    let v = initial;
    for (const k of keys) {
      if (k.t > t) break;
      const from = k.from !== undefined ? k.from : v;
      if (k.d <= 0 || t >= k.t + k.d) { v = k.to; continue; }
      const u = (k.ease || E.out)(clamp((t - k.t) / k.d));
      if (isColor) { const a = parseColor(from), b = parseColor(k.to); v = [lerp(a[0], b[0], u), lerp(a[1], b[1], u), lerp(a[2], b[2], u), lerp(a[3], b[3], u)]; }
      else v = lerp(from, k.to, u);
    }
    return v;
  }
  seek(t) {
    for (const [el, r] of this.els) {
      if (!r.sorted) { for (const p in r.props) r.props[p].sort((a, b) => a.t - b.t); r.texts.sort((a, b) => a.t - b.t); r.sorted = true; }
      const P = r.props, val = (p) => {
        if (!P[p]) return undefined;
        let init = r.custom[p] ? r.custom[p].initial : (el._init && el._init[p] !== undefined ? el._init[p] : DEFAULTS[p]);
        if (COLOR_PROPS.has(p)) { init = r.init && r.init[p]; if (!init) { const c = parseColor(P[p][0].from !== undefined ? P[p][0].from : P[p][0].to); init = [c[0], c[1], c[2], p === 'color' ? c[3] : 0]; } }
        return this._value(P[p], t, p, init);
      };
      if (P.x || P.y || P.s || P.sx || P.sy || P.r) {
        const x = val('x') ?? (el._init?.x ?? 0), y = val('y') ?? (el._init?.y ?? 0), s = val('s') ?? 1, sx = val('sx') ?? 1, sy = val('sy') ?? 1, rr = val('r') ?? 0;
        el.style.transform = `translate(${x.toFixed(2)}px,${y.toFixed(2)}px) rotate(${rr.toFixed(3)}deg) scale(${(s * sx).toFixed(4)},${(s * sy).toFixed(4)})`;
      }
      if (P.o) { const o = val('o'); el.style.opacity = o.toFixed(4); el.style.visibility = o <= 0.001 ? 'hidden' : 'visible'; }
      if (P.blur) { const b = val('blur'); el.style.filter = b > 0.05 ? `blur(${b.toFixed(2)}px)` : 'none'; }
      if (P.color) el.style.color = rgba(parseColor(val('color')));
      if (P.bg) el.style.backgroundColor = rgba(parseColor(val('bg')));
      if (P.border) el.style.borderColor = rgba(parseColor(val('border')));
      if (P.stroke) el.style.stroke = rgba(parseColor(val('stroke')));
      if (P.fill) el.style.fill = rgba(parseColor(val('fill')));
      for (const name in r.custom) if (P[name]) r.custom[name].fn(el, this._value(P[name], t, name, r.custom[name].initial));
      if (r.texts.length) {
        let s = el._text0 ?? '';
        for (const k of r.texts) { if (k.t > t) break; s = k.str; }
        if (el._shown !== s) { el.textContent = s; el._shown = s; }
      }
    }
  }
}

// ---- DOM helpers --------------------------------------------------------------------------------------------
function el(parent, tag = 'div', style = {}, text) {
  const svg = tag === 'svg' || tag === 'path' || tag === 'circle' || tag === 'line' || tag === 'rect' || tag === 'g';
  const e = svg ? document.createElementNS('http://www.w3.org/2000/svg', tag) : document.createElement(tag);
  if (!svg) e.style.position = 'absolute';
  Object.assign(e.style, style);
  if (text !== undefined) { e.textContent = text; e._text0 = text; e._shown = text; }
  parent.appendChild(e);
  return e;
}
// an absolutely placed box; x, y are its top-left on the stage, animated offsets are relative to it
function box(parent, x, y, style = {}, text) {
  const e = el(parent, 'div', Object.assign({ left: x + 'px', top: y + 'px' }, style), text);
  return e;
}
function svgLayer(parent) {
  const s = el(parent, 'svg');
  s.setAttribute('width', W); s.setAttribute('height', H); s.setAttribute('viewBox', `0 0 ${W} ${H}`);
  Object.assign(s.style, { position: 'absolute', left: 0, top: 0, overflow: 'visible', pointerEvents: 'none' });
  return s;
}
// a stroked path that can be drawn: tl key 'draw' from 0 to 1
function path(tl, svg, d, { stroke = C.ink, width = 3, fill = 'none', cap = 'round', dash } = {}) {
  const p = el(svg, 'path');
  p.setAttribute('d', d); p.setAttribute('fill', fill); p.setAttribute('stroke-width', width);
  p.setAttribute('stroke-linecap', cap); p.setAttribute('stroke-linejoin', 'round');
  p.style.stroke = stroke;
  const len = p.getTotalLength();
  if (dash) { p.style.strokeDasharray = dash; }
  else {
    p.style.strokeDasharray = `${len} ${len}`; p.style.strokeDashoffset = len; p.style.strokeOpacity = 0;
    // an undrawn path with round caps would still show a dot: it has no stroke at all until it starts to draw
    tl.custom(p, 'draw', (e, v) => { e.style.strokeDashoffset = (len * (1 - v)).toFixed(2); e.style.strokeOpacity = v <= 0.002 ? 0 : 1; }, 0);
  }
  p._len = len;
  return p;
}
// a tick or a cross centred at (x, y)
function tick(tl, svg, x, y, size = 18, color = C.good, width = 4) {
  return path(tl, svg, `M ${x - size * 0.55} ${y + size * 0.05} L ${x - size * 0.12} ${y + size * 0.45} L ${x + size * 0.6} ${y - size * 0.45}`, { stroke: color, width });
}
function cross(tl, svg, x, y, size = 16, color = C.bad, width = 4) {
  const a = path(tl, svg, `M ${x - size / 2} ${y - size / 2} L ${x + size / 2} ${y + size / 2}`, { stroke: color, width });
  const b = path(tl, svg, `M ${x + size / 2} ${y - size / 2} L ${x - size / 2} ${y + size / 2}`, { stroke: color, width });
  return [a, b];
}
// a smooth arrow from (x1,y1) to (x2,y2), bending by `bend` pixels to the left of the direction of travel
function arrowPath(x1, y1, x2, y2, bend = 0) {
  const mx = (x1 + x2) / 2, my = (y1 + y2) / 2, dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy) || 1;
  const cx = mx - dy / L * bend, cy = my + dx / L * bend;
  return { d: `M ${x1} ${y1} Q ${cx} ${cy} ${x2} ${y2}`, cx, cy };
}
function arrow(tl, svg, x1, y1, x2, y2, { bend = 0, stroke = C.dim, width = 3, head = 12 } = {}) {
  const a = arrowPath(x1, y1, x2, y2, bend);
  const p = path(tl, svg, a.d, { stroke, width });
  const ang = Math.atan2(y2 - a.cy, x2 - a.cx);
  const h = el(svg, 'path');
  h.setAttribute('d', `M ${-head} ${-head * 0.55} L 0 0 L ${-head} ${head * 0.55}`);
  h.setAttribute('fill', 'none'); h.setAttribute('stroke-width', width); h.setAttribute('stroke-linecap', 'round'); h.setAttribute('stroke-linejoin', 'round');
  h.style.stroke = stroke; h.style.opacity = 0;
  h.setAttribute('transform', `translate(${x2} ${y2}) rotate(${ang * 180 / Math.PI})`);
  tl.set(h, { o: 0 }, 0);
  p._head = h;
  return p;
}
function drawArrow(tl, p, at, dur = 0.5) { tl.to(p, { draw: 1 }, at, dur, E.io); tl.fromTo(p._head, { o: 0 }, { o: 1 }, at + dur * 0.75, dur * 0.25); }
function hideArrow(tl, p, at, dur = 0.3) { tl.to(p, { o: 0 }, at, dur); tl.to(p._head, { o: 0 }, at, dur); }

// ---- code on a character grid -------------------------------------------------------------------------------
const KEYWORDS = new Set(['if', 'then', 'else', 'let', 'in', 'where', 'case', 'of']);
let _cw = {};
function charWidth(size) {
  if (_cw[size]) return _cw[size];
  const m = document.createElement('span');
  Object.assign(m.style, { position: 'absolute', visibility: 'hidden', fontFamily: 'var(--mono)', fontSize: size + 'px', whiteSpace: 'pre', fontVariantLigatures: 'none' });
  m.textContent = '0'.repeat(100); document.body.appendChild(m);
  const w = m.getBoundingClientRect().width / 100; m.remove();
  return (_cw[size] = w);
}
// "loop({i1|i}, {x1|1|p}) = ..."  ->  tokens. {id|text|class} gives a token an identity (kept across states) and
// an optional class: p pattern, b binder, o outer name, k keyword, n number, f function, d dim, g good, r bad.
function tokenize(src) {
  const lines = src.split('\n'), out = [];
  lines.forEach((line, li) => {
    const re = /\{([^}|]*)\|([^}|]*)(?:\|([^}]*))?\}|(\s+)|(\?[A-Za-z]\w*)|([A-Za-z_][\w']*)|(\d+)|(==|!=|<=|>=)|(.)/gu;
    let m, col = 0; const seen = {};
    while ((m = re.exec(line))) {
      if (m[4] !== undefined) { col += m[4].length; continue; }
      let id, text, cls;
      if (m[1] !== undefined) { id = m[1]; text = m[2]; cls = m[3]; }
      else text = m[0];
      if (!cls) {
        if (/^\?/.test(text)) cls = 'b';
        else if (KEYWORDS.has(text)) cls = 'k';
        else if (/^\d+$/.test(text)) cls = 'n';
        else if (/^[A-Za-z_]/.test(text) && line[re.lastIndex] === '(') cls = 'f';
        else if (/^[A-Za-z_]/.test(text)) cls = 'v';
        else cls = 'x';
      }
      if (!id) { seen[text] = (seen[text] || 0) + 1; id = `${text}@${li}.${seen[text]}`; }
      out.push({ id, text, cls, line: li, col, len: [...text].length });
      col += [...text].length;
    }
  });
  return out;
}
const CLS_COLOR = { p: C.pat, b: C.bind, o: C.outer, k: C.key, n: C.code, f: C.ink, v: C.code, x: C.dim, d: C.faint, g: C.good, r: C.bad };

class Code {
  // x, y: top-left on the stage; size: font size in px
  constructor(tl, parent, x, y, size = 44, opts = {}) {
    this.tl = tl; this.size = size; this.cw = charWidth(size); this.lh = Math.round(size * (opts.leading || 1.62));
    this.x = x; this.y = y; this.tokens = new Map(); this.state = [];
    this.root = box(parent, x, y, { width: '10px', height: '10px' });
    this.marks = box(this.root, 0, 0);
    this.layer = box(this.root, 0, 0);
    this.palette = Object.assign({}, CLS_COLOR, opts.palette || {});
    this.weight = opts.weight || 450;
  }
  _span(tok) {
    const s = box(this.layer, 0, 0, {
      fontFamily: 'var(--mono)', fontSize: this.size + 'px', lineHeight: this.lh + 'px', whiteSpace: 'pre', fontWeight: tok.cls === 'f' ? 560 : this.weight,
      fontVariantLigatures: 'none', color: this.palette[tok.cls] || C.code, opacity: 0, willChange: 'transform, opacity',
    }, tok.text);
    s._init = { x: tok.col * this.cw, y: tok.line * this.lh };
    s.style.transform = `translate(${s._init.x}px,${s._init.y}px)`;
    return s;
  }
  px(tok) { return { x: tok.col * this.cw, y: tok.line * this.lh }; }
  // first appearance
  show(src, at, { dur = 0.5, stagger = 0.012, rise = 14, byLine = 0.12 } = {}) {
    const toks = tokenize(src); this.state = toks;
    toks.forEach((tok, i) => {
      const s = this._span(tok); this.tokens.set(tok.id, { span: s, tok });
      const p = this.px(tok), t0 = at + i * stagger + tok.line * byLine;
      this.tl.set(s, { x: p.x, y: p.y + rise, o: 0 }, 0);
      this.tl.to(s, { y: p.y, o: 1 }, t0, dur, E.out5);
    });
    return this;
  }
  // move to a new arrangement: tokens with the same id travel, the others fade
  morph(src, at, { dur = 0.7, ease = E.io, stagger = 0.006, flash = null } = {}) {
    const toks = tokenize(src), next = new Map(toks.map(t => [t.id, t])), tl = this.tl;
    for (const [id, cur] of this.tokens) {
      if (!next.has(id)) { tl.to(cur.span, { o: 0, s: 0.8 }, at, dur * 0.45, E.in); cur.gone = true; }
    }
    toks.forEach((tok, i) => {
      const p = this.px(tok), cur = this.tokens.get(tok.id);
      if (cur && !cur.gone) {
        tl.to(cur.span, { x: p.x, y: p.y }, at + i * stagger, dur, ease);
        if (cur.tok.text !== tok.text) {
          // the token changes what it says: squeeze, swap, release
          tl.to(cur.span, { sy: 0.05 }, at, dur * 0.3, E.in); tl.text(cur.span, tok.text, at + dur * 0.3); tl.to(cur.span, { sy: 1 }, at + dur * 0.3, dur * 0.45, E.back);
        }
        const col = this.palette[tok.cls] || C.code;
        if (cur.tok.cls !== tok.cls || cur.tok.text !== tok.text) {
          if (flash) { tl.to(cur.span, { color: flash }, at, dur * 0.3); tl.to(cur.span, { color: col }, at + dur * 0.6, dur * 0.8); }
          else tl.to(cur.span, { color: col }, at, dur);
        }
        cur.tok = tok;
      } else {
        const s = this._span(tok); this.tokens.set(tok.id, { span: s, tok });
        tl.set(s, { x: p.x, y: p.y, o: 0, s: 0.85 }, 0);
        tl.to(s, { o: 1, s: 1 }, at + dur * 0.45 + i * stagger, dur * 0.55, E.out);
      }
    });
    for (const [id, cur] of this.tokens) if (cur.gone) this.tokens.delete(id);
    this.state = toks;
    return this;
  }
  // a new arrangement with nothing travelling: tokens that keep their id, text and place stay; the others leave,
  // and only then do the new ones arrive, so no frame has one glyph printed over another. Readable from at + dur.
  swap(src, at, { dur = 0.5 } = {}) {
    const toks = tokenize(src), next = new Map(toks.map(t => [t.id, t])), tl = this.tl;
    for (const [id, cur] of this.tokens) {
      const n = next.get(id);
      if (!n || n.text !== cur.tok.text || n.col !== cur.tok.col || n.line !== cur.tok.line) { tl.to(cur.span, { o: 0 }, at, dur * 0.4, E.in); cur.gone = true; }
    }
    for (const [id, cur] of this.tokens) if (cur.gone) this.tokens.delete(id);
    for (const tok of toks) {
      const p = this.px(tok), cur = this.tokens.get(tok.id);
      if (cur) { if (cur.tok.cls !== tok.cls) tl.to(cur.span, { color: this.palette[tok.cls] || C.code }, at, dur); cur.tok = tok; continue; }
      const s = this._span(tok); this.tokens.set(tok.id, { span: s, tok });
      tl.set(s, { x: p.x, y: p.y, o: 0 }, 0); tl.to(s, { o: 1 }, at + dur * 0.5, dur * 0.5, E.out);
    }
    this.state = toks;
    return this;
  }
  // what is deleted, the same way everywhere: the tokens go faint and a grey line is drawn through them (one line
  // of code). Red is for a refutation, never for a deletion.
  strike(sel, at, { dur = 0.4, out = null, fade = true } = {}) {
    const r = this.rect(sel, 4), u = box(this.marks, r.x - this.x, r.y - this.y + this.lh * 0.5 - 1, { width: r.w + 'px', height: '3px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center', opacity: 0 });
    this.tl.set(u, { sx: 0, o: 1 }, 0); this.tl.to(u, { sx: 1 }, at, dur, E.io);
    if (fade) this.color(sel, C.faint, at, dur);
    if (out !== null) this.tl.to(u, { o: 0 }, out, 0.3);
    return u;
  }
  ids(sel) {
    if (typeof sel === 'string') sel = [sel];
    if (sel instanceof RegExp) return [...this.tokens.keys()].filter(id => sel.test(id));
    if (typeof sel === 'function') return [...this.tokens.values()].filter(c => sel(c.tok)).map(c => c.tok.id);
    return sel.filter(id => { if (!this.tokens.has(id)) console.warn('no token', id); return this.tokens.has(id); });
  }
  spans(sel) { return this.ids(sel).map(id => this.tokens.get(id).span); }
  color(sel, col, at, dur = 0.35) { for (const s of this.spans(sel)) this.tl.to(s, { color: col }, at, dur); return this; }
  recolor(sel, at, dur = 0.5) { for (const id of this.ids(sel)) { const c = this.tokens.get(id); this.tl.to(c.span, { color: this.palette[c.tok.cls] || C.code }, at, dur); } return this; }
  fade(sel, o, at, dur = 0.4) { for (const s of this.spans(sel)) this.tl.to(s, { o }, at, dur); return this; }
  // a token lights for a moment. It grows very little: a glyph scaled further reads as a different glyph
  pulse(sel, at, { color = C.ink, scale = 1.07, dur = 0.5 } = {}) {
    scale = Math.min(scale, 1.08);
    for (const id of this.ids(sel)) { const c = this.tokens.get(id); this.tl.to(c.span, { s: scale, color }, at, dur * 0.4, E.out); this.tl.to(c.span, { s: 1, color: this.palette[c.tok.cls] || C.code }, at + dur * 0.4, dur * 0.6, E.io); }
    return this;
  }
  // the box around some tokens, in stage coordinates
  rect(sel, pad = 0) {
    const ts = this.ids(sel).map(id => this.tokens.get(id).tok);
    const x0 = Math.min(...ts.map(t => t.col)), x1 = Math.max(...ts.map(t => t.col + t.len)), l0 = Math.min(...ts.map(t => t.line)), l1 = Math.max(...ts.map(t => t.line));
    return { x: this.x + x0 * this.cw - pad, y: this.y + l0 * this.lh - pad * 0.4, w: (x1 - x0) * this.cw + 2 * pad, h: (l1 - l0 + 1) * this.lh + pad * 0.8, cx: this.x + (x0 + x1) / 2 * this.cw, cy: this.y + (l0 + l1 + 1) / 2 * this.lh };
  }
  // a soft highlight behind some tokens (they must be on one line)
  mark(sel, color, at, { dur = 0.4, pad = 10, out = null, fill = 0.16 } = {}) {
    const r = this.rect(sel, pad), m = box(this.marks, r.x - this.x, r.y - this.y + this.lh * 0.08, {
      width: r.w + 'px', height: (r.h - this.lh * 0.16) + 'px', borderRadius: '10px', background: alpha(color, fill), boxShadow: `inset 0 0 0 1.5px ${alpha(color, 0.55)}`, transformOrigin: 'left center', opacity: 0,
    });
    this.tl.set(m, { sx: 0.2, o: 0 }, 0); this.tl.to(m, { sx: 1, o: 1 }, at, dur, E.out5);
    if (out !== null) this.tl.to(m, { o: 0 }, out, 0.35);
    return m;
  }
  // an underline that draws itself under some tokens
  underline(sel, color, at, { dur = 0.45, out = null, dy = 0 } = {}) {
    const r = this.rect(sel, 2), u = box(this.marks, r.x - this.x, r.y - this.y + this.lh * 0.86 + dy, { width: r.w + 'px', height: '4px', borderRadius: '2px', background: color, transformOrigin: 'left center', opacity: 0 });
    this.tl.set(u, { sx: 0, o: 1 }, 0); this.tl.to(u, { sx: 1 }, at, dur, E.io);
    if (out !== null) this.tl.to(u, { o: 0 }, out, 0.3);
    return u;
  }
  hide(at, dur = 0.45, { rise = -10 } = {}) { this.tl.to(this.root, { o: 0 }, at, dur, E.in); return this; }
  move(dx, dy, at, dur = 0.8, ease = E.io) { this.tl.to(this.root, { x: dx, y: dy }, at, dur, ease); return this; }
}

// ---- a grid for comparing a pattern with calls, place by place ----------------------------------------------
// Columns are the places of a block (its parameters, with a pair's parts as two places); rows are a pattern and
// the calls checked against it. The same picture is used wherever a call is checked.
class Grid {
  constructor(tl, parent, x, y, { cols, labelW = 250, rowH = 92, size = 40, gap = 14, headH = 44 } = {}) {
    this.tl = tl; this.x = x; this.y = y; this.cols = cols; this.labelW = labelW; this.rowH = rowH; this.size = size; this.gap = gap; this.headH = headH;
    this.root = box(parent, x, y); this.rows = new Map(); this.n = 0;
    this.svg = el(this.root, 'svg'); Object.assign(this.svg.style, { position: 'absolute', left: 0, top: 0, overflow: 'visible' });
    this.cx = []; let cx = labelW;
    for (const c of cols) { this.cx.push(cx); cx += c.w + gap; }
    this.width = cx - gap;
    this.heads = cols.map((c, i) => box(this.root, this.cx[i], 0, { width: c.w + 'px', textAlign: 'center', fontFamily: 'var(--mono)', fontSize: '26px', color: C.dim, whiteSpace: 'pre', opacity: 0 }, c.head));
  }
  showHead(at, dur = 0.5) { this.heads.forEach((h, i) => { this.tl.set(h, { o: 0, y: 10 }, 0); this.tl.to(h, { o: 1, y: 0 }, at + i * 0.05, dur, E.out5); }); return this; }
  rowY(name) { return this.headH + this.rows.get(name).i * (this.rowH + this.gap); }
  // a row: its label on the left, and one empty cell per column
  row(name, text, at, { color = C.dim, dur = 0.5 } = {}) {
    const i = this.n++, y = this.headH + i * (this.rowH + this.gap);
    const lab = box(this.root, 0, y, { width: (this.labelW - 26) + 'px', height: this.rowH + 'px', display: 'flex', alignItems: 'center', justifyContent: 'flex-end', fontFamily: 'var(--sans)', fontSize: '24px', fontWeight: 560, letterSpacing: '0.14em', textTransform: 'uppercase', color, whiteSpace: 'pre', opacity: 0 }, text);
    this.tl.set(lab, { o: 0, x: -12 }, 0); this.tl.to(lab, { o: 1, x: 0 }, at, dur, E.out5);
    const cells = this.cols.map((c, j) => {
      const b = box(this.root, this.cx[j], y, { width: c.w + 'px', height: this.rowH + 'px', borderRadius: '14px', background: alpha(C.panel, 0.9), boxShadow: `inset 0 0 0 1.5px ${C.line}`, opacity: 0 });
      const t = box(b, 0, 0, { width: c.w + 'px', height: this.rowH + 'px', display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--mono)', fontSize: this.size + 'px', fontVariantLigatures: 'none', color: C.code, whiteSpace: 'pre' }, '');
      this.tl.set(b, { o: 0, s: 0.94 }, 0); this.tl.to(b, { o: 1, s: 1 }, at + 0.05 + j * 0.04, dur, E.out5);
      // the cell's tint: 0 neutral; set through tint()
      this.tl.custom(b, 'ring', (e, v) => {}, 0);
      return { b, t };
    });
    this.rows.set(name, { i, lab, cells });
    return this;
  }
  // put text into a cell
  cell(name, j, text, at, { color = C.code, dur = 0.45 } = {}) {
    const c = this.rows.get(name).cells[j];
    this.tl.text(c.t, text, at); this.tl.set(c.t, { o: 0, y: 12 }, 0);
    this.tl.fromTo(c.t, { o: 0, y: 12 }, { o: 1, y: 0 }, at, dur, E.out5);
    this.tl.set(c.t, { color }, at);
    return this;
  }
  recolor(name, j, color, at, dur = 0.4) { this.tl.to(this.rows.get(name).cells[j].t, { color }, at, dur); return this; }
  // tint a cell's box: the colour says what the cell is (assumed, matched, refuted, kept)
  tint(name, j, color, at, { dur = 0.4, fill = 0.13, line = 0.75 } = {}) {
    const c = this.rows.get(name).cells[j];
    this.tl.to(c.b, { bg: alpha(color, fill) }, at, dur);
    if (!c.ringEl) { c.ringEl = box(c.b, 0, 0, { width: '100%', height: '100%', borderRadius: '14px', boxShadow: `inset 0 0 0 2px ${color}`, opacity: 0 }); this.tl.set(c.ringEl, { o: 0 }, 0); }
    else this.tl.custom(c.ringEl, 'noop', () => {}, 0);
    const ring = box(c.b, 0, 0, { width: '100%', height: '100%', borderRadius: '14px', boxShadow: `inset 0 0 0 2px ${alpha(color, line)}`, opacity: 0 });
    this.tl.set(ring, { o: 0 }, 0); this.tl.to(ring, { o: 1 }, at, dur);
    if (c.ring) this.tl.to(c.ring, { o: 0 }, at, dur);
    c.ring = ring;
    return this;
  }
  untint(name, j, at, dur = 0.4) { const c = this.rows.get(name).cells[j]; this.tl.to(c.b, { bg: alpha(C.panel, 0.9) }, at, dur); if (c.ring) { this.tl.to(c.ring, { o: 0 }, at, dur); c.ring = null; } return this; }
  // the stage rectangle of a cell
  rect(name, j) { const y = this.rowY(name); return { x: this.x + this.cx[j], y: this.y + y, w: this.cols[j].w, h: this.rowH, cx: this.x + this.cx[j] + this.cols[j].w / 2, cy: this.y + y + this.rowH / 2 }; }
  // a tick or a cross to the lower right of a cell
  mark(name, j, ok, at, { dur = 0.3 } = {}) {
    const y = this.rowY(name), mx = this.cx[j] + this.cols[j].w - 22, my = y + this.rowH - 20;
    const disc = box(this.root, mx - 17, my - 17, { width: '34px', height: '34px', borderRadius: '50%', background: ok ? C.good : C.bad });
    this.tl.set(disc, { o: 0, s: 0.3 }, 0); this.tl.to(disc, { o: 1, s: 1 }, at, dur, E.back);
    const marks = ok ? [tick(this.tl, this.svg, mx, my, 11, C.bg, 3.5)] : cross(this.tl, this.svg, mx, my, 11, C.bg, 3.5);
    this.svg.parentNode.appendChild(this.svg);
    marks.forEach(m => this.tl.to(m, { draw: 1 }, at + dur * 0.5, dur, E.out));
    const c = this.rows.get(name).cells[j]; (c.marks = c.marks || []).push(disc, ...marks);
    return this;
  }
  unmark(name, j, at, dur = 0.3) { const c = this.rows.get(name).cells[j]; for (const m of c.marks || []) this.tl.to(m, { o: 0 }, at, dur); c.marks = []; return this; }
  hideRow(name, at, { dur = 0.45, dx = -40 } = {}) {
    const r = this.rows.get(name);
    this.tl.to(r.lab, { o: 0, x: dx }, at, dur, E.in);
    r.cells.forEach((c, j) => { this.tl.to(c.b, { o: 0, x: dx }, at + j * 0.03, dur, E.in); for (const m of c.marks || []) this.tl.to(m, { o: 0 }, at, dur * 0.6); });
    return this;
  }
  hide(at, dur = 0.45) { this.tl.to(this.root, { o: 0 }, at, dur, E.in); return this; }
}

// ---- type ---------------------------------------------------------------------------------------------------
function label(parent, x, y, text, style = {}) {
  return box(parent, x, y, Object.assign({ fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim, whiteSpace: 'pre' }, style), text);
}
function serif(parent, x, y, text, size = 64, style = {}) {
  return box(parent, x, y, Object.assign({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, whiteSpace: 'pre', fontWeight: 400, letterSpacing: '-0.005em' }, style), text);
}
// lines of serif text that rise in one after another; returns the line elements
function lines(tl, parent, x, y, texts, at, { size = 64, gap = 1.28, stagger = 0.14, style = {}, dur = 0.8 } = {}) {
  return texts.map((t, i) => {
    const e = serif(parent, x, y + i * size * gap, t, size, style);
    tl.set(e, { y: 26, o: 0 }, 0); tl.to(e, { y: 0, o: 1 }, at + i * stagger, dur, E.out5);
    return e;
  });
}
function fadeIn(tl, e, at, dur = 0.6, dy = 18) { tl.set(e, { y: dy, o: 0 }, 0); tl.to(e, { y: 0, o: 1 }, at, dur, E.out5); return e; }
function fadeOut(tl, e, at, dur = 0.4, dy = -12) { tl.to(e, { y: dy, o: 0 }, at, dur, E.in); return e; }

// ---- scenes -------------------------------------------------------------------------------------------------
// A scene is { id, build(ctx) }. ctx = { tl, root, cue(name, fallback), dur }.
const SCENES = [];
function scene(id, build) { SCENES.push({ id, build }); }

window.Film = { W, H, C, E, Timeline, SCENES, scene };

// ==== src/narration.js ====
// The full-length video on "Fast Coalgebraic Bisimilarity Minimization" (POPL 2023). One story: many kinds of
// machine are one thing (states, each with a structure that has states inside); equivalent states are found by
// guessing blocks, renaming and comparing; doing that for every state in every round is correct but slow; two
// ideas (recompute only dirty states, the largest part of a split keeps its name) give m log n signatures; the
// data structure; kinds of machine as shapes built from a few pieces that fit inside one another; the measurements.
// {name} marks a cue. Blocks are named X, Y, Z (the paper numbers them), so that by ear they are never confused
// with the states 1 to 5 or with the automaton's letters a and b; in the automaton, X is {2, 3}, Y is {4, 5} and Z
// is {1} wherever all three exist. "co-algebra" is written as it is spoken (src/caption-fixes.json has the
// spelling). No person is named in the narration.
window.NARRATION = [
  // ------------------------------------------------------------------------------------------------ opening
  { id: 'hook', chapter: '', pre: 0.8, post: 0.7, text:
    `{one}Here is a small machine: a finite automaton with five states. {same}Two of its states behave in exactly the same way, {same2}and so do two others. {merge}Merge them, and the machine has three states, and does what it did before. {min}That is minimization. Tools that verify systems often minimize first, because a smaller machine is cheaper to analyse. ` +
    `{zoo}There are many kinds of machine like this: {ts}transition systems, {mc}Markov chains, and more. {each}For a long time, each kind had its own minimization algorithm. {generic}A general theory, called co-algebra, promises one algorithm for all of them. But the general algorithm that existed was slow in practice, needed a great deal of memory, and did not cover every kind of machine. ` +
    `{video}This video is about a new algorithm, and a tool called Boa that implements it. {claim}It covers all of these kinds and more, and it is faster than the earlier tools, with far less memory. {hand}By the end, we will have run the algorithm by hand, {why}and we will know why it is fast.` },
  { id: 'roadmap', chapter: '', pre: 0.3, post: 0.8, text:
    `{coming}Here is what is coming. {shape}First, one way to describe all these machines. {equiv}Then what it means for two states to be equivalent. {naive}Then a simple algorithm that is correct but slow, {fast}and two ideas that make it fast. ` +
    `{types}Then how kinds of machine are put together from a few pieces, {bench}and the measurements.` },
  { id: 'title', chapter: '', pre: 0.6, post: 1.0, text:
    `{title}Fast co-algebraic bisimilarity minimization.` },

  // ------------------------------------------------------------------------------------------------ one shape
  { id: 'shape_a', chapter: 'One shape for many machines', pre: 1.9, post: 0.6, text:
    `{dfa}Start with the finite automaton. {usual}The usual picture has states, and arrows labelled with letters. A double border means accepting. {state}Now look at it from the point of view of one state. {s3}State three is not accepting. On the letter A it goes to state five, and on the letter B it goes to itself. ` +
    `{triple}So state three comes with three pieces of data: whether it is accepting, where the letter A leads, and where the letter B leads. False, five, three. {table}Write that down for every state, and the table is the whole automaton.` },
  { id: 'shape_b', chapter: 'One shape for many machines', pre: 0.4, post: 0.6, text:
    `{ts}A transition system has no letters and no accepting states. {succ}A state just has a set of states it can step to. {t3}State three can step to three, four, or five. {t5}State five cannot step at all: its set is empty. ` +
    `{mc}In a Markov chain, a state steps at random. {m1}State one goes to state two with probability one third, and to state three with probability two thirds. {dist}So its data is a probability distribution over states, {lab}together with a flag, true or false.` },
  { id: 'shape_c', chapter: 'One shape for many machines', pre: 0.4, post: 0.9, text:
    `{pattern}The pattern is the same each time. {states}There is a set of states, {struct}and each state has a piece of data with states inside it. We call it the state's successor structure. ` +
    `{kind}What differs is the shape of that data: {k1}a flag and two states; {k2}a set of states; {k3}a flag and a distribution. {built}These shapes are built from the same few pieces: flags, tuples, sets, distributions. That will matter later. {functor}The shape is the kind of machine. In category theory, such a shape is called a functor, {coalg}and a machine of that shape is called a co-algebra. That is the word in the title. {no}We will not need more category theory than that.` },

  // ------------------------------------------------------------------------------------------------ equivalent states
  { id: 'eq_a', chapter: 'Equivalent states', pre: 1.9, post: 0.6, text:
    `{q}When are two states equivalent? {circ}They should have equivalent successor structures. But those contain states, so the definition seems to go in a circle. {guess}The way out is to start from a guess. ` +
    `{blocks}Group the states into blocks, and give each block a name. {subst}Then, in every successor structure, replace each state by the name of its block. {stable}The guess is called stable if states in the same block end up with exactly the same structure.` },
  { id: 'eq_b', chapter: 'Equivalent states', pre: 0.4, post: 0.6, text:
    `{d}Try it on the automaton, with the guess that states two and three are equivalent, and four and five. {num}Call the block of two and three X, the block of four and five Y, and state one, on its own, Z. ` +
    `{r2}State two had: false, four, three. After renaming: false, Y, X. {r3}State three had: false, five, three. After renaming: also false, Y, X. {ok}They agree. {r45}So do four and five. {st}The guess is stable.` },
  { id: 'eq_c', chapter: 'Equivalent states', pre: 0.4, post: 0.6, text:
    `{ts}The same test works for the other machines, with one addition. {t12}In the transition system, guess that one and two are equivalent, and three and four, with five on its own. {s1}State one steps to two, three, and four. After renaming, that is: X, Y, Y. ` +
    `{dup}But this is a set, and a set does not hold duplicates. It is just X and Y. {s2}State two steps to one and four: X and Y again. They agree. ` +
    `{mc}In the Markov chain, guess that two, three, and five are equivalent, and call their block X. {m3}State three goes to state two with probability one quarter, to state five with one quarter, and to state four with one half. {add}Two and five are both in X, so their probabilities are added: one half to X. ` +
    `{m2}State two goes to itself and to four, one half each: the same. {norm}So renaming is followed by tidying up: duplicates removed, probabilities added.` },
  { id: 'eq_d', chapter: 'Equivalent states', pre: 0.4, post: 0.6, text:
    `{only}This renaming, with its tidying up, is essentially all we will ask of a kind of machine. {best}Among the stable guesses, there is one with the fewest blocks. {name}Its blocks are the classes of equivalent states. ` +
    `{bisim}For transition systems, this equivalence is known as bisimilarity: the other word in the title. {lang}For finite automata, it says that two states accept the same language. {min}And the minimized machine has one state for each block.` },
  { id: 'cool_one', chapter: 'Equivalent states', pre: 0.5, post: 0.9, text:
    `{three}Notice what just happened. {diff}Language equivalence, bisimilarity, and bisimilarity with probabilities are usually defined separately. {same}Here they are one definition, seen in three different shapes.` },

  // ------------------------------------------------------------------------------------------------ the simple algorithm
  { id: 'naive_a', chapter: 'The simple algorithm', pre: 1.9, post: 0.6, text:
    `{how}How do we find the best stable guess? {opt}Start by being optimistic: put all states in one block, X. {sig}Compute every state's structure, renamed by block. From here on we call that the state's signature. ` +
    `{r1}In the automaton, every signature now reads: a flag, then X, X. {split1}But the flags differ. Three states say false, and two say true. So they cannot all be equivalent. {two}Split the block in two: the false ones stay X, and the true ones become Y.` },
  { id: 'naive_b', chapter: 'The simple algorithm', pre: 0.4, post: 0.6, text:
    `{again}Now do it again, with the new blocks. {r2}State one reads: false, X, X. {r23}States two and three read: false, Y, X. {r45}Four and five read: true, Y, Y. {three}Three different signatures, so three blocks. State one gets a new name, Z. ` +
    `{once}Once more. {r3}This time every signature is the same as before, so no block splits. {done}The guess is stable. And because we only ever separated states that had to be separated, it is the best one.` },
  { id: 'naive_c', chapter: 'The simple algorithm', pre: 0.4, post: 0.9, text:
    `{general}Nothing here was special to automata. The loop only computes signatures and compares them. {cost}But look at the cost. {every}Every round recomputes the signature of every state, {most}even when it cannot have changed. ` +
    `{chain}And there can be many rounds. In a machine shaped like a long chain, each round splits off a single state. {sq}With N states, that is N rounds of N signatures: N squared. {million}For a million states, a million million.` },

  // ------------------------------------------------------------------------------------------------ two ideas
  { id: 'idea_dirty', chapter: 'Two ideas', pre: 1.9, post: 0.6, text:
    `{first}The first idea: do not recompute what cannot have changed. {when}A state's signature depends only on the blocks of its successors. {so}So it can change only when one of its successors moves to a different block. ` +
    `{dirty}Call a state dirty when that has happened, and clean once its signature has been computed again. {only}Only dirty states need a new signature. ` +
    `{clean}And the clean states of a block all share one signature: they had the same signature when the block was formed, and nothing they depend on has moved. So computing it for one of them is enough.` },
  { id: 'idea_name', chapter: 'Two ideas', pre: 0.4, post: 0.6, text:
    `{second}The second idea is about names. {free}When a block splits, one part can keep the old name, and the others get new names. We are free to choose which. {large}Let the largest part keep the old name. ` +
    `{unch}Then the states in the largest part have not moved at all, and nothing that points to them becomes dirty. {small}Only the smaller parts cost anything.` },
  { id: 'trick', chapter: 'Two ideas', pre: 0.4, post: 0.6, text:
    `{game}Why does that help so much? {set}Take a set of N things, and keep splitting it. {follow}Follow one element. {half}Each time it lands in a smaller part, the set around it is at most half as big as before. ` +
    `{log}That can happen only about log N times. {twenty}For a million elements: twenty times. {old}This is an old trick in automaton minimization, known as the half the size trick. {bound}So a state gets a new name at most log N times. ` +
    `{edges}Each new name makes dirty the states that point to it, its predecessors: one signature for each incoming edge. {total}Altogether, with M edges: M times log N signatures, instead of N squared.` },
  { id: 'algo', chapter: 'Two ideas', pre: 0.5, post: 0.6, text:
    `{algo}Here is the whole algorithm. {init}Put all states in one block, and mark them all dirty. {loop}Then repeat. {pick}Pick a block that has dirty states. {comp}Compute the signatures of its dirty states, and of one clean state. Now they are all clean. ` +
    `{split}Split the block by signature, and let the largest part keep the name. {mark}Mark as dirty every predecessor of a state that got a new name. {until}Stop when nothing is dirty.` },
  { id: 'run_a', chapter: 'Two ideas', pre: 0.5, post: 0.6, text:
    `{run}Run it on the automaton. {all}One block, X, and all five states dirty. {five}Five signatures, and now all five are clean. {sp}Three say false, two say true. The three are the larger part, so they stay X, and states four and five become block Y. ` +
    `{pred}Who points to four or five? States two, three, four, and five. They become dirty. {one}State one does not. It stays clean.` },
  { id: 'run_b', chapter: 'Two ideas', pre: 0.4, post: 0.6, text:
    `{blockA}Take block X. {two}Two dirty states, two and three, and one clean state. {sigs}Three signatures. Two and three read: false, Y, X. State one reads: false, X, X. ` +
    `{split}The block splits. Two and three are the larger part, so they keep the name X, and state one becomes block Z. {nobody}Who points to state one? Nobody. So nothing becomes dirty. ` +
    `{blockB}Take block Y. Two dirty states, two signatures, and they agree: no split. {end}Nothing is dirty. Done. {count}That was ten signatures, where the simple algorithm computed fifteen.` },
  { id: 'cool_two', chapter: 'Two ideas', pre: 0.5, post: 0.9, text:
    `{never}Notice what the algorithm never did. {inside}It never looked inside a signature. It only asked for signatures, and compared them. {any}So it works for any kind of machine that can compute them.` },

  // ------------------------------------------------------------------------------------------------ fast in practice
  { id: 'ds_a', chapter: 'Fast in practice', pre: 1.9, post: 0.6, text:
    `{count}Counting signatures is not the whole cost. {touch}If splitting a block meant walking over all of its states, the clean ones too, the M log N bound would be lost. {arr}So the states are kept in one array, each block a stretch of it, ` +
    `{cd}with its clean states first and its dirty states at the end. {mark}Marking a state dirty is one swap, with the last clean state of its block. {split}Splitting a block rearranges only its dirty states. {cost}So a split costs time proportional to the number of dirty states, however many clean ones there are.` },
  { id: 'ds_b', chapter: 'Fast in practice', pre: 0.4, post: 0.9, text:
    `{mem}The algorithm also needs little memory. {need}It keeps the machine, each state's predecessors, and this structure for the blocks. {no}The earlier fast algorithms keep more: a counter for each transition, for example. ` +
    `{theory}In theory, there is a price. {k}Computing a signature looks at all of a state's successors. The fastest earlier algorithms, which ask more of the shape, avoid that cost. {practice}In the measurements, as we will see, this price does not show.` },

  // ------------------------------------------------------------------------------------------------ any kind of machine
  { id: 'types_a', chapter: 'Any kind of machine', pre: 1.9, post: 0.6, text:
    `{what}What does a kind of machine have to provide? {fn}Essentially one function: given a state and the current blocks, return the state's signature. {kit}But these functions are not written one kind of machine at a time. Shapes are built from a few pieces, and each piece knows how to rename. ` +
    `{p1}A tuple renames each of its parts. {p2}A set renames its elements, sorts them, and drops duplicates. {p3}A distribution, or weights of any kind: rename, sort, and add up the weights that land in the same block. {p4}A flag or a label stays as it is.` },
  { id: 'types_comp', chapter: 'Any kind of machine', pre: 0.4, post: 0.6, text:
    `{comp}The pieces fit inside one another, and so do their functions. {dfa}The automaton's shape is a tuple of a flag and two states. {lts}Put a set around pairs of a label and a state, and you have a labelled transition system. ` +
    `{mdp}Put a set around distributions, and you have a Markov decision process, which has both choice and chance. {wlan}One of the benchmark models we will see has this shape: a number, with a set of pairs of a number and a distribution. Four pieces, nested. ` +
    `{own}So to describe a new kind of machine, you usually just write down its shape. {sig}Its signature function follows the shape: the outer piece calls the inner ones.` },
  { id: 'types_b', chapter: 'Any kind of machine', pre: 0.4, post: 0.9, text:
    `{earlier}The earlier fast algorithm could not take a combined shape as it is. {interm}It had to cut every state into intermediate states, between the pieces, which made the machine larger. {direct}Here, one state stays one state. ` +
    `{new}And when no combination fits, a new piece can be added. {mono}One comes from logics about games: a set of sets of states, in which any larger set also belongs. The earlier algorithm, which needs a special way of splitting blocks for every piece, could not handle that shape at all. ` +
    `{boa}In Boa, a new piece is a small amount of Rust: essentially its signature function.` },

  // ------------------------------------------------------------------------------------------------ measurements
  { id: 'bench_a', chapter: 'Measurements', pre: 1.9, post: 0.6, text:
    `{bench}Now the measurements. {suite}The benchmarks are from earlier work: models from a probabilistic model checker, and large, randomly generated tree automata with weights. {tools}Boa is compared with two general tools: the earlier fast algorithm, and a distributed version of the simple algorithm, running on a cluster with thirty-two workers. ` +
    `{caveat}Their numbers are the ones reported with the distributed tool, on that cluster's hardware. Boa's are from one core of a laptop. {rule}On the random benchmarks, roughly: where the earlier tool takes ten minutes, the cluster takes one minute, and Boa takes one second. ` +
    `{wlan}On one of the real models, the cluster needs almost an hour. Boa needs less than a second.` },
  { id: 'bench_b', chapter: 'Measurements', pre: 0.4, post: 0.6, text:
    `{memq}Memory often decides whether a machine can be minimized at all. {big}The biggest benchmark has over a million states, and almost two hundred million transitions. {out}The earlier tool runs out of memory on it. ` +
    `{cl}The cluster handles it, with about seven gigabytes on each of its thirty-two workers. {boa}Boa uses under two gigabytes in total, most of it for the machine itself.` },
  { id: 'bench_c', chapter: 'Measurements', pre: 0.4, post: 0.6, text:
    `{spec}What about a specialized tool? {mcrl}For plain transition systems, Boa is compared with a mature verification toolset, on a standard collection of very large transition systems. {faster}On every benchmark in the table, Boa is faster, typically by about ten times, and it uses several times less memory. ` +
    `{agree}And the two tools find the same number of blocks every time. {fair}To be fair: that toolset also supports other notions of equivalence, which this algorithm does not cover.` },
  { id: 'cool_three', chapter: 'Measurements', pre: 0.5, post: 0.6, text:
    `{so}So the general algorithm is the fast one. {why}Why? {r1}It keeps almost nothing besides the machine, in a compact form. {r2}It works on a combined shape directly, without cutting states into pieces. ` +
    `{r3}And when it comes back to a block, one pass accounts for everything that has changed since its last visit, where the earlier algorithm handles each change separately. {r4}These benchmarks do not even show its advantage over the simple algorithm in full: the random ones need only a few rounds.` },
  { id: 'limits', chapter: 'Measurements', pre: 0.5, post: 0.9, text:
    `{lim}What is left open? {other}Other notions of equivalence, such as trace equivalence and branching bisimilarity, do not fit this definition directly. They are future work. {factor}And in theory, the extra cost of computing signatures is the price of being general.` },

  // ------------------------------------------------------------------------------------------------ close
  { id: 'recap', chapter: 'Looking back', pre: 1.9, post: 0.7, text:
    `{r1}Many kinds of machine are one thing: states, each with a structure that has states inside, built from a few pieces. {r2}Equivalent states are found by guessing blocks, renaming, and comparing. {r3}Doing that for every state in every round is too slow. ` +
    `{r4}So recompute only the dirty states, and let the largest part of a split keep its name. {r5}That takes M times log N signatures, and little memory beyond the machine. {r6}The result is one tool for many kinds of machine, faster than the tools it was measured against.` },
  { id: 'end', chapter: 'Looking back', pre: 0.5, post: 3.0, text:
    `{title}Fast co-algebraic bisimilarity minimization. {paper}The paper has the formal definitions, the data structure in full, the complexity analysis, and all the measurements.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "hook",
   "chapter": "",
   "start": 0.0,
   "dur": 65.18,
   "pre": 0.8,
   "post": 0.7,
   "audio": 63.68,
   "cues": {
    "one": 0.8,
    "same": 5.84,
    "same2": 8.88,
    "merge": 10.56,
    "min": 15.12,
    "zoo": 23.6,
    "ts": 26.2,
    "mc": 27.36,
    "each": 29.52,
    "generic": 33.76,
    "video": 47.36,
    "claim": 52.64,
    "hand": 59.12,
    "why": 62.24
   }
  },
  {
   "id": "roadmap",
   "chapter": "",
   "start": 65.18,
   "dur": 22.22,
   "pre": 0.3,
   "post": 0.8,
   "audio": 21.12,
   "cues": {
    "coming": 0.3,
    "shape": 2.06,
    "equiv": 5.74,
    "naive": 9.42,
    "fast": 12.94,
    "types": 15.66,
    "bench": 19.66
   }
  },
  {
   "id": "title",
   "chapter": "",
   "start": 87.4,
   "dur": 5.2,
   "pre": 0.6,
   "post": 1,
   "audio": 3.6,
   "cues": {
    "title": 0.6
   }
  },
  {
   "id": "shape_a",
   "chapter": "One shape for many machines",
   "start": 92.6,
   "dur": 38.02,
   "pre": 1.9,
   "post": 0.6,
   "audio": 35.52,
   "cues": {
    "dfa": 1.9,
    "usual": 4.38,
    "state": 11.1,
    "s3": 14.22,
    "triple": 22.38,
    "table": 33.34
   }
  },
  {
   "id": "shape_b",
   "chapter": "One shape for many machines",
   "start": 130.62,
   "dur": 33.8,
   "pre": 0.4,
   "post": 0.6,
   "audio": 32.8,
   "cues": {
    "ts": 0.4,
    "succ": 4.84,
    "t3": 8.32,
    "t5": 12.293,
    "mc": 16.36,
    "m1": 19.76,
    "dist": 26.56,
    "lab": 30.267
   }
  },
  {
   "id": "shape_c",
   "chapter": "One shape for many machines",
   "start": 164.42,
   "dur": 45.62,
   "pre": 0.4,
   "post": 0.9,
   "audio": 44.32,
   "cues": {
    "pattern": 0.4,
    "states": 3.2,
    "struct": 4.8,
    "kind": 12.0,
    "k1": 14.8,
    "k2": 16.907,
    "k3": 18.32,
    "built": 20.88,
    "functor": 29.92,
    "coalg": 36.107,
    "no": 41.813
   }
  },
  {
   "id": "eq_a",
   "chapter": "Equivalent states",
   "start": 210.04,
   "dur": 31.06,
   "pre": 1.9,
   "post": 0.6,
   "audio": 28.56,
   "cues": {
    "q": 1.9,
    "circ": 4.46,
    "guess": 12.38,
    "blocks": 15.26,
    "subst": 19.34,
    "stable": 24.46
   }
  },
  {
   "id": "eq_b",
   "chapter": "Equivalent states",
   "start": 241.1,
   "dur": 35.24,
   "pre": 0.4,
   "post": 0.6,
   "audio": 34.24,
   "cues": {
    "d": 0.4,
    "num": 7.52,
    "r2": 15.68,
    "r3": 22.72,
    "ok": 29.84,
    "r45": 31.12,
    "st": 32.96
   }
  },
  {
   "id": "eq_c",
   "chapter": "Equivalent states",
   "start": 276.34,
   "dur": 64.12,
   "pre": 0.4,
   "post": 0.6,
   "audio": 63.12,
   "cues": {
    "ts": 0.4,
    "t12": 4.56,
    "s1": 12.08,
    "dup": 19.28,
    "s2": 25.36,
    "mc": 30.88,
    "m3": 37.52,
    "add": 46.24,
    "m2": 52.4,
    "norm": 57.72
   }
  },
  {
   "id": "eq_d",
   "chapter": "Equivalent states",
   "start": 340.46,
   "dur": 30.28,
   "pre": 0.4,
   "post": 0.6,
   "audio": 29.28,
   "cues": {
    "only": 0.4,
    "best": 6.64,
    "name": 10.72,
    "bisim": 14.08,
    "lang": 20.88,
    "min": 25.92
   }
  },
  {
   "id": "cool_one",
   "chapter": "Equivalent states",
   "start": 370.74,
   "dur": 15.32,
   "pre": 0.5,
   "post": 0.9,
   "audio": 13.92,
   "cues": {
    "three": 0.5,
    "diff": 2.62,
    "same": 10.06
   }
  },
  {
   "id": "naive_a",
   "chapter": "The simple algorithm",
   "start": 386.06,
   "dur": 37.3,
   "pre": 1.9,
   "post": 0.6,
   "audio": 34.8,
   "cues": {
    "how": 1.9,
    "opt": 4.86,
    "sig": 9.98,
    "r1": 17.313,
    "split1": 23.367,
    "two": 30.86
   }
  },
  {
   "id": "naive_b",
   "chapter": "The simple algorithm",
   "start": 423.36,
   "dur": 35.56,
   "pre": 0.4,
   "post": 0.6,
   "audio": 34.56,
   "cues": {
    "again": 0.4,
    "r2": 3.36,
    "r23": 7.04,
    "r45": 11.36,
    "three": 15.2,
    "once": 21.76,
    "r3": 22.96,
    "done": 27.76
   }
  },
  {
   "id": "naive_c",
   "chapter": "The simple algorithm",
   "start": 458.92,
   "dur": 30.58,
   "pre": 0.4,
   "post": 0.9,
   "audio": 29.28,
   "cues": {
    "general": 0.4,
    "cost": 6.48,
    "every": 8.16,
    "most": 11.76,
    "chain": 13.92,
    "sq": 21.4,
    "million": 26.72
   }
  },
  {
   "id": "idea_dirty",
   "chapter": "Two ideas",
   "start": 489.5,
   "dur": 37.38,
   "pre": 1.9,
   "post": 0.6,
   "audio": 34.88,
   "cues": {
    "first": 1.9,
    "when": 6.62,
    "so": 10.78,
    "dirty": 15.86,
    "only": 22.06,
    "clean": 25.127
   }
  },
  {
   "id": "idea_name",
   "chapter": "Two ideas",
   "start": 526.88,
   "dur": 23.16,
   "pre": 0.4,
   "post": 0.6,
   "audio": 22.16,
   "cues": {
    "second": 0.4,
    "free": 3.147,
    "large": 10.72,
    "unch": 13.6,
    "small": 19.92
   }
  },
  {
   "id": "trick",
   "chapter": "Two ideas",
   "start": 550.04,
   "dur": 44.52,
   "pre": 0.4,
   "post": 0.6,
   "audio": 43.52,
   "cues": {
    "game": 0.4,
    "set": 2.72,
    "follow": 6.16,
    "half": 7.84,
    "log": 13.92,
    "twenty": 17.08,
    "old": 20.04,
    "bound": 25.76,
    "edges": 30.08,
    "total": 37.76
   }
  },
  {
   "id": "algo",
   "chapter": "Two ideas",
   "start": 594.56,
   "dur": 29.18,
   "pre": 0.5,
   "post": 0.6,
   "audio": 28.08,
   "cues": {
    "algo": 0.5,
    "init": 2.86,
    "loop": 6.9,
    "pick": 8.42,
    "comp": 10.82,
    "split": 17.54,
    "mark": 22.1,
    "until": 26.58
   }
  },
  {
   "id": "run_a",
   "chapter": "Two ideas",
   "start": 623.74,
   "dur": 30.78,
   "pre": 0.5,
   "post": 0.6,
   "audio": 29.68,
   "cues": {
    "run": 0.5,
    "all": 2.5,
    "five": 6.66,
    "sp": 10.58,
    "pred": 19.86,
    "one": 27.06
   }
  },
  {
   "id": "run_b",
   "chapter": "Two ideas",
   "start": 654.52,
   "dur": 42.52,
   "pre": 0.4,
   "post": 0.6,
   "audio": 41.52,
   "cues": {
    "blockA": 0.4,
    "two": 2.08,
    "sigs": 6.56,
    "split": 15.88,
    "nobody": 23.76,
    "blockB": 28.68,
    "end": 35.04,
    "count": 37.36
   }
  },
  {
   "id": "cool_two",
   "chapter": "Two ideas",
   "start": 697.04,
   "dur": 13.72,
   "pre": 0.5,
   "post": 0.9,
   "audio": 12.32,
   "cues": {
    "never": 0.5,
    "inside": 3.22,
    "any": 9.38
   }
  },
  {
   "id": "ds_a",
   "chapter": "Fast in practice",
   "start": 710.76,
   "dur": 36.42,
   "pre": 1.9,
   "post": 0.6,
   "audio": 33.92,
   "cues": {
    "count": 1.9,
    "touch": 4.86,
    "arr": 12.54,
    "cd": 16.62,
    "mark": 20.7,
    "split": 25.82,
    "cost": 29.5
   }
  },
  {
   "id": "ds_b",
   "chapter": "Fast in practice",
   "start": 747.18,
   "dur": 31.3,
   "pre": 0.4,
   "post": 0.9,
   "audio": 30.0,
   "cues": {
    "mem": 0.4,
    "need": 3.2,
    "no": 8.8,
    "theory": 14.56,
    "k": 16.8,
    "practice": 26.28
   }
  },
  {
   "id": "types_a",
   "chapter": "Any kind of machine",
   "start": 778.48,
   "dur": 38.02,
   "pre": 1.9,
   "post": 0.6,
   "audio": 35.52,
   "cues": {
    "what": 1.9,
    "fn": 4.86,
    "kit": 11.26,
    "p1": 20.22,
    "p2": 23.02,
    "p3": 27.58,
    "p4": 34.54
   }
  },
  {
   "id": "types_comp",
   "chapter": "Any kind of machine",
   "start": 816.5,
   "dur": 44.12,
   "pre": 0.4,
   "post": 0.6,
   "audio": 43.12,
   "cues": {
    "comp": 0.4,
    "dfa": 4.72,
    "lts": 9.28,
    "mdp": 15.28,
    "wlan": 22.8,
    "own": 32.96,
    "sig": 38.16
   }
  },
  {
   "id": "types_b",
   "chapter": "Any kind of machine",
   "start": 860.62,
   "dur": 39.38,
   "pre": 0.4,
   "post": 0.9,
   "audio": 38.08,
   "cues": {
    "earlier": 0.4,
    "interm": 5.12,
    "direct": 11.76,
    "new": 14.64,
    "mono": 18.48,
    "boa": 32.88
   }
  },
  {
   "id": "bench_a",
   "chapter": "Measurements",
   "start": 900.0,
   "dur": 47.54,
   "pre": 1.9,
   "post": 0.6,
   "audio": 45.04,
   "cues": {
    "bench": 1.9,
    "suite": 3.5,
    "tools": 12.86,
    "caveat": 23.58,
    "rule": 31.66,
    "wlan": 40.7
   }
  },
  {
   "id": "bench_b",
   "chapter": "Measurements",
   "start": 947.54,
   "dur": 25.16,
   "pre": 0.4,
   "post": 0.6,
   "audio": 24.16,
   "cues": {
    "memq": 0.4,
    "big": 4.72,
    "out": 10.88,
    "cl": 13.76,
    "boa": 19.2
   }
  },
  {
   "id": "bench_c",
   "chapter": "Measurements",
   "start": 972.7,
   "dur": 31.72,
   "pre": 0.4,
   "post": 0.6,
   "audio": 30.72,
   "cues": {
    "spec": 0.4,
    "mcrl": 2.72,
    "faster": 12.16,
    "agree": 20.72,
    "fair": 24.64
   }
  },
  {
   "id": "cool_three",
   "chapter": "Measurements",
   "start": 1004.42,
   "dur": 32.62,
   "pre": 0.5,
   "post": 0.6,
   "audio": 31.52,
   "cues": {
    "so": 0.5,
    "why": 3.46,
    "r1": 4.5,
    "r2": 8.9,
    "r3": 13.967,
    "r4": 24.1
   }
  },
  {
   "id": "limits",
   "chapter": "Measurements",
   "start": 1037.04,
   "dur": 18.92,
   "pre": 0.5,
   "post": 0.9,
   "audio": 17.52,
   "cues": {
    "lim": 0.5,
    "other": 2.34,
    "factor": 12.18
   }
  },
  {
   "id": "recap",
   "chapter": "Looking back",
   "start": 1055.96,
   "dur": 37.24,
   "pre": 1.9,
   "post": 0.7,
   "audio": 34.64,
   "cues": {
    "r1": 1.9,
    "r2": 10.5,
    "r3": 15.3,
    "r4": 19.26,
    "r5": 25.26,
    "r6": 30.66
   }
  },
  {
   "id": "end",
   "chapter": "Looking back",
   "start": 1093.2,
   "dur": 15.26,
   "pre": 0.5,
   "post": 3,
   "audio": 11.76,
   "cues": {
    "title": 0.5,
    "paper": 4.9
   }
  }
 ],
 "total": 1108.46
};

// ==== src/scenes/common.js ====
// Shared pieces of the Boa video ("Fast Coalgebraic Bisimilarity Minimization"), as window.BX. Loaded after
// engine.js, before the scene files. Everything here only builds elements and puts keys on the scene's timeline
// `tl`; nothing is visible until a time says so. Coordinates are stage pixels (1920 x 1080); times are seconds on
// the scene's clock. Colours follow SCENES.md: ink = states, edges, letters, flags, numbers; cyan C.bind = a block
// name (tabs, renamed structures); amber C.pat = dirty; green C.good = agrees / stable; red C.bad only "OUT OF
// MEMORY". Call the methods of one object in time order (they keep track of what is where as they go).
//
// ---- constants -----------------------------------------------------------------------------------------------
//   BX.CX = 960 (stage centre), BX.RAIL = 160 (the left rail), BX.LINE = 3 (drawing line width).
//
// ---- type (as SX) ----------------------------------------------------------------------------------------------
//   BX.LABEL(size) / BX.SERIF(size) / BX.MONO(size): style objects (small caps sans in C.dim, serif in C.ink, mono
//     in C.code without ligatures). Pass them to box(), or Object.assign(BX.LABEL(32), {color: C.ink}).
//     Labels in this video are at least 32 px. Small caps text: letters, digits, basic punctuation, "·" only.
//   BX.cline(root, cx, y, parts, style) -> {root, parts}: one line centred on cx, top at y, made of parts
//     [[text, colour|null], ...]; each part is its own inline span (fade, strike or colour it by itself).
//   BX.lline(root, x, y, parts, style) -> {root, parts}: the same, left edge at x.
//   BX.clabel(root, cx, y, text, size=32, colour) -> el   centred small caps label (top at y).
//   BX.cserif(root, cx, y, text, size=56, colour) -> el   centred serif line (top at y).
//   BX.note(tl, root, x, y, text, at, out, {size=32, color=C.dim, align='center'|'left', dy=10}) -> el
//     a label that rises in at `at` and leaves at `out` (out may be null: it stays). x is its centre, or its
//     left edge with align 'left'; y its top.
//   BX.strikeEl(tl, el, at, {out, faint=true}) -> {line, undo(at)}: the neutral grey strike through an element
//     (a span of cline, a label); its text goes C.faint. undo(at) takes the strike back and restores the colour.
//
// ---- small drawings (as SX) --------------------------------------------------------------------------------------
//   BX.svg(root): an SVG layer over the whole stage (engine's svgLayer).
//   BX.tick(tl, svg, x, y, size=48, at, {color=C.good, width=6}) -> {els, hide(at)}  a tick drawn in at `at`.
//   BX.cross(tl, svg, x, y, size=40, at, {color=C.bad, width=6}) -> {els, hide(at)}  (red: only for a failure).
//   BX.dpath(tl, svg, d, {stroke=C.ink, width=3, dash}) -> path el with a `draw` key (0..1) also when dashed.
//     Draw with tl.to(p, {draw: 1}, at, dur, E.io); fade with {o}.
//   BX.line(tl, svg, x1, y1, x2, y2, {at, dur=0.5, bend=0, dash, stroke=C.ink, width=3, head=14}) -> {path, head,
//     hide(at)}: an arrow (head=0: a plain line) drawn in at `at` (omit `at` to draw it yourself: tl.to(a.path,
//     {draw: 1}, ...) and tl.to(a.head, {o: 1}, ...)). bend > 0 bends it to the right of the direction of travel
//     (below a left-to-right arrow). A dashed green link: {dash: '12 10', stroke: C.good, head: 0}.
//   BX.arc(tl, svg, x1, x2, y, depth, {at, dur=0.5, stroke, width, dash, up=false}) -> path: a round arc from
//     (x1, y) to (x2, y) bulging `depth` px down (up: true, up).
//   BX.bracket(tl, svg, x1, x2, y, {at, dur=0.6, legs='up'|'down', depth=18, notch=0, stroke=C.ink, width=3})
//     -> path: a square bracket along y from x1 to x2 whose two legs point up (a bracket under things) or down (a
//     bracket over things), with an optional notch at the middle pointing the other way. Drawn in at `at`.
//   BX.cell(parent, x, y, w, h, text, {stroke, color, font, radius, width}) -> box el, its text el in ._t
//   BX.flip(tl, textEl, text, at, dur=0.45): a text squeezes, changes, comes back.
//   BX.circleD(x, y, r): an SVG path string for a circle.
//   BX.ctext(parent, cx, cy, text, style, h): a box with text centred on (cx, cy), h px high.
//   BX.dim(tl, els, o, at, dur=0.5): opacity of many elements (or of things with a .root / .g).
//
// ---- state chips: BX.Chip ----------------------------------------------------------------------------------------
//   const c = new BX.Chip(tl, parent, cx, cy, text, {r=26, size (number size, default max(22, round(r * 1.2))),
//     accepting=false (a second, inner border), line=3, italic=false})
//   A small copy of a state's circle with its number (serif), centred on (cx, cy). Hidden until shown. Machine
//   states are Chips too. text may be '' (an unnumbered chip) or a letter ('s', 't' are set in italic with italic).
//   c.show(at, {draw=false, dur=0.5, dy=10}) fades in (draw: the circle is drawn round, then the number fades in).
//   c.hide(at, dur=0.35)        c.dim(o, at, dur=0.4)        c.move(dx, dy, at, dur=0.8)   (offsets from build)
//   c.pulse(at, {dur=0.6, scale=1.1})  grows a little in a soft neutral disc, and back (its ring with it).
//   c.mark(at, {color=C.dim, fill=0.1, out}) -> el   a soft disc behind it (the neutral "look here", or green).
//   c.dirty(at) / c.clean(at)   the amber ring (radius r + 9, 4 px) appears / goes out.
//   c.color(colour, at) / c.recolor(at)   the circle's line colour.     c.flip(text, at)  the number changes.
//   c.x, c.y, c.r, c.g (the group: a div, its transform origin the chip's centre), c.circle() -> {x, y, r}.
//
// ---- block outlines: BX.Block, BX.tab ------------------------------------------------------------------------------
//   const b = new BX.Block(tl, parent, items, name, {at, out, pad=20, tab='nw', tabDx=0, tabDy=0, tabSize=32,
//     dur=0.6, width=2.5, resolve})
//   A thin cyan rounded outline around `items` with a cyan tab carrying `name` (name '' or null: no tab). Items
//   are circles {x, y, r} (a Chip's c.circle()), rectangles {x, y, w, h} (top-left), or whatever `resolve` turns
//   into those (a Machine passes state numbers). The outline is the convex hull of the items, `pad` px further
//   out, with round corners. The tab sits on the outline at the side named by `tab` ('n', 'ne', 'e', 'se', 's',
//   'sw', 'w', 'nw'), nudged by tabDx, tabDy; tab: {x, y} puts its centre there. With `at` it is drawn in then
//   (outline drawn round, tab pops in at at + 0.6 * dur); `out` hides it then.
//   b.show(at, {dur}) / b.hide(at, dur=0.35) / b.dim(o, at, dur=0.4)
//   b.pulse(at, {dur=0.6})       the outline thickens and the tab grows a little, and back.
//   b.rename(name, at)           the tab's letter flips (a tab can be added this way to a block without one).
//   b.split(at, parts, {dur=0.6}) -> [Block, ...]   parts: [[items, name, opts], ...]. The outline is replaced by
//     one outline per part: the old one fades out at `at`, the new ones are drawn from at + 0.15. The part whose
//     name is this block's name keeps the tab: it glides to its new place. The other tabs pop in at at + 0.5 (a
//     name '?' is fine; rename it later). opts as for the constructor (tab, pad, ...). Use the new blocks after.
//   b.rect() -> {x, y, w, h, cx, cy} (the outline's box), b.tabPos() -> {x, y} (the tab's centre, after any glide),
//   b.path, b.tabEl, b.name, b.items.
//   BX.tab(parent, cx, cy, name, {size=32}) -> el   a free-standing cyan tab (hidden until faded in).
//
// ---- the machines: BX.Machine ---------------------------------------------------------------------------------------
//   const m = new BX.Machine(tl, parent, {kind: 'dfa' | 'ts' | 'mc' | 'dfa3', cx=960, cy=500, scale=1})
//   One of the machines of the paper's Figure 1 in the fixed layout (state 1 top centre; 2, 3 middle row; 4, 5
//   bottom row), centred on (cx, cy). scale multiplies distances and the circles (radius 36 * scale); lines stay
//   3 px; state numbers are serif max(24, 30 * scale); edge labels mono max(24, 28 * scale). At scale 1 the drawing
//   is about 680 x 560 px (m.bounds() has the exact box). 'dfa': the automaton (letters a, b; 4, 5 accepting;
//   5 -> 4 is one edge labelled 'a, b'). 'ts': the transition system (no labels). 'mc': the Markov chain (labels the
//   probabilities; 4 accepting). 'dfa3': the minimized automaton, states 1, 2, 4 where they are in 'dfa'
//   (1 -a, b-> 2; 2 -a-> 4; 2 -b-> 2; 4 -a, b-> 4). Nothing is visible until shown.
//   Edge ids: 'from>to' (a loop is 'k>k'). m.edges lists them ({id, from, to, label}).
//   Selectors `sel` (for every method below that takes one): a state number (3 or '3'); an edge id ('3>5', '3>3'; '1>2:a, b'
//   also checks the label); 'out:3' (the edges out of 3, its loop included), 'in:4' (the edges
//   into 4, its loop included); 'states', 'edges', 'all'; an array of these; a function (rec) -> bool, where rec
//   is {type: 'state', k} or {type: 'edge', id, from, to, label}.
//   m.show(at, {sel='all', stagger=0.12, dur=0.5}) -> end time   draws in: the states first (circle drawn round,
//     number), then the edges (line drawn, head, label), one after another in the order of m.edges.
//   m.appear(at, {sel='all', dur=0.5})   everything in `sel` fades in at once (no drawing).
//   m.dim(sel, o, at, dur=0.4) / m.light(sel, at, dur=0.4) (= dim to 1) / m.hide(at, dur=0.4) (the whole drawing)
//   m.focus(sel, at, {o=0.3, dur=0.4})  `sel` at full, everything else dimmed to o.
//   m.pulse(sel, at, {dur=0.6})   a state grows in a soft neutral disc; an edge's line thickens and its label grows.
//   m.mark(sel, at, {color=C.dim, fill=0.1, out}) -> [els]   lasting "look here": a soft disc behind a state, a
//     soft wide band along an edge (pass color: C.good etc. for a meaning). Hide with `out` or tl.to(el, {o: 0}).
//   m.color(sel, colour, at, dur=0.35) / m.recolor(sel, at)   an edge's line and head (its label stays ink), a
//     state's circle. Amber (C.pat) is for an edge that makes a state dirty while it is being followed.
//   m.dirty(ks, at) / m.clean(ks, at)   the amber ring on a state (ks: a number or an array).
//   m.slide(k, target, at, dur=0.8)    state k (circle, number, ring) moves onto state `target` (a number) or to
//     {x, y}; its edges are not moved (fade them first).
//   m.travel(id, at, dur=0.8, {color=C.ink, r=9, out}) -> dot   a dot runs along an edge.
//   m.to(props, at, dur=0.8, ease)   the whole drawing ({x, y, s, o}; s scales about (cx, cy)).
//   m.block(states, name, at, {out, tab, tabDx, tabDy, pad=20 * scale, dur}) -> Block   a cyan outline around
//     those states (drawn under the edges; its tab over them). The label of an edge between two of its states
//     that the outline would cross is taken inside it (the automaton's {4, 5} reaches around the 'a' under it). The tab's side is chosen for each block of the
//     storyboard so that it covers no state and no label; pass tab to choose. Split it with
//     block.split(at, [[[2, 3], 'X'], [[1], 'Z']]) (parts given as state numbers).
//   m.pos(k) -> {x, y} (stage centre of a state), m.r (circle radius), m.circle(k) -> {x, y, r},
//   m.state(k) -> the Chip, m.edge(from, to, label) -> {id, g, path, head, lab, ...},
//   m.labelPos(id) -> {x, y} centre of an edge's label, m.bounds() -> {x0, y0, x1, y1, cx, cy} of the drawing,
//   m.g (the group), m.k (the scale).
//
// ---- structures: BX.Struct, and the table: BX.Table ----------------------------------------------------------------
//   const s = new BX.Struct(tl, parent, x, y, text, {size=52, align='left'|'center', at, stagger=0.03})
//   One structure or signature in mono on a character grid: x is its left edge (with align 'center', its centre
//   as first built), y the line's vertical MIDDLE. Tokens: a state number (a digit not after ':'), a block name
//   (X, Y, Z: cyan), a weight (what follows ':', e.g. ½, ⅓, 1), true / false, other words, and single symbols.
//   Spaces are columns. Hidden until shown.
//   s.parts: [{el, text, kind ('state' | 'block' | 'w' | 'flag' | 'word' | 'sym'), col, len}] (the current ones).
//   A part selector `psel`: an index, an array of indices, 'all' (default), 'states', 'blocks', 'weights',
//   a string (every part with that text), a RegExp on the text, a function (part, i), {from, to} (inclusive).
//   s.show(at, {sel='all', stagger=0.03, rise=12, dur=0.5})    s.hideParts(psel, at)    s.hide(at, dur=0.4)
//   s.dim(psel, o, at, dur=0.4) / s.light(psel, at)          opacity of parts.
//   s.color(psel, colour, at) / s.recolor(psel, at)
//   s.pulse(psel, at, {dur=0.5})          the parts grow a little in a soft neutral box, and back.
//   s.mark(psel, colour, at, {out, fill=0.12, pad=6}) -> el     a soft box behind parts (C.dim fill 0.08: neutral).
//   s.underline(psel, colour, at, {out}) -> [els]               a thin line under each part (eq_a's cyan lines).
//   s.strike(psel, at, {out, fade=true}) -> {line, undo(at)}    the neutral grey strike.
//   s.flip(i, text, at, {color}) -> part   part i squeezes and reads `text` (the same width).
//   s.rename(map, at, {stagger=0, dur=0.45})  each state part whose number is in map flips to its block name (cyan).
//     map: {X: [2, 3], Y: [4, 5], Z: [1]} (blocks), or {'4': 'Y', '3': 'X'} (state -> name).
//   s.morph(text, at, {dur=0.6})   the line becomes `text`: parts that stay slide to their new columns; a changed
//     part in the same place flips (¼ -> ½); a run of left-over parts that contains a block or state equal to one
//     that stays slides onto it and fades ("the two Y slide together", "{X: ¼} joins {X: ¼}"); other left-overs
//     fade; new parts fade in (the "(false, " and ")" around a distribution). Settled at at + dur.
//   s.merge = s.morph.     s.set(text, at, {dur=0.5})  the old line fades out, the new one rises in (a new signature).
//   s.rect(psel='all', pad=0) -> {x, y, w, h, cx, cy}  stage box of parts (current columns).  s.width (current px),
//   s.cols, s.cw (px per column), s.lh, s.colX(c), s.to(props, at, dur, ease) (the whole line), s.root.
//
//   const t = new BX.Table(tl, parent, x, y, rows, {size=52, pitch=92, cy, chipR=round(size * 0.52),
//     gap=round(size * 0.5), accepting=[]})
//   The table of structures: one row per [k, text] of `rows` (or {k, text}); k is the state number (any key works;
//   its text is the chip's number). Row i's middle is y + i * pitch (with opts.cy, the rows are centred on cy
//   instead). Each row is a Chip (left edge at x, radius chipR) and a Struct (from x + 2 * chipR + gap). text ''
//   gives a chip with no structure yet (set it later). Rows are addressed by k. `ks` below is a k, an array of
//   them, or 'all'.
//   t.show(at, {stagger=0.12})                   every row: chip, then its structure.
//   t.showRow(k, at, {parts='all', chip=true})   one row (or some parts of its structure: build it in steps).
//   t.hideRow(k, at) / t.hide(at, dur=0.4) / t.to(props, at, dur, ease) (the whole table)
//   t.set(k, text, at)       the structure is replaced (fade out, new one in): the next round's signature.
//   t.rename(k, map, at, opts) / t.morph(k, text, at, opts) / t.merge(k, text, at, opts)   as Struct.
//   t.fade(ks, o=0.3, at, dur=0.4)   structures only (a signature out of date goes faint; fade(k, 1, at) back).
//   t.dim(ks, o, at, {part='both'|'chip'|'struct', dur=0.4}) / t.light(ks, at, {part})   opacity of rows.
//   t.pulse(k, at, {part='all'})   the structure's parts (psel), or the chip with part: 'chip'.
//   t.mark(k, at, {part='all', color=C.dim, fill=0.08, out}) -> el    t.underline(k, part, colour, at, {out})
//   t.strike(k, at, {out})       t.dirty(ks, at) / t.clean(ks, at)   the amber ring on the chip.
//   t.equal(k1, k2, at, {x, tick=true}) -> {els, hide(at)}   a green bracket at the right of the two rows (x: its
//     left; default 30 px right of the wider of the two structures as they are then), with a green "=" beside
//     its middle and a green tick after it (about 150 px wide in all).
//   t.chip(k) -> Chip, t.struct(k) -> Struct, t.rowY(k) (the row's middle), t.rect(k, part='all') (the structure's
//   stage box), t.structX (the structures' left edge), t.rows (in order).
//
// ---- pieces and nests (the chapter on kinds of machine) -----------------------------------------------------
//   BX.piece(parent, x, y, text, {size=30, align='left'|'center', dashed=false, color=C.ink}) -> el   a piece chip:
//     a rounded rectangle with a 2 px line and the piece's name in small caps ('\n' breaks it into lines); x its left
//     edge (or centre), y its middle; el._w, el._h. Hidden only once you fade it (fadeIn sets o 0 at 0).
//   const n = new BX.Nest(tl, parent, spec, cx, cy, {size=30, pad=16, gap=14, stateR=26})   nested boxes centred
//     on (cx, cy). spec: {box: 'tuple', id, items: [spec, ...]} (a box with its name on a tab at its top left, its
//     items side by side inside it), {leaf: 'flag', id} (a piece chip), {state: true, id} (a state circle, no number).
//     Every node is its own element, hidden until shown. n.show(id, at) one node; n.showTree(id, at, {stagger}) a node
//     and its contents, outside in; n.pulse(id, at) a box's tab grows and back; n.glow(id, at, {dur}) a soft band of
//     light fills a box and goes; n.to(props, at, dur), n.dim(o, at) (the whole nest; s scales about its centre);
//     n.node(id) -> {x, y, w, h, els}; n.w, n.h, n.top, n.bottom.
//
// ---- counters, cells, bars ---------------------------------------------------------------------------------------------
//   const n = new BX.Counter(tl, parent, x, y, label, {value=0, size=48, labelSize=32, align='left'|'right', gap=22})
//   A small caps label and a mono number on one line, the number after the label; x is the left edge (align
//   'right': the right edge of the number), y the line's vertical middle. Hidden until shown.
//   n.show(at)   n.set(v, at, {step=0})  the number changes to v (step > 0: it counts one by one, `step` s apart,
//   from the value set before). n.pulse(at)   n.color(colour, at) (e.g. C.good)   n.dim(o, at)   n.hide(at)
//   n.el (the line), n.num (the number span), n.labelEl, n.value (as last set), n.bottom (y below the line).
//
//   const c = new BX.Cells(tl, parent, x, y, n, {w=96, h=96, gap=10, size=40, texts=[], align='left'|'center',
//     stroke=C.ink})
//   A row of n square cells (x: the left edge, or the centre with align 'center'; y: the top). A cell is named by
//   its id 0..n-1 (it keeps its id when it moves); a slot is a position in the row 0..n-1. Hidden until shown.
//   c.show(at, {stagger=0.04})        c.hide(at)   c.to(props, at, dur, ease)
//   c.text(i, s)                      cell i's text, from the start (no time).   c.flip(i, s, at)
//   c.swap(i, j, at, {dur=0.7})       cells i and j change places (i passes above, j below).
//   c.move(order, at, {dur=0.8})      order: the cell ids in their new slot order; cells that change slot move
//                                     (leftwards above the row, rightwards below it), the others stay.
//   c.outline(i, colour, at)          cell i's line in a colour (C.pat: dirty); colour null: back to ink.
//   c.fill(i, colour, at)             cell i filled (its text turns the page colour); null: unfilled.
//   c.dim(ids, o, at) / c.dimSlots(s0, s1, o, at)   opacity of cells (by id, or the cells now in slots s0..s1).
//   c.bracket(s0, s1, name, at, {out, depth=16}) -> {path, tab, hide(at), rename(name, at)}  a bracket under the
//                                     slots s0..s1 with a cyan tab under its middle (name '' : no tab).
//   c.divider(s, at) -> {el, move(s2, at), hide(at)}   a vertical line before slot s (between s - 1 and s).
//   c.gap(s, px, at, {dur=0.6})       slots s and after move px to the right (gaps add up; brackets, dividers
//                                     made after it use the new places).
//   c.slotX(s) (left edge of slot s now), c.slotOf(i), c.cellRect(i) -> {x, y, w, h, cx, cy}, c.els (by id).
//
//   const b = BX.bars(tl, parent, x, y, rows, {scale='log'|'linear', min=1, max, w=900, h=40, pitch=130,
//     minLen=10, names=true, nameX=x - 40, nameSize=48, textSize=36, unit=''})
//   Horizontal bars growing right from x; row i's middle at y + i * pitch. rows: [{name, value, text, good,
//   segments}]: text (default value + unit) sits after the bar's end; good: true makes the bar and its text
//   green (Boa), otherwise the bar is C.dim and the text ink; segments: n draws the bar as n thin pieces (32
//   workers). Length: linear: w * value / max; log: w * log(value / min) / log(max / min); at least minLen.
//   names: the name in serif, right-aligned to nameX (false: no names, when the scene sets them itself).
//   b.grow(at, {stagger=0.3, dur=0.8, rows})   bars grow in, then their texts appear.
//   b.set(i, {value, text}, at, {dur=0.7})     a bar changes length and text.
//   b.replace(i, text, colour, at)             the bar and its text leave; `text` (small caps) takes its place
//                                              (C.bad for "OUT OF MEMORY").
//   b.hide(at)   b.rows: [{bar, text, name, len}]   b.len(value) -> px.
//
// ---- the title, and rows -------------------------------------------------------------------------------------------
//   BX.titleCard(tl, root, {align='center'|'left', x, y=300, size=110, at, lineGap=0.25, authorsAt,
//     authorSize=32, gap=34}) -> {lines: [l1, l2], authors: [a1, a2], bottom}: "Fast Coalgebraic" and
//     "Bisimilarity Minimization" (serif, two lines from y), then "Jules Jacobs · Thorsten Wißmann" (it reads
//     WISSMANN in small caps) and "POPL 2023". A time left out means that part is not shown.
//   const rows = new BX.Rows(tl, root, {x=160, y, pitch, size=56, numbers=true, titleX=x + 70, back=0.6})
//   rows.row(title, at, {num}) -> row {y, at, parts, add(el), num, title}: a numbered serif row rising in; when a
//     later row arrives, the earlier rows (with everything add()ed to them) step back to opacity `back`.
//   rows.evidence(i, el, at, dy=14) fades `el` (or a thing with .root / .g) in and adds it to row i.
//   rows.mid(i): the y of row i's middle.   rows.all(): every element.
'use strict';
(function () {
  const { W, H, C, E } = Film;
  const CX = W / 2, RAIL = 160, LINE = 3;

  // ---- type ----------------------------------------------------------------------------------------------------
  const LS = 0.16;
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase', color: C.dim, lineHeight: 1.2 });
  const SERIF = size => ({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, letterSpacing: '-0.005em' });
  const MONO = size => ({ fontFamily: 'var(--mono)', fontSize: size + 'px', lineHeight: 1.3, color: C.code, fontVariantLigatures: 'none', fontWeight: 450 });

  function partsLine(b, parts) {
    return parts.map(([t, col]) => {
      const s = document.createElement('span');
      Object.assign(s.style, { display: 'inline-block', position: 'relative', whiteSpace: 'pre' });
      if (col) s.style.color = col;
      s.textContent = t; b.appendChild(s);
      return s;
    });
  }
  function cline(root, cx, y, parts, style) {
    const b = box(root, cx - 1200, y, Object.assign({ width: '2400px', textAlign: 'center', whiteSpace: 'pre' }, style));
    if (style.letterSpacing) b.style.paddingLeft = style.letterSpacing;
    return { root: b, parts: partsLine(b, parts) };
  }
  function lline(root, x, y, parts, style) {
    const b = box(root, x, y, Object.assign({ whiteSpace: 'pre' }, style));
    return { root: b, parts: partsLine(b, parts) };
  }
  const clabel = (root, cx, y, text, size = 32, col) => cline(root, cx, y, [[text, col]], LABEL(size)).root;
  const cserif = (root, cx, y, text, size = 56, col) => cline(root, cx, y, [[text, col]], SERIF(size)).root;
  function note(tl, root, x, y, text, at, out, { size = 32, color = C.dim, align = 'center', dy = 10 } = {}) {
    const e = align === 'left' ? box(root, x, y, Object.assign(LABEL(size), { color, whiteSpace: 'pre' }), text) : clabel(root, x, y, text, size, color);
    fadeIn(tl, e, at, 0.5, dy);
    if (out != null) fadeOut(tl, e, out, 0.3, -8);
    return e;
  }
  function strikeEl(tl, span, at, { out = null, faint = true } = {}) {
    const u = el(span, 'div', { left: '-0.12em', right: '-0.02em', top: '52%', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
    const col0 = span.style.color || null;
    tl.set(u, { sx: 0, o: 0 }, 0); tl.set(u, { o: 1 }, at); tl.to(u, { sx: 1 }, at, 0.45, E.io);
    if (faint) tl.to(span, { color: C.faint }, at, 0.45);
    if (out != null) tl.to(u, { o: 0 }, out, 0.3);
    return { line: u, undo(t) { tl.to(u, { sx: 0 }, t, 0.4, E.io); if (faint) tl.to(span, { color: col0 || C.ink }, t, 0.4); } };
  }

  // ---- drawings ------------------------------------------------------------------------------------------------
  const circleD = (x, y, r) => `M ${x - r} ${y} a ${r} ${r} 0 1 0 ${2 * r} 0 a ${r} ${r} 0 1 0 ${-2 * r} 0`;
  function ctext(parent, cx, cy, text, style, h) {
    return box(parent, cx - 400, cy - h / 2, Object.assign({ width: '800px', height: h + 'px', display: 'flex', alignItems: 'center', justifyContent: 'center', whiteSpace: 'pre' }, style), text);
  }
  function cell(parent, x, y, w, h, text, { stroke = C.ink, color = C.ink, font = MONO(44), radius = 14, width = LINE } = {}) {
    const b = box(parent, x, y, { width: w + 'px', height: h + 'px', borderRadius: radius + 'px', boxShadow: `inset 0 0 0 ${width}px ${stroke}` });
    const t = box(b, 0, 0, Object.assign({ width: w + 'px', height: h + 'px', display: 'flex', alignItems: 'center', justifyContent: 'center', whiteSpace: 'pre' }, font, { color }), text);
    b._t = t;
    return b;
  }
  function flip(tl, t, text, at, dur = 0.45) {
    tl.to(t, { sy: 0.05 }, at, dur * 0.4, E.in); tl.text(t, text, at + dur * 0.4); tl.to(t, { sy: 1 }, at + dur * 0.4, dur * 0.6, E.out);
  }
  const rootOf = e => (e && (e.root || e.g)) || e;
  function dim(tl, els, o, at, dur = 0.5) { for (const e of [].concat(els)) tl.to(rootOf(e), { o }, at, dur); }

  function tickM(tl, svg, x, y, size = 48, at, { color = C.good, width = 6 } = {}) {
    const p = tick(tl, svg, x, y, size, color, width);
    if (at != null) tl.to(p, { draw: 1 }, at, 0.4, E.out);
    return { els: [p], hide(t) { tl.to(p, { o: 0 }, t, 0.3); } };
  }
  function crossM(tl, svg, x, y, size = 40, at, { color = C.bad, width = 6 } = {}) {
    const ps = cross(tl, svg, x, y, size, color, width);
    if (at != null) ps.forEach((p, i) => tl.to(p, { draw: 1 }, at + i * 0.12, 0.28, E.out));
    return { els: ps, hide(t) { ps.forEach(p => tl.to(p, { o: 0 }, t, 0.3)); } };
  }

  let maskN = 0;
  const NS = 'http://www.w3.org/2000/svg';
  function dpath(tl, svg, d, { stroke = C.ink, width = LINE, dash } = {}) {
    if (!dash) return path(tl, svg, d, { stroke, width });
    const id = 'bxm' + (++maskN);
    const mask = document.createElementNS(NS, 'mask');
    mask.setAttribute('id', id); mask.setAttribute('maskUnits', 'userSpaceOnUse');
    mask.setAttribute('x', -W); mask.setAttribute('y', -H); mask.setAttribute('width', 3 * W); mask.setAttribute('height', 3 * H);
    svg.appendChild(mask);
    const m = path(tl, mask, d, { stroke: '#ffffff', width: width + 8, cap: 'butt' });
    const p = path(tl, svg, d, { stroke, width, dash, cap: 'butt' });
    p.setAttribute('mask', `url(#${id})`);
    tl.custom(p, 'draw', (e, v) => { m.style.strokeDashoffset = (m._len * (1 - v)).toFixed(2); m.style.strokeOpacity = v <= 0.002 ? 0 : 1; }, 0);
    p._len = m._len;
    return p;
  }
  function headEl(svg, x, y, ang, { stroke = C.ink, width = LINE, head = 14 } = {}) {
    const h = el(svg, 'path');
    h.setAttribute('d', `M ${-head} ${-head * 0.55} L 0 0 L ${-head} ${head * 0.55}`);
    h.setAttribute('fill', 'none'); h.setAttribute('stroke-width', width); h.setAttribute('stroke-linecap', 'round'); h.setAttribute('stroke-linejoin', 'round');
    h.style.stroke = stroke; h.style.opacity = 0;
    h.setAttribute('transform', `translate(${x} ${y}) rotate(${ang * 180 / Math.PI})`);
    return h;
  }
  function line(tl, svg, x1, y1, x2, y2, { at, dur = 0.5, bend = 0, dash, stroke = C.ink, width = LINE, head = 14 } = {}) {
    const a = arrowPath(x1, y1, x2, y2, bend);
    const p = dpath(tl, svg, a.d, { stroke, width, dash });
    let h = null;
    if (head) { h = headEl(svg, x2, y2, Math.atan2(y2 - a.cy, x2 - a.cx), { stroke, width, head }); tl.set(h, { o: 0 }, 0); }
    if (at != null) { tl.to(p, { draw: 1 }, at, dur, E.io); if (h) tl.fromTo(h, { o: 0 }, { o: 1 }, at + dur * 0.75, dur * 0.25); }
    return { path: p, head: h, hide(t, d = 0.3) { tl.to(p, { o: 0 }, t, d); if (h) tl.to(h, { o: 0 }, t, d); } };
  }
  function arc(tl, svg, x1, x2, y, depth, { at, dur = 0.5, stroke = C.ink, width = LINE, dash, up = false } = {}) {
    const k = up ? -1 : 1, c = depth * 4 / 3 * k;
    const p = dpath(tl, svg, `M ${x1} ${y} C ${x1} ${y + c} ${x2} ${y + c} ${x2} ${y}`, { stroke, width, dash });
    if (at != null) tl.to(p, { draw: 1 }, at, dur, E.io);
    return p;
  }
  function bracket(tl, svg, x1, x2, y, { at, dur = 0.6, legs = 'up', depth = 18, notch = 0, stroke = C.ink, width = LINE } = {}) {
    const s = legs === 'up' ? -1 : 1, m = (x1 + x2) / 2;
    let d = `M ${x1} ${y + s * depth} L ${x1} ${y} L ${x2} ${y} L ${x2} ${y + s * depth}`;
    if (notch) d = `M ${x1} ${y + s * depth} L ${x1} ${y} L ${m} ${y} L ${m} ${y - s * notch} M ${m} ${y} L ${x2} ${y} L ${x2} ${y + s * depth}`;
    const p = path(tl, svg, d, { stroke, width });
    if (at != null) tl.to(p, { draw: 1 }, at, dur, E.io);
    return p;
  }

  // ---- chips -----------------------------------------------------------------------------------------------------
  class Chip {
    constructor(tl, parent, cx, cy, text, { r = 26, size, accepting = false, line = LINE, italic = false } = {}) {
      Object.assign(this, { tl, x: cx, y: cy, r });
      const R0 = r + 18; this.R0 = R0;
      this.g = box(parent, cx - R0, cy - R0, { width: 2 * R0 + 'px', height: 2 * R0 + 'px', transformOrigin: 'center center' });
      // the soft disc of a pulse or a mark, under everything
      this.halo = box(this.g, R0 - r - 12, R0 - r - 12, { width: 2 * (r + 12) + 'px', height: 2 * (r + 12) + 'px', borderRadius: '50%', background: alpha(C.dim, 0.12) });
      tl.set(this.halo, { o: 0 }, 0);
      const s = el(this.g, 'svg');
      s.setAttribute('width', 2 * R0); s.setAttribute('height', 2 * R0); s.setAttribute('viewBox', `0 0 ${2 * R0} ${2 * R0}`);
      Object.assign(s.style, { position: 'absolute', left: 0, top: 0, overflow: 'visible' });
      this.svg = s;
      this.circ = path(tl, s, circleD(R0, R0, r), { stroke: C.ink, width: line });
      this.inner = accepting ? path(tl, s, circleD(R0, R0, r - Math.max(5, r * 0.16)), { stroke: C.ink, width: line * 0.85 }) : null;
      this.ring = el(s, 'path'); this.ring.setAttribute('d', circleD(R0, R0, r + 9)); this.ring.setAttribute('fill', 'none'); this.ring.setAttribute('stroke-width', 4);
      this.ring.style.stroke = C.pat; tl.set(this.ring, { o: 0 }, 0);
      const fs = size || Math.max(22, Math.round(r * 1.2));
      this.name = box(this.g, 0, 0, Object.assign(SERIF(fs), { width: 2 * R0 + 'px', height: 2 * R0 + 'px', lineHeight: 2 * R0 + 'px', textAlign: 'center', whiteSpace: 'pre', fontStyle: italic ? 'italic' : 'normal' }), text);
      tl.set(this.g, { o: 0 }, 0);
      this.shown = false;
    }
    circle() { return { x: this.x, y: this.y, r: this.r }; }
    show(at, { draw = false, dur = 0.5, dy = 10 } = {}) {
      const tl = this.tl;
      if (draw) {
        tl.set(this.g, { o: 1 }, at);
        for (const p of [this.circ, this.inner]) if (p) tl.to(p, { draw: 1 }, at, dur, E.io);
        tl.set(this.name, { o: 0 }, 0); tl.to(this.name, { o: 1 }, at + dur * 0.5, 0.4);
      } else {
        for (const p of [this.circ, this.inner]) if (p) tl.set(p, { draw: 1 }, at);
        tl.set(this.g, { y: dy }, 0); tl.to(this.g, { o: 1, y: 0 }, at, dur, E.out5);
      }
      this.shown = true;
      return this;
    }
    hide(at, dur = 0.35) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    dim(o, at, dur = 0.4) { this.tl.to(this.g, { o }, at, dur); return this; }
    move(dx, dy, at, dur = 0.8) { this.tl.to(this.g, { x: dx, y: dy }, at, dur, E.io); return this; }
    pulse(at, { dur = 0.6, scale = 1.1 } = {}) {
      this.tl.to(this.g, { s: scale }, at, dur * 0.4, E.out); this.tl.to(this.g, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io);
      this.tl.to(this.halo, { o: 1 }, at, dur * 0.4); this.tl.to(this.halo, { o: 0 }, at + dur * 0.5, dur * 0.5);
      return this;
    }
    mark(at, { color = C.dim, fill = 0.1, out = null, dur = 0.4 } = {}) {
      const r = this.r + 14, m = box(this.g, this.R0 - r, this.R0 - r, { width: 2 * r + 'px', height: 2 * r + 'px', borderRadius: '50%', background: alpha(color, fill), boxShadow: `inset 0 0 0 2px ${alpha(color, 0.55)}` });
      this.g.insertBefore(m, this.g.firstChild);
      this.tl.set(m, { o: 0, s: 0.85 }, 0); this.tl.to(m, { o: 1, s: 1 }, at, dur, E.out5);
      if (out != null) this.tl.to(m, { o: 0 }, out, 0.35);
      return m;
    }
    dirty(at, dur = 0.35) { this.tl.to(this.ring, { o: 1 }, at, dur); return this; }
    clean(at, dur = 0.35) { this.tl.to(this.ring, { o: 0 }, at, dur); return this; }
    color(col, at, dur = 0.35) { for (const p of [this.circ, this.inner]) if (p) this.tl.to(p, { stroke: col }, at, dur); return this; }
    recolor(at, dur = 0.35) { return this.color(C.ink, at, dur); }
    flip(text, at) { flip(this.tl, this.name, text, at); return this; }
  }

  // ---- block outlines ----------------------------------------------------------------------------------------------
  // the convex hull of points (x, y), counter-clockwise on the stage (y down: clockwise as seen)
  function hull(pts) {
    const p = pts.slice().sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    if (p.length < 3) return p;
    const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    const lo = [], up = [];
    for (const q of p) { while (lo.length >= 2 && cr(lo[lo.length - 2], lo[lo.length - 1], q) <= 0) lo.pop(); lo.push(q); }
    for (let i = p.length - 1; i >= 0; i--) { const q = p[i]; while (up.length >= 2 && cr(up[up.length - 2], up[up.length - 1], q) <= 0) up.pop(); up.push(q); }
    up.pop(); lo.pop();
    return lo.concat(up);
  }
  function itemPoints(it) {
    if (it.w != null) return [[it.x, it.y], [it.x + it.w, it.y], [it.x + it.w, it.y + it.h], [it.x, it.y + it.h]];
    const n = 48, out = [];
    for (let i = 0; i < n; i++) { const a = i / n * 2 * Math.PI; out.push([it.x + it.r * Math.cos(a), it.y + it.r * Math.sin(a)]); }
    return out;
  }
  // the outline: the hull of the items, pad further out, as a closed polygon of many points
  function outlinePts(items, pad) {
    const h = hull(items.flatMap(itemPoints));
    if (h.length === 1) { const out = []; for (let i = 0; i < 64; i++) { const a = i / 64 * 2 * Math.PI; out.push([h[0][0] + pad * Math.cos(a), h[0][1] + pad * Math.sin(a)]); } return out; }
    const n = h.length, out = [];
    const nrm = (a, b) => { const dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy) || 1; return [dy / L, -dx / L]; };
    for (let i = 0; i < n; i++) {
      const prev = h[(i - 1 + n) % n], v = h[i], next = h[(i + 1) % n];
      const n0 = nrm(prev, v), n1 = nrm(v, next);
      let a0 = Math.atan2(n0[1], n0[0]), a1 = Math.atan2(n1[1], n1[0]);
      // the hull from the monotone chain is counter-clockwise in its own axes: the outward normal of an edge is
      // (dy, -dx), and from one edge's normal to the next the angle grows
      while (a1 < a0 - 1e-9) a1 += 2 * Math.PI;
      const steps = Math.max(1, Math.ceil((a1 - a0) / 0.12));
      for (let s = 0; s <= steps; s++) { const a = a0 + (a1 - a0) * s / steps; out.push([v[0] + pad * Math.cos(a), v[1] + pad * Math.sin(a)]); }
    }
    return out;
  }
  // a closed polygon with points at most 6 px apart
  function densify(pts) {
    const out = [];
    pts.forEach((p, i) => { const q = pts[(i + 1) % pts.length], n = Math.ceil(Math.hypot(q[0] - p[0], q[1] - p[1]) / 6); for (let j = 0; j < n; j++) out.push([p[0] + (q[0] - p[0]) * j / n, p[1] + (q[1] - p[1]) * j / n]); });
    return out;
  }
  function insidePoly([x, y], P) {
    let c = false;
    for (let i = 0, j = P.length - 1; i < P.length; j = i++) { const [xi, yi] = P[i], [xj, yj] = P[j]; if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c; }
    return c;
  }
  // the outline of the union of two overlapping outlines (both turning the same way): walk one until it enters the
  // other, then go on along the other
  function unionPts(A0, B0) {
    const A = densify(A0), B = densify(B0);
    const i0 = A.findIndex(p => !insidePoly(p, B));
    if (i0 < 0) return B0;
    const out = [];
    let cur = A, oth = B, i = i0;
    for (let guard = 0; guard < 20000; guard++) {
      out.push(cur[i]);
      const nx = (i + 1) % cur.length;
      if (insidePoly(cur[nx], oth)) {
        const q = cur[nx];
        let j = 0, bd = Infinity;
        oth.forEach((p, k) => { const d = (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2; if (d < bd) { bd = d; j = k; } });
        let n = 0;
        while (insidePoly(oth[j], cur) && n++ < oth.length) j = (j + 1) % oth.length;
        [cur, oth, i] = [oth, cur, j];
      } else i = nx;
      if (cur === A && i === i0) break;
    }
    return out;
  }
  const DIRS = { n: [0, -1], ne: [0.71, -0.71], e: [1, 0], se: [0.71, 0.71], s: [0, 1], sw: [-0.71, 0.71], w: [-1, 0], nw: [-0.71, -0.71] };
  function tabEl(parent, cx, cy, name, { size = 32 } = {}) {
    const h = Math.round(size * 1.3), w = Math.max(h, Math.round([...String(name)].length * charWidth(size) + size * 0.7));
    const t = box(parent, cx - w / 2, cy - h / 2, Object.assign(MONO(size), { width: w + 'px', height: h + 'px', lineHeight: (h - 5) + 'px', textAlign: 'center', borderRadius: Math.round(size * 0.28) + 'px', background: C.bg, border: `2.5px solid ${C.bind}`, color: C.bind, fontWeight: 560, whiteSpace: 'pre', transformOrigin: 'center center' }), name);
    t._cx = cx; t._cy = cy;
    return t;
  }
  function freeTab(parent, cx, cy, name, opts = {}) { const t = tabEl(parent, cx, cy, name, opts); return t; }

  class Block {
    constructor(tl, parent, items, name, opts = {}) {
      const { at, out, pad = 20, tab = 'nw', tabDx = 0, tabDy = 0, tabSize = 32, dur = 0.6, width = 2.5, resolve, extra, always, groups, layer, tabLayer, reuseTab } = opts;
      Object.assign(this, { tl, parent, name, pad, tabSize, width, opts, resolve, extra, always });
      this.items = items;
      // the outline of some items: `always` gives more round items it goes around (a machine's loops and bent edges
      // inside the block); a label that it would cross is taken inside it (as a round item)
      const build = its => {
        const circles = its.map(it => resolve && (typeof it !== 'object') ? resolve(it) : it).concat(always ? always(its) : []);
        let pts = outlinePts(circles, pad);
        if (extra) {
          const dense = densify(pts);
          const hit = extra(its).filter(q => dense.some(([px, py]) => px > q.x && px < q.x + q.w && py > q.y && py < q.y + q.h));
          if (hit.length) pts = outlinePts(circles.concat(hit.map(q => ({ x: q.x + q.w / 2, y: q.y + q.h / 2, r: Math.max(q.w, q.h) / 2 }))), pad);
        }
        return pts;
      };
      // groups (lists of items): the outline is the union of the groups' outlines, so that it can bend around
      // something that is not in the block
      this.pts = groups ? groups.map(build).reduce(unionPts) : build(items);
      const d = 'M ' + this.pts.map(p => p[0].toFixed(1) + ' ' + p[1].toFixed(1)).join(' L ') + ' Z';
      this.layer = layer || svgLayer(parent);
      this.tabLayer = tabLayer || parent;
      this.path = path(tl, this.layer, d, { stroke: C.bind, width });
      this.sw = width;
      tl.custom(this.path, 'sw', (e, v) => e.setAttribute('stroke-width', v), width);
      // where the tab goes
      let tp;
      if (tab && typeof tab === 'object') tp = [tab.x, tab.y];
      else {
        const [dx, dy] = DIRS[tab] || DIRS.nw;
        let best = null, bv = -Infinity;
        for (const p of this.pts) { const v = p[0] * dx + p[1] * dy; if (v > bv) { bv = v; best = p; } }
        // among the points nearly as far out, the middle one
        const near = this.pts.filter(p => p[0] * dx + p[1] * dy > bv - 2);
        best = near[Math.floor(near.length / 2)] || best;
        tp = best;
      }
      this.tp = [tp[0] + tabDx, tp[1] + tabDy];
      this.tabEl = null;
      if (reuseTab) { this.tabEl = reuseTab; }
      else if (name) { this.tabEl = tabEl(this.tabLayer, this.tp[0], this.tp[1], name, { size: tabSize }); tl.set(this.tabEl, { o: 0 }, 0); }
      tl.set(this.path, { o: 1 }, 0);
      if (at != null) this.show(at, { dur });
      if (out != null) this.hide(out);
    }
    show(at, { dur = 0.6 } = {}) {
      this.tl.to(this.path, { draw: 1 }, at, dur, E.io);
      if (this.tabEl) { this.tl.set(this.tabEl, { s: 0.6 }, 0); this.tl.to(this.tabEl, { o: 1, s: 1 }, at + dur * 0.6, 0.4, E.out5); }
      return this;
    }
    hide(at, dur = 0.35) { this.tl.to(this.path, { o: 0 }, at, dur, E.in); if (this.tabEl) this.tl.to(this.tabEl, { o: 0 }, at, dur, E.in); return this; }
    dim(o, at, dur = 0.4) { this.tl.to(this.path, { o }, at, dur); if (this.tabEl) this.tl.to(this.tabEl, { o }, at, dur); return this; }
    pulse(at, { dur = 0.6 } = {}) {
      this.tl.to(this.path, { sw: this.sw * 2.2 }, at, dur * 0.4, E.out); this.tl.to(this.path, { sw: this.sw }, at + dur * 0.4, dur * 0.6, E.io);
      if (this.tabEl) { this.tl.to(this.tabEl, { s: 1.15 }, at, dur * 0.4, E.out); this.tl.to(this.tabEl, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      return this;
    }
    rename(name, at) {
      if (!this.tabEl) { this.tabEl = tabEl(this.tabLayer, this.tp[0], this.tp[1], name, { size: this.tabSize }); this.tl.set(this.tabEl, { o: 0, s: 0.6 }, 0); this.tl.to(this.tabEl, { o: 1, s: 1 }, at, 0.4, E.out5); }
      else flip(this.tl, this.tabEl, name, at);
      this.name = name;
      return this;
    }
    tabPos() { return { x: this.tp[0], y: this.tp[1] }; }
    rect() {
      const xs = this.pts.map(p => p[0]), ys = this.pts.map(p => p[1]);
      const x0 = Math.min(...xs), y0 = Math.min(...ys), x1 = Math.max(...xs), y1 = Math.max(...ys);
      return { x: x0, y: y0, w: x1 - x0, h: y1 - y0, cx: (x0 + x1) / 2, cy: (y0 + y1) / 2 };
    }
    split(at, parts, { dur = 0.6 } = {}) {
      const tl = this.tl;
      tl.to(this.path, { o: 0 }, at, 0.4);
      let kept = false;
      const out = parts.map(([items, name, o = {}]) => {
        const keep = !kept && name && name === this.name && this.tabEl;
        if (keep) kept = true;
        const b = new Block(tl, this.parent, items, name, Object.assign({ pad: this.pad, tabSize: this.tabSize, width: this.width, resolve: this.resolve, extra: this.extra, always: this.always, layer: this.layer, tabLayer: this.tabLayer }, o, { at: undefined, out: undefined, reuseTab: keep ? this.tabEl : null }));
        tl.to(b.path, { draw: 1 }, at + 0.15, dur, E.io);
        if (keep) {
          // the tab glides from where it was to its place on the new outline
          const ox = this.tabEl._ox || 0, oy = this.tabEl._oy || 0;
          const nx = b.tp[0] - this.tabEl._cx, ny = b.tp[1] - this.tabEl._cy;
          if (Math.abs(nx - ox) + Math.abs(ny - oy) > 0.5) tl.to(this.tabEl, { x: nx, y: ny }, at, 0.75, E.io);
          this.tabEl._ox = nx; this.tabEl._oy = ny;
        } else if (b.tabEl) { tl.set(b.tabEl, { s: 0.6 }, 0); tl.to(b.tabEl, { o: 1, s: 1 }, at + 0.5, 0.4, E.out5); }
        return b;
      });
      if (!kept && this.tabEl) tl.to(this.tabEl, { o: 0 }, at, 0.35);
      return out;
    }
  }

  // ---- the machines --------------------------------------------------------------------------------------------------
  const POS = { 1: [0, -190], 2: [-170, -20], 3: [170, -20], 4: [-170, 160], 5: [170, 160] };
  // [id, from, to, label, {bend, side, dx, dy}]; a loop: from === to, {dir: 'left' | 'right'}
  const EDGES = {
    dfa: [
      ['1>2', 1, 2, 'a'], ['1>3', 1, 3, 'b'], ['2>3', 2, 3, 'b'], ['3>3', 3, 3, 'b', { dir: 'right' }],
      ['2>4', 2, 4, 'a'], ['3>5', 3, 5, 'a', { side: -1 }],
      ['5>4', 5, 4, 'a, b'], ['4>5', 4, 5, 'a', { bend: 100 }],
      ['4>4', 4, 4, 'b', { dir: 'left' }],
    ],
    ts: [
      ['1>2', 1, 2, null, { bend: -14 }], ['1>3', 1, 3, null], ['1>4', 1, 4, null, { bend: -22 }],
      ['2>1', 2, 1, null, { bend: -52 }], ['2>4', 2, 4, null],
      ['3>3', 3, 3, null, { dir: 'right' }], ['3>4', 3, 4, null], ['3>5', 3, 5, null],
      ['4>4', 4, 4, null, { dir: 'left' }], ['4>5', 4, 5, null],
    ],
    mc: [
      ['1>2', 1, 2, '⅓'], ['1>3', 1, 3, '⅔'],
      ['2>2', 2, 2, '½', { dir: 'left' }], ['2>4', 2, 4, '½'],
      ['3>2', 3, 2, '¼'], ['3>4', 3, 4, '½', { t: 0.5 }], ['3>5', 3, 5, '¼', { bend: 34 }],
      ['4>4', 4, 4, '1', { dir: 'left' }],
      ['5>3', 5, 3, '½', { bend: 34 }], ['5>4', 5, 4, '½', { side: -1 }],
    ],
    dfa3: [
      ['1>2', 1, 2, 'a, b'], ['2>2', 2, 2, 'b', { dir: 'left' }], ['2>4', 2, 4, 'a'], ['4>4', 4, 4, 'a, b', { dir: 'left' }],
    ],
  };
  const STATES = { dfa: [1, 2, 3, 4, 5], ts: [1, 2, 3, 4, 5], mc: [1, 2, 3, 4, 5], dfa3: [1, 2, 4] };
  const ACCEPT = { dfa: [4, 5], ts: [], mc: [4], dfa3: [4] };
  // where the tab of each block of the storyboard goes (kind, states) -> side
  const TABS = {
    'dfa:2,3': 'w', 'dfa:4,5': 's', 'dfa:1': 'w', 'dfa:1,2,3': 'nw', 'dfa:1,2,3,4,5': 'nw',
    'ts:1,2': 'w', 'ts:3,4': 's', 'ts:5': 'e',
    'mc:2,3,5': 'ne', 'mc:4': 's', 'mc:1': 'nw',
  };

  class Machine {
    constructor(tl, parent, { kind = 'dfa', cx = CX, cy = 500, scale = 1 } = {}) {
      const k = scale;
      Object.assign(this, { tl, kind, cx, cy, k });
      if (!EDGES[kind]) console.warn('BX.Machine: no kind', kind);
      this.r = 36 * k;
      this.nameSize = Math.max(24, Math.round(30 * k));
      this.size = Math.max(24, Math.round(28 * k));
      this.head = Math.round(14 * Math.min(1.15, Math.max(0.85, k)));
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${cx}px ${cy}px` });
      this.blockSvg = svgLayer(this.g);
      this.halo = svgLayer(this.g);
      this.svg = svgLayer(this.g);
      this.stLayer = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.lay = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.tabLayer = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.states = new Map(); this.edgeMap = new Map(); this.edges = [];
      this.boxes = [];
      for (const s of STATES[kind]) {
        const [px, py] = POS[s], x = cx + px * k, y = cy + py * k;
        const c = new Chip(tl, this.stLayer, x, y, String(s), { r: this.r, size: this.nameSize, accepting: ACCEPT[kind].includes(s) });
        this.states.set(s, c);
        this.boxes.push({ x0: x - this.r - 13, y0: y - this.r - 13, x1: x + this.r + 13, y1: y + this.r + 13 });
      }
      for (const [id, from, to, label, o] of EDGES[kind]) this._edge(id, from, to, label, o || {});
    }
    pos(s) { const c = this.states.get(+s); return { x: c.x, y: c.y }; }
    circle(s) { const c = this.states.get(+s); if (!c) console.warn('BX.Machine: no state', s); return { x: c.x, y: c.y, r: this.r }; }
    state(s) { return this.states.get(+s); }
    edge(from, to, label) {
      const r = this.edges.find(e => e.from === +from && e.to === +to && (label == null || e.label === label));
      if (!r) console.warn('BX.Machine: no edge', from, to, label || '');
      return r;
    }
    _labelEl(text, x, y) {
      const size = this._lsize(text), h = Math.round(size * 1.3), w = [...text].length * charWidth(size);
      const e = box(this.lay, x - w / 2 - 20, y - h / 2, Object.assign(MONO(size), { width: (w + 40) + 'px', height: h + 'px', lineHeight: h + 'px', textAlign: 'center', whiteSpace: 'pre', color: C.ink, transformOrigin: 'center center' }), text);
      this.tl.set(e, { o: 0 }, 0);
      this.boxes.push({ x0: x - w / 2, y0: y - h / 2, x1: x + w / 2, y1: y + h / 2 });
      return e;
    }
    _edge(id, from, to, label, o) {
      const tl = this.tl, r = this.r, gap = 6;
      const A = this.pos(from), B = this.pos(to);
      const rec = { type: 'edge', id, from, to, label, o };
      rec.g = el(this.svg, 'g'); tl.set(rec.g, { o: 0 }, 0);
      let d, hx, hy, ang, lx, ly;
      const ls = label ? this._lsize(label) : this.size;
      const lw = label ? [...label].length * charWidth(ls) : 0, lh = Math.round(ls * 1.3) * 0.78;
      const beside = (mx, my, nx, ny, g = 8) => { const dd = Math.abs(nx) * lw / 2 + Math.abs(ny) * lh / 2 + g; return [mx + nx * dd, my + ny * dd]; };
      if (from === to) {
        // a loop on the outer side of the state, like the paper's: a round hook
        const rot = { up: 0, right: Math.PI / 2, down: Math.PI, left: -Math.PI / 2 }[o.dir || 'up'];
        const a0 = -2.05 + rot, a1 = -1.09 + rot, P = (a, rr) => [A.x + rr * Math.cos(a), A.y + rr * Math.sin(a)];
        const [x0, y0] = P(a0, r + 4), [x1, y1] = P(a1, r + 4), [c0x, c0y] = P(a0 - 0.25, r * 3.2), [c1x, c1y] = P(a1 + 0.25, r * 3.2);
        d = `M ${x0} ${y0} C ${c0x} ${c0y} ${c1x} ${c1y} ${x1} ${y1}`;
        hx = x1; hy = y1; ang = Math.atan2(y1 - c1y, x1 - c1x);
        const ux = Math.cos(rot - Math.PI / 2), uy = Math.sin(rot - Math.PI / 2), apex = r * 2.6;
        [lx, ly] = beside(A.x + ux * apex, A.y + uy * apex, ux, uy, 6);
        rec.mid = [A.x + ux * apex, A.y + uy * apex];
        this.boxes.push({ x0: A.x + ux * apex - r, y0: A.y + uy * apex - r, x1: A.x + ux * apex + r, y1: A.y + uy * apex + r });
      } else {
        const bend = (o.bend || 0) * this.k;
        const ux = B.x - A.x, uy = B.y - A.y, L = Math.hypot(ux, uy);
        const mx = (A.x + B.x) / 2, my = (A.y + B.y) / 2;
        const qx = mx - uy / L * bend, qy = my + ux / L * bend;
        const dir = (px, py, tx, ty) => { const l = Math.hypot(tx - px, ty - py) || 1; return [(tx - px) / l, (ty - py) / l]; };
        const [ax, ay] = dir(A.x, A.y, qx, qy), [bx, by] = dir(B.x, B.y, qx, qy);
        const s = [A.x + ax * (r + gap), A.y + ay * (r + gap)], e = [B.x + bx * (r + gap), B.y + by * (r + gap)];
        d = `M ${s[0]} ${s[1]} Q ${qx} ${qy} ${e[0]} ${e[1]}`;
        hx = e[0]; hy = e[1]; ang = Math.atan2(e[1] - qy, e[0] - qx);
        const t = o.t ?? 0.5, it = 1 - t;
        const cmx = it * it * s[0] + 2 * it * t * qx + t * t * e[0], cmy = it * it * s[1] + 2 * it * t * qy + t * t * e[1];
        let nx = uy / L, ny = -ux / L;
        if (bend) { const b = Math.sign(bend); nx = -uy / L * b; ny = ux / L * b; }
        else if (ny > 1e-6 || (Math.abs(ny) <= 1e-6 && nx > 0)) { nx = -nx; ny = -ny; }
        if (o.side === -1) { nx = -nx; ny = -ny; }
        [lx, ly] = beside(cmx, cmy, nx, ny);
        rec.mid = [cmx, cmy];
        this.boxes.push({ x0: Math.min(s[0], e[0], cmx), y0: Math.min(s[1], e[1], cmy), x1: Math.max(s[0], e[0], cmx), y1: Math.max(s[1], e[1], cmy) });
      }
      rec.d = d;
      rec.path = path(tl, rec.g, d, { stroke: C.ink, width: LINE });
      tl.custom(rec.path, 'sw', (e, v) => e.setAttribute('stroke-width', v), LINE);
      rec.head = headEl(rec.g, hx, hy, ang, { head: this.head }); tl.set(rec.head, { o: 0 }, 0);
      if (label) { rec.lx = lx + (o.dx || 0) * this.k; rec.ly = ly + (o.dy || 0) * this.k; rec.lw = lw; rec.lh = lh; rec.lab = this._labelEl(label, rec.lx, rec.ly); }
      this.edgeMap.set(id, rec); this.edges.push(rec);
      return rec;
    }
    // a fraction is a small glyph in Fira Code: its label is set larger
    _lsize(text) { return /^[½⅓⅔¼¾]$/u.test(text) ? Math.round(this.size * 1.3) : this.size; }
    labelPos(id) { const r = this.edgeMap.get(id); return r && r.lab ? { x: r.lx, y: r.ly } : null; }
    // the records a selector names
    _sel(sel) {
      const out = [], add = r => { if (r && !out.includes(r)) out.push(r); };
      const stateRec = s => { const c = this.states.get(+s); if (!c) { console.warn('BX.Machine: no state', s); return null; } return { type: 'state', k: +s, chip: c }; };
      const one = q => {
        if (q === 'all') { this._sel('states').forEach(add); this.edges.forEach(add); return; }
        if (q === 'states') { for (const s of this.states.keys()) add(this._stRec(s)); return; }
        if (q === 'edges') { this.edges.forEach(add); return; }
        if (typeof q === 'number' || /^\d+$/.test(q)) { const r = stateRec(q); if (r) add(this._stRec(+q)); return; }
        if (typeof q === 'function') { for (const s of this.states.keys()) { const r = this._stRec(s); if (q(r)) add(r); } this.edges.filter(q).forEach(add); return; }
        if (Array.isArray(q)) { q.forEach(one); return; }
        let m;
        if ((m = /^out:(\d+)$/.exec(q))) { this.edges.filter(e => e.from === +m[1]).forEach(add); return; }
        if ((m = /^in:(\d+)$/.exec(q))) { this.edges.filter(e => e.to === +m[1]).forEach(add); return; }
        if ((m = /^(\d+)>(\d+)(?::(.+))?$/.exec(q))) {
          const es = this.edges.filter(e => e.from === +m[1] && e.to === +m[2] && (m[3] == null || e.label === m[3]));
          if (!es.length) console.warn('BX.Machine: no edge', q); es.forEach(add); return;
        }
        console.warn('BX.Machine: bad selector', q);
      };
      one(sel);
      return out;
    }
    _stRec(s) { this._srec = this._srec || new Map(); if (!this._srec.has(s)) this._srec.set(s, { type: 'state', k: s, chip: this.states.get(s) }); return this._srec.get(s); }
    show(at, { sel = 'all', stagger = 0.12, dur = 0.5 } = {}) {
      const recs = this._sel(sel), tl = this.tl;
      let t = at;
      for (const r of recs.filter(r => r.type === 'state')) { r.chip.show(t, { draw: true, dur }); t += stagger; }
      for (const r of recs.filter(r => r.type === 'edge')) {
        tl.set(r.g, { o: 1 }, t); tl.to(r.path, { draw: 1 }, t, dur, E.io); tl.fromTo(r.head, { o: 0 }, { o: 1 }, t + dur * 0.75, dur * 0.25);
        if (r.lab) fadeIn(tl, r.lab, t + dur * 0.55, 0.45, 8);
        t += stagger;
      }
      return t - stagger + dur + 0.2;
    }
    appear(at, { sel = 'all', dur = 0.5 } = {}) {
      const tl = this.tl;
      for (const r of this._sel(sel)) {
        if (r.type === 'state') r.chip.show(at, { dur, dy: 0 });
        else { tl.set(r.path, { draw: 1 }, at); tl.set(r.head, { o: 1 }, at); tl.to(r.g, { o: 1 }, at, dur); if (r.lab) tl.to(r.lab, { o: 1 }, at, dur); }
      }
      return this;
    }
    _els(r) { return r.type === 'state' ? [r.chip.g] : [r.g, ...(r.lab ? [r.lab] : []), ...(r.marks || [])]; }
    dim(sel, o, at, dur = 0.4) { for (const r of this._sel(sel)) for (const e of this._els(r)) this.tl.to(e, { o }, at, dur); return this; }
    light(sel, at, dur = 0.4) { return this.dim(sel, 1, at, dur); }
    focus(sel, at, { o = 0.3, dur = 0.4 } = {}) {
      const on = this._sel(sel);
      for (const r of this._sel('all')) for (const e of this._els(r)) this.tl.to(e, { o: on.includes(r) ? 1 : o }, at, dur);
      return this;
    }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    pulse(sel, at, { dur = 0.6 } = {}) {
      const tl = this.tl;
      for (const r of this._sel(sel)) {
        if (r.type === 'state') { r.chip.pulse(at, { dur }); continue; }
        tl.to(r.path, { sw: LINE * 2 }, at, dur * 0.4, E.out); tl.to(r.path, { sw: LINE }, at + dur * 0.4, dur * 0.6, E.io);
        if (r.lab) { tl.to(r.lab, { s: 1.25 }, at, dur * 0.4, E.out); tl.to(r.lab, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      }
      return this;
    }
    mark(sel, at, { color = C.dim, fill = 0.1, out = null, dur = 0.4 } = {}) {
      const tl = this.tl, els = [];
      for (const r of this._sel(sel)) {
        if (r.type === 'state') { els.push(r.chip.mark(at, { color, fill, out, dur })); continue; }
        const p = el(this.halo, 'path');
        p.setAttribute('d', r.d); p.setAttribute('fill', 'none'); p.setAttribute('stroke-width', 18); p.setAttribute('stroke-linecap', 'round');
        p.style.stroke = alpha(color, Math.min(0.35, fill * 2.2));
        tl.set(p, { o: 0 }, 0); tl.to(p, { o: 1 }, at, dur);
        if (out != null) tl.to(p, { o: 0 }, out, 0.35);
        (r.marks = r.marks || []).push(p); els.push(p);
      }
      return els;
    }
    color(sel, col, at, dur = 0.35) {
      for (const r of this._sel(sel)) {
        if (r.type === 'state') r.chip.color(col, at, dur);
        else { this.tl.to(r.path, { stroke: col }, at, dur); this.tl.to(r.head, { stroke: col }, at, dur); }
      }
      return this;
    }
    recolor(sel, at, dur = 0.35) { return this.color(sel, C.ink, at, dur); }
    dirty(ks, at) { for (const s of [].concat(ks)) this.states.get(+s).dirty(at); return this; }
    clean(ks, at) { for (const s of [].concat(ks)) this.states.get(+s).clean(at); return this; }
    slide(s, target, at, dur = 0.8) {
      const c = this.states.get(+s), p = typeof target === 'object' ? target : this.pos(target);
      c.move(p.x - c.x, p.y - c.y, at, dur);
      return this;
    }
    travel(id, at, dur = 0.8, { color = C.ink, r = 9, out = null } = {}) {
      const rec = this.edgeMap.get(id); if (!rec) { console.warn('BX.Machine: no edge', id); return null; }
      const p = rec.path, len = p._len;
      const d = el(this.svg, 'circle'); d.setAttribute('r', r); d.style.fill = color;
      const place = v => { const q = p.getPointAtLength(len * v); d.setAttribute('cx', q.x); d.setAttribute('cy', q.y); };
      place(0);
      this.tl.custom(d, 'u', (e, v) => place(v), 0);
      this.tl.set(d, { o: 0 }, 0); this.tl.to(d, { o: 1 }, at, 0.2); this.tl.to(d, { u: 1 }, at, dur, E.io);
      if (out != null) this.tl.to(d, { o: 0 }, out, 0.3);
      return d;
    }
    bounds() {
      const b = this.boxes, x0 = Math.min(...b.map(q => q.x0)), y0 = Math.min(...b.map(q => q.y0)), x1 = Math.max(...b.map(q => q.x1)), y1 = Math.max(...b.map(q => q.y1));
      return { x0, y0, x1, y1, cx: (x0 + x1) / 2, cy: (y0 + y1) / 2 };
    }
    // the labels of the edges between states of a block lie inside its outline
    _inner(ss) {
      const set = new Set(ss.map(Number));
      return this.edges.filter(e => e.lab && e.from !== e.to && set.has(e.from) && set.has(e.to)).map(e => ({ x: e.lx - e.lw / 2 - 4, y: e.ly - e.lh / 2 - 4, w: e.lw + 8, h: e.lh + 8 }));
    }
    // the self-loops of the states of a block (with their labels), and the bent edges between two of them, as round
    // items: an outline goes around them instead of through them
    _loops(ss) {
      const set = new Set(ss.map(Number)), r = this.r, out = [];
      for (const e of this.edges) {
        if (!set.has(e.from) || !set.has(e.to)) continue;
        if (e.from === e.to) {
          const rot = { up: 0, right: Math.PI / 2, down: Math.PI, left: -Math.PI / 2 }[e.o.dir || 'up'], A = this.pos(e.from);
          out.push({ x: A.x + Math.cos(rot - Math.PI / 2) * 1.6 * r, y: A.y + Math.sin(rot - Math.PI / 2) * 1.6 * r, r: 0.85 * r });
          if (e.lab) out.push({ x: e.lx, y: e.ly, r: Math.max(e.lw, e.lh) / 2 + 4 });   // its label too
        } else if (e.o.bend) out.push({ x: e.mid[0], y: e.mid[1], r: 4 });
      }
      return out;
    }
    block(states, name, at, opts = {}) {
      const key = this.kind + ':' + [...states].sort().join(',');
      return new Block(this.tl, this.g, states, name, Object.assign({
        pad: 20 * this.k, tabSize: Math.max(26, Math.round(30 * this.k)), tab: TABS[key] || 'nw',
        resolve: s => this.circle(s), extra: ss => this._inner(ss), always: ss => this._loops(ss), layer: this.blockSvg, tabLayer: this.tabLayer, at,
      }, opts));
    }
  }
  // a split of a machine's block picks each part's tab side from the table too
  const _split = Block.prototype.split;
  Block.prototype.split = function (at, parts, opts) {
    if (this.resolve && this.machineKind) parts = parts.map(([items, name, o = {}]) => [items, name, Object.assign({ tab: TABS[this.machineKind + ':' + [...items].sort().join(',')] || 'nw' }, o)]);
    const out = _split.call(this, at, parts, opts);
    for (const b of out) b.machineKind = this.machineKind;
    return out;
  };
  const _block = Machine.prototype.block;
  Machine.prototype.block = function (states, name, at, opts) { const b = _block.call(this, states, name, at, opts); b.machineKind = this.kind; return b; };

  // ---- structures --------------------------------------------------------------------------------------------------
  function stokens(text) {
    const out = []; let col = 0, prev = null;
    const re = /(\s+)|(true|false)|([XYZ])(?![A-Za-z])|(\d+(?:\.\d+)?)|([A-Za-z_][\w']*)|(.)/gu;
    let m;
    while ((m = re.exec(text))) {
      const len = [...m[0]].length;
      if (m[1] !== undefined) { col += len; continue; }
      let kind;
      if (m[2]) kind = 'flag';
      else if (m[3]) kind = 'block';
      else if (m[4]) kind = prev === ':' ? 'w' : 'state';
      else if (m[5]) kind = 'word';
      else kind = prev === ':' && /[½⅓⅔¼¾⅕⅙⅛]/u.test(m[0]) ? 'w' : 'sym';
      out.push({ text: m[0], kind, col, len });
      prev = m[0]; col += len;
    }
    return { toks: out, cols: col };
  }
  const KCOL = k => (k === 'block' ? C.bind : C.code);

  class Struct {
    constructor(tl, parent, x, y, text, { size = 52, align = 'left', at, stagger = 0.03 } = {}) {
      Object.assign(this, { tl, size });
      this.cw = charWidth(size); this.lh = Math.round(size * 1.3);
      const { toks, cols } = stokens(text);
      this.cols = cols;
      this.x = align === 'center' ? x - cols * this.cw / 2 : x; this.y = y;
      this.root = box(parent, this.x, y - this.lh / 2, { width: Math.max(1, cols * this.cw) + 'px', height: this.lh + 'px', transformOrigin: align === 'center' ? 'center center' : 'left center' });
      this.marks = box(this.root, 0, 0);
      this.layer = box(this.root, 0, 0);
      this.parts = toks.map(t => this._make(t));
      if (at != null) this.show(at, { stagger });
    }
    get width() { return this.cols * this.cw; }
    _make(t, color) {
      // a fraction is a small glyph in Fira Code: it is set larger, its right edge on its column's (it always follows
      // a space, so that it grows to the left, and does not crowd the brace or comma after it)
      const frac = /^[½⅓⅔¼¾]$/u.test(t.text), fs = frac ? Math.round(this.size * 1.3) : this.size;
      const e = box(this.layer, t.col * this.cw - (frac ? (charWidth(fs) - this.cw) * 0.85 : 0), 0, Object.assign(MONO(fs), { lineHeight: this.lh + 'px', whiteSpace: 'pre', color: color || KCOL(t.kind), transformOrigin: 'center center' }), t.text);
      this.tl.set(e, { o: 0 }, 0);
      return { el: e, text: t.text, kind: t.kind, col: t.col, len: t.len, base: t.col };
    }
    ids(sel = 'all') {
      const n = this.parts.length, all = [...Array(n).keys()], P = this.parts;
      if (sel === 'all') return all;
      if (sel === 'states') return all.filter(i => P[i].kind === 'state');
      if (sel === 'blocks') return all.filter(i => P[i].kind === 'block');
      if (sel === 'weights') return all.filter(i => P[i].kind === 'w');
      if (typeof sel === 'number') return [sel];
      if (typeof sel === 'string') { const r = all.filter(i => P[i].text === sel); if (!r.length) console.warn('BX.Struct: no part', sel); return r; }
      if (sel instanceof RegExp) return all.filter(i => sel.test(P[i].text));
      if (typeof sel === 'function') return all.filter(i => sel(P[i], i));
      if (Array.isArray(sel)) return sel;
      if (sel && sel.from != null) return all.filter(i => i >= sel.from && i <= (sel.to ?? n - 1));
      return [];
    }
    els(sel) { return this.ids(sel).map(i => this.parts[i].el); }
    show(at, { sel = 'all', stagger = 0.03, rise = 12, dur = 0.5 } = {}) {
      this.ids(sel).forEach((i, k) => { const e = this.parts[i].el; this.tl.set(e, { y: rise }, 0); this.tl.to(e, { y: 0, o: 1 }, at + k * stagger, dur, E.out5); });
      return this;
    }
    hideParts(sel, at, dur = 0.35) { for (const e of this.els(sel)) this.tl.to(e, { o: 0 }, at, dur, E.in); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.root, { o: 0 }, at, dur, E.in); return this; }
    dim(sel, o, at, dur = 0.4) { for (const e of this.els(sel)) this.tl.to(e, { o }, at, dur); return this; }
    light(sel, at, dur = 0.4) { return this.dim(sel, 1, at, dur); }
    color(sel, col, at, dur = 0.35) { for (const e of this.els(sel)) this.tl.to(e, { color: col }, at, dur); return this; }
    recolor(sel, at, dur = 0.4) { for (const i of this.ids(sel)) this.tl.to(this.parts[i].el, { color: KCOL(this.parts[i].kind) }, at, dur); return this; }
    rect(sel = 'all', pad = 0) {
      const ps = this.ids(sel).map(i => this.parts[i]);
      if (!ps.length) return { x: this.x, y: this.y - this.lh / 2, w: 0, h: this.lh, cx: this.x, cy: this.y };
      const c0 = Math.min(...ps.map(p => p.col)), c1 = Math.max(...ps.map(p => p.col + p.len));
      const x = this.x + c0 * this.cw - pad, w = (c1 - c0) * this.cw + 2 * pad;
      return { x, y: this.y - this.lh / 2 - pad * 0.4, w, h: this.lh + pad * 0.8, cx: x + w / 2, cy: this.y };
    }
    colX(c) { return this.x + c * this.cw; }
    pulse(sel, at, { dur = 0.5, scale = 1.08 } = {}) {
      for (const e of this.els(sel)) { this.tl.to(e, { s: scale }, at, dur * 0.4, E.out); this.tl.to(e, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      this.mark(sel, C.dim, at, { fill: 0.1, out: at + dur, dur: dur * 0.4 });
      return this;
    }
    mark(sel, color, at, { dur = 0.4, pad = 6, out = null, fill = 0.12 } = {}) {
      const r = this.rect(sel, pad);
      const m = box(this.marks, r.x - this.x, this.lh * 0.1 - pad * 0.4, { width: r.w + 'px', height: (this.lh * 0.8 + pad * 0.8) + 'px', borderRadius: '10px', background: alpha(color, fill), boxShadow: `inset 0 0 0 1.5px ${alpha(color, 0.5)}`, transformOrigin: 'left center' });
      this.tl.set(m, { sx: 0.2, o: 0 }, 0); this.tl.to(m, { sx: 1, o: 1 }, at, dur, E.out5);
      if (out != null) this.tl.to(m, { o: 0 }, out, 0.35);
      return m;
    }
    underline(sel, color, at, { dur = 0.4, out = null, stagger = 0.04 } = {}) {
      return this.ids(sel).map((i, k) => {
        const p = this.parts[i];
        const u = box(this.marks, p.col * this.cw + 2, this.lh * 0.86, { width: (p.len * this.cw - 4) + 'px', height: '3px', borderRadius: '2px', background: color, transformOrigin: 'left center' });
        this.tl.set(u, { sx: 0, o: 0 }, 0); this.tl.set(u, { o: 1 }, at + k * stagger); this.tl.to(u, { sx: 1 }, at + k * stagger, dur, E.io);
        if (out != null) this.tl.to(u, { o: 0 }, out, 0.3);
        return u;
      });
    }
    strike(sel, at, { dur = 0.4, out = null, fade = true } = {}) {
      const r = this.rect(sel, 4), ids = this.ids(sel);
      const u = box(this.marks, r.x - this.x, this.lh * 0.5 - 1, { width: r.w + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
      this.tl.set(u, { sx: 0, o: 0 }, 0); this.tl.set(u, { o: 1 }, at); this.tl.to(u, { sx: 1 }, at, dur, E.io);
      if (fade) this.color(ids, C.faint, at, dur);
      if (out != null) this.tl.to(u, { o: 0 }, out, 0.3);
      const self = this;
      return { line: u, undo(t) { self.tl.to(u, { sx: 0 }, t, 0.4, E.io); if (fade) self.recolor(ids, t, 0.4); } };
    }
    // part i turns into `text` where it stands now
    flip(i, text, at, { dur = 0.45, color, kind } = {}) {
      const old = this.parts[i], tk = stokens(text).toks[0] || { text, kind: 'word', len: [...text].length };
      const n = this._make({ text, kind: kind || tk.kind, col: old.col, len: tk.len }, color);
      const tl = this.tl;
      tl.to(old.el, { sy: 0.05 }, at, dur * 0.4, E.in); tl.set(old.el, { o: 0 }, at + dur * 0.4);
      tl.set(n.el, { sy: 0.05 }, 0); tl.set(n.el, { o: 1 }, at + dur * 0.4); tl.to(n.el, { sy: 1 }, at + dur * 0.4, dur * 0.6, E.out);
      this.parts[i] = n;
      return n;
    }
    rename(map, at, { stagger = 0, dur = 0.45 } = {}) {
      const m = {};
      for (const [key, v] of Object.entries(map)) { if (Array.isArray(v)) v.forEach(s => { m[String(s)] = key; }); else m[key] = v; }
      let k = 0;
      this.parts.forEach((p, i) => { if (p.kind === 'state' && m[p.text] != null) this.flip(i, m[p.text], at + stagger * k++, { dur, kind: 'block' }); });
      return this;
    }
    _moveTo(p, col, at, dur) { this.tl.to(p.el, { x: (col - p.base) * this.cw }, at, dur, E.io); p.col = col; }
    morph(text, at, { dur = 0.6 } = {}) {
      const tl = this.tl, old = this.parts, { toks, cols } = stokens(text);
      const n = old.length, m = toks.length;
      // longest common subsequence on the texts
      const L = Array.from({ length: n + 1 }, () => new Array(m + 1).fill(0));
      for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) L[i][j] = old[i].text === toks[j].text ? L[i + 1][j + 1] + 1 : Math.max(L[i + 1][j], L[i][j + 1]);
      const pairs = []; let i = 0, j = 0;
      while (i < n && j < m) { if (old[i].text === toks[j].text) { pairs.push([i, j]); i++; j++; } else if (L[i + 1][j] >= L[i][j + 1]) i++; else j++; }
      const next = new Array(m).fill(null), used = new Set();
      for (const [a, b] of pairs) { this._moveTo(old[a], toks[b].col, at, dur); next[b] = old[a]; used.add(a); }
      // the gaps between matches: pair up left-overs of the same kind in place (a flip), the rest is handled below
      const bounds = [[-1, -1], ...pairs, [n, m]];
      const leftOld = [];
      for (let q = 0; q + 1 < bounds.length; q++) {
        const [a0, b0] = bounds[q], [a1, b1] = bounds[q + 1];
        const os = [], ns = [];
        for (let a = a0 + 1; a < a1; a++) os.push(a);
        for (let b = b0 + 1; b < b1; b++) ns.push(b);
        while (os.length && ns.length && old[os[0]].kind === toks[ns[0]].kind && old[os[0]].kind !== 'sym') {
          const a = os.shift(), b = ns.shift(), p = old[a];
          this._moveTo(p, toks[b].col, at, dur);
          const np = this._make(Object.assign({}, toks[b]));
          tl.set(np.el, { sy: 0.05 }, 0);
          // (late, so that a part sliding onto it has faded before its text changes: nothing overprints)
          tl.to(p.el, { sy: 0.05 }, at + dur * 0.5, dur * 0.25, E.in); tl.set(p.el, { o: 0 }, at + dur * 0.75);
          tl.set(np.el, { o: 1 }, at + dur * 0.75); tl.to(np.el, { sy: 1 }, at + dur * 0.75, dur * 0.25, E.out);
          next[b] = np; used.add(a);
        }
        leftOld.push(os);
      }
      // runs of left-over old parts: slide onto an equal block/state that stays, and fade; else fade in place
      for (const run of leftOld) {
        if (!run.length) continue;
        let delta = null;
        for (const a of run) {
          const p = old[a]; if (p.kind !== 'block' && p.kind !== 'state') continue;
          const tgt = toks.findIndex((t, b) => t.text === p.text && next[b]);
          if (tgt >= 0) { delta = toks[tgt].col - p.col; break; }
        }
        for (const a of run) {
          const p = old[a];
          // (it rises a little as it slides, so that it passes over the parts between and not through them)
          if (delta != null) { this._moveTo(p, p.col + delta, at, dur); tl.to(p.el, { y: -0.5 * this.lh }, at, dur * 0.35, E.out); tl.to(p.el, { o: 0 }, at + dur * 0.2, dur * 0.45, E.in); }
          else tl.to(p.el, { o: 0 }, at, dur * 0.4, E.in);
        }
      }
      // new parts fade in
      toks.forEach((t, b) => {
        if (next[b]) return;
        const np = this._make(t);
        tl.to(np.el, { o: 1 }, at + dur * 0.5, dur * 0.5, E.out);
        next[b] = np;
      });
      this.parts = next; this.cols = cols;
      this.root.style.width = Math.max(cols * this.cw, parseFloat(this.root.style.width)) + 'px';
      return this;
    }
    merge(text, at, opts) { return this.morph(text, at, opts); }
    set(text, at, { dur = 0.5 } = {}) {
      for (const p of this.parts) this.tl.to(p.el, { o: 0 }, at, dur * 0.45, E.in);
      const { toks, cols } = stokens(text);
      this.parts = toks.map(t => this._make(t));
      this.cols = cols;
      this.root.style.width = Math.max(cols * this.cw, parseFloat(this.root.style.width)) + 'px';
      this.parts.forEach((p, k) => { this.tl.set(p.el, { y: 10 }, 0); this.tl.to(p.el, { o: 1, y: 0 }, at + dur * 0.45 + k * 0.012, dur, E.out5); });
      return this;
    }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.root, props, at, dur, ease); return this; }
  }

  class Table {
    constructor(tl, parent, x, y, rows, { size = 52, pitch = 92, cy, chipR, gap, accepting = [] } = {}) {
      Object.assign(this, { tl, size, pitch, x });
      this.chipR = chipR || Math.round(size * 0.52);
      this.gap = gap ?? Math.round(size * 0.5);
      const list = rows.map(r => Array.isArray(r) ? { k: r[0], text: r[1] } : r);
      if (cy != null) y = cy - (list.length - 1) * pitch / 2;
      this.y = y;
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px' });
      this.svg = svgLayer(this.g);
      this.structX = x + 2 * this.chipR + this.gap;
      this.map = new Map();
      this.rows = list.map((r, i) => {
        const yy = y + i * pitch;
        const chip = new Chip(tl, this.g, x + this.chipR, yy, String(r.k), { r: this.chipR, size: Math.max(22, Math.round(size * 0.62)), accepting: accepting.includes(r.k), line: size >= 44 ? 3 : 2.5 });
        const s = new Struct(tl, this.g, this.structX, yy, r.text || '', { size });
        const row = { k: r.k, i, y: yy, chip, s };
        this.map.set(String(r.k), row);
        return row;
      });
    }
    _row(k) { const r = this.map.get(String(k)); if (!r) console.warn('BX.Table: no row', k); return r; }
    _rows(ks) { return ks === 'all' ? this.rows : [].concat(ks).map(k => this._row(k)).filter(Boolean); }
    chip(k) { return this._row(k).chip; }
    struct(k) { return this._row(k).s; }
    rowY(k) { return this._row(k).y; }
    rect(k, part = 'all') { return this._row(k).s.rect(part); }
    show(at, { stagger = 0.12 } = {}) { this.rows.forEach((r, i) => this.showRow(r.k, at + i * stagger)); return this; }
    showRow(k, at, { parts = 'all', chip = true } = {}) {
      const r = this._row(k);
      if (chip && !r.chip.shown) r.chip.show(at);
      r.s.show(at + (chip ? 0.1 : 0), { sel: parts });
      return this;
    }
    hideRow(k, at, dur = 0.35) { const r = this._row(k); r.chip.hide(at, dur); r.s.hide(at, dur); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    set(k, text, at, opts) { this._row(k).s.set(text, at, opts); return this; }
    rename(k, map, at, opts) { this._row(k).s.rename(map, at, opts); return this; }
    morph(k, text, at, opts) { this._row(k).s.morph(text, at, opts); return this; }
    merge(k, text, at, opts) { return this.morph(k, text, at, opts); }
    fade(ks, o = 0.3, at, dur = 0.4) { for (const r of this._rows(ks)) this.tl.to(r.s.root, { o }, at, dur); return this; }
    dim(ks, o, at, { part = 'both', dur = 0.4 } = {}) {
      for (const r of this._rows(ks)) {
        if (part !== 'struct') r.chip.dim(o, at, dur);
        if (part !== 'chip') this.tl.to(r.s.root, { o }, at, dur);
      }
      return this;
    }
    light(ks, at, { part = 'both', dur = 0.4 } = {}) { return this.dim(ks, 1, at, { part, dur }); }
    pulse(k, at, { part = 'all', dur } = {}) { const r = this._row(k); if (part === 'chip') r.chip.pulse(at, dur ? { dur } : {}); else r.s.pulse(part, at, dur ? { dur } : {}); return this; }
    mark(k, at, { part = 'all', color = C.dim, fill = 0.08, out = null } = {}) { return this._row(k).s.mark(part, color, at, { fill, out }); }
    underline(k, part, color, at, opts) { return this._row(k).s.underline(part, color, at, opts); }
    strike(k, at, opts) { return this._row(k).s.strike('all', at, opts); }
    dirty(ks, at) { for (const r of this._rows(ks)) r.chip.dirty(at); return this; }
    clean(ks, at) { for (const r of this._rows(ks)) r.chip.clean(at); return this; }
    equal(k1, k2, at, { x, tick: withTick = true } = {}) {
      const a = this._row(k1), b = this._row(k2), tl = this.tl;
      const bx = x ?? (this.structX + Math.max(a.s.width, b.s.width) + 30);
      const y1 = Math.min(a.y, b.y), y2 = Math.max(a.y, b.y), my = (y1 + y2) / 2, arm = 16;
      const p = path(tl, this.svg, `M ${bx} ${y1} L ${bx + arm} ${y1} L ${bx + arm} ${y2} L ${bx} ${y2}`, { stroke: C.good, width: LINE });
      tl.to(p, { draw: 1 }, at, 0.45, E.io);
      const sz = Math.max(36, Math.round(this.size * 0.85));
      const eq = box(this.g, bx + arm + 14, my - Math.round(sz * 1.3) / 2, Object.assign(MONO(sz), { color: C.good, lineHeight: Math.round(sz * 1.3) + 'px', whiteSpace: 'pre' }), '=');
      fadeIn(tl, eq, at + 0.25, 0.4, 0);
      const els = [p, eq];
      if (withTick) { const t = tickM(tl, this.svg, bx + arm + 14 + charWidth(sz) + 40, my, 40, at + 0.45, { width: 5 }); els.push(...t.els); }
      return { els, hide(t) { for (const e of els) tl.to(e, { o: 0 }, t, 0.3); } };
    }
  }

  // ---- counter -------------------------------------------------------------------------------------------------------
  class Counter {
    constructor(tl, parent, x, y, label, { value = 0, size = 48, labelSize = 32, align = 'left', gap = 22 } = {}) {
      Object.assign(this, { tl, value });
      const h = Math.round(size * 1.3);
      this.el = box(parent, align === 'right' ? x - 1400 : x, y - h / 2, { width: align === 'right' ? '1400px' : 'auto', height: h + 'px', display: 'flex', alignItems: 'center', justifyContent: align === 'right' ? 'flex-end' : 'flex-start', gap: gap + 'px', whiteSpace: 'pre' });
      this.labelEl = el(this.el, 'span', Object.assign(LABEL(labelSize), { position: 'relative' }), label);
      this.num = el(this.el, 'span', Object.assign(MONO(size), { position: 'relative', color: C.ink, lineHeight: h + 'px', display: 'inline-block', transformOrigin: 'center center' }), String(value));
      this.bottom = y + h / 2;
      tl.set(this.el, { o: 0 }, 0);
    }
    show(at) { fadeIn(this.tl, this.el, at, 0.5, 10); return this; }
    set(v, at, { step = 0 } = {}) {
      if (step > 0) { let t = at; for (let n = this.value + 1; n <= v; n++) { this._to(n, t); t += step; } }
      else this._to(v, at);
      this.value = v;
      return this;
    }
    _to(n, at) { this.tl.to(this.num, { sy: 0.1 }, at, 0.1, E.in); this.tl.text(this.num, String(n), at + 0.1); this.tl.to(this.num, { sy: 1 }, at + 0.1, 0.18, E.out); }
    pulse(at, dur = 0.6) { this.tl.to(this.num, { s: 1.2 }, at, dur * 0.4, E.out); this.tl.to(this.num, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); return this; }
    color(col, at, dur = 0.4) { this.tl.to(this.num, { color: col }, at, dur); return this; }
    dim(o, at, dur = 0.4) { this.tl.to(this.el, { o }, at, dur); return this; }
    hide(at, dur = 0.35) { this.tl.to(this.el, { o: 0 }, at, dur, E.in); return this; }
  }

  // ---- cells ---------------------------------------------------------------------------------------------------------
  class Cells {
    constructor(tl, parent, x, y, n, { w = 96, h = 96, gap = 10, size = 40, texts = [], align = 'left', stroke = C.ink } = {}) {
      Object.assign(this, { tl, n, w, h, gapPx: gap, size, y });
      this.x = align === 'center' ? x - (n * w + (n - 1) * gap) / 2 : x;
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px' });
      this.svg = svgLayer(this.g);
      this.extra = new Array(n + 1).fill(0);   // extra px before each slot (gaps)
      this.slots = [...Array(n).keys()];        // slot -> cell id
      this.pos = [...Array(n).keys()];          // cell id -> slot
      this.off = new Array(n).fill(0);          // cell id -> current x offset from its build place
      this.els = [...Array(n).keys()].map(i => {
        const b = cell(this.g, this.x + i * (w + gap), y, w, h, texts[i] || '', { stroke, font: MONO(size), radius: 10 });
        b.style.transformOrigin = 'center center';
        tl.set(b, { o: 0 }, 0);
        return b;
      });
      this.ring = this.els.map(b => { const r = box(b, 0, 0, { width: w + 'px', height: h + 'px', borderRadius: '10px', boxShadow: `inset 0 0 0 4px ${C.pat}` }); tl.set(r, { o: 0 }, 0); return r; });
      this.fillEl = this.els.map(b => { const f = box(b, 0, 0, { width: w + 'px', height: h + 'px', borderRadius: '10px', background: C.ink }); b.insertBefore(f, b.firstChild); tl.set(f, { o: 0 }, 0); return f; });
    }
    slotX(s) { let x = this.x + s * (this.w + this.gapPx); for (let q = 0; q <= s && q < this.extra.length; q++) x += this.extra[q]; return x; }
    slotOf(i) { return this.pos[i]; }
    cellRect(i) { const x = this.slotX(this.pos[i]); return { x, y: this.y, w: this.w, h: this.h, cx: x + this.w / 2, cy: this.y + this.h / 2 }; }
    show(at, { stagger = 0.04 } = {}) { this.slots.forEach((id, s) => fadeIn(this.tl, this.els[id], at + s * stagger, 0.5, 12)); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    text(i, s) { const t = this.els[i]._t; t.textContent = s; t._text0 = s; t._shown = s; return this; }
    flip(i, s, at) { flip(this.tl, this.els[i]._t, s, at); return this; }
    _place(i, s, at, dur, lift = 0) {
      const tl = this.tl, dx = this.slotX(s) - (this.x + i * (this.w + this.gapPx));
      if (Math.abs(dx - this.off[i]) < 0.5) return;
      tl.to(this.els[i], { x: dx }, at, dur, E.io);
      if (lift) { tl.to(this.els[i], { y: lift }, at, dur * 0.5, E.out); tl.to(this.els[i], { y: 0 }, at + dur * 0.5, dur * 0.5, E.in); }
      this.off[i] = dx;
    }
    swap(i, j, at, { dur = 0.7 } = {}) {
      const si = this.pos[i], sj = this.pos[j];
      this.pos[i] = sj; this.pos[j] = si; this.slots[si] = j; this.slots[sj] = i;
      this._place(i, sj, at, dur, -this.h * 0.7); this._place(j, si, at, dur, this.h * 0.7);
      return this;
    }
    move(order, at, { dur = 0.8 } = {}) {
      if (order.length !== this.n) console.warn('BX.Cells.move: order must list every cell');
      // cells that move left pass above the row, cells that move right below it
      order.forEach((id, s) => {
        const from = this.pos[id];
        this.pos[id] = s; this.slots[s] = id;
        // a longer way goes further out, so that cells moving the same way do not cross
        if (from !== s) this._place(id, s, at, dur, (s < from ? -1 : 1) * this.h * Math.min(1.9, 0.6 + 0.4 * (Math.abs(s - from) - 1)));
      });
      return this;
    }
    outline(i, col, at, dur = 0.35) {
      if (col == null || col === C.pat) { this.tl.to(this.ring[i], { o: col ? 1 : 0 }, at, dur); return this; }
      this.ring[i].style.boxShadow = `inset 0 0 0 4px ${col}`; this.tl.to(this.ring[i], { o: 1 }, at, dur); return this;
    }
    fill(i, col, at, dur = 0.35) {
      if (col == null) { this.tl.to(this.fillEl[i], { o: 0 }, at, dur); this.tl.to(this.els[i]._t, { color: C.ink }, at, dur); return this; }
      this.fillEl[i].style.background = col; this.tl.to(this.fillEl[i], { o: 1 }, at, dur); this.tl.to(this.els[i]._t, { color: C.bg }, at, dur);
      return this;
    }
    dim(ids, o, at, dur = 0.4) { for (const i of [].concat(ids)) this.tl.to(this.els[i], { o }, at, dur); return this; }
    dimSlots(s0, s1, o, at, dur = 0.4) { for (let s = s0; s <= s1; s++) this.tl.to(this.els[this.slots[s]], { o }, at, dur); return this; }
    bracket(s0, s1, name, at, { out = null, depth = 16 } = {}) {
      const tl = this.tl, x1 = this.slotX(s0) + 4, x2 = this.slotX(s1) + this.w - 4, y = this.y + this.h + 14 + depth;
      const p = bracket(tl, this.svg, x1, x2, y, { at, legs: 'up', depth, stroke: C.bind, width: 2.5 });
      let tab = null;
      if (name) { tab = tabEl(this.g, (x1 + x2) / 2, y + 28, name, { size: 32 }); tl.set(tab, { o: 0, s: 0.6 }, 0); tl.to(tab, { o: 1, s: 1 }, at + 0.35, 0.4, E.out5); }
      const res = { path: p, tab, hide(t) { tl.to(p, { o: 0 }, t, 0.3); if (tab) tl.to(tab, { o: 0 }, t, 0.3); }, rename(nm, t) { if (tab) flip(tl, tab, nm, t); } };
      if (out != null) res.hide(out);
      return res;
    }
    divider(s, at) {
      const tl = this.tl, self = this;
      const xAt = q => self.slotX(q) - self.gapPx / 2 - 2;
      const e = box(this.g, xAt(s), this.y - 22, { width: '4px', height: (this.h + 44) + 'px', borderRadius: '2px', background: C.ink });
      const x0 = xAt(s);
      tl.set(e, { o: 0, sy: 0.2 }, 0); tl.to(e, { o: 1, sy: 1 }, at, 0.45, E.out5);
      return { el: e, move(s2, t, dur = 0.7) { tl.to(e, { x: xAt(s2) - x0 }, t, dur, E.io); }, hide(t) { tl.to(e, { o: 0 }, t, 0.3); } };
    }
    gap(s, px, at, { dur = 0.6 } = {}) {
      this.extra[s] += px;
      for (let q = s; q < this.n; q++) this._place(this.slots[q], q, at, dur);
      return this;
    }
  }

  // ---- bars ----------------------------------------------------------------------------------------------------------
  function bars(tl, parent, x, y, rows, { scale = 'log', min = 1, max, w = 900, h = 40, pitch = 130, minLen = 10, names = true, nameX, nameSize = 48, textSize = 36, unit = '' } = {}) {
    max = max ?? Math.max(...rows.map(r => r.value || 0));
    const len = v => {
      const L = scale === 'log' ? w * Math.log(Math.max(v, 1e-9) / min) / Math.log(max / min) : w * v / max;
      return Math.max(minLen, Math.min(w, L));
    };
    const g = box(parent, 0, 0, { width: W + 'px', height: H + 'px' });
    const out = rows.map((r, i) => {
      const yy = y + i * pitch, col = r.good ? C.good : C.dim, L = len(r.value);
      const bar = box(g, x, yy - h / 2, { width: w + 'px', height: h + 'px', transformOrigin: 'left center' });
      if (r.segments) {
        const n = r.segments, sw = (w - (n - 1) * 3) / n;
        for (let q = 0; q < n; q++) box(bar, q * (sw + 3), 0, { width: sw + 'px', height: h + 'px', borderRadius: '2px', background: col });
      } else box(bar, 0, 0, { width: w + 'px', height: h + 'px', borderRadius: '4px', background: col });
      bar._len = L;
      tl.set(bar, { sx: 0, o: 0 }, 0);
      const text = box(g, x + L + 22, yy - Math.round(textSize * 1.3) / 2, Object.assign(MONO(textSize), { color: r.good ? C.good : C.ink, whiteSpace: 'pre', lineHeight: Math.round(textSize * 1.3) + 'px' }), r.text ?? (String(r.value) + unit));
      tl.set(text, { o: 0 }, 0);
      let name = null;
      if (names) {
        const nx = nameX ?? x - 40;
        name = box(g, nx - 800, yy - Math.round(nameSize * 1.22) / 2, Object.assign(SERIF(nameSize), { width: '800px', textAlign: 'right', whiteSpace: 'pre', color: r.good ? C.good : C.ink }), r.name);
        tl.set(name, { o: 0 }, 0);
      }
      return { bar, text, name, len: L, x0: x };
    });
    return {
      g, rows: out, len,
      grow(at, { stagger = 0.3, dur = 0.8, rows: which } = {}) {
        out.forEach((r, i) => {
          if (which && !which.includes(i)) return;
          const t = at + i * stagger;
          if (r.name) fadeIn(tl, r.name, t - 0.1, 0.5, 10);
          tl.set(r.bar, { o: 1 }, t); tl.to(r.bar, { sx: r.len / w }, t, dur, E.io);
          tl.fromTo(r.text, { o: 0 }, { o: 1 }, t + dur * 0.8, 0.4);
        });
        return this;
      },
      set(i, { value, text }, at, { dur = 0.7 } = {}) {
        const r = out[i];
        if (value != null) { const L = len(value); tl.to(r.bar, { sx: L / w }, at, dur, E.io); tl.to(r.text, { x: L - r.len }, at, dur, E.io); }
        if (text != null) flip(tl, r.text, text, at + dur * 0.3);
        return this;
      },
      replace(i, text, col, at) {
        const r = out[i];
        tl.to(r.bar, { o: 0 }, at, 0.35, E.in); tl.to(r.text, { o: 0 }, at, 0.35, E.in);
        const e = box(g, x, y + i * pitch - 20, Object.assign(LABEL(34), { color: col || C.ink, whiteSpace: 'pre', lineHeight: '40px' }), text);
        fadeIn(tl, e, at + 0.3, 0.5, 10);
        r.replaced = e;
        return e;
      },
      hide(at, dur = 0.4) { tl.to(g, { o: 0 }, at, dur, E.in); return this; },
    };
  }

  // ---- the title -------------------------------------------------------------------------------------------------------
  const TITLE = ['Fast Coalgebraic', 'Bisimilarity Minimization'];
  const AUTHORS = ['Jules Jacobs · Thorsten Wißmann', 'POPL 2023'];
  function titleCard(tl, root, { align = 'center', x = CX, y = 300, size = 110, at, lineGap = 0.25, authorsAt, authorSize = 32, gap = 34 } = {}) {
    const mk = (text, yy, style) => align === 'left' ? box(root, x, yy, Object.assign({ whiteSpace: 'pre' }, style), text) : cline(root, x, yy, [[text, null]], style).root;
    const lh = Math.round(size * 1.12);
    const lines = TITLE.map((t, i) => mk(t, y + i * lh, Object.assign(SERIF(size), { lineHeight: lh + 'px' })));
    if (align === 'left') lines.forEach(l => { l.style.left = (x - size * 0.05) + 'px'; });
    const ay = y + 2 * lh + gap;
    const authors = AUTHORS.map((t, i) => mk(t, ay + i * Math.round(authorSize * 1.65), LABEL(authorSize)));
    for (const e of [...lines, ...authors]) tl.set(e, { o: 0 }, 0);
    if (at != null) lines.forEach((l, i) => fadeIn(tl, l, at + i * lineGap, 0.8, 24));
    if (authorsAt != null) authors.forEach((a, i) => fadeIn(tl, a, authorsAt + i * 0.25, 0.6, 10));
    return { lines, authors, bottom: ay + 2 * Math.round(authorSize * 1.65) };
  }

  // ---- rows ------------------------------------------------------------------------------------------------------------
  class Rows {
    constructor(tl, root, { x = RAIL, y = 270, pitch = 124, size = 56, numbers = true, titleX, back = 0.6, numSize = 32 } = {}) {
      Object.assign(this, { tl, root, x, y, pitch, size, numbers, back, numSize }); this.titleX = titleX ?? x + 70; this.rows = [];
    }
    rowY(i) { return this.y + i * this.pitch; }
    mid(i) { return this.rowY(i) + Math.round(this.size * 1.22) / 2; }
    row(title, at, { num } = {}) {
      const i = this.rows.length, y = this.rowY(i), parts = [];
      const nm = num !== undefined ? num : (this.numbers ? String(i + 1) : null);
      let numEl = null;
      if (nm) { numEl = box(this.root, this.x, this.mid(i) - this.numSize * 0.62, Object.assign(LABEL(this.numSize), { whiteSpace: 'pre' }), nm); fadeIn(this.tl, numEl, at - 0.05, 0.5, 12); parts.push(numEl); }
      const t = box(this.root, this.titleX, y, Object.assign(SERIF(this.size), { whiteSpace: 'pre' }), title);
      fadeIn(this.tl, t, at, 0.6, 16); parts.push(t);
      for (const r of this.rows) if (r.backAt == null) { r.backAt = at - 0.15; for (const e of r.parts) this.tl.to(e, { o: this.back }, r.backAt, 0.5); }
      const row = { y, at, parts, num: numEl, title: t, backAt: null };
      row.add = e => { const x = rootOf(e); parts.push(x); if (row.backAt != null) this.tl.to(x, { o: this.back }, row.backAt, 0.5); return e; };
      this.rows.push(row);
      return row;
    }
    evidence(i, e, at, dy = 14) { fadeIn(this.tl, rootOf(e), at, 0.5, dy); this.rows[i].add(e); return e; }
    all() { return this.rows.flatMap(r => r.parts); }
  }


  // ---- pieces and nests ----------------------------------------------------------------------------------------------
  // the width of a small caps label (system sans), measured once per text and size
  const _lw = {};
  function labelW(text, size) {
    const k = size + '|' + text;
    if (_lw[k] != null) return _lw[k];
    const m = document.createElement('span');
    Object.assign(m.style, LABEL(size), { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' });
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return (_lw[k] = w);
  }
  // a piece chip: a rounded rectangle with a 2 px ink line and the piece's name in ink small caps ('\n' breaks it)
  function piece(parent, x, y, text, { size = 30, align = 'left', dashed = false, color = C.ink } = {}) {
    const lines = String(text).split('\n');
    const w = Math.round(Math.max(...lines.map(l => labelW(l, size))) + size * 1.2), h = Math.round(lines.length * size * 1.2 + size * 0.7);
    const e = box(parent, align === 'center' ? x - w / 2 : x, y - h / 2, Object.assign(LABEL(size), {
      width: w + 'px', height: h + 'px', boxSizing: 'border-box', display: 'flex', alignItems: 'center', justifyContent: 'center',
      textAlign: 'center', whiteSpace: 'pre', color, borderRadius: Math.round(size * 0.35) + 'px', border: `2px ${dashed ? 'dashed' : 'solid'} ${color}`,
      paddingLeft: LS + 'em', transformOrigin: 'center center',
    }), text);
    e._w = w; e._h = h;
    return e;
  }
  class Nest {
    constructor(tl, parent, spec, cx, cy, { size = 30, pad = 16, gap = 14, stateR = 26 } = {}) {
      Object.assign(this, { tl, size, pad, gap, stateR, cx, cy });
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${cx}px ${cy}px` });
      this.nodes = [];
      const sz = this._measure(spec);
      this.w = sz.w; this.h = sz.h;
      this._place(spec, cx - sz.w / 2, cy - sz.h / 2, 0);
      for (const n of this.nodes) for (const e of n.els) tl.set(e, { o: 0 }, 0);
    }
    get top() { return this.cy - this.h / 2; }
    get bottom() { return this.cy + this.h / 2; }
    _tab(name) { const s = this.size; return { w: Math.round(labelW(name, s) + s * 0.9), h: Math.round(s * 1.2 + 10) }; }
    _measure(n) {
      if (n.state) return (n._sz = { w: 2 * this.stateR, h: 2 * this.stateR });
      if (n.leaf) { const lines = n.leaf.split('\n'); return (n._sz = { w: Math.round(Math.max(...lines.map(l => labelW(l.toUpperCase(), this.size))) + this.size * 1.2), h: Math.round(lines.length * this.size * 1.2 + this.size * 0.7) }); }
      const kids = n.items.map(c => this._measure(c)), t = this._tab(n.box);
      const cw = kids.reduce((a, k) => a + k.w, 0) + this.gap * (kids.length - 1), ch = Math.max(...kids.map(k => k.h));
      // (a box inside starts below this box's tab, so that the two tabs never touch)
      n._top = Math.round(n.items.some(c => c.box) ? t.h + 8 : t.h / 2 + this.pad * 0.75);
      return (n._sz = { w: Math.max(cw + 2 * this.pad, t.w + 2 * 16), h: n._top + ch + this.pad, cw, ch });
    }
    _place(n, x, y, depth) {
      const { w, h } = n._sz, tl = this.tl, rec = { id: n.id, kind: n.state ? 'state' : n.leaf ? 'leaf' : 'box', x, y, w, h, depth, els: [] };
      this.nodes.push(rec);
      if (n.state) {
        rec.els.push(box(this.g, x, y, { width: w + 'px', height: h + 'px', boxSizing: 'border-box', borderRadius: '50%', border: `3px solid ${C.ink}`, transformOrigin: 'center center' }));
      } else if (n.leaf) {
        rec.els.push(piece(this.g, x, y + h / 2, n.leaf, { size: this.size }));
      } else {
        const rect = box(this.g, x, y, { width: w + 'px', height: h + 'px', boxSizing: 'border-box', borderRadius: '16px', border: `2px solid ${C.ink}`, background: alpha(C.ink, 0) });
        const t = this._tab(n.box);
        const tab = box(this.g, x + 16, y - t.h / 2, Object.assign(LABEL(this.size), { width: t.w + 'px', height: t.h + 'px', boxSizing: 'border-box', lineHeight: (t.h - 4) + 'px', textAlign: 'center', whiteSpace: 'pre', color: C.ink, background: C.bg, border: `2px solid ${C.ink}`, borderRadius: '9px', paddingLeft: LS + 'em', transformOrigin: 'center center' }), n.box);
        rec.els.push(rect, tab); rec.rect = rect; rec.tab = tab;
        let cx = x + (w - n._sz.cw) / 2;
        const cy = y + n._top + n._sz.ch / 2;
        for (const c of n.items) { this._place(c, cx, cy - c._sz.h / 2, depth + 1); cx += c._sz.w + this.gap; }
      }
      return rec;
    }
    node(id) { const n = this.nodes.find(q => q.id === id); if (!n) console.warn('BX.Nest: no node', id); return n; }
    // one node (not its contents) appears: a box grows a little into place, a leaf or a state rises in
    show(id, at, { dur = 0.5 } = {}) {
      const n = typeof id === 'object' ? id : this.node(id); if (!n) return this;
      for (const e of n.els) { this.tl.set(e, { s: n.kind === 'box' && e === n.rect ? 1.03 : 0.9 }, 0); this.tl.to(e, { o: 1, s: 1 }, at, dur, E.out5); }
      return this;
    }
    // a node and everything inside it, outside in, `stagger` apart
    showTree(id, at, { stagger = 0.12, dur = 0.5 } = {}) {
      const i0 = this.nodes.indexOf(this.node(id)), d0 = this.nodes[i0].depth;
      let i = i0, k = 0;
      do { this.show(this.nodes[i], at + k * stagger, { dur }); k++; i++; } while (i < this.nodes.length && this.nodes[i].depth > d0);
      return this;
    }
    pulse(id, at, { dur = 0.6 } = {}) { const n = this.node(id); if (n && n.tab) { this.tl.to(n.tab, { s: 1.18 }, at, dur * 0.4, E.out); this.tl.to(n.tab, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); } return this; }
    // a soft neutral band of light fills a box, and goes
    glow(id, at, { dur = 0.9, fill = 0.09 } = {}) { const n = this.node(id); if (n && n.rect) { this.tl.to(n.rect, { bg: alpha(C.ink, fill) }, at, dur * 0.35); this.tl.to(n.rect, { bg: alpha(C.ink, 0) }, at + dur * 0.5, dur * 0.5); } return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    dim(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
  }

  window.BX = {
    CX, RAIL, LINE, LABEL, SERIF, MONO, cline, lline, clabel, cserif, note, strikeEl,
    svg: svgLayer, tick: tickM, cross: crossM, dpath, line, arc, bracket, cell, flip, circleD, ctext, dim,
    Chip, Block, tab: freeTab, Machine, Struct, Table, Counter, Cells, bars, titleCard, TITLE, AUTHORS, Rows,
    stokens, piece, Nest, labelW,
  };
})();

// ==== src/scenes/a_open.js ====
// The opening (hook, roadmap, title) and the close (recap, end) of the Boa video, built with BX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = BX;

  // ============================================ hook ==========================================================
  scene('hook', ({ tl, root, cue }) => {
    const svg = BX.svg(root);
    // "Here is a small machine: a finite automaton with five states."
    const tOne = cue('one');
    const m5 = new BX.Machine(tl, root, { kind: 'dfa', cx: CX, cy: 480, scale: 1.3 });
    m5.show(tOne - 0.2, { stagger: 0.14 });
    const b5 = m5.bounds();
    BX.note(tl, root, CX, b5.y1 + 22, 'a finite automaton · five states', tOne + 2.1, cue('same') - 0.3);

    // "Two of its states behave in exactly the same way, and so do two others.": green dashed links, labelled at
    // the right of the drawing
    const r = m5.r + 8, p2 = m5.pos(2), p3 = m5.pos(3), p4 = m5.pos(4), p5 = m5.pos(5);
    const a = 0.62;   // the angle below the horizontal where the 2-3 link leaves its circles
    const link23 = BX.dpath(tl, svg, `M ${p2.x + r * Math.cos(a)} ${p2.y + r * Math.sin(a)} Q ${CX} ${p2.y + 120} ${p3.x - r * Math.cos(a)} ${p3.y + r * Math.sin(a)}`, { stroke: C.good, width: 4, dash: '12 10' });
    const yb = b5.y1 + 40;   // the 4-5 link runs under the whole drawing
    const s4 = [p4.x - r * 0.35, p4.y + r * 0.94], e5 = [p5.x + r * 0.35, p5.y + r * 0.94];
    const link45 = BX.dpath(tl, svg, `M ${s4[0]} ${s4[1]} C ${s4[0] - 30} ${yb + 10} ${e5[0] + 30} ${yb + 10} ${e5[0]} ${e5[1]}`, { stroke: C.good, width: 4, dash: '12 10' });
    const tSame = cue('same'), tSame2 = cue('same2'), tMerge = cue('merge');
    tl.to(link23, { draw: 1 }, tSame + 1.2, 0.6, E.io);
    BX.note(tl, root, 1385, p2.y + 22, 'same behaviour', tSame + 1.5, tMerge - 0.35, { align: 'left', color: C.good });
    tl.to(link45, { draw: 1 }, tSame2 + 0.4, 0.7, E.io);
    BX.note(tl, root, 1385, yb - 24, 'same behaviour', tSame2 + 0.6, tMerge - 0.35, { align: 'left', color: C.good });
    for (const l of [link23, link45]) tl.to(l, { o: 0 }, tMerge - 0.35, 0.3);

    // "Merge them, and the machine has three states, and does what it did before.": 3 slides onto 2 and 5 onto 4,
    // the edges go, the minimized automaton takes over, moves to the middle and is drawn
    // (3 and 5 fade as they slide, so that two numbers never overprint; the new edges are drawn while the drawing
    // moves to the middle, so that the stage never shows the circles alone for long)
    // (the edges that the minimized automaton keeps stay until it takes over)
    const kept = ['1>2', '2>4', '4>4'];
    m5.dim(r => r.type === 'edge' && !kept.includes(r.id), 0, tMerge - 0.2, 0.35);
    m5.slide(3, 2, tMerge, 0.7); m5.slide(5, 4, tMerge, 0.7);
    m5.dim([3, 5], 0, tMerge + 0.15, 0.45);
    const tSwap = tMerge + 0.7;
    const m3 = new BX.Machine(tl, root, { kind: 'dfa3', cx: CX, cy: 480, scale: 1.3 });
    m3.appear(tSwap, { sel: 'states', dur: 0 });
    tl.set(m5.g, { o: 0 }, tSwap);
    const b3 = m3.bounds(), dx = CX - b3.cx, dy = 420 - b3.cy;
    m3.to({ x: dx, y: dy }, tSwap + 0.05, 0.75);
    m3.appear(tSwap, { sel: ['1>2', '2>4'], dur: 0 });
    m3.show(tSwap + 0.1, { sel: ['2>2', '4>4'], stagger: 0.18 });
    const lab3 = BX.note(tl, root, CX, b3.y1 + dy + 22, 'three states · same behaviour', tMerge + 1.55, null);
    // "That is minimization."
    const tMin = cue('min');
    const word = BX.cserif(root, CX, b3.y1 + dy + 78, 'minimization', 72);
    fadeIn(tl, word, tMin + 0.3, 0.7, 18);

    // "There are many kinds of machine like this: transition systems, Markov chains, and more."
    const tZoo = cue('zoo');
    m3.hide(tZoo - 0.35); fadeOut(tl, lab3, tZoo - 0.35); fadeOut(tl, word, tZoo - 0.35);
    const zoo = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const XS = [400, 960, 1520], ZY = 430, LY = 655;
    const zd = new BX.Machine(tl, zoo, { kind: 'dfa', cx: XS[0], cy: ZY, scale: 0.75 });
    const zt = new BX.Machine(tl, zoo, { kind: 'ts', cx: XS[1], cy: ZY, scale: 0.75 });
    const zm = new BX.Machine(tl, zoo, { kind: 'mc', cx: XS[2], cy: ZY, scale: 0.75 });
    zd.appear(tZoo, { dur: 0.6 });
    zt.show(cue('ts') - 0.25, { stagger: 0.05, dur: 0.45 });
    zm.show(cue('mc') - 0.25, { stagger: 0.05, dur: 0.45 });
    const names = ['finite automaton', 'transition system', 'markov chain'].map((t, i) => BX.clabel(zoo, XS[i], LY, t));
    fadeIn(tl, names[0], tZoo + 0.3, 0.5, 10);
    fadeIn(tl, names[1], cue('ts') + 0.4, 0.5, 10);
    fadeIn(tl, names[2], cue('mc') + 0.4, 0.5, 10);
    const more = box(zoo, 1760, ZY - 50, Object.assign(BX.SERIF(72), { color: C.dim, width: '100px', textAlign: 'center' }), '…');
    fadeIn(tl, more, cue('mc') + 1.05, 0.5, 10);

    // "For a long time, each kind had its own minimization algorithm."
    const tEach = cue('each'), tGen = cue('generic');
    XS.forEach((x, i) => BX.note(tl, zoo, x, LY + 52, 'its own algorithm', tEach + 1.0 + i * 0.4, tGen - 0.35));

    // "A general theory, called co-algebra, promises one algorithm for all of them. But the general algorithm that
    // existed was slow in practice, needed a great deal of memory, and did not cover every kind of machine."
    const zsvg = BX.svg(zoo);
    BX.bracket(tl, zsvg, 190, 1730, 722, { at: tGen + 0.2, dur: 0.7, legs: 'up', depth: 20, notch: 14 });
    BX.note(tl, zoo, CX, 752, 'one general algorithm (coalgebra)', tGen + 1.25, null, { color: C.ink });
    [['slow in practice', 510, 7.6], ['memory hungry', 960, 9.2], ['not every kind', 1410, 10.85]].forEach(([t, x, d]) => BX.note(tl, zoo, x, 830, t, tGen + d, null));

    // "This video is about a new algorithm, and a tool called Boa that implements it."
    const tV = cue('video');
    tl.to(zoo, { o: 0.3 }, tV - 0.2, 0.5);
    tl.to(zoo, { o: 0 }, tV + 0.9, 0.4, E.in);
    BX.note(tl, root, CX, 500, 'a new algorithm, and a tool', tV + 1.2, null);
    const boa = BX.cserif(root, CX, 300, 'Boa', 140);
    fadeIn(tl, boa, tV + 3.1, 0.8, 22);

    // "It covers all of these kinds and more, and it is faster than the earlier tools, with far less memory."
    const tC = cue('claim');
    [['all these kinds, and more', 0.6], ['faster', 2.85], ['far less memory', 4.75]].forEach(([t, d], i) => BX.note(tl, root, CX, 590 + i * 56, t, tC + d, null, { color: C.good }));
    // "By the end, we will have run the algorithm by hand, and we will know why it is fast."
    BX.note(tl, root, CX, 806, 'by the end: the algorithm, run by hand', cue('hand') + 0.2, null, { color: C.ink });
    BX.note(tl, root, CX, 858, 'and why it is fast', cue('why') + 0.4, null, { color: C.ink });
  });

  // ============================================ roadmap =======================================================
  scene('roadmap', ({ tl, root, cue }) => {
    const head = box(root, RAIL, 160, Object.assign(BX.LABEL(32), { color: C.ink, whiteSpace: 'pre' }), 'in this video');
    fadeIn(tl, head, cue('coming') - 0.15, 0.5, 10);
    const rows = new BX.Rows(tl, root, { x: RAIL, y: 250, pitch: 108, size: 52 });
    const EX = 1120;   // (clear of the longest title, row 5's)

    rows.row('One shape for many machines', cue('shape') - 0.1);
    const t1 = new BX.Table(tl, root, EX, rows.mid(0), [[3, '(false, 5, 3)']], { size: 40 });
    t1.show(cue('shape') + 1.55); rows.rows[0].add(t1.g);

    rows.row('Equivalent states', cue('equiv') - 0.1);
    const g2 = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const c2 = new BX.Chip(tl, g2, EX + 28, rows.mid(1), '2', { r: 26 }), c3 = new BX.Chip(tl, g2, EX + 158, rows.mid(1), '3', { r: 26 });
    const eq = BX.ctext(g2, EX + 93, rows.mid(1), '=', Object.assign(BX.MONO(44), { color: C.good }), 60);
    const tE = cue('equiv') + 2.2;
    c2.show(tE); c3.show(tE + 0.1); fadeIn(tl, eq, tE + 0.3, 0.5, 8);
    rows.rows[1].add(g2);

    rows.row('A simple algorithm', cue('naive') - 0.1);
    rows.evidence(2, box(root, EX, rows.mid(2) - 20, Object.assign(BX.LABEL(32), { whiteSpace: 'pre' }), 'correct, but slow'), cue('naive') + 1.7);

    rows.row('Two ideas that make it fast', cue('fast') - 0.1);
    rows.evidence(3, box(root, EX, rows.mid(3) - 26, Object.assign(BX.MONO(40), { whiteSpace: 'pre', color: C.ink }), 'M log N'), cue('fast') + 1.2);

    rows.row('Kinds of machine, built from pieces', cue('types') - 0.1);
    // two small nested outlined boxes, at "put together from a few pieces"
    const g5 = box(root, 0, 0, { width: W + 'px', height: '1080px' }), m5 = rows.mid(4);
    box(g5, EX, m5 - 26, { width: '132px', height: '52px', boxSizing: 'border-box', borderRadius: '10px', border: `2px solid ${C.ink}` });
    box(g5, EX + 52, m5 - 15, { width: '68px', height: '30px', boxSizing: 'border-box', borderRadius: '7px', border: `2px solid ${C.ink}` });
    box(g5, EX + 12, m5 - 9, { width: '30px', height: '18px', boxSizing: 'border-box', borderRadius: '5px', border: `2px solid ${C.ink}` });
    rows.evidence(4, g5, cue('types') + 2.0, 8);

    rows.row('Measurements', cue('bench') - 0.1);
    const g6 = box(root, EX, rows.mid(5) - 18, { width: '240px', height: '36px' });
    box(g6, 0, 0, { width: '230px', height: '14px', borderRadius: '3px', background: C.dim });
    box(g6, 0, 22, { width: '22px', height: '14px', borderRadius: '3px', background: C.good });
    rows.evidence(5, g6, cue('bench') + 0.5, 8);
  });

  // ============================================ title =========================================================
  scene('title', ({ tl, root, cue }) => {
    BX.titleCard(tl, root, { align: 'left', x: RAIL, y: 300, size: 110, at: cue('title') - 0.2, authorsAt: cue('title') + 1.2 });
  });

  // ============================================ recap =========================================================
  scene('recap', ({ tl, root, cue }) => {
    const rows = new BX.Rows(tl, root, { x: RAIL, y: 200, pitch: 108, size: 48 });
    const EX = 1380;

    rows.row('States, each with a structure built from a few pieces', cue('r1') - 0.1);
    const t1 = new BX.Table(tl, root, EX, rows.mid(0), [[3, '(false, 5, 3)']], { size: 36 });
    t1.show(cue('r1') + 4.3); rows.rows[0].add(t1.g);

    rows.row('Guess blocks, rename, compare', cue('r2') - 0.1);
    const t2 = new BX.Table(tl, root, EX, rows.mid(1), [[2, '(false, Y, X)'], [3, '(false, Y, X)']], { size: 30, pitch: 42, cy: rows.mid(1) });
    t2.show(cue('r2') + 2.6, { stagger: 0.1 });
    t2.equal(2, 3, cue('r2') + 3.6);
    rows.rows[1].add(t2.g);

    rows.row('Every state, every round: too slow', cue('r3') - 0.1);
    rows.evidence(2, box(root, EX, rows.mid(2) - 26, Object.assign(BX.MONO(40), { whiteSpace: 'pre', color: C.ink }), 'N²'), cue('r3') + 2.7);

    rows.row('Only dirty states; the largest part keeps its name', cue('r4') - 0.1);
    const g4 = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const ch = new BX.Chip(tl, g4, EX + 28, rows.mid(3), '', { r: 24 });
    ch.show(cue('r4') + 1.5); ch.dirty(cue('r4') + 1.7);
    const tab = BX.tab(g4, EX + 130, rows.mid(3), 'X', { size: 32 });
    tl.set(tab, { o: 0 }, 0); fadeIn(tl, tab, cue('r4') + 4.5, 0.5, 8);
    rows.rows[3].add(g4);

    rows.row('M log N signatures, little memory', cue('r5') - 0.1);
    rows.evidence(4, box(root, EX, rows.mid(4) - 26, Object.assign(BX.MONO(40), { whiteSpace: 'pre', color: C.good }), 'M log N'), cue('r5') + 0.6);

    rows.row('One tool for many kinds of machine', cue('r6') - 0.1);
    rows.evidence(5, box(root, EX, rows.mid(5) - 32, Object.assign(BX.SERIF(52), { whiteSpace: 'pre', color: C.good }), 'Boa'), cue('r6') + 1.0);
  });

  // ============================================ end ===========================================================
  scene('end', ({ tl, root, cue }) => {
    const tc = BX.titleCard(tl, root, { align: 'center', x: CX, y: 290, size: 96, at: cue('title') - 0.2, authorsAt: cue('title') + 2.0 });
    const y = tc.bottom + 40, t = cue('paper');
    const l1 = BX.cline(root, CX, y, [['in the paper:', null], ['  the definitions', null], [' · the data structure', null]], BX.LABEL(32));
    const l2 = BX.cline(root, CX, y + 54, [['the complexity analysis', null], [' · all the measurements', null]], BX.LABEL(32));
    // the parts arrive at their words
    [[l1.parts[0], 0], [l1.parts[1], 1.25], [l1.parts[2], 2.45], [l2.parts[0], 4.5], [l2.parts[1], 6.1]].forEach(([e, d]) => { tl.set(e, { o: 0 }, 0); fadeIn(tl, e, t + d - 0.1, 0.5, 10); });
    return { keep: true };
  });
})();

// ==== src/scenes/b.js ====
// One shape for many machines (shape_a, shape_b, shape_c), and the guess (eq_a, eq_b), built with BX (common.js).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const { CX } = BX;

  // ---- local helpers -----------------------------------------------------------------------------------------
  // a soft neutral band along an edge of a machine (not kept in the machine's records, so that m.light/m.focus
  // do not bring it back after it has gone)
  function edgeMark(tl, m, id, at, out, { color = C.dim, fill = 0.12 } = {}) {
    const r = m.edges.find(e => e.id === id);
    const p = el(m.halo, 'path');
    p.setAttribute('d', r.d); p.setAttribute('fill', 'none'); p.setAttribute('stroke-width', 18); p.setAttribute('stroke-linecap', 'round');
    p.style.stroke = alpha(color, Math.min(0.35, fill * 2.2));
    tl.set(p, { o: 0 }, 0); tl.to(p, { o: 1 }, at, 0.4);
    if (out != null) tl.to(p, { o: 0 }, out, 0.35);
    return p;
  }
  // the labels of some edges grow a little, and back
  function pulseLabels(tl, m, pred, at, dur = 0.6) {
    for (const r of m.edges.filter(pred)) {
      if (!r.lab) continue;
      tl.to(r.lab, { s: 1.35 }, at, dur * 0.4, E.out); tl.to(r.lab, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io);
    }
  }
  // a whole table (its group, the size of the stage, placed at 0, 0) scaled by s about the point (fx, fy), which
  // lands on (tx, ty)
  function scaleTo(tl, t, s, fx, fy, tx, ty, at, dur = 0.7) {
    t.g.style.transformOrigin = '0 0';
    tl.to(t.g, { s, x: tx - s * fx, y: ty - s * fy }, at, dur, E.io);
  }
  // a row of a table appears at once (to take over from another copy of it in the same place)
  function rowNow(tl, t, k, at) {
    const r = t._row(k);
    r.chip.show(at, { dur: 0.01, dy: 0 });
    r.s.show(at, { stagger: 0, rise: 0, dur: 0.01 });
  }
  // a centred small caps label whose pieces may be set in mono (an edge letter keeps its lower case):
  // parts [[text, 'label' | 'mono']]
  function mixLabel(tl, root, cx, y, parts, at, out, { size = 32, color = C.dim } = {}) {
    const b = box(root, cx - 400, y, { width: '800px', textAlign: 'center', whiteSpace: 'pre', lineHeight: Math.round(size * 1.3) + 'px' });
    for (const [text, kind] of parts) {
      const st = kind === 'mono' ? Object.assign(BX.MONO(size + 2), { color, lineHeight: 'inherit', fontWeight: 500 }) : Object.assign(BX.LABEL(size), { color, lineHeight: 'inherit' });
      el(b, 'span', Object.assign(st, { position: 'relative', display: 'inline' }), text);
    }
    fadeIn(tl, b, at, 0.5, 10);
    if (out != null) fadeOut(tl, b, out, 0.35);
    return b;
  }
  // a label left-aligned at x (BX.note with align left)
  const lnote = (tl, root, x, y, text, at, out, o = {}) => BX.note(tl, root, x, y, text, at, out, Object.assign({ align: 'left' }, o));

  const DFA = [[1, '(false, 2, 3)'], [2, '(false, 4, 3)'], [3, '(false, 5, 3)'], [4, '(true, 5, 4)'], [5, '(true, 4, 4)']];
  const TS = [[1, '{2, 3, 4}'], [2, '{1, 4}'], [3, '{3, 4, 5}'], [4, '{4, 5}'], [5, '{ }']];
  const MC = [[1, '(false, {2: ⅓, 3: ⅔})'], [2, '(false, {2: ½, 4: ½})'], [3, '(false, {2: ¼, 4: ½, 5: ¼})'], [4, '(true, {4: 1})'], [5, '(false, {3: ½, 4: ½})']];

  // ============================================ shape_a =======================================================
  scene('shape_a', ({ tl, root, cue }) => {
    // "Start with the finite automaton."
    const m = new BX.Machine(tl, root, { kind: 'dfa', cx: 520, cy: 500, scale: 1.3 });
    m.show(cue('dfa') - 0.25, { stagger: 0.12 });
    const bd = m.bounds();

    // "The usual picture has states, and arrows labelled with letters. A double border means accepting."
    const tU = cue('usual');
    pulseLabels(tl, m, e => /a/.test(e.label || ''), tU + 2.45);
    pulseLabels(tl, m, e => /b/.test(e.label || ''), tU + 3.15);
    m.pulse([4, 5], tU + 4.4, { dur: 0.7 });
    const lDouble = BX.note(tl, root, 520, bd.y1 + 24, 'double border: accepting', tU + 4.6, cue('state') - 0.3);

    // "Now look at it from the point of view of one state."
    const tS = cue('state');
    m.focus([3, 'out:3'], tS - 0.1, { o: 0.3, dur: 0.5 });

    // "State three is not accepting. On the letter A it goes to state five, and on the letter B it goes to itself."
    const t3 = cue('s3');
    m.pulse(3, t3 + 1.0, { dur: 0.7 });
    const tTable = cue('table');
    edgeMark(tl, m, '3>5', t3 + 2.3, t3 + 5.1);
    m.pulse('3>5', t3 + 2.3);
    m.light(5, t3 + 3.85);
    edgeMark(tl, m, '3>3', t3 + 5.2, tTable - 0.3);
    m.pulse('3>3', t3 + 5.2);

    // "So state three comes with three pieces of data: whether it is accepting, where the letter A leads, and where
    // the letter B leads. False, five, three."
    const tT = cue('triple');
    const X0 = 1060, Y0 = 420;
    const t1 = new BX.Table(tl, root, X0, Y0, [[3, '(false, 5, 3)']], { size: 60 });
    const s1 = t1.struct(3);
    t1.chip(3).show(tT + 0.2);
    s1.show(tT + 3.0, { sel: [0, 1, 2] });
    s1.show(tT + 4.55, { sel: [3, 4] });
    s1.show(tT + 6.3, { sel: [5, 6] });
    const ly = Y0 + 56, c = i => s1.rect(i).cx;
    const lab = [
      mixLabel(tl, root, c(1), ly, [['accepting?', 'label']], tT + 3.2, tTable - 0.3),
      mixLabel(tl, root, c(3), ly + 52, [['on ', 'label'], ['a', 'mono']], tT + 4.75, tTable - 0.3),
      mixLabel(tl, root, c(5), ly, [['on ', 'label'], ['b', 'mono']], tT + 6.5, tTable - 0.3),
    ];
    // short leaders from the 5 down to its (lower) label
    const lsvg = BX.svg(root);
    const lead = BX.dpath(tl, lsvg, `M ${c(3)} ${Y0 + 40} L ${c(3)} ${ly + 48}`, { stroke: C.faint, width: 2 });
    tl.to(lead, { draw: 1 }, tT + 4.65, 0.3, E.io); tl.to(lead, { o: 0 }, tTable - 0.3, 0.3);
    void lab;
    [0, 0.8, 1.44].forEach((d, i) => s1.pulse([1, 3, 5][i], tT + 8.25 + d, { dur: 0.55 }));

    // "Write that down for every state, and the table is the whole automaton."
    m.light('all', tTable - 0.15, 0.6);
    const tab = new BX.Table(tl, root, X0, 0, DFA, { size: 52, pitch: 92, cy: 500, accepting: [4, 5] });
    scaleTo(tl, t1, 52 / 60, X0, Y0, X0, tab.rowY(3), tTable - 0.1, 0.7);
    const tSwap = tTable + 0.65;
    tl.set(t1.g, { o: 0 }, tSwap);
    rowNow(tl, tab, 3, tSwap);
    [1, 2, 4, 5].forEach((k, i) => tab.showRow(k, tSwap + 0.1 + i * 0.14));
    lnote(tl, root, X0, tab.rowY(1) - 100, 'the whole automaton', tTable + 2.6, null);
  });

  // ============================================ shape_b =======================================================
  scene('shape_b', ({ tl, root, cue }) => {
    const TX = 1000;
    // "A transition system has no letters and no accepting states. A state just has a set of states it can step to."
    const tTs = cue('ts');
    const box1 = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const m = new BX.Machine(tl, box1, { kind: 'ts', cx: 520, cy: 500, scale: 1.3 });
    m.show(tTs - 0.2, { stagger: 0.1 });
    const bd = m.bounds();
    BX.note(tl, box1, 520, bd.y1 + 24, 'transition system', tTs + 0.9, null);

    // "State three can step to three, four, or five."
    const t3 = cue('t3');
    m.focus([3, 'out:3'], t3 - 0.1, { o: 0.35, dur: 0.5 });
    const tab = new BX.Table(tl, box1, TX, 0, TS, { size: 60, pitch: 96, cy: 500 });
    const s3 = tab.struct(3);
    tab.chip(3).show(t3 + 0.3);
    // {3, 4, 5}: '{' 3 , 4 , 5 '}'
    s3.show(t3 + 1.35, { sel: [0, 1] }); m.pulse('3>3', t3 + 1.35);
    s3.show(t3 + 2.0, { sel: [2, 3] }); m.pulse('3>4', t3 + 2.0);
    s3.show(t3 + 3.15, { sel: [4, 5, 6] }); m.pulse('3>5', t3 + 3.15);

    // "State five cannot step at all: its set is empty."
    const t5 = cue('t5');
    m.focus(5, t5 - 0.1, { o: 0.35, dur: 0.5 });
    tab.dim(3, 0.5, t5 - 0.1);
    tab.showRow(5, t5 + 0.65);
    const s5 = tab.struct(5);
    const lCant = lnote(tl, box1, s5.x + s5.width + 40, tab.rowY(5) - 20, 'cannot step', t5 + 0.95, t5 + 2.95);
    void lCant;
    // then the rest of the table, and the whole drawing
    const tFill = t5 + 2.9;
    tab.light(3, tFill);
    [1, 2, 4].forEach((k, i) => tab.showRow(k, tFill + i * 0.14));
    m.light('all', tFill, 0.5);

    // "In a Markov chain, a state steps at random."
    const tMc = cue('mc');
    tl.to(box1, { o: 0 }, tMc - 0.25, 0.4, E.in);
    const mc = new BX.Machine(tl, root, { kind: 'mc', cx: 520, cy: 500, scale: 1.3 });
    mc.show(tMc + 0.2, { stagger: 0.1 });
    BX.note(tl, root, 520, mc.bounds().y1 + 24, 'markov chain', tMc + 1.3, null);

    // "State one goes to state two with probability one third, and to state three with probability two thirds."
    const tM1 = cue('m1');
    mc.focus([1, 'out:1'], tM1 - 0.1, { o: 0.35, dur: 0.5 });
    mc.pulse('1>2', tM1 + 2.55); edgeMark(tl, mc, '1>2', tM1 + 2.55, cue('lab') + 1.5);
    mc.pulse('1>3', tM1 + 5.45); edgeMark(tl, mc, '1>3', tM1 + 5.45, cue('lab') + 1.5);

    // "So its data is a probability distribution over states,"
    const tD = cue('dist');
    const MY = 500 - 2 * 84;   // row 1's place in the full table (mono 44, pitch 84, centred on 500)
    const t1 = new BX.Table(tl, root, TX, MY, [[1, '{2: ⅓, 3: ⅔}']], { size: 56 });
    t1.showRow(1, tD + 0.05);
    const sd = t1.struct(1);
    const lDist = lnote(tl, root, sd.x, MY - 90, 'a distribution over states', tD + 1.6, cue('lab') - 0.2);
    void lDist;

    // "together with a flag, true or false."
    const tL = cue('lab');
    sd.morph('(false, {2: ⅓, 3: ⅔})', tL - 0.2, { dur: 0.6 });
    BX.note(tl, root, sd.rect('false').cx, MY - 90, 'a flag', tL + 0.75, null);
    const full = new BX.Table(tl, root, TX, 0, MC, { size: 44, pitch: 84, cy: 500, accepting: [4] });
    const tF = tL + 1.5;
    scaleTo(tl, t1, 44 / 56, TX, MY, TX, MY, tF, 0.6);
    tl.set(t1.g, { o: 0 }, tF + 0.6);
    rowNow(tl, full, 1, tF + 0.6);
    [2, 3, 4, 5].forEach((k, i) => full.showRow(k, tF + 0.6 + i * 0.12));
    mc.light('all', tF + 0.4, 0.5);
  });

  // ============================================ shape_c =======================================================
  scene('shape_c', ({ tl, root, cue }) => {
    // "The pattern is the same each time."
    const tP = cue('pattern');
    // columns: the automaton's at 330, the transition system's at 930, the Markov chain's at 1505 (moved in from
    // the storyboard's 960 and 1590 so that the widest table ends inside the right margin)
    const XS = [330, 930, 1505];
    const size = 34, pitch = 62, Y = 250;
    const chipW = 2 * Math.round(size * 0.52) + Math.round(size * 0.5), cw = charWidth(size);
    const wide = rows => chipW + Math.max(...rows.map(r => [...r[1]].length)) * cw;
    const specs = [[DFA, 'finite automaton', [4, 5]], [TS, 'transition system', []], [MC, 'markov chain', [4]]];
    const tabs = specs.map(([rows, name, acc], i) => {
      const x = XS[i] - wide(rows) / 2;
      BX.note(tl, root, XS[i], Y - 92, name, tP + 0.1 + i * 0.15, null);
      const t = new BX.Table(tl, root, x, Y, rows, { size, pitch, accepting: acc });
      t.show(tP + 0.2 + i * 0.15, { stagger: 0.06 });
      return t;
    });

    // "There is a set of states, and each state has a piece of data with states inside it. We call it the state's
    // successor structure."
    const tSt = cue('states'), tSu = cue('struct');
    for (const t of tabs) t.dim('all', 0.35, tSt - 0.15, { part: 'struct' });
    for (const t of tabs) for (const r of t.rows) r.chip.pulse(tSt + 0.6, { dur: 0.6 });
    for (const t of tabs) { t.light('all', tSu - 0.1, { part: 'struct' }); t.dim('all', 0.35, tSu - 0.1, { part: 'chip' }); }
    // "with states inside it": the state numbers in the structures
    for (const t of tabs) for (const r of t.rows) for (const i of r.s.ids('states')) r.s.pulse(i, tSu + 2.3, { dur: 0.6 });
    const lSucc = BX.note(tl, root, CX, 590, 'successor structure: data with states inside', tSu + 5.2, cue('kind') - 0.3);
    void lSucc;

    // "What differs is the shape of that data: a flag and two states; a set of states; a flag and a distribution."
    const tK = cue('kind');
    for (const t of tabs) t.light('all', tK - 0.1, { part: 'chip' });
    const SY = 630;
    ['a flag and two states', 'a set of states', 'a flag and a distribution'].forEach((s, i) => {
      const e = BX.cserif(root, XS[i], SY, s, 44);
      fadeIn(tl, e, cue('k' + (i + 1)) - 0.15, 0.6, 14);
    });

    // "These shapes are built from the same few pieces: flags, tuples, sets, distributions. That will matter later."
    // A row of piece chips (the same chips as in the chapter on kinds of machine), each at its word; they leave
    // before "functor".
    {
      const PY = 760, texts = ['flag', 'tuple', 'set', 'distribution'], ats = [24.2, 24.68, 25.56, 26.33], gap = 30;
      const lw = BX.labelW('THE SAME FEW PIECES', 32) + 40;
      const ws = texts.map(t => BX.labelW(t.toUpperCase(), 30) + 36);
      let x = CX - (lw + ws.reduce((p, q) => p + q, 0) + gap * 3) / 2;
      const out = cue('functor') - 0.4, l = lnote(tl, root, x, PY - 19, 'the same few pieces', 22.3, out);
      void l;
      x += lw;
      texts.forEach((t, i) => { const e = BX.piece(root, x, PY, t); fadeIn(tl, e, ats[i], 0.5, 8); fadeOut(tl, e, out, 0.3, -8); x += ws[i] + gap; });
    }

    // "The shape is the kind of machine. In category theory, such a shape is called a functor, and a machine of that
    // shape is called a co-algebra. That is the word in the title."
    const tFn = cue('functor');
    for (const t of tabs) t.dim('all', 0.45, tFn - 0.1);
    BX.note(tl, root, CX, SY - 52, 'the shape is the kind of machine', tFn + 0.2, null);
    const FY = 735;
    const fn = BX.cserif(root, 520, FY, 'functor', 64);
    fadeIn(tl, fn, tFn + 5.2, 0.7, 16);
    BX.note(tl, root, 520, FY + 86, 'a shape', tFn + 5.65, null);
    const tCo = cue('coalg');
    const co = BX.cserif(root, 1400, FY, 'coalgebra', 64);
    fadeIn(tl, co, tCo + 2.05, 0.7, 16);
    BX.note(tl, root, 1400, FY + 86, 'a machine of that shape', tCo + 2.5, null);
    // "We will not need more category theory than that.": nothing new
  });

  // ============================================ eq_a / eq_b ===================================================
  // the layout of both: the automaton left, its table right; eq_b starts from where eq_a ends
  const EQ = { cx: 460, cy: 500, scale: 1.15, TX: 940 };
  function eqLayout(tl, root) {
    const m = new BX.Machine(tl, root, { kind: 'dfa', cx: EQ.cx, cy: EQ.cy, scale: EQ.scale });
    const t = new BX.Table(tl, root, EQ.TX, 0, DFA, { size: 52, pitch: 92, cy: 500, accepting: [4, 5] });
    return { m, t };
  }
  const GUESS = [[[2, 3], 'X'], [[4, 5], 'Y'], [[1], 'Z']];
  const STABLE_Y = 846;

  scene('eq_a', ({ tl, root, cue, dur }) => {
    const { m, t } = eqLayout(tl, root);
    // "When are two states equivalent?"
    const tQ = cue('q');
    m.show(tQ - 0.25, { stagger: 0.1 });
    t.show(tQ + 0.2, { stagger: 0.1 });
    m.pulse([2, 3], tQ + 0.5, { dur: 0.7 });
    const p2 = m.pos(2), p3 = m.pos(3);
    const qm = BX.ctext(root, (p2.x + p3.x) / 2, p2.y + 100, '?', Object.assign(BX.SERIF(72), { color: C.dim }), 90);
    fadeIn(tl, qm, tQ + 0.75, 0.5, 10);

    // "They should have equivalent successor structures. But those contain states, so the definition seems to go
    // in a circle."
    const tC = cue('circ'), tG = cue('guess');
    fadeOut(tl, qm, tC - 0.2);
    const PY = 790;
    const ph1 = BX.cserif(root, 1000, PY, 'equivalent states', 40), ph2 = BX.cserif(root, 1560, PY, 'equivalent structures', 40);
    fadeIn(tl, ph1, tC - 0.15, 0.6, 12);
    fadeIn(tl, ph2, tC + 0.9, 0.6, 12);
    const svg = BX.svg(root);
    // the loop: over the top from the first phrase to the second, and back under them
    const aTop = BX.line(tl, svg, 1175, PY + 12, 1350, PY + 12, { bend: -30, head: 14 });
    const aBot = BX.line(tl, svg, 1350, PY + 40, 1175, PY + 40, { bend: -30, head: 14 });
    tl.to(aTop.path, { draw: 1 }, tC + 0.6, 0.6, E.io); tl.to(aTop.head, { o: 1 }, tC + 1.1, 0.15);
    tl.to(aBot.path, { draw: 1 }, tC + 3.8, 0.6, E.io); tl.to(aBot.head, { o: 1 }, tC + 4.3, 0.15);
    // "The way out is to start from a guess.": the loop leaves
    for (const e of [ph1, ph2]) fadeOut(tl, e, tG - 0.2);
    aTop.hide(tG - 0.2); aBot.hide(tG - 0.2);

    // "Group the states into blocks, and give each block a name."
    const tB = cue('blocks');
    const blocks = GUESS.map(([ss], i) => m.block(ss, '', tB + 0.3 + i * 0.3, { dur: 0.7 }));
    blocks.forEach((b, i) => b.rename(GUESS[i][1], tB + 2.0 + i * 0.25));

    // "Then, in every successor structure, replace each state by the name of its block."
    const tS = cue('subst');
    t.rows.forEach((r, i) => t.underline(r.k, 'states', C.bind, tS + 2.25 + i * 0.1));

    // "The guess is called stable if states in the same block end up with exactly the same structure."
    const lab = BX.note(tl, root, CX, STABLE_Y, 'stable: same block, same structure', cue('stable') + 1.5, null);
    // eq_b continues from this frame: everything stays but this label
    tl.to(lab, { o: 0 }, dur - 0.4, 0.4, E.in);
    return { keep: true };
  });

  scene('eq_b', ({ tl, root, cue }) => {
    // where eq_a left it: the drawing, the three outlines, the table with its underlines
    const { m, t } = eqLayout(tl, root);
    m.appear(0, { dur: 0 });
    for (const r of t.rows) { r.chip.show(0, { dur: 0, dy: 0 }); r.s.show(0, { stagger: 0, rise: 0, dur: 0 }); }
    const blocks = GUESS.map(([ss, name]) => {
      const b = m.block(ss, name);
      tl.set(b.path, { draw: 1 }, 0); tl.set(b.tabEl, { o: 1, s: 1 }, 0);
      return b;
    });
    const under = {};
    for (const r of t.rows) under[r.k] = t.underline(r.k, 'states', C.bind, 0, { dur: 0.001, stagger: 0 });
    const BXY = Object.fromEntries(GUESS.map(([ss, n]) => [n, ss]));
    const rename = (k, at) => {
      t.rename(k, BXY, at, { stagger: 0.18 });
      for (const u of under[k]) tl.to(u, { o: 0 }, at, 0.3);
    };
    const pulseTab = (b, at) => { tl.to(b.tabEl, { s: 1.3 }, at, 0.25, E.out); tl.to(b.tabEl, { s: 1 }, at + 0.25, 0.4, E.io); };

    // "Try it on the automaton, with the guess that states two and three are equivalent, and four and five."
    const tD = cue('d');
    blocks[0].pulse(tD + 3.0, { dur: 0.7 });
    blocks[1].pulse(tD + 5.35, { dur: 0.7 });

    // "Call the block of two and three X, the block of four and five Y, and state one, on its own, Z."
    const tN = cue('num');
    pulseTab(blocks[0], tN + 1.9);
    pulseTab(blocks[1], tN + 4.15);
    pulseTab(blocks[2], tN + 6.95);

    // "State two had: false, four, three. After renaming: false, Y, X."
    const tR2 = cue('r2');
    t.dim([1, 3, 4, 5], 0.35, tR2 - 0.15);
    m.pulse(2, tR2 + 0.1);
    t.pulse(2, tR2 + 1.2, { dur: 0.6 });
    rename(2, cue('r2') + 3.3);

    // "State three had: false, five, three. After renaming: also false, Y, X."
    const tR3 = cue('r3');
    t.light(3, tR3 - 0.15);
    m.pulse(3, tR3 + 0.1);
    t.pulse(3, tR3 + 1.2, { dur: 0.6 });
    rename(3, tR3 + 3.3);

    // "They agree."
    const EQX = t.structX + t.struct(2).width + 30;
    t.equal(2, 3, cue('ok') - 0.15, { x: EQX });

    // "So do four and five."
    const tR45 = cue('r45');
    t.light([4, 5], tR45 - 0.15);
    rename(4, tR45 + 0.2); rename(5, tR45 + 0.2);
    t.equal(4, 5, tR45 + 0.9, { x: EQX });
    rename(1, tR45 + 1.3);

    // "The guess is stable."
    const tSt = cue('st');
    t.light(1, tSt - 0.15);
    BX.note(tl, root, CX, STABLE_Y, 'stable', tSt + 0.4, null, { color: C.good });
  });
})();

// ==== src/scenes/c.js ====
// The other machines, the definition, the simple algorithm (SCENES.md, "c.js"): eq_c, eq_d, cool_one, naive_a,
// naive_b, naive_c. Built with BX (common.js). Times in the comments are the words of the narration they belong to.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const { CX } = BX;

  // a label (small caps) that rises in at `at` and leaves at `out`
  const note = (tl, root, x, y, text, at, out, o) => BX.note(tl, root, x, y, text, at, out, o);

  // ============================================ eq_c ==========================================================
  scene('eq_c', ({ tl, root, cue }) => {
    // ---- the transition system
    const TS = [[1, '{2, 3, 4}'], [2, '{1, 4}'], [3, '{3, 4, 5}'], [4, '{4, 5}'], [5, '{ }']];
    const MAP_TS = { X: [1, 2], Y: [3, 4], Z: [5] };
    const m = new BX.Machine(tl, root, { kind: 'ts', cx: 460, cy: 500, scale: 1.15 });
    m.show(cue('ts') - 0.2, { stagger: 0.07 });
    const t = new BX.Table(tl, root, 940, 0, TS, { size: 52, pitch: 92, cy: 500 });
    t.show(cue('ts') + 1.7, { stagger: 0.12 });

    // "guess that one and two are equivalent, and three and four, with five on its own"
    m.block([1, 2], 'X', cue('t12') + 2.3);
    m.block([3, 4], 'Y', cue('t12') + 4.4);
    m.block([5], 'Z', cue('t12') + 5.8);

    // "State one steps to two, three, and four. After renaming, that is: X, Y, Y."
    t.dim([3, 4, 5], 0.35, cue('s1') - 0.1);
    t.pulse(1, cue('s1') + 0.15); m.pulse(1, cue('s1') + 0.15);
    t.rename(1, MAP_TS, cue('s1') + 5.25, { stagger: 0.52 });
    // "But this is a set, and a set does not hold duplicates. It is just X and Y."
    const nSet = note(tl, root, t.structX, 222, 'a set holds no duplicates', cue('dup') + 1.6, cue('mc') - 0.4, { align: 'left' });
    t.merge(1, '{X, Y}', cue('dup') + 3.95);
    // "State two steps to one and four: X and Y again. They agree."
    t.pulse(2, cue('s2') + 0.15); m.pulse(2, cue('s2') + 0.15);
    t.rename(2, MAP_TS, cue('s2') + 2.5, { stagger: 0.45 });
    t.equal(1, 2, cue('s2') + 4.15);
    void nSet;

    // ---- the Markov chain
    const tMc = cue('mc');
    m.hide(tMc - 0.4); t.hide(tMc - 0.4);
    const MC = [[1, '(false, {2: ⅓, 3: ⅔})'], [2, '(false, {2: ½, 4: ½})'], [3, '(false, {2: ¼, 4: ½, 5: ¼})'], [4, '(true, {4: 1})'], [5, '(false, {3: ½, 4: ½})']];
    const MAP_MC = { X: [2, 3, 5], Y: [4], Z: [1] };
    const mc = new BX.Machine(tl, root, { kind: 'mc', cx: 460, cy: 500, scale: 1.15 });
    mc.show(tMc + 0.05, { stagger: 0.06 });
    const u = new BX.Table(tl, root, 900, 0, MC, { size: 44, pitch: 88, cy: 500, accepting: [4] });
    u.show(tMc + 1.3, { stagger: 0.1 });
    // "guess that two, three, and five are equivalent, and call their block X"
    mc.block([2, 3, 5], 'X', tMc + 2.8, { dur: 0.8, groups: [[2, 3], [3, 5]] });   // it bends around state 4
    mc.block([4], 'Y', tMc + 4.0);
    mc.block([1], 'Z', tMc + 4.2);

    // "State three goes to state two with probability one quarter, to state five with one quarter, and to state
    // four with one half."
    const tM3 = cue('m3');
    u.dim([1, 2, 4, 5], 0.35, tM3 - 0.1);
    mc.focus([3], tM3 - 0.1, { o: 0.3 });
    const s3 = u.struct(3);
    // parts of (false, {2: ¼, 4: ½, 5: ¼}): 4-6 is "2: ¼", 8-10 "4: ½", 12-14 "5: ¼"
    const ent = [[[4, 5, 6], ['3>2', 2], tM3 + 1.5], [[12, 13, 14], ['3>5', 5], tM3 + 4.3], [[8, 9, 10], ['3>4', 4], tM3 + 6.6]];
    ent.forEach(([ps, sel, at], i) => {
      mc.light(sel, at);
      s3.mark(ps, C.dim, at, { fill: 0.1, out: i < 2 ? ent[i + 1][2] - 0.1 : tM3 + 7.9 });
    });
    u.rename(3, MAP_MC, tM3 + 8.0);
    // "Two and five are both in X, so their probabilities are added: one half to X."
    const tAdd = cue('add') + 3.35;
    u.merge(3, '(false, {X: ½, Y: ½})', tAdd, { dur: 0.8 });
    note(tl, root, u.structX, 236, 'probabilities add', cue('add') + 3.5, cue('norm') - 0.3, { align: 'left' });
    // "State two goes to itself and to four, one half each: the same."
    const tM2 = cue('m2');
    u.light(2, tM2 - 0.1);
    mc.focus([2, '2>2', '2>4', 4], tM2 - 0.1, { o: 0.3 });
    u.pulse(2, tM2 + 0.2);
    u.rename(2, MAP_MC, tM2 + 2.1);
    u.equal(2, 3, tM2 + 3.9);
    // "So renaming is followed by tidying up"
    mc.light('all', cue('norm') - 0.1);
    note(tl, root, CX, 820, 'rename, then tidy up', cue('norm') + 1.5, null, { color: C.ink });
  });

  // ============================================ eq_d ==========================================================
  scene('eq_d', ({ tl, root, cue }) => {
    const svg = BX.svg(root);
    // ---- "This renaming, with its tidying up, is essentially all we will ask of a kind of machine."
    const Y0 = 300, cw = charWidth(60), AW = 240, G = 44;
    const x0 = CX - (15 * cw + AW + 2 * G) / 2;
    const a = new BX.Struct(tl, root, x0, Y0, '{2, 3, 4}', { size: 60 });
    const b = new BX.Struct(tl, root, x0 + 9 * cw + AW + 2 * G, Y0, '{X, Y}', { size: 60 });
    const ax1 = x0 + 9 * cw + G, ax2 = ax1 + AW;
    const t0 = cue('only'), tOut = cue('best') - 0.35;
    a.show(t0 - 0.1);
    const arr = BX.line(tl, svg, ax1, Y0, ax2, Y0, { at: t0 + 0.6, dur: 0.6 });
    const lArr = note(tl, root, (ax1 + ax2) / 2, Y0 - 82, 'rename, tidy up', t0 + 1.0, tOut);
    b.show(t0 + 1.7);
    const lAll = note(tl, root, CX, Y0 + 70, 'essentially all that a kind of machine must provide', t0 + 3.4, tOut);
    a.hide(tOut); b.hide(tOut); arr.hide(tOut);
    void lArr; void lAll;

    // ---- three guesses for the automaton
    const R = 30, IN = 92, BETWEEN = 132, LX = 800;
    const tB = cue('best');
    const rows = [
      { y: 250, groups: [[1], [2], [3], [4], [5]], label: '5 blocks · stable', at: tB - 0.1 },
      { y: 420, groups: [[1], [2, 3], [4, 5]], label: '3 blocks · stable', at: tB + 0.5 },
      { y: 610, groups: [[1, 2, 3], [4, 5]], label: '2 blocks · not stable', at: tB + 1.1 },
    ].map(r => {
      const g = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
      let x = 200 - IN; const chips = [], blocks = [];
      r.groups.forEach((grp, gi) => {
        const cs = grp.map((k, i) => { x += (i === 0 && gi > 0) ? BETWEEN : IN; return new BX.Chip(tl, g, x, r.y, String(k), { r: R, accepting: k >= 4 }); });
        chips.push(...cs);
        blocks.push(new BX.Block(tl, g, cs.map(c => c.circle()), '', { pad: 14 }));
      });
      chips.forEach((c, i) => c.show(r.at + i * 0.05));
      blocks.forEach((bl, i) => bl.show(r.at + 0.2 + i * 0.06, { dur: 0.5 }));
      const ln = BX.lline(g, LX, r.y - 20, [[r.label, null], ['  ·  ', null], ['the fewest blocks', C.good]], BX.LABEL(32));
      ln.parts.slice(1).forEach(e => tl.set(e, { o: 0 }, 0));
      const lab = ln.root;
      fadeIn(tl, lab, r.at + 0.35, 0.5, 10);
      return Object.assign(r, { g, chips, blocks, lab, parts: ln.parts, x0: 200 - R, x1: x + R });
    });
    // row 3 is not stable: the neutral grey strike through it
    const r3 = rows[2], tS = tB + 1.75;
    const sl = box(r3.g, r3.x0 - 24, r3.y - 2, { width: (r3.x1 - r3.x0 + 48) + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
    tl.set(sl, { sx: 0, o: 0 }, 0); tl.set(sl, { o: 1 }, tS); tl.to(sl, { sx: 1 }, tS, 0.45, E.io);
    r3.chips.forEach(c => c.dim(0.45, tS, 0.45)); r3.blocks.forEach(bl => bl.dim(0.45, tS, 0.45));
    BX.strikeEl(tl, r3.parts[0], tS + 0.1);
    // "there is one with the fewest blocks": row 2 is marked green
    const r2 = rows[1], tF = tB + 2.55;
    const gm = box(r2.g, r2.x0 - 30, r2.y - R - 26, { width: (r2.x1 - r2.x0 + 60) + 'px', height: (2 * R + 52) + 'px', borderRadius: '30px', background: alpha(C.good, 0.08), boxShadow: `inset 0 0 0 2px ${alpha(C.good, 0.5)}` });
    r2.g.insertBefore(gm, r2.g.firstChild);
    tl.set(gm, { o: 0 }, 0); tl.to(gm, { o: 1 }, tF, 0.5);
    r2.parts.slice(1).forEach(e => fadeIn(tl, e, tF + 0.15, 0.5, 0));
    // "Its blocks are the classes of equivalent states."
    note(tl, r2.g, 200 - R - 30, r2.y + R + 48, 'its blocks: the equivalent states', cue('name') + 0.3, null, { align: 'left' });
    // "For transition systems, this equivalence is known as bisimilarity"
    const tBi = cue('bisim');
    for (const r of [rows[0], rows[2]]) tl.to(r.g, { o: 0 }, tBi - 0.3, 0.35, E.in);
    fadeOut(tl, r2.lab, tBi - 0.3, 0.3);
    const RX = 1150;
    const word = box(root, RX, 280, Object.assign(BX.SERIF(72), { whiteSpace: 'pre' }), 'bisimilarity');
    fadeIn(tl, word, tBi + 3.1, 0.7, 18);
    // (the label comes with the word, so that it never stands under an empty place)
    note(tl, root, RX, 382, 'for transition systems', tBi + 3.4, null, { align: 'left' });
    // "For finite automata, it says that two states accept the same language."
    note(tl, root, RX, 450, 'for finite automata:', cue('lang') + 0.2, null, { align: 'left' });
    note(tl, root, RX, 492, 'the same language', cue('lang') + 3.3, null, { align: 'left' });
    // "And the minimized machine has one state for each block."
    const tMin = cue('min');
    const MIN = [[1, '(false, 2, 2)', false], [2, '(false, 4, 2)', false], [4, '(true, 4, 4)', true]];
    const c44 = charWidth(44), chipR = Math.round(44 * 0.52), gap = 22, sep = 72;
    const wid = MIN.map(([, s]) => 2 * chipR + gap + s.length * c44);
    let mx = CX - (wid.reduce((p, q) => p + q, 0) + sep * 2) / 2;
    MIN.forEach(([k, s, acc], i) => {
      const tb = new BX.Table(tl, root, mx, 690, [[k, s]], { size: 44, accepting: acc ? [k] : [] });
      tb.show(tMin + 0.3 + i * 0.35);
      mx += wid[i] + sep;
    });
    note(tl, root, CX, 748, 'the minimized automaton: one state for each block', tMin + 1.6, null);
  });

  // ============================================ cool_one ======================================================
  scene('cool_one', ({ tl, root, cue }) => {
    const svg = BX.svg(root);
    // (the outer columns sit a little further in than 330 and 1590: the longest phrase would cross the margin)
    const XS = [380, 960, 1540], Y = 300;
    const tD = cue('diff');
    // "Language equivalence, bisimilarity, and bisimilarity with probabilities are usually defined separately."
    [['language equivalence', 'finite automata', 0], ['bisimilarity', 'transition systems', 1.3], ['probabilistic bisimilarity', 'markov chains', 2.65]].forEach(([p, l, d], i) => {
      const e = BX.cserif(root, XS[i], Y, p, 48);
      fadeIn(tl, e, tD + d - 0.15, 0.7, 16);
      note(tl, root, XS[i], Y + 72, l, tD + d + 0.3, null);
    });
    // "Here they are one definition, seen in three different shapes."
    const tS = cue('same'), PY = 640;
    XS.forEach((x, i) => {
      const ln = BX.line(tl, svg, x, Y + 128, CX + (x - CX) * 0.04, PY - 18, { head: 0, stroke: C.dim, width: 2.5 });
      tl.to(ln.path, { draw: 1 }, tS - 0.1 + i * 0.1, 0.7, E.io);
    });
    const ph = BX.cserif(root, CX, PY, 'stable under renaming', 64);
    fadeIn(tl, ph, tS + 0.7, 0.7, 16);
    note(tl, root, CX, PY + 94, 'one definition', tS + 1.1, null);
  });

  // ============================================ the simple algorithm ==========================================
  // One layout for naive_a, naive_b and naive_c: the automaton left, the table of signatures right, the counter
  // top right. naive_b and naive_c rebuild it as the scene before ended, visible from their first frame.
  const R1 = ['(false, X, X)', '(false, X, X)', '(false, X, X)', '(true, X, X)', '(true, X, X)'];
  const R2 = ['(false, X, X)', '(false, Y, X)', '(false, Y, X)', '(true, Y, Y)', '(true, Y, Y)'];
  function naive(tl, root, sigs) {
    const m = new BX.Machine(tl, root, { kind: 'dfa', cx: 440, cy: 500, scale: 1.15 });
    const t = new BX.Table(tl, root, 900, 0, [1, 2, 3, 4, 5].map((k, i) => [k, sigs ? sigs[i] : '']), { size: 52, pitch: 92, cy: 540, accepting: [4, 5] });
    const n = new BX.Counter(tl, root, 1810, 160, 'signatures computed', { align: 'right' });
    return { m, t, n };
  }
  // everything of the layout visible at once, from t = 0
  function continued(tl, { m, t, n }, blocks, count) {
    m.appear(0, { dur: 0 });
    for (const r of t.rows) { r.chip.show(0, { dur: 0, dy: 0 }); for (const p of r.s.parts) tl.set(p.el, { o: 1, y: 0 }, 0); }
    tl.set(n.el, { o: 1, y: 0 }, 0); n.set(count, -1);
    return blocks.map(([ss, name]) => {
      const b = m.block(ss, name);
      tl.set(b.path, { draw: 1 }, 0);
      if (b.tabEl) tl.set(b.tabEl, { o: 1, s: 1 }, 0);
      return b;
    });
  }

  // ============================================ naive_a =======================================================
  scene('naive_a', ({ tl, root, cue }) => {
    const L = naive(tl, root), { m, t, n } = L;
    // "How do we find the best stable guess?"
    m.show(cue('how') - 0.25, { stagger: 0.1 });
    // "Start by being optimistic: put all states in one block, X."
    const bAll = m.block([1, 2, 3, 4, 5], 'X', cue('opt') + 2.4, { dur: 0.8 });
    // "Compute every state's structure, renamed by block. From here on we call that the state's signature."
    const tSig = cue('sig');
    t.rows.forEach((r, i) => r.chip.show(tSig + 0.1 + i * 0.1));
    const l1 = note(tl, root, t.structX, 222, 'signature:', tSig + 6.4, cue('two') - 0.3, { align: 'left' });
    const l2 = note(tl, root, t.structX, 264, 'the structure, renamed by block', tSig + 6.6, cue('two') - 0.3, { align: 'left' });
    void l1; void l2;
    // "In the automaton, every signature now reads: a flag, then X, X."
    const tR = cue('r1');
    n.show(tR - 0.1);
    R1.forEach((s, i) => { t.set(i + 1, s, tR + 0.2 + i * 0.55); n.set(i + 1, tR + 0.35 + i * 0.55); });
    // "Three states say false, and two say true."
    const tS = cue('split1'), tOut = cue('two') + 0.3;
    [1, 2, 3].forEach((k, i) => t.mark(k, tS + 2.55 + i * 0.1, { part: 'false', out: tOut }));
    [4, 5].forEach((k, i) => t.mark(k, tS + 4.05 + i * 0.1, { part: 'true', out: tOut }));
    // "Split the block in two: the false ones stay X, and the true ones become Y."
    const [, bY] = bAll.split(cue('two') + 0.5, [[[1, 2, 3], 'X'], [[4, 5], '']]);
    bY.rename('Y', cue('two') + 4.3);
    return { keep: true };
  });

  // ============================================ naive_b =======================================================
  scene('naive_b', ({ tl, root, cue, dur }) => {
    const L = naive(tl, root, R1), { m, t, n } = L;
    const [bX, bY] = continued(tl, L, [[[1, 2, 3], 'X'], [[4, 5], 'Y']], 5);
    // "Now do it again, with the new blocks."
    t.fade('all', 0.3, cue('again') + 0.1);
    // a row's new signature replaces its faint one
    const sig = (k, s, at) => { t.set(k, s, at); tl.to(t.struct(k).root, { o: 1 }, at + 0.2, 0.3); };
    let c = 5;
    const count = at => n.set(++c, at + 0.15);
    // "State one reads: false, X, X."
    sig(1, R2[0], cue('r2') + 1.3); count(cue('r2') + 1.3);
    // "States two and three read: false, Y, X."
    [2, 3].forEach((k, i) => { sig(k, R2[k - 1], cue('r23') + 1.7 + i * 0.15); count(cue('r23') + 1.7 + i * 0.15); });
    // "Four and five read: true, Y, Y."
    [4, 5].forEach((k, i) => { sig(k, R2[k - 1], cue('r45') + 1.3 + i * 0.15); count(cue('r45') + 1.3 + i * 0.15); });
    // "Three different signatures, so three blocks. State one gets a new name, Z."
    const tT = cue('three');
    const [bX2, bZ] = bX.split(tT + 2.2, [[[2, 3], 'X'], [[1], '']]);
    bZ.rename('Z', tT + 5.2);
    const p1 = m.pos(1);
    note(tl, root, p1.x + m.r + 44, p1.y - 22, 'new name', tT + 4.4, cue('once') - 0.2, { align: 'left' });
    // "Once more. This time every signature is the same as before, so no block splits."
    t.fade('all', 0.3, cue('once') + 0.05);
    const tR3 = cue('r3');
    R2.forEach((s, i) => { sig(i + 1, s, tR3 + 0.45 + i * 0.3); count(tR3 + 0.45 + i * 0.3); });
    note(tl, root, 900, 772, 'the same as before', tR3 + 1.8, cue('done') - 0.2, { align: 'left' });
    [bX2, bY, bZ].forEach((b, i) => b.pulse(tR3 + 3.1 + i * 0.18));
    // "The guess is stable. And because we only ever separated states that had to be separated, it is the best one."
    // (they leave before the cut, so that naive_c begins with the picture alone)
    const tD = cue('done');
    note(tl, root, CX, 790, 'stable', tD + 0.4, dur - 0.5, { color: C.good, size: 40 });
    note(tl, root, CX, 850, 'only split when forced: the fewest blocks', tD + 2.3, dur - 0.5);
    return { keep: true };
  });

  // ============================================ naive_c =======================================================
  scene('naive_c', ({ tl, root, cue }) => {
    const L = naive(tl, root, R2), { m, t, n } = L;
    continued(tl, L, [[[2, 3], 'X'], [[4, 5], 'Y'], [[1], 'Z']], 15);
    // naive_b's last labels leave as it ends: STABLE and the line under it are gone here
    // "Nothing here was special to automata. The loop only computes signatures and compares them."
    m.to({ o: 0.4 }, cue('general') + 0.1, 0.5, E.out); t.to({ o: 0.4 }, cue('general') + 0.1, 0.5, E.out);
    // "But look at the cost."
    n.pulse(cue('cost') + 0.5, 0.8);
    // "Every round recomputes the signature of every state, even when it cannot have changed."
    const tE = cue('every');
    m.hide(tE - 0.3); t.hide(tE - 0.3);
    const grid = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const SQ = 70, SG = 18, GX = 880, GY = [330, 440, 550], LXG = 640;
    const sq = [];
    GY.forEach((y, r) => {
      const lab = box(grid, LXG, y - 20, Object.assign(BX.LABEL(32), { whiteSpace: 'pre' }), 'round ' + (r + 1));
      fadeIn(tl, lab, tE + 0.1 + r * 1.0, 0.4, 8);
      for (let k = 0; k < 5; k++) {
        const s = box(grid, GX + k * (SQ + SG), y - SQ / 2, { width: SQ + 'px', height: SQ + 'px', borderRadius: '10px', background: alpha(C.ink, 0.1), boxShadow: `inset 0 0 0 3px ${C.ink}` });
        fadeIn(tl, s, tE + 0.15 + (r * 5 + k) * 0.2, 0.35, 10);
        sq.push(s);
      }
    });
    const tM = cue('most');
    [5, 10, 11, 12, 13, 14].forEach((i, j) => tl.to(sq[i], { o: 0.22 }, tM + 0.3 + j * 0.08, 0.4));
    note(tl, grid, CX, 610, 'nothing had changed', tM + 0.8, null);
    // "And there can be many rounds. In a machine shaped like a long chain, each round splits off a single state."
    const tC = cue('chain');
    tl.to(grid, { o: 0 }, tC - 0.25, 0.35, E.in); n.hide(tC - 0.25);
    const svg = BX.svg(root);
    const CR = 38, CY = 420, X0 = 330, STEP = 180;
    const chips = [1, 2, 3, 4, 5, 6, 7, 8].map((k, i) => new BX.Chip(tl, root, X0 + i * STEP, CY, String(k), { r: CR, size: 36 }));
    chips.forEach((ch, i) => ch.show(tC + 0.25 + i * 0.1, { draw: true }));
    for (let i = 0; i < 7; i++) BX.line(tl, svg, X0 + i * STEP + CR + 8, CY, X0 + (i + 1) * STEP - CR - 8, CY, { at: tC + 0.6 + i * 0.1, dur: 0.4 });
    let blk = new BX.Block(tl, root, chips.map(c => c.circle()), 'X', { at: tC + 1.6, pad: 16, tab: 'nw', dur: 0.8 });
    note(tl, root, CX, CY + 82, 'a long chain: one state splits off each round', tC + 3.6, null);
    // the counter appears with the first split, reading 1
    const rc = new BX.Counter(tl, root, 1810, 250, 'round', { align: 'right', value: 1 });
    const tSp = tC + 4.4;
    rc.show(tSp);
    for (let j = 0; j < 7; j++) {
      const at = tSp + j * 0.55, k = 7 - j;   // the last state still inside: chips[k]
      const parts = blk.split(at, [[chips.slice(0, k).map(c => c.circle()), 'X'], [[chips[k].circle()], '']]);
      blk = parts[0];
      if (j > 0) rc.set(j + 1, at + 0.1);
    }
    // "With N states, that is N rounds of N signatures: N squared."
    const tQ = cue('sq');
    const eq = BX.cline(root, CX, 590, [['N rounds', null], [' × N signatures', null], [' = N²', null]], Object.assign(BX.MONO(64), { color: C.ink }));
    [[0, 1.65], [1, 2.75], [2, 4.0]].forEach(([i, d]) => { tl.set(eq.parts[i], { o: 0 }, 0); fadeIn(tl, eq.parts[i], tQ + d, 0.5, 12); });
    // "For a million states, a million million."
    const tMi = cue('million'), c48 = charWidth(48), AW = 110, G = 34;
    const A = 'N = 1 000 000', B = '1 000 000 000 000 signatures';
    const lx = CX - ((A.length + B.length) * c48 + AW + 2 * G) / 2, my = 740;
    const ea = box(root, lx, my - 31, Object.assign(BX.MONO(48), { color: C.ink, whiteSpace: 'pre' }), A);
    const eb = box(root, lx + A.length * c48 + AW + 2 * G, my - 31, Object.assign(BX.MONO(48), { color: C.ink, whiteSpace: 'pre' }), B);
    fadeIn(tl, ea, tMi + 0.1, 0.5, 12);
    BX.line(tl, svg, lx + A.length * c48 + G, my, lx + A.length * c48 + G + AW, my, { at: tMi + 1.0, dur: 0.45 });
    fadeIn(tl, eb, tMi + 1.35, 0.6, 12);
  });
})();

// ==== src/scenes/d.js ====
// Two ideas (idea_dirty, idea_name, trick, algo) of the Boa video, built with BX (common.js).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const { CX, RAIL } = BX;

  // ---- local helpers ---------------------------------------------------------------------------------------------
  // a full-stage group, so that a whole picture can be faded or moved at once
  const group = root => box(root, 0, 0, { width: W + 'px', height: H + 'px' });

  // the number of an idea on the rail (serif 64) and its label beside it
  function ideaHead(tl, root, num, text, at) {
    const n = box(root, RAIL, 170, Object.assign(BX.SERIF(64), { whiteSpace: 'pre', lineHeight: '78px' }), num);
    const l = box(root, RAIL + 72, 190, Object.assign(BX.LABEL(32), { color: C.ink, whiteSpace: 'pre', lineHeight: '38px' }), text);
    fadeIn(tl, n, at, 0.6, 14); fadeIn(tl, l, at + 0.15, 0.6, 14);
    return [n, l];
  }

  // a straight arrow between two circles {x, y}; its end can travel to a second place (b2) with the key `u`, and
  // it is drawn with the key `draw`
  function liveArrow(tl, svg, a, b, { b2 = null, ra = 44, rb = 34, stroke = C.ink, width = 3, head = 14 } = {}) {
    const p = el(svg, 'path');
    p.setAttribute('fill', 'none'); p.setAttribute('stroke-width', width); p.setAttribute('stroke-linecap', 'round');
    p.style.stroke = stroke;
    const h = el(svg, 'path');
    h.setAttribute('d', `M ${-head} ${-head * 0.55} L 0 0 L ${-head} ${head * 0.55}`);
    h.setAttribute('fill', 'none'); h.setAttribute('stroke-width', width); h.setAttribute('stroke-linecap', 'round'); h.setAttribute('stroke-linejoin', 'round');
    h.style.stroke = stroke;
    const st = { draw: 0, u: 0 };
    const redraw = () => {
      const bx = b.x + (b2 ? (b2.x - b.x) * st.u : 0), by = b.y + (b2 ? (b2.y - b.y) * st.u : 0);
      const dx = bx - a.x, dy = by - a.y, L = Math.hypot(dx, dy) || 1, ux = dx / L, uy = dy / L;
      const sx = a.x + ux * ra, sy = a.y + uy * ra, ex = bx - ux * rb, ey = by - uy * rb;
      const qx = sx + (ex - sx) * st.draw, qy = sy + (ey - sy) * st.draw;
      p.setAttribute('d', `M ${sx.toFixed(1)} ${sy.toFixed(1)} L ${qx.toFixed(1)} ${qy.toFixed(1)}`);
      p.style.strokeOpacity = st.draw <= 0.002 ? 0 : 1;
      h.setAttribute('transform', `translate(${ex.toFixed(1)} ${ey.toFixed(1)}) rotate(${(Math.atan2(uy, ux) * 180 / Math.PI).toFixed(2)})`);
    };
    tl.custom(p, 'draw', (e, v) => { st.draw = v; redraw(); }, 0);
    tl.custom(p, 'u', (e, v) => { st.u = v; redraw(); }, 0);
    tl.set(p, { draw: 0 }, 0); tl.set(h, { o: 0 }, 0);
    redraw();
    return {
      path: p, head: h,
      draw(at, dur = 0.5) { tl.to(p, { draw: 1 }, at, dur, E.io); tl.to(h, { o: 1 }, at + dur * 0.75, dur * 0.25); return this; },
      color(col, at, dur = 0.35) { tl.to(p, { stroke: col }, at, dur); tl.to(h, { stroke: col }, at, dur); return this; },
      travel(at, dur = 0.8) { tl.to(p, { u: 1 }, at, dur, E.io); return this; },
    };
  }

  // a small caps label whose right edge is at x, vertically centred on cy
  function rlabel(root, x, cy, text, col = C.dim, size = 32) {
    return box(root, x - 900, cy - size * 0.6, Object.assign(BX.LABEL(size), { color: col, width: '900px', textAlign: 'right', whiteSpace: 'pre' }), text);
  }

  // ============================================ idea_dirty ====================================================
  scene('idea_dirty', ({ tl, root, cue }) => {
    // "The first idea: do not recompute what cannot have changed."
    ideaHead(tl, root, '1', 'do not recompute what cannot have changed', cue('first') - 0.2);

    // "A state's signature depends only on the blocks of its successors."
    const pic = group(root), svg = BX.svg(pic);
    const tWhen = cue('when');
    const S = { x: 520, y: 560 }, T = { x: 420, y: 360 };
    const A = { x: 1100, y: 420 }, A2 = { x: 1220, y: 420 };
    const B = { x: 1100, y: 640 }, B2 = { x: 1220, y: 640 }, BZ = { x: 1100, y: 815 };
    const s = new BX.Chip(tl, pic, S.x, S.y, 's', { r: 40, size: 40, italic: true });
    s.show(tWhen - 0.2, { draw: true });
    const ca = new BX.Chip(tl, pic, A.x, A.y, '', { r: 32 }), ca2 = new BX.Chip(tl, pic, A2.x, A2.y, '', { r: 32 });
    const cb = new BX.Chip(tl, pic, B.x, B.y, '', { r: 32 }), cb2 = new BX.Chip(tl, pic, B2.x, B2.y, '', { r: 32 });
    const tSucc = tWhen + 0.9;   // "depends"
    ca.show(tSucc - 0.2); cb.show(tSucc - 0.1);
    const sa = liveArrow(tl, svg, S, A, { ra: 46, rb: 38 }).draw(tSucc, 0.5);
    const sb = liveArrow(tl, svg, S, B, { b2: BZ, ra: 46, rb: 38 }).draw(tSucc + 0.1, 0.5);
    // "the blocks of its successors": the outlines (each block holds one more state)
    const tBlocks = tWhen + 2.2;
    ca2.show(tBlocks - 0.25); cb2.show(tBlocks - 0.2);
    const bX = new BX.Block(tl, pic, [ca.circle(), ca2.circle()], 'X', { at: tBlocks, tab: 'e' });
    const bY = new BX.Block(tl, pic, [cb.circle(), cb2.circle()], 'Y', { at: tBlocks + 0.1, tab: 'e' });
    // beside s, its signature
    const sig = new BX.Struct(tl, pic, S.x, S.y + 92, '(…, X, Y)', { size: 48, align: 'center' });
    sig.show(tWhen + 3.1, { stagger: 0.05 });

    // "So it can change only when one of its successors moves to a different block."
    const tMove = cue('so') + 2.85;   // "moves"
    sb.color(C.pat, tMove - 0.25);
    cb.move(BZ.x - B.x, BZ.y - B.y, tMove, 0.9);
    sb.travel(tMove, 0.9);
    const bZ = new BX.Block(tl, pic, [{ x: BZ.x, y: BZ.y, r: 32 }], 'Z', { at: tMove + 0.85, tab: 'e' });
    bY.pulse(tMove - 0.1);

    // "Call a state dirty when that has happened, and clean once its signature has been computed again."
    const tD = cue('dirty');
    s.dirty(tD + 0.75);
    const dl = rlabel(pic, S.x - 66, S.y, 'dirty', C.pat);
    fadeIn(tl, dl, tD + 0.85, 0.5, 8);
    sig.dim('all', 0.3, tD + 1.1);
    // a second state t, pointing only into X, which did not move
    const t = new BX.Chip(tl, pic, T.x, T.y, 't', { r: 40, size: 40, italic: true });
    const tClean = tD + 2.85;   // "clean"
    t.show(tClean - 0.3, { draw: true });
    liveArrow(tl, svg, T, A, { ra: 46, rb: 38 }).draw(tClean - 0.05, 0.5);
    const cl = rlabel(pic, T.x - 66, T.y, 'clean');
    fadeIn(tl, cl, tClean + 0.2, 0.5, 8);

    // "Only dirty states need a new signature."
    const tOnly = cue('only');
    const tag = box(pic, S.x - 190, S.y + 140, Object.assign(BX.LABEL(32), { color: C.pat, width: '380px', height: '50px', lineHeight: '50px', textAlign: 'center', borderRadius: '10px', boxShadow: `inset 0 0 0 2.5px ${C.pat}`, background: C.bg, whiteSpace: 'pre' }), 'compute again');
    fadeIn(tl, tag, tOnly + 0.3, 0.5, 10);

    // "And the clean states of a block all share one signature ... So computing it for one of them is enough."
    const tC = cue('clean');
    tl.to(pic, { o: 0 }, tC - 0.35, 0.4, E.in);
    const blk = group(root), bsvg = BX.svg(blk);
    const XS = [0, 1, 2, 3, 4, 5].map(i => 685 + i * 110), CY = 580;
    const chips = XS.map(x => new BX.Chip(tl, blk, x, CY, '', { r: 34 }));
    chips.forEach((c, i) => c.show(tC + 0.2 + i * 0.06));
    new BX.Block(tl, blk, chips.map(c => c.circle()), 'X', { at: tC + 0.3, tab: 'sw' });
    chips[4].dirty(tC + 0.9); chips[5].dirty(tC + 0.95);
    // "share one signature": a bracket over the four clean ones, up to one signature
    const tShare = tC + 1.85;
    BX.bracket(tl, bsvg, XS[0] - 34, XS[3] + 34, 500, { at: tShare, legs: 'down', depth: 18, notch: 52 });
    const mid = (XS[0] + XS[3]) / 2;
    const sbox = BX.cell(blk, mid - 85, 372, 170, 76, '(…)', { font: BX.MONO(44) });
    fadeIn(tl, sbox, tShare + 0.4, 0.5, 10);
    BX.note(tl, blk, mid, 296, 'one signature for all the clean states', tShare + 0.8, null, { color: C.good });
    // "computing it for one of them is enough"
    const tOne = cue('clean') + 9.85;
    const c1 = chips[1];
    const ring = BX.dpath(tl, bsvg, BX.circleD(c1.x, c1.y, c1.r + 18), { stroke: C.dim, width: 3 });
    tl.to(ring, { draw: 1 }, tOne - 0.1, 0.5, E.io);
    BX.note(tl, blk, c1.x, CY + 70, 'one is enough', tOne + 0.4, null);
  });

  // ============================================ idea_name =====================================================
  scene('idea_name', ({ tl, root, cue }) => {
    // "The second idea is about names."
    ideaHead(tl, root, '2', 'the largest part keeps the name', cue('second') - 0.2);

    // "When a block splits, one part can keep the old name, and the others get new names. We are free to choose which."
    const tF = cue('free'), CY = 480, R = 32;
    const base = [...Array(9).keys()].map(i => 960 + (i - 4) * 96);
    const part = i => (i < 5 ? 0 : i < 8 ? 1 : 2), DX = [-70, 0, 70];
    const chips = base.map(x => new BX.Chip(tl, root, x, CY, '', { r: R }));
    chips.forEach((c, i) => c.show(tF - 0.25 + i * 0.04));
    const b9 = new BX.Block(tl, root, chips.map(c => c.circle()), 'X', { at: tF - 0.05, tab: 's' });
    const tOpen = tF + 0.55;   // "splits"
    chips.forEach((c, i) => { if (DX[part(i)]) c.move(DX[part(i)], 0, tOpen, 0.55); });
    const after = i => ({ x: base[i] + DX[part(i)], y: CY, r: R });
    const idx = [[0, 1, 2, 3, 4], [5, 6, 7], [8]];
    const parts = b9.split(tOpen + 0.05, idx.map(ids => [ids.map(after), '?', { tab: 's' }]));
    // "Let the largest part keep the old name."
    const tL = cue('large');
    parts[0].rename('X', tL + 0.35);
    parts[1].rename('Y', tL + 1.4); parts[2].rename('Z', tL + 1.55);
    [1, 2].forEach(k => { const p = parts[k].tabPos(); BX.note(tl, root, p.x, p.y + 34, 'new', tL + 1.8 + 0.1 * k, null); });

    // "Then the states in the largest part have not moved at all, and nothing that points to them becomes dirty."
    const tU = cue('unch');
    const svg = BX.svg(root);
    const DY = 330;
    // [dot x as a chip position (fractional), [chips it points to]]
    const preds = [[0.5, [0, 1]], [2.5, [2, 3]], [4, [4]], [5.5, [5, 6]], [7, [7]], [8, [8]]];
    const xAt = f => { const i = Math.floor(f), j = Math.ceil(f); return (after(i).x + after(j).x) / 2; };
    const dots = [], arrows = [];
    preds.forEach(([f, to], k) => {
      const d = { x: xAt(f), y: DY };
      const dot = box(root, d.x - 11, d.y - 11, { width: '22px', height: '22px', borderRadius: '50%', background: C.dim });
      const ring = box(root, d.x - 20, d.y - 20, { width: '40px', height: '40px', borderRadius: '50%', boxShadow: `inset 0 0 0 4px ${C.pat}` });
      tl.set(ring, { o: 0 }, 0);
      fadeIn(tl, dot, tU - 0.1 + k * 0.08, 0.4, 8);
      const as = to.map(i => liveArrow(tl, svg, d, after(i), { ra: 16, rb: R + 8, stroke: C.dim, width: 3, head: 12 }).draw(tU + 0.15 + k * 0.08, 0.45));
      dots.push({ dot, ring, small: part(to[0]) > 0 }); arrows.push(...as.map(a => ({ a, small: part(to[0]) > 0 })));
    });
    parts[0].pulse(tU + 2.0);
    const nd = rlabel(root, xAt(0.5) - 34, DY, 'not dirty');
    fadeIn(tl, nd, tU + 4.2, 0.5, 8);

    // "Only the smaller parts cost anything."
    const tS = cue('small');
    arrows.filter(a => a.small).forEach(({ a }) => a.color(C.pat, tS + 0.4));
    dots.filter(d => d.small).forEach(d => tl.to(d.ring, { o: 1 }, tS + 0.5, 0.35));
    BX.note(tl, root, CX, 700, 'only the smaller parts cost', tS + 1.0, null, { color: C.ink });
  });

  // ============================================ trick =========================================================
  scene('trick', ({ tl, root, cue }) => {
    const all = group(root);
    // "Take a set of N things, and keep splitting it."
    const cells = new BX.Cells(tl, all, CX - 50, 300, 16, { w: 60, h: 60, gap: 10, align: 'center' });
    cells.show(cue('set') + 0.6, { stagger: 0.03 });
    // "Follow one element."
    const F = 6;   // the seventh cell: it can end alone at the end of its part (see the report)
    cells.fill(F, C.ink, cue('follow') + 0.35);

    // "Each time it lands in a smaller part, the set around it is at most half as big as before."
    const tH = cue('half');
    const cnt = new BX.Counter(tl, all, cells.slotX(15) + 60 + 100, 220, 'times in a smaller part', { value: 1, align: 'right' });
    const sizes = BX.cline(all, CX, 420, [['16', null], ['  →  7', null], ['  →  3', null], ['  →  1', null]], Object.assign(BX.MONO(44), { color: C.ink }));
    sizes.parts.forEach(p => tl.set(p, { o: 0 }, 0));
    fadeIn(tl, sizes.parts[0], tH - 0.1, 0.5, 10);
    // nine and seven: the element is in the seven
    const t1 = tH + 0.4;
    cells.gap(7, 44, t1); cells.dimSlots(7, 15, 0.3, t1 + 0.3);
    cnt.show(t1 + 0.45);
    fadeIn(tl, sizes.parts[1], t1 + 0.45, 0.5, 10);
    // the seven into four and three
    const t2 = tH + 1.85;
    cells.gap(4, 32, t2); cells.dimSlots(0, 3, 0.3, t2 + 0.3);
    cnt.set(2, t2 + 0.45); fadeIn(tl, sizes.parts[2], t2 + 0.45, 0.5, 10);
    // the three into two and one: the element alone
    const t3 = tH + 3.3;
    cells.gap(6, 24, t3); cells.dimSlots(4, 5, 0.3, t3 + 0.3);
    cnt.set(3, t3 + 0.45); fadeIn(tl, sizes.parts[3], t3 + 0.45, 0.5, 10);
    BX.note(tl, all, CX, 490, 'at most half each time', tH + 3.95, null);

    // "That can happen only about log N times."
    const tLog = cue('log');
    tl.to(all, { y: -70, o: 0.4 }, tLog - 0.2, 0.8, E.io);
    const lg = BX.cline(root, CX, 540, [['at most log₂ N times', null]], Object.assign(BX.MONO(64), { color: C.ink }));
    fadeIn(tl, lg.root, tLog + 1.3, 0.6, 14);
    // "For a million elements: twenty times."
    const tTw = cue('twenty');
    const tw = BX.cline(root, CX, 660, [['N = 1 000 000 :', null], ['  20', null]], Object.assign(BX.MONO(48), { color: C.ink }));
    tw.parts.forEach(p => tl.set(p, { o: 0 }, 0));
    fadeIn(tl, tw.parts[0], tTw + 0.1, 0.5, 10); fadeIn(tl, tw.parts[1], tTw + 1.3, 0.5, 10);
    // "This is an old trick in automaton minimization, known as the half the size trick."
    const tOld = cue('old');
    const n1 = BX.note(tl, root, CX, 768, 'the half-the-size trick', tOld + 3.6, null, { color: C.ink });
    const n2 = BX.note(tl, root, CX, 820, "also called hopcroft's trick", tOld + 4.3, null);

    // "So a state gets a new name at most log N times."
    const tB = cue('bound');
    tl.to(all, { o: 0 }, tB - 0.4, 0.35, E.in);
    for (const e of [lg.root, tw.root, n1, n2]) fadeOut(tl, e, tB - 0.4, 0.35);
    const l1 = box(root, RAIL, 330, Object.assign(BX.SERIF(48), { whiteSpace: 'pre' }), 'a state gets a new name at most log N times');
    fadeIn(tl, l1, tB, 0.7, 18);
    // "Each new name makes dirty the states that point to it, its predecessors: one signature for each incoming edge."
    const l2 = box(root, RAIL, 440, Object.assign(BX.SERIF(48), { whiteSpace: 'pre' }), 'each new name: one signature for each incoming edge');
    fadeIn(tl, l2, cue('edges') - 0.1, 0.7, 18);
    // "Altogether, with M edges: M times log N signatures, instead of N squared."
    const tT = cue('total');
    const mw = 7 * charWidth(96), nw = 2 * charWidth(64), gap = 110, x0 = CX - (mw + gap + nw) / 2;
    const mln = box(root, x0, 590, Object.assign(BX.MONO(96), { color: C.good, whiteSpace: 'pre', lineHeight: '124px' }), 'M log N');
    fadeIn(tl, mln, tT + 2.1, 0.7, 18);
    BX.note(tl, root, x0 + mw / 2, 724, 'signatures', tT + 3.4, null);
    const nsq = BX.lline(root, x0 + mw + gap, 616, [['N²', null]], Object.assign(BX.MONO(64), { color: C.ink, lineHeight: '84px' }));
    fadeIn(tl, nsq.root, tT + 4.85, 0.5, 10);
    BX.strikeEl(tl, nsq.parts[0], tT + 5.35, { faint: false });
    tl.to(nsq.parts[0], { color: C.dim }, tT + 5.35, 0.45);
  });

  // ============================================ algo ==========================================================
  scene('algo', ({ tl, root, cue }) => {
    // "Here is the whole algorithm."
    BX.note(tl, root, RAIL, 160, 'the algorithm', cue('algo') - 0.2, null, { align: 'left', color: C.ink });
    const L = [
      ['put all states in one block; mark them all dirty', 'init'],
      ['repeat', 'loop'],
      ['    pick a block with dirty states', 'pick'],
      ['    compute the signatures of its dirty states,', 'comp'],
      ['        and of one clean state; they are now clean', 'comp+'],
      ['    split by signature; the largest part keeps the name', 'split'],
      ['    mark dirty: predecessors of states with a new name', 'mark'],
      ['until nothing is dirty', 'until'],
    ];
    // "dirty" amber, "name" cyan
    const partsOf = s => s.split(/(\bdirty\b|\bname\b)/).filter(x => x).map(x => [x, x === 'dirty' ? C.pat : x === 'name' ? C.bind : null]);
    // when each line arrives: at its cue; the second line of `comp` at "and of one clean state"
    const at = L.map(([, c]) => (c === 'comp+' ? cue('comp') + 2.56 : cue(c)) - 0.2);
    const rows = L.map(([s], i) => BX.lline(root, RAIL, 240 + i * 78, partsOf(s), Object.assign(BX.MONO(40), { lineHeight: '52px' })).root);
    rows.forEach((r, i) => {
      fadeIn(tl, r, at[i], 0.6, 14);
      // earlier lines step back when the next step is read (the two lines of `comp` are one step)
      const next = at.findIndex((t, j) => j > i && L[j][1] !== 'comp+');
      if (next > 0) tl.to(r, { o: 0.7 }, at[next], 0.4);
    });
  });
})();

// ==== src/scenes/e.js ====
// The run of the algorithm on the automaton (run_a, run_b), what it never does (cool_two), and the array that
// keeps the blocks (ds_a, ds_b). Built with BX (common.js). run_b starts exactly where run_a ends, and cool_two from
// the table as run_b leaves it: each of the three builds the same layout, in the state the last one left it.
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = BX;

  // ---- the layout of the run ------------------------------------------------------------------------------------
  const MX = 440, MY = 500, MS = 1.15;              // the automaton
  const TX = 900, TY = 500, TS = 52, TP = 92;       // the table: left edge, centre, size, pitch
  const NX = 1810, NY = 170;                        // the counter (its right edge, its middle)
  const LOW = 840;                                  // a label at the bottom
  const SIG1 = '(false, X, X)', SIGT = '(true, X, X)';
  const SIG2 = '(false, Y, X)', SIG4 = '(true, Y, Y)';

  // texts: the five rows' signatures to start with ('' for none)
  const table = (tl, root, texts) => new BX.Table(tl, root, TX, 0, [1, 2, 3, 4, 5].map((k, i) => [k, texts ? texts[i] : '']), { size: TS, pitch: TP, cy: TY, accepting: [4, 5] });
  function runLayout(tl, root, texts) {
    const m = new BX.Machine(tl, root, { kind: 'dfa', cx: MX, cy: MY, scale: MS });
    return { m, t: table(tl, root, texts) };
  }
  // where the green "=" brackets of the run go: the same place for both pairs, clear of the cool_two boxes
  const eqX = t => t.structX + 14 * charWidth(TS) + 44;
  // everything of a layout at once, at time 0
  function tableNow(t, fades) {
    t.rows.forEach((r, i) => {
      r.chip.show(0, { dur: 0, dy: 0 });
      r.s.show(0, { stagger: 0, rise: 0, dur: 0 });
      if (fades && fades[i] !== 1) t.fade(r.k, fades[i], 0, 0);
    });
  }
  const blockNow = (tl, b) => { tl.set(b.path, { draw: 1 }, 0); if (b.tabEl) tl.set(b.tabEl, { o: 1, s: 1 }, 0); return b; };
  // a dim label just above state 1 (clear of the outline and its tab)
  const aboveOne = (tl, root, m, text, at, out) => BX.note(tl, root, m.pos(1).x, m.pos(1).y - m.r - 86, text, at, out);

  // ============================================ run_a =======================================================
  scene('run_a', ({ tl, root, cue, dur }) => {
    const { m, t } = runLayout(tl, root);
    const n = new BX.Counter(tl, root, NX, NY, 'signatures computed', { align: 'right' });
    // "Run it on the automaton."
    const tRun = cue('run');
    m.show(tRun - 0.2, { stagger: 0.09 });
    [1, 2, 3, 4, 5].forEach((k, i) => t.chip(k).show(tRun + 0.9 + i * 0.1));

    // "One block, X, and all five states dirty."
    const tAll = cue('all');
    const bAll = m.block([1, 2, 3, 4, 5], 'X', tAll - 0.1);
    [1, 2, 3, 4, 5].forEach((k, i) => { m.dirty(k, tAll + 2.85 + i * 0.06); t.dirty(k, tAll + 2.85 + i * 0.06); });

    // "Five signatures, and now all five are clean."
    const tFive = cue('five');
    n.show(tFive - 0.2);
    [[1, SIG1], [2, SIG1], [3, SIG1], [4, SIGT], [5, SIGT]].forEach(([k, s], i) => t.set(k, s, tFive + 0.25 + i * 0.3));
    n.set(5, tFive + 0.45, { step: 0.3 });
    [1, 2, 3, 4, 5].forEach(k => { m.clean(k, tFive + 2.95); t.clean(k, tFive + 2.95); });

    // "Three say false, two say true. The three are the larger part, so they stay X, and states four and five
    // become block Y."
    const tSp = cue('sp');
    [1, 2, 3].forEach((k, i) => t.struct(k).pulse('false', tSp + 0.4 + i * 0.1));
    [4, 5].forEach((k, i) => t.struct(k).pulse('true', tSp + 1.45 + i * 0.1));
    const [bX, bY] = bAll.split(tSp + 4.85, [[[1, 2, 3], 'X'], [[4, 5], '']]);
    BX.note(tl, root, RAIL, 150, 'the larger part keeps X', tSp + 5.4, cue('pred') - 0.35, { align: 'left' });
    bY.rename('Y', tSp + 7.95);

    // "Who points to four or five? States two, three, four, and five. They become dirty."
    const tPred = cue('pred');
    ['2>4', '4>4', '5>4'].forEach((e, i) => m.color(e, C.pat, tPred + 0.55 + i * 0.13));
    ['3>5', '4>5'].forEach((e, i) => m.color(e, C.pat, tPred + 1.1 + i * 0.13));
    [[2, 2.65], [3, 3.3], [4, 3.95], [5, 4.95]].forEach(([k, d]) => { m.dirty(k, tPred + d); t.dirty(k, tPred + d); });
    t.fade([2, 3, 4, 5], 0.3, tPred + 6.0);
    m.recolor(['in:4', 'in:5'], tPred + 6.6, 0.5);

    // "State one does not. It stays clean."
    const tOne = cue('one');
    m.pulse(1, tOne + 0.4); t.pulse(1, tOne + 0.4, { part: 'chip' });
    aboveOne(tl, root, m, 'clean', tOne + 1.7, dur - 0.45);
    return { keep: true };
  });

  // ============================================ run_b =======================================================
  scene('run_b', ({ tl, root, cue, dur }) => {
    // as run_a left it: X = {1, 2, 3}, Y = {4, 5}; 2, 3, 4, 5 dirty, their signatures faint; the counter at 5
    const { m, t } = runLayout(tl, root, [SIG1, SIG1, SIG1, SIGT, SIGT]);
    m.appear(0, { dur: 0 });
    tableNow(t, [1, 0.3, 0.3, 0.3, 0.3]);
    const bX = blockNow(tl, m.block([1, 2, 3], 'X'));
    const bY = blockNow(tl, m.block([4, 5], 'Y'));
    for (const k of [2, 3, 4, 5]) { m.state(k).dirty(0, 0); t.chip(k).dirty(0, 0); }
    const n = new BX.Counter(tl, root, NX, NY, 'signatures computed', { align: 'right', value: 5 });
    tl.set(n.el, { o: 1 }, 0);

    const ofY = ['4>4', '4>5', '5>4'], ofX = ['1>2', '1>3', '2>3', '3>3', '2>4', '3>5'];
    // "Take block X."
    const tA = cue('blockA');
    bY.dim(0.4, tA); m.dim([4, 5, ...ofY], 0.4, tA); t.dim([4, 5], 0.4, tA, { part: 'chip' }); tl.to(t.struct(4).root, { o: 0.16 }, tA, 0.4); tl.to(t.struct(5).root, { o: 0.16 }, tA, 0.4);
    bX.pulse(tA + 0.8);
    // "Two dirty states, two and three, and one clean state."
    const tTwo = cue('two');
    m.pulse(2, tTwo + 1.4); t.pulse(2, tTwo + 1.4, { part: 'chip' });
    m.pulse(3, tTwo + 2.05); t.pulse(3, tTwo + 2.05, { part: 'chip' });
    aboveOne(tl, root, m, 'one clean state', tTwo + 2.85, cue('split') - 0.3);

    // "Three signatures. Two and three read: false, Y, X. State one reads: false, X, X."
    const tS = cue('sigs');
    [2, 3].forEach((k, i) => { t.fade(k, 1, tS + 2.35 + i * 0.3, 0.2); t.set(k, SIG2, tS + 2.35 + i * 0.3); });
    n.set(6, tS + 2.55); n.set(7, tS + 2.85);
    [2, 3].forEach(k => { m.clean(k, tS + 5.0); t.clean(k, tS + 5.0); });
    t.set(1, SIG1, tS + 5.45); n.set(8, tS + 5.65);
    t.pulse(1, tS + 6.9);

    // "The block splits. Two and three are the larger part, so they keep the name X, and state one becomes block Z."
    const tSplit = cue('split');
    const [bX2, bZ] = bX.split(tSplit + 0.3, [[[2, 3], 'X'], [[1], '']]);
    bX2.pulse(tSplit + 4.85);
    bZ.rename('Z', tSplit + 6.65);

    // "Who points to state one? Nobody. So nothing becomes dirty."
    const tNo = cue('nobody');
    m.pulse(1, tNo + 0.85); t.pulse(1, tNo + 0.85, { part: 'chip' });
    aboveOne(tl, root, m, 'no predecessors', tNo + 1.85, cue('blockB') - 0.3);

    // "Take block Y. Two dirty states, two signatures, and they agree: no split."
    const tB = cue('blockB');
    bY.dim(1, tB); m.light([4, 5, ...ofY], tB); t.light([4, 5], tB, { part: 'chip' });
    bX2.dim(0.4, tB); bZ.dim(0.4, tB); m.dim([1, 2, 3, ...ofX], 0.4, tB); t.dim([1, 2, 3], 0.4, tB);
    [4, 5].forEach((k, i) => { t.fade(k, 1, tB + 3.05 + i * 0.3, 0.2); t.set(k, SIG4, tB + 3.05 + i * 0.3); });
    n.set(9, tB + 3.25); n.set(10, tB + 3.55);
    const eq45 = t.equal(4, 5, tB + 4.2, { x: eqX(t) });
    [4, 5].forEach(k => { m.clean(k, tB + 5.1); t.clean(k, tB + 5.1); });

    // "Nothing is dirty. Done."
    const tEnd = cue('end');
    bX2.dim(1, tEnd - 0.1); bZ.dim(1, tEnd - 0.1); m.light('all', tEnd - 0.1); t.light([1, 2, 3], tEnd - 0.1);
    const done = BX.note(tl, root, CX, LOW, 'nothing is dirty', tEnd + 0.15, null, { color: C.good });

    // "That was ten signatures, where the simple algorithm computed fifteen."
    const tC = cue('count');
    n.pulse(tC + 0.45); n.color(C.good, tC + 0.45);
    const simple = BX.note(tl, root, NX, NY + 44, 'the simple algorithm: 15', tC + 1.8, null, { align: 'left' });
    simple.style.left = ''; simple.style.right = (W - NX) + 'px';
    // the table stays for cool_two; everything else leaves
    const tOut = dur - 0.55;
    m.hide(tOut); n.hide(tOut); fadeOut(tl, done, tOut, 0.4); fadeOut(tl, simple, tOut, 0.4);
    return { keep: true };
  });

  // ============================================ cool_two ====================================================
  scene('cool_two', ({ tl, root, cue }) => {
    // the table as run_b left it, with the "=" of 4 and 5; it moves to the centre
    const t = table(tl, root, [SIG1, SIG2, SIG2, SIG4, SIG4]);
    tableNow(t);
    const rows = t.rows.map(r => [r.k]);
    const xe = eqX(t);
    const eq45 = t.equal(4, 5, -1, { x: xe });
    tl.set(eq45.els[1], { o: 1, y: 0 }, 0);
    const right = xe + 16 + 14 + charWidth(Math.round(TS * 0.85)) + 60;
    const dx = Math.round(CX - (TX + right) / 2);
    t.to({ x: dx }, 0.15, 0.85);

    // "It never looked inside a signature. It only asked for signatures, and compared them."
    const tIn = cue('inside');
    rows.forEach(([k], i) => {
      const r = t.rect(k);
      const b = box(t.g, r.x - 16, r.y + 2, { width: (14 * charWidth(TS) + 32) + 'px', height: (r.h - 4) + 'px', borderRadius: '14px', background: C.bg, boxShadow: `inset 0 0 0 3px ${C.ink}`, transformOrigin: 'left center' });
      tl.set(b, { o: 0, sx: 0.04 }, 0); tl.set(b, { o: 1 }, tIn + 0.6 + i * 0.09); tl.to(b, { sx: 1 }, tIn + 0.6 + i * 0.09, 0.5, E.io);
    });
    t.equal(2, 3, tIn + 4.85, { x: xe });
    BX.note(tl, root, CX, 780, 'asked for, and compared. never opened', tIn + 2.0, null);
    // "So it works for any kind of machine that can compute them."
    BX.note(tl, root, CX, 836, 'any kind of machine that can compute a signature', cue('any') + 0.6, null, { color: C.ink });
  });

  // ============================================ ds_a ========================================================
  scene('ds_a', ({ tl, root, cue }) => {
    const svg = BX.svg(root);
    // "Counting signatures is not the whole cost."
    const tCount = cue('count'), tTouch = cue('touch');
    const mlog = BX.cline(root, CX, 360, [['M log N', C.good]], BX.MONO(72)).root;
    fadeIn(tl, mlog, tCount - 0.2, 0.6, 16); fadeOut(tl, mlog, tTouch - 0.3, 0.35);
    BX.note(tl, root, CX, 470, 'signatures', tCount + 0.2, tTouch - 0.3);

    // "If splitting a block meant walking over all of its states, the clean ones too, the M log N bound would be
    // lost."
    const many = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const R = 30, P = 86, X0 = CX - 5 * P, ROWS = [390, 480], DIRTY = [8, 14];
    const chips = [];
    for (let q = 0; q < 22; q++) {
      const c = new BX.Chip(tl, many, X0 + (q % 11) * P, ROWS[Math.floor(q / 11)], '', { r: R });
      c.show(tTouch - 0.1 + q * 0.015, { dur: 0.4 });
      if (DIRTY.includes(q)) c.dirty(tTouch - 0.1 + q * 0.015);
      chips.push(c);
    }
    const blk = new BX.Block(tl, many, chips.map(c => c.circle()), 'X', { at: tTouch + 0.15, pad: 28, tab: { x: CX, y: ROWS[0] - R - 28 } });
    // the sweep: a thin bar runs over every chip
    const s0 = X0 - R - 30, s1 = X0 + 10 * P + R + 30, sA = tTouch + 1.5, sB = tTouch + 4.2;
    const bar = box(many, s0, ROWS[0] - R - 34, { width: '4px', height: (ROWS[1] - ROWS[0] + 2 * R + 68) + 'px', borderRadius: '2px', background: C.ink });
    tl.set(bar, { o: 0 }, 0); tl.to(bar, { o: 1 }, sA - 0.2, 0.2); tl.to(bar, { x: s1 - s0 }, sA, sB - sA, E.lin); tl.to(bar, { o: 0 }, sB, 0.3);
    chips.forEach(c => c.pulse(sA + (c.x - s0) / (s1 - s0) * (sB - sA) - 0.1, { dur: 0.45, scale: 1.08 }));
    BX.note(tl, many, CX, 580, 'walking over every state: the bound is lost', tTouch + 4.95, null);
    const tArr = cue('arr');
    tl.to(many, { o: 0 }, tArr - 0.3, 0.35, E.in);

    // "So the states are kept in one array, each block a stretch of it,"
    const N = 9, CW = 120, CY = 380, LY = 300;
    const cells = new BX.Cells(tl, root, CX, CY, N, { w: CW, h: CW, gap: 10, size: 44, align: 'center' });
    for (let i = 0; i < N; i++) cells.text(i, 's' + '₁₂₃₄₅₆₇₈₉'[i]);
    cells.show(tArr + 0.1, { stagger: 0.06 });
    const brX = cells.bracket(0, N - 1, 'X', tArr + 2.35);
    // the neighbouring blocks: a faint cell and a dim "…" at each end
    const x0 = cells.slotX(0), x9 = cells.slotX(N - 1) + CW;
    const hints = [
      BX.cell(root, x0 - 10 - CW, CY, CW, CW, '', { stroke: C.faint, radius: 10 }),
      BX.cell(root, x9 + 10, CY, CW, CW, '', { stroke: C.faint, radius: 10 }),
      box(root, x0 - 2 * CW - 20, CY, Object.assign(BX.MONO(44), { color: C.dim, width: CW + 'px', lineHeight: CW + 'px', textAlign: 'center' }), '…'),
      box(root, x9 + CW + 20, CY, Object.assign(BX.MONO(44), { color: C.dim, width: CW + 'px', lineHeight: CW + 'px', textAlign: 'center' }), '…'),
    ];
    hints.forEach((h, i) => fadeIn(tl, h, tArr + 2.6 + (i % 2) * 0.1, 0.5, 0));

    // "with its clean states first and its dirty states at the end."
    const tCd = cue('cd');
    const span = (a, b) => (cells.slotX(a) + cells.slotX(b) + CW) / 2;
    const cleanL = BX.clabel(root, span(0, 3), LY, 'clean');
    const dirtyL = BX.clabel(root, span(4, 8), LY, 'dirty', 32, C.pat);
    fadeIn(tl, cleanL, tCd + 0.35, 0.5, 10);
    const div = cells.divider(4, tCd + 1.6);
    fadeIn(tl, dirtyL, tCd + 2.15, 0.5, 10);
    for (let i = 4; i < N; i++) cells.outline(i, C.pat, tCd + 2.2 + (i - 4) * 0.05);

    // "Marking a state dirty is one swap, with the last clean state of its block."
    const tMark = cue('mark');
    cells.outline(2, C.pat, tMark + 0.95);
    // the swap: s₃ passes above (the labels make room), s₄ slides along the row
    const tSw = tMark + 1.6;
    fadeOut(tl, cleanL, tSw - 0.35, 0.3); fadeOut(tl, dirtyL, tSw - 0.35, 0.3);
    {
      const si = cells.pos[2], sj = cells.pos[3];
      cells.pos[2] = sj; cells.pos[3] = si; cells.slots[si] = 3; cells.slots[sj] = 2;
      cells._place(2, sj, tSw, 0.85, -(CW + 14));
      cells._place(3, si, tSw, 0.85, 0);
    }
    div.move(3, tSw + 0.5);
    const cleanL2 = BX.clabel(root, span(0, 2), LY, 'clean');
    const dirtyL2 = BX.clabel(root, span(3, 8), LY, 'dirty', 32, C.pat);
    fadeIn(tl, cleanL2, tSw + 1.0, 0.5, 10); fadeIn(tl, dirtyL2, tSw + 1.0, 0.5, 10);
    const markL = BX.note(tl, root, CX, 620, 'mark dirty: one swap', tSw + 0.6, null);

    // "Splitting a block rearranges only its dirty states."
    const tSplit = cue('split');
    const tGo = tSplit + 0.45;
    for (const e of [cleanL2, dirtyL2, markL]) fadeOut(tl, e, tGo - 0.4, 0.3);
    brX.hide(tGo - 0.4); div.hide(tGo - 0.4);
    // s₁ s₂ s₄ s₇ s₈ · s₃ s₆ s₉ · s₅ (ids are the subscripts minus one)
    cells.move([0, 1, 3, 6, 7, 2, 5, 8, 4], tGo, { dur: 1.1 });
    const tB = tGo + 1.25;
    cells.bracket(0, 4, 'X', tB); cells.bracket(5, 7, 'Y', tB + 0.12); cells.bracket(8, 8, 'Z', tB + 0.24);
    for (let i = 0; i < N; i++) cells.outline(i, null, tB + 0.2);
    BX.note(tl, root, CX, 620, 'split: only the dirty states move', tSplit + 2.3, null);

    // "So a split costs time proportional to the number of dirty states, however many clean ones there are."
    BX.note(tl, root, CX, 800, 'cost of a split: the number of dirty states', cue('cost') + 0.6, null, { color: C.ink });
  });

  // ============================================ ds_b ========================================================
  scene('ds_b', ({ tl, root, cue }) => {
    // "The algorithm also needs little memory."
    const tMem = cue('mem'), tNeed = cue('need'), tTh = cue('theory');
    const memL = BX.note(tl, root, CX, 150, 'memory', tMem + 1.8, tNeed - 0.3, { color: C.ink });
    // "It keeps the machine, each state's predecessors, and this structure for the blocks."
    const group = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    BX.note(tl, group, CX, 150, 'what the algorithm keeps', tNeed + 0.1, null);
    const BY = 330, boxes = [['the machine', 700, 230, 0.75], ['predecessors', 400, 130, 1.95], ['the blocks', 340, 130, 3.7]];
    const gapB = 40, total = boxes.reduce((a, b) => a + b[1], 0) + gapB * (boxes.length - 1);
    let bx = CX - total / 2;
    for (const [text, w, h, d] of boxes) {
      const b = BX.cell(group, bx, BY - h / 2, w, h, text, { font: Object.assign(BX.LABEL(32), { color: C.ink }), radius: 16 });
      fadeIn(tl, b, tNeed + d, 0.6, 14);
      bx += w + gapB;
    }
    // "The earlier fast algorithms keep more: a counter for each transition, for example."
    const tNo = cue('no');
    const dash = box(group, CX - 420, 520, { width: '840px', height: '120px', borderRadius: '16px', border: `3px dashed ${C.dim}`, boxSizing: 'border-box' });
    fadeIn(tl, dash, tNo + 0.4, 0.6, 14);
    const dashT = BX.ctext(group, CX, 580, 'a counter for each transition', Object.assign(BX.LABEL(32), { color: C.dim }), 120);
    fadeIn(tl, dashT, tNo + 2.75, 0.5, 8);
    BX.note(tl, group, CX, 662, 'earlier fast algorithms', tNo + 0.6, null);
    tl.to(group, { o: 0 }, tTh - 0.2, 0.4, E.in);

    // "In theory, there is a price."
    BX.note(tl, root, RAIL, 170, 'in theory', tTh + 0.35, null, { align: 'left', color: C.ink });
    // "Computing a signature looks at all of a state's successors. The fastest earlier algorithms, which ask more
    // of the shape, avoid that cost."
    const tK = cue('k'), MXk = 1140;
    const row = (i, text, mono, at, col) => {
      const y = 300 + i * 120;
      const l = box(root, RAIL, y - 20, Object.assign(BX.LABEL(32), { whiteSpace: 'pre', lineHeight: '40px' }), text);
      const v = box(root, MXk, y - 37, Object.assign(BX.MONO(56), { whiteSpace: 'pre', lineHeight: '74px', color: col || C.code }), mono);
      fadeIn(tl, l, at, 0.5, 12); fadeIn(tl, v, at + 0.15, 0.5, 12);
      return { l, v, y };
    };
    row(0, 'signatures', 'M log N', tK - 0.15);
    const r1 = row(1, 'time for one signature', 'k', tK + 0.8);
    const hint = box(root, MXk + charWidth(56) + 36, r1.y - 20, { whiteSpace: 'pre', display: 'flex', alignItems: 'baseline', lineHeight: '40px' });
    el(hint, 'span', Object.assign(BX.MONO(34), { position: 'relative', color: C.dim }), 'k');
    el(hint, 'span', Object.assign(BX.LABEL(32), { position: 'relative' }), ': successors of a state');
    fadeIn(tl, hint, tK + 2.6, 0.5, 10);
    row(2, 'fastest earlier algorithms, in all', 'M log N', tK + 3.85, C.dim);

    // "In the measurements, as we will see, this price does not show."
    BX.note(tl, root, CX, 780, 'in the measurements: the price does not show', cue('practice') + 0.3, null, { color: C.ink });
  });
})();

// ==== src/scenes/f.js ====
// Kinds of machine, and the measurements: types_a, types_b, bench_a, bench_b, bench_c, cool_three, limits.
// Built with BX (common.js). Every number is from SCENES.md ("The measurements"), which follows the paper's
// Tables 2 and 3.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const { CX } = BX;
  const LX = 200;   // the left edge of the rows and labels in these scenes

  // ---- local helpers ----------------------------------------------------------------------------------------------
  // a full-stage group (to dim or move several things together)
  const group = root => box(root, 0, 0, { width: W + 'px', height: H + 'px' });
  // a small caps label, left edge at x (align 'right': right edge; 'center': centre), top at y
  function lab(root, x, y, text, { size = 32, color = C.dim, align = 'left' } = {}) {
    if (align === 'center') return BX.clabel(root, x, y, text, size, color);
    const st = Object.assign(BX.LABEL(size), { color, whiteSpace: 'pre' });
    if (align === 'right') Object.assign(st, { width: '1600px', textAlign: 'right' });
    return box(root, align === 'right' ? x - 1600 : x, y, st, text);
  }
  // a label line in which some parts are tool names, set in the serif so that their lower-case letters stay
  // lower case: parts [[text, 'serif' | null, colour], ...]
  function mixed(root, x, y, parts, { size = 32, color = C.dim, align = 'left' } = {}) {
    const st = Object.assign(BX.LABEL(size), { color });
    const L = align === 'center' ? BX.cline(root, x, y, parts.map(p => [p[0], p[2] || null]), st)
      : BX.lline(root, x, y, parts.map(p => [p[0], p[2] || null]), st);
    parts.forEach((p, i) => {
      if (p[1] === 'serif') Object.assign(L.parts[i].style, { fontFamily: 'var(--serif)', textTransform: 'none', letterSpacing: '0', fontWeight: 400, fontSize: Math.round(size * 1.22) + 'px', lineHeight: '1' });
    });
    return L.root;
  }
  // a serif line, left edge at x, top at y
  const serifL = (root, x, y, text, size, color = C.ink) => box(root, x, y, Object.assign(BX.SERIF(size), { color, whiteSpace: 'pre' }), text);
  const show = (tl, e, at, dy = 10, dur = 0.5) => fadeIn(tl, e, at, dur, dy);
  const hide = (tl, e, at, dur = 0.35) => fadeOut(tl, e, at, dur, -8);

  // ============================================ types_a =======================================================
  // the pieces, as chips: the same look wherever pieces are shown (shape_c, types_a, types_comp, types_b)
  const PIECES = ['flag, label', 'tuple', 'set', 'distribution'];
  // a row of piece chips centred on cx (middle at y), after an optional dim label; returns the chips
  function pieceRow(tl, root, cx, y, texts, at, { label, gap = 30, size = 30, stagger = 0.15, extra = 0 } = {}) {
    const ws = texts.map(t => Math.max(...String(t).split('\n').map(l => BX.labelW(l.toUpperCase(), size))) + size * 1.2);
    const lw = label ? BX.labelW(label.toUpperCase(), size) + gap : 0;
    let x = cx - (lw + ws.reduce((a, b) => a + b, 0) + gap * (texts.length - 1) + extra) / 2;
    if (label) show(tl, lab(root, x, y - Math.round(size * 0.6), label, { size }), at - 0.1);
    x += lw;
    const out = texts.map((t, i) => { const e = BX.piece(root, x, y, t, { size }); show(tl, e, at + i * stagger, 8); x += e._w + gap; return e; });
    out.next = x;
    return out;
  }

  scene('types_a', ({ tl, root, cue }) => {
    const tFn = cue('fn');
    // "What does a kind of machine have to provide?": the three machines seen so far, small, until the answer
    const zoo = group(root);
    [['dfa', 520], ['ts', 960], ['mc', 1400]].forEach(([kind, x], i) => new BX.Machine(tl, zoo, { kind, cx: x, cy: 480, scale: 0.6 }).appear(cue('what') - 0.2 + i * 0.25, { dur: 0.6 }));
    fadeOut(tl, zoo, tFn - 0.4, 0.4, -10);
    // "Essentially one function: given a state and the current blocks, return the state's signature."
    const fn = new BX.Struct(tl, root, CX, 190, 'signature(state, blocks)', { size: 52, align: 'center' });
    fn.show(tFn - 0.2, { stagger: 0.02 });
    fn.pulse('state', 7.25); fn.pulse('blocks', 8.65); fn.pulse('signature', 10.5);
    // "But these functions are not written one kind of machine at a time. Shapes are built from a few pieces, and
    // each piece knows how to rename."
    const tK = cue('kit');
    fn.to({ y: -30, o: 0.6 }, tK - 0.1, 0.7, E.io);
    show(tl, lab(root, BX.RAIL, 300, 'shapes are built from a few pieces', { color: C.ink }), 15.4);
    const ROWY = [390, 520, 650, 780];
    const chipTexts = ['tuple', 'set', 'distribution,\nweights', 'flag,\nlabel'];
    const chips = chipTexts.map((t, i) => { const e = BX.piece(root, LX, ROWY[i], t); show(tl, e, 16.55 + i * 0.15, 8); return e; });

    // the rows: before, a drawn arrow, after, and a dim label under the example
    const EX = 640, AX = EX + 18 * charWidth(44) + 30, BX2 = AX + 130;
    const rows = [];
    function row(i, before, tB, tA, note, tN) {
      const y = ROWY[i], g = group(root);
      rows.forEach(r => tl.to(r, { o: 0.55 }, tB - 0.2, 0.5));
      rows.push(g);
      tl.to(chips[i], { s: 1.1 }, tB - 0.2, 0.25, E.out); tl.to(chips[i], { s: 1 }, tB + 0.05, 0.4, E.io);
      const b = new BX.Struct(tl, g, EX, y, before, { size: 44 });
      b.show(tB - 0.1);
      BX.line(tl, BX.svg(g), AX, y, AX + 100, y, { at: tA - 0.25, dur: 0.4, stroke: C.ink, head: 14 });
      show(tl, lab(g, EX, y + 36, note), tN);
      return t => new BX.Struct(tl, g, BX2, y, t, { size: 44 });
    }
    // "A tuple renames each of its parts."
    const a1 = row(0, '(4, 3)', cue('p1'), 20.94, 'rename each part', 22.0)('(Y, X)');
    a1.show(21.0, { sel: [0, 1] }); a1.show(21.6, { sel: [2, 3, 4] });
    // "A set renames its elements, sorts them, and drops duplicates."
    const a2 = row(1, '{2, 3, 4}', cue('p2'), 23.66, 'rename, sort, drop duplicates', 26.5)('{X, Y, Y}');
    a2.show(23.75);
    a2.morph('{X, Y}', 25.95, { dur: 0.6 });
    // "A distribution, or weights of any kind: rename, sort, and add up the weights that land in the same block."
    const a3 = row(2, '{2: ¼, 4: ½, 5: ¼}', cue('p3'), 30.3, 'rename, sort, add', 32.6)('{X: ¼, X: ¼, Y: ½}');
    a3.show(30.4);
    a3.morph('{X: ½, Y: ½}', 31.65, { dur: 0.6 });
    // "A flag or a label stays as it is."
    const a4 = row(3, 'false', cue('p4'), 36.06, 'stays as it is', 36.6)('false');
    a4.show(36.1);
  });

  // ============================================ types_comp ====================================================
  scene('types_comp', ({ tl, root, cue }) => {
    // "The pieces fit inside one another, and so do their functions."
    const top = group(root);
    pieceRow(tl, top, CX, 170, ['flag, label', 'tuple', 'set', 'distribution'], cue('comp') - 0.2, { label: 'the pieces', stagger: 0.12 });

    // three small nests in a row, their labels on one line under the tallest
    const S = { size: 28 };
    const small = group(root);
    small.style.transformOrigin = `${CX}px 420px`;
    const st = id => ({ state: true, id });
    const nD = new BX.Nest(tl, small, { box: 'tuple', id: 'T', items: [{ leaf: 'flag', id: 'F' }, st('a'), st('b')] }, 380, 480, S);
    const nL = new BX.Nest(tl, small, { box: 'set', id: 'S', items: [{ box: 'tuple', id: 'T', items: [{ leaf: 'label', id: 'L' }, st('s')] }] }, 960, 480, S);
    const nM = new BX.Nest(tl, small, { box: 'set', id: 'S', items: [{ box: 'distribution', id: 'D', items: [st('s')] }] }, 1540, 480, S);
    const LY = Math.max(nD.bottom, nL.bottom, nM.bottom) + 24;
    // "The automaton's shape is a tuple of a flag and two states."
    show(tl, lab(small, 380, LY, 'finite automaton', { align: 'center' }), 5.0);
    nD.show('T', 6.45); nD.show('F', 7.2); nD.show('a', 7.75); nD.show('b', 7.9);
    // "Put a set around pairs of a label and a state, and you have a labelled transition system."
    nL.show('S', 9.55); nL.show('T', 10.3); nL.show('L', 10.95); nL.show('s', 11.65);
    show(tl, lab(small, 960, LY, 'labelled', { align: 'center' }), 13.0);
    show(tl, lab(small, 960, LY + 40, 'transition system', { align: 'center' }), 13.3);
    // "Put a set around distributions, and you have a Markov decision process, which has both choice and chance."
    nM.show('S', 15.55); nM.show('D', 16.2); nM.show('s', 16.55);
    show(tl, lab(small, 1540, LY, 'markov', { align: 'center' }), 17.8);
    show(tl, lab(small, 1540, LY + 40, 'decision process', { align: 'center' }), 18.4);
    show(tl, lab(small, 1540, LY + 80, 'choice and chance', { align: 'center', color: C.faint }), 20.4);

    // "One of the benchmark models we will see has this shape: a number, with a set of pairs of a number and a
    // distribution. Four pieces, nested."
    const tW = cue('wlan');
    tl.to(small, { o: 0.35, y: -230, s: 0.8 }, tW - 0.2, 0.8, E.io);
    hide(tl, top, tW - 0.2, 0.4);
    const big = new BX.Nest(tl, root, { box: 'tuple', id: 'T1', items: [{ leaf: 'number', id: 'N1' }, { box: 'set', id: 'S', items: [{ box: 'tuple', id: 'T2', items: [{ leaf: 'number', id: 'N2' }, { box: 'distribution', id: 'D', items: [st('s')] }] }] }] }, CX, 625, { size: 32, stateR: 28, pad: 18, gap: 18 });
    const wl = mixed(root, CX, big.bottom + 18, [['a benchmark model (', null], ['wlan', 'serif'], [')', null]], { align: 'center' });
    show(tl, wl, 23.3);
    big.show('T1', 25.35); big.show('N1', 26.35); big.show('S', 27.4); big.show('T2', 27.8); big.show('N2', 28.35); big.show('D', 29.05); big.show('s', 29.4);
    ['T1', 'S', 'T2', 'D'].forEach((id, i) => big.pulse(id, 30.6 + i * 0.3));
    // "So to describe a new kind of machine, you usually just write down its shape."
    const own = lab(root, CX, 856, 'a new kind of machine: write down its shape', { align: 'center', color: C.ink });
    show(tl, own, 33.6); hide(tl, own, 38.0);
    // "Its signature function follows the shape: the outer piece calls the inner ones."
    show(tl, lab(root, CX, 856, 'its signature function follows the shape', { align: 'center', color: C.ink }), 38.4);
    ['T1', 'S', 'T2', 'D'].forEach((id, i) => big.glow(id, 40.75 + i * 0.45, { dur: 1.0 }));
  });

  // ============================================ types_b =======================================================
  scene('types_b', ({ tl, root, cue }) => {
    // "The earlier fast algorithm could not take a combined shape as it is."
    const st = { state: true, id: 's' };
    const nest = new BX.Nest(tl, root, { box: 'set', id: 'S', items: [{ box: 'distribution', id: 'D', items: [st] }] }, CX, 205, { size: 26, stateR: 22 });
    nest.showTree('S', cue('earlier') - 0.1, { stagger: 0.12 });
    const halves = group(root), hs = BX.svg(halves);
    const LH = 420, RH = 1440, HY = 310, CY0 = 425;
    show(tl, lab(halves, LH, HY, 'the earlier fast algorithm', { align: 'center', color: C.ink }), cue('earlier') + 0.2);
    // "It had to cut every state into intermediate states, between the pieces, which made the machine larger."
    const big = new BX.Chip(tl, halves, LH, CY0, '', { r: 40 });
    big.show(5.5, { draw: true });
    [-90, 0, 90].forEach((dx, i) => {
      const x = LH + dx, y = CY0 + 100, ux = dx / Math.hypot(dx, 100), uy = 100 / Math.hypot(dx, 100);
      const ln = BX.line(tl, hs, LH + 41 * ux, CY0 + 41 * uy, x - 21 * ux, y - 21 * uy, { head: 0, stroke: C.ink, width: 3 });
      tl.to(ln.path, { draw: 1 }, 6.9 + i * 0.15, 0.35, E.io);
      new BX.Chip(tl, halves, x, y, '', { r: 20 }).show(7.15 + i * 0.15, { draw: true, dur: 0.4 });
    });
    show(tl, lab(halves, LH, 565, 'intermediate states:', { align: 'center' }), 7.6);
    show(tl, lab(halves, LH, 605, 'a larger machine', { align: 'center' }), 10.2);
    // "Here, one state stays one state."
    show(tl, lab(halves, RH, HY, 'here', { align: 'center', color: C.ink }), cue('direct') - 0.1);
    new BX.Chip(tl, halves, RH, CY0, '', { r: 40 }).show(12.45, { draw: true });
    BX.tick(tl, hs, RH + 84, CY0, 44, 13.5);
    show(tl, lab(halves, RH, 565, 'one state stays one state', { align: 'center', color: C.good }), 13.0);

    // "And when no combination fits, a new piece can be added."
    const tN = cue('new');
    tl.to(halves, { o: 0.35, y: -65 }, tN - 0.15, 0.7, E.io); nest.dim(0.35, tN - 0.15);
    const PY = 642, NEWT = 'set of sets,\nupward closed', NS = 30;
    const newW = BX.labelW('UPWARD CLOSED', NS) + NS * 1.2;
    const row = pieceRow(tl, root, CX, PY, PIECES, tN + 0.2, { stagger: 0.1, extra: 30 + newW });
    const dashed = BX.piece(root, row.next, PY, ' ', { dashed: true, color: C.dim });
    Object.assign(dashed.style, { width: newW + 'px', height: Math.round(2 * NS * 1.2 + NS * 0.7) + 'px', top: (PY - Math.round(2 * NS * 1.2 + NS * 0.7) / 2) + 'px' });
    show(tl, dashed, 16.5, 8);
    // "One comes from logics about games: a set of sets of states, in which any larger set also belongs. The earlier
    // algorithm, which needs a special way of splitting blocks for every piece, could not handle that shape at all."
    const named = BX.piece(root, row.next, PY, NEWT);
    tl.set(named, { o: 0 }, 0); tl.to(named, { o: 1 }, 20.9, 0.4); tl.to(dashed, { o: 0 }, 20.9, 0.4);
    const EXC = CX - 70, EY = 744;
    show(tl, lab(root, EXC, EY + 40, 'from logics about games (monotone neighbourhood frames)', { align: 'center' }), 19.3);
    // the sets of sets: {1} and {2, 3}, then the larger sets that also belong
    const SOS = '{ {1}, {2, 3}, {1, 2}, {1, 3}, {1, 2, 3} }', C0 = '{ {1}, {2, 3}'.length;
    const sos = new BX.Struct(tl, root, EXC, EY, SOS, { size: 44, align: 'center' });
    sos.show(21.3, { sel: p => p.col < C0 || p.col === SOS.length - 1, stagger: 0.02 });
    sos.show(23.4, { sel: p => p.col >= C0 && p.col < SOS.length - 1, stagger: 0.03 });
    const tag = box(root, sos.x + sos.width + 30, EY - 40, Object.assign(BX.LABEL(28), { color: C.dim, whiteSpace: 'pre', lineHeight: '34px', padding: '6px 14px 6px 18px', borderRadius: '8px', boxShadow: `inset 0 0 0 2px ${C.dim}` }), 'earlier:\nnot supported');
    show(tl, tag, 30.6);
    // "In Boa, a new piece is a small amount of Rust: essentially its signature function."
    show(tl, mixed(root, CX, 858, [['in ', null], ['Boa', 'serif'], [': a new piece is one function in rust', null]], { align: 'center', color: C.ink }), cue('boa') + 0.1);
  });

  // ============================================ bench_a =======================================================
  // the three tools, as rows of names at x = 200 (row i's middle at y0 + i * pitch)
  function names(tl, root, y0, pitch, size = 52) {
    const mk = (i, text, col) => {
      const e = box(root, LX, y0 + i * pitch - Math.round(size * 1.22) / 2, Object.assign(BX.SERIF(size), { color: col, whiteSpace: 'pre' }), text);
      tl.set(e, { o: 0 }, 0);
      return e;
    };
    return [mk(0, 'CoPaR', C.ink), mk(1, 'DCPR', C.ink), mk(2, 'Boa', C.good)];
  }

  scene('bench_a', ({ tl, root, cue }) => {
    // "The benchmarks are from earlier work: models from a probabilistic model checker, and large, randomly
    // generated tree automata with weights."
    const tSu = cue('suite');
    const s1 = lab(root, LX, 160, 'models from a probabilistic model checker (prism)');
    const s2 = lab(root, LX, 210, 'random weighted tree automata');
    show(tl, s1, tSu - 0.2); show(tl, s2, 9.1);
    // "Boa is compared with two general tools: the earlier fast algorithm, and a distributed version of the simple
    // algorithm, running on a cluster with thirty-two workers."
    const Y0 = 380, P = 130;
    const nm = names(tl, root, Y0, P);
    const tT = cue('tools');
    show(tl, nm[2], tT - 0.2, 12);
    show(tl, nm[0], 15.6, 12);
    const n0 = lab(root, LX, Y0 + 38, 'the earlier fast algorithm');
    show(tl, n0, 16.3);
    show(tl, nm[1], 17.8, 12);
    const n1 = lab(root, LX, Y0 + P + 38, 'the simple algorithm, distributed: 32 workers');
    show(tl, n1, 18.4);
    // "Their numbers are the ones reported with the distributed tool, on that cluster's hardware. Boa's are from one
    // core of a laptop."
    const tCa = cue('caveat');
    const cav = mixed(root, LX, 850, [['CoPaR', 'serif'], [' and ', null], ['DCPR', 'serif'], [': as reported, on the cluster\'s hardware', null]]);
    show(tl, cav, tCa - 0.1);
    const n2 = lab(root, LX, Y0 + 2 * P + 38, 'one core of a laptop');
    show(tl, n2, 29.3);

    // "On the random benchmarks, roughly: where the earlier tool takes ten minutes, the cluster takes one minute,
    // and Boa takes one second." Log scale from 1 s; 3000 s at full length (wlan's 49 minutes fits).
    const tR = cue('rule');
    hide(tl, s1, tR - 0.3); hide(tl, s2, tR - 0.3);
    const rule = lab(root, LX, 160, 'random benchmarks, roughly', { color: C.ink });
    show(tl, rule, tR - 0.05);
    for (const e of [n0, n1, n2]) hide(tl, e, tR - 0.3);
    const bars = BX.bars(tl, root, 760, Y0, [
      { name: 'CoPaR', value: 600, text: '10 minutes' },
      { name: 'DCPR', value: 60, text: '1 minute' },
      { name: 'Boa', value: 1, text: '1 second', good: true },
    ], { scale: 'log', min: 1, max: 3000, w: 800, h: 40, pitch: P, minLen: 16, names: false, textSize: 36 });
    bars.grow(35.2, { rows: [0] });
    bars.grow(36.7, { rows: [1], stagger: 0 });
    bars.grow(38.4, { rows: [2], stagger: 0 });

    // "On one of the real models, the cluster needs almost an hour. Boa needs less than a second."
    const tWl = cue('wlan');
    tl.to(rule, { o: 0 }, tWl - 0.3, 0.3, E.in);
    const wl = lab(root, LX, 160, 'a real model: 1.6 million states', { color: C.ink });
    show(tl, wl, tWl);
    // the random benchmarks' bars leave with their heading; the real model's arrive as they are said
    for (const i of [0, 1, 2]) for (const e of [bars.rows[i].bar, bars.rows[i].text]) tl.to(e, { o: 0 }, tWl - 0.3, 0.3, E.in);
    bars.replace(0, 'out of memory', C.bad, 42.3);
    bars.set(1, { value: 2960, text: '49 minutes' }, 42.2, { dur: 0.05 });
    bars.set(2, { value: 0.81, text: '0.8 seconds' }, 43.9, { dur: 0.05 });
    for (const e of [bars.rows[1].bar, bars.rows[1].text]) tl.to(e, { o: 1 }, 42.8, 0.5, E.out);
    for (const e of [bars.rows[2].bar, bars.rows[2].text]) tl.to(e, { o: 1 }, 44.6, 0.5, E.out);
  });

  // ============================================ bench_b =======================================================
  scene('bench_b', ({ tl, root, cue }) => {
    // "Memory often decides whether a machine can be minimized at all."
    const mem = lab(root, LX, 140, 'memory', { color: C.ink });
    show(tl, mem, cue('memq') - 0.2);
    // "The biggest benchmark has over a million states, and almost two hundred million transitions."
    const tB = cue('big');
    const bl = BX.cline(root, CX, 206, [['1.3 million states', null], [' · 195 million transitions', null]], BX.SERIF(56));
    bl.parts.forEach(p => tl.set(p, { o: 0 }, 0));
    show(tl, bl.parts[0], 6.2, 14, 0.6); show(tl, bl.parts[1], 8.3, 14, 0.6);
    const bigL = lab(root, CX, 292, 'the biggest benchmark', { align: 'center' });
    show(tl, bigL, tB - 0.1);

    const Y0 = 420, P = 130, BXX = 480;
    const nm = names(tl, root, Y0, P);
    // "The earlier tool runs out of memory on it."
    const tO = cue('out');
    show(tl, nm[0], tO - 0.2, 12);
    const oom = lab(root, BXX, Y0 - 20, 'out of memory (16 gb)', { size: 34, color: C.bad });
    show(tl, oom, 12.2);
    // "The cluster handles it, with about seven gigabytes on each of its thirty-two workers." Linear scale: DCPR
    // 7092 MB on each of 32 workers, Boa 1647 MB.
    const tCl = cue('cl');
    // (the red stays full: red dimmed reads as pink, a colour with no meaning here)
    tl.to(nm[0], { o: 0.45 }, tCl - 0.2, 0.5);
    show(tl, nm[1], tCl - 0.2, 12);
    const bars = BX.bars(tl, root, BXX, Y0 + P, [
      { name: 'DCPR', value: 7092 * 32, text: '7 GB × 32 workers ≈ 227 GB', segments: 32 },
      { name: 'Boa', value: 1647, text: '1.6 GB', good: true },
    ], { scale: 'linear', w: 660, h: 40, pitch: P, minLen: 10, names: false, textSize: 36 });
    // the bar is built worker by worker: its 32 pieces arrive one after another
    const dBar = bars.rows[0].bar, pieces = [...dBar.children];
    tl.set(dBar, { sx: 1 }, 0.01); tl.set(dBar, { o: 1 }, 15.6);
    pieces.forEach((q, i) => { tl.set(q, { o: 0 }, 0); tl.to(q, { o: 1 }, 15.6 + i * 0.075, 0.2); });
    tl.fromTo(bars.rows[0].text, { o: 0 }, { o: 1 }, 15.6 + 32 * 0.075, 0.4);
    // "Boa uses under two gigabytes in total, most of it for the machine itself."
    const tBo = cue('boa');
    tl.to(bars.rows[0].bar, { o: 0.6 }, tBo - 0.2, 0.5);
    show(tl, nm[2], tBo - 0.2, 12);
    bars.grow(20.1, { rows: [1], dur: 0.4 });
    const most = lab(root, BXX, Y0 + 2 * P + 38, 'mostly the machine itself');
    show(tl, most, 22.3);
  });

  // ============================================ bench_c =======================================================
  // Table 3: [states, mCRL2 s, Boa s], in the table's order (by number of states)
  const VLTS = [
    [52268, 0.31, 0.04], [65537, 6.62, 0.14], [66929, 2.56, 0.08], [69754, 0.93, 0.04], [83436, 0.38, 0.04],
    [116456, 0.47, 0.06], [142472, 0.85, 0.08], [164865, 1.92, 0.23], [166464, 0.81, 0.08], [214202, 0.63, 0.15],
    [371804, 0.38, 0.11], [386496, 0.67, 0.08], [566640, 6.19, 0.44], [574057, 18.84, 2.41], [720247, 0.38, 0.05],
    [1112490, 8.86, 0.78], [2165446, 10.72, 1.52], [2416632, 14.87, 1.56], [2581374, 31.95, 2.30],
    [4220790, 31.82, 2.87], [4338672, 34.89, 3.12], [6020550, 34.91, 4.11], [6120718, 15.56, 2.37],
    [7838608, 231.08, 17.43], [8082905, 72.45, 3.79], [11026932, 60.57, 6.26], [12323703, 63.49, 8.16],
    [33949609, 312.11, 35.41],
  ];

  scene('bench_c', ({ tl, root, cue }) => {
    // "What about a specialized tool? For plain transition systems, Boa is compared with a mature verification
    // toolset, on a standard collection of very large transition systems."
    const sw = (y, col) => box(root, 166, y - 20, { width: '12px', height: '40px', borderRadius: '3px', background: col });
    const mY = 200, bY = 280;
    const mName = box(root, LX, mY - 29, Object.assign(BX.SERIF(48), { whiteSpace: 'pre' }), 'mCRL2');
    const mSw = sw(mY, C.dim);
    for (const e of [mName, mSw]) show(tl, e, cue('spec') + 0.9);
    const mL = lab(root, 400, mY - 19, 'a verification toolset: transition systems');
    show(tl, mL, 6.0);
    const bName = box(root, LX, bY - 29, Object.assign(BX.SERIF(48), { whiteSpace: 'pre', color: C.good }), 'Boa');
    const bSw = sw(bY, C.good);
    for (const e of [bName, bSw]) show(tl, e, 4.5);
    const vl = lab(root, 1720, bY - 19, '28 very large transition systems (vlts)', { align: 'right' });
    show(tl, vl, 8.6);

    // "On every benchmark in the table, Boa is faster, typically by about ten times, and it uses several times
    // less memory." A logarithmic time axis from 0.01 s (the baseline) to 1000 s (the top).
    const tF = cue('faster');
    const X0 = 330, X1 = 1720, Y0 = 350, YB = 700, DEC = (YB - Y0) / 5;
    const yOf = t => YB - DEC * Math.log10(t / 0.01);
    const svg = BX.svg(root);
    const axis = [];
    [[0.1, '0.1 s'], [1, '1 s'], [10, '10 s'], [100, '100 s']].forEach(([t, s]) => {
      const y = yOf(t);
      const gl = BX.line(tl, svg, X0 - 10, y, X1, y, { head: 0, stroke: C.faint, width: 1.5 });
      const l = box(root, 0, y - 17, Object.assign(BX.LABEL(28), { textTransform: 'none', width: (X0 - 24) + 'px', textAlign: 'right', whiteSpace: 'pre', lineHeight: '34px' }), s);
      axis.push(gl.path, l);
      tl.set(l, { o: 0 }, 0);
      tl.to(gl.path, { draw: 1 }, tF - 0.2, 0.6, E.io);
      show(tl, l, tF - 0.1, 6);
    });
    const base = BX.line(tl, svg, X0 - 10, YB, X1, YB, { head: 0, stroke: C.ink, width: 2 });
    tl.to(base.path, { draw: 1 }, tF - 0.25, 0.6, E.io);
    const n = VLTS.length, pitch = (X1 - X0) / n, bw = 18, gap = 4;
    VLTS.forEach(([, tm, tb], i) => {
      const x = X0 + i * pitch + (pitch - 2 * bw - gap) / 2;
      const mk = (xx, t, col) => {
        const h = YB - yOf(t);
        const b = box(root, xx, YB - h, { width: bw + 'px', height: h + 'px', background: col, borderRadius: '3px 3px 0 0', transformOrigin: 'center bottom' });
        tl.set(b, { sy: 0, o: 0 }, 0);
        const at = tF + 0.3 + i * 0.1;
        tl.set(b, { o: 1 }, at); tl.to(b, { sy: 1 }, at, 0.6, E.out5);
      };
      mk(x, tm, C.dim); mk(x + bw + gap, tb, C.good);
    });
    const L1 = 728, L2 = 790, L3 = 852;
    show(tl, lab(root, X0, L1, 'typically about 10× faster', { color: C.good }), 16.6);
    show(tl, lab(root, 1100, L1, 'several times less memory', { color: C.good }), 18.4);
    // "And the two tools find the same number of blocks every time."
    const tA = cue('agree');
    BX.tick(tl, svg, X0 + 16, L2 + 19, 36, tA + 0.9, { width: 5 });
    show(tl, lab(root, X0 + 56, L2, 'the same number of blocks, every time', { color: C.ink }), tA + 0.9);
    // "To be fair: that toolset also supports other notions of equivalence, which this algorithm does not cover."
    const tFa = cue('fair');
    show(tl, mixed(root, X0, L3, [['mCRL2', 'serif'], [' also supports other notions of equivalence', null]]), 26.4);
  });

  // ============================================ cool_three ====================================================
  scene('cool_three', ({ tl, root, cue }) => {
    // "So the general algorithm is the fast one."
    const so = BX.cserif(root, CX, 206, 'the general algorithm is the fast one', 64);
    show(tl, so, cue('so') - 0.2, 18, 0.7);
    // "Why? It keeps almost nothing besides the machine ... works on a combined shape directly ... one pass accounts
    // for everything that has changed since its last visit"
    const svg = BX.svg(root);
    const rows = [];
    [['r1', 'almost nothing besides the machine'], ['r2', 'a combined shape, directly'], ['r3', 'one pass sees every change since the last visit']].forEach(([c, t], i) => {
      const y = 420 + i * 100, at = cue(c) - 0.15;
      const g = group(root), gs = BX.svg(g);
      const l = lab(g, 250, y - 22, t, { size: 36, color: C.ink });
      show(tl, l, at);
      BX.tick(tl, gs, 196, y, 38, at + 0.35, { width: 5 });
      rows.forEach(r => tl.to(r, { o: 0.6 }, at, 0.5));
      if (i === 0) tl.to(so, { o: 0.6 }, at, 0.5);
      rows.push(g);
    });
    // "These benchmarks do not even show its advantage over the simple algorithm in full: the random ones need
    // only a few rounds."
    tl.to(rows[2], { o: 0.6 }, 28.8, 0.5);
    show(tl, lab(root, 250, 730, 'the random benchmarks need only a few rounds'), 28.9);
  });

  // ============================================ limits ========================================================
  scene('limits', ({ tl, root, cue }) => {
    show(tl, lab(root, LX, 180, 'left open', { color: C.ink }), cue('lim') - 0.2);
    // "Other notions of equivalence, such as trace equivalence and branching bisimilarity, do not fit this
    // definition directly. They are future work."
    const up = group(root);
    show(tl, serifL(up, LX, 330, 'trace equivalence', 52), 4.5, 14, 0.7);
    show(tl, serifL(up, LX, 405, 'branching bisimilarity', 52), 5.7, 14, 0.7);
    show(tl, lab(up, LX, 500, 'future work'), 10.9);
    // "And in theory, the extra cost of computing signatures is the price of being general."
    const tF = cue('factor');
    tl.to(up, { o: 0.5 }, tF - 0.1, 0.5);
    const k = box(root, LX, 660 - 36, Object.assign(BX.MONO(56), { whiteSpace: 'pre', color: C.code, lineHeight: '72px' }), 'k · M log N');
    show(tl, k, 14.4, 14, 0.6);
    show(tl, lab(root, LX, 712, 'in theory: the price of being general'), 16.2);
  });
})();

// ==== ../src/film.js ====
(function (addEventListener) {
// Puts the scenes on one clock. window.seek(t) shows the film at t seconds; window.DURATION is its length.
'use strict';
(function () {
  const { W, H, C, E, Timeline, SCENES } = Film;
  const stage = document.getElementById('stage');

  // Timings come from the narration (build/timeline.js). Without it, estimate from the words, so that scenes
  // can be designed before any audio exists.
  function estimate(narr) {
    let t = 0; const scenes = [];
    for (const n of narr) {
      const pre = n.pre ?? 0.6, post = n.post ?? 0.8, cues = {};
      const plain = n.text.replace(/\{[^}]*\}/g, '');
      const wps = 2.55, words = plain.trim().split(/\s+/).length, audio = words / wps;
      let seen = 0, re = /\{([^}]*)\}|([^{]+)/g, m;
      while ((m = re.exec(n.text))) {
        if (m[1] !== undefined) cues[m[1]] = pre + (seen / Math.max(1, plain.length)) * audio;
        else seen += m[2].length;
      }
      scenes.push({ id: n.id, start: t, dur: pre + audio + post, audio, pre, post, cues, chapter: n.chapter || '' });
      t += pre + audio + post;
    }
    return { scenes, total: t, estimated: true };
  }
  const T = window.TIMELINE || estimate(window.NARRATION);

  // ---- the room: background, a slow drift of dots, a vignette ---------------------------------------------
  const room = new Timeline();
  box(stage, 0, 0, { width: W + 'px', height: H + 'px', background: `radial-gradient(1200px 800px at 18% 12%, ${C.glow1} 0%, ${alpha(C.glow1, 0)} 60%), radial-gradient(1100px 900px at 88% 96%, ${C.glow2} 0%, ${alpha(C.glow2, 0)} 62%), ${C.bg}` });
  const dots = box(stage, -80, -80, { width: (W + 160) + 'px', height: (H + 160) + 'px', backgroundImage: `radial-gradient(${C.dots} 1.2px, transparent 1.6px)`, backgroundSize: '44px 44px' });
  room.fromTo(dots, { x: 0, y: 0 }, { x: -44, y: -22 }, 0, T.total, E.lin);
  const sceneLayer = box(stage, 0, 0, { width: W + 'px', height: H + 'px' });
  box(stage, 0, 0, { width: W + 'px', height: H + 'px', background: `radial-gradient(ellipse at center, ${alpha(C.vignette, 0)} 55%, ${C.vignette} 100%)`, pointerEvents: 'none' });

  // ---- chrome: the chapter's name, top left, and a hairline of progress along the bottom -----------------
  const chapEl = box(stage, 160, 76, { fontFamily: 'var(--sans)', fontSize: '22px', fontWeight: 600, letterSpacing: '0.2em', textTransform: 'uppercase', color: C.dim, whiteSpace: 'pre' }, '');
  box(stage, 0, H - 4, { width: W + 'px', height: '4px', background: C.track });
  const bar = box(stage, 0, H - 4, { width: W + 'px', height: '4px', background: C.dim, transformOrigin: 'left center', opacity: 0.5 });
  room.fromTo(bar, { sx: 0 }, { sx: 1 }, 0, T.total, E.lin);
  let prevChap = '';
  for (const s of T.scenes) {
    if (s.chapter !== prevChap) {
      room.to(chapEl, { o: 0 }, Math.max(0, s.start - 0.25), 0.25);
      room.text(chapEl, s.chapter, s.start);
      if (s.chapter) room.to(chapEl, { o: 1 }, s.start + Math.max(0.5, s.pre - 0.4), 0.6);
      prevChap = s.chapter;
    }
  }
  room.set(chapEl, { o: 0 }, 0);

  // ---- chapter cards: the chapter's name, large, for a moment before its first scene begins --------------
  let chapNo = 0, prevC = '';
  for (const s of T.scenes) {
    if (s.chapter && s.chapter !== prevC && s.pre >= 1.5) {
      chapNo++;
      const num = box(stage, 160, 396, { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 600, letterSpacing: '0.24em', color: C.dim, whiteSpace: 'pre' }, String(chapNo).padStart(2, '0'));
      const big = box(stage, 156, 440, { fontFamily: 'var(--serif)', fontSize: '104px', lineHeight: 1.1, color: C.ink, whiteSpace: 'pre', letterSpacing: '-0.012em' }, s.chapter);
      const rule = box(stage, 160, 590, { width: '220px', height: '2px', background: C.faint, transformOrigin: 'left center' });
      for (const e of [num, big, rule]) room.set(e, { o: 0 }, 0);
      room.fromTo(num, { o: 0, y: 14 }, { o: 1, y: 0 }, s.start + 0.1, 0.5, E.out5);
      room.fromTo(big, { o: 0, y: 30 }, { o: 1, y: 0 }, s.start + 0.16, 0.7, E.out5);
      room.fromTo(rule, { o: 1, sx: 0 }, { o: 1, sx: 1 }, s.start + 0.3, 0.7, E.io);
      for (const e of [num, big, rule]) room.to(e, { o: 0, y: -18 }, s.start + s.pre - 0.5, 0.4, E.in);
    }
    prevC = s.chapter;
  }

  // ---- the scenes ---------------------------------------------------------------------------------------
  // A scene covers one narration segment, or several in a row (so that what is on screen can stay while the
  // narrator goes on). Its clock starts at its first segment; cue('name') finds a cue in any of its segments,
  // cue('segment.name') in one of them; seg('segment') is that segment's start on the scene's clock.
  const built = [], covered = new Set();
  for (const sc of SCENES) {
    const ids = Array.isArray(sc.id) ? sc.id : [sc.id];
    const segs = ids.map(id => T.scenes.find(s => s.id === id));
    if (segs.some(x => !x)) { console.warn('scene without narration', ids.join(',')); continue; }
    ids.forEach(id => covered.add(id));
    const start = segs[0].start, dur = segs.reduce((a, s) => a + s.dur, 0);
    const root = box(sceneLayer, 0, 0, { width: W + 'px', height: H + 'px', display: 'none' });
    const tl = new Timeline();
    const cue = (name, fallback) => {
      const [a, b] = name.includes('.') ? name.split('.') : [null, name];
      for (const s of segs) if ((!a || s.id === a) && s.cues[b] !== undefined) return s.start - start + s.cues[b];
      console.warn(`cue "${name}" missing in ${ids.join(',')}`); return fallback ?? 0;
    };
    const seg = id => { const s = segs.find(x => x.id === id); return s ? s.start - start : 0; };
    const info = { start, dur, pre: segs[0].pre, segs };
    // a scene that throws is left out and reported, so that one broken file does not blank the others
    let res;
    try { res = sc.build({ tl, root, cue, seg, dur, info, end: dur }) || {}; }
    catch (e) { console.error(`scene ${ids.join(',')} failed: ${e.message}`); root.remove(); continue; }
    // everything in a scene leaves in its last moments unless the scene says otherwise
    if (!res.keep) { tl.set(root, { o: 1 }, 0); tl.to(root, { o: 0 }, dur - 0.4, 0.4, E.in); }
    built.push({ sc, info, root, tl });
  }
  for (const s of T.scenes) if (!covered.has(s.id)) console.warn('narration without scene', s.id);

  window.DURATION = T.total;
  window.TIMING = T;
  window.seek = function (t) {
    room.seek(t);
    for (const b of built) {
      const lt = t - b.info.start, on = lt >= 0 && lt < b.info.dur;
      b.root.style.display = on ? 'block' : 'none';
      if (on) b.tl.seek(lt);
    }
    return true;
  };
  // every declared face is loaded before the first frame: a face is otherwise fetched only when text first uses it,
  // and a render worker that starts on such a frame would draw it in the fallback
  window.ready = Promise.all([...document.fonts].map(f => f.load().catch(() => null))).then(() => document.fonts.ready).then(() => true);

  // a scrubber for working on scenes in a browser: ?t=12.5 or ?scene=refute1, arrows to step, space to play
  const q = new URLSearchParams(location.search);
  let t0 = parseFloat(q.get('t') || '0');
  if (q.get('scene')) { const s = T.scenes.find(x => x.id === q.get('scene')); if (s) t0 = s.start + parseFloat(q.get('dt') || '0'); }
  if (q.get('fit') !== '0') { const fit = () => { const k = Math.min(innerWidth / W, innerHeight / H); stage.style.transformOrigin = '0 0'; stage.style.transform = `scale(${k})`; }; addEventListener('resize', fit); fit(); }
  document.fonts.ready.then(() => window.seek(t0));
  let playing = false, last = 0, cur = t0;
  addEventListener('keydown', e => {
    if (e.key === ' ') { playing = !playing; last = performance.now(); requestAnimationFrame(loop); }
    if (e.key === 'ArrowRight') { cur += e.shiftKey ? 5 : 0.5; window.seek(cur); }
    if (e.key === 'ArrowLeft') { cur = Math.max(0, cur - (e.shiftKey ? 5 : 0.5)); window.seek(cur); }
  });
  function loop(now) { if (!playing) return; cur += (now - last) / 1000; last = now; if (cur > T.total) { playing = false; return; } window.seek(cur); requestAnimationFrame(loop); }
})();

}).call(window, function (type, fn, opts) {
  if (type !== 'keydown' && type !== 'resize') window.addEventListener(type, fn, opts);
});

// ==== build/captions.js ====
window.CAPTIONS = [[0.8, 2.76, "Here is a small machine:"], [2.8, 5.8, "a finite automaton with five states."], [5.84, 8.84, "Two of its states behave in exactly the same way,"], [8.88, 10.52, "and so do two others."], [10.56, 13.12, "Merge them, and the machine has three states,"], [13.16, 15.08, "and does what it did before."], [15.12, 17.08, "That is minimization."], [17.12, 20.48, "Tools that verify systems often minimize first,"], [20.52, 23.56, "because a smaller machine is cheaper to analyse."], [23.6, 26.16, "There are many kinds of machine like this:"], [26.2, 28.36, "transition systems, Markov chains,"], [28.4, 29.48, "and more."], [29.52, 32.6, "For a long time, each kind had its own minimization"], [32.64, 33.72, "algorithm."], [33.76, 36.36, "A general theory, called coalgebra,"], [36.4, 39.08, "promises one algorithm for all of them."], [39.12, 41.72, "But the general algorithm that existed was slow"], [41.76, 44.48, "in practice, needed a great deal of memory,"], [44.52, 47.32, "and did not cover every kind of machine."], [47.36, 49.68, "This video is about a new algorithm,"], [49.72, 52.6, "and a tool called Boa that implements it."], [52.64, 55.12, "It covers all of these kinds and more,"], [55.16, 57.32, "and it is faster than the earlier tools,"], [57.36, 59.08, "with far less memory."], [59.12, 62.2, "By the end, we will have run the algorithm by hand,"], [62.24, 65.38, "and we will know why it is fast."], [65.48, 67.2, "Here is what is coming."], [67.24, 70.88, "First, one way to describe all these machines."], [70.92, 74.56, "Then what it means for two states to be equivalent."], [74.6, 78.08, "Then a simple algorithm that is correct but slow,"], [78.12, 80.8, "and two ideas that make it fast."], [80.84, 83.52, "Then how kinds of machine are put together from"], [83.56, 87.5, "a few pieces, and the measurements."], [88.0, 92.5, "Fast coalgebraic bisimilarity minimization."], [94.5, 96.94, "Start with the finite automaton."], [96.98, 98.86, "The usual picture has states,"], [98.9, 101.1, "and arrows labelled with letters."], [101.14, 103.66, "A double border means accepting."], [103.7, 106.78, "Now look at it from the point of view of one state."], [106.82, 109.18, "State three is not accepting."], [109.22, 111.9, "On the letter A it goes to state five,"], [111.94, 114.94, "and on the letter B it goes to itself."], [114.98, 118.06, "So state three comes with three pieces of data:"], [118.1, 121.18, "whether it is accepting, where the letter A leads,"], [121.22, 123.26, "and where the letter B leads."], [123.3, 125.9, "False, five, three."], [125.94, 127.74, "Write that down for every state,"], [127.78, 130.98, "and the table is the whole automaton."], [131.02, 134.5, "A transition system has no letters and no accepting"], [134.54, 135.42, "states."], [135.46, 138.9, "A state just has a set of states it can step to."], [138.94, 140.98, "State three can step to three,"], [141.02, 142.87, "four, or five."], [142.91, 144.98, "State five cannot step at all:"], [145.02, 146.94, "its set is empty."], [146.98, 150.34, "In a Markov chain, a state steps at random."], [150.38, 153.3, "State one goes to state two with probability one"], [153.34, 156.18, "third, and to state three with probability two"], [156.22, 157.14, "thirds."], [157.18, 160.38, "So its data is a probability distribution over"], [160.42, 162.18, "states, together with a flag,"], [162.22, 164.78, "true or false."], [164.82, 167.58, "The pattern is the same each time."], [167.62, 170.42, "There is a set of states, and each state has a"], [170.46, 173.18, "piece of data with states inside it."], [173.22, 176.38, "We call it the state's successor structure."], [176.42, 179.18, "What differs is the shape of that data:"], [179.22, 182.7, "a flag and two states; a set of states;"], [182.74, 185.26, "a flag and a distribution."], [185.3, 188.7, "These shapes are built from the same few pieces:"], [188.74, 192.38, "flags, tuples, sets, distributions."], [192.42, 194.3, "That will matter later."], [194.34, 196.78, "The shape is the kind of machine."], [196.82, 200.49, "In category theory, such a shape is called a functor,"], [200.53, 204.14, "and a machine of that shape is called a coalgebra."], [204.18, 206.19, "That is the word in the title."], [206.23, 210.12, "We will not need more category theory than that."], [211.94, 214.46, "When are two states equivalent?"], [214.5, 217.5, "They should have equivalent successor structures."], [217.54, 220.54, "But those contain states, so the definition seems"], [220.58, 222.38, "to go in a circle."], [222.42, 225.26, "The way out is to start from a guess."], [225.3, 226.94, "Group the states into blocks,"], [226.98, 229.34, "and give each block a name."], [229.38, 231.66, "Then, in every successor structure,"], [231.7, 234.46, "replace each state by the name of its block."], [234.5, 237.74, "The guess is called stable if states in the same"], [237.78, 241.46, "block end up with exactly the same structure."], [241.5, 244.58, "Try it on the automaton, with the guess that states"], [244.62, 246.62, "two and three are equivalent,"], [246.66, 248.58, "and four and five."], [248.62, 251.22, "Call the block of two and three X,"], [251.26, 253.65, "the block of four and five Y,"], [253.69, 255.62, "and state one, on its own,"], [255.66, 256.74, "Z."], [256.78, 258.02, "State two had:"], [258.06, 260.18, "false, four, three."], [260.22, 261.46, "After renaming:"], [261.5, 263.78, "false, Y, X."], [263.82, 265.06, "State three had:"], [265.1, 267.14, "false, five, three."], [267.18, 268.34, "After renaming:"], [268.38, 270.9, "also false, Y, X."], [270.94, 272.18, "They agree."], [272.22, 274.02, "So do four and five."], [274.06, 276.7, "The guess is stable."], [276.74, 279.26, "The same test works for the other machines,"], [279.3, 280.86, "with one addition."], [280.9, 283.98, "In the transition system, guess that one and two"], [284.02, 286.54, "are equivalent, and three and four,"], [286.58, 288.38, "with five on its own."], [288.42, 290.62, "State one steps to two, three,"], [290.66, 291.66, "and four."], [291.7, 293.82, "After renaming, that is:"], [293.86, 295.58, "X, Y, Y."], [295.62, 299.42, "But this is a set, and a set does not hold duplicates."], [299.46, 301.66, "It is just X and Y."], [301.7, 304.38, "State two steps to one and four:"], [304.42, 305.9, "X and Y again."], [305.94, 307.18, "They agree."], [307.22, 309.58, "In the Markov chain, guess that two,"], [309.62, 311.61, "three, and five are equivalent,"], [311.65, 313.82, "and call their block X."], [313.86, 316.7, "State three goes to state two with probability"], [316.74, 319.93, "one quarter, to state five with one quarter,"], [319.97, 322.54, "and to state four with one half."], [322.58, 324.89, "Two and five are both in X,"], [324.93, 326.94, "so their probabilities are added:"], [326.98, 328.7, "one half to X."], [328.74, 331.5, "State two goes to itself and to four,"], [331.54, 332.78, "one half each:"], [332.82, 334.02, "the same."], [334.06, 336.75, "So renaming is followed by tidying up:"], [336.79, 340.76, "duplicates removed, probabilities added."], [340.86, 343.46, "This renaming, with its tidying up,"], [343.5, 347.06, "is essentially all we will ask of a kind of machine."], [347.1, 349.7, "Among the stable guesses, there is one with the"], [349.74, 351.14, "fewest blocks."], [351.18, 354.5, "Its blocks are the classes of equivalent states."], [354.54, 357.46, "For transition systems, this equivalence is known"], [357.5, 359.22, "as bisimilarity:"], [359.26, 361.3, "the other word in the title."], [361.34, 364.82, "For finite automata, it says that two states accept"], [364.86, 366.34, "the same language."], [366.38, 369.66, "And the minimized machine has one state for each"], [369.7, 371.12, "block."], [371.24, 373.32, "Notice what just happened."], [373.36, 375.8, "Language equivalence, bisimilarity,"], [375.84, 379.0, "and bisimilarity with probabilities are usually"], [379.04, 380.76, "defined separately."], [380.8, 382.88, "Here they are one definition,"], [382.92, 386.06, "seen in three different shapes."], [387.96, 390.88, "How do we find the best stable guess?"], [390.92, 393.08, "Start by being optimistic:"], [393.12, 395.28, "put all states in one block,"], [395.32, 396.0, "X."], [396.04, 398.08, "Compute every state's structure,"], [398.12, 399.84, "renamed by block."], [399.88, 403.33, "From here on we call that the state's signature."], [403.37, 406.35, "In the automaton, every signature now reads:"], [406.39, 409.39, "a flag, then X, X."], [409.43, 410.96, "But the flags differ."], [411.0, 414.52, "Three states say false, and two say true."], [414.56, 416.88, "So they cannot all be equivalent."], [416.92, 418.64, "Split the block in two:"], [418.68, 422.0, "the false ones stay X, and the true ones become"], [422.04, 423.72, "Y."], [423.76, 426.68, "Now do it again, with the new blocks."], [426.72, 428.2, "State one reads:"], [428.24, 430.36, "false, X, X."], [430.4, 432.28, "States two and three read:"], [432.32, 434.68, "false, Y, X."], [434.72, 436.2, "Four and five read:"], [436.24, 438.52, "true, Y, Y."], [438.56, 440.2, "Three different signatures,"], [440.24, 442.04, "so three blocks."], [442.08, 443.96, "State one gets a new name,"], [444.0, 445.08, "Z."], [445.12, 446.28, "Once more."], [446.32, 449.24, "This time every signature is the same as before,"], [449.28, 451.08, "so no block splits."], [451.12, 452.87, "The guess is stable."], [452.91, 455.48, "And because we only ever separated states that"], [455.52, 459.28, "had to be separated, it is the best one."], [459.32, 462.0, "Nothing here was special to automata."], [462.04, 464.72, "The loop only computes signatures and compares"], [464.76, 465.36, "them."], [465.4, 467.04, "But look at the cost."], [467.08, 470.64, "Every round recomputes the signature of every state,"], [470.68, 472.8, "even when it cannot have changed."], [472.84, 474.8, "And there can be many rounds."], [474.84, 477.28, "In a machine shaped like a long chain,"], [477.32, 480.28, "each round splits off a single state."], [480.32, 484.4, "With N states, that is N rounds of N signatures:"], [484.44, 485.6, "N squared."], [485.64, 489.5, "For a million states, a million million."], [491.4, 492.8, "The first idea:"], [492.84, 496.08, "do not recompute what cannot have changed."], [496.12, 498.64, "A state's signature depends only on the blocks"], [498.68, 500.24, "of its successors."], [500.28, 503.2, "So it can change only when one of its successors"], [503.24, 505.32, "moves to a different block."], [505.36, 508.0, "Call a state dirty when that has happened,"], [508.04, 510.92, "and clean once its signature has been computed"], [510.96, 511.52, "again."], [511.56, 514.59, "Only dirty states need a new signature."], [514.63, 518.16, "And the clean states of a block all share one signature:"], [518.2, 520.24, "they had the same signature when the block was"], [520.28, 523.52, "formed, and nothing they depend on has moved."], [523.56, 527.18, "So computing it for one of them is enough."], [527.28, 529.99, "The second idea is about names."], [530.03, 533.04, "When a block splits, one part can keep the old"], [533.08, 535.4, "name, and the others get new names."], [535.44, 537.56, "We are free to choose which."], [537.6, 540.44, "Let the largest part keep the old name."], [540.48, 543.08, "Then the states in the largest part have not moved"], [543.12, 545.72, "at all, and nothing that points to them becomes"], [545.76, 546.76, "dirty."], [546.8, 550.4, "Only the smaller parts cost anything."], [550.44, 552.72, "Why does that help so much?"], [552.76, 556.16, "Take a set of N things, and keep splitting it."], [556.2, 557.84, "Follow one element."], [557.88, 560.19, "Each time it lands in a smaller part,"], [560.23, 563.92, "the set around it is at most half as big as before."], [563.96, 567.08, "That can happen only about log N times."], [567.12, 568.48, "For a million elements:"], [568.52, 570.04, "twenty times."], [570.08, 573.12, "This is an old trick in automaton minimization,"], [573.16, 575.76, "known as the half the size trick."], [575.8, 580.08, "So a state gets a new name at most log N times."], [580.12, 582.72, "Each new name makes dirty the states that point"], [582.76, 584.8, "to it, its predecessors:"], [584.84, 587.76, "one signature for each incoming edge."], [587.8, 590.0, "Altogether, with M edges:"], [590.04, 594.94, "M times log N signatures, instead of N squared."], [595.06, 597.38, "Here is the whole algorithm."], [597.42, 599.34, "Put all states in one block,"], [599.38, 601.42, "and mark them all dirty."], [601.46, 602.94, "Then repeat."], [602.98, 605.34, "Pick a block that has dirty states."], [605.38, 607.9, "Compute the signatures of its dirty states,"], [607.94, 610.06, "and of one clean state."], [610.1, 612.06, "Now they are all clean."], [612.1, 613.93, "Split the block by signature,"], [613.97, 616.62, "and let the largest part keep the name."], [616.66, 619.58, "Mark as dirty every predecessor of a state that"], [619.62, 621.1, "got a new name."], [621.14, 624.12, "Stop when nothing is dirty."], [624.24, 626.2, "Run it on the automaton."], [626.24, 630.36, "One block, X, and all five states dirty."], [630.4, 634.28, "Five signatures, and now all five are clean."], [634.32, 637.08, "Three say false, two say true."], [637.12, 638.92, "The three are the larger part,"], [638.96, 642.2, "so they stay X, and states four and five become"], [642.24, 643.56, "block Y."], [643.6, 646.0, "Who points to four or five?"], [646.04, 649.16, "States two, three, four, and five."], [649.2, 650.76, "They become dirty."], [650.8, 652.36, "State one does not."], [652.4, 654.88, "It stays clean."], [654.92, 656.56, "Take block X."], [656.6, 659.28, "Two dirty states, two and three,"], [659.32, 661.04, "and one clean state."], [661.08, 662.64, "Three signatures."], [662.68, 664.24, "Two and three read:"], [664.28, 666.64, "false, Y, X."], [666.68, 668.0, "State one reads:"], [668.04, 670.36, "false, X, X."], [670.4, 671.92, "The block splits."], [671.96, 674.0, "Two and three are the larger part,"], [674.04, 676.96, "so they keep the name X, and state one becomes"], [677.0, 678.24, "block Z."], [678.28, 680.24, "Who points to state one?"], [680.28, 681.12, "Nobody."], [681.16, 683.16, "So nothing becomes dirty."], [683.2, 684.64, "Take block Y."], [684.68, 687.23, "Two dirty states, two signatures,"], [687.27, 688.32, "and they agree:"], [688.36, 689.52, "no split."], [689.56, 690.8, "Nothing is dirty."], [690.84, 691.84, "Done."], [691.88, 694.64, "That was ten signatures, where the simple algorithm"], [694.68, 697.42, "computed fifteen."], [697.54, 700.22, "Notice what the algorithm never did."], [700.26, 703.02, "It never looked inside a signature."], [703.06, 704.97, "It only asked for signatures,"], [705.01, 706.38, "and compared them."], [706.42, 709.18, "So it works for any kind of machine that can compute"], [709.22, 710.84, "them."], [712.66, 715.58, "Counting signatures is not the whole cost."], [715.62, 718.06, "If splitting a block meant walking over all of"], [718.1, 720.49, "its states, the clean ones too,"], [720.53, 723.26, "the M log N bound would be lost."], [723.3, 725.66, "So the states are kept in one array,"], [725.7, 727.34, "each block a stretch of it,"], [727.38, 730.18, "with its clean states first and its dirty states"], [730.22, 731.42, "at the end."], [731.46, 734.01, "Marking a state dirty is one swap,"], [734.05, 736.54, "with the last clean state of its block."], [736.58, 740.22, "Splitting a block rearranges only its dirty states."], [740.26, 743.1, "So a split costs time proportional to the number"], [743.14, 745.9, "of dirty states, however many clean ones there"], [745.94, 747.54, "are."], [747.58, 750.34, "The algorithm also needs little memory."], [750.38, 753.46, "It keeps the machine, each state's predecessors,"], [753.5, 755.94, "and this structure for the blocks."], [755.98, 758.66, "The earlier fast algorithms keep more:"], [758.7, 760.34, "a counter for each transition,"], [760.38, 761.7, "for example."], [761.74, 763.94, "In theory, there is a price."], [763.98, 766.66, "Computing a signature looks at all of a state's"], [766.7, 767.78, "successors."], [767.82, 769.86, "The fastest earlier algorithms,"], [769.9, 771.62, "which ask more of the shape,"], [771.66, 773.42, "avoid that cost."], [773.46, 775.62, "In the measurements, as we will see,"], [775.66, 778.56, "this price does not show."], [780.38, 783.3, "What does a kind of machine have to provide?"], [783.34, 785.38, "Essentially one function:"], [785.42, 787.86, "given a state and the current blocks,"], [787.9, 789.7, "return the state's signature."], [789.74, 792.22, "But these functions are not written one kind of"], [792.26, 793.98, "machine at a time."], [794.02, 796.05, "Shapes are built from a few pieces,"], [796.09, 798.66, "and each piece knows how to rename."], [798.7, 801.46, "A tuple renames each of its parts."], [801.5, 803.54, "A set renames its elements,"], [803.58, 806.02, "sorts them, and drops duplicates."], [806.06, 808.74, "A distribution, or weights of any kind:"], [808.78, 811.62, "rename, sort, and add up the weights that land"], [811.66, 812.98, "in the same block."], [813.02, 816.86, "A flag or a label stays as it is."], [816.9, 819.26, "The pieces fit inside one another,"], [819.3, 821.18, "and so do their functions."], [821.22, 824.3, "The automaton's shape is a tuple of a flag and"], [824.34, 825.74, "two states."], [825.78, 828.94, "Put a set around pairs of a label and a state,"], [828.98, 831.74, "and you have a labelled transition system."], [831.78, 833.9, "Put a set around distributions,"], [833.94, 836.3, "and you have a Markov decision process,"], [836.34, 839.26, "which has both choice and chance."], [839.3, 842.02, "One of the benchmark models we will see has this"], [842.06, 842.86, "shape:"], [842.9, 845.66, "a number, with a set of pairs of a number and a"], [845.7, 847.02, "distribution."], [847.06, 849.42, "Four pieces, nested."], [849.46, 851.98, "So to describe a new kind of machine,"], [852.02, 854.62, "you usually just write down its shape."], [854.66, 857.26, "Its signature function follows the shape:"], [857.3, 860.92, "the outer piece calls the inner ones."], [861.02, 864.18, "The earlier fast algorithm could not take a combined"], [864.22, 865.7, "shape as it is."], [865.74, 869.17, "It had to cut every state into intermediate states,"], [869.21, 872.34, "between the pieces, which made the machine larger."], [872.38, 875.22, "Here, one state stays one state."], [875.26, 877.11, "And when no combination fits,"], [877.15, 879.06, "a new piece can be added."], [879.1, 881.54, "One comes from logics about games:"], [881.58, 884.82, "a set of sets of states, in which any larger set"], [884.86, 886.34, "also belongs."], [886.38, 889.06, "The earlier algorithm, which needs a special way"], [889.1, 891.25, "of splitting blocks for every piece,"], [891.29, 893.46, "could not handle that shape at all."], [893.5, 896.74, "In Boa, a new piece is a small amount of Rust:"], [896.78, 900.08, "essentially its signature function."], [901.9, 903.46, "Now the measurements."], [903.5, 905.94, "The benchmarks are from earlier work:"], [905.98, 908.5, "models from a probabilistic model checker,"], [908.54, 911.7, "and large, randomly generated tree automata with"], [911.74, 912.82, "weights."], [912.86, 915.78, "Boa is compared with two general tools:"], [915.82, 917.73, "the earlier fast algorithm,"], [917.77, 920.58, "and a distributed version of the simple algorithm,"], [920.62, 923.54, "running on a cluster with thirty-two workers."], [923.58, 926.18, "Their numbers are the ones reported with the distributed"], [926.22, 928.82, "tool, on that cluster's hardware."], [928.86, 931.62, "Boa's are from one core of a laptop."], [931.66, 934.13, "On the random benchmarks, roughly:"], [934.17, 936.45, "where the earlier tool takes ten minutes,"], [936.49, 938.26, "the cluster takes one minute,"], [938.3, 940.66, "and Boa takes one second."], [940.7, 942.18, "On one of the real models,"], [942.22, 944.58, "the cluster needs almost an hour."], [944.62, 947.84, "Boa needs less than a second."], [947.94, 951.18, "Memory often decides whether a machine can be minimized"], [951.22, 952.22, "at all."], [952.26, 955.26, "The biggest benchmark has over a million states,"], [955.3, 958.38, "and almost two hundred million transitions."], [958.42, 961.26, "The earlier tool runs out of memory on it."], [961.3, 964.22, "The cluster handles it, with about seven gigabytes"], [964.26, 966.7, "on each of its thirty-two workers."], [966.74, 969.74, "Boa uses under two gigabytes in total,"], [969.78, 973.06, "most of it for the machine itself."], [973.1, 975.38, "What about a specialized tool?"], [975.42, 977.38, "For plain transition systems,"], [977.42, 980.9, "Boa is compared with a mature verification toolset,"], [980.94, 984.22, "on a standard collection of very large transition"], [984.26, 984.82, "systems."], [984.86, 986.9, "On every benchmark in the table,"], [986.94, 990.61, "Boa is faster, typically by about ten times,"], [990.65, 993.38, "and it uses several times less memory."], [993.42, 995.94, "And the two tools find the same number of blocks"], [995.98, 997.3, "every time."], [997.34, 998.26, "To be fair:"], [998.3, 1001.54, "that toolset also supports other notions of equivalence,"], [1001.58, 1004.8, "which this algorithm does not cover."], [1004.92, 1007.84, "So the general algorithm is the fast one."], [1007.88, 1008.88, "Why?"], [1008.92, 1011.52, "It keeps almost nothing besides the machine,"], [1011.56, 1013.28, "in a compact form."], [1013.32, 1015.84, "It works on a combined shape directly,"], [1015.88, 1018.35, "without cutting states into pieces."], [1018.39, 1020.24, "And when it comes back to a block,"], [1020.28, 1022.96, "one pass accounts for everything that has changed"], [1023.0, 1026.0, "since its last visit, where the earlier algorithm"], [1026.04, 1028.48, "handles each change separately."], [1028.52, 1031.12, "These benchmarks do not even show its advantage"], [1031.16, 1033.52, "over the simple algorithm in full:"], [1033.56, 1037.42, "the random ones need only a few rounds."], [1037.54, 1039.34, "What is left open?"], [1039.38, 1041.14, "Other notions of equivalence,"], [1041.18, 1044.67, "such as trace equivalence and branching bisimilarity,"], [1044.71, 1047.34, "do not fit this definition directly."], [1047.38, 1049.18, "They are future work."], [1049.22, 1053.02, "And in theory, the extra cost of computing signatures"], [1053.06, 1056.04, "is the price of being general."], [1057.86, 1060.66, "Many kinds of machine are one thing:"], [1060.7, 1064.22, "states, each with a structure that has states inside,"], [1064.26, 1066.42, "built from a few pieces."], [1066.46, 1069.02, "Equivalent states are found by guessing blocks,"], [1069.06, 1071.22, "renaming, and comparing."], [1071.26, 1074.58, "Doing that for every state in every round is too"], [1074.62, 1075.18, "slow."], [1075.22, 1077.79, "So recompute only the dirty states,"], [1077.83, 1081.18, "and let the largest part of a split keep its name."], [1081.22, 1084.06, "That takes M times log N signatures,"], [1084.1, 1086.58, "and little memory beyond the machine."], [1086.62, 1089.9, "The result is one tool for many kinds of machine,"], [1089.94, 1093.48, "faster than the tools it was measured against."], [1093.7, 1098.04, "Fast coalgebraic bisimilarity minimization."], [1098.1, 1100.5, "The paper has the formal definitions,"], [1100.54, 1102.38, "the data structure in full,"], [1102.42, 1106.44, "the complexity analysis, and all the measurements."]];
