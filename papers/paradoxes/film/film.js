// Paradoxes of Probabilistic Programming: the video: the film's scripts in one file, made by tools/web.py.

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
// The full-length film on "Paradoxes of Probabilistic Programming" (POPL 2021). One story: a program whose answer
// changes with the unit of measurement; what observe means (rejection) and how it is run (weights); why densities
// break it (three paradoxes); what the answer should be; the fix (observe an interval of infinitesimal width, and
// compute with infinitesimal probabilities); why that is right, and what it does to changes of scale.
// {name} marks a cue. Numbers are written as they are spoken. No person is named in the narration.
window.NARRATION = [
  // ------------------------------------------------------------------------------------------------ opening
  { id: 'hook', chapter: '', pre: 0.8, post: 0.7, text:
    `{prog}Here is a probabilistic program. {h}It draws a person's height, around one point seven meters. {coin}Then it flips a coin, {obs}and only if the coin comes up heads, it observes that a noisy measurement of that height came out as two meters. ` +
    `{ask}What is the expected height? {m}Run it, and the answer is about one point eight one. {cm}Now write the same program in centimeters. {exp}Converting, we would expect a hundred and eighty-one. {got}We get a hundred and seventy. ` +
    `{unit}The answer depends on the unit of measurement. {promise}By the end of this video, the two programs will agree, and we will know what the answer should be.` },
  { id: 'roadmap', chapter: '', pre: 0.3, post: 0.8, text:
    `{coming}Here is what is coming. {mean}First, what a program like this means, on two dice. {run}Then how such programs are run, with weights, {wrong}and where that goes wrong: three paradoxes. ` +
    `{should}Then what the answer should be. {fix}And then the fix, {inf}which computes with infinitesimal numbers.` },
  { id: 'title', chapter: '', pre: 0.6, post: 1.0, text:
    `{title}Paradoxes of probabilistic programming: {sub}how to condition on events of measure zero.` },

  // ------------------------------------------------------------------------------------------------ what observe means
  { id: 'dice_a', chapter: 'What observe means', pre: 1.9, post: 0.6, text:
    `{lang}A probabilistic program is an ordinary program with two extra operations. {rand}The first draws a random value from a distribution. {obs}The second is observe, and it is what this video is about. ` +
    `{dice}Here is an example. Throw two dice, X and Y, {cond}and observe that their sum is eight. {ret}Then return X. {dist}The program stands for a distribution: the first die, given that the sum is eight.` },
  { id: 'dice_b', chapter: 'What observe means', pre: 0.4, post: 0.6, text:
    `{how}What does observe do? The simplest answer is rejection. {trial}Run the program from the top. That is one trial. {test}At the observe, test the condition. {rej}If it is false, throw the trial away, and start again. ` +
    `{keep}If it is true, go on, and keep the returned value as a sample. {avg}The average of the kept samples estimates the expected value. {mean}So observe means: continue only if this holds.` },
  { id: 'dice_c', chapter: 'What observe means', pre: 0.4, post: 0.6, text:
    `{flow}Because this is a program, observe can sit inside control flow. {b}Here a coin decides whether the sum is observed at all. {event}A trial is kept if the coin comes up tails, or if the sum is eight. ` +
    `{fine}That is a perfectly good event to condition on.` },
  { id: 'weights', chapter: 'What observe means', pre: 0.5, post: 0.6, text:
    `{slow}Rejection is wasteful. With dice of a thousand sides, almost every trial is thrown away. {form}So languages have a second form of observe. It takes a distribution and a value, ` +
    `{means}and it means: draw from the distribution, and continue only if the draw equals the value. {rewrite}The dice program can be written with it: observe that a fresh die equals eight minus X. ` +
    `{weight}This form can be run without rejecting anything. Each trial carries a weight, which starts at one. {mul}At the observe, multiply the weight by the probability of that value: the chance that the trial would have survived. ` +
    `{wavg}At the end, take a weighted average of the results. {is}This is called importance sampling.` },
  { id: 'cool_discrete', chapter: 'What observe means', pre: 0.5, post: 0.9, text:
    `{note}Notice what we have. {three}For dice, three things agree: the exact conditional expectation, rejection, and the weighted average. {opt}The weight is only an optimization: ` +
    `{still}we can still think of every observe as rejecting a trial. {hold}The rest of the video is about keeping that true.` },

  // ------------------------------------------------------------------------------------------------ densities
  { id: 'dens_a', chapter: 'Densities', pre: 1.9, post: 0.6, text:
    `{cont}Now replace the dice by continuous distributions. {zero}The probability that a draw from a normal distribution equals one exact value is zero. {rejall}Rejection would throw away every trial, ` +
    `{wz}and every weight would be multiplied by zero. {so}So in practice, languages do something else. {pdf}For a continuous distribution, observe multiplies the weight by the probability density at the value. ` +
    `{ex}Here is the continuous version of the dice: two normal variables, given that their sum is eight. {works}For this program, that works.` },
  { id: 'dens_b', chapter: 'Densities', pre: 0.4, post: 0.9, text:
    `{but}But a density is not a probability. {q}Is observe still a rejection, in any sense? {branch}In general, it is not. And once control flow is involved, it gives answers that rejection would not. {back}Go back to the program from the beginning, with its if statement.` },

  // ------------------------------------------------------------------------------------------------ three paradoxes
  { id: 'why_a', chapter: 'Three paradoxes', pre: 1.9, post: 0.6, text:
    `{run}This is what the language actually runs. {w1}The weight starts at one. {pdf}On heads, it is multiplied by a density: the density of the measurement, at two meters. {unit}And a density has a unit. ` +
    `{per}The probability that the measurement lands in a narrow interval is about the density times the interval's width. A probability has no unit, and the width is a length. So the density is per meter. ` +
    `{ex}Take a run that drew a height of one point nine five. The density of its measurement at two is three point five per meter. That is its weight. {skip}On tails, nothing is multiplied. The weight stays one, with no unit.` },
  { id: 'why_b', chapter: 'Three paradoxes', pre: 0.5, post: 0.7, text:
    `{add}The weighted average adds the weights of all runs. {mix}So it adds a number per meter to a number with no unit. {cm}Now change the unit. In centimeters, the same run has a weight of zero point zero three five per centimeter. The number is a hundred times smaller. ` +
    `{tails}The tails runs still have weight one. {shift}So the heads runs count for a hundred times less. {slide}And the answer slides from one point eight one toward one point seven, the average height before any measurement. We will call that the prior.` },
  { id: 'cool_units', chapter: 'Three paradoxes', pre: 0.5, post: 0.8, text:
    `{look}Look at where the mistake is. {text}Nothing is wrong in the program text. Its units are consistent. {inside}The inconsistency is inside the method that runs it. ` +
    `{all}And it is not one tool's bug: other inference algorithms do the same arithmetic.` },
  { id: 'should_a', chapter: 'Three paradoxes', pre: 0.5, post: 0.5, text:
    `{q}So what should the answer be? {analogy}Reason as we did for the dice. {event}A trial is kept if the coin comes up tails, or if the measurement is exactly two. {half}The second case has probability zero. But the first has probability one half. ` +
    `{notzero}So this event does not have probability zero at all, {defn}and the ordinary definition of conditional probability applies.` },
  { id: 'should_b', chapter: 'Three paradoxes', pre: 0.4, post: 0.8, text:
    `{rej}In terms of rejection: a heads trial is rejected with probability one. Only tails trials survive, {prior}and in those, the height is untouched. {ans}The answer is the prior: one point seven meters, or a hundred and seventy centimeters. {noeffect}The whole if statement should have no effect. ` +
    `{coin}If that seems strange, remember that the coin is not known to have come up heads. Among the trials that are kept, tails has probability one. ` +
    `{twist}So of the two answers at the start, a hundred and seventy was the one close to the truth, and only by an accident of the unit. One point eight one was simply wrong.` },
  { id: 'type1', chapter: 'Three paradoxes', pre: 0.6, post: 0.6, text:
    `{more}That was one paradox. There are two more. {bmi}This program draws a person's height, and their body weight. {coin}A coin decides which of the two is measured. {ret}It returns the body mass index. ` +
    `{units}Now one branch multiplies by a density per meter, and the other by a density per kilogram. {sum}The weighted average adds the two. {change}Change meters to centimeters, correct the formula for it, and the answer still changes. ` +
    `{zero}And this time, every trial observes an exact value. The event really has probability zero, so the definition of conditional probability gives no answer at all. {later}We will come back to this program.` },
  { id: 'type3', chapter: 'Three paradoxes', pre: 0.5, post: 0.6, text:
    `{third}The third paradox has no branch. {prog}Draw X from a normal distribution. Observe that a draw from a second normal distribution equals X. {ret}Then return the exponential of X. {db}Think of X as a sound level in decibels, and of its exponential as an energy. ` +
    `{change}Now write the same program on the energy scale. The two distributions become what is called log-normal, {same}and the event is the same event: two exponentials are equal exactly when their exponents are. ` +
    `{diff}Yet the two programs give different answers. {known}It is a version of what probability theory calls the Borel-Kolmogorov paradox.` },
  { id: 'cool_scale', chapter: 'Three paradoxes', pre: 0.5, post: 0.9, text:
    `{all}All three paradoxes break one principle: {principle}the answer should not depend on the scale we measure in. {lin}Meters or centimeters. {non}Decibels or energy. ` +
    `{cause}And all three have one cause. An observe on an exact value multiplies by a density, and a density depends on the scale.` },

  // ------------------------------------------------------------------------------------------------ intervals
  { id: 'int_a', chapter: 'Intervals', pre: 1.9, post: 0.6, text:
    `{dis}Why were the dice free of all this? {prob}Not because dice are discrete, but because their weights were probabilities, {nounit}and a probability has no unit. ` +
    `{cont}A continuous distribution has probabilities too: the probability that a draw lands in an interval. {obs}So let observe take an interval. {mean}It means: draw from the distribution, and continue only if the draw lies in the interval. ` +
    `{exec}It runs by multiplying the weight by that probability. {rej}Rejection is back, as the meaning of observe.` },
  { id: 'int_b', chapter: 'Intervals', pre: 0.4, post: 0.6, text:
    `{units}And units are safe. {m}Here is an interval around two meters, of width zero point one. {cmm}In centimeters, its center becomes two hundred, and its width becomes ten. ` +
    `{same}The area under the curve is the same, so the weight is the same. {forced}A change of unit now changes the width as well, and that keeps the weight in place.` },
  { id: 'int_c', chapter: 'Intervals', pre: 0.5, post: 0.7, text:
    `{price}But we have changed the question. {exact}We wanted to observe exactly two meters, not roughly two meters. {small}We could choose a tiny width, say one ten-thousandth. But why that number? ` +
    `{limit}What we want is the limit, as the width goes to zero. {amb}But there is a catch. {jaynes}Conditioning on an event of probability zero is ambiguous. {which}Intervals can shrink onto the same event in different ways, and give different answers. ` +
    `{say}So the program has to say which limit it means. {next}The next program shows that this matters.` },
  { id: 'int_d', chapter: 'Intervals', pre: 0.5, post: 0.9, text:
    `{bmi}Take the program that measures either height or body weight. {eps}Give each observe an interval whose width is a constant times epsilon, where epsilon is a small number with no unit. {A}The constant A is a length. {B}The constant B is a mass. ` +
    `{both}As epsilon shrinks, both observes become exact. {ratio}But the ratio of the two widths stays, and it matters. {thousand}Make B a thousand times larger, and the second branch succeeds a thousand times more often. ` +
    `{part}So the widths are part of the model. {old}The old observe had no place to write them. That is what went wrong.` },

  // ------------------------------------------------------------------------------------------------ infinitesimals
  { id: 'eps_a', chapter: 'Infinitesimal probabilities', pre: 1.9, post: 0.6, text:
    `{how}How do we compute a limit inside a running program? {sym}Treat epsilon as a symbol. {num}An infinitesimal number is a real number times a power of epsilon. {real}Power zero gives the ordinary numbers. ` +
    `{mul}To multiply, multiply the real parts, and add the powers. {add}To add two numbers with the same power, add the real parts. {low}To add numbers with different powers, keep the one with the lower power. It is the larger number, because epsilon is tiny, and next to it the other is negligible. ` +
    `{div}Division subtracts the powers. {pair}Each number is just a pair, so the arithmetic is cheap.` },
  { id: 'eps_b', chapter: 'Infinitesimal probabilities', pre: 0.4, post: 0.6, text:
    `{prob}Now the probability of an interval. {fin}If its width is an ordinary number, it is the area under the curve, as before. {infw}If its width is infinitesimal, it is the density times the width. ` +
    `{thin}That is the area of a strip so thin that the curve is flat across it. {unit}The density is per meter, the width is in meters, and the product has no unit. {name}It is an infinitesimal probability.` },
  { id: 'eps_c', chapter: 'Infinitesimal probabilities', pre: 0.5, post: 0.6, text:
    `{run}Run the first program again, with an interval around two meters, whose width is one meter times epsilon. {heads}The heads run from before now has weight three point five epsilon. {tails}A tails run has weight one. ` +
    `{sum}Add them: one plus three point five epsilon is one. {gone}The heads run is negligible, exactly as rejection said it should be. {any}Any other width times epsilon would be negligible too. {avg}The weighted average is the average over the tails runs: about one point seven. ` +
    `{cm}In centimeters, the width is a hundred epsilon, the density is a hundred times smaller, and the weight is again three point five epsilon. {agree}The two programs agree. {done}That was the promise at the start of the video: one answer in both units, and it is the answer that the rejection argument gave.` },
  { id: 'cool_less', chapter: 'Infinitesimal probabilities', pre: 0.5, post: 0.8, text:
    `{rule}There is a general rule in this. {fewer}A run that makes fewer exact observations outweighs a run that makes more, by an infinite factor. {power}The power of epsilon counts them. {tie}Among runs with the same count, the ordinary weights decide.` },
  { id: 'eps_d', chapter: 'Infinitesimal probabilities', pre: 0.5, post: 0.7, text:
    `{bmi}Now back to the program with height and body weight. Every run makes one exact observation. {one}So every weight has power one. {cancel}In the weighted average, epsilon appears above and below, and it cancels. ` +
    `{real}The result is an ordinary number, {AB}and it depends on the two widths only through their ratio. {choice}That ratio is a choice, and the programmer now makes it in the open.` },
  { id: 'thm', chapter: 'Infinitesimal probabilities', pre: 0.6, post: 0.9, text:
    `{right}Is this arithmetic sound, or is it a trick? {claim}The claim is that it computes the limit we wanted. {f}Hold the random draws fixed, and run the whole estimate with a small real width W. Call the result F of W. {eval}Then run the same computation with epsilon in place of W. ` +
    `{sup}Suppose that gives R times epsilon to the power N. {thm}The theorem says: as W goes to zero, F of W, divided by W to the power N, tends to R. {zero}For a weighted average, the power is zero. So R is the limit itself. ` +
    `{fig}Here is that convergence for the first program. As a real width shrinks, the estimate moves to one point seven. {direct}The infinitesimal run gives one point seven directly.` },

  // ------------------------------------------------------------------------------------------------ old programs, other scales
  { id: 'compat', chapter: 'Old programs, other scales', pre: 1.9, post: 0.6, text:
    `{old}What about programs that already work? {trans}Translate each observe on an exact value into an observe on an interval of width W times epsilon. {same}If every run makes the same observations, every weight gains the same factor. ` +
    `{cancel}It cancels in the weighted average, and the answer does not change. {cons}So nothing that behaved well before is disturbed. {only}Only programs whose runs make different observations get a new answer.` },
  { id: 'scale', chapter: 'Old programs, other scales', pre: 0.5, post: 0.9, text:
    `{third}One paradox is left: the change from decibels to energy. {int}With intervals, we can see what went wrong. {exp}Take the exponential of a small interval around X. {wide}The result is an interval around the exponential of X. But its width is not epsilon. {deriv}It is epsilon times the derivative of the exponential at X, which is the exponential of X itself. ` +
    `{prog}So on the energy scale, the program must observe an interval of that width. {agree}Now the two programs give the same answer. ` +
    `{gen}This holds for every smooth, increasing change of scale. Transform the distribution and the interval together, and the probability of the interval does not change.` },

  // ------------------------------------------------------------------------------------------------ close
  { id: 'recap', chapter: 'Looking back', pre: 1.9, post: 0.7, text:
    `{p1}We began with a program whose answer changed with the unit of measurement. {p2}The cause was an observe that multiplies by a density. {p3}The repair is to observe an interval, and to let its width be infinitesimal. ` +
    `{p4}Then observe is rejection again, and an event of probability zero is a limit of events that have a probability. {p5}The program says which limit it means. {p6}And both units give the same answer: one point seven meters.` },
  { id: 'end', chapter: 'Looking back', pre: 0.5, post: 3.0, text:
    `{impl}All of this is implemented as a small library in the Julia language. {title}Paradoxes of probabilistic programming. {paper}The paper has the proofs, a discussion of measurements with finite precision, and what remains to be done for other inference algorithms.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "hook",
   "chapter": "",
   "start": 0.0,
   "dur": 38.62,
   "pre": 0.8,
   "post": 0.7,
   "audio": 37.12,
   "cues": {
    "prog": 0.8,
    "h": 3.28,
    "coin": 7.28,
    "obs": 8.96,
    "ask": 15.84,
    "m": 17.84,
    "cm": 21.36,
    "exp": 24.24,
    "got": 27.68,
    "unit": 29.76,
    "promise": 32.72
   }
  },
  {
   "id": "roadmap",
   "chapter": "",
   "start": 38.62,
   "dur": 20.7,
   "pre": 0.3,
   "post": 0.8,
   "audio": 19.6,
   "cues": {
    "coming": 0.3,
    "mean": 2.22,
    "run": 6.54,
    "wrong": 9.767,
    "should": 13.42,
    "fix": 15.5,
    "inf": 17.1
   }
  },
  {
   "id": "title",
   "chapter": "",
   "start": 59.32,
   "dur": 7.6,
   "pre": 0.6,
   "post": 1,
   "audio": 6.0,
   "cues": {
    "title": 0.6,
    "sub": 3.56
   }
  },
  {
   "id": "dice_a",
   "chapter": "What observe means",
   "start": 66.92,
   "dur": 29.7,
   "pre": 1.9,
   "post": 0.6,
   "audio": 27.2,
   "cues": {
    "lang": 1.9,
    "rand": 7.18,
    "obs": 10.7,
    "dice": 14.86,
    "cond": 19.127,
    "ret": 21.66,
    "dist": 23.58
   }
  },
  {
   "id": "dice_b",
   "chapter": "What observe means",
   "start": 96.62,
   "dur": 29.24,
   "pre": 0.4,
   "post": 0.6,
   "audio": 28.24,
   "cues": {
    "how": 0.4,
    "trial": 4.88,
    "test": 8.667,
    "rej": 11.44,
    "keep": 15.28,
    "avg": 20.0,
    "mean": 24.4
   }
  },
  {
   "id": "dice_c",
   "chapter": "What observe means",
   "start": 125.86,
   "dur": 17.56,
   "pre": 0.4,
   "post": 0.6,
   "audio": 16.56,
   "cues": {
    "flow": 0.4,
    "b": 5.12,
    "event": 9.12,
    "fine": 14.08
   }
  },
  {
   "id": "weights",
   "chapter": "What observe means",
   "start": 143.42,
   "dur": 44.62,
   "pre": 0.5,
   "post": 0.6,
   "audio": 43.52,
   "cues": {
    "slow": 0.5,
    "form": 7.34,
    "means": 12.687,
    "rewrite": 18.74,
    "weight": 24.9,
    "mul": 31.46,
    "wavg": 38.26,
    "is": 41.62
   }
  },
  {
   "id": "cool_discrete",
   "chapter": "What observe means",
   "start": 188.04,
   "dur": 20.52,
   "pre": 0.5,
   "post": 0.9,
   "audio": 19.12,
   "cues": {
    "note": 0.5,
    "three": 2.18,
    "opt": 10.18,
    "still": 12.66,
    "hold": 16.66
   }
  },
  {
   "id": "dens_a",
   "chapter": "Densities",
   "start": 208.56,
   "dur": 36.18,
   "pre": 1.9,
   "post": 0.6,
   "audio": 33.68,
   "cues": {
    "cont": 1.9,
    "zero": 5.5,
    "rejall": 11.58,
    "wz": 14.167,
    "so": 17.18,
    "pdf": 20.62,
    "ex": 27.02,
    "works": 33.42
   }
  },
  {
   "id": "dens_b",
   "chapter": "Densities",
   "start": 244.74,
   "dur": 18.26,
   "pre": 0.4,
   "post": 0.9,
   "audio": 16.96,
   "cues": {
    "but": 0.4,
    "q": 3.36,
    "branch": 6.72,
    "back": 13.6
   }
  },
  {
   "id": "why_a",
   "chapter": "Three paradoxes",
   "start": 263.0,
   "dur": 44.66,
   "pre": 1.9,
   "post": 0.6,
   "audio": 42.16,
   "cues": {
    "run": 1.9,
    "w1": 4.78,
    "pdf": 6.86,
    "unit": 13.22,
    "per": 15.607,
    "ex": 29.26,
    "skip": 38.78
   }
  },
  {
   "id": "why_b",
   "chapter": "Three paradoxes",
   "start": 307.66,
   "dur": 35.12,
   "pre": 0.5,
   "post": 0.7,
   "audio": 33.92,
   "cues": {
    "add": 0.5,
    "mix": 4.02,
    "cm": 8.42,
    "tails": 18.9,
    "shift": 21.62,
    "slide": 24.953
   }
  },
  {
   "id": "cool_units",
   "chapter": "Three paradoxes",
   "start": 342.78,
   "dur": 17.38,
   "pre": 0.5,
   "post": 0.8,
   "audio": 16.08,
   "cues": {
    "look": 0.5,
    "text": 2.74,
    "inside": 7.3,
    "all": 11.193
   }
  },
  {
   "id": "should_a",
   "chapter": "Three paradoxes",
   "start": 360.16,
   "dur": 24.12,
   "pre": 0.5,
   "post": 0.5,
   "audio": 23.12,
   "cues": {
    "q": 0.5,
    "analogy": 2.66,
    "event": 4.98,
    "half": 10.74,
    "notzero": 16.42,
    "defn": 19.753
   }
  },
  {
   "id": "should_b",
   "chapter": "Three paradoxes",
   "start": 384.28,
   "dur": 40.56,
   "pre": 0.4,
   "post": 0.8,
   "audio": 39.36,
   "cues": {
    "rej": 0.4,
    "prior": 8.0,
    "ans": 10.96,
    "noeffect": 16.84,
    "coin": 19.92,
    "twist": 28.96
   }
  },
  {
   "id": "type1",
   "chapter": "Three paradoxes",
   "start": 424.84,
   "dur": 41.84,
   "pre": 0.6,
   "post": 0.6,
   "audio": 40.64,
   "cues": {
    "more": 0.6,
    "bmi": 4.36,
    "coin": 8.04,
    "ret": 10.92,
    "units": 13.48,
    "sum": 19.72,
    "change": 22.44,
    "zero": 28.04,
    "later": 39.12
   }
  },
  {
   "id": "type3",
   "chapter": "Three paradoxes",
   "start": 466.68,
   "dur": 42.06,
   "pre": 0.5,
   "post": 0.6,
   "audio": 40.96,
   "cues": {
    "third": 0.5,
    "prog": 3.54,
    "ret": 10.9,
    "db": 13.9,
    "change": 19.62,
    "same": 26.553,
    "diff": 33.14,
    "known": 36.153
   }
  },
  {
   "id": "cool_scale",
   "chapter": "Three paradoxes",
   "start": 508.74,
   "dur": 21.32,
   "pre": 0.5,
   "post": 0.9,
   "audio": 19.92,
   "cues": {
    "all": 0.5,
    "principle": 3.62,
    "lin": 7.14,
    "non": 8.98,
    "cause": 11.087
   }
  },
  {
   "id": "int_a",
   "chapter": "Intervals",
   "start": 530.06,
   "dur": 33.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 31.44,
   "cues": {
    "dis": 1.9,
    "prob": 4.46,
    "nounit": 8.967,
    "cont": 11.42,
    "obs": 18.06,
    "mean": 20.62,
    "exec": 26.62,
    "rej": 30.3
   }
  },
  {
   "id": "int_b",
   "chapter": "Intervals",
   "start": 564.0,
   "dur": 23.08,
   "pre": 0.4,
   "post": 0.6,
   "audio": 22.08,
   "cues": {
    "units": 0.4,
    "m": 2.68,
    "cmm": 7.52,
    "same": 12.8,
    "forced": 17.147
   }
  },
  {
   "id": "int_c",
   "chapter": "Intervals",
   "start": 587.08,
   "dur": 34.24,
   "pre": 0.5,
   "post": 0.7,
   "audio": 33.04,
   "cues": {
    "price": 0.5,
    "exact": 2.66,
    "small": 7.46,
    "limit": 12.9,
    "amb": 16.5,
    "jaynes": 18.18,
    "which": 22.18,
    "say": 27.513,
    "next": 30.9
   }
  },
  {
   "id": "int_d",
   "chapter": "Intervals",
   "start": 621.32,
   "dur": 38.44,
   "pre": 0.5,
   "post": 0.9,
   "audio": 37.04,
   "cues": {
    "bmi": 0.5,
    "eps": 4.18,
    "A": 12.18,
    "B": 14.42,
    "both": 16.74,
    "ratio": 20.58,
    "thousand": 24.66,
    "part": 30.82,
    "old": 33.22
   }
  },
  {
   "id": "eps_a",
   "chapter": "Infinitesimal probabilities",
   "start": 659.76,
   "dur": 41.38,
   "pre": 1.9,
   "post": 0.6,
   "audio": 38.88,
   "cues": {
    "how": 1.9,
    "sym": 5.66,
    "num": 7.9,
    "real": 12.86,
    "mul": 15.767,
    "add": 20.06,
    "low": 24.14,
    "div": 34.673,
    "pair": 36.62
   }
  },
  {
   "id": "eps_b",
   "chapter": "Infinitesimal probabilities",
   "start": 701.14,
   "dur": 27.0,
   "pre": 0.4,
   "post": 0.6,
   "audio": 26.0,
   "cues": {
    "prob": 0.4,
    "fin": 3.04,
    "infw": 8.56,
    "thin": 13.28,
    "unit": 18.16,
    "name": 23.76
   }
  },
  {
   "id": "eps_c",
   "chapter": "Infinitesimal probabilities",
   "start": 728.14,
   "dur": 52.78,
   "pre": 0.5,
   "post": 0.6,
   "audio": 51.68,
   "cues": {
    "run": 0.5,
    "heads": 7.86,
    "tails": 12.5,
    "sum": 15.06,
    "gone": 19.3,
    "any": 23.94,
    "avg": 27.567,
    "cm": 32.82,
    "agree": 41.86,
    "done": 43.94
   }
  },
  {
   "id": "cool_less",
   "chapter": "Infinitesimal probabilities",
   "start": 780.92,
   "dur": 16.74,
   "pre": 0.5,
   "post": 0.8,
   "audio": 15.44,
   "cues": {
    "rule": 0.5,
    "fewer": 2.82,
    "power": 9.487,
    "tie": 12.02
   }
  },
  {
   "id": "eps_d",
   "chapter": "Infinitesimal probabilities",
   "start": 797.66,
   "dur": 25.84,
   "pre": 0.5,
   "post": 0.7,
   "audio": 24.64,
   "cues": {
    "bmi": 0.5,
    "one": 6.98,
    "cancel": 9.42,
    "real": 14.74,
    "AB": 16.953,
    "choice": 20.74
   }
  },
  {
   "id": "thm",
   "chapter": "Infinitesimal probabilities",
   "start": 823.5,
   "dur": 49.02,
   "pre": 0.6,
   "post": 0.9,
   "audio": 47.52,
   "cues": {
    "right": 0.6,
    "claim": 4.04,
    "f": 7.28,
    "eval": 15.4,
    "sup": 19.8,
    "thm": 23.56,
    "zero": 31.613,
    "fig": 37.04,
    "direct": 44.2
   }
  },
  {
   "id": "compat",
   "chapter": "Old programs, other scales",
   "start": 872.52,
   "dur": 29.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 27.44,
   "cues": {
    "old": 1.9,
    "trans": 4.78,
    "same": 12.06,
    "cancel": 17.26,
    "cons": 21.5,
    "only": 24.86
   }
  },
  {
   "id": "scale",
   "chapter": "Old programs, other scales",
   "start": 902.46,
   "dur": 44.52,
   "pre": 0.5,
   "post": 0.9,
   "audio": 43.12,
   "cues": {
    "third": 0.5,
    "int": 5.42,
    "exp": 8.42,
    "wide": 12.14,
    "deriv": 18.26,
    "prog": 25.22,
    "agree": 30.42,
    "gen": 33.46
   }
  },
  {
   "id": "recap",
   "chapter": "Looking back",
   "start": 946.98,
   "dur": 30.44,
   "pre": 1.9,
   "post": 0.7,
   "audio": 27.84,
   "cues": {
    "p1": 1.9,
    "p2": 6.3,
    "p3": 10.06,
    "p4": 15.18,
    "p5": 22.7,
    "p6": 25.42
   }
  },
  {
   "id": "end",
   "chapter": "Looking back",
   "start": 977.42,
   "dur": 20.3,
   "pre": 0.5,
   "post": 3,
   "audio": 16.8,
   "cues": {
    "impl": 0.5,
    "title": 5.46,
    "paper": 8.9
   }
  }
 ],
 "total": 997.72
};

// ==== src/scenes/common.js ====
// Shared pieces of the full-length Paradoxes film, as window.PX. Every scene file builds on these so that the same
// thing looks the same everywhere. Only engine.js globals are used (box, el, svgLayer, path, tick, fadeIn, fadeOut,
// alpha, charWidth, Code, Film.C, Film.E).
//
// Text is laid out by the browser (flex and grid boxes), never by measuring a font, so nothing depends on fonts
// having loaded at build time. Only whole elements are animated, with the scene's timeline `tl`.
//
// ---- parts: coloured pieces of one line ------------------------------------------------------------------------
// Wherever a function below takes `parts`, it is a string, or an array of parts, each one of:
//   'text'                       ink (or the line's colour)
//   ['text', colour]             in a colour, e.g. ['1.81', C.pat] -- alone it must still be wrapped: [['1.81', C.pat]]
//   ['text', colour, {style}]    with extra CSS, e.g. PX.mono('x + y', C.code) or PX.lc('h') builds one
//   PX.sup(parts) / PX.sub(parts) a raised / lowered small span (0.62 em, raised 0.42 em / lowered 0.2 em)
//   PX.frac(numParts, denParts)  a real fraction: numerator over a 3 px rule over denominator, centred on the line
//   PX.tick(tl, at, size)        a green tick drawn at `at`, in the line
//   a DOM node                   appended as it is
// Every top-level part becomes an inline-block span, so it can be animated on its own: the element a function
// returns has `.parts`, the list of those spans in order (e.g. `e.parts[1]` is the "≠" of ['1.81 m ', ['≠', C.bad],
// ' 170 cm']; tl.set(e.parts[1], {o: 0}, 0); tl.to(e.parts[1], {o: 1}, t, 0.4) brings it in later).
//
// ---- type --------------------------------------------------------------------------------------------------
// PX.SERIF(size), PX.LABEL(size), PX.MONO(size): CSS style objects (serif sentences/formulas, line-height 1.22;
//   small-caps sans labels, dim, letter-spacing 0.16 em, line-height 1.2; code, line-height 1.3, no ligatures).
// PX.rich(parent, parts, {size = 56, font = 'serif'|'label'|'mono', color, style}) -> a block in the flow of
//   `parent` (for flex/grid rows). Its parts sit on one baseline.
// PX.line(parent, x, y, parts, {size, font, align = 'left'|'center'|'right', color, style}) -> an absolutely
//   placed line: y is the TOP of its line box (height ≈ 1.22 size for serif, 1.2 for labels, 1.3 for mono; a
//   frac makes the line taller and pushes its baseline down); x is its left edge, centre or right edge by `align`.
//   Labels are compensated for the letter spacing after their last letter, so they centre and right-align true.
// PX.cline(parent, y, parts, opts): PX.line centred on the stage (x = 960).
// PX.crow(parent, y, {gap = 40, x, align = 'center'}) -> a full-width flex row at top y whose children (PX.rich
//   blocks, ticks) sit side by side, centred (or, with x, starting at x); items are vertically centred.
// PX.label(tl, parent, x, y, parts, at, out, {size = 34, color = C.dim, align}) -> a label that rises in at `at`
//   and leaves at `out` (null: stays). Labels are upper case; PX.lc(text, colour) keeps a piece lower case (h, x,
//   ε), PX.EPS is an amber lower-case ε for labels.
// PX.mono(text, colour = C.code) -> a part in code type inside a serif or label line (0.9 em).
// PX.sup(parts, colour?), PX.sub(parts, colour?) -> parts. ['r ', ['ε', C.pat], PX.sup('n', C.pat)] is r εⁿ;
//   ['weight', PX.sub('k')] is weightₖ.
// PX.frac(num, den, {scale = 1, color}) -> a part: num and den are parts, set at `scale` em; the rule is 3 px in
//   the line's colour (or `color`), as wide as the wider of the two plus 0.2 em.
//
// ---- timing ------------------------------------------------------------------------------------------------
// PX.inout(tl, e, at, out, {dy = 16, dur = 0.6}) -> e: rises in at `at` (E.out5), leaves upward at `out` if given.
// PX.leave(tl, els, at, {dur = 0.35}) leaves upward, fast (E.in). PX.dim(tl, els, o, at, {dur = 0.5}) dims to o.
// PX.pulse(tl, e, at, {scale = 1.08, dur = 0.6}) a short swell and back (an element, not Code tokens: for those
//   use code.pulse).
// PX.markEl(tl, e, colour, at, {out, pad = 12, fill = 0.14}) a soft box behind an element or part (its colour is
//   its meaning: C.good kept, C.bad wrong, C.dim with fill 0.08 the neutral "look here"). Returns the box.
// PX.strikeEl(tl, e, at, {dur = 0.4}) the neutral deletion of text: a grey line through it, and it goes faint.
// PX.alt(tl, parent, [parts0, parts1, …], {size, font, align = 'start'|'center'|'end', style}) -> a block in the
//   flow of `parent` holding alternatives stacked in one place (its size is the largest); `.show(k, at)` makes
//   alternative k the visible one: the old leaves in 0.2 s, the new arrives from at + 0.2, settled at at + 0.55,
//   so start it 0.2 s before the word. Alternative 0 shows from the start. `.alts[k]` are the elements.
// PX.retext(tl, e, text, at) the same for a plain element's text (tick labels): fade, change, fade back in.
// PX.tickAt(tl, parent, x, y, at, {size = 56}) a green tick centred at (x, y), drawn at `at`. Returns its svg.
//
// ---- code --------------------------------------------------------------------------------------------------
// PX.RAIL = 160, the programs' left edge. PX.progY(nLines) -> the first line's y for a program of that many lines
//   (8: 200, 6–7: 240, 4–5: 300, 3 or fewer: 360). Code at 48 has lh = 78 and cw ≈ 28.8.
// PX.look(code, sel, at, out) the neutral "look here" mark on Code tokens (one line). PX.lineOf(l) selects line l.
// PX.P: the film's programs as Code sources, copied from SCENES.md: HOOK_M, HOOK_CM, HOOK_M5, HOOK_CM5 (with
//   `return h`), WEIGHT, DICE1, DICE2, DICE3, NORM, BMI, BMI_EPS, DB, ENERGY, DB_EPS, ENERGY_EPS, FIX_M, FIX_CM.
//   In the hook family (HOOK_*, WEIGHT, FIX_*) the numbers have ids that survive a swap/morph from meters to
//   centimeters: mu (1.7 / 170), sd (0.5 / 50), p (0.5 of the coin), so (0.1 / 10), ob (2.0 / 200); FIX_* have
//   iw (the width: `eps` / `100*eps`, ids iw for `eps`, ik for `100*`). Other numbers are split by the tokenizer
//   at the "." (1.7 is three tokens), which only matters if you select them.
//
// ---- pictures ----------------------------------------------------------------------------------------------
// PX.runsTable(tl, root, rows, {y, x, cx = 960, size = 52, labelSize = 34, rowGap = 22, colGap = 40, plus})
//   A table of runs, one row each: LABEL (right-aligned) · "weight" (dim serif) · value (serif) · note (label).
//   rows: [{label: parts, value: parts | values: [parts, parts…], note: parts}]. Write values with PX.wv('3.5',
//   '/ m') (amber value, cyan unit) or any parts. y is the table's top; with x the table's left edge is at x, else
//   it is centred on cx (all notes and alternative values count for its width, so it never shifts). Nothing shows
//   until shown. Returns T with:
//     T.el (the grid, to move/dim as a whole), T.rows[i] = {lab, w, val, note, cells}, T.plusEl
//     T.show(at, step = 0.45)        every row in turn;  T.showRow(i, at)  one row (rises in, cells staggered)
//     T.value(i, k, at)              row i's value becomes alternative k (as PX.alt)
//     T.dimRow(i, o, at)  T.pulse(i, at)  T.hideRow(i, at)  T.hide(at)
//     T.showNote(i, at, out)         row i's note (a label in the fourth column) comes in (and goes)
//     T.showPlus(at)                 with {plus: true}: a "+" in the value column between rows 0 and 1
// PX.axis(tl, root, {x0, x1, y, from, to, ticks = [], fmt = v => String(v), tickSize = 28, unit, width = 3})
//   A horizontal number line from stage x0 to x1 at stage y, for data values from..to. Returns A with A.el (a
//   full-stage layer: animate it to move or dim everything on it; add your own annotations into it), A.svg,
//   A.X(v) (stage x of a value), A.y, A.ticks = [{v, mark, text}], A.unitEl (cyan, at the right end),
//   A.show(at, dur = 0.6) (line draws, ticks follow), A.retick([texts], at), A.reunit(text, at), A.hide(at).
// PX.bell(tl, root, {cx = 960, y = 720, w = 1000, h = 380, mu = 0, sd = 1, from, to, ticks, fmt, tickSize, unit,
//   stroke = 4.5})  A normal curve over an axis. y is the axis's stage y, h the peak's height in px; the axis runs
//   from `from` to `to` (default mu ± 3.3 sd) across w, centred on cx. Returns B, an axis (all of A above) plus:
//     B.Y(v)  the stage y of the curve at v;  B.top  the peak's stage y
//     B.show(at)  axis, curve (drawn over 0.9 s) and ticks
//     B.band(a, b, {at, color = C.pat, fill = 0.32}) -> {el, to(a, b, at, dur = 0.8, ease = E.io), hide(at)}:
//       the area under the curve between data values a and b, filled and outlined (a hairline stays visible)
//     B.vline(v, {at, dash = true, color = C.ink, width = 3, full = false}) -> a path from the axis up to the
//       curve (full: to the top), drawn at `at`
//     B.dot(v, {at, color = C.pat, r = 11, stem = true}) -> {dot, stem}: a dot on the curve, with a solid
//       vertical from the axis to it
//   Its el's transform origin is the picture's centre, so tl.to(B.el, {s: 0.8, x: -300}, …) shrinks it in place.
// PX.dots(tl, root, {n, y, x, cx = 960, size = 36, gap = 26, label, labelSize = 34, color = C.code})
//   A row of trials as dots. y is the dots' centre line; with x the first dot's left edge, else the row of dots
//   is centred on cx (the label hangs to the left of the dots, right-aligned, 30 px before them). Returns D with
//   D.el (the row, label included), D.dots[i] (each dot's element), D.X(i) (centre x of dot i), D.y, D.label,
//   D.show(at, stagger = 0.03), D.strike(i, at) (a grey line through it, it goes faint: rejected),
//   D.strikeAll(at, step = 0.15, except = []) one after another, D.keep(i, at) (the dot turns green: kept),
//   D.mark(colour, at, {out}) (a soft box behind the row of dots, e.g. C.good for "kept"), D.hide(at).
// PX.titleCard(tl, root, {lines, size = 104, x = 160, y = 330, align = 'left'|'center', at, step = 0.5, sub,
//   subSize = 46, subAt, label, labelSize = 34, labelAt}) -> {lines, sub, label}: title lines (serif), then an
//   italic subtitle (a string or an array of lines), then a label, stacked from y. `at` is a time or one time per
//   line. Parts not given a time stay hidden.
//
// Word times: cues are in build/timeline.json; the time of every word (from the narration's character alignment)
// can be printed with python3 over build/audio/<segment>.json (alignment.characters and
// alignment.character_start_times_seconds, plus the segment's `pre`).
'use strict';
(function () {
  const { W, C, E } = Film;
  const LS = 0.16, RAIL = 160;

  // ---- type ----------------------------------------------------------------------------------------------
  const SERIF = size => ({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, whiteSpace: 'pre', letterSpacing: '-0.005em', fontWeight: 400 });
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', lineHeight: 1.2, fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase', color: C.dim, whiteSpace: 'pre' });
  const MONO = size => ({ fontFamily: 'var(--mono)', fontSize: size + 'px', lineHeight: 1.3, color: C.code, whiteSpace: 'pre', fontVariantLigatures: 'none', fontWeight: 450 });
  const FONT = { serif: SERIF, label: LABEL, mono: MONO };

  // a plain element in the flow (not absolutely placed)
  function div(parent, style = {}, text, tag = 'div') {
    const e = document.createElement(tag);
    Object.assign(e.style, { position: 'relative' }, style);
    if (text !== undefined) { e.textContent = text; e._text0 = text; e._shown = text; }
    parent.appendChild(e);
    return e;
  }
  // put parts into e; returns the top-level elements made
  function put(e, parts) {
    const out = [];
    for (const p of [].concat(parts)) {
      let s;
      if (typeof p === 'function') s = p(e);
      else if (p instanceof Node) { e.appendChild(p); s = p; }
      else {
        const [t, col, st] = typeof p === 'string' ? [p, null, null] : p;
        s = div(e, { display: 'inline-block' }, t, 'span');
        if (col) s.style.color = col;
        if (st) Object.assign(s.style, st);
      }
      out.push(s);
    }
    return out;
  }
  const fill = (e, parts) => { e.parts = put(e, parts); return e; };
  const lc = (t, col) => [t, col || null, { textTransform: 'none', letterSpacing: '0.02em' }];
  // set in the serif: the system sans of the labels is not shipped, and its ε differs between devices
  const EPS = ['ε', C.pat, { textTransform: 'none', letterSpacing: '0.02em', fontFamily: 'var(--serif)', fontSize: '1.2em', fontWeight: 400, lineHeight: 1 }];
  const mono = (t, col = C.code) => [t, col, { fontFamily: 'var(--mono)', fontSize: '0.9em', fontVariantLigatures: 'none', letterSpacing: '0', textTransform: 'none' }];
  // raised / lowered small spans: 0.62 em of the line, raised 0.42 em (0.677 of their own em) or lowered 0.2 em
  const script = (raise) => (parts, col) => parent => {
    const s = div(parent, { display: 'inline-block', fontSize: '0.62em', verticalAlign: (raise / 0.62).toFixed(3) + 'em', lineHeight: 1 }, undefined, 'span');
    if (col) s.style.color = col;
    s.parts = put(s, parts);
    return s;
  };
  const sup = script(0.42), sub = script(-0.2);
  function frac(num, den, { scale = 1, color } = {}) {
    return parent => {
      const f = div(parent, { display: 'inline-flex', flexDirection: 'column', alignItems: 'center', verticalAlign: 'middle', margin: '0 0.12em', lineHeight: 1.1 }, undefined, 'span');
      const n = div(f, { display: 'block', fontSize: scale + 'em', padding: '0 0.1em 0.06em' }, undefined, 'span');
      const r = div(f, { display: 'block', alignSelf: 'stretch', height: '3px', background: color || 'currentColor' }, undefined, 'span');
      const d = div(f, { display: 'block', fontSize: scale + 'em', padding: '0.04em 0.1em 0' }, undefined, 'span');
      n.parts = put(n, num); d.parts = put(d, den);
      f.num = n; f.rule = r; f.den = d;
      return f;
    };
  }
  function rich(parent, parts, { size = 56, font = 'serif', color, style = {} } = {}) {
    const e = div(parent, Object.assign(FONT[font](size), color ? { color } : {}, style));
    return fill(e, parts);
  }
  function line(parent, x, y, parts, { size = 56, font = 'serif', align = 'left', color, style = {} } = {}) {
    const st = Object.assign(FONT[font](size), color ? { color } : {});
    const ls = font === 'label' ? LS * size : 0, BIG = 4000;
    if (align === 'center') Object.assign(st, { left: (x - BIG / 2) + 'px', width: BIG + 'px', textAlign: 'center', paddingLeft: ls + 'px' });
    else if (align === 'right') Object.assign(st, { left: (x - BIG + ls) + 'px', width: BIG + 'px', textAlign: 'right' });
    else st.left = x + 'px';
    st.top = y + 'px';
    const e = el(parent, 'div', Object.assign(st, style));
    return fill(e, parts);
  }
  const cline = (parent, y, parts, opts = {}) => line(parent, W / 2, y, parts, Object.assign({}, opts, { align: 'center' }));
  function crow(parent, y, { gap = 40, x, align = 'center' } = {}) {
    const st = { top: y + 'px', display: 'flex', alignItems: 'center', columnGap: gap + 'px' };
    if (x !== undefined) Object.assign(st, { left: x + 'px' });
    else Object.assign(st, { left: 0, width: W + 'px', justifyContent: align === 'center' ? 'center' : 'flex-start' });
    return el(parent, 'div', st);
  }

  // ---- timing --------------------------------------------------------------------------------------------
  function inout(tl, e, at, out, { dy = 16, dur = 0.6 } = {}) {
    fadeIn(tl, e, at, dur, dy);
    if (out != null) fadeOut(tl, e, out, 0.35, -Math.max(8, dy * 0.6));
    return e;
  }
  function label(tl, parent, x, y, parts, at, out, { size = 34, color = C.dim, align = 'left', style } = {}) {
    return inout(tl, line(parent, x, y, parts, { size, font: 'label', color, align, style }), at, out, { dy: 10, dur: 0.5 });
  }
  const each = els => [].concat(els);
  const leave = (tl, els, at, { dur = 0.35 } = {}) => { for (const e of each(els)) fadeOut(tl, e, at, dur, -12); };
  const dim = (tl, els, o, at, { dur = 0.5 } = {}) => { for (const e of each(els)) tl.to(e, { o }, at, dur); };
  function pulse(tl, e, at, { scale = 1.08, dur = 0.6 } = {}) {
    tl.to(e, { s: scale }, at, dur * 0.4, E.out); tl.to(e, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io);
  }
  function markEl(tl, e, color, at, { out = null, pad = 12, fill = 0.14, dur = 0.4 } = {}) {
    if (!e.style.position || e.style.position === 'static') e.style.position = 'relative';
    e.style.isolation = 'isolate';   // the box (z-index -1) stays behind e's text, and in front of the room
    const m = el(e, 'div', { left: -pad + 'px', right: -pad + 'px', top: -pad * 0.4 + 'px', bottom: -pad * 0.4 + 'px', borderRadius: '12px', background: alpha(color, fill), boxShadow: `inset 0 0 0 1.5px ${alpha(color, 0.55)}`, zIndex: -1, transformOrigin: 'left center', opacity: 0 });
    tl.set(m, { o: 0, sx: 0.2 }, 0); tl.to(m, { o: 1, sx: 1 }, at, dur, E.out5);
    if (out != null) tl.to(m, { o: 0 }, out, 0.35);
    return m;
  }
  function strikeEl(tl, e, at, { dur = 0.4 } = {}) {
    if (!e.style.position || e.style.position === 'static') e.style.position = 'relative';
    const b = el(e, 'div', { left: '-0.08em', right: '-0.08em', top: '52%', height: '3px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
    tl.set(b, { sx: 0 }, 0); tl.to(b, { sx: 1 }, at, dur, E.io);
    tl.to(e, { color: C.faint }, at, dur);
    for (const s of e.querySelectorAll('span')) if (s.style.color) tl.to(s, { color: C.faint }, at, dur);
    return b;
  }
  function alt(tl, parent, list, { size = 56, font = 'serif', align = 'start', style = {} } = {}) {
    const g = div(parent, Object.assign(FONT[font](size), { display: 'grid', justifyItems: align, alignItems: 'baseline' }, style));
    g.alts = list.map((p, k) => { const a = fill(div(g, { gridArea: '1 / 1' }), p); if (k) tl.set(a, { o: 0 }, 0); return a; });
    let cur = 0;
    g.show = (k, at) => {
      if (k === cur) return g;
      tl.to(g.alts[cur], { o: 0, y: -8 }, at, 0.2, E.in);
      tl.set(g.alts[k], { y: 10 }, at); tl.to(g.alts[k], { o: 1, y: 0 }, at + 0.2, 0.35, E.out5);
      cur = k; return g;
    };
    return g;
  }
  function retext(tl, e, text, at) { tl.to(e, { o: 0 }, at, 0.2, E.in); tl.text(e, text, at + 0.2); tl.to(e, { o: 1 }, at + 0.2, 0.3); }
  // a green tick: in a line (a part) or at a place
  function tickSvg(tl, parent, at, size, style) {
    const s = el(parent, 'svg');
    s.setAttribute('width', size * 1.3); s.setAttribute('height', size * 1.3);
    Object.assign(s.style, { overflow: 'visible' }, style);
    const k = tick(tl, s, size * 0.65, size * 0.65, size, C.good, size / 9);
    tl.to(k, { draw: 1 }, at, 0.45, E.out);
    s.path = k;
    return s;
  }
  const tickPart = (tl, at, size = 56) => parent => tickSvg(tl, parent, at, size, { position: 'relative', display: 'inline-block', verticalAlign: 'middle', marginLeft: '0.2em' });
  const tickAt = (tl, parent, x, y, at, { size = 56 } = {}) => tickSvg(tl, parent, at, size, { position: 'absolute', left: (x - size * 0.65) + 'px', top: (y - size * 0.65) + 'px' });

  // ---- code ----------------------------------------------------------------------------------------------
  const progY = n => (n >= 8 ? 200 : n >= 6 ? 240 : n >= 4 ? 300 : 360);
  const look = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out, pad: 10 });
  const lineOf = l => t => t.line === l;
  const hook = (cm, ret) => [
    `h = rand(Normal({mu|${cm ? '170' : '1.7'}|n}, {sd|${cm ? '50' : '0.5'}|n}))`,
    'if rand(Bernoulli({p|0.5|n}))',
    `  observe(Normal(h, {so|${cm ? '10' : '0.1'}|n}), {ob|${cm ? '200' : '2.0'}|n})`,
    'end',
  ].concat(ret ? ['return h'] : []).join('\n');
  const fix = cm => [
    `h = rand(Normal({mu|${cm ? '170' : '1.7'}|n}, {sd|${cm ? '50' : '0.5'}|n}))`,
    'if rand(Bernoulli({p|0.5|n}))',
    `  observe(Normal(h, {so|${cm ? '10' : '0.1'}|n}), Interval({ob|${cm ? '200' : '2.0'}|n}, ${cm ? '{ik|100*|n}' : ''}{iw|eps}))`,
    'end',
    'return h',
  ].join('\n');
  const P = {
    HOOK_M: hook(false, false), HOOK_CM: hook(true, false), HOOK_M5: hook(false, true), HOOK_CM5: hook(true, true),
    WEIGHT: [
      'weight = 1',
      'h = rand(Normal({mu|1.7|n}, {sd|0.5|n}))',
      'if rand(Bernoulli({p|0.5|n}))',
      '  weight *= pdf(Normal(h, {so|0.1|n}), {ob|2.0|n})',
      'end',
      'return h',
    ].join('\n'),
    DICE1: 'function twoDice()\n  x = rand(DiscreteUniform(1,6))\n  y = rand(DiscreteUniform(1,6))\n  observe(x + y == 8)\n  return x\nend',
    DICE2: 'x = rand(DiscreteUniform(1,6))\ny = rand(DiscreteUniform(1,6))\nb = rand(Bernoulli(0.5))\nif b\n  observe(x + y == 8)\nend\nreturn x',
    DICE3: 'x = rand(DiscreteUniform(1,6))\nb = rand(Bernoulli(0.5))\nif b\n  observe(DiscreteUniform(1,6), 8 - x)\nend\nreturn x',
    NORM: 'x = rand(Normal(2,3))\nobserve(Normal(2,3), 8 - x)\nreturn x',
    BMI: 'h = rand(Normal(1.7, 0.5))\nw = rand(Normal(70, 30))\nif rand(Bernoulli(0.5))\n  observe(Normal(h, 0.1), 2.0)\nelse\n  observe(Normal(w, 5), 90)\nend\nbmi = w / h^2',
    BMI_EPS: 'h = rand(Normal(1.7, 0.5))\nw = rand(Normal(70, 30))\nif rand(Bernoulli(0.5))\n  observe(Normal(h, 0.1), (2.0, A*eps))\nelse\n  observe(Normal(w, 5), (90, B*eps))\nend\nbmi = w / h^2',
    DB: 'x = rand(Normal(10,5))\nobserve(Normal(15,5), x)\nreturn exp(x)',
    ENERGY: 'a = rand(LogNormal(10,5))\nobserve(LogNormal(15,5), a)\nreturn a',
    DB_EPS: 'x = rand(Normal(10,5))\nobserve(Normal(15,5), (x,eps))\nreturn exp(x)',
    ENERGY_EPS: 'exp_x = rand(LogNormal(10,5))\nobserve(LogNormal(15,5), (exp_x,exp_x*eps))\nreturn exp_x',
    FIX_M: fix(false), FIX_CM: fix(true),
  };

  // ---- a table of runs -----------------------------------------------------------------------------------
  const wv = (v, unit) => unit ? [[v, C.pat], ' ', [unit, C.bind]] : [[v, C.pat]];
  function runsTable(tl, root, rows, { y = 300, x, cx = W / 2, size = 52, labelSize = 34, rowGap = 22, colGap = 40, plus = false } = {}) {
    const st = { top: y + 'px', display: 'grid', gridTemplateColumns: 'auto auto auto auto', alignItems: 'center', columnGap: colGap + 'px', rowGap: rowGap + 'px' };
    if (x !== undefined) st.left = x + 'px';
    else Object.assign(st, { left: (cx - 2000) + 'px', width: '4000px', justifyContent: 'center' });
    const g = el(root, 'div', st);
    const T = { el: g, rows: [] };
    rows.forEach((r, i) => {
      if (i === 1 && plus) {
        div(g, {}); div(g, {});
        T.plusEl = rich(g, '+', { size: size * 1.1, style: { justifySelf: 'start', lineHeight: 0.9 } });
        div(g, {});
        tl.set(T.plusEl, { o: 0 }, 0);
      }
      const lab = rich(g, r.label, { size: labelSize, font: 'label', style: { justifySelf: 'end' } });
      const w = rich(g, 'weight', { size, color: C.dim, style: { justifySelf: 'start' } });
      const val = alt(tl, g, r.values || [r.value], { size, style: { justifySelf: 'start' } });
      const note = rich(g, r.note || '', { size: labelSize, font: 'label', style: { justifySelf: 'start' } });
      const cells = [lab, w, val];
      for (const c of cells.concat([note])) tl.set(c, { o: 0 }, 0);
      T.rows.push({ lab, w, val, note, cells });
    });
    T.showRow = (i, at) => { T.rows[i].cells.forEach((c, j) => fadeIn(tl, c, at + j * 0.06, 0.6, 14)); return T; };
    T.show = (at, step = 0.45) => { T.rows.forEach((_, i) => T.showRow(i, at + i * step)); return T; };
    T.value = (i, k, at) => { T.rows[i].val.show(k, at); return T; };
    T.dimRow = (i, o, at, dur = 0.5) => { for (const c of T.rows[i].cells.concat([T.rows[i].note])) tl.to(c, { o: Math.min(o, 1) }, at, dur); return T; };
    T.pulse = (i, at) => { pulse(tl, T.rows[i].val, at); return T; };
    T.hideRow = (i, at) => { leave(tl, T.rows[i].cells.concat([T.rows[i].note]), at); return T; };
    T.hide = at => { tl.to(g, { o: 0, y: -12 }, at, 0.35, E.in); return T; };
    T.showNote = (i, at, out) => { inout(tl, T.rows[i].note, at, out, { dy: 10, dur: 0.5 }); return T; };
    T.showPlus = at => { tl.to(T.plusEl, { o: 1 }, at, 0.4); return T; };
    return T;
  }

  // ---- a number line, and a bell curve over one ----------------------------------------------------------
  function layer(root) {
    const e = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const svg = svgLayer(e);
    return { e, svg };
  }
  function axisIn(tl, L, { x0, x1, y, from, to, ticks = [], fmt = v => String(v), tickSize = 28, unit, width = 3 }) {
    const A = { el: L.e, svg: L.svg, y, X: v => x0 + (v - from) / (to - from) * (x1 - x0) };
    A.line = path(tl, L.svg, `M ${x0 - 20} ${y} L ${x1 + 20} ${y}`, { stroke: C.dim, width });
    A.ticks = ticks.map(v => {
      const X = A.X(v);
      const mark = path(tl, L.svg, `M ${X} ${y - 10} L ${X} ${y + 10}`, { stroke: C.dim, width });
      const text = box(L.e, X - 100, y + 18, Object.assign(SERIF(tickSize), { width: '200px', textAlign: 'center', color: C.dim }), fmt(v));
      tl.set(text, { o: 0 }, 0);
      return { v, mark, text };
    });
    if (unit !== undefined) { A.unitEl = box(L.e, x1 + 34, y - tickSize * 0.62, Object.assign(SERIF(tickSize + 4), { color: C.bind }), unit); tl.set(A.unitEl, { o: 0 }, 0); }
    A.show = (at, dur = 0.6) => {
      tl.to(A.line, { draw: 1 }, at, dur, E.io);
      A.ticks.forEach((t, i) => { tl.to(t.mark, { draw: 1 }, at + dur * 0.5 + i * 0.06, 0.3); fadeIn(tl, t.text, at + dur * 0.5 + i * 0.06, 0.5, 8); });
      if (A.unitEl) fadeIn(tl, A.unitEl, at + dur, 0.5, 8);
      return A;
    };
    A.retick = (texts, at) => { A.ticks.forEach((t, i) => retext(tl, t.text, texts[i], at)); return A; };
    A.reunit = (text, at) => { retext(tl, A.unitEl, text, at); return A; };
    A.hide = at => { tl.to(L.e, { o: 0, y: -12 }, at, 0.35, E.in); return A; };
    return A;
  }
  function axis(tl, root, opts) { return axisIn(tl, layer(root), opts); }
  function bell(tl, root, { cx = W / 2, y = 720, w = 1000, h = 380, mu = 0, sd = 1, from, to, ticks = [], fmt, tickSize = 28, unit, stroke = 4.5 } = {}) {
    if (from === undefined) from = mu - 3.3 * sd;
    if (to === undefined) to = mu + 3.3 * sd;
    const L = layer(root);
    L.e.style.transformOrigin = `${cx}px ${y - h / 2}px`;
    const B = axisIn(tl, L, { x0: cx - w / 2, x1: cx + w / 2, y, from, to, ticks, fmt, tickSize, unit });
    B.Y = v => y - h * Math.exp(-0.5 * ((v - mu) / sd) ** 2);
    B.top = y - h;
    let d = '';
    for (let i = 0; i <= 200; i++) { const v = from + (to - from) * i / 200; d += (i ? ' L ' : 'M ') + B.X(v).toFixed(1) + ' ' + B.Y(v).toFixed(1); }
    B.curve = path(tl, L.svg, d, { stroke: C.ink, width: stroke });
    const axisShow = B.show;
    B.show = (at) => { axisShow(at - 0.1, 0.6); tl.to(B.curve, { draw: 1 }, at + 0.2, 0.9, E.io); return B; };
    const bandD = (a, b) => {
      const n = 40; let s = `M ${B.X(a).toFixed(2)} ${y}`;
      for (let i = 0; i <= n; i++) { const v = a + (b - a) * i / n; s += ` L ${B.X(v).toFixed(2)} ${B.Y(v).toFixed(2)}`; }
      return s + ` L ${B.X(b).toFixed(2)} ${y} Z`;
    };
    B.band = (a, b, { at = 0, color = C.pat, fill = 0.32 } = {}) => {
      const p = el(L.svg, 'path');
      L.svg.insertBefore(p, L.svg.firstChild);
      p.setAttribute('stroke-width', 2); p.setAttribute('stroke-linejoin', 'round');
      Object.assign(p.style, { fill: alpha(color, fill), stroke: color });
      p._a = a; p._b = b;
      const redraw = e => e.setAttribute('d', bandD(e._a, e._b));
      tl.custom(p, 'a', (e, v) => { e._a = v; redraw(e); }, a);
      tl.custom(p, 'b', (e, v) => { e._b = v; redraw(e); }, b);
      tl.set(p, { a, b, o: 0 }, 0);
      redraw(p);
      tl.to(p, { o: 1 }, at, 0.5);
      return { el: p, to: (a2, b2, t, dur = 0.8, ease = E.io) => { tl.to(p, { a: a2, b: b2 }, t, dur, ease); }, hide: t => tl.to(p, { o: 0 }, t, 0.35) };
    };
    B.vline = (v, { at = 0, dash = true, color = C.ink, width = 3, full = false } = {}) => {
      const X = B.X(v), top = full ? B.top - 20 : B.Y(v);
      // a dashed line fades in; a solid one draws upward
      const p = path(tl, L.svg, `M ${X} ${y} L ${X} ${top}`, { stroke: color, width, cap: dash ? 'butt' : 'round', dash: dash ? '12 10' : undefined });
      if (dash) { tl.set(p, { o: 0 }, 0); tl.to(p, { o: 1 }, at, 0.4); return p; }
      tl.to(p, { draw: 1 }, at, 0.4, E.io);
      return p;
    };
    B.dot = (v, { at = 0, color = C.pat, r = 11, stem = true } = {}) => {
      let st = null;
      if (stem) { st = path(tl, L.svg, `M ${B.X(v)} ${y} L ${B.X(v)} ${B.Y(v)}`, { stroke: color, width: 4 }); tl.to(st, { draw: 1 }, at, 0.45, E.io); }
      const c = el(L.svg, 'circle');
      c.setAttribute('cx', B.X(v)); c.setAttribute('cy', B.Y(v)); c.setAttribute('r', r);
      c.style.fill = color;
      tl.set(c, { o: 0 }, 0); tl.to(c, { o: 1 }, at + (stem ? 0.35 : 0), 0.3);
      return { dot: c, stem: st };
    };
    return B;
  }

  // ---- a row of trials -----------------------------------------------------------------------------------
  function dots(tl, root, { n, y, x, cx = W / 2, size = 36, gap = 26, label: lab, labelSize = 34, color = C.code } = {}) {
    const width = n * size + (n - 1) * gap, x0 = x !== undefined ? x : Math.round(cx - width / 2);
    const row = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const D = { el: row, y, dots: [], X: i => x0 + i * (size + gap) + size / 2 };
    if (lab !== undefined) D.label = line(row, x0 - 30, y - labelSize * 0.6, lab, { size: labelSize, font: 'label', align: 'right' });
    const strip = box(row, x0, y - size / 2, { width: width + 'px', height: size + 'px' });
    D.strip = strip;
    for (let i = 0; i < n; i++) {
      const d = box(strip, i * (size + gap), 0, { width: size + 'px', height: size + 'px' });
      d.dot = box(d, 0, 0, { width: size + 'px', height: size + 'px', borderRadius: '50%', background: color });
      tl.set(d, { o: 0 }, 0);
      D.dots.push(d);
    }
    if (D.label) tl.set(D.label, { o: 0 }, 0);
    D.show = (at, stagger = 0.03) => { if (D.label) fadeIn(tl, D.label, at - 0.05, 0.5, 10); D.dots.forEach((d, i) => fadeIn(tl, d, at + i * stagger, 0.5, 12)); return D; };
    D.strike = (i, at) => {
      const d = D.dots[i];
      const bar = box(d, -size * 0.25, size / 2 - 2, { width: size * 1.5 + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
      tl.set(bar, { sx: 0 }, 0); tl.to(bar, { sx: 1 }, at, 0.25, E.io);
      tl.to(d.dot, { bg: C.faint }, at, 0.3);
      return D;
    };
    D.strikeAll = (at, step = 0.15, except = []) => { let k = 0; D.dots.forEach((_, i) => { if (!except.includes(i)) D.strike(i, at + (k++) * step); }); return D; };
    D.keep = (i, at) => { tl.to(D.dots[i].dot, { bg: C.good }, at, 0.35); pulse(tl, D.dots[i], at, { scale: 1.15, dur: 0.5 }); return D; };
    D.mark = (col, at, { out = null } = {}) => markEl(tl, strip, col, at, { out, pad: 18 });
    D.hide = at => { tl.to(row, { o: 0, y: -12 }, at, 0.35, E.in); return D; };
    return D;
  }

  // ---- a title card --------------------------------------------------------------------------------------
  function titleCard(tl, root, { lines: L, size = 104, x = RAIL, y = 330, align = 'left', at, step = 0.5, sub, subSize = 46, subAt, label: lab, labelSize = 34, labelAt } = {}) {
    const lx = align === 'center' ? W / 2 : x, lh = size * 1.12;
    const out = { lines: [] };
    L.forEach((t, i) => {
      const e = line(root, lx, y + i * lh, t, { size, align, style: { letterSpacing: '-0.012em' } });
      const ta = Array.isArray(at) ? at[i] : at + i * step;
      if (ta != null) fadeIn(tl, e, ta, 0.8, 22); else tl.set(e, { o: 0 }, 0);
      out.lines.push(e);
    });
    let yy = y + L.length * lh + size * 0.28;
    if (sub !== undefined) {
      const subs = [].concat(sub);
      out.sub = subs.map((t, i) => {
        const e = line(root, lx, yy + i * subSize * 1.3, t, { size: subSize, align, style: { fontStyle: 'italic', color: C.ink } });
        if (subAt != null) fadeIn(tl, e, subAt + i * 0.12, 0.7, 16); else tl.set(e, { o: 0 }, 0);
        return e;
      });
      yy += subs.length * subSize * 1.3 + subSize * 0.7;
    }
    if (lab !== undefined) {
      out.label = line(root, lx, yy, lab, { size: labelSize, font: 'label', align });
      if (labelAt != null) fadeIn(tl, out.label, labelAt, 0.5, 10); else tl.set(out.label, { o: 0 }, 0);
    }
    return out;
  }

  window.PX = {
    LS, RAIL, SERIF, LABEL, MONO, div, rich, line, cline, crow, label, lc, EPS, mono, sup, sub, frac,
    inout, leave, dim, pulse, markEl, strikeEl, alt, retext, tick: tickPart, tickAt,
    progY, look, lineOf, P, wv, runsTable, axis, bell, dots, titleCard,
  };
})();

// ==== src/scenes/a_open.js ====
// The opening and the close: the hook (a program whose answer changes with the unit), the roadmap, the title, and
// at the end the recap and the closing card. Built on PX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { RAIL } = PX;

  // ============================================ hook ===========================================================
  // The program is centred at size 64; what is said about it, then the result, come under it.
  scene('hook', ({ tl, root, cue }) => {
    const S = 64, y0 = 188;
    const x0 = Math.round((W - 30 * charWidth(S)) / 2);
    const code = new Code(tl, root, x0, y0, S), lh = code.lh;
    const tP = cue('prog'), tH = cue('h'), tC = cue('coin'), tO = cue('obs'), tA = cue('ask'), tM = cue('m'), tCm = cue('cm'),
      tE = cue('exp'), tG = cue('got'), tU = cue('unit'), tPr = cue('promise');
    // "Here is a probabilistic program."
    code.show(PX.P.HOOK_M, tP - 0.2, { stagger: 0.008 });
    // one line at a time, with what it is under the program
    const underY = y0 + 4 * lh + 40;
    PX.look(code, PX.lineOf(0), tH - 0.1, tC - 0.2);
    PX.label(tl, root, x0, underY, 'a height, in meters', tH + 0.1, tC - 0.3);
    PX.look(code, PX.lineOf(1), tC - 0.1, tO - 0.2);
    // "Then it flips a coin": the label comes at "coin"
    PX.label(tl, root, x0, underY, 'a coin', tC + 0.75, tO - 0.3);
    PX.look(code, PX.lineOf(2), tO - 0.1, tA - 0.3);
    // "and only if the coin comes up heads, it observes that a noisy measurement ... came out as two meters"
    const ob = PX.label(tl, root, x0, underY, ['only on heads: ', 'a noisy measurement, 2.0'], tO + 0.05, tA - 0.3);
    tl.set(ob.parts[1], { o: 0 }, 0); tl.to(ob.parts[1], { o: 1 }, tO + 3.1, 0.5);

    // under the program, the question and its answers
    const RY = 712;
    const ans = PX.crow(root, RY, { gap: 0 });
    const pre = PX.rich(ans, 'E[h] ', { size: 96 });
    const slot = PX.alt(tl, ans, ['= ?', ['≈ 1.81 ', ['m', C.bind]]], { size: 96 });
    // "What is the expected height?"
    for (const e of [pre, slot]) PX.inout(tl, e, tA + 0.2, tCm - 0.2, { dur: 0.6 });
    // "Run it, and the answer is about one point eight one."
    slot.show(1, tM + 1.35);
    // "Now write the same program in centimeters.": the result has left; the numbers change in place
    const tSw = tCm + 1.35;
    code.swap(PX.P.HOOK_CM, tSw, { dur: 0.5 });
    const changed = ['mu', 'sd', 'so', 'ob'];
    code.pulse(changed, tSw + 0.5, { dur: 0.9 });
    // "Converting, we would expect a hundred and eighty-one."
    const exp = PX.label(tl, root, W / 2, RY - 62, ['expected: ', ['181', C.ink]], tE + 1.0, tU - 0.25, { size: 36, align: 'center' });
    tl.set(exp.parts[1], { o: 0 }, 0); tl.to(exp.parts[1], { o: 1 }, tE + 1.65, 0.4);
    // "We get a hundred and seventy."
    const got = PX.cline(root, RY, ['E[h] ≈ 170 ', ['cm', C.bind]], { size: 96 });
    PX.inout(tl, got, tG + 0.4, tU - 0.25);
    code.hide(tU - 0.25, 0.4);
    // "The answer depends on the unit of measurement."
    const same = PX.label(tl, root, W / 2, 392, 'the same program', tU - 0.1, null, { size: 36, align: 'center' });
    const neq = PX.cline(root, 440, ['1.81 ', ['m', C.bind], '  ', ['≠', C.bad], '  170 ', ['cm', C.bind]], { size: 110 });
    PX.inout(tl, neq, tU - 0.1, null, { dy: 20, dur: 0.7 });
    // "... and we will know what the answer should be."
    PX.label(tl, root, W / 2, 628, 'what should the answer be?', tPr + 3.6, null, { size: 36, align: 'center' });
  });

  // ---- rows of a list: a number, a statement, and one piece of evidence at ex --------------------------------
  // the row being read is bright; when the next arrives, the earlier ones step back to 60 %
  function rowList(tl, root, { top, pitch, size, ex }) {
    const rows = [];
    const add = (title, at) => {
      const i = rows.length, y = top + pitch * i;
      const num = PX.line(root, RAIL, y + size * 0.3, String(i + 1), { font: 'label', size: 32 });
      const t = PX.line(root, RAIL + 64, y, title, { size });
      fadeIn(tl, num, at - 0.15, 0.5, 12); fadeIn(tl, t, at - 0.1, 0.6, 16);
      if (rows.length) for (const e of rows[i - 1].parts) tl.to(e, { o: 0.6 }, at - 0.25, 0.5);
      const r = { y, at, parts: [num, t] };
      rows.push(r);
      return r;
    };
    // evidence: serif parts, or code (a Code object at size 40), set level with the row's text
    const ev = (r, parts, at, { size: s = size, x = ex } = {}) => {
      const e = PX.line(root, x, r.y + (size - s) * 0.62, parts, { size: s });
      fadeIn(tl, e, at, 0.5, 14); r.parts.push(e); return e;
    };
    const code = (r, src, at, { x = ex, s = 40 } = {}) => {
      const c = new Code(tl, root, x, r.y + (size * 1.22 - Math.round(s * 1.62)) / 2 + 2, s);
      c.show(src, at, { stagger: 0.01 }); r.parts.push(c.root); return c;
    };
    return { add, ev, code, rows };
  }

  // ============================================ roadmap ========================================================
  scene('roadmap', ({ tl, root, cue }) => {
    PX.label(tl, root, RAIL, 180, 'in this video', cue('coming') - 0.15, null, { color: C.ink });
    const L = rowList(tl, root, { top: 270, pitch: 124, size: 56, ex: 1000 });
    // "First, what a program like this means, on two dice."
    const r1 = L.add('What a program means', cue('mean'));
    L.code(r1, 'observe(x + y == 8)', cue('mean') + 2.6);
    // "Then how such programs are run, with weights,"
    const r2 = L.add('How it is run', cue('run'));
    L.code(r2, 'weight *= …', cue('run') + 2.5);
    // "and where that goes wrong: three paradoxes."
    const r3 = L.add('Three paradoxes', cue('wrong'));
    L.ev(r3, ['1.81 ', ['m', C.bind], '  ', ['≠', C.bad], '  170 ', ['cm', C.bind]], cue('wrong') + 0.6);
    // "Then what the answer should be."
    const r4 = L.add('What the answer should be', cue('should'));
    L.ev(r4, 'E[h] = ?', cue('should') + 0.45);
    // "And then the fix, which computes with infinitesimal numbers."
    const r5 = L.add('The fix', cue('fix') + 0.6);
    L.code(r5, 'Interval(2.0, {e|eps|p})', cue('inf') + 0.7);
  });

  // ============================================ title ==========================================================
  // The poster frame.
  scene('title', ({ tl, root, cue }) => {
    PX.titleCard(tl, root, {
      lines: ['Paradoxes of', 'Probabilistic Programming'], size: 104, x: RAIL, y: 330,
      at: [cue('title') - 0.15, cue('title') + 0.85],
      sub: ['And how to condition on events of measure zero', 'with infinitesimal probabilities'], subSize: 46, subAt: cue('sub') - 0.15,
      label: 'Jules Jacobs  ·  POPL 2021', labelAt: cue('sub') + 2.4,
    });
  });

  // ============================================ recap ==========================================================
  scene('recap', ({ tl, root, cue }) => {
    const L = rowList(tl, root, { top: 200, pitch: 112, size: 50, ex: 1260 });
    // "We began with a program whose answer changed with the unit of measurement."
    const r1 = L.add('The answer changed with the unit', cue('p1'));
    L.ev(r1, ['1.81 ', ['m', C.bind], '  ', ['≠', C.bad], '  170 ', ['cm', C.bind]], cue('p1') + 2.8);
    // "The cause was an observe that multiplies by a density."
    const r2 = L.add('The cause: a density', cue('p2'));
    L.code(r2, 'weight *= {pdf|pdf|p}{a|(|p}{D|D|p}{c|,|p} {x|x|p}{b|)|p}', cue('p2') + 2.4);
    // "The repair is to observe an interval, and to let its width be infinitesimal."
    const r3 = L.add('The repair: an interval of infinitesimal width', cue('p3'));
    L.code(r3, 'observe(D, (x, w*{e|eps|p}))', cue('p3') + 1.35);
    // "Then observe is rejection again, and an event of probability zero is a limit of events ..."
    const r4 = L.add([PX.mono('observe', C.ink), ' is rejection again'], cue('p4'));
    L.ev(r4, 'width → 0', cue('p4') + 4.9);
    // "The program says which limit it means."
    const r5 = L.add('The program says which limit', cue('p5'));
    L.code(r5, 'A*{e1|eps|p}   B*{e2|eps|p}', cue('p5') + 0.8);
    // "And both units give the same answer: one point seven meters."
    const r6 = L.add('One answer', cue('p6'));
    L.ev(r6, [['1.7', C.good], ' ', ['m', C.bind], ' ', ['=', C.good], ' ', ['170', C.good], ' ', ['cm', C.bind], PX.tick(tl, cue('p6') + 3.0, 50)], cue('p6') + 2.25);
  });

  // ============================================ end ============================================================
  scene('end', ({ tl, root, cue }) => {
    const tI = cue('impl'), tT = cue('title'), tP = cue('paper');
    // "All of this is implemented as a small library in the Julia language."
    const S = 48, src = 'estimate = importance(1000000,example1_m)';
    const lab = PX.label(tl, root, W / 2, 400, 'an embedded language in Julia', tI - 0.1, tT - 0.4, { align: 'center' });
    const code = new Code(tl, root, Math.round((W - src.length * charWidth(S)) / 2), 468, S);
    code.show(src, tI - 0.1, { stagger: 0.008 });
    code.hide(tT - 0.4, 0.35);
    const res = PX.cline(root, 590, ['≈ 1.7'], { size: 72, color: C.good });
    PX.inout(tl, res, tI + 1.6, tT - 0.4);
    // "Paradoxes of probabilistic programming."
    PX.titleCard(tl, root, {
      lines: ['Paradoxes of Probabilistic Programming'], size: 88, align: 'center', y: 320, at: tT - 0.15,
      label: 'Jules Jacobs  ·  POPL 2021', labelAt: tT + 1.2,
    });
    // "The paper has the proofs, a discussion of measurements with finite precision, and what remains to be done
    // for other inference algorithms." The list is too long for one line: a heading and one line per item, each
    // at its words.
    PX.label(tl, root, W / 2, 580, 'in the paper', tP - 0.1, null, { size: 32, align: 'center' });
    const items = [['the proofs', 0.85], ['measurements with finite precision', 2.45], ['what remains for other inference algorithms', 4.6]];
    items.forEach(([t, dt], i) => PX.label(tl, root, W / 2, 650 + i * 52, t, tP + dt, null, { size: 32, align: 'center' }));
    return { keep: true };
  });
})();

// ==== src/scenes/b.js ====
// What observe means: the two primitives, rejection on two dice, observe inside control flow, weights and importance
// sampling, the three things that agree for dice, and how densities break it. Built on PX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { RAIL } = PX;

  // a piece of code centred on the stage at size S, top at y (a Code object)
  const centred = (tl, root, src, y, S, opts) => {
    const n = Math.max(...src.replace(/\{[^}|]*\|([^}|]*)(\|[^}]*)?\}/g, '$1').split('\n').map(l => l.length));
    return new Code(tl, root, Math.round((W - n * charWidth(S)) / 2), y, S, opts);
  };
  // the y that puts a Code line of size S level with a serif line of size s whose top is y
  const level = (y, s, S) => Math.round(y + s * 1.22 / 2 - S * 1.62 / 2);

  // ============================================ dice_a, dice_b =================================================
  // One scene over two segments: the dice program stays at its place while it is run.
  scene(['dice_a', 'dice_b'], ({ tl, root, cue }) => {
    // ---- dice_a: the two operations
    const tR = cue('rand'), tO = cue('obs'), tD = cue('dice'), tC = cue('cond'), tRet = cue('ret'), tDist = cue('dist');
    // "A probabilistic program is an ordinary program with two extra operations.": the label that names what the
    // two items under it are (the stage was empty through this sentence)
    const langL = PX.label(tl, root, W / 2, 190, 'a probabilistic program: an ordinary program, plus', cue('lang') + 0.25, null, { align: 'center' });
    // "The first draws a random value from a distribution."
    const rand = centred(tl, root, 'rand(D)', 290, 64);
    rand.show('rand(D)', tR - 0.15, { stagger: 0.01 });
    const randL = PX.label(tl, root, W / 2, 400, 'draw a random value from a distribution', tR + 0.55, null, { align: 'center' });
    // "The second is observe, and it is what this video is about."
    const obs = centred(tl, root, 'observe(…)', 540, 64);
    obs.show('observe(…)', tO + 0.6, { stagger: 0.01 });
    PX.dim(tl, [rand.root, randL], 0.4, tO + 0.6);
    const obsL = PX.label(tl, root, W / 2, 650, 'this video', tO + 2.2, null, { align: 'center' });
    // "Here is an example."
    rand.hide(tD - 0.4, 0.35); obs.hide(tD - 0.4, 0.35); PX.leave(tl, [randL, obsL, langL], tD - 0.4);
    const L = PX.P.DICE1.split('\n'), y0 = PX.progY(6);
    const code = new Code(tl, root, RAIL, y0, 48);
    code.show(L.slice(0, 3).join('\n'), tD - 0.1, { stagger: 0.008 });
    // "and observe that their sum is eight."
    code.morph(L.slice(0, 4).join('\n'), tC - 0.2, { dur: 0.5 });
    PX.look(code, PX.lineOf(3), tC + 0.2, tRet - 0.2);
    // "Then return X."
    code.morph(L.join('\n'), tRet - 0.2, { dur: 0.5 });
    // "The program stands for a distribution: the first die, given that the sum is eight."
    const DX = 1200;
    const distL = PX.label(tl, root, DX, 400, 'the program stands for', tDist - 0.15, cue('dice_b.how') - 0.1);
    const dist = PX.line(root, DX, 452, 'P(x | x + y = 8)', { size: 64 });
    PX.inout(tl, dist, tDist + 2.3, cue('dice_b.how') - 0.1);

    // ---- dice_b: rejection, one trial at a time
    const tH = cue('dice_b.how'), tT = cue('dice_b.trial'), tTe = cue('dice_b.test'), tRj = cue('dice_b.rej'),
      tK = cue('dice_b.keep'), tA = cue('dice_b.avg'), tM = cue('dice_b.mean');
    // "What does observe do?": the program steps back, all but its observe
    code.fade(t => t.line !== 3, 0.45, tH + 0.3, 0.5);
    // the trials: a column right of the program
    const X0 = 1160, RY = 300, PITCH = 80;
    const rows = [];
    const row = (i, x, y, at, sumAt) => {
      const e = PX.line(root, X0, RY + i * PITCH, [`x=${x}`, `  y=${y}   `, `x + y = ${x + y}`], { size: 44, font: 'mono' });
      PX.inout(tl, e, at, null, { dy: 14, dur: 0.5 });
      tl.set(e.parts[2], { o: 0 }, 0); tl.to(e.parts[2], { o: 1 }, sumAt, 0.4);
      rows.push(e);
      return e;
    };
    const tick = (i, at) => PX.tickAt(tl, root, X0 + 600, RY + i * PITCH + 30, at, { size: 44 });
    // "Run the program from the top. That is one trial."
    const r0 = row(0, 2, 3, tT - 0.15, tTe + 1.0);
    // "At the observe, test the condition."
    PX.look(code, PX.lineOf(3), tTe + 0.05, tRj + 0.6);
    // "If it is false, throw the trial away, and start again."
    const rejL = PX.label(tl, root, X0, 220, 'rejected', tRj + 0.55, tK - 0.2);
    PX.strikeEl(tl, r0, tRj + 0.95);
    // "If it is true, go on, and keep the returned value as a sample."
    row(1, 6, 2, tK - 0.15, tK - 0.15);
    const ticks = [tick(1, tK + 0.3)];
    const keepL = PX.label(tl, root, X0, 220, 'kept', tK + 1.95, tA - 0.2);
    // then quickly three more
    [[4, 1, false], [3, 5, true], [5, 3, true]].forEach(([x, y, ok], k) => {
      const at = tK + 2.5 + k * 0.45, i = 2 + k;
      const e = row(i, x, y, at, at);
      if (ok) ticks.push(tick(i, at + 0.25)); else PX.strikeEl(tl, e, at + 0.25, { dur: 0.3 });
    });
    // "The average of the kept samples estimates the expected value."
    for (const i of [1, 3, 4]) PX.markEl(tl, rows[i].parts[0], C.dim, tA + 0.7, { fill: 0.1, pad: 8 });
    const avg1 = PX.line(root, X0, 720, 'average of the kept x', { size: 44 });
    const avg2 = PX.line(root, X0, 782, '≈ E[x | x + y = 8]', { size: 44 });
    PX.inout(tl, avg1, tA - 0.1, tM - 0.2); PX.inout(tl, avg2, tA + 1.7, tM - 0.2);
    // "So observe means: continue only if this holds."
    PX.leave(tl, rows.concat(ticks), tM - 0.2);
    PX.look(code, PX.lineOf(3), tM + 0.2);
    const k1 = PX.line(root, X0, 400, 'observe: continue', { size: 60, style: { fontStyle: 'italic' } });
    const k2 = PX.line(root, X0, 474, 'only if this holds.', { size: 60, style: { fontStyle: 'italic' } });
    PX.inout(tl, k1, tM + 0.25); PX.inout(tl, k2, tM + 2.2);
  });

  // ============================================ dice_c =========================================================
  scene('dice_c', ({ tl, root, cue }) => {
    const tF = cue('flow'), tB = cue('b'), tE = cue('event'), tFi = cue('fine');
    // "Because this is a program, observe can sit inside control flow."
    const code = new Code(tl, root, RAIL, PX.progY(7), 48);
    code.show(PX.P.DICE2, tF - 0.2, { stagger: 0.006 });
    // "Here a coin decides whether the sum is observed at all."
    PX.look(code, PX.lineOf(2), tB + 0.5, tE - 0.2);
    PX.look(code, PX.lineOf(3), tB + 0.5, tE - 0.2);
    // "A trial is kept if the coin comes up tails, or if the sum is eight."
    const EX = 1250, S = 52;
    PX.label(tl, root, 1140, 360, 'a trial is kept when', tE - 0.1, null);
    const op = s => [s, C.ink, { fontFamily: 'var(--mono)', fontSize: '1.05em', lineHeight: 1 }];
    const e1 = PX.line(root, EX, 424, ['(b = true ', op('∧'), ' x + y = 8)'], { size: S });
    const e2 = PX.line(root, EX, 500, [op('∨'), ' (b = false)'], { size: S });
    PX.inout(tl, e2, tE + 2.0);           // "tails"
    PX.inout(tl, e1, tE + 3.4);           // "the sum is eight"
    // "That is a perfectly good event to condition on."
    const eName = PX.line(root, EX - 16, 424, 'E =', { size: S, align: 'right' });
    PX.inout(tl, eName, tFi - 0.1);
    const p = PX.line(root, 1140, 620, ['P(x | E)', PX.tick(tl, tFi + 1.0, 56)], { size: 60 });
    PX.inout(tl, p, tFi + 0.4);
  });

  // ============================================ weights ========================================================
  scene('weights', ({ tl, root, cue }) => {
    const tS = cue('slow'), tF = cue('form'), tMe = cue('means'), tRw = cue('rewrite'), tW = cue('weight'), tMu = cue('mul'),
      tWa = cue('wavg'), tI = cue('is');
    // "Rejection is wasteful. With dice of a thousand sides, almost every trial is thrown away."
    const D = PX.dots(tl, root, { n: 24, y: 420 });
    D.show(tS - 0.1, 0.02);
    PX.label(tl, root, W / 2, 490, 'dice with 1000 sides', tS + 2.6, tF - 0.25, { align: 'center' });
    const KEEP = 15;
    D.strikeAll(tS + 4.1, 0.09, [KEEP]);
    D.keep(KEEP, tS + 6.25);
    D.hide(tF - 0.25);
    // "So languages have a second form of observe. It takes a distribution and a value,"
    const form = centred(tl, root, 'observe(D, x)', 300, 64);
    form.show('observe(D, x)', tF + 1.35, { stagger: 0.01 });
    // "and it means: draw from the distribution, and continue only if the draw equals the value."
    PX.label(tl, root, W / 2, 452, 'means', tMe - 0.1, tRw - 0.25, { align: 'center' });
    const dimPal = { f: C.dim, v: C.dim, x: C.dim, n: C.dim, k: C.dim };
    const means = centred(tl, root, 'observe(rand(D) == x)', 510, 56, { palette: dimPal });
    means.show('observe(rand(D) == x)', tMe + 0.75, { stagger: 0.01 });
    form.hide(tRw - 0.25, 0.35); means.hide(tRw - 0.25, 0.35);
    // "The dice program can be written with it: observe that a fresh die equals eight minus X."
    const code = new Code(tl, root, RAIL, PX.progY(6), 48);
    code.show(PX.P.DICE3, tRw - 0.1, { stagger: 0.006 });
    PX.look(code, PX.lineOf(3), tRw + 2.1, tWa - 0.3);
    // "Each trial carries a weight, which starts at one."
    const S = 52, WY = 730;
    const w = new Code(tl, root, RAIL, WY, S);
    w.show('{w|weight} {eq|=} {one|1}', tW + 4.3, { stagger: 0.02 });
    // "At the observe, multiply the weight by the probability of that value"
    w.swap('{w|weight} {eq|*=} {P|P|p}{l|(|p}{D|D|p}{c|,|p} {x|x|p}{r|)|p}', tMu + 0.9, { dur: 0.5 });
    const wEnd = RAIL + 17 * charWidth(S);
    PX.label(tl, root, wEnd + 60, WY + (w.lh - 41) / 2, ['the probability of ', PX.lc('x'), ' in D'], tMu + 2.55, tWa - 0.3);
    // "At the end, take a weighted average of the results."
    code.hide(tWa - 0.25, 0.4);
    const toX = Math.round((W - 17 * charWidth(S)) / 2), toY = 330;
    w.move(toX - RAIL, toY - WY, tWa - 0.1, 0.8);
    const k = () => PX.sub('k');
    const avg = PX.cline(root, 480, ['E[V] ≈ ', PX.frac(['Σ weight', k(), ' · V', k()], ['Σ weight', k()])], { size: 60 });
    PX.inout(tl, avg, tWa + 1.2);
    // "This is called importance sampling."
    PX.label(tl, root, W / 2, 700, 'importance sampling', tI + 0.75, null, { align: 'center' });
  });

  // ============================================ cool_discrete ==================================================
  scene('cool_discrete', ({ tl, root, cue }) => {
    const tT = cue('three'), tO = cue('opt'), tS = cue('still'), tH = cue('hold');
    // "For dice, three things agree:"
    PX.label(tl, root, W / 2, 330, 'for dice', tT - 0.15, null, { align: 'center' });
    const row = PX.crow(root, 410, { gap: 56 });
    row.style.alignItems = 'flex-start';
    const item = (text, at, lab) => {
      const col = PX.div(row, { display: 'flex', flexDirection: 'column', alignItems: 'center', rowGap: '18px' });
      const t = PX.rich(col, text, { size: 56 });
      PX.inout(tl, t, at);
      const l = PX.rich(col, lab || ' ', { size: 34, font: 'label', style: { paddingLeft: PX.LS * 34 + 'px' } });
      tl.set(l, { o: 0 }, 0);
      return { t, l };
    };
    const eq = at => { const e = PX.rich(row, [['=', C.good]], { size: 56 }); PX.inout(tl, e, at); return e; };
    // "the exact conditional expectation, rejection, and the weighted average."
    const a = item('exact E[x | E]', tT + 2.45);
    const e1 = eq(tT + 4.75);
    const b = item('rejection', tT + 4.8, 'the meaning');
    const e2 = eq(tT + 6.25);
    const c = item('weighted average', tT + 6.3, 'an optimization');
    // "The weight is only an optimization:"
    PX.inout(tl, c.l, tO + 1.0, null, { dy: 10, dur: 0.5 });
    // "we can still think of every observe as rejecting a trial."
    PX.inout(tl, b.l, tS + 1.9, null, { dy: 10, dur: 0.5 });
    // "The rest of the video is about keeping that true."
    PX.dim(tl, [a.t, e1, e2, c.t, c.l], 0.35, tH - 0.15);
  });

  // ============================================ dens_a =========================================================
  scene('dens_a', ({ tl, root, cue }) => {
    const tC = cue('cont'), tZ = cue('zero'), tR = cue('rejall'), tWz = cue('wz'), tSo = cue('so'), tP = cue('pdf'),
      tEx = cue('ex'), tWo = cue('works');
    // "Now replace the dice by continuous distributions."
    const XV = 0.8;
    const B = PX.bell(tl, root, { cx: 960, y: 640, w: 1000, h: 330 });
    B.show(tC + 0.1);
    // the picture shrinks and moves right at "pdf"; its labels keep their size and go with it (each in a holder)
    const BS = 0.8, BDX = 290, BDY = 60, OX = 960, OY = 640 - 330 / 2;
    const holder = (x, y) => { const h = box(root, 0, 0, { width: '1px', height: '1px' }); h._at = [x, y]; return h; };
    const follow = (h, at) => { const [x, y] = h._at; tl.to(h, { x: (OX + (x - OX) * BS + BDX) - x, y: (OY + (y - OY) * BS + BDY) - y }, at, 0.8, E.io); };
    const hN = holder(1250, 350), hX = holder(B.X(XV), 672);
    const nm = PX.line(hN, 1250, 330, [PX.mono('Normal(μ, σ)')], { size: 49 });
    PX.inout(tl, nm, tC + 1.6);
    // "The probability that a draw from a normal distribution equals one exact value is zero."
    B.vline(XV, { at: tZ + 3.5 });
    const xl = PX.line(hX, B.X(XV), 652, 'x', { size: 40, align: 'center', style: { fontStyle: 'italic' } });
    PX.inout(tl, xl, tZ + 3.5, null, { dy: 8, dur: 0.5 });
    const fz = PX.line(root, 700, 740, ['P(rand(D) == x)', ' = ', ['0', C.pat]], { size: 56, align: 'center' });
    PX.inout(tl, fz, tZ + 0.25);
    tl.set(fz.parts[1], { o: 0 }, 0); tl.set(fz.parts[2], { o: 0 }, 0);
    tl.to(fz.parts[1], { o: 1 }, tZ + 4.85, 0.4); tl.to(fz.parts[2], { o: 1 }, tZ + 4.85, 0.4);
    // "Rejection would throw away every trial,"
    const D = PX.dots(tl, root, { n: 16, y: 210 });
    D.show(tR - 0.15, 0.02);
    D.strikeAll(tR + 0.8, 0.1);
    // "and every weight would be multiplied by zero."
    const wz = new Code(tl, root, 1170, level(740, 56, 52), 52);
    wz.show('weight *= {z|0|p}', tWz + 0.25, { stagger: 0.02 });
    // "So in practice, languages do something else."
    PX.leave(tl, [fz], tSo - 0.2); D.hide(tSo - 0.2); wz.hide(tSo - 0.2, 0.35);
    // "For a continuous distribution, observe multiplies the weight by the probability density at the value."
    tl.to(B.el, { s: BS, x: BDX, y: BDY }, tP - 0.2, 0.8, E.io);
    follow(hN, tP - 0.2); follow(hX, tP - 0.2);
    const pd = new Code(tl, root, RAIL, 480, 56);
    pd.show('weight *= {pdf|pdf|p}{a|(|p}{D|D|p}{c|,|p} {x|x|p}{b|)|p}', tP + 2.3, { stagger: 0.015 });
    B.dot(XV, { at: tP + 4.3 });
    PX.label(tl, root, RAIL, 590, ['the density of D at ', PX.lc('x')], tP + 4.3, null);
    // "Here is the continuous version of the dice"
    for (const e of root.children) if (e !== pd.root) tl.to(e, { o: 0, y: -12 }, tEx - 0.25, 0.35, E.in);
    pd.hide(tEx - 0.25, 0.35);
    const code = new Code(tl, root, RAIL, PX.progY(3), 52);
    code.show(PX.P.NORM, tEx - 0.05, { stagger: 0.008 });
    // "given that their sum is eight."
    const pr = PX.line(root, 1140, 452, ['P(x | x + y = 8)', PX.tick(tl, tWo + 1.15, 56)], { size: 56 });
    PX.inout(tl, pr, tEx + 4.05);
  });

  // ============================================ dens_b =========================================================
  scene('dens_b', ({ tl, root, cue }) => {
    const tB = cue('but'), tQ = cue('q'), tBk = cue('back');
    // "But a density is not a probability."
    const row = PX.crow(root, 360, { gap: 64 });
    row.style.alignItems = 'flex-start';
    const col = (code, lab, at) => {
      const c = PX.div(row, { display: 'flex', flexDirection: 'column', alignItems: 'center', rowGap: '14px' });
      const t = PX.rich(c, code, { size: 64, font: 'mono', color: C.pat });
      const l = PX.rich(c, lab, { size: 34, font: 'label', style: { paddingLeft: PX.LS * 34 + 'px' } });
      PX.inout(tl, t, at); PX.inout(tl, l, at + 0.15, null, { dy: 10, dur: 0.5 });
      return c;
    };
    const a = col('pdf(D, x)', 'a density', tB + 0.45);
    const ne = PX.rich(row, '≠', { size: 64, style: { paddingTop: '4px' } });
    PX.inout(tl, ne, tB + 1.15);
    const b = col('P(D, x)', 'a probability', tB + 1.7);
    // "Is observe still a rejection, in any sense?"
    const q = PX.cline(root, 580, 'Is observe still rejection?', { size: 60, style: { fontStyle: 'italic' } });
    PX.inout(tl, q, tQ - 0.15);
    // "Go back to the program from the beginning, with its if statement."
    tl.to(row, { o: 0, y: -12 }, tBk - 0.25, 0.35, E.in); PX.leave(tl, q, tBk - 0.25);
    const code = new Code(tl, root, RAIL, 300, 48);
    code.show(PX.P.HOOK_M5, tBk + 0.1, { stagger: 0.006 });
    PX.look(code, PX.lineOf(1), tBk + 2.45);
    PX.look(code, PX.lineOf(3), tBk + 2.45);
  });
})();

// ==== src/scenes/c.js ====
// Three paradoxes, the first: what the weights are (a density has a unit), why the answer changes with the unit,
// where the mistake is, and what the answer should be. Built on PX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { RAIL } = PX;

  // ---- local helpers ---------------------------------------------------------------------------------------
  // a column in a flex row: a line on top and, centred under it, a smaller one (its unit, its label)
  function col(parent, top, bot, { size = 52, botSize = 40, botFont = 'serif', gap = 4 } = {}) {
    const c = PX.div(parent, { display: 'flex', flexDirection: 'column', alignItems: 'center', rowGap: gap + 'px' });
    c.top = PX.rich(c, top, { size });
    c.bot = PX.rich(c, bot === undefined ? ' ' : bot, { size: botSize, font: botFont });
    return c;
  }
  // a part in serif inside a label (a symbol the sans face lacks, kept lower case)
  const serifIn = (t, colr) => [t, colr || null, { fontFamily: 'var(--serif)', textTransform: 'none', letterSpacing: '0', fontSize: '1.15em', fontWeight: 400, lineHeight: '1' }];
  // a logic symbol from the code face inside a serif line (the serif face lacks ∧ ∨ ∩)
  const sym = t => [t, null, { fontFamily: 'var(--mono)', fontSize: '1em', fontVariantLigatures: 'none', fontWeight: 400 }];
  const show = (tl, e, at) => { tl.set(e, { o: 0 }, 0); fadeIn(tl, e, at, 0.55, 14); return e; };

  // ============================================ why_a, why_b ===================================================
  // One scene over both segments: the runs table made under the program in why_a moves up and grows in why_b.
  scene(['why_a', 'why_b'], ({ tl, root, cue, seg }) => {
    const B = seg('why_b');
    const tRun = cue('run'), tW1 = cue('w1'), tPdf = cue('pdf'), tUnit = cue('unit'), tPer = cue('per'), tEx = cue('ex'), tSkip = cue('skip');
    // "This is what the language actually runs."
    const y0 = PX.progY(6);
    const runLab = PX.label(tl, root, RAIL, y0 - 66, 'what is run', tRun - 0.2, null);
    const code = new Code(tl, root, RAIL, y0, 48);
    code.show(PX.P.WEIGHT, tRun - 0.2, { stagger: 0.006 });
    // "The weight starts at one."
    PX.look(code, PX.lineOf(0), tW1 - 0.1, tPdf - 0.15);
    // "On heads, it is multiplied by a density": the mark moves to line 4, and at "density" the pdf turns amber
    PX.look(code, PX.lineOf(3), tPdf - 0.1, tEx - 0.2);
    code.color(t => t.line === 3 && t.col >= 12, C.pat, tPdf + 2.08, 0.5);

    // "And a density has a unit."
    const UY = 770;
    PX.label(tl, root, RAIL, UY, 'a density has a unit', tUnit - 0.1, tPer - 0.15);
    // "probability ≈ density × width", each word with its unit under it, at its words
    const pr = PX.crow(root, UY - 20, { gap: 30 });
    pr.style.alignItems = 'flex-start';
    const cP = col(pr, 'probability', [['no unit', C.bind]]);
    const cA = col(pr, '≈');
    const cD = col(pr, 'density', [['/ m', C.bind]]);
    const cX = col(pr, '×');
    const cWd = col(pr, 'width', [['m', C.bind]]);
    show(tl, cP.top, tPer + 0.17);
    show(tl, cA.top, tPer + 4.1); show(tl, cD.top, tPer + 4.1);
    show(tl, cX.top, tPer + 5.73); show(tl, cWd.top, tPer + 5.73);
    for (const c of [cA, cX]) tl.set(c.bot, { o: 0 }, 0);
    show(tl, cP.bot, tPer + 7.77);     // "A probability has no unit,"
    show(tl, cWd.bot, tPer + 9.3);     // "and the width is a length."
    show(tl, cD.bot, tPer + 12.13);    // "So the density is per meter."
    PX.leave(tl, pr, tEx - 0.2);

    // the runs: "Take a run that drew a height of one point nine five ... three point five per meter."
    const T = PX.runsTable(tl, root, [
      { label: ['a heads run, ', PX.lc('h'), ' = 1.95'], values: [PX.wv('3.5', '/ m'), PX.wv('0.035', '/ cm')], note: '100× smaller' },
      { label: 'a tails run', value: [['1', C.pat], ['no unit', C.bind, Object.assign(PX.LABEL(34), { color: C.bind, marginLeft: '0.7em', fontSize: '0.62em' })]] },
    ], { y: 740, size: 52 });
    const r0 = T.rows[0], r1 = T.rows[1];
    fadeIn(tl, r0.lab, tEx - 0.15, 0.6, 14);
    fadeIn(tl, r0.w, tEx + 5.64, 0.6, 14); fadeIn(tl, r0.val, tEx + 5.7, 0.6, 14);
    // "On tails, nothing is multiplied. The weight stays one, with no unit."
    fadeIn(tl, r1.lab, tSkip - 0.1, 0.6, 14);
    fadeIn(tl, r1.w, tSkip + 2.5, 0.6, 14); fadeIn(tl, r1.val, tSkip + 3.24, 0.6, 14);
    const noUnit = r1.val.alts[0].parts[1];
    tl.set(noUnit, { o: 0 }, 0); fadeIn(tl, noUnit, tSkip + 3.96, 0.5, 8);

    // ---- why_b: the program goes; the table moves up to the centre and grows (values at 64) -------------------
    const tAdd = cue('why_b.add'), tMix = cue('mix'), tCm = cue('cm'), tTails = cue('tails'), tShift = cue('shift'), tSlide = cue('slide');
    code.hide(B - 0.1, 0.4); PX.leave(tl, runLab, B - 0.1);
    T.el.style.transformOrigin = '50% 0';
    tl.custom(T.el, 'rg', (e, v) => { e.style.rowGap = v.toFixed(1) + 'px'; }, 22);
    tl.to(T.el, { y: 300 - 740, s: 64 / 52, rg: 80 }, B + 0.05, 0.85, E.io);
    // "The weighted average adds the weights of all runs.": a "+" between the two values
    const plus = el(r1.val, 'div', Object.assign(PX.SERIF(57), { left: '0', top: '-78px' }), '+');
    tl.set(plus, { o: 0 }, 0); fadeIn(tl, plus, tAdd + 1.0, 0.5, 8);
    // under the table, the sum
    const sum = PX.crow(root, 620, { gap: 0 });
    const s1 = PX.alt(tl, sum, [PX.wv('3.5', '/ m'), PX.wv('0.035', '/ cm')], { size: 60, align: 'end' });
    const s2 = PX.rich(sum, ['  ', '+', '  ', ['1', C.pat], '  +  …'], { size: 60 });
    for (const e of [s1, s2]) show(tl, e, tAdd + 1.56);
    const labRow = PX.crow(root, 716, { gap: 0 });
    const lab = PX.alt(tl, labRow, ['the weighted average adds them', [['different units', C.bad]], 'heads runs count 100× less'], { size: 34, font: 'label', align: 'center' });
    show(tl, lab, tAdd + 1.9);
    // "So it adds a number per meter to a number with no unit."
    PX.markEl(tl, s2.parts[1], C.bad, tMix + 0.36, { out: tShift - 0.2, pad: 14 });
    lab.show(1, tMix + 0.4);
    // "In centimeters, the same run has a weight of zero point zero three five per centimeter."
    T.value(0, 1, tCm + 4.44); s1.show(1, tCm + 4.44);
    // "The number is a hundred times smaller."
    T.showNote(0, tCm + 8.49, null);
    // "The tails runs still have weight one."
    T.pulse(1, tTails + 1.75);
    // "So the heads runs count for a hundred times less."
    lab.show(2, tShift - 0.2);
    // "And the answer slides from one point eight one toward one point seven"
    PX.dim(tl, T.el, 0.35, tSlide - 0.2);
    PX.leave(tl, [sum, labRow], tSlide - 0.2);
    const A = PX.axis(tl, root, { x0: 560, x1: 1360, y: 790, from: 1.65, to: 1.85, ticks: [1.70, 1.81], fmt: v => v.toFixed(2) });
    A.show(tSlide);
    // the marker: a dot on the axis, its value above it and what unit the run was in above that
    const mk = box(A.el, A.X(1.81) - 300, 0, { width: '600px', height: '1080px' });
    const dot = box(mk, 300 - 13, A.y - 13, { width: '26px', height: '26px', borderRadius: '50%', background: C.pat });
    const valRow = PX.crow(mk, A.y - 104, { x: 0 }); valRow.style.width = '600px'; valRow.style.justifyContent = 'center';
    const val = PX.alt(tl, valRow, ['1.81', ['1.70 = 170 ', ['cm', C.bind]]], { size: 52, align: 'center' });
    const unRow = PX.crow(mk, A.y - 154, { x: 0 }); unRow.style.width = '600px'; unRow.style.justifyContent = 'center';
    const un = PX.alt(tl, unRow, ['in meters', 'in centimeters'], { size: 32, font: 'label', align: 'center' });
    const tM = tSlide + 1.27;
    tl.set(dot, { o: 0, s: 0.3 }, 0); tl.to(dot, { o: 1, s: 1 }, tM, 0.4, E.out5);
    show(tl, val, tM); show(tl, un, tM + 0.1);
    tl.to(mk, { x: A.X(1.70) - A.X(1.81) }, tSlide + 2.6, 1.5, E.io);
    un.show(1, tSlide + 3.3);    // the value and its unit change together, at "one point seven"
    val.show(1, tSlide + 3.3);
    // "We will call that the prior."
    PX.label(tl, A.el, A.X(1.70), A.y + 66, 'the prior', tSlide + 8.15, null, { size: 32, align: 'center' });
  });

  // ============================================ cool_units =====================================================
  scene('cool_units', ({ tl, root, cue }) => {
    const tText = cue('text'), tIn = cue('inside'), tAll = cue('all');
    const S = 56, cw = charWidth(S);
    const x0 = Math.round((W - 30 * cw) / 2), y0 = 250;
    // "Nothing is wrong in the program text."
    const code = new Code(tl, root, x0, y0, S);
    code.show(PX.P.HOOK_M, tText - 0.2, { stagger: 0.006 });
    // "Its units are consistent.": each number gets its unit, a small raised tag
    const tags = ['mu', 'sd', 'so', 'ob'].map((id, i) => {
      const t = code.tokens.get(id).tok;
      const e = PX.line(root, x0 + (t.col + t.len) * cw + 3, y0 + t.line * code.lh - 28, [['m', C.bind]], { size: 34 });
      tl.set(e, { o: 0 }, 0); fadeIn(tl, e, tText + 2.6 + i * 0.12, 0.5, 8);
      return e;
    });
    const ok = PX.label(tl, root, W / 2, 666, ['units consistent', PX.tick(tl, tText + 3.9, 40)], tText + 3.68, tIn - 0.2, { align: 'center' });
    // "The inconsistency is inside the method that runs it."
    PX.dim(tl, [code.root, ...tags], 0.35, tIn - 0.1);
    const sum = PX.cline(root, 680, [['3.5', C.pat], ' ', ['/ m', C.bind], '  ', '+', '  ', ['1', C.pat]], { size: 64 });
    show(tl, sum, tIn - 0.1);
    PX.markEl(tl, sum.parts[4], C.bad, tIn + 0.25, { pad: 14 });
    PX.label(tl, root, W / 2, 790, 'inside the method', tIn + 1.32, null, { align: 'center' });
    // "other inference algorithms do the same arithmetic"
    PX.label(tl, root, W / 2, 846, 'the same in other inference algorithms', tAll + 2.07, null, { align: 'center' });
  });

  // ============================================ should_a, should_b =============================================
  // One scene over both: the question stays at the top until the answer replaces it.
  scene(['should_a', 'should_b'], ({ tl, root, cue, seg }) => {
    const S2 = seg('should_b');
    const tQ = cue('q'), tAn = cue('analogy'), tEv = cue('event'), tHalf = cue('half'), tNz = cue('notzero'), tDef = cue('defn');
    // "So what should the answer be?"
    const q = PX.cline(root, 420, 'E[h] = ?', { size: 96 });
    q.style.transformOrigin = '50% 0';
    show(tl, q, tQ - 0.2);
    // "Reason as we did for the dice."
    tl.to(q, { y: 170 - 420, s: 64 / 96 }, tAn - 0.15, 0.8, E.io);
    // "A trial is kept if the coin comes up tails, or if the measurement is exactly two."
    const keptLab = PX.label(tl, root, W / 2, 310, 'a trial is kept when', tEv - 0.15, null, { align: 'center' });
    const ev = PX.crow(root, 370, { gap: 0 });
    ev.style.alignItems = 'flex-start';
    const d1 = PX.rich(ev, ['(b = true ', sym('∧'), ' h′ = 2.0)'], { size: 60 });
    const orC = PX.rich(ev, ['  ', sym('∨'), '  '], { size: 60 });
    const d2 = PX.rich(ev, '(b = false)', { size: 60 });
    // the labels under the disjuncts (they take no room in the row): the measurement's name, then each case's
    // probability
    const under = e => el(e, 'div', { left: '-600px', right: '-600px', top: '100%', marginTop: '10px', display: 'flex', justifyContent: 'center' });
    const l1 = PX.alt(tl, under(d1), [[serifIn('h′'), ': the measurement'], ['probability ', ['0', C.pat]]], { size: 34, font: 'label', align: 'center' });
    const l2 = PX.alt(tl, under(d2), [['probability ', serifIn('½', C.pat)]], { size: 34, font: 'label', align: 'center' });
    show(tl, d2, tEv + 1.96);
    show(tl, orC, tEv + 2.76); show(tl, d1, tEv + 2.76);
    show(tl, l1, tEv + 3.56);
    // "The second case has probability zero. But the first has probability one half."
    l1.show(1, tHalf - 0.1);
    show(tl, l2, tHalf + 2.84);
    // "So this event does not have probability zero at all,"
    const pe = PX.cline(root, 560, ['P(E) = ', ['½', C.pat]], { size: 64 });
    show(tl, pe, tNz - 0.1);
    // "and the ordinary definition of conditional probability applies."
    const df = PX.cline(root, 690, ['P(A | E) = ', PX.frac(['P(A ', sym('∩'), ' E)'], 'P(E)'), PX.tick(tl, tDef + 2.63, 56)], { size: 60 });
    show(tl, df, tDef + 0.5);
    PX.leave(tl, [keptLab, ev, pe, df], S2 - 0.2);

    // ---- should_b ------------------------------------------------------------------------------------------
    const tRej = cue('rej'), tPr = cue('prior'), tAns = cue('ans'), tNo = cue('noeffect'), tCoin = cue('coin'), tTw = cue('twist');
    const DX = 300;
    const H = PX.dots(tl, root, { n: 12, y: 400, x: DX, label: 'heads', labelSize: 34 });
    const T = PX.dots(tl, root, { n: 12, y: 500, x: DX, label: 'tails', labelSize: 34 });
    const RX = H.X(11) + 18 + 40;
    // "a heads trial is rejected with probability one."
    H.show(tRej + 1.8);
    H.strikeAll(tRej + 2.6, 0.1);
    const rejLab = PX.label(tl, root, RX, 400 - 20, 'rejected with probability 1', tRej + 3.7, tAns - 0.2, { size: 32 });
    // "Only tails trials survive, and in those, the height is untouched."
    T.show(tRej + 5.3);
    const tMark = T.mark(C.good, tPr - 0.2);
    const keptH = PX.label(tl, root, RX, 500 - 20, ['kept: ', PX.lc('h'), ' untouched'], tPr + 1.0, tAns - 0.2, { size: 32 });
    // "The answer is the prior: one point seven meters, or a hundred and seventy centimeters."
    for (const D of [H, T]) { tl.to(D.el, { y: -230 }, tAns - 0.2, 0.8, E.io); PX.dim(tl, D.el, 0.4, tAns - 0.2); }
    PX.leave(tl, q, tAns - 0.3);
    const ans = PX.cline(root, 330, ['E[h] = ', ['1.7', C.good], ' ', ['m', C.bind], ' ', ['=', C.good], ' ', ['170', C.good], ' ', ['cm', C.bind], PX.tick(tl, tAns + 4.6, 72)], { size: 96 });
    tl.set(ans.parts[0], { o: 0 }, 0); fadeIn(tl, ans.parts[0], tAns + 0.1, 0.6, 16);
    [[1, 3, 1.64], [4, 9, 3.5]].forEach(([a, b, d]) => { for (let k = a; k <= b; k++) { tl.set(ans.parts[k], { o: 0 }, 0); fadeIn(tl, ans.parts[k], tAns + d + (k - a) * 0.04, 0.6, 16); } });
    PX.label(tl, root, W / 2, 470, 'the prior', tAns + 1.12, null, { align: 'center' });
    // "The whole if statement should have no effect."
    const S = 40, src = PX.P.HOOK_M5;
    const prog = new Code(tl, root, Math.round((W - 30 * charWidth(S)) / 2), 560, S);
    prog.show(src, tNo - 0.2, { stagger: 0.004, byLine: 0.06 });
    [1, 2, 3].forEach((l, i) => prog.strike(PX.lineOf(l), tNo + 0.32 + i * 0.15));
    // "remember that the coin is not known to have come up heads. Among the trials that are kept, tails has
    // probability one."
    prog.hide(tCoin - 0.2, 0.4);
    for (const D of [H, T]) tl.to(D.el, { o: 1 }, tCoin, 0.6);
    PX.label(tl, root, RX, 270 - 20, ['among the kept trials: ', ['tails', C.good]], tCoin + 4.76, tTw - 0.2, { size: 32 });
    PX.pulse(tl, tMark, tCoin + 6.6, { scale: 1.04 });
    for (const D of [H, T]) tl.to(D.el, { o: 0 }, tTw - 0.2, 0.35, E.in);
    // "a hundred and seventy was the one close to the truth, and only by an accident of the unit. One point eight
    // one was simply wrong."
    const tw = PX.crow(root, 640, { gap: 180 });
    tw.style.alignItems = 'flex-start';
    const a170 = col(tw, ['170 ', ['cm', C.bind]], 'close, by accident of the unit', { size: 64, botSize: 34, botFont: 'label', gap: 12 });
    const a181 = col(tw, [['1.81', C.bad], ' ', ['m', C.bind]], 'wrong', { size: 64, botSize: 34, botFont: 'label', gap: 12 });
    show(tl, a170.top, tTw + 2.25); show(tl, a170.bot, tTw + 4.0);
    show(tl, a181.top, tTw + 7.96); show(tl, a181.bot, tTw + 10.2);
  });
})();

// ==== src/scenes/d.js ====
// Two more paradoxes (type1: body mass index, type3: decibels and energy), the principle they break (cool_scale),
// and intervals (int_a, int_b, int_c as one scene so that the bell curve never blinks; int_d). Built on PX
// (common.js). Times written as numbers are word times from build/audio/<segment>.json (with the segment's pre).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { RAIL } = PX;

  // A double arrow drawn as an inline SVG part (the serif font has no ↔ or ⟺): `double` draws two parallel lines.
  // Its width is in em of the line it sits in.
  function arrowPart({ em = 1.6, double = false, color } = {}) {
    return parent => {
      const s = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      const fs = parseFloat(getComputedStyle(parent).fontSize) || parseFloat(parent.style.fontSize) || 56;
      const w = em * fs, h = fs * 0.6, m = h / 2, g = double ? fs * 0.085 : 0, hd = fs * 0.2, sw = Math.max(3, fs * 0.05);
      s.setAttribute('width', w); s.setAttribute('height', h); s.setAttribute('viewBox', `0 0 ${w} ${h}`);
      Object.assign(s.style, { display: 'inline-block', verticalAlign: '0.12em', margin: '0 0.3em', overflow: 'visible' });
      const p = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      const x0 = sw, x1 = w - sw;
      const lines = double ? `M ${x0 + hd * 0.5} ${m - g} L ${x1 - hd * 0.5} ${m - g} M ${x0 + hd * 0.5} ${m + g} L ${x1 - hd * 0.5} ${m + g}` : `M ${x0} ${m} L ${x1} ${m}`;
      const heads = `M ${x0 + hd} ${m - hd} L ${x0} ${m} L ${x0 + hd} ${m + hd} M ${x1 - hd} ${m - hd} L ${x1} ${m} L ${x1 - hd} ${m + hd}`;
      p.setAttribute('d', lines + ' ' + heads);
      p.setAttribute('fill', 'none'); p.setAttribute('stroke-width', sw); p.setAttribute('stroke-linecap', 'round'); p.setAttribute('stroke-linejoin', 'round');
      p.style.stroke = color || 'currentColor';
      s.appendChild(p);
      parent.appendChild(s);
      return s;
    };
  }
  // a symbol in Fira Code, in the line's colour, a little larger than PX.mono's code so that it holds its own
  const M = (t, em = 1.05) => [t, null, { fontFamily: 'var(--mono)', fontSize: em + 'em', fontVariantLigatures: 'none', letterSpacing: '0', textTransform: 'none' }];
  const MC = (t, col) => [t, col, { fontFamily: 'var(--mono)', fontSize: '1em', fontVariantLigatures: 'none', letterSpacing: '0', textTransform: 'none' }];

  // the BMI program, with ids on what changes (meters to centimeters; exact values to intervals)
  const bmi = ({ cm = false, eps = false, lines = 8 } = {}) => [
    `h = rand(Normal({mu|${cm ? '170' : '1.7'}|n}, {sd|${cm ? '50' : '0.5'}|n}))`,
    'w = rand(Normal(70, 30))',
    'if rand(Bernoulli(0.5))',
    `  observe(Normal(h, {so|${cm ? '10' : '0.1'}|n}), ${eps ? '(2.0, A*{e1|eps})' : `{ob|${cm ? '200' : '2.0'}|n}`})`,
    'else',
    `  observe(Normal(w, 5), ${eps ? '(90, B*{e2|eps})' : '90'})`,
    'end',
    cm ? 'bmi = w / (0.01 * h)^2' : 'bmi = w / h^2',
  ].slice(0, lines).join('\n');

  // ============================================ type1 ==========================================================
  scene('type1', ({ tl, root, cue }) => {
    const tMore = cue('more'), tB = cue('bmi'), tC = cue('coin'), tR = cue('ret'), tU = cue('units'), tS = cue('sum'),
      tCh = cue('change'), tZ = cue('zero');
    // "That was one paradox. There are two more."
    PX.label(tl, root, W / 2, 500, 'two more', tMore + 2.3, tB - 0.35, { size: 40, align: 'center' });
    // the program arrives in three parts
    const y0 = PX.progY(8), code = new Code(tl, root, RAIL, y0, 48), lh = code.lh;
    code.show(bmi({ lines: 2 }), tB - 0.15, { stagger: 0.008 });
    code.morph(bmi({ lines: 7 }), tC - 0.35, { dur: 0.5 });
    code.morph(bmi(), tR - 0.3, { dur: 0.5 });
    // what each branch multiplies by: "a density per meter", "a density per kilogram"
    const LX = 1120, mid = l => y0 + l * lh + lh / 2;
    const unitM = parent => PX.alt(tl, parent, [[['/ m', C.bind]], [['/ cm', C.bind]]], { size: 40, font: 'mono', style: { display: 'inline-grid' } });
    const dM = PX.line(root, LX, mid(3) - 26, [['density', C.pat], ' ', unitM], { size: 40, font: 'mono' });
    const dK = PX.line(root, LX, mid(5) - 26, [['density', C.pat], ' ', ['/ kg', C.bind]], { size: 40, font: 'mono' });
    PX.look(code, PX.lineOf(3), 15.55, 17.95);
    PX.inout(tl, dM, 15.6, tZ - 0.2);
    PX.look(code, PX.lineOf(5), 17.95, tS - 0.1);
    PX.inout(tl, dK, 18.0, tZ - 0.2);
    // "The weighted average adds the two."
    const plus = PX.line(root, LX + 6, mid(4) - 42, [['+', C.bad]], { size: 64 });
    PX.inout(tl, plus, 20.6, tZ - 0.2, { dy: 0 });
    PX.label(tl, root, LX + 70, mid(4) - 20, 'added', 20.75, tZ - 0.2);
    // "Change meters to centimeters, correct the formula for it, and the answer still changes."
    code.swap(bmi({ cm: true }).split('\n').slice(0, 7).concat(['bmi = w / h^2']).join('\n'), 23.05, { dur: 0.45 });
    dM.parts[2].show(1, 23.0);
    code.swap(bmi({ cm: true }), 24.1, { dur: 0.45 });
    PX.label(tl, root, RAIL, y0 + 8 * lh + 22, ['E[', PX.lc('bmi'), '] still changes'], 26.0, tZ - 0.2, { color: C.bad });
    // "And this time, every trial observes an exact value." The observes stay lit a moment, then all dims.
    code.fade(t => t.line !== 3 && t.line !== 5, 0.4, tZ - 0.1);
    code.fade(t => t.line === 3 || t.line === 5, 0.4, 31.8);
    // "The event really has probability zero, ..."
    const RX = 1140;
    const ev1 = PX.line(root, RX, 250, ['(b = true ', M('∧'), ' h′ = 2.0)'], { size: 52 });
    const ev2 = PX.line(root, RX, 318, [M('∨'), ' (b = false ', M('∧'), ' w′ = 90)'], { size: 52 });
    PX.inout(tl, ev1, 31.95); PX.inout(tl, ev2, 32.05);
    PX.label(tl, root, RX, 410, ['probability ', ['0', C.pat]], 33.3, null);
    // "... so the definition of conditional probability gives no answer at all."
    const fr = PX.line(root, RX + 10, 500, [PX.frac(['0'], ['0'])], { size: 72 });
    PX.inout(tl, fr, 35.1);
    PX.label(tl, root, RX, 712, 'no answer from', 37.3, null);
    PX.label(tl, root, RX, 754, 'the definition', 37.35, null);
  });

  // ============================================ type3 ==========================================================
  scene('type3', ({ tl, root, cue }) => {
    const tT = cue('third'), tP = cue('prog'), tR = cue('ret'), tCh = cue('change'), tS = cue('same'), tD = cue('diff'), tK = cue('known');
    PX.label(tl, root, W / 2, 500, 'no branch', tT + 1.3, tP - 0.35, { size: 40, align: 'center' });
    // "Draw X from a normal distribution. Observe that ... equals X. Then return the exponential of X."
    const y0 = 300, db = new Code(tl, root, RAIL, y0, 48), lh = db.lh;
    const DB = PX.P.DB.split('\n');
    db.show(DB[0], tP - 0.2, { stagger: 0.008 });
    db.morph(DB.slice(0, 2).join('\n'), 6.1, { dur: 0.5 });
    db.morph(PX.P.DB, tR - 0.25, { dur: 0.5 });
    // "Think of X as a sound level in decibels, and of its exponential as an energy."
    const under = y0 + 3 * lh + 34;
    PX.label(tl, root, RAIL, under, [PX.mono('x', C.ink), ': decibels'], 15.6, tCh + 0.2);
    PX.label(tl, root, RAIL, under + 52, [PX.mono('exp(x)', C.ink), ': energy'], 18.15, tCh + 0.2);
    // "Now write the same program on the energy scale."
    const EX = 1010, en = new Code(tl, root, EX, y0, 48);
    en.show(PX.P.ENERGY, 20.25, { stagger: 0.008 });
    PX.label(tl, root, EX, y0 - 66, 'the energy scale', 21.4, null);
    PX.label(tl, root, RAIL, y0 - 66, 'the decibel scale', 21.5, null);
    // "The two distributions become what is called log-normal,"
    PX.look(en, t => t.line === 0 && t.text === 'LogNormal', 25.15, tS + 0.3);
    PX.look(en, t => t.line === 1 && t.text === 'LogNormal', 25.2, tS + 0.3);
    // "and the event is the same event: two exponentials are equal exactly when their exponents are."
    const sameL = PX.label(tl, root, W / 2, 678, 'the same event', 27.3, null, { align: 'center' });
    const f = PX.cline(root, 730, ['x = y', arrowPart({ double: true, em: 1.5 }), 'exp(x) = exp(y)'], { size: 52 });
    PX.inout(tl, f, 28.5);
    // "Yet the two programs give different answers."
    PX.dim(tl, [sameL, f], 0.4, tD - 0.2);
    const ne = PX.line(root, 930, y0 + 2 * lh + lh / 2 - 46, [['≠', C.bad]], { size: 72, align: 'center' });
    PX.inout(tl, ne, tD + 0.1, null, { dy: 0 });
    PX.label(tl, root, 930, y0 + 3 * lh + 16, 'different answers', 34.5, null, { color: C.bad, align: 'center' });
    // "It is a version of what probability theory calls the Borel-Kolmogorov paradox."
    PX.label(tl, root, W / 2, 850, 'a version of the Borel–Kolmogorov paradox', 36.3, null, { align: 'center' });
  });

  // ============================================ cool_scale =====================================================
  scene('cool_scale', ({ tl, root, cue }) => {
    const tPr = cue('principle'), tC = cue('cause');
    const p1 = PX.cline(root, 300, 'The answer should not depend', { size: 64, style: { fontStyle: 'italic' } });
    const p2 = PX.cline(root, 300 + 82, 'on the scale we measure in.', { size: 64, style: { fontStyle: 'italic' } });
    PX.inout(tl, p1, tPr - 0.15, null, { dy: 20 }); PX.inout(tl, p2, tPr + 0.0, null, { dy: 20 });
    // "Meters or centimeters. Decibels or energy."
    const row = PX.crow(root, 530, { gap: 140 });
    const a = PX.rich(row, [['m', C.bind], arrowPart({ em: 1.3 }), ['cm', C.bind]], { size: 52 });
    const b = PX.rich(row, ['decibels', arrowPart({ em: 1.3 }), 'energy'], { size: 52 });
    PX.inout(tl, a, 6.95); PX.inout(tl, b, 8.8);
    // "And all three have one cause. An observe on an exact value multiplies by a density, ..."
    PX.dim(tl, [p1, p2, a, b], 0.4, tC);
    const S = 60, src = 'weight *= {a|pdf|p}{b|(|p}{c|D|p}{d|,|p} {e|x|p}{f|)|p}';
    const code = new Code(tl, root, Math.round((W - 19 * charWidth(S)) / 2), 690, S);
    code.show(src, 15.55, { stagger: 0.01 });
    // "... and a density depends on the scale."
    PX.label(tl, root, W / 2, 810, 'depends on the scale', 18.45, null, { align: 'center' });
  });

  // ============================================ int_a, int_b, int_c ============================================
  // One scene, so that the bell curve stays. In int_a it is on the right (a generic interval [a, b]); in int_b it
  // grows into the centre, where it is Normal(1.95, 0.1) on an axis in meters, drawn to scale.
  scene(['int_a', 'int_b', 'int_c'], ({ tl, root, cue, seg }) => {
    const A = t => seg('int_a') + t, Bt = t => seg('int_b') + t, Ct = t => seg('int_c') + t;
    // ---- int_a: "Not because dice are discrete, but because their weights were probabilities"
    const S60 = 60, pw = 'weight *= {p1|P|p}{p2|(|p}{p3|D|p}{p4|,|p} {p5|x|p}{p6|)|p}';
    const dice = new Code(tl, root, Math.round((W - 17 * charWidth(S60)) / 2), 380, S60);
    dice.show(pw, cue('prob') - 0.2, { stagger: 0.01 });
    dice.hide(cue('cont') - 0.25, 0.35);
    const dl = PX.label(tl, root, W / 2, 500, ['for dice: a probability', '     ', ['no unit', C.bind]], A(7.55), cue('cont') - 0.25, { align: 'center' });
    tl.set(dl.parts[2], { o: 0 }, 0); tl.to(dl.parts[2], { o: 1 }, A(10.05), 0.4);

    // the bell on the right: Normal(1.95, 0.1) (any normal looks the same), later moved and scaled into int_b's
    const mu = 1.95, sd = 0.1, from = mu - 3.3 * sd, to = mu + 3.3 * sd;
    const g1 = { cx: 1410, w: 760, y: 700, h: 340 }, g2 = { cx: 960, w: 1100, y: 720 };
    const k = g2.w / g1.w; g2.h = g1.h * k;
    const ia = 1.99, ib = 2.08;
    const B1 = PX.bell(tl, root, { cx: g1.cx, w: g1.w, y: g1.y, h: g1.h, mu, sd, from, to, ticks: [ia, ib], fmt: v => (v === ia ? 'a' : 'b'), tickSize: 32, stroke: 4.5 / k * 1.0 });
    B1.line.setAttribute('d', `M ${g1.cx - g1.w / 2 - 20 / k} ${g1.y} L ${g1.cx + g1.w / 2 + 20 / k} ${g1.y}`);
    for (const t of B1.ticks) t.text.style.fontStyle = 'italic';
    B1.show(cue('cont') - 0.1);
    // "the probability that a draw lands in an interval"
    const band1 = B1.band(ia, ib, { at: A(15.0) });
    const bl = PX.line(root, 1800, 336, [['P(', C.pat], PX.mono('rand(D)', C.pat), [' ', C.pat], M('∈'), [' I)', C.pat]], { size: 46, align: 'right', color: C.pat });
    PX.inout(tl, bl, A(15.0), cue('units') - 0.3);
    // left of it: "So let observe take an interval. It means: ... continue only if the draw lies in the interval."
    const ob = new Code(tl, root, RAIL, 220, 64);
    ob.show('observe(D, I)', cue('obs') - 0.2, { stagger: 0.01 });
    const ml = PX.label(tl, root, RAIL, 342, ['continue only if ', MC('rand(D) ', C.ink), MC('∈', C.ink), MC(' I', C.ink)], A(20.9), cue('units') - 0.3);
    // "It runs by multiplying the weight by that probability."
    const ex = new Code(tl, root, RAIL, 440, 52);
    ex.show('weight *= {p1|P|p}{p2|(|p}{p3|D|p}{p4|,|p} {p5|I|p}{p6|)|p}', A(27.3), { stagger: 0.01 });
    const cdf = new Code(tl, root, RAIL, 536, 44);
    cdf.show('{q1|P|p}{q2|(|p}{q3|D|p}{q4|,|p} {q5|[a,b]|p}{q6|)|p} = cdf(D, b) - cdf(D, a)', A(29.3), { stagger: 0.008 });
    // "Rejection is back, as the meaning of observe."
    PX.dim(tl, [ex.root, cdf.root], 0.4, cue('rej') - 0.1);
    const rj = PX.line(root, RAIL, 650, [PX.tick(tl, cue('rej') + 0.1, 48), ['  ', null], ['rejection, again', C.dim]], { size: 34, font: 'label' });
    PX.inout(tl, rj, cue('rej') - 0.15, cue('units') - 0.3, { dy: 10 });
    for (const c of [ob, ex, cdf]) c.hide(cue('units') - 0.3, 0.35);

    // ---- int_b: the bell grows into the centre ("And units are safe.")
    const tMv = cue('units') - 0.1, tSw = tMv + 1.0;
    for (const t of B1.ticks) tl.to(t.text, { o: 0 }, tMv - 0.2, 0.3);
    for (const t of B1.ticks) tl.to(t.mark, { o: 0 }, tMv - 0.2, 0.3);
    band1.hide(tMv - 0.2);
    tl.to(B1.el, { x: g2.cx - g1.cx, y: (g2.y - g2.h / 2) - (g1.y - g1.h / 2), s: k }, tMv, 0.9, E.io);
    tl.set(B1.el, { o: 1 }, 0); tl.set(B1.el, { o: 0 }, tSw);
    const fmtM = v => v.toFixed(1);
    const B = PX.bell(tl, root, { cx: g2.cx, w: g2.w, y: g2.y, h: g2.h, mu, sd, from, to, ticks: [1.8, 1.9, 2.0, 2.1], fmt: fmtM, tickSize: 32, unit: 'm', stroke: 4.5 });
    B.line.setAttribute('stroke-width', 3 * k);   // the axis as thick as the one that grew into it
    tl.set(B.el, { o: 0 }, 0); tl.set(B.el, { o: 1 }, tSw);
    tl.set(B.line, { draw: 1 }, tSw - 0.05); tl.set(B.curve, { draw: 1 }, tSw - 0.05);
    B.ticks.forEach((t, i) => { tl.to(t.mark, { draw: 1 }, tSw + i * 0.06, 0.3); fadeIn(tl, t.text, tSw + i * 0.06, 0.5, 8); });
    fadeIn(tl, B.unitEl, tSw + 0.3, 0.5, 8);
    // "Here is an interval around two meters, of width zero point one."
    const band = B.band(1.95, 2.05, { at: cue('m') - 0.2 });
    const S52 = 52, iv = new Code(tl, root, Math.round(g2.cx - 18 * charWidth(S52) / 2), 800, S52);
    iv.show('Interval({c|2.0|n}, {w|0.1|n})', Bt(3.0), { stagger: 0.01 });
    const P34 = PX.line(root, 1250, 330, [['P = 0.34', C.pat]], { size: 52 });
    PX.inout(tl, P34, Bt(6.5), cue('price') - 0.1);
    // "In centimeters, its center becomes two hundred, and its width becomes ten."
    B.retick(['180', '190', '200', '210'], cue('cmm') - 0.05);
    B.reunit('cm', cue('cmm') - 0.05);
    iv.swap('Interval({c|200|n}, {w|0.1|n})', Bt(9.45), { dur: 0.45 });
    iv.swap('Interval({c|200|n}, {w|10|n})', Bt(11.55), { dur: 0.45 });
    // "The area under the curve is the same, so the weight is the same."
    PX.pulse(tl, P34, cue('same') + 0.05, { scale: 1.1, dur: 0.7 });
    const tk = PX.tickAt(tl, root, 1505, 362, cue('same') + 0.45, { size: 48 });
    tl.set(tk, { o: 1 }, 0); tl.to(tk, { o: 0 }, cue('price') - 0.1, 0.35);
    PX.label(tl, root, 1250, 420, 'the same area,', Bt(13.2), cue('price') - 0.1, { size: 32 });
    PX.label(tl, root, 1250, 460, 'the same weight', Bt(15.3), cue('price') - 0.1, { size: 32 });
    // "A change of unit now changes the width as well, ..."
    const wd = PX.line(root, 1370, 803, ['0.1 ', ['m', C.bind], '  ', ['=', C.good], '  10 ', ['cm', C.bind]], { size: 52 });
    PX.inout(tl, wd, Bt(19.1), cue('price') - 0.1);

    // ---- int_c: "But we have changed the question." Back to meters.
    B.retick(['1.8', '1.9', '2.0', '2.1'], cue('price') - 0.1);
    B.reunit('m', cue('price') - 0.1);
    iv.swap('Interval({c|2.0|n}, {w|0.1|n})', cue('price') - 0.1, { dur: 0.45 });
    // "We wanted to observe exactly two meters"
    const vl = B.vline(2.0, { at: Ct(3.55), full: true });
    const exl = PX.label(tl, root, B.X(2.0), B.top - 76, 'exactly 2.0', Ct(3.6), null, { align: 'center' });
    // "We could choose a tiny width, say one ten-thousandth. But why that number?"
    band.to(2.0 - 0.00005, 2.0 + 0.00005, Ct(8.3), 1.4);
    tl.to(vl, { o: 0.35 }, Ct(8.3), 0.6);
    iv.swap('Interval({c|2.0|n}, {w|0.0001|n})', Ct(9.5), { dur: 0.45 });
    PX.label(tl, root, Math.round(g2.cx - 18 * charWidth(S52) / 2) + 21 * charWidth(S52) + 50, 815, 'why 0.0001?', Ct(11.3), cue('limit') - 0.1);
    // "What we want is the limit, as the width goes to zero."
    iv.hide(Ct(14.3), 0.35);
    const lim = PX.cline(root, 790, ['width → 0'], { size: 60 });
    PX.inout(tl, lim, Ct(14.6));
    // "But there is a catch." The picture steps back, then leaves for the quote.
    PX.dim(tl, [B.el, lim, exl], 0.3, cue('amb') - 0.1);
    PX.leave(tl, [B.el, lim, exl], cue('jaynes') - 0.3);
    // "Conditioning on an event of probability zero is ambiguous."
    const q1 = PX.cline(root, 330, '“the final result will and must depend', { size: 56 });
    const q2 = PX.cline(root, 330 + 74, 'on which limiting operation was specified.”', { size: 56 });
    PX.inout(tl, q1, cue('jaynes') - 0.1, null, { dy: 20 }); PX.inout(tl, q2, cue('jaynes') + 0.05, null, { dy: 20 });
    PX.label(tl, root, W / 2, 520, 'E. T. Jaynes, Probability Theory: The Logic of Science', cue('jaynes') + 0.6, null, { size: 32, align: 'center' });
    // "So the program has to say which limit it means."
    PX.label(tl, root, W / 2, 680, 'the program must say which limit', cue('say') - 0.1, null, { align: 'center', color: C.ink, size: 38 });
  });

  // ============================================ int_d ==========================================================
  scene('int_d', ({ tl, root, cue }) => {
    const y0 = PX.progY(8), code = new Code(tl, root, RAIL, y0, 48), lh = code.lh;
    // "Take the program that measures either height or body weight."
    code.show(bmi(), cue('bmi') - 0.15, { stagger: 0.006 });
    // "Give each observe an interval whose width is a constant times epsilon"
    code.swap(bmi({ eps: true }), 5.5, { dur: 0.45 });
    code.mark(t => t.line === 3 && t.col >= 26, C.pat, 7.7, { pad: 8 });
    code.mark(t => t.line === 5 && t.col >= 24, C.pat, 7.8, { pad: 8 });
    // "The constant A is a length. The constant B is a mass."
    const LX = 1350, mid = l => y0 + l * lh + lh / 2 - 20;
    const unit = t => [t, C.bind, { textTransform: 'none', letterSpacing: '0', fontFamily: 'var(--serif)', fontSize: '1.3em', fontWeight: 400 }];
    const la = PX.label(tl, root, LX, mid(3), ['a: a length   ', unit('m')], 12.95, null);
    const lb = PX.label(tl, root, LX, mid(5), ['b: a mass   ', unit('kg')], 14.85, null);
    // "As epsilon shrinks, both observes become exact."
    const BX = 720, BY = 690;
    const e0 = PX.line(root, BX, BY, [['ε', C.pat], ' → 0'], { size: 56 });
    PX.inout(tl, e0, 17.0, cue('part') - 0.2);
    code.pulse(['e1', 'e2'], 17.2, { color: C.pat });
    // "But the ratio of the two widths stays, and it matters."
    const r = PX.line(root, BX + 300, BY, [['A : B', C.pat]], { size: 56 });
    PX.inout(tl, r, 20.85, cue('part') - 0.2);
    PX.label(tl, root, BX + 300, BY + 84, 'stays', 22.2, cue('thousand') + 0.4);
    // "Make B a thousand times larger, and the second branch succeeds a thousand times more often."
    const th = PX.line(root, BX + 620, BY, [['B', C.pat], ' × 1000'], { size: 56 });
    PX.inout(tl, th, 25.25, cue('part') - 0.2);
    PX.label(tl, root, BX, BY + 84, 'the second branch succeeds', 27.0, cue('part') - 0.2);
    PX.label(tl, root, BX, BY + 126, '1000× more often', 27.1, cue('part') - 0.2);
    // "So the widths are part of the model."
    PX.label(tl, root, BX, BY + 40, 'the widths are part of the model', 31.0, cue('old') - 0.1, { color: C.ink, size: 36 });
    // "The old observe had no place to write them."
    // the program leaves (dimmed beside it, the old form read as part of the program's last line)
    PX.dim(tl, [code.root, la, lb], 0, cue('old') - 0.2);
    const S = 64, old = new Code(tl, root, Math.round((W - 13 * charWidth(S)) / 2), 420, S);
    old.show('observe(D, x)', 33.6, { stagger: 0.01 });
    PX.label(tl, root, W / 2, 540, 'no place for a width', 34.2, null, { align: 'center' });
  });
})();

// ==== src/scenes/e.js ====
// Infinitesimal probabilities: the arithmetic of r εⁿ, the probability of an interval of infinitesimal width, the
// first program run with it in both units, the general rule (fewer exact observations win), the BMI program (ε
// cancels), and the theorem that this computes the limit, with the convergence plot. Built on PX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { RAIL } = PX;
  const EPS = ['ε', C.pat];                       // ε in a serif line
  const SUP = t => PX.sup(t, C.pat);              // a power of ε
  const ITAL = t => [t, null, { fontStyle: 'italic' }];

  // A label hanging under an element of a line (its host), centred on it or starting at its left edge. A local
  // helper: PX places labels on the stage, this one places them by the host's own box, wherever the flow put it.
  function under(tl, host, parts, at, out, { size = 32, dy = 6, align = 'center', color = C.dim } = {}) {
    if (!host.style.position || host.style.position === 'static') host.style.position = 'relative';
    const st = { position: 'absolute', top: '100%', marginTop: dy + 'px', color };
    if (align === 'center') Object.assign(st, { left: '-1000px', right: '-1000px', textAlign: 'center', paddingLeft: PX.LS * size + 'px' });
    else Object.assign(st, { left: '0px' });
    const e = PX.rich(host, parts, { size, font: 'label', style: st });
    PX.inout(tl, e, at, out, { dy: 10, dur: 0.5 });
    return e;
  }
  // parts of an element shown later than the element itself
  const later = (tl, parts, at, dur = 0.45) => { for (const p of [].concat(parts)) { tl.set(p, { o: 0 }, 0); tl.to(p, { o: 1 }, at, dur, E.out5); } };
  // "lim" with "w → 0" set under it, on the line's baseline
  const LIM = (sub = 'w → 0') => parent => {
    const f = PX.div(parent, { display: 'inline-flex', flexDirection: 'column', alignItems: 'center', lineHeight: 1.05, margin: '0 0.12em' }, undefined, 'span');
    PX.div(f, { display: 'block' }, 'lim', 'span');
    PX.div(f, { display: 'block', fontSize: '0.5em' }, sub, 'span');
    return f;
  };

  // ============================================ eps_a ==========================================================
  // ε arrives large in the centre, then becomes the ε of "r εⁿ" at the top left; the rules come in a column under it.
  scene('eps_a', ({ tl, root, cue }) => {
    const tSym = cue('sym'), tNum = cue('num'), tReal = cue('real'), tMul = cue('mul'), tAdd = cue('add'), tLow = cue('low'),
      tDiv = cue('div'), tPair = cue('pair');
    const HY = 168, RW = 76;                       // the header's top; the width given to "r"
    // the header, laid out on one baseline: r | εⁿ | (r ε⁰ = r, later "= (r, n)")
    const head = box(root, RAIL, HY, { display: 'flex', alignItems: 'baseline' });
    const r = PX.rich(head, 'r', { size: 110, style: { width: RW + 'px' } });
    const en = PX.rich(head, [EPS, SUP('n')], { size: 110 });
    const eps = en.parts[0], n = en.parts[1];
    PX.div(head, { width: '72px' });
    const slot = PX.alt(tl, head, [
      ['r ', EPS, SUP('0'), ' = r'],
      [['= (r, n)', C.code, { fontFamily: 'var(--mono)', fontSize: '56px', fontVariantLigatures: 'none' }]],
    ], { size: 64 });
    // "Treat epsilon as a symbol.": the ε of the header, scaled up and in the centre of the stage
    const k = 200 / 110, cx0 = RAIL + RW + 0.23 * 110, cy0 = HY + 0.61 * 110;
    const dx = W / 2 - cx0, dy = 470 - cy0;
    tl.set(eps, { x: dx, y: dy + 22, s: k, o: 0 }, 0);
    tl.to(eps, { y: dy, o: 1 }, tSym + 0.2, 0.7, E.out5);
    // "An infinitesimal number is a real number times a power of epsilon."
    tl.to(eps, { x: 0, y: 0, s: 1 }, tNum - 0.15, 0.85, E.io);
    fadeIn(tl, r, tNum + 0.45, 0.6, 14); fadeIn(tl, n, tNum + 0.45, 0.6, 10);
    under(tl, r, 'a real number', tNum + 1.8, tMul - 0.35, { align: 'left', dy: 54, size: 32 });
    under(tl, en, ['a power of ', PX.EPS], tNum + 3.15, tMul - 0.35, { align: 'left', dy: 4, size: 32 });
    // "Power zero gives the ordinary numbers."
    tl.set(slot, { o: 0 }, 0); tl.to(slot, { o: 1 }, tReal - 0.2, 0.6, E.out5);
    tl.to(slot.alts[0], { o: 0.45 }, tMul - 0.3, 0.5);

    // the rules: rule on the left, an example at x = 1100; the newest is bright, the earlier ones at 45 %
    const rows = [];
    const rule = (i, parts, ex, at, exAt) => {
      const y = 400 + 110 * i;
      const a = PX.line(root, RAIL, y, parts, { size: 56 }), b = PX.line(root, 1100, y, ex, { size: 56 });
      fadeIn(tl, a, at, 0.6, 16); fadeIn(tl, b, exAt, 0.6, 16);
      for (const p of rows) for (const e of p) tl.to(e, { o: 0.45 }, at - 0.1, 0.5);
      rows.push([a, b]);
    };
    // "To multiply, multiply the real parts, and add the powers."
    rule(0, ['(r ', EPS, SUP('n'), ') · (s ', EPS, SUP('k'), ') = (r·s) ', EPS, SUP('n+k')],
      ['2 ', EPS, ' · 3 ', EPS, ' = 6 ', EPS, SUP('2')], tMul - 0.15, tMul + 2.4);
    // "To add two numbers with the same power, add the real parts."
    rule(1, ['r ', EPS, SUP('n'), ' + s ', EPS, SUP('n'), ' = (r + s) ', EPS, SUP('n')],
      ['3.5 ', EPS, ' + 0.8 ', EPS, ' = 4.3 ', EPS], tAdd - 0.15, tAdd + 2.2);
    // "To add numbers with different powers, keep the one with the lower power."
    rule(2, ['r ', EPS, SUP('n'), ' + s ', EPS, SUP('k'), ' = r ', EPS, SUP('n'), '   (n < k)'],
      ['1 + 3.5 ', EPS, ' = 1'], tLow - 0.15, tLow + 1.85);
    // "Division subtracts the powers."
    rule(3, [PX.frac(['r ', EPS, SUP('n')], ['s ', EPS, SUP('k')]), ' = ', PX.frac('r', 's'), ' ', EPS, SUP('n−k'), '   (s ≠ 0)'],
      [PX.frac(['6 ', EPS, SUP('2')], ['2 ', EPS]), ' = 3 ', EPS], tDiv - 0.15, tDiv + 0.85);
    // "Each number is just a pair, so the arithmetic is cheap."
    for (const p of rows) for (const e of p) tl.to(e, { o: 0.7 }, tPair - 0.15, 0.5);
    slot.show(1, tPair + 0.95);
    under(tl, slot.alts[1], 'a pair', tPair + 1.2, null, { align: 'left', dy: 4, size: 32 });
  });

  // ============================================ eps_b ==========================================================
  // Left: what the probability of an interval is; right: a bell whose band narrows to a hairline, and a magnified
  // inset of the strip.
  scene('eps_b', ({ tl, root, cue }) => {
    const tP = cue('prob'), tF = cue('fin'), tI = cue('infw'), tT = cue('thin'), tU = cue('unit'), tN = cue('name');
    const B = PX.bell(tl, root, { cx: 1420, y: 760, w: 640, h: 360, mu: 0, sd: 1 });
    B.show(tP - 0.1);
    const M = 0.35;
    const band = B.band(M - 0.45, M + 0.45, { at: tP + 1.35 });
    // the midpoint x on the axis
    const xm = path(tl, B.svg, `M ${B.X(M)} ${B.y - 12} L ${B.X(M)} ${B.y + 12}`, { stroke: C.ink, width: 3 });
    tl.to(xm, { draw: 1 }, tP + 1.4, 0.3);
    const xl = PX.line(B.el, B.X(M), B.y + 16, [['x', null, { fontStyle: 'italic' }]], { size: 34, align: 'center' });
    fadeIn(tl, xl, tP + 1.4, 0.5, 8);

    // "Now the probability of an interval."
    const pl = PX.line(root, RAIL, 270, 'P(D, (x, w))', { size: 52, font: 'mono' });
    fadeIn(tl, pl, tP + 0.3, 0.6, 14);
    const l1 = PX.label(tl, root, RAIL, 352, 'an interval:', tP + 1.3, tI + 0.7, { size: 32 });
    const l2 = PX.label(tl, root, RAIL, 394, ['midpoint ', PX.lc('x'), ', width ', PX.lc('w')], tP + 1.4, tI + 0.7, { size: 32 });
    // "If its width is an ordinary number, it is the area under the curve, as before."
    const cdf = PX.line(root, RAIL, 470, 'cdf(D, x + ½w) - cdf(D, x - ½w)', { size: 44, font: 'mono' });
    fadeIn(tl, cdf, tF - 0.1, 0.6, 14);
    PX.label(tl, root, RAIL, 540, [PX.lc('w'), ' an ordinary number'], tF + 1.0, tI + 0.7, { size: 32 });
    tl.to(band.el, { fill: alpha(C.pat, 0.6) }, tF + 2.7, 0.4); tl.to(band.el, { fill: alpha(C.pat, 0.32) }, tF + 3.4, 0.7);
    // "If its width is infinitesimal, it is the density times the width."
    tl.to(cdf, { o: 0.4 }, tI + 0.7, 0.5);
    band.to(M - 0.06, M + 0.06, tI + 0.85, 0.9);
    // the product, with its units under its factors (a grid: factor over unit)
    const g = box(root, RAIL, 620, { display: 'grid', gridTemplateColumns: 'auto auto auto auto', columnGap: '18px', rowGap: '6px', alignItems: 'baseline', justifyItems: 'center' });
    const cell = (parts, opts) => PX.rich(g, parts, opts);
    const MONO = { size: 52, font: 'mono', color: C.pat };
    const f1 = cell('pdf(D, x)', MONO), f2 = cell('·', MONO), f3 = cell(['r ', ['ε'], PX.sup('n')], MONO);
    const wl = cell(['w = r ', EPS, SUP('n')], { size: 44, color: C.dim, style: { justifySelf: 'start', marginLeft: '30px' } });
    const UN = { size: 44, color: C.bind };
    const u1 = cell('/ m', UN), u2 = cell('×', { size: 44 }), u3 = cell('m', UN), u4 = cell(['= ', ['no unit', C.bind]], { size: 44, style: { justifySelf: 'start', marginLeft: '30px' } });
    for (const e of [f1, f2, f3]) fadeIn(tl, e, tI + 2.0, 0.6, 14);
    fadeIn(tl, wl, tI + 3.4, 0.5, 10);
    // "That is the area of a strip so thin that the curve is flat across it."
    band.to(M - 0.006, M + 0.006, tT - 0.1, 0.8);
    const ICX = 1640, ICY = 282, IR = 150;
    const L = box(root, 0, 0, { width: W + 'px', height: '1080px' }), sv = svgLayer(L);
    const ns = 'http://www.w3.org/2000/svg';
    const cp = document.createElementNS(ns, 'clipPath'); cp.id = 'eps-b-inset';
    const cc = document.createElementNS(ns, 'circle'); cc.setAttribute('cx', ICX); cc.setAttribute('cy', ICY); cc.setAttribute('r', IR - 2);
    cp.appendChild(cc); sv.appendChild(cp);
    const grp = el(sv, 'g'); grp.setAttribute('clip-path', 'url(#eps-b-inset)');
    const top = ICY - 72, base = ICY + 92, hw = 26;
    const rect = el(grp, 'rect');
    rect.setAttribute('x', ICX - hw); rect.setAttribute('y', top); rect.setAttribute('width', 2 * hw); rect.setAttribute('height', base - top);
    Object.assign(rect.style, { fill: alpha(C.pat, 0.32), stroke: C.pat, strokeWidth: 2 });
    path(tl, grp, `M ${ICX - 170} ${base} L ${ICX + 170} ${base}`, { stroke: C.dim, width: 3 });
    const slope = 0.1;
    path(tl, grp, `M ${ICX - 170} ${top - 170 * slope} L ${ICX + 170} ${top + 170 * slope}`, { stroke: C.ink, width: 4.5 });
    // its height and its width, as dimension lines
    const dl = ICX - hw - 26, db = base + 22;
    path(tl, grp, `M ${dl} ${top} L ${dl} ${base} M ${dl - 8} ${top} L ${dl + 8} ${top} M ${dl - 8} ${base} L ${dl + 8} ${base}`, { stroke: C.dim, width: 2.5 });
    path(tl, grp, `M ${ICX - hw} ${db} L ${ICX + hw} ${db} M ${ICX - hw} ${db - 8} L ${ICX - hw} ${db + 8} M ${ICX + hw} ${db - 8} L ${ICX + hw} ${db + 8}`, { stroke: C.dim, width: 2.5 });
    for (const p of grp.querySelectorAll('path')) { tl.set(p, { draw: 1 }, 0); }
    tl.set(grp, { o: 0 }, 0);
    const ring = el(sv, 'circle'); ring.setAttribute('cx', ICX); ring.setAttribute('cy', ICY); ring.setAttribute('r', IR);
    Object.assign(ring.style, { fill: alpha(C.bg, 0.0), stroke: C.dim, strokeWidth: 2.5 });
    tl.set(ring, { o: 0 }, 0);
    // where it is magnified from: a small ring at the strip's top, joined to the inset
    const sx = B.X(M), sy = B.Y(M);
    const small = el(sv, 'circle'); small.setAttribute('cx', sx); small.setAttribute('cy', sy); small.setAttribute('r', 18);
    Object.assign(small.style, { fill: 'none', stroke: C.dim, strokeWidth: 2.5 });
    tl.set(small, { o: 0 }, 0);
    const ang = Math.atan2(sy - ICY, sx - ICX), ex = ICX + IR * Math.cos(ang), ey = ICY + IR * Math.sin(ang);
    const lead = path(tl, sv, `M ${sx - 18 * Math.cos(ang)} ${sy - 18 * Math.sin(ang)} L ${ex} ${ey}`, { stroke: C.dim, width: 2.5 });
    const tIn = tT + 1.1;
    tl.to(small, { o: 1 }, tIn, 0.35); tl.to(lead, { draw: 1 }, tIn + 0.15, 0.4, E.io);
    tl.fromTo(ring, { s: 0.85 }, { s: 1 }, tIn + 0.4, 0.6, E.out5); tl.to(ring, { o: 1 }, tIn + 0.4, 0.4);
    ring.style.transformOrigin = `${ICX}px ${ICY}px`; ring.style.transformBox = 'view-box';
    tl.to(grp, { o: 1 }, tIn + 0.6, 0.5);
    PX.label(tl, root, ICX - IR - 18, ICY - 20, 'density', tIn + 1.3, null, { size: 32, align: 'right' });
    PX.label(tl, root, ICX, ICY + IR + 10, 'width', tIn + 1.5, null, { size: 32, align: 'center' });
    // "The density is per meter, the width is in meters, and the product has no unit."
    fadeIn(tl, u1, tU + 0.8, 0.5, 10);
    fadeIn(tl, u2, tU + 2.35, 0.5, 10); fadeIn(tl, u3, tU + 2.45, 0.5, 10);
    fadeIn(tl, u4, tU + 4.4, 0.5, 10);
    // "It is an infinitesimal probability."
    PX.label(tl, root, RAIL, 792, 'an infinitesimal probability', tN + 0.3, null, { size: 36, color: C.ink });
    void l1; void l2;
  });

  // ============================================ eps_c ==========================================================
  // The first program with an interval of width eps: the heads run is negligible; in centimeters the weight is the
  // same; one answer.
  scene('eps_c', ({ tl, root, cue }) => {
    const tR = cue('run'), tH = cue('heads'), tTl = cue('tails'), tS = cue('sum'), tG = cue('gone'), tA = cue('avg'),
      tCm = cue('cm'), tAg = cue('agree'), tD = cue('done');
    const code = new Code(tl, root, RAIL, 200, 48);
    code.show(PX.P.FIX_M, tR - 0.15, { stagger: 0.008 });
    const interval = () => {
      const ts = [...code.tokens.values()].map(c => c.tok).filter(t => t.line === 2);
      const c0 = code.tokens.get('Interval@2.1').tok.col, last = Math.max(...ts.map(t => t.col));
      return t => t.line === 2 && t.col >= c0 && t.col < last;
    };
    // "with an interval around two meters, whose width is one meter times epsilon."
    const m1 = code.mark(interval(), C.pat, tR + 2.2, { fill: 0.12 });
    code.color('iw', C.pat, tR + 6.4, 0.4);
    // the runs
    const T = PX.runsTable(tl, root, [
      { label: ['a heads run, ', PX.lc('h'), ' = 1.95'], values: [
        [['3.5 ', C.pat], EPS],
        [['0.035', C.pat], ' ', ['/ cm', C.bind], ' × ', ['100 ', C.pat], EPS, ' ', ['cm', C.bind], ' = ', ['3.5 ', C.pat], EPS],
      ] },
      { label: 'a tails run', value: [['1', C.pat]] },
    ], { x: RAIL, y: 650 });
    // "The heads run from before now has weight three point five epsilon."
    T.showRow(0, tH - 0.15);
    // "A tails run has weight one."
    T.showRow(1, tTl - 0.15);
    // "Add them: one plus three point five epsilon is one."
    const SX = 1240, SY = 680;
    const sum = PX.line(root, SX, SY, [['1', C.pat], ' + ', ['3.5 ', C.pat], EPS, ' = ', ['1', C.pat]], { size: 64 });
    fadeIn(tl, sum, tS + 0.8, 0.6, 14);
    later(tl, sum.parts.slice(4), tS + 3.0);
    // "The heads run is negligible, exactly as rejection said it should be."
    T.dimRow(0, 0.25, tG - 0.1);
    // "The weighted average is the average over the tails runs: about one point seven."
    T.pulse(1, tA + 2.0);
    PX.leave(tl, sum, tA + 2.9);
    const avg = PX.line(root, SX, SY - 10, 'E[h] ≈ 1.7', { size: 80, color: C.good });
    PX.inout(tl, avg, tA + 3.15, tCm - 0.25);
    // "In centimeters, the width is a hundred epsilon, the density is a hundred times smaller, and the weight is
    // again three point five epsilon."
    const tSw = tCm - 0.1;
    tl.to(m1, { o: 0 }, tSw - 0.1, 0.3);
    code.swap(PX.P.FIX_CM, tSw, { dur: 0.5 });
    code.color(['iw', 'ik'], C.pat, tSw + 0.25, 0.25);
    code.pulse(['mu', 'sd', 'so', 'ob'], tSw + 0.5, { dur: 0.9 });
    code.mark(interval(), C.pat, tSw + 0.6, { fill: 0.12 });
    T.dimRow(0, 1, tCm + 1.1);
    T.value(0, 1, tCm + 1.1);
    const v = T.rows[0].val.alts[1].parts;
    tl.set(v[0], { o: 0 }, 0); tl.set(v[1], { o: 0 }, 0); tl.set(v[2], { o: 0 }, 0); tl.set(v[3], { o: 0 }, 0);
    tl.to(v[0], { o: 1 }, tCm + 3.4, 0.45); tl.to(v[2], { o: 1 }, tCm + 3.5, 0.45); tl.to(v[3], { o: 1 }, tCm + 3.6, 0.45);
    later(tl, v.slice(8), tCm + 6.0);
    // "The two programs agree."
    code.hide(tAg - 0.3, 0.35); T.hide(tAg - 0.3);
    const ans = PX.cline(root, 360, [['1.7', C.good], ' ', ['m', C.bind], '  ', ['=', C.good], '  ', ['170', C.good], ' ', ['cm', C.bind], PX.tick(tl, tAg + 1.0, 84)], { size: 110 });
    PX.inout(tl, ans, tAg - 0.1, null, { dy: 20, dur: 0.7 });
    // "one answer in both units, and it is the answer that the rejection argument gave."
    PX.label(tl, root, W / 2, 560, "one answer, and it is rejection's", tD + 2.5, null, { size: 36, align: 'center' });
  });

  // ============================================ cool_less ======================================================
  // Fewer exact observations win: rows of counts and weights; the power of ε counts them.
  scene('cool_less', ({ tl, root, cue }) => {
    const tF = cue('fewer'), tP = cue('power'), tT = cue('tie');
    const X0 = 300, TOP = 320, RH = 120;
    const g = box(root, X0, TOP, { display: 'grid', gridTemplateColumns: 'auto auto auto auto auto', gridAutoRows: RH + 'px', columnGap: '26px', alignItems: 'center' });
    const rows = [];
    [['0', 'exact observations', 'weight'], ['1', 'exact observation', 'weight'], ['2', 'exact observations', 'weight']].forEach(([c, d, w], i) => {
      const cells = [
        PX.rich(g, c, { size: 56, style: { justifySelf: 'end' } }),
        PX.rich(g, d, { size: 56 }),
        PX.rich(g, '·', { size: 56 }),
        PX.rich(g, w, { size: 56, color: C.dim }),
        PX.rich(g, ['r ', EPS, SUP(String(i))], { size: 56 }),
      ];
      rows.push(cells);
    });
    // "A run that makes fewer exact observations outweighs a run that makes more, by an infinite factor."
    rows.forEach((cells, i) => cells.forEach((e, j) => fadeIn(tl, e, tF - 0.15 + i * 0.45 + j * 0.05, 0.6, 14)));
    // each weight is larger than the next: a chain under the rows (a ">" turned to point down read as a "v")
    const GX = 1270;
    const chain = PX.line(root, X0, TOP + 3 * RH + 6, ['r ', EPS, SUP('0'), '   >   r ', EPS, SUP('1'), '   >   r ', EPS, SUP('2')], { size: 56 });
    PX.inout(tl, chain, tF + 2.6, tP - 0.25);
    const gts = [];
    const inf = PX.label(tl, root, X0 + 640, TOP + 3 * RH + 26, 'each infinitely larger than the next', tF + 4.9, tP - 0.25, { size: 32 });
    // "The power of epsilon counts them."
    rows.forEach((cells, i) => { const s = cells[4].parts[2]; PX.pulse(tl, s, tP + 0.15 + i * 0.12, { scale: 1.35, dur: 0.7 }); });
    PX.label(tl, root, X0, TOP + 3 * RH + 24, ['the power of ', PX.EPS, ' counts them'], tP + 0.1, tT - 0.3, { size: 32 });
    // "Among runs with the same count, the ordinary weights decide."
    PX.dim(tl, rows[1].concat(rows[2]), 0.35, tT - 0.2);
    const tie = PX.line(root, GX + 30, TOP + RH / 2 - 34, ['r', PX.sub('1'), ' ', EPS, SUP('0'), '   vs   r', PX.sub('2'), ' ', EPS, SUP('0')], { size: 56 });
    fadeIn(tl, tie, tT - 0.1, 0.6, 14);
    ['same power:', 'the ordinary', 'weights decide'].forEach((t, i) => PX.label(tl, root, GX + 30, TOP + RH / 2 + 50 + i * 42, t, tT + 1.9 + i * 0.1, null, { size: 32 }));
    void inf;
  });

  // ============================================ eps_d ==========================================================
  // The BMI program: every run has power one, ε cancels in the weighted average, only A : B remains.
  scene('eps_d', ({ tl, root, cue }) => {
    const tB = cue('bmi'), tO = cue('one'), tC = cue('cancel'), tR = cue('real'), tAB = cue('AB'), tCh = cue('choice');
    const pq = t => parent => PX.div(parent, { display: 'inline-block' }, t, 'span');
    const T = PX.runsTable(tl, root, [
      { label: 'a run that measures height', value: [pq('p'), ' · ', ['A ', C.pat], EPS] },
      { label: 'a run that measures body weight', value: [pq('q'), ' · ', ['B ', C.pat], EPS] },
    ], { y: 190, rowGap: 64 });
    // "Now back to the program with height and body weight."
    T.showRow(0, tB + 1.35); T.showRow(1, tB + 1.95);
    for (const i of [0, 1]) under(tl, T.rows[i].val.alts[0].parts[0], 'a density', tB + 3.0 + i * 0.15, null, { size: 32, dy: 0 });
    // "So every weight has power one."
    for (const i of [0, 1]) { const e = T.rows[i].val.alts[0].parts[3]; PX.pulse(tl, e, tO + 1.0 + i * 0.1, { scale: 1.3, dur: 0.7 }); }
    PX.label(tl, root, W / 2, 452, 'power one, both', tO + 1.0, tC - 0.3, { size: 32, align: 'center' });
    // "In the weighted average, epsilon appears above and below, and it cancels."
    const row = PX.crow(root, 486, { gap: 30 });
    const fr2 = PX.frac(['… ', EPS], ['… ', EPS]);
    const F = PX.rich(row, ['E[bmi] ≈ ', PX.frac(['Σ weight', PX.sub('k'), ' · bmi', PX.sub('k')], ['Σ weight', PX.sub('k')]), ' = ', fr2], { size: 60 });
    const lab = PX.rich(row, '= an ordinary number', { size: 32, font: 'label', style: { marginLeft: '6px' } });
    fadeIn(tl, F, tC + 0.2, 0.6, 14);
    later(tl, F.parts.slice(2), tC + 1.3);
    const f2 = F.parts[3];
    PX.strikeEl(tl, f2.num.parts[1], tC + 3.9); PX.strikeEl(tl, f2.den.parts[1], tC + 4.0);
    // "The result is an ordinary number,"
    tl.set(lab, { o: 0 }, 0); fadeIn(tl, lab, tR + 0.8, 0.5, 10);
    // "and it depends on the two widths only through their ratio."
    const row2 = PX.crow(root, 706, { gap: 40 });
    const ab = PX.rich(row2, 'A : B', { size: 72, color: C.pat });
    const col = PX.div(row2, { display: 'flex', flexDirection: 'column', rowGap: '8px' });
    const l1 = PX.rich(col, 'only the ratio', { size: 32, font: 'label' });
    const l2 = PX.rich(col, 'chosen in the open', { size: 32, font: 'label' });
    fadeIn(tl, ab, tAB + 2.7, 0.6, 14);
    fadeIn(tl, l1, tAB + 3.0, 0.5, 10);
    // "That ratio is a choice, and the programmer now makes it in the open."
    fadeIn(tl, l2, tCh + 3.4, 0.5, 10);
  });

  // ============================================ thm ============================================================
  // The theorem in a column on the left; then the convergence plot on the right.
  scene('thm', ({ tl, root, cue }) => {
    const tC = cue('claim'), tF = cue('f'), tE = cue('eval'), tS = cue('sup'), tT = cue('thm'), tZ = cue('zero'),
      tFig = cue('fig'), tD = cue('direct');
    // "The claim is that it computes the limit we wanted."
    PX.label(tl, root, W / 2, 500, 'does it compute the limit?', tC - 0.15, tF + 2.0, { size: 40, align: 'center' });
    const colm = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    colm.style.transformOrigin = `${RAIL}px 200px`;
    // "Hold the random draws fixed, and run the whole estimate with a small real width W."
    const f = PX.line(colm, RAIL, 200, 'f(w) = the estimate, with real width w', { size: 56 });
    fadeIn(tl, f, tF + 2.45, 0.6, 16);
    // "Then run the same computation with epsilon in place of W."
    const ev = box(colm, RAIL, 292);
    const a = PX.alt(tl, ev, [['f(', EPS, ') = the same computation, with ', EPS], ['f(', EPS, ') = r ', EPS, SUP('n')]], { size: 56 });
    fadeIn(tl, ev, tE - 0.15, 0.6, 16);
    // "Suppose that gives R times epsilon to the power N."
    a.show(1, tS + 0.9);
    // "The theorem says: as W goes to zero, F of W, divided by W to the power N, tends to R."
    tl.to(ev, { o: 0.45 }, tT - 0.15, 0.5);
    PX.label(tl, colm, RAIL, 412, 'theorem', tT - 0.1, null, { size: 32 });
    const bx = box(colm, RAIL, 460, { border: `2px solid ${C.line}`, borderRadius: '14px', padding: '22px 40px 26px' });
    const th = PX.rich(bx, [ITAL('if'), '  f(', EPS, ') = r ', EPS, SUP('n'), '  ', ITAL('then'), '  ', LIM(), ' ', PX.frac('f(w)', ['w', PX.sup('n')]), ' = r'], { size: 56 });
    fadeIn(tl, bx, tT - 0.1, 0.6, 16);
    later(tl, th.parts[9], tT + 1.1);
    later(tl, th.parts.slice(10, 12), tT + 3.95);
    later(tl, th.parts[12], tT + 6.95);
    // "For a weighted average, the power is zero. So R is the limit itself."
    const z = PX.line(colm, RAIL, 712, ['n = 0:   ', LIM(), ' f(w) = r'], { size: 56 });
    fadeIn(tl, z, tZ + 1.3, 0.6, 16);
    later(tl, z.parts.slice(1), tZ + 2.75);

    // "Here is that convergence for the first program."
    PX.dim(tl, colm, 0.35, tFig - 0.1, { dur: 0.7 });
    tl.to(colm, { s: 0.72, y: -40 }, tFig - 0.1, 0.8, E.io);
    const X0 = 1090, X1 = 1760, Y0 = 760;
    const PX_ = w => X0 + (1 - w) * (X1 - X0), PY = v => Y0 - (v - 1.68) / 0.12 * 510;
    const L = box(root, 0, 0, { width: W + 'px', height: '1080px' }), sv = svgLayer(L);
    const tAx = tFig + 0.1;
    const xa = path(tl, sv, `M ${X0} ${Y0} L ${X1 + 20} ${Y0}`, { stroke: C.dim, width: 3 });
    const ya = path(tl, sv, `M ${X0} ${Y0} L ${X0} ${PY(1.80)}`, { stroke: C.dim, width: 3 });
    tl.to(xa, { draw: 1 }, tAx, 0.6, E.io); tl.to(ya, { draw: 1 }, tAx, 0.6, E.io);
    const TS = Object.assign(PX.SERIF(28), { color: C.dim });
    [[1, '1.0'], [0.75, '0.75'], [0.5, '0.5'], [0.25, '0.25'], [0, '0']].forEach(([w, t], i) => {
      const x = PX_(w), m = path(tl, sv, `M ${x} ${Y0} L ${x} ${Y0 + 12}`, { stroke: C.dim, width: 3 });
      tl.to(m, { draw: 1 }, tAx + 0.3 + i * 0.05, 0.3);
      fadeIn(tl, box(L, x - 100, Y0 + 16, Object.assign({}, TS, { width: '200px', textAlign: 'center' }), t), tAx + 0.3 + i * 0.05, 0.5, 8);
    });
    [1.70, 1.75].forEach((v, i) => {
      const y = PY(v), m = path(tl, sv, `M ${X0 - 12} ${y} L ${X0} ${y}`, { stroke: C.dim, width: 3 });
      tl.to(m, { draw: 1 }, tAx + 0.3 + i * 0.05, 0.3);
      fadeIn(tl, box(L, X0 - 220, y - 18, Object.assign({}, TS, { width: '200px', textAlign: 'right' }), v.toFixed(2)), tAx + 0.3 + i * 0.05, 0.5, 8);
    });
    PX.label(tl, root, (X0 + X1) / 2, Y0 + 66, ['interval width ', PX.lc('w')], tAx + 0.5, null, { size: 32, align: 'center' });
    // the estimate at each width: a smooth monotone curve through the points (Fritsch-Carlson)
    const pts = [[1.0, 1.778], [0.9, 1.778], [0.8, 1.778], [0.7, 1.775], [0.6, 1.771], [0.5, 1.765], [0.4, 1.756], [0.3, 1.746], [0.2, 1.733], [0.1, 1.718], [0.05, 1.709], [0, 1.700]]
      .map(([w, v]) => [PX_(w), PY(v)]);
    const n = pts.length, d = [], m = [];
    for (let i = 0; i < n - 1; i++) d.push((pts[i + 1][1] - pts[i][1]) / (pts[i + 1][0] - pts[i][0]));
    m[0] = d[0]; m[n - 1] = d[n - 2];
    for (let i = 1; i < n - 1; i++) m[i] = d[i - 1] * d[i] <= 0 ? 0 : (d[i - 1] + d[i]) / 2;
    for (let i = 0; i < n - 1; i++) {
      if (d[i] === 0) { m[i] = 0; m[i + 1] = 0; continue; }
      const al = m[i] / d[i], be = m[i + 1] / d[i], s = al * al + be * be;
      if (s > 9) { const t = 3 / Math.sqrt(s); m[i] = t * al * d[i]; m[i + 1] = t * be * d[i]; }
    }
    let cd = `M ${pts[0][0].toFixed(2)} ${pts[0][1].toFixed(2)}`;
    for (let i = 0; i < n - 1; i++) {
      const h = pts[i + 1][0] - pts[i][0];
      cd += ` C ${(pts[i][0] + h / 3).toFixed(2)} ${(pts[i][1] + m[i] * h / 3).toFixed(2)} ${(pts[i + 1][0] - h / 3).toFixed(2)} ${(pts[i + 1][1] - m[i + 1] * h / 3).toFixed(2)} ${pts[i + 1][0].toFixed(2)} ${pts[i + 1][1].toFixed(2)}`;
    }
    const curve = path(tl, sv, cd, { stroke: C.ink, width: 4.5 });
    // "As a real width shrinks, the estimate moves to one point seven."
    const tCv = tFig + 2.75;
    tl.to(curve, { draw: 1 }, tCv, 2.5, E.io);
    PX.label(tl, root, X0 + 14, PY(1.778) - 58, 'real width', tCv - 0.1, null, { size: 32 });
    // "The infinitesimal run gives one point seven directly."
    const gl = path(tl, sv, `M ${X0} ${PY(1.70)} L ${X1} ${PY(1.70)}`, { stroke: C.good, width: 4 });
    tl.to(gl, { draw: 1 }, tD + 0.1, 0.6, E.io);
    const dot = el(sv, 'circle'); dot.setAttribute('cx', X1); dot.setAttribute('cy', PY(1.70)); dot.setAttribute('r', 12); dot.style.fill = C.good;
    tl.set(dot, { o: 0 }, 0); tl.to(dot, { o: 1 }, tD + 0.6, 0.3);
    PX.label(tl, root, X0 + 14, PY(1.70) + 14, 'infinitesimal width: 1.7', tD + 0.2, null, { size: 32, color: C.good });
  });
})();

// ==== src/scenes/f.js ====
// Old programs, other scales: the translation leaves programs that already worked alone (compat), and the change
// from decibels to energy, seen through intervals (scale). Built on PX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { RAIL } = PX;

  // ============================================ compat =========================================================
  // NORM at 52 on the rail; the rule above it; then a runs table under it, which moves up to the program's place
  // when the program leaves, with the weighted average and what it says to its right.
  scene('compat', ({ tl, root, cue }) => {
    const tOld = cue('old'), tTr = cue('trans'), tSame = cue('same'), tCan = cue('cancel'), tCons = cue('cons'), tOnly = cue('only');
    const S = 52, Y = 300;
    const code = new Code(tl, root, RAIL, Y, S), lh = code.lh;
    // "What about programs that already work?"
    code.show(PX.P.NORM, tOld - 0.15, { stagger: 0.008 });
    const ok = PX.label(tl, root, RAIL, Y + 3 * lh + 34, ['already works', PX.tick(tl, tOld + 1.45, 40)], tOld + 1.1, tTr - 0.3, { color: C.ink });

    // "Translate each observe on an exact value into an observe on an interval of width W times epsilon."
    const R = 44, rcw = charWidth(R), RY = 170;
    const ruleL = new Code(tl, root, RAIL, RY, R);
    ruleL.show('observe(D, x)', tTr + 0.65, { stagger: 0.01 });
    const ruleR = new Code(tl, root, RAIL + 15 * rcw, RY, R);
    ruleR.show('→  observe(D, (x, {w|w|p}{s|*|p}{e|eps|p}))', tTr + 2.7, { stagger: 0.01 });
    PX.look(code, PX.lineOf(1), tTr + 0.65, tTr + 4.05);
    code.swap('x = rand(Normal(2,3))\nobserve(Normal(2,3), (8 - x, {w|w|p}{s|*|p}{e|eps|p}))\nreturn x', tTr + 4.1, { dur: 0.5 });
    // "... of width W times epsilon"
    const tW = tTr + 5.25;
    ruleR.pulse(['w', 's', 'e'], tW, { color: C.pat });
    code.pulse(['w', 's', 'e'], tW, { color: C.pat });
    ruleL.hide(tSame - 0.3, 0.35); ruleR.hide(tSame - 0.3, 0.35);

    // "If every run makes the same observations, every weight gains the same factor."
    const val = k => ['p', PX.sub(String(k)), ' · ', ['w ε', C.pat]];
    const T = PX.runsTable(tl, root, [1, 2, 3].map(k => ({ label: 'run ' + k, value: val(k), note: k === 2 ? 'the same factor in every run' : '' })),
      { x: RAIL, y: 610, size: 52, rowGap: 16 });
    T.show(tSame + 0.1, 0.3);
    PX.look(code, PX.lineOf(1), tSame + 1.85, tSame + 4.4);   // "the same observations"
    const tF = tSame + 3.85;                                   // "the same factor"
    const facs = T.rows.map(r => PX.markEl(tl, r.val.alts[0].parts[3], C.pat, tF, { out: tCan - 0.4, pad: 10 }));
    T.showNote(1, tF + 0.1, tCan - 0.45);

    // "It cancels in the weighted average, and the answer does not change."
    const tUp = tCan - 0.5;
    code.hide(tUp, 0.35);
    tl.to(T.el, { y: 350 - 610 }, tUp + 0.1, 0.8, E.io);
    const FX = 900;
    const fr = PX.line(root, FX, 368, [PX.frac(
      ['Σ p', PX.sub('k'), ' · ', ['w ε', C.pat], ' · V', PX.sub('k')],
      ['Σ p', PX.sub('k'), ' · ', ['w ε', C.pat]])], { size: 56 });
    PX.inout(tl, fr, tCan + 0.3, null, { dur: 0.6 });
    const F = fr.parts[0];
    PX.strikeEl(tl, F.num.parts[3], tCan + 1.0);
    PX.strikeEl(tl, F.den.parts[3], tCan + 1.15);

    // "So nothing that behaved well before is disturbed."
    PX.label(tl, root, FX, 590, ['the same answer as before', PX.tick(tl, tCons + 0.5, 40)], tCons - 0.15, null, { color: C.ink });
    // "Only programs whose runs make different observations get a new answer."
    PX.label(tl, root, FX, 680, 'a new answer only where runs', tOnly - 0.15, null, { size: 32 });
    PX.label(tl, root, FX, 722, 'make different observations', tOnly - 0.05, null, { size: 32 });
  });

  // ============================================ scale ==========================================================
  // DB_EPS top left; a true graph of y = exp(x) to its right; ENERGY_EPS under the first. At the end everything
  // leaves for the general statement, centred.
  scene('scale', ({ tl, root, cue }) => {
    const tTh = cue('third'), tInt = cue('int'), tExp = cue('exp'), tWide = cue('wide'), tDer = cue('deriv'),
      tProg = cue('prog'), tAg = cue('agree'), tGen = cue('gen');
    const S = 48;
    // "One paradox is left: the change from decibels to energy."
    const DY = 184;
    const db = new Code(tl, root, RAIL, DY, S), lh = db.lh;
    db.show('x = rand(Normal(10,5))\nobserve(Normal(15,5), {a|(|p}{b|x|p}{c|,|p}{d|eps|p}{e|)|p})\nreturn exp(x)', tTh - 0.2, { stagger: 0.008 });
    const dbLab = PX.label(tl, root, RAIL, DY - 58, 'decibels', tTh + 2.6, tGen - 0.5);
    // "With intervals, we can see what went wrong."
    db.pulse(['a', 'b', 'c', 'd', 'e'], tInt + 0.1, { color: C.pat });

    // ---- the graph: y = exp(x), equal-honest scales on both axes (each axis linear) ----
    const gx0 = -0.6, gx1 = 2.35, gy1 = 10.8;
    const PX0 = 1300, PX1 = 1760, PY0 = 620, PY1 = 150;
    const X = v => PX0 + (v - gx0) / (gx1 - gx0) * (PX1 - PX0);
    const Yv = v => PY0 - v / gy1 * (PY0 - PY1);
    const G = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const svg = svgLayer(G);
    const ax = path(tl, svg, `M ${PX0} ${PY1 - 10} L ${PX0} ${PY0} L ${PX1 + 20} ${PY0}`, { stroke: C.dim, width: 3 });
    let d = '';
    for (let i = 0; i <= 160; i++) { const v = gx0 + (gx1 - gx0) * i / 160; d += (i ? ' L ' : 'M ') + X(v).toFixed(1) + ' ' + Yv(Math.exp(v)).toFixed(1); }
    const curve = path(tl, svg, d, { stroke: C.ink, width: 4.5 });
    const curveLab = PX.line(G, X(0.75), Yv(Math.exp(0.75)) - 70, ['exp(x)'], { size: 36, font: 'mono', align: 'right' });
    // "Take the exponential of a small interval around X."
    const tG = tExp + 0.2;
    tl.to(ax, { draw: 1 }, tG, 0.6, E.io);
    tl.to(curve, { draw: 1 }, tG + 0.3, 0.9, E.io);
    PX.inout(tl, curveLab, tG + 0.9, null, { dy: 10, dur: 0.5 });
    const x0 = 2.1, h = 0.2, a = x0 - h, b = x0 + h, ea = Math.exp(a), eb = Math.exp(b);
    const tI = tExp + 1.55;                                   // "a small interval"
    const xi = path(tl, svg, `M ${X(a)} ${PY0} L ${X(b)} ${PY0}`, { stroke: C.pat, width: 9, cap: 'butt' });
    tl.to(xi, { draw: 1 }, tI, 0.4, E.io);
    const epsX = PX.line(G, X(x0), PY0 - 62, [['ε', C.pat]], { size: 44, align: 'center' });
    PX.inout(tl, epsX, tI + 0.15, null, { dy: 8, dur: 0.5 });
    const xLab = PX.line(G, X(x0), PY0 + 14, ['x'], { size: 36, align: 'center', style: { fontStyle: 'italic' } });
    PX.inout(tl, xLab, tExp + 2.85, null, { dy: 8, dur: 0.5 });   // "around X"
    // "The result is an interval around the exponential of X."
    const dash = { stroke: C.dim, width: 2.5, cap: 'butt', dash: '10 8' };
    const guides = [a, b].map(v => path(tl, svg, `M ${X(v)} ${PY0} L ${X(v)} ${Yv(Math.exp(v))} L ${PX0} ${Yv(Math.exp(v))}`, dash));
    for (const g of guides) { tl.set(g, { o: 0 }, 0); tl.to(g, { o: 1 }, tWide - 0.1, 0.5); }
    const yi = path(tl, svg, `M ${PX0} ${Yv(ea)} L ${PX0} ${Yv(eb)}`, { stroke: C.pat, width: 9, cap: 'butt' });
    tl.to(yi, { draw: 1 }, tWide + 0.85, 0.45, E.io);
    // "But its width is not epsilon."
    const pulseW = (p, at) => { tl.to(p, { o: 0.35 }, at, 0.25); tl.to(p, { o: 1 }, at + 0.25, 0.4); };
    pulseW(yi, tWide + 3.95);
    PX.pulse(tl, epsX, tWide + 4.85, { scale: 1.2 });
    // "It is epsilon times the derivative of the exponential at X, which is the exponential of X itself."
    const der = PX.line(G, PX0 - 22, (Yv(ea) + Yv(eb)) / 2 - 28, [['exp(x) · ε', C.pat]], { size: 40, align: 'right' });
    PX.inout(tl, der, tDer - 0.15, null, { dy: 10, dur: 0.6 });

    // "So on the energy scale, the program must observe an interval of that width."
    const EY = 604;
    for (const e of [svg, curveLab, epsX, xLab, der]) tl.to(e, { o: 0.45 }, tProg - 0.2, 0.5);
    db.fade(() => true, 0.45, tProg - 0.2, 0.5);
    tl.to(dbLab, { o: 0.45 }, tProg - 0.2, 0.5);
    const enLab = PX.label(tl, root, RAIL, EY - 58, 'energy', tProg + 0.55, tGen - 0.5);
    const en = new Code(tl, root, RAIL, EY, S);
    en.show('exp_x = rand(LogNormal(10,5))\nobserve(LogNormal(15,5), {a|(|p}{b|exp_x|p}{c|,|p}{d|exp_x|p}{e|*|p}{f|eps|p}{g|)|p})\nreturn exp_x', tProg + 0.5, { stagger: 0.008 });
    const tThat = tProg + 3.8;                               // "of that width"
    en.mark(['d', 'e', 'f'], C.pat, tThat, { out: tAg - 0.3 });
    tl.to(der, { o: 1 }, tThat - 0.1, 0.4);   // "that width": the label lights again
    tl.to(der, { o: 0.45 }, tAg - 0.2, 0.5);

    // "Now the two programs give the same answer."
    db.fade(() => true, 1, tAg - 0.2, 0.5);
    tl.to(dbLab, { o: 1 }, tAg - 0.2, 0.5);
    const retDb = db.mark(PX.lineOf(2), C.good, tAg + 0.3, { out: tGen - 0.5 });
    const retEn = en.mark(PX.lineOf(2), C.good, tAg + 0.3, { out: tGen - 0.5 });
    const eqY = (DY + 3 * lh + EY - 58) / 2;
    // a green "=" set upright between the two programs: two strokes from under the first's return line to above
    // the second's label
    const ex = RAIL + 6.5 * db.cw, ey0 = DY + 3 * lh + 16, ey1 = EY - 58 - 14;
    const eqSvg = svgLayer(root);
    for (const dx of [-9, 9]) {
      const s = path(tl, eqSvg, `M ${ex + dx} ${ey0} L ${ex + dx} ${ey1}`, { stroke: C.good, width: 6 });
      tl.to(s, { draw: 1 }, tAg + 0.9, 0.45, E.io);
    }
    tl.to(eqSvg, { o: 0 }, tGen - 0.5, 0.35);
    PX.label(tl, root, ex + 50, eqY - 21, ['the same answer', PX.tick(tl, tAg + 1.9, 40)], tAg + 1.6, tGen - 0.5, { color: C.ink });

    // "This holds for every smooth, increasing change of scale. Transform the distribution and the interval
    // together, and the probability of the interval does not change."
    tl.to(G, { o: 0, y: -12 }, tGen - 0.5, 0.35, E.in);
    db.hide(tGen - 0.5, 0.35); en.hide(tGen - 0.5, 0.35);
    const FS = 56, src = '{P1|P|p}(T(D), T(I)) {eq|=|g} {P2|P|p}(D, I)';
    const lem = new Code(tl, root, Math.round((W - 23 * charWidth(FS)) / 2), 400, FS);
    lem.show(src, tGen - 0.1, { stagger: 0.01 });
    PX.label(tl, root, W / 2, 530, 'for every smooth, increasing change of scale T', tGen + 0.65, null, { align: 'center' });
    lem.pulse(['eq'], tGen + 8.7, { color: C.good, scale: 1.08 });
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
window.CAPTIONS = [[0.8, 3.24, "Here is a probabilistic program."], [3.28, 5.0, "It draws a person's height,"], [5.04, 7.24, "around one point seven meters."], [7.28, 10.28, "Then it flips a coin, and only if the coin comes"], [10.32, 13.08, "up heads, it observes that a noisy measurement"], [13.12, 15.8, "of that height came out as two meters."], [15.84, 17.8, "What is the expected height?"], [17.84, 20.36, "Run it, and the answer is about one point eight"], [20.4, 21.32, "one."], [21.36, 24.2, "Now write the same program in centimeters."], [24.24, 27.64, "Converting, we would expect a hundred and eighty-one."], [27.68, 29.72, "We get a hundred and seventy."], [29.76, 32.68, "The answer depends on the unit of measurement."], [32.72, 35.24, "By the end of this video, the two programs will"], [35.28, 37.4, "agree, and we will know what the answer should"], [37.44, 38.82, "be."], [38.92, 40.8, "Here is what is coming."], [40.84, 43.4, "First, what a program like this means,"], [43.44, 45.12, "on two dice."], [45.16, 47.28, "Then how such programs are run,"], [47.32, 50.0, "with weights, and where that goes wrong:"], [50.04, 52.0, "three paradoxes."], [52.04, 54.08, "Then what the answer should be."], [54.12, 57.6, "And then the fix, which computes with infinitesimal"], [57.64, 59.5, "numbers."], [59.92, 62.84, "Paradoxes of probabilistic programming:"], [62.88, 66.9, "how to condition on events of measure zero."], [68.82, 71.74, "A probabilistic program is an ordinary program"], [71.78, 74.06, "with two extra operations."], [74.1, 77.58, "The first draws a random value from a distribution."], [77.62, 80.54, "The second is observe, and it is what this video"], [80.58, 81.74, "is about."], [81.78, 83.34, "Here is an example."], [83.38, 87.02, "Throw two dice, X and Y, and observe that their"], [87.06, 88.54, "sum is eight."], [88.58, 90.46, "Then return X."], [90.5, 92.97, "The program stands for a distribution:"], [93.01, 96.92, "the first die, given that the sum is eight."], [97.02, 98.9, "What does observe do?"], [98.94, 101.46, "The simplest answer is rejection."], [101.5, 103.54, "Run the program from the top."], [103.58, 105.25, "That is one trial."], [105.29, 108.02, "At the observe, test the condition."], [108.06, 110.45, "If it is false, throw the trial away,"], [110.49, 111.86, "and start again."], [111.9, 115.18, "If it is true, go on, and keep the returned value"], [115.22, 116.58, "as a sample."], [116.62, 120.3, "The average of the kept samples estimates the expected"], [120.34, 120.98, "value."], [121.02, 122.74, "So observe means:"], [122.78, 126.22, "continue only if this holds."], [126.26, 127.9, "Because this is a program,"], [127.94, 130.94, "observe can sit inside control flow."], [130.98, 133.82, "Here a coin decides whether the sum is observed"], [133.86, 134.94, "at all."], [134.98, 137.9, "A trial is kept if the coin comes up tails,"], [137.94, 139.9, "or if the sum is eight."], [139.94, 143.8, "That is a perfectly good event to condition on."], [143.92, 145.92, "Rejection is wasteful."], [145.96, 148.07, "With dice of a thousand sides,"], [148.11, 150.72, "almost every trial is thrown away."], [150.76, 153.64, "So languages have a second form of observe."], [153.68, 156.07, "It takes a distribution and a value,"], [156.11, 157.0, "and it means:"], [157.04, 158.68, "draw from the distribution,"], [158.72, 162.12, "and continue only if the draw equals the value."], [162.16, 164.44, "The dice program can be written with it:"], [164.48, 168.28, "observe that a fresh die equals eight minus X."], [168.32, 171.32, "This form can be run without rejecting anything."], [171.36, 173.16, "Each trial carries a weight,"], [173.2, 174.84, "which starts at one."], [174.88, 177.92, "At the observe, multiply the weight by the probability"], [177.96, 179.08, "of that value:"], [179.12, 181.64, "the chance that the trial would have survived."], [181.68, 185.0, "At the end, take a weighted average of the results."], [185.04, 188.42, "This is called importance sampling."], [188.54, 190.18, "Notice what we have."], [190.22, 192.66, "For dice, three things agree:"], [192.7, 195.14, "the exact conditional expectation,"], [195.18, 198.18, "rejection, and the weighted average."], [198.22, 200.66, "The weight is only an optimization:"], [200.7, 203.54, "we can still think of every observe as rejecting"], [203.58, 204.66, "a trial."], [204.7, 208.64, "The rest of the video is about keeping that true."], [210.46, 214.02, "Now replace the dice by continuous distributions."], [214.06, 216.98, "The probability that a draw from a normal distribution"], [217.02, 220.1, "equals one exact value is zero."], [220.14, 222.69, "Rejection would throw away every trial,"], [222.73, 225.7, "and every weight would be multiplied by zero."], [225.74, 229.14, "So in practice, languages do something else."], [229.18, 230.98, "For a continuous distribution,"], [231.02, 233.62, "observe multiplies the weight by the probability"], [233.66, 235.54, "density at the value."], [235.58, 238.18, "Here is the continuous version of the dice:"], [238.22, 241.94, "two normal variables, given that their sum is eight."], [241.98, 245.1, "For this program, that works."], [245.14, 248.06, "But a density is not a probability."], [248.1, 249.9, "Is observe still a rejection,"], [249.94, 251.42, "in any sense?"], [251.46, 253.34, "In general, it is not."], [253.38, 255.53, "And once control flow is involved,"], [255.57, 258.3, "it gives answers that rejection would not."], [258.34, 260.46, "Go back to the program from the beginning,"], [260.5, 263.08, "with its if statement."], [264.9, 267.74, "This is what the language actually runs."], [267.78, 269.82, "The weight starts at one."], [269.86, 273.02, "On heads, it is multiplied by a density:"], [273.06, 274.74, "the density of the measurement,"], [274.78, 276.18, "at two meters."], [276.22, 278.57, "And a density has a unit."], [278.61, 280.78, "The probability that the measurement lands in a"], [280.82, 283.94, "narrow interval is about the density times the"], [283.98, 285.42, "interval's width."], [285.46, 287.58, "A probability has no unit,"], [287.62, 289.66, "and the width is a length."], [289.7, 292.22, "So the density is per meter."], [292.26, 295.1, "Take a run that drew a height of one point nine"], [295.14, 295.66, "five."], [295.7, 298.46, "The density of its measurement at two is three"], [298.5, 300.14, "point five per meter."], [300.18, 301.74, "That is its weight."], [301.78, 304.3, "On tails, nothing is multiplied."], [304.34, 308.04, "The weight stays one, with no unit."], [308.16, 311.64, "The weighted average adds the weights of all runs."], [311.68, 314.6, "So it adds a number per meter to a number with"], [314.64, 316.04, "no unit."], [316.08, 317.96, "Now change the unit."], [318.0, 321.08, "In centimeters, the same run has a weight of zero"], [321.12, 323.88, "point zero three five per centimeter."], [323.92, 326.52, "The number is a hundred times smaller."], [326.56, 329.24, "The tails runs still have weight one."], [329.28, 332.57, "So the heads runs count for a hundred times less."], [332.61, 335.36, "And the answer slides from one point eight one"], [335.4, 338.6, "toward one point seven, the average height before"], [338.64, 339.88, "any measurement."], [339.92, 343.06, "We will call that the prior."], [343.28, 345.48, "Look at where the mistake is."], [345.52, 347.96, "Nothing is wrong in the program text."], [348.0, 350.04, "Its units are consistent."], [350.08, 353.16, "The inconsistency is inside the method that runs"], [353.2, 353.93, "it."], [353.97, 356.2, "And it is not one tool's bug:"], [356.24, 360.34, "other inference algorithms do the same arithmetic."], [360.66, 362.78, "So what should the answer be?"], [362.82, 365.1, "Reason as we did for the dice."], [365.14, 368.06, "A trial is kept if the coin comes up tails,"], [368.1, 370.86, "or if the measurement is exactly two."], [370.9, 373.58, "The second case has probability zero."], [373.62, 376.54, "But the first has probability one half."], [376.58, 379.26, "So this event does not have probability zero at"], [379.3, 382.26, "all, and the ordinary definition of conditional"], [382.3, 384.64, "probability applies."], [384.68, 386.4, "In terms of rejection:"], [386.44, 390.12, "a heads trial is rejected with probability one."], [390.16, 392.24, "Only tails trials survive,"], [392.28, 395.2, "and in those, the height is untouched."], [395.24, 397.04, "The answer is the prior:"], [397.08, 399.76, "one point seven meters, or a hundred and seventy"], [399.8, 401.08, "centimeters."], [401.12, 404.16, "The whole if statement should have no effect."], [404.2, 407.0, "If that seems strange, remember that the coin is"], [407.04, 409.12, "not known to have come up heads."], [409.16, 410.96, "Among the trials that are kept,"], [411.0, 413.2, "tails has probability one."], [413.24, 415.6, "So of the two answers at the start,"], [415.64, 417.84, "a hundred and seventy was the one close to the"], [417.88, 421.36, "truth, and only by an accident of the unit."], [421.4, 425.02, "One point eight one was simply wrong."], [425.44, 427.32, "That was one paradox."], [427.36, 429.16, "There are two more."], [429.2, 431.43, "This program draws a person's height,"], [431.47, 432.84, "and their body weight."], [432.88, 435.72, "A coin decides which of the two is measured."], [435.76, 438.28, "It returns the body mass index."], [438.32, 441.72, "Now one branch multiplies by a density per meter,"], [441.76, 444.52, "and the other by a density per kilogram."], [444.56, 447.24, "The weighted average adds the two."], [447.28, 449.08, "Change meters to centimeters,"], [449.12, 450.68, "correct the formula for it,"], [450.72, 452.84, "and the answer still changes."], [452.88, 456.76, "And this time, every trial observes an exact value."], [456.8, 459.56, "The event really has probability zero,"], [459.6, 462.28, "so the definition of conditional probability gives"], [462.32, 463.92, "no answer at all."], [463.96, 467.06, "We will come back to this program."], [467.18, 470.18, "The third paradox has no branch."], [470.22, 472.98, "Draw X from a normal distribution."], [473.02, 475.94, "Observe that a draw from a second normal distribution"], [475.98, 477.54, "equals X."], [477.58, 480.54, "Then return the exponential of X."], [480.58, 483.38, "Think of X as a sound level in decibels,"], [483.42, 486.26, "and of its exponential as an energy."], [486.3, 489.62, "Now write the same program on the energy scale."], [489.66, 493.19, "The two distributions become what is called log-normal,"], [493.23, 495.38, "and the event is the same event:"], [495.42, 498.9, "two exponentials are equal exactly when their exponents"], [498.94, 499.78, "are."], [499.82, 502.79, "Yet the two programs give different answers."], [502.83, 505.46, "It is a version of what probability theory calls"], [505.5, 509.04, "the Borel-Kolmogorov paradox."], [509.24, 512.32, "All three paradoxes break one principle:"], [512.36, 515.2, "the answer should not depend on the scale we measure"], [515.24, 515.84, "in."], [515.88, 517.68, "Meters or centimeters."], [517.72, 519.79, "Decibels or energy."], [519.83, 522.24, "And all three have one cause."], [522.28, 526.48, "An observe on an exact value multiplies by a density,"], [526.52, 530.14, "and a density depends on the scale."], [531.96, 534.48, "Why were the dice free of all this?"], [534.52, 536.51, "Not because dice are discrete,"], [536.55, 538.99, "but because their weights were probabilities,"], [539.03, 541.44, "and a probability has no unit."], [541.48, 544.8, "A continuous distribution has probabilities too:"], [544.84, 548.08, "the probability that a draw lands in an interval."], [548.12, 550.64, "So let observe take an interval."], [550.68, 551.52, "It means:"], [551.56, 553.23, "draw from the distribution,"], [553.27, 556.64, "and continue only if the draw lies in the interval."], [556.68, 560.32, "It runs by multiplying the weight by that probability."], [560.36, 564.36, "Rejection is back, as the meaning of observe."], [564.4, 566.64, "And units are safe."], [566.68, 569.08, "Here is an interval around two meters,"], [569.12, 571.48, "of width zero point one."], [571.52, 574.49, "In centimeters, its center becomes two hundred,"], [574.53, 576.76, "and its width becomes ten."], [576.8, 579.16, "The area under the curve is the same,"], [579.2, 581.11, "so the weight is the same."], [581.15, 584.39, "A change of unit now changes the width as well,"], [584.43, 587.46, "and that keeps the weight in place."], [587.58, 589.7, "But we have changed the question."], [589.74, 592.5, "We wanted to observe exactly two meters,"], [592.54, 594.5, "not roughly two meters."], [594.54, 596.26, "We could choose a tiny width,"], [596.3, 598.34, "say one ten-thousandth."], [598.38, 599.94, "But why that number?"], [599.98, 601.54, "What we want is the limit,"], [601.58, 603.54, "as the width goes to zero."], [603.58, 605.22, "But there is a catch."], [605.26, 607.94, "Conditioning on an event of probability zero is"], [607.98, 609.22, "ambiguous."], [609.26, 612.34, "Intervals can shrink onto the same event in different"], [612.38, 614.55, "ways, and give different answers."], [614.59, 617.94, "So the program has to say which limit it means."], [617.98, 621.6, "The next program shows that this matters."], [621.82, 624.38, "Take the program that measures either height or"], [624.42, 625.46, "body weight."], [625.5, 628.54, "Give each observe an interval whose width is a"], [628.58, 631.82, "constant times epsilon, where epsilon is a small"], [631.86, 633.46, "number with no unit."], [633.5, 635.7, "The constant A is a length."], [635.74, 638.02, "The constant B is a mass."], [638.06, 641.86, "As epsilon shrinks, both observes become exact."], [641.9, 644.58, "But the ratio of the two widths stays,"], [644.62, 645.94, "and it matters."], [645.98, 648.26, "Make B a thousand times larger,"], [648.3, 650.98, "and the second branch succeeds a thousand times"], [651.02, 652.1, "more often."], [652.14, 654.5, "So the widths are part of the model."], [654.54, 657.3, "The old observe had no place to write them."], [657.34, 659.84, "That is what went wrong."], [661.66, 665.38, "How do we compute a limit inside a running program?"], [665.42, 667.62, "Treat epsilon as a symbol."], [667.66, 670.74, "An infinitesimal number is a real number times"], [670.78, 672.58, "a power of epsilon."], [672.62, 675.49, "Power zero gives the ordinary numbers."], [675.53, 678.18, "To multiply, multiply the real parts,"], [678.22, 679.78, "and add the powers."], [679.82, 682.1, "To add two numbers with the same power,"], [682.14, 683.86, "add the real parts."], [683.9, 685.86, "To add numbers with different powers,"], [685.9, 688.06, "keep the one with the lower power."], [688.1, 691.33, "It is the larger number, because epsilon is tiny,"], [691.37, 694.39, "and next to it the other is negligible."], [694.43, 696.34, "Division subtracts the powers."], [696.38, 698.29, "Each number is just a pair,"], [698.33, 701.5, "so the arithmetic is cheap."], [701.54, 704.14, "Now the probability of an interval."], [704.18, 706.46, "If its width is an ordinary number,"], [706.5, 708.38, "it is the area under the curve,"], [708.42, 709.66, "as before."], [709.7, 711.74, "If its width is infinitesimal,"], [711.78, 714.38, "it is the density times the width."], [714.42, 717.66, "That is the area of a strip so thin that the curve"], [717.7, 719.26, "is flat across it."], [719.3, 722.86, "The density is per meter, the width is in meters,"], [722.9, 724.86, "and the product has no unit."], [724.9, 728.52, "It is an infinitesimal probability."], [728.64, 730.55, "Run the first program again,"], [730.59, 732.76, "with an interval around two meters,"], [732.8, 735.96, "whose width is one meter times epsilon."], [736.0, 738.96, "The heads run from before now has weight three"], [739.0, 740.6, "point five epsilon."], [740.64, 743.16, "A tails run has weight one."], [743.2, 744.12, "Add them:"], [744.16, 747.4, "one plus three point five epsilon is one."], [747.44, 749.4, "The heads run is negligible,"], [749.44, 752.04, "exactly as rejection said it should be."], [752.08, 754.68, "Any other width times epsilon would be negligible"], [754.72, 755.67, "too."], [755.71, 758.2, "The weighted average is the average over the tails"], [758.24, 759.0, "runs:"], [759.04, 760.92, "about one point seven."], [760.96, 764.12, "In centimeters, the width is a hundred epsilon,"], [764.16, 766.6, "the density is a hundred times smaller,"], [766.64, 769.96, "and the weight is again three point five epsilon."], [770.0, 772.04, "The two programs agree."], [772.08, 774.76, "That was the promise at the start of the video:"], [774.8, 777.96, "one answer in both units, and it is the answer"], [778.0, 781.3, "that the rejection argument gave."], [781.42, 783.7, "There is a general rule in this."], [783.74, 786.95, "A run that makes fewer exact observations outweighs"], [786.99, 790.37, "a run that makes more, by an infinite factor."], [790.41, 792.9, "The power of epsilon counts them."], [792.94, 794.74, "Among runs with the same count,"], [794.78, 797.84, "the ordinary weights decide."], [798.16, 801.4, "Now back to the program with height and body weight."], [801.44, 804.6, "Every run makes one exact observation."], [804.64, 807.04, "So every weight has power one."], [807.08, 810.04, "In the weighted average, epsilon appears above"], [810.08, 812.36, "and below, and it cancels."], [812.4, 814.57, "The result is an ordinary number,"], [814.61, 817.68, "and it depends on the two widths only through their"], [817.72, 818.36, "ratio."], [818.4, 821.32, "That ratio is a choice, and the programmer now"], [821.36, 823.78, "makes it in the open."], [824.1, 827.5, "Is this arithmetic sound, or is it a trick?"], [827.54, 830.74, "The claim is that it computes the limit we wanted."], [830.78, 832.57, "Hold the random draws fixed,"], [832.61, 835.58, "and run the whole estimate with a small real width"], [835.62, 836.38, "W."], [836.42, 838.86, "Call the result F of W."], [838.9, 842.06, "Then run the same computation with epsilon in place"], [842.1, 843.26, "of W."], [843.3, 846.22, "Suppose that gives R times epsilon to the power"], [846.26, 847.02, "N."], [847.06, 848.3, "The theorem says:"], [848.34, 851.18, "as W goes to zero, F of W,"], [851.22, 853.5, "divided by W to the power N,"], [853.54, 855.07, "tends to R."], [855.11, 857.98, "For a weighted average, the power is zero."], [858.02, 860.5, "So R is the limit itself."], [860.54, 863.34, "Here is that convergence for the first program."], [863.38, 866.22, "As a real width shrinks, the estimate moves to"], [866.26, 867.66, "one point seven."], [867.7, 872.6, "The infinitesimal run gives one point seven directly."], [874.42, 877.26, "What about programs that already work?"], [877.3, 880.78, "Translate each observe on an exact value into an"], [880.82, 884.54, "observe on an interval of width W times epsilon."], [884.58, 887.18, "If every run makes the same observations,"], [887.22, 889.74, "every weight gains the same factor."], [889.78, 891.77, "It cancels in the weighted average,"], [891.81, 893.98, "and the answer does not change."], [894.02, 897.34, "So nothing that behaved well before is disturbed."], [897.38, 900.46, "Only programs whose runs make different observations"], [900.5, 902.84, "get a new answer."], [902.96, 905.0, "One paradox is left:"], [905.04, 907.84, "the change from decibels to energy."], [907.88, 910.84, "With intervals, we can see what went wrong."], [910.88, 913.88, "Take the exponential of a small interval around"], [913.92, 914.56, "X."], [914.6, 917.28, "The result is an interval around the exponential"], [917.32, 918.28, "of X."], [918.32, 920.68, "But its width is not epsilon."], [920.72, 923.8, "It is epsilon times the derivative of the exponential"], [923.84, 927.64, "at X, which is the exponential of X itself."], [927.68, 930.76, "So on the energy scale, the program must observe"], [930.8, 932.84, "an interval of that width."], [932.88, 935.88, "Now the two programs give the same answer."], [935.92, 937.64, "This holds for every smooth,"], [937.68, 939.88, "increasing change of scale."], [939.92, 942.92, "Transform the distribution and the interval together,"], [942.96, 947.06, "and the probability of the interval does not change."], [948.88, 951.72, "We began with a program whose answer changed with"], [951.76, 953.24, "the unit of measurement."], [953.28, 957.0, "The cause was an observe that multiplies by a density."], [957.04, 959.35, "The repair is to observe an interval,"], [959.39, 962.12, "and to let its width be infinitesimal."], [962.16, 964.52, "Then observe is rejection again,"], [964.56, 967.68, "and an event of probability zero is a limit of"], [967.72, 969.64, "events that have a probability."], [969.68, 972.36, "The program says which limit it means."], [972.4, 974.84, "And both units give the same answer:"], [974.88, 977.7, "one point seven meters."], [977.92, 980.76, "All of this is implemented as a small library in"], [980.8, 982.84, "the Julia language."], [982.88, 986.28, "Paradoxes of probabilistic programming."], [986.32, 989.44, "The paper has the proofs, a discussion of measurements"], [989.48, 992.6, "with finite precision, and what remains to be done"], [992.64, 995.7, "for other inference algorithms."]];
