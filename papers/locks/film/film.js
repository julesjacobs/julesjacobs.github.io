// Higher-Order Leak and Deadlock Free Locks: the video: the film's scripts in one file, made by tools/web.py.

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
// The full-length video on "Higher-Order Leak and Deadlock Free Locks" (POPL 2023). One story: deadlocks and
// leaks are cycles, in who holds a reference to which lock and in which lock refers to which; so keep the picture
// of threads and locks (the sharing topology) free of cycles, by restricting how references spread and not how
// they are used; new and fork keep it acyclic; one owner per lock, who waits for the clients, frees it; programs;
// the theorem; lock groups with local lock orders, for when a cycle is wanted.
// {name} marks a cue. No person is named in the narration, and no proof assistant: its name is on screen only.
// The philosophers' forks are called chopsticks aloud, because "fork" is also the operation that starts a thread.
window.NARRATION = [
  // ------------------------------------------------------------------------------------------------ opening
  { id: 'hook', chapter: '', pre: 0.8, post: 0.7, text:
    `{rust}Here is a short program in Rust. {m}It creates a lock, a mutex, holding the number one. {two}It makes a second reference to the same mutex, {swap}and passes both to a function that swaps the contents of two mutexes. {ok}The compiler accepts it. ` +
    `{run}Run it, and it never finishes. {why}The function locks its first argument, and then its second. But they are the same lock, so the thread waits for itself, forever. {dead}That is a deadlock. ` +
    `{leak}A similar program fails in another way: it stores the second reference inside the mutex itself. {cycle}Now the mutex keeps itself alive, and its memory is never freed. {safe}Rust's types rule out data races. They do not rule out deadlocks, or leaks. ` +
    `{video}This video is about a small model language with locks, in which the type checker rules out both. {promise}We will see the single rule behind it, the lock operations that keep the rule, {end}and how it extends to programs that need a cycle, like the dining philosophers.` },
  { id: 'roadmap', chapter: '', pre: 0.3, post: 0.8, text:
    `{coming}Here is what is coming. {wrong}First, what deadlocks and leaks have in common. {inv}Then the rule: a picture of the program that must never contain a cycle. {ops}Then the lock operations, and why each one keeps the rule. ` +
    `{own}Then who frees a lock. {prog}Then programs written this way, {thm}the theorem, {groups}and lock groups, for when a cycle is what you want.` },
  { id: 'title', chapter: '', pre: 0.6, post: 1.0, text:
    `{title}Higher-order leak and deadlock-free locks.` },

  // ------------------------------------------------------------------------------------------------ what goes wrong
  { id: 'wrong_a', chapter: 'What goes wrong', pre: 1.9, post: 0.6, text:
    `{swap}Look again at the swap. {fn}The function is fine: locking two mutexes and exchanging their contents is a reasonable thing to do. {call}The caller is fine too: making a second reference is what references are for. {comp}Only the combination fails. ` +
    `{local}So a deadlock is not a mistake at one place in the program. {graph}To see it, draw a picture. {t}A circle for each thread. {l}A square for each lock. {e}A line when the thread holds a reference to the lock. ` +
    `{two}Our thread holds two references to one lock: two lines between the same two points. {cyc}We count that as a cycle: you can go out along one line, and come back along the other.` },
  { id: 'wrong_b', chapter: 'What goes wrong', pre: 0.4, post: 0.6, text:
    `{classic}The classic deadlock has two threads and two locks. {ord}One thread takes the first lock and then the second. The other takes the second and then the first. {stuck}Each can end up holding one lock, and waiting for the other. ` +
    `{sq}In the picture: four lines that close a loop. {three}With three threads and three locks, any two threads share only one lock, {still}and still they can wait for each other around a ring. ` +
    `{leak}And the leak: a lock whose contents hold a reference to the lock itself. {loop}Draw that reference as a line too. It goes from the lock back to itself. {all}Every one of these failures is a cycle.` },
  { id: 'wrong_c', chapter: 'What goes wrong', pre: 0.4, post: 0.9, text:
    `{usual}The usual defence is a lock order: number all the locks in the program, and always take them in increasing order. {global}That works, but the order is global: every part of the program has to respect the same order. ` +
    `{idea}This paper does something else. {use}It puts no restriction on how a thread uses the locks it has. It may take any of them, at any time, in any order. {spread}Instead, it restricts how references to locks spread.` },

  // ------------------------------------------------------------------------------------------------ one rule
  { id: 'rule_a', chapter: 'One rule', pre: 1.9, post: 0.6, text:
    `{rule}The rule is this. {draw}Draw the threads, the locks, and a line for every reference: from a thread to a lock, or from a lock's contents to another lock. {no}That picture must never contain a cycle. {name}The paper calls the picture the sharing topology. ` +
    `{c1}Counting each reference as its own line, no cycle means, first, that a thread never holds two references to the same lock. {c2}It means that two threads never share more than one lock. {c3}And it rules out the longer rings as well.` },
  { id: 'rule_b', chapter: 'One rule', pre: 0.4, post: 0.6, text:
    `{why}Why is that enough? {wait}Suppose a thread is waiting to acquire a lock. {held}Some other thread has acquired that lock. {next}That thread is either able to run, or it is waiting too, for another lock. ` +
    `{walk}Follow the chain: thread, lock, thread, lock. {back}Each step goes along a line of the picture. And it never turns straight back: a thread that has acquired a lock is not waiting for that same lock. ` +
    `{end}In a picture without cycles, such a walk cannot go on forever. {runs}It must end at a thread that can run. {so}So whoever is waiting is waiting, in the end, on something that can move.` },
  { id: 'rule_c', chapter: 'One rule', pre: 0.4, post: 0.9, text:
    `{ho}Locks here are higher-order: a lock can hold any value, including references to other locks. {edge}That is why the picture has lines from locks to locks. {same}The rule covers them too: no cycles. ` +
    `{pass}It is also how a lock is handed from one thread to another. {put}The first thread puts its reference into a lock that both threads share. {take}The second thread takes it out. {moves}Each time, one end of a line moves along another line, and no cycle appears.` },

  // ------------------------------------------------------------------------------------------------ operations
  { id: 'ops_a', chapter: 'Operations that keep the rule', pre: 1.9, post: 0.6, text:
    `{ops}Now the operations. {new}New creates a lock. In the picture: a new square, with a single line to the thread that made it. No cycle. {acq}Acquire takes the lock, and hands over its contents. {rel}Release puts contents back, and gives the lock up. ` +
    `{same}Neither creates a reference. Contents only move along a line that is already there. {lin}And references are linear. A reference cannot be copied, {forget}and it cannot be silently forgotten. {rust}So the second reference of the Rust program cannot be made.` },
  { id: 'ops_b', chapter: 'Operations that keep the rule', pre: 0.4, post: 0.6, text:
    `{fork}So how do two threads ever share a lock? {f}With fork. {start}Fork starts a new thread, and gives it one new reference to one lock of the parent. {pic}In the picture: a new circle, joined to its parent through exactly one lock. {give}Anything else the child gets, the parent gives up. ` +
    `{tree}A new circle joined in one place can never close a cycle. {two}If fork could share two locks at once, parent and child would be joined twice, and that is a cycle. {one}So: one shared lock for each fork.` },
  { id: 'cool_free', chapter: 'Operations that keep the rule', pre: 0.5, post: 0.9, text:
    `{notice}Notice what is missing. {noorder}There is no lock order, and no rule about when a thread may acquire. {any}A thread may take any lock it holds, in any order, while holding any others. ` +
    `{local}And notice how the rule is enforced. The type checker never looks at the whole picture. It checks one operation at a time, in one thread at a time. {l1}Is a reference being copied, or forgotten? {l2}Does this fork share more than one lock? ` +
    `{global}Yet together, these local checks keep a property of the whole program: no cycle, anywhere.` },

  // ------------------------------------------------------------------------------------------------ who frees a lock
  { id: 'own_a', chapter: 'Who frees a lock', pre: 1.9, post: 0.6, text:
    `{free}That takes care of locking. What about getting rid of a lock? {open}A thread cannot simply drop a lock it has acquired: everyone else would wait forever. {closed}Can it drop a lock it has not acquired? {all}If every thread did that, the lock would be gone, and its contents with it. ` +
    `{lin}And the contents may be something that must not be thrown away: another lock, say. {stuck}So dropping is wrong either way. {owner}The way out: among the references to a lock, exactly one is the owner. The others are clients. {cl}A client may drop its reference. {ow}The owner may not. It must wait.` },
  { id: 'own_b', chapter: 'Who frees a lock', pre: 0.4, post: 0.6, text:
    `{wait}The wait operation blocks until every client has dropped its reference. {ret}Then it removes the lock, and returns its contents to the owner. {nothing}Nothing is lost. {type}The type of a reference records two facts, as two bits. {b1}The upper bit is one for the owner, and zero for a client. {b2}The lower bit is one if the lock is opened, meaning acquired through this reference, and zero if it is closed. ` +
    `{rules}With these two bits, every operation has a type. {acq}Acquire takes a reference whose lower bit is zero, and returns it with that bit set to one, together with the contents. {rel}Release takes a reference whose lower bit is one, and a value, and returns the reference with the bit back at zero. ` +
    `{drop}Drop takes a closed client: zero, zero. {w}The wait operation takes a closed owner: one, zero. It returns the contents. {new}And new returns one, one: an opened owner. The lock is empty, and must be filled.` },
  { id: 'own_c', chapter: 'Who frees a lock', pre: 0.4, post: 0.9, text:
    `{fork}Fork splits a reference in two, one for each thread, and it splits the bits as well. {o}The upper bits of the two halves add up to the upper bit of the original. So an owner splits into an owner and a client, and a client into two clients. ` +
    `{a}The lower bits add up in the same way: if the reference was opened, exactly one of the two is opened, and the duty to release goes with it. ` +
    `{check}So the type checker always knows, for each reference, who must release and who must wait. {must}And because references are linear, those duties cannot be dropped on the floor. They can only be carried out, or handed to someone else.` },

  // ------------------------------------------------------------------------------------------------ programs
  { id: 'prog_a', chapter: 'Programs', pre: 1.9, post: 0.6, text:
    `{cell}What can be written this way? {ref}A lock with no clients is a mutable cell. {rw}Acquire reads it, release writes it, and wait takes the value out for good. {fj}With one client, it is a future. ` +
    `{parent}The parent creates a lock, which is opened, and forks a child. Fork splits the reference: the parent keeps the owner, closed, and the child gets the client, opened. {child}The child cannot drop its reference until it has released a value into the lock. {res}That value is its result. ` +
    `{pw}The parent calls wait, and gets it. {promise}The child cannot finish without delivering, or handing that duty to someone else.` },
  { id: 'prog_b', chapter: 'Programs', pre: 0.4, post: 0.6, text:
    `{shared}With several clients, it is shared data. {three}The parent puts a value in a lock, forks three children with a client reference each, and waits. {each}Each child may acquire and release as often as it likes. ` +
    `{bank}Here is a bank. {acc}Each account is a lock holding a balance, shared between the bank and one customer. {tr}To transfer money, the bank acquires two accounts, changes both balances, and releases them. {noord}It does not matter which it takes first. ` +
    `{safe}Whatever the customers do, the picture has no cycle, so nothing can deadlock.` },
  { id: 'prog_c', chapter: 'Programs', pre: 0.4, post: 0.8, text:
    `{tree}Shared data can be recursive. {node}In this tree, every node is a lock, holding a value and owning its children. {walk}A thread with a client reference to a node can step down the tree: it acquires the node, exchanges its reference for a client reference to one of the children, and releases the node. {conc}So several threads can work in different parts of the tree at once.` },
  { id: 'chan_a', chapter: 'Programs', pre: 0.5, post: 0.6, text:
    `{chan}Message passing comes with all this, for free. {st}A session type describes a conversation over a channel: send a number, then receive a yes or no, then stop. {dual}Each end of the channel has such a type, and the two fit together: where one end sends, the other receives. ` +
    `{fut}Now recall the future. {one}It is a channel for a single message. {sender}The thread with the opened client reference has to put a value in: it is the sender. {recv}The thread with the closed owner reference waits for that value: it is the receiver. ` +
    `{bits}So sending is a lock type with the bits zero, one, and receiving is a lock type with the bits one, zero.` },
  { id: 'chan_b', chapter: 'Programs', pre: 0.4, post: 0.9, text:
    `{more}For a longer conversation, each message carries one more thing: a reference to a fresh lock, for the rest of the conversation. {send}To send, a thread creates the fresh lock, puts the value and one reference to that lock into the old lock, and keeps the other reference. ` +
    `{recv}To receive, the other thread waits on the old lock. It gets the value, and its end of the new lock. {chain}So a channel is a chain of locks, each used once. {types}And every session type is a lock type. Nothing has to be added to the type system. ` +
    `{dl}So the guarantee covers channels too: programs with session types cannot deadlock, and channels can be stored in locks, and locks sent over channels. {cost}One caveat: done literally, every send starts a tiny thread, so a real implementation would still provide channels directly.` },

  // ------------------------------------------------------------------------------------------------ the theorem
  { id: 'thm_a', chapter: 'The theorem', pre: 1.9, post: 0.6, text:
    `{thm}Now the guarantee, stated properly. {start}Take a program that type-checks, and run it for any number of steps. {every}Then every thread is in one of two situations. {can}It can take a step. ` +
    `{or}Or it is waiting, and what it waits for leads, along a chain, to something that can take a step. {reach}The paper calls this full reachability. {dl}It rules out deadlock: not only the whole program being stuck, but any group of threads being stuck among themselves. ` +
    `{lk}The same holds for every lock, and that rules out leaks: no lock is ever cut off, with nothing left that can reach it. {empty}And when all threads have finished, no lock is left.` },
  { id: 'thm_b', chapter: 'The theorem', pre: 0.4, post: 0.9, text:
    `{proof}The proof follows the picture. {inv}An invariant says: everything is well typed, the picture has no cycle, and every lock has exactly one owner and at most one opened reference. {pres}Every step of the program preserves it. ` +
    `{walk}And from the invariant, the walk we took earlier, from a waiting thread along the lines of the picture, always ends at something that can step. {coq}All of this is checked by machine, in a proof assistant.` },

  // ------------------------------------------------------------------------------------------------ lock groups
  { id: 'grp_a', chapter: 'Lock groups', pre: 1.9, post: 0.6, text:
    `{limit}The rule has a price. {two}Two threads can never share two locks. {tellers}So a bank with two tellers, both working on the same accounts, cannot be written with a lock for each account. {phil}Nor can the dining philosophers: threads around a table, each sharing a lock with each neighbour. {ring}That picture is a ring. ` +
    `{ext}The second language in the paper allows this, with lock groups. {grp}A lock group is a collection of locks behind a single reference. {fork}Fork may share a whole group. {pic}In the picture, the group is one square. Between groups, the rule is as before.` },
  { id: 'grp_b', chapter: 'Lock groups', pre: 0.4, post: 0.6, text:
    `{inside}Inside a group, cycles are possible, so something else must prevent deadlock. {order}That something is a lock order, but a local one. {list}The type of a group reference lists its locks, in order. {inc}A lock may be acquired only if every lock after it in the list is closed. ` +
    `{so}So within a group, locks are taken in increasing order. {wait}The wait operation has a stricter condition of the same kind. {local}The order belongs to the group. There is no global order, and locks of different groups can still be taken in any order.` },
  { id: 'grp_c', chapter: 'Lock groups', pre: 0.4, post: 0.6, text:
    `{dyn}Groups can grow and shrink while the program runs. {table}Here is the philosophers' table, for a number of philosophers chosen at run time. {line}Each chopstick is a lock. Think of the chopsticks as a line. {add}The program adds a chopstick at the end of the line, and starts a philosopher between the last two. ` +
    `{again}Then it drops its reference to the one before last, and repeats. {close}At the end, one more philosopher dines with the first chopstick and the last, and the line becomes a ring. {view}Each philosopher's reference shows only two locks of the group.` },
  { id: 'grp_d', chapter: 'Lock groups', pre: 0.4, post: 0.6, text:
    `{why}Why can this ring not deadlock? {ord}The group's order is the order of the line: the first chopstick, the second, and so on. {each}Every philosopher has to take the earlier one of its two chopsticks first. {most}For a philosopher inside the line, that is the one on its left. ` +
    `{last}But the philosopher who closed the ring sits between the last chopstick and the first. It has to take the first one first: the one on its right. {break}So one philosopher reaches the other way round, and the circle of waiting cannot close. ` +
    `{old}That is a well-known remedy. {here}What is new is that the type checker enforces it, with local checks only: each philosopher's type mentions just its own two locks. ` +
    `{grow}The table can even grow while they eat. {three}Change one line, and a philosopher who has eaten replaces itself by three. {frac}Change it again, and it replaces itself by two rows of three, which share its two chopsticks. ` +
    `{wild}The table then grows in a branching pattern that nobody can predict, with chopsticks shared by more and more philosophers. {still}The same local checks still guarantee that it never deadlocks.` },
  { id: 'limits', chapter: 'Lock groups', pre: 0.5, post: 0.9, text:
    `{lim}There are limits. {stat}How many locks of a group one reference can see is fixed by its type. {dag}Shared data cannot be an arbitrary acyclic graph: two paths to the same lock could become two references to it. ` +
    `{unsafe}And there is no escape hatch yet, like Rust's unsafe: what it would have to promise is an open question. {calc}The paper presents all this as a small model language, by choice, so that it does not depend on any one existing language.` },

  // ------------------------------------------------------------------------------------------------ close
  { id: 'recap', chapter: 'Looking back', pre: 1.9, post: 0.7, text:
    `{r1}Deadlocks and leaks are cycles: in who holds which lock, and in which lock refers to which. {r2}So keep the picture of threads and locks free of cycles. {r3}New and fork join each new thing to the picture in one place, so they keep it that way, and threads stay free to lock in any order. ` +
    `{r4}One owner for each lock, who waits for the clients, takes care of freeing. {r5}Lock groups add local lock orders, where a cycle is needed. {r6}And all of it is checked locally, one operation at a time: a program that type-checks cannot deadlock, and cannot leak.` },
  { id: 'end', chapter: 'Looking back', pre: 0.5, post: 3.0, text:
    `{title}Higher-order leak and deadlock-free locks. {paper}The paper has the full type systems, the operational semantics, the encoding of channels, and a sketch of the proofs, which are checked in full by machine.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "hook",
   "chapter": "",
   "start": 0.0,
   "dur": 62.62,
   "pre": 0.8,
   "post": 0.7,
   "audio": 61.12,
   "cues": {
    "rust": 0.8,
    "m": 3.2,
    "two": 7.28,
    "swap": 10.08,
    "ok": 14.8,
    "run": 16.8,
    "why": 19.04,
    "dead": 27.52,
    "leak": 29.36,
    "cycle": 36.0,
    "safe": 40.88,
    "video": 46.8,
    "promise": 52.72,
    "end": 57.52
   }
  },
  {
   "id": "roadmap",
   "chapter": "",
   "start": 62.62,
   "dur": 24.3,
   "pre": 0.3,
   "post": 0.8,
   "audio": 23.2,
   "cues": {
    "coming": 0.3,
    "wrong": 2.14,
    "inv": 5.58,
    "ops": 10.78,
    "own": 15.22,
    "prog": 17.18,
    "thm": 19.34,
    "groups": 20.327
   }
  },
  {
   "id": "title",
   "chapter": "",
   "start": 86.92,
   "dur": 4.96,
   "pre": 0.6,
   "post": 1,
   "audio": 3.36,
   "cues": {
    "title": 0.6
   }
  },
  {
   "id": "wrong_a",
   "chapter": "What goes wrong",
   "start": 91.88,
   "dur": 43.86,
   "pre": 1.9,
   "post": 0.6,
   "audio": 41.36,
   "cues": {
    "swap": 1.9,
    "fn": 3.9,
    "call": 10.78,
    "comp": 16.14,
    "local": 18.54,
    "graph": 22.647,
    "t": 24.78,
    "l": 26.86,
    "e": 28.86,
    "two": 32.14,
    "cyc": 37.9
   }
  },
  {
   "id": "wrong_b",
   "chapter": "What goes wrong",
   "start": 135.74,
   "dur": 41.32,
   "pre": 0.4,
   "post": 0.6,
   "audio": 40.32,
   "cues": {
    "classic": 0.4,
    "ord": 4.48,
    "stuck": 11.04,
    "sq": 15.16,
    "three": 19.04,
    "still": 23.947,
    "leak": 27.36,
    "loop": 32.48,
    "all": 38.0
   }
  },
  {
   "id": "wrong_c",
   "chapter": "What goes wrong",
   "start": 177.06,
   "dur": 29.3,
   "pre": 0.4,
   "post": 0.9,
   "audio": 28.0,
   "cues": {
    "usual": 0.4,
    "global": 7.92,
    "idea": 14.4,
    "use": 16.4,
    "spread": 24.48
   }
  },
  {
   "id": "rule_a",
   "chapter": "One rule",
   "start": 206.36,
   "dur": 35.06,
   "pre": 1.9,
   "post": 0.6,
   "audio": 32.56,
   "cues": {
    "rule": 1.9,
    "draw": 3.66,
    "no": 12.7,
    "name": 15.66,
    "c1": 19.02,
    "c2": 27.9,
    "c3": 31.66
   }
  },
  {
   "id": "rule_b",
   "chapter": "One rule",
   "start": 241.42,
   "dur": 40.6,
   "pre": 0.4,
   "post": 0.6,
   "audio": 39.6,
   "cues": {
    "why": 0.4,
    "wait": 2.24,
    "held": 5.56,
    "next": 8.32,
    "walk": 13.44,
    "back": 18.08,
    "end": 27.573,
    "runs": 32.0,
    "so": 34.88
   }
  },
  {
   "id": "rule_c",
   "chapter": "One rule",
   "start": 282.02,
   "dur": 32.1,
   "pre": 0.4,
   "post": 0.9,
   "audio": 30.8,
   "cues": {
    "ho": 0.4,
    "edge": 7.68,
    "same": 11.387,
    "pass": 14.88,
    "put": 18.72,
    "take": 23.44,
    "moves": 25.6
   }
  },
  {
   "id": "ops_a",
   "chapter": "Operations that keep the rule",
   "start": 314.12,
   "dur": 35.7,
   "pre": 1.9,
   "post": 0.6,
   "audio": 33.2,
   "cues": {
    "ops": 1.9,
    "new": 3.98,
    "acq": 12.3,
    "rel": 15.9,
    "same": 19.62,
    "lin": 25.26,
    "forget": 28.913,
    "rust": 31.42
   }
  },
  {
   "id": "ops_b",
   "chapter": "Operations that keep the rule",
   "start": 349.82,
   "dur": 34.6,
   "pre": 0.4,
   "post": 0.6,
   "audio": 33.6,
   "cues": {
    "fork": 0.4,
    "f": 3.76,
    "start": 5.2,
    "pic": 10.8,
    "give": 16.4,
    "tree": 19.84,
    "two": 24.08,
    "one": 30.96
   }
  },
  {
   "id": "cool_free",
   "chapter": "Operations that keep the rule",
   "start": 384.42,
   "dur": 35.56,
   "pre": 0.5,
   "post": 0.9,
   "audio": 34.16,
   "cues": {
    "notice": 0.5,
    "noorder": 2.42,
    "any": 6.98,
    "local": 12.66,
    "l1": 22.58,
    "l2": 25.38,
    "global": 28.1
   }
  },
  {
   "id": "own_a",
   "chapter": "Who frees a lock",
   "start": 419.98,
   "dur": 40.26,
   "pre": 1.9,
   "post": 0.6,
   "audio": 37.76,
   "cues": {
    "free": 1.9,
    "open": 6.3,
    "closed": 11.74,
    "all": 14.3,
    "lin": 19.1,
    "stuck": 24.3,
    "owner": 27.18,
    "cl": 34.62,
    "ow": 36.86
   }
  },
  {
   "id": "own_b",
   "chapter": "Who frees a lock",
   "start": 460.24,
   "dur": 62.52,
   "pre": 0.4,
   "post": 0.6,
   "audio": 61.52,
   "cues": {
    "wait": 0.4,
    "ret": 5.12,
    "nothing": 9.44,
    "type": 10.88,
    "b1": 15.04,
    "b2": 19.24,
    "rules": 26.48,
    "acq": 30.0,
    "rel": 37.68,
    "drop": 44.96,
    "w": 48.64,
    "new": 54.8
   }
  },
  {
   "id": "own_c",
   "chapter": "Who frees a lock",
   "start": 522.76,
   "dur": 40.98,
   "pre": 0.4,
   "post": 0.9,
   "audio": 39.68,
   "cues": {
    "fork": 0.4,
    "o": 6.76,
    "a": 16.96,
    "check": 26.0,
    "must": 32.0
   }
  },
  {
   "id": "prog_a",
   "chapter": "Programs",
   "start": 563.74,
   "dur": 42.58,
   "pre": 1.9,
   "post": 0.6,
   "audio": 40.08,
   "cues": {
    "cell": 1.9,
    "ref": 4.06,
    "rw": 7.26,
    "fj": 13.22,
    "parent": 15.66,
    "child": 27.42,
    "res": 32.3,
    "pw": 34.38,
    "promise": 36.94
   }
  },
  {
   "id": "prog_b",
   "chapter": "Programs",
   "start": 606.32,
   "dur": 36.68,
   "pre": 0.4,
   "post": 0.6,
   "audio": 35.68,
   "cues": {
    "shared": 0.4,
    "three": 3.68,
    "each": 10.24,
    "bank": 14.48,
    "acc": 16.16,
    "tr": 21.72,
    "noord": 28.16,
    "safe": 30.8
   }
  },
  {
   "id": "prog_c",
   "chapter": "Programs",
   "start": 643.0,
   "dur": 24.72,
   "pre": 0.4,
   "post": 0.8,
   "audio": 23.52,
   "cues": {
    "tree": 0.4,
    "node": 2.96,
    "walk": 8.4,
    "conc": 19.84
   }
  },
  {
   "id": "chan_a",
   "chapter": "Programs",
   "start": 667.72,
   "dur": 43.34,
   "pre": 0.5,
   "post": 0.6,
   "audio": 42.24,
   "cues": {
    "chan": 0.5,
    "st": 3.86,
    "dual": 12.26,
    "fut": 19.62,
    "one": 21.58,
    "sender": 24.18,
    "recv": 29.46,
    "bits": 34.74
   }
  },
  {
   "id": "chan_b",
   "chapter": "Programs",
   "start": 711.06,
   "dur": 53.54,
   "pre": 0.4,
   "post": 0.9,
   "audio": 52.24,
   "cues": {
    "more": 0.4,
    "send": 8.48,
    "recv": 17.52,
    "chain": 24.16,
    "types": 28.0,
    "dl": 33.44,
    "cost": 43.84
   }
  },
  {
   "id": "thm_a",
   "chapter": "The theorem",
   "start": 764.6,
   "dur": 43.7,
   "pre": 1.9,
   "post": 0.6,
   "audio": 41.2,
   "cues": {
    "thm": 1.9,
    "start": 4.9,
    "every": 9.62,
    "can": 12.86,
    "or": 14.62,
    "reach": 21.02,
    "dl": 24.14,
    "lk": 31.82,
    "empty": 39.82
   }
  },
  {
   "id": "thm_b",
   "chapter": "The theorem",
   "start": 808.3,
   "dur": 30.18,
   "pre": 0.4,
   "post": 0.9,
   "audio": 28.88,
   "cues": {
    "proof": 0.4,
    "inv": 2.8,
    "pres": 13.76,
    "walk": 16.56,
    "coq": 25.52
   }
  },
  {
   "id": "grp_a",
   "chapter": "Lock groups",
   "start": 838.48,
   "dur": 38.82,
   "pre": 1.9,
   "post": 0.6,
   "audio": 36.32,
   "cues": {
    "limit": 1.9,
    "two": 3.94,
    "tellers": 6.78,
    "phil": 13.74,
    "ring": 19.82,
    "ext": 21.98,
    "grp": 25.98,
    "fork": 30.06,
    "pic": 32.42
   }
  },
  {
   "id": "grp_b",
   "chapter": "Lock groups",
   "start": 877.3,
   "dur": 34.76,
   "pre": 0.4,
   "post": 0.6,
   "audio": 33.76,
   "cues": {
    "inside": 0.4,
    "order": 6.0,
    "list": 9.52,
    "inc": 13.52,
    "so": 18.72,
    "wait": 22.56,
    "local": 26.4
   }
  },
  {
   "id": "grp_c",
   "chapter": "Lock groups",
   "start": 912.06,
   "dur": 35.0,
   "pre": 0.4,
   "post": 0.6,
   "audio": 34.0,
   "cues": {
    "dyn": 0.4,
    "table": 3.92,
    "line": 9.12,
    "add": 13.44,
    "again": 19.52,
    "close": 23.787,
    "view": 30.56
   }
  },
  {
   "id": "grp_d",
   "chapter": "Lock groups",
   "start": 947.06,
   "dur": 69.48,
   "pre": 0.4,
   "post": 0.6,
   "audio": 68.48,
   "cues": {
    "why": 0.4,
    "ord": 2.92,
    "each": 8.88,
    "most": 13.467,
    "last": 17.6,
    "break": 26.56,
    "old": 32.16,
    "here": 34.32,
    "grow": 43.36,
    "three": 46.16,
    "frac": 51.2,
    "wild": 57.36,
    "still": 65.04
   }
  },
  {
   "id": "limits",
   "chapter": "Lock groups",
   "start": 1016.54,
   "dur": 30.28,
   "pre": 0.5,
   "post": 0.9,
   "audio": 28.88,
   "cues": {
    "lim": 0.5,
    "stat": 2.02,
    "dag": 6.953,
    "unsafe": 14.5,
    "calc": 21.7
   }
  },
  {
   "id": "recap",
   "chapter": "Looking back",
   "start": 1046.82,
   "dur": 39.88,
   "pre": 1.9,
   "post": 0.7,
   "audio": 37.28,
   "cues": {
    "r1": 1.9,
    "r2": 8.727,
    "r3": 12.62,
    "r4": 21.98,
    "r5": 26.94,
    "r6": 31.02
   }
  },
  {
   "id": "end",
   "chapter": "Looking back",
   "start": 1086.7,
   "dur": 17.02,
   "pre": 0.5,
   "post": 3,
   "audio": 13.52,
   "cues": {
    "title": 0.5,
    "paper": 4.1
   }
  }
 ],
 "total": 1103.72
};

// ==== src/scenes/common.js ====
// Shared pieces of the video on "Higher-Order Leak and Deadlock Free Locks", as window.LX. Loaded after engine.js,
// before the scene files. Everything here only builds elements and puts keys on the scene's timeline `tl`; nothing
// is visible until a time says so. Coordinates are stage pixels (1920 x 1080), times are seconds on the scene's
// clock. Colours follow SCENES.md: cyan C.bind = a lock (squares, lock names, the word Lock, group outlines), amber
// C.pat = opened (a reference through which the lock is acquired now), green C.good = allowed / no cycle / can
// step, red C.bad = only a cycle, a deadlock or a leak; the neutral grey strike for what is merely not permitted.
//
// ---- constants -----------------------------------------------------------------------------------------------
//   LX.CX = 960 (stage centre), LX.RAIL = 160 (the left rail), LX.LINE = 3 (drawing line width).
//   LX.LOCKS: the texts LX.code colours cyan by default: ℓ ℓ₀ … ℓ₉ m1 m2 Lock.
//   LX.sub(n) -> the number n in subscript digits: 'T' + LX.sub(3) is 'T₃', 'ℓ' + LX.sub(12) is 'ℓ₁₂'.
//
// ---- type (as SX) --------------------------------------------------------------------------------------------
//   LX.LABEL(size) / LX.SERIF(size) / LX.MONO(size): style objects (small caps sans in C.dim, serif in C.ink, mono
//     in C.code without ligatures). Pass them to box(), or Object.assign(LX.LABEL(32), {color: C.ink}).
//   LX.cline(root, cx, y, parts, style) -> {root, parts}: one line centred on cx, top at y, made of parts
//     [[text, colour|null, style|null], ...] (a part may also be a plain string); each part is its own inline span
//     (fade, strike or colour it by itself). A part's style is merged into its span: use it for a subscript in a
//     small-caps label, which the label font lacks: ['ACQUIRED BY T', ['₂', null, LX.SERIF(34)]].
//   LX.lline(root, x, y, parts, style) -> {root, parts}: the same, left edge at x.
//   LX.clabel(root, cx, y, text, size=32, colour) -> el   centred small caps label (text: a string or parts).
//   LX.cserif(root, cx, y, text, size=56, colour) -> el   centred serif line.
//   LX.note(tl, root, x, y, text, at, out, {size=32, color=C.dim, align='center'|'left'|'right', dy=10}) -> el
//     a small caps label that rises in at `at` and leaves at `out` (out may be null: it stays). x is its centre,
//     its left edge with align 'left', its right edge with align 'right'. `text` is a string or parts (as cline).
//   LX.strikeEl(tl, el, at, {out, faint=true}) -> {line, undo(at)}: the neutral grey strike through an element
//     (a span of cline, a label); its text goes C.faint. undo(at) takes the strike back and restores the colour.
//
// ---- small drawings (as SX) ----------------------------------------------------------------------------------
//   LX.svg(root): an SVG layer over the whole stage (engine's svgLayer).
//   LX.tick(tl, svg, x, y, size=48, at, {color=C.good, width=6}) -> {els, hide(at)}  a tick drawn in at `at`.
//   LX.cross(tl, svg, x, y, size=40, at, {color=C.bad, width=6}) -> {els, hide(at)}  a cross drawn in at `at`.
//   LX.dpath(tl, svg, d, {stroke=C.ink, width=3, dash}) -> path el with a `draw` key (0..1) also when dashed
//     (a dashed path is drawn through a mask). Draw with tl.to(p, {draw: 1}, at, dur, E.io); fade with {o}.
//   LX.line(tl, svg, x1, y1, x2, y2, {at, dur=0.5, bend=0, dash, stroke=C.ink, width=3, head=14}) -> {path, head,
//     hide(at)}: an arrow (head=0: a plain line) drawn in at `at` (omit `at` to draw it yourself). bend > 0 bends
//     it to the right of the direction of travel (below for a left-to-right arrow), as engine.arrowPath.
//   LX.arc(tl, svg, x1, x2, y, depth, {at, dur=0.5, stroke=C.ink, width=3, dash, up=false}) -> path
//     a round arc from (x1, y) to (x2, y), bulging `depth` px down (or up).
//   LX.strikeLine(tl, svg, x1, y1, x2, y2, at, {out, width=4}) -> path   the grey strike as a drawn line (across a
//     drawing); it draws in over 0.4 s from (x1, y1).
//   LX.cell(parent, x, y, w, h, text, {stroke, color, font, radius, width}) -> box el, its text el in ._t
//   LX.flip(tl, textEl, text, at, dur=0.45): a text squeezes, changes, comes back.
//   LX.circleD(x, y, r): an SVG path string for a circle.
//   LX.ctext(parent, cx, cy, text, style, h): a box with text centred on (cx, cy), h px high.
//   LX.dim(tl, els, o, at, dur=0.5): opacity of many elements (or of things with a .root / .g).
//
// ---- code listings: LX.code ----------------------------------------------------------------------------------
//   const c = LX.code(tl, parent, x, y, size, lines, {locks=LX.LOCKS, colors={}, paint=[], leading=1.4, at,
//     stagger=0.1})
//   `lines` is an array of strings (one per line; indent with spaces), set in mono on a character grid with its
//   top-left at (x, y); a line is c.lh = round(size * leading) high, a character c.cw wide. Every line and every
//   token is its own element. Colours: a token whose text is in `locks` is cyan, `…` is C.dim, everything else
//   ink (C.code). colors {tokenText: colour} overrides by a token's exact text; paint [[substring, colour], ...]
//   colours every token inside each occurrence of a substring (['customer 1', C.dim]). Tokens are names
//   (letters, digits, _, ℓ and subscripts: ℓ₁, balance₁, m1), numbers, and single symbols (λ ( ) . , ⟨ …).
//   Nothing shows until show() (or opts.at). Methods (k is a line index from 0, or an array of them):
//   c.show(at, {lines (default all), stagger=0.1})   lines rise in one after the other.
//   c.showLine(k, at)                                   one line rises in.
//   c.light(k, at, {others=0.4})                        line(s) k at full; every other line already shown at that
//                                                       time goes to `others` (null: left alone).
//   c.dim(k, o, at, dur=0.4)                            opacity of line(s) k ('all' for every line).
//   c.mark(k, text, colour, at, {out, fill=0.12, pad=8, nth=1}) -> el   a soft box behind the nth occurrence of
//                                                       `text` on line k (text null: the whole line from its first
//                                                       non-space), in the colour of what it is (C.pat, C.bad), or
//                                                       the neutral one: colour C.dim, fill 0.08.
//   c.strike(k, at, {text, out, fade=true}) -> {line, undo(at)}   the grey strike through line k (or `text` on
//                                                       it); its tokens go C.faint.
//   c.color(k, text, colour, at, dur) / c.recolor(k, text, at)   tokens of `text` on line k (null: all).
//   c.pulse(k, text, at)                                tokens grow a little, with a soft neutral box.
//   c.moveLine(k, dl, at, {dur=0.7})                    line k moves by dl lines (dl = 0 moves it back home);
//                                                       to exchange lines 1 and 2: moveLine(1, 1), moveLine(2, -1).
//   c.hideLine(k, at) / c.hide(at, dur=0.45)            one line / everything leaves.
//   c.to(props, at, dur=0.8, ease=E.io)                 move/scale/fade the whole listing (scale about its top-left).
//   c.rect(k, text) -> {x, y, w, h, cx, cy}             stage rectangle of `text` on line k (null: the whole line),
//                                                       at the build position.
//   c.colX(col) stage x of a column; c.lineY(k) stage y of line k's top; c.width (longest line), c.height,
//   c.lineEls[k], c.root.
//
// ---- the sharing topology: LX.Picture ------------------------------------------------------------------------
//   const p = new LX.Picture(tl, parent, {x=0, y=0, k=1, r=46, size=84, line, names, cx=960, cy=480})
//   Node coordinates given to the methods are picture coordinates; on the stage a point (px, py) is at
//   (x + k * px, y + k * py). With the defaults they are stage coordinates. A small copy: new LX.Picture(tl, root,
//   {x: 1300, y: 300, k: 0.35}) and coordinates relative to (1300, 300). Every size scales with k: r (thread
//   radius), size (lock side), bends, chips, names; names are left out when they would be under 20 px (names:
//   true/false forces). line: the line width (default 3, or 2.5 when k < 0.6). cx, cy: the picture's centre, in
//   picture coordinates, about which p.to({s}) scales. Lines follow their ends at every moment.
//   Ids are strings of your choice, one namespace for nodes, chips and references.
//   Nodes:
//   p.thread(id, x, y, {name, label, r, stroke}) -> p   a circle (3 px ink), its name inside in serif italic
//                                     ('T₁'), and/or a small caps word under it (label: 'PARENT', 32 px).
//   p.lock(id, x, y, {name, contents, size, stroke, group, nameSide}) -> p   a rounded square (3 px cyan), its
//                                     name in cyan mono ('ℓ₁'): inside, or above the square when it has contents
//                                     (nameSide 'inside'|'above'|'below'|'left'|'right' to choose). contents: its chips, a string
//                                     ('42') or an array of them; an entry {ref: true} is a small cyan square (a
//                                     reference to a lock); an entry {id, text} or {id, ref: true} names its chip.
//                                     Chips are laid out in a row at the centre; their ids default to
//                                     `${lockId}/0`, `${lockId}/1`, … group: the id of a group the lock is in (it
//                                     moves with the group).
//   p.group(id, x, y, w, h, {name, stroke}) -> p   a lock group: a large rounded cyan rectangle, centre (x, y),
//                                     w x h; put locks in it with lock(..., {group: id}). Lines to it end at its edge.
//   p.chip(id, lockId, content, {start}) -> p   a chip added later (shown only by p.show(id, at)): content is a
//                                     string or {ref: true}; its home is beside the other chips of lockId; start: a
//                                     node id where it first is (beside that node) instead of at home.
//   References:
//   p.ref(id, from, to, {owner=false, bend=0, dash=false, color=C.ink, width, side='up', loop, at, dur}) -> p
//                                     a line from the holder (a thread, a lock, or a chip id: the line then starts
//                                     at that chip) to a lock (or a group). bend: px the middle bows out, > 0 to the
//                                     left of the direction from -> to (upwards for a left-to-right line); two lines
//                                     between the same two nodes with bend 60 and -60 make a lens. When from and to
//                                     are the same lock (or a chip of it and the lock), the line is a loop that
//                                     leaves the lock on `side` ('up'|'down'|'left'|'right') and comes back into its
//                                     edge; loop: how far it reaches out, in px (default 1.1 x the lock's side).
//                                     owner: drawn as the owner's double line from the start. dash: dashed (a
//                                     sketch). at: draw it in then (else p.show).
//   Showing and hiding (ids: one id or an array):
//   p.show(ids, at, {stagger=0, dur}) a node fades in and grows to size (0.5 s; a lock's chips with it); a chip fades
//                                     in; a reference is drawn from its holder's end to the lock (dur 0.6 s). Calling
//                                     show again on a dropped or hidden item brings it back (a line is redrawn).
//   p.showAll(at, {stagger=0.12})     every node and reference in the order they were added (a lock's chips come
//                                     with it; chips added by p.chip need their own p.show).
//   p.hide(ids, at, dur=0.4) / p.dim(ids, o, at, dur=0.4)   fade out / opacity, with the item's labels (p.label)
//                                     and, for a lock, the chips in it at that time. ids 'all': everything.
//                                     A node's lines are separate items: hide or dim them too.
//   p.to(props, at, dur=0.8, ease) / p.fade(o, at, dur=0.5) / p.out(at, dur=0.4)   the whole picture: {x, y, s, o}
//                                     (x, y offsets; scale about cx, cy) / its opacity / it leaves.
//   References, what happens to them (each returns p):
//   p.open(refId, at) / p.close(refId, at)   the line turns amber (acquired through it) / back to ink (0.35 s).
//   p.color(refId, colour, at, dur=0.35)     any colour.
//   p.owner(refId, at, {dur=0.5, on=true})   the line becomes the owner's double line (on: false: single again).
//   p.drop(refId, at, {dur=0.6, toward='from'})   the line retracts toward its holder (or 'to': toward the lock)
//                                     and is gone, with its labels. Bring it back with p.show (labels are
//                                     not brought back: add new ones).
//   p.cycle(refIds, at, {out, stagger=0})    the lines turn red (one after the other with stagger), and at `out`
//                                     back to the colour each had just before `at`.
//   p.waiting(refId, at, {out})              the line becomes dashed (the gaps open over 0.4 s); solid again at out.
//   p.bend(refId, b, at, {dur=0.7})          the bend changes (the line bows out, or straightens with 0).
//   p.retarget(refId, end, nodeId, at, {via=[], dur=0.9})   end 'from' or 'to' slides to another node (or chip),
//                                     straight, or by way of the nodes in `via` (along the lines between them):
//                                     handing a reference on. The line follows at every moment.
//   p.walk(nodeIds, at, {via, step=0.7, times, dur, color=C.dim, trail='soft'|'line'|false, marker='dot'|'head'|
//     false, offset=0, out, r=11}) -> {end, trails, dot}   a marker travels from node to node along the lines
//                                     (the line joining each two consecutive nodes; via: the reference ids to take,
//                                     one per step, where two lines join the same nodes). Step i starts at
//                                     times[i] (default at + i * step) and lasts dur (default 0.85 * step). The
//                                     marker is hidden while it crosses a node. trail 'soft': a broad soft band
//                                     along the way (alpha 0.25 of color); 'line': a 3 px line of that colour, best
//                                     with offset (px beside the reference, to its left) and marker 'head' (an
//                                     arrowhead at the trail's front: an arrow running along the line). out: the
//                                     trail and marker fade then. end: when the last step is finished.
//   Nodes and chips, what happens to them:
//   p.move(id, x, y, at, {dur=0.8})          a node glides to (x, y) (picture coordinates); its lines, chips at
//                                     home and labels follow; a group's locks move with it.
//   p.moveChip(chipId, target, at, {dur=0.7}) a chip slides to `target`: a node id (it stops beside that node, on
//                                     the side facing its lock: so beside a thread it sits on the thread's line to
//                                     the lock), 'home' (back into its lock), or {x, y} (picture coordinates).
//   p.chipText(chipId, text, at)            the chip's text flips to `text` (keep the length about the same).
//   p.can(id, at, {out, color=C.good})       the green "can step" ring around a node.
//   p.gone(id, at, {dur=0.7, lines=true, chips=true})   a node dissolves (fades, grows a little, blurs); with it
//                                     the lines attached to it at that time and the chips still in it. Pass chips:
//                                     false when a chip slides out at that moment (p.moveChip), lines: false to
//                                     handle the lines yourself.
//   p.nodeColor(id, colour, at, dur=0.4)    the outline's colour (a lock drawn in red: a leak).
//   Any item:
//   p.pulse(id, at, {dur=0.6})               a node or chip grows a little and back; a reference gets a soft
//                                     neutral band along it for a moment.
//   p.strike(id, at, {out, fade}) -> el      the grey strike: a horizontal bar through a node, a short bar across
//                                     a reference's middle, or (id 'all') across the whole picture. fade: the item
//                                     (the whole picture for 'all') goes to that opacity as it is struck.
//   p.label(id, text, at, {out, side, gap=14, size=32, color=C.dim, font='label'|'mono'|'serif', italic, dx=0,
//     dy=0, along=0.5}) -> el   a label attached to a node (side 'below' (default) | 'above' | 'left' | 'right' |
//                                     'center') or to a reference (side 'above' (default) | 'below' | 'left' |
//                                     'right' of the point `along` the line, 0 = holder end), following it as it
//                                     moves. text: a string or parts (as LX.cline). Rises in at `at`, leaves at out.
//                                     Lock names on lines: p.label('m1', 'm1', at, {font: 'mono', size: 36, color:
//                                     C.bind}).
//   Asking:
//   p.pos(id, t=0) -> {x, y}   stage centre of a node or chip at time t (with the moves added so far).
//   p.size(id) -> {hw, hh}     half width and half height of a node or chip on the stage.
//   p.bounds() -> {x0, y0, x1, y1, cx, cy}   stage box of all nodes at their build positions.
//   p.item(id)                 the record: {kind, body (the element to animate with tl), outline, nameEl, ...};
//                              for a reference {g, path, ...}.
//   Presets (each returns a Picture whose origin is (cx, cy): its coordinates are relative to the centre; opts.k
//   scales it; opts r, size (a lock's side; for selfloop: that lock's side), line, names are passed to the Picture,
//   for a tiny one with legible lines: LX.ring(tl, root, x, y, {radius: 36, r: 12, size: 22}); nothing is shown
//   until p.showAll(at) or p.show):
//   LX.double(tl, parent, cx, cy, {k=1, gap=520, bend=70})  thread 't' (name '') at -gap/2, lock 'l'
//                              at +gap/2; refs 'a' (bowing up) and 'b' (bowing down). The two lines to one lock.
//   LX.square(tl, parent, cx, cy, {k=1, w=400, h=200})  threads 'T1', 'T2' (T₁, T₂) at (-w, 0), (w, 0), locks
//                              'l1', 'l2' (ℓ₁, ℓ₂) at (0, -h), (0, h); refs 'T1-l1', 'T1-l2', 'T2-l1', 'T2-l2'.
//                              With the defaults at (960, 480) it is wrong_b's classic deadlock.
//   LX.ring(tl, parent, cx, cy, {k=1, n=3, radius=290, angle=-90})  n threads and n locks alternating
//                              on a circle, starting at `angle` (degrees, -90 = the top): node i is 'T1', 'l1',
//                              'T2', 'l2', … (T₁, ℓ₁, …); ref 'r' + i joins node i and node i + 1 (the last one
//                              closes the ring). LX.ringIds(n) -> {nodes, refs} lists them in order.
//   LX.selfloop(tl, parent, cx, cy, {k=1, size=140, chip=true, side='up', loop})  lock 'l' with a chip 'l/0' (a small
//                              cyan square: its contents refer to it) and the ref 'loop' from the chip back to
//                              the lock's edge (chip: false: a loop from the lock to itself).
//
// ---- a reference's type: LX.refTag, LX.pill ------------------------------------------------------------------
//   const t = LX.refTag(tl, parent, x, y, {size=56, owner=null, opened=null, pillSize, at})
//   `Lock⟨τ⟩` in mono (Lock cyan, ⟨τ⟩ ink), centred on x with its top at y; under it two pills side by side:
//   owner true -> OWNER, false -> CLIENT; opened true -> OPENED (amber), false -> CLOSED (dim); null -> that pill
//   is not shown (yet). pillSize (small caps, default 30, or 26 for size < 48). The pills' row is
//   t.pillY .. t.bottom; t.width is the wider of the text and the pills.
//   t.show(at) / t.hide(at) / t.dim(o, at) / t.move(dx, dy, at, dur=0.8) / t.to(props, at, dur, ease)  (scale
//     about the tag's top centre).
//   t.set({owner, opened}, at)    a pill flips to its new word and colour (a pill not shown yet rises in).
//   t.pulse('owner'|'opened'|'type', at)   one part grows a little and back.
//   t.split(at, dx, dy=0, {left, right}) -> [L, R]   the tag becomes two: L (this tag) moves by (-dx, dy), R (a
//     copy) by (+dx, dy), over 0.8 s; left/right {owner, opened} are set on each at at + 0.5. R has all methods.
//   t.g (the container), t.text, t.pills {owner, opened}.
//   const q = LX.pill(parent, cx, y, value, {size=30, tl, at}) -> pill   one pill on its own (a table entry):
//     value 'owner' | 'client' | 'opened' | 'closed' (or true/false/null as above with kind), centred on cx, top
//     at y. q.el, q.w, q.h, q.show(at), q.set(value, at), q.hide(at). Pass tl in the options.
//
// ---- a lock type with its two bits: LX.lockType, LX.typeLine ------------------------------------------------
//   const t = LX.lockType(tl, parent, x, y, {size=56, of='τ', a, b, entries, align='left'|'center'|'right', at,
//     bitSize, bitChars})
//   The paper's lock type: `Lock⟨τ` (mono, Lock cyan), then its two bits stacked in one column, the upper bit `a`
//   (1 owner, 0 client) raised and the lower bit `b` (1 opened, 0 closed) lowered, then `⟩`. Top at y; x is the
//   left edge (or centre / right edge with align). A bit is 0, 1, a string (a variable: 'a', 'a₁+a₂', drawn dim)
//   or null (empty). A lower bit 1 is amber. Bits are mono at bitSize (default 0.66 x size, at least 28 px).
//   entries: [{of, a, b}, ...] for a group's type `Lock⟨τ, τ, τ⟩` with bits after every entry. bitChars: the bit
//   column's width in characters (default: the longest bit given).
//   t.show(at) / t.hide(at) / t.dim(o, at) / t.move(dx, dy, at, dur) / t.to(props, at, dur)  (scale about the
//     top-left).
//   t.set({a, b}, at, {i=0})       a bit of entry i flips to its new value and colour, and pulses.
//   t.pulse('a'|'b'|'type', at, {i=0, s=1.45})   a bit (or the whole type) grows and comes back.
//   t.width, t.height, t.x (left), t.cx, t.rect(), t.bitRect(i), t.entryX(i) (stage x of entry i's `τ`),
//     t.g, t.lockEl, t.entries[i].a / .b ({wrap, text, v}), t.entries[i].els (its comma, τ and bits: to show
//     the entries of a group's type one by one).
//   const l = LX.typeLine(tl, parent, x, y, size, parts, {align, at})   a typing in one line: parts are strings
//     (mono, ink; or [text, colour]) and lock types given as their options ({a, b} or {entries}), e.g.
//     [': ', {a: 'a', b: 0}, ' → ', {a: 'a', b: 1}, ' × τ']. l.types[k]: the k-th LockType (set, pulse); l.els;
//     l.show / hide / dim / to; l.width, l.rect().
//
// ---- the title -----------------------------------------------------------------------------------------------
//   LX.titleCard(tl, root, {align='left'|'center', x (left edge or centre), y=300, size=110, at, at2, authorsAt,
//     authorSize=32, gap=34}) -> {lines: [l1, l2], authors: [a1, a2], bottom}: "Higher-Order Leak and" /
//     "Deadlock Free Locks" in serif (line 2 at at2, default at + 0.5), then the label lines "JULES JACOBS ·
//     STEPHANIE BALZER" and "POPL 2023" (from authorsAt). A time left out means that part is not shown.
//
// ---- rows (roadmap, recap) -----------------------------------------------------------------------------------
//   const rows = new LX.Rows(tl, root, {x=160, y, pitch, size=56, numbers=true, titleX=x + 70, back=0.6})
//   rows.row(title, at, {num}) -> row {y, at, parts, add(el), num, title}: a numbered serif row rising in; when a
//     later row arrives, the earlier rows (with everything add()ed to them) step back to opacity `back`.
//   rows.evidence(i, el, at, dy=14) fades `el` in at `at` and adds it to row i.  rows.mid(i): the y of row i's
//     middle.  rows.all(): every element.  rows.rows[i].add(x) for things that show themselves (a Picture: its .g).
//
// Only Fira Code (var(--mono)) and Source Serif 4 (var(--serif)) ship. Both have ℓ λ τ → × ≠ ≤ ≥ · … ₀-₉ ✓; only
// Fira Code has ⟨ ⟩ ≡ ∈ ∅. Neither has ⊸ ↦ ≜ ′ ✗ ⇒ or the minus sign. Small caps labels: letters, digits, basic
// punctuation only (a subscript in a label: a serif part, see LX.cline).
'use strict';
(function () {
  const { W, H, C, E } = Film;
  const CX = W / 2, RAIL = 160, LINE = 3;
  const LOCKS = ['ℓ', 'ℓ₀', 'ℓ₁', 'ℓ₂', 'ℓ₃', 'ℓ₄', 'ℓ₅', 'ℓ₆', 'ℓ₇', 'ℓ₈', 'ℓ₉', 'm1', 'm2', 'Lock'];

  // ---- type ----------------------------------------------------------------------------------------------------
  const LS = 0.16;
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase', color: C.dim, lineHeight: 1.2 });
  const SERIF = size => ({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, letterSpacing: '-0.005em' });
  const MONO = size => ({ fontFamily: 'var(--mono)', fontSize: size + 'px', lineHeight: 1.3, color: C.code, fontVariantLigatures: 'none', fontWeight: 450 });

  const asParts = text => (Array.isArray(text) ? text : [text]).map(p => (Array.isArray(p) ? p : [p, null, null]));
  function partsLine(b, parts) {
    return asParts(parts).map(([t, col, st]) => {
      const s = document.createElement('span');
      Object.assign(s.style, { display: 'inline-block', position: 'relative', whiteSpace: 'pre' });
      if (st) Object.assign(s.style, st, { position: 'relative' });
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
  const clabel = (root, cx, y, text, size = 32, col) => { const l = cline(root, cx, y, text, LABEL(size)); if (col) l.root.style.color = col; return l.root; };
  const cserif = (root, cx, y, text, size = 56, col) => { const l = cline(root, cx, y, text, SERIF(size)); if (col) l.root.style.color = col; return l.root; };
  function note(tl, root, x, y, text, at, out, { size = 32, color = C.dim, align = 'center', dy = 10 } = {}) {
    let e;
    if (align === 'left') e = lline(root, x, y, text, Object.assign(LABEL(size), { color })).root;
    else if (align === 'right') { e = lline(root, x - 2400, y, text, Object.assign(LABEL(size), { color, width: '2400px', textAlign: 'right' })).root; e.style.marginRight = '-' + LS + 'em'; }
    else e = clabel(root, x, y, text, size, color);
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
    const id = 'lxm' + (++maskN);
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
  function strikeLine(tl, svg, x1, y1, x2, y2, at, { out = null, width = 4 } = {}) {
    const p = path(tl, svg, `M ${x1} ${y1} L ${x2} ${y2}`, { stroke: C.dim, width });
    tl.to(p, { draw: 1 }, at, 0.4, E.io);
    if (out != null) tl.to(p, { o: 0 }, out, 0.3);
    return p;
  }

  // ---- code listings ---------------------------------------------------------------------------------------------
  const TOK = /(\s+)|(…)|([A-Za-z_ℓ][A-Za-z0-9_₀-₉]*)|(\d+)|(.)/gu;
  const chars = s => [...s];
  class Listing {
    constructor(tl, parent, x, y, size, lines, { locks = LOCKS, colors = {}, paint = [], leading = 1.4, at, stagger = 0.1 } = {}) {
      Object.assign(this, { tl, x, y, size });
      this.cw = charWidth(size); this.lh = Math.round(size * leading);
      this.root = box(parent, x, y, { width: '0px', height: '0px', transformOrigin: '0 0' });
      this.marks = box(this.root, 0, 0);
      this.layer = box(this.root, 0, 0);
      this.shownAt = lines.map(() => null);
      this.L = lines.map((text, k) => {
        const cs = chars(text);
        const le = box(this.layer, 0, k * this.lh, { width: (cs.length * this.cw) + 'px', height: this.lh + 'px' });
        tl.set(le, { o: 0 }, 0);
        // painted columns
        const paintCol = new Array(cs.length).fill(null);
        for (const [sub, col] of paint) {
          const sc = chars(sub); if (!sc.length) continue;
          for (let i = 0; i + sc.length <= cs.length; i++) if (sc.every((c, j) => cs[i + j] === c)) for (let j = 0; j < sc.length; j++) paintCol[i + j] = col;
        }
        const toks = []; let m, col = 0; TOK.lastIndex = 0;
        while ((m = TOK.exec(text))) {
          const len = chars(m[0]).length;
          if (m[1] === undefined) {
            const t = m[0];
            let c = colors[t] ?? (locks.includes(t) ? C.bind : t === '…' ? C.dim : C.code);
            if (paintCol[col] && paintCol[col + len - 1]) c = paintCol[col];
            const s = box(le, col * this.cw, 0, Object.assign(MONO(size), { lineHeight: this.lh + 'px', whiteSpace: 'pre', color: c }), t);
            toks.push({ el: s, text: t, col, len, c0: c });
          }
          col += len;
        }
        return { el: le, text, cs, toks };
      });
      this.lineEls = this.L.map(l => l.el);
      this.cols = Math.max(0, ...this.L.map(l => l.cs.length));
      this.width = this.cols * this.cw; this.height = lines.length * this.lh;
      if (at != null) this.show(at, { stagger });
    }
    _ks(k) { return k === 'all' ? this.L.map((_, i) => i) : [].concat(k); }
    lineY(k) { return this.y + k * this.lh; }
    colX(c) { return this.x + c * this.cw; }
    // columns [c0, c1) of the nth occurrence of text on line k (null: the line from its first non-space)
    _span(k, text, nth = 1) {
      const cs = this.L[k].cs;
      if (text == null) { let c0 = cs.findIndex(c => c !== ' '); if (c0 < 0) c0 = 0; return [c0, cs.length]; }
      const sc = chars(text); let seen = 0;
      for (let i = 0; i + sc.length <= cs.length; i++) if (sc.every((c, j) => cs[i + j] === c) && ++seen === nth) return [i, i + sc.length];
      console.warn('code: no text', JSON.stringify(text), 'on line', k); return [0, cs.length];
    }
    _toks(k, text, nth) { const [c0, c1] = this._span(k, text, nth); return this.L[k].toks.filter(t => t.col >= c0 && t.col + t.len <= c1); }
    rect(k, text, pad = 0, nth = 1) {
      const [c0, c1] = this._span(k, text, nth), x = this.x + c0 * this.cw - pad, w = (c1 - c0) * this.cw + 2 * pad;
      return { x, y: this.lineY(k) - pad * 0.4, w, h: this.lh + pad * 0.8, cx: x + w / 2, cy: this.lineY(k) + this.lh / 2 };
    }
    show(at, { lines, stagger = 0.1 } = {}) { (lines ? [].concat(lines) : this.L.map((_, i) => i)).forEach((k, i) => this.showLine(k, at + i * stagger)); return this; }
    showLine(k, at) { fadeIn(this.tl, this.L[k].el, at, 0.5, 14); if (this.shownAt[k] == null || at < this.shownAt[k]) this.shownAt[k] = at; return this; }
    light(k, at, { others = 0.4, dur = 0.4 } = {}) {
      const ks = this._ks(k);
      this.L.forEach((l, i) => {
        if (ks.includes(i)) this.tl.to(l.el, { o: 1 }, at, dur);
        else if (others != null && this.shownAt[i] != null && this.shownAt[i] <= at) this.tl.to(l.el, { o: others }, at, dur);
      });
      return this;
    }
    dim(k, o, at, dur = 0.4) { for (const i of this._ks(k)) this.tl.to(this.L[i].el, { o }, at, dur); return this; }
    mark(k, text, color, at, { out = null, fill = 0.12, pad = 8, nth = 1, dur = 0.4 } = {}) {
      const r = this.rect(k, text, pad, nth);
      const m = box(this.marks, r.x - this.x, r.y - this.y + this.lh * 0.06, { width: r.w + 'px', height: (r.h - this.lh * 0.12) + 'px', borderRadius: '10px', background: alpha(color, fill), boxShadow: `inset 0 0 0 1.5px ${alpha(color, 0.5)}`, transformOrigin: 'left center' });
      this.tl.set(m, { sx: 0.2, o: 0 }, 0); this.tl.to(m, { sx: 1, o: 1 }, at, dur, E.out5);
      if (out != null) this.tl.to(m, { o: 0 }, out, 0.35);
      return m;
    }
    strike(k, at, { text = null, out = null, fade = true, dur = 0.4, nth = 1 } = {}) {
      const r = this.rect(k, text, 4, nth), toks = this._toks(k, text, nth);
      const u = box(this.marks, r.x - this.x, this.lineY(k) - this.y + this.lh * 0.5 - 2, { width: r.w + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
      this.tl.set(u, { sx: 0, o: 0 }, 0); this.tl.set(u, { o: 1 }, at); this.tl.to(u, { sx: 1 }, at, dur, E.io);
      if (fade) for (const t of toks) this.tl.to(t.el, { color: C.faint }, at, dur);
      if (out != null) this.tl.to(u, { o: 0 }, out, 0.3);
      const tl = this.tl;
      return { line: u, undo(t) { tl.to(u, { sx: 0 }, t, 0.4, E.io); if (fade) for (const q of toks) tl.to(q.el, { color: q.c0 }, t, 0.4); } };
    }
    color(k, text, col, at, dur = 0.35) { for (const t of this._toks(k, text)) this.tl.to(t.el, { color: col }, at, dur); return this; }
    recolor(k, text, at, dur = 0.45) { for (const t of this._toks(k, text)) this.tl.to(t.el, { color: t.c0 }, at, dur); return this; }
    pulse(k, text, at, { scale = 1.07, dur = 0.5 } = {}) {
      for (const t of this._toks(k, text)) { this.tl.to(t.el, { s: scale }, at, dur * 0.4, E.out); this.tl.to(t.el, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      this.mark(k, text, C.dim, at, { fill: 0.1, out: at + dur, dur: dur * 0.4 });
      return this;
    }
    moveLine(k, dl, at, { dur = 0.7 } = {}) { this.tl.to(this.L[k].el, { y: dl * this.lh }, at, dur, E.io); return this; }
    hideLine(k, at, dur = 0.35) { this.tl.to(this.L[k].el, { o: 0 }, at, dur, E.in); return this; }
    hide(at, dur = 0.45) { this.tl.to(this.root, { o: 0 }, at, dur, E.in); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.root, props, at, dur, ease); return this; }
  }
  const code = (tl, parent, x, y, size, lines, opts) => new Listing(tl, parent, x, y, size, lines, opts);

  // ---- keyframes evaluated by the picture's own clock ---------------------------------------------------------------
  // A track holds a value that changes at times; a key's target may depend on time (a node that moves), so the
  // value is computed for each frame: resolve(v, t) gives a key's target at time t.
  class Track {
    constructor(v0) { this.v0 = v0; this.k = []; this.sorted = true; }
    add(t, d, v, ease = E.io) { this.k.push({ t, d, v, ease }); this.sorted = false; return this; }
    keys() { if (!this.sorted) { this.k.sort((a, b) => a.t - b.t); this.sorted = true; } return this.k; }
    // the raw value set by the last key that starts at or before t
    last(t) { let v = this.v0; for (const k of this.keys()) { if (k.t > t) break; v = k.v; } return v; }
    at(t, res) {
      let v = res ? res(this.v0, t) : this.v0;
      for (const k of this.keys()) {
        if (t < k.t) break;
        const target = res ? res(k.v, t) : k.v;
        if (k.d <= 0 || t >= k.t + k.d) { v = target; continue; }
        const u = k.ease(clamp((t - k.t) / k.d));
        v = typeof v === 'number' ? lerp(v, target, u) : { x: lerp(v.x, target.x, u), y: lerp(v.y, target.y, u) };
      }
      return v;
    }
  }

  // ---- geometry ------------------------------------------------------------------------------------------------------
  const unit = (x, y) => { const l = Math.hypot(x, y) || 1; return [x / l, y / l]; };
  const rot = ([x, y], a) => [x * Math.cos(a) - y * Math.sin(a), x * Math.sin(a) + y * Math.cos(a)];
  const GAP = 2;
  // how far from a shape's centre its edge is in the direction (ux, uy)
  function edge(s, ux, uy) {
    if (!s) return 0;
    if (s.kind === 'circle') return s.r + GAP;
    const ax = Math.abs(ux), ay = Math.abs(uy);
    return Math.min(ax > 1e-6 ? s.hw / ax : 1e9, ay > 1e-6 ? s.hh / ay : 1e9) + GAP;
  }
  function inside(s, x, y, pad = 0) {
    if (!s) return false;
    if (s.kind === 'circle') return Math.hypot(x - s.x, y - s.y) < s.r + pad;
    return Math.abs(x - s.x) < s.hw + pad && Math.abs(y - s.y) < s.hh + pad;
  }
  function evalCurve(c, u) {
    const v = 1 - u;
    if (c.type === 'Q') { const [a, b, d] = c.p; return [v * v * a[0] + 2 * v * u * b[0] + u * u * d[0], v * v * a[1] + 2 * v * u * b[1] + u * u * d[1]]; }
    const [a, b, d, e] = c.p;
    return [v * v * v * a[0] + 3 * v * v * u * b[0] + 3 * v * u * u * d[0] + u * u * u * e[0], v * v * v * a[1] + 3 * v * v * u * b[1] + 3 * v * u * u * d[1] + u * u * u * e[1]];
  }
  const curveD = c => c.type === 'Q' ? `M ${c.p[0][0].toFixed(2)} ${c.p[0][1].toFixed(2)} Q ${c.p[1][0].toFixed(2)} ${c.p[1][1].toFixed(2)} ${c.p[2][0].toFixed(2)} ${c.p[2][1].toFixed(2)}`
    : `M ${c.p[0][0].toFixed(2)} ${c.p[0][1].toFixed(2)} C ${c.p.slice(1).map(q => q[0].toFixed(2) + ' ' + q[1].toFixed(2)).join(' ')}`;
  // the stroke-dasharray (and offset) that shows the part [a, b] of a path of length len, dashed by `dash` (0..1)
  function dashes(len, a, b, dash) {
    const A = a * len, B = b * len;
    if (B - A <= 0.5) return null;
    let segs;
    if (dash <= 0.001) segs = [[A, B]];
    else {
      segs = []; const on = 14, per = on + 12 * dash;
      for (let s = Math.floor(A / per) * per; s < B; s += per) { const x0 = Math.max(s, A), x1 = Math.min(s + on, B); if (x1 > x0) segs.push([x0, x1]); }
      if (!segs.length) return null;
    }
    const arr = [];
    segs.forEach(([x0, x1], i) => { arr.push((x1 - x0).toFixed(2)); arr.push(((i + 1 < segs.length ? segs[i + 1][0] : len + 20) - x1).toFixed(2)); });
    return { array: arr.join(' '), offset: (-segs[0][0]).toFixed(2) };
  }

  // ---- the picture ------------------------------------------------------------------------------------------------
  // An element placed by the picture's clock (wrap: positioned; mid: a fixed CSS offset; body: what tl animates).
  const ORIGIN = { below: 'translate(-50%, 0)', above: 'translate(-50%, -100%)', left: 'translate(-100%, -50%)', right: 'translate(0, -50%)', center: 'translate(-50%, -50%)' };
  class Picture {
    constructor(tl, parent, { x = 0, y = 0, k = 1, r = 46, size = 84, line: lw, names, cx = CX, cy = 480 } = {}) {
      Object.assign(this, { tl, ox: x, oy: y, k });
      this.r0 = r; this.s0 = size;
      this.lw = lw ?? (k >= 0.6 ? LINE : 2.5);
      this.names = names ?? (34 * k >= 20);
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${x + k * cx}px ${y + k * cy}px` });
      this.halo = svgLayer(this.g);
      this.svg = svgLayer(this.g);
      this.trailSvg = svgLayer(this.g);
      this.nodeLay = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.chipLay = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.labLay = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.items = new Map(); this.order = []; this.refs = []; this.walks = []; this.anchors = [];
      const clk = box(this.g, 0, 0, { width: '0px', height: '0px' });
      tl.custom(clk, 'clock', (e, t) => this._frame(t), 0);
      tl.fromTo(clk, { clock: 0 }, { clock: 1e4 }, 0, 1e4, E.lin);
    }
    P(x, y) { return { x: this.ox + this.k * x, y: this.oy + this.k * y }; }
    item(id) { const r = this.items.get(id); if (!r) console.warn('picture: no item', id); return r; }
    _add(id, rec) { if (this.items.has(id)) console.warn('picture: duplicate id', id); rec.id = id; this.items.set(id, rec); this.order.push(id); return rec; }

    // ---- nodes
    _node(kind, id, x, y, o) {
      const k = this.k, p = this.P(x, y);
      let hw, hh, radius;
      if (kind === 'thread') { hw = hh = (o.r ?? this.r0) * k; radius = '50%'; }
      else if (kind === 'lock') { const s = (o.size ?? this.s0) * k; hw = hh = s / 2; radius = Math.round(Math.max(6, s * 0.19)) + 'px'; }
      else { hw = o.w * k / 2; hh = o.h * k / 2; radius = Math.round(30 * k) + 'px'; }
      const wrap = box(this.nodeLay, 0, 0, { width: '0px', height: '0px' });
      const body = box(wrap, 0, 0, { width: '0px', height: '0px' });
      const stroke = o.stroke || (kind === 'thread' ? C.ink : C.bind);
      const outline = box(body, -hw, -hh, { width: 2 * hw + 'px', height: 2 * hh + 'px', borderRadius: radius, border: `${this.lw}px solid ${stroke}` });
      tl0(this.tl, body);
      const rec = { kind, wrap, body, outline, hw, hh, radius, home: p, pos: new Track(p), group: o.group || null, chips: [], extra: [] };
      if (rec.group) { const g = this.items.get(rec.group); if (g) g.members.push(id); else console.warn('picture: no group', rec.group); }
      return rec;
    }
    _name(rec, text, kind, side) {
      if (!text || !this.names) return;
      const k = this.k;
      const st = kind === 'thread' ? Object.assign(SERIF(Math.round(34 * k)), { fontStyle: 'italic', color: C.ink, lineHeight: 1 })
        : Object.assign(MONO(Math.round(32 * k)), { color: C.bind, lineHeight: 1, letterSpacing: '-0.1em' });
      const fs = parseFloat(st.fontSize), hgt = Math.round(fs * 1.3);
      let y = -rec.hh, x = -200, jc = 'center';
      if (side === 'above') y = -rec.hh - hgt - 4 * k;
      else if (side === 'below') y = rec.hh + 4 * k;
      else if (side === 'left') { y = -hgt / 2; x = -rec.hw - 10 * k - 400; jc = 'flex-end'; }
      else if (side === 'right') { y = -hgt / 2; x = rec.hw + 10 * k; jc = 'flex-start'; }
      const h = side === 'inside' ? 2 * rec.hh : hgt;
      rec.nameEl = box(rec.body, x, y, Object.assign(st, { width: '400px', height: h + 'px', display: 'flex', alignItems: 'center', justifyContent: jc, whiteSpace: 'pre' }), text);
    }
    thread(id, x, y, o = {}) {
      const rec = this._node('thread', id, x, y, o);
      this._name(rec, o.name, 'thread', 'inside');
      if (o.label) {
        rec.labelEl = box(rec.body, -400, rec.hh + 12, Object.assign(LABEL(32), { width: '800px', textAlign: 'center', whiteSpace: 'pre', paddingLeft: LS + 'em' }), o.label);
      }
      this._add(id, rec);
      return this;
    }
    lock(id, x, y, o = {}) {
      const rec = this._node('lock', id, x, y, o);
      const cont = o.contents == null ? [] : [].concat(o.contents);
      this._add(id, rec);
      this._name(rec, o.name, 'lock', o.nameSide || (cont.length ? 'above' : 'inside'));
      cont.forEach((c, i) => this._chip(typeof c === 'object' && c.id ? c.id : `${id}/${i}`, id, c, {}));
      this._layoutChips(rec);
      return this;
    }
    group(id, x, y, w, h, o = {}) {
      const rec = this._node('group', id, x, y, Object.assign({}, o, { w, h }));
      rec.members = [];
      if (o.name && this.names) {
        rec.nameEl = box(rec.body, -200, -rec.hh - Math.round(32 * this.k * 1.3) - 6, Object.assign(MONO(Math.round(32 * this.k)), { color: C.bind, width: '400px', textAlign: 'center', whiteSpace: 'pre' }), o.name);
      }
      this._add(id, rec);
      return this;
    }
    // ---- chips
    _chipSize(lockRec) { const big = Math.max(1, (2 * lockRec.hh / this.k) / 84); return Math.round(Math.min(46, 30 * Math.sqrt(big)) * this.k); }
    _chip(id, lockId, content, { start } = {}) {
      const L = this.items.get(lockId);
      if (!L) { console.warn('picture: chip of no lock', lockId); return null; }
      const fs = this._chipSize(L), isRef = typeof content === 'object' && content.ref;
      const text = typeof content === 'object' ? (content.text ?? '') : String(content);
      let hw, hh;
      const wrap = box(this.chipLay, 0, 0, { width: '0px', height: '0px' });
      const body = box(wrap, 0, 0, { width: '0px', height: '0px' });
      let textEl = null;
      if (isRef) {
        const s = Math.round(fs * 1.0); hw = hh = s / 2;
        box(body, -hw, -hh, { width: s + 'px', height: s + 'px', borderRadius: Math.round(s * 0.24) + 'px', border: `${this.lw}px solid ${C.bind}`, background: C.bg });
      } else {
        const h = Math.round(fs * 1.45), w = Math.max(h, Math.round(chars(text).length * charWidth(fs) + fs * 0.8));
        hw = w / 2; hh = h / 2;
        const b = box(body, -hw, -hh, { width: w + 'px', height: h + 'px', borderRadius: Math.round(fs * 0.3) + 'px', border: `${Math.max(2, this.lw - 0.5)}px solid ${C.ink}`, background: C.bg });
        textEl = box(b, 0, 0, Object.assign(MONO(fs), { position: 'absolute', left: 0, top: 0, width: '100%', height: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', whiteSpace: 'pre', color: C.ink, lineHeight: 1, marginTop: '-1px' }), text);
      }
      tl0(this.tl, body);
      const rec = { kind: 'chip', lock: lockId, wrap, body, textEl, hw, hh, off: { x: 0, y: 0 }, track: new Track(start || 'home'), extra: [] };
      L.chips.push(id);
      this._add(id, rec);
      return rec;
    }
    _layoutChips(L) {
      const cs = L.chips.map(c => this.items.get(c)), gap = 10 * this.k;
      const tot = cs.reduce((a, c) => a + 2 * c.hw, 0) + gap * (cs.length - 1);
      let x = -tot / 2;
      for (const c of cs) { c.off = { x: x + c.hw, y: 0 }; x += 2 * c.hw + gap; }
    }
    chip(id, lockId, content, { start } = {}) {
      const rec = this._chip(id, lockId, content, { start });
      if (rec) { rec.late = true; if (!start) this._layoutChips(this.items.get(lockId)); }
      return this;
    }

    // ---- references
    ref(id, from, to, o = {}) {
      const nf = this._nodeOf(from), nt = this._nodeOf(to);
      if (!this.items.has(from) || !this.items.has(to)) { console.warn('picture: ref to nothing', id, from, to); return this; }
      const gEl = el(this.svg, 'g'), haloEl = el(this.halo, 'path');
      const mid = 'lxr' + (++maskN);
      const mask = document.createElementNS(NS, 'mask');
      mask.setAttribute('id', mid); mask.setAttribute('maskUnits', 'userSpaceOnUse');
      mask.setAttribute('x', -W); mask.setAttribute('y', -H); mask.setAttribute('width', 3 * W); mask.setAttribute('height', 3 * H);
      const mr = document.createElementNS(NS, 'rect');
      mr.setAttribute('x', -W); mr.setAttribute('y', -H); mr.setAttribute('width', 3 * W); mr.setAttribute('height', 3 * H); mr.setAttribute('fill', '#ffffff');
      const mp = document.createElementNS(NS, 'path');
      mp.setAttribute('fill', 'none'); mp.setAttribute('stroke', '#000000'); mp.setAttribute('stroke-linecap', 'butt');
      mask.appendChild(mr); mask.appendChild(mp); gEl.appendChild(mask);
      const pathEl = el(gEl, 'path');
      pathEl.setAttribute('fill', 'none'); pathEl.setAttribute('stroke-linecap', 'round'); pathEl.setAttribute('stroke-linejoin', 'round');
      pathEl.setAttribute('mask', `url(#${mid})`);
      const col = o.color || C.ink;
      pathEl.style.stroke = col;
      haloEl.setAttribute('fill', 'none'); haloEl.setAttribute('stroke-linecap', 'round');
      haloEl.style.stroke = alpha(C.dim, 0.28); this.tl.set(haloEl, { o: 0 }, 0);
      const rec = {
        kind: 'ref', g: gEl, path: pathEl, maskPath: mp, haloEl, width: o.width ?? this.lw,
        from: new Track(from), to: new Track(to), bend: new Track(o.bend || 0), a: new Track(0), b: new Track(0),
        dash: new Track(o.dash ? 1 : 0), dbl: new Track(o.owner ? 1 : 0), cols: [{ t: -1, c: col }], c0: col,
        loop: nf === nt, side: o.side || 'up', loopLen: o.loop, extra: [],
      };
      this._add(id, rec); this.refs.push(rec);
      if (o.at != null) this.show(id, o.at, { dur: o.dur });
      return this;
    }
    _nodeOf(id) { const r = this.items.get(id); return r && r.kind === 'chip' ? r.lock : id; }

    // ---- where things are
    _npos(id, t) {
      const r = this.items.get(id);
      if (r.kind === 'chip') return this._cpos(r, t);
      let p = r.pos.at(t);
      if (r.group) { const g = this.items.get(r.group), gp = g.pos.at(t); p = { x: p.x + gp.x - g.home.x, y: p.y + gp.y - g.home.y }; }
      return p;
    }
    _cpos(c, t) {
      const res = (v, tt) => {
        const L = this._npos(c.lock, tt);
        if (v === 'home') return { x: L.x + c.off.x, y: L.y + c.off.y };
        if (typeof v === 'string') {
          const n = this.items.get(v), q = this._npos(v, tt);
          let [ux, uy] = unit(L.x - q.x, L.y - q.y);
          if (v === c.lock) return { x: L.x + c.off.x, y: L.y + c.off.y };
          const d = edge(this._shape(v, tt), ux, uy) + edge({ kind: 'rect', hw: c.hw, hh: c.hh }, ux, uy) + 8 * this.k;
          return { x: q.x + ux * d, y: q.y + uy * d };
        }
        return this.P(v.x, v.y);
      };
      return c.track.at(t, res);
    }
    _shape(id, t) {
      const r = this.items.get(id), p = this._npos(id, t);
      if (r.kind === 'thread') return { kind: 'circle', x: p.x, y: p.y, r: r.hw };
      return { kind: 'rect', x: p.x, y: p.y, hw: r.hw, hh: r.hh };
    }
    pos(id, t = 0) { return this._npos(id, t); }
    size(id) { const r = this.item(id); return { hw: r.hw, hh: r.hh }; }
    bounds() {
      const ns = [...this.items.values()].filter(r => r.kind !== 'ref' && r.kind !== 'chip');
      const x0 = Math.min(...ns.map(r => r.home.x - r.hw)), x1 = Math.max(...ns.map(r => r.home.x + r.hw));
      const y0 = Math.min(...ns.map(r => r.home.y - r.hh)), y1 = Math.max(...ns.map(r => r.home.y + r.hh));
      return { x0, y0, x1, y1, cx: (x0 + x1) / 2, cy: (y0 + y1) / 2 };
    }
    // an end of a reference at time t: {x, y, shape, node}
    _end(tr, t) {
      const ks = tr.keys();
      let cur = tr.v0, k = null;
      for (const q of ks) { if (q.t > t) break; if (k) cur = k.v.node; k = q; }
      if (!k || t >= k.t + k.d) { const id = k ? k.v.node : cur; const p = this._npos(id, t); return { x: p.x, y: p.y, shape: this._shape(id, t), node: id }; }
      // sliding: along the polyline cur -> via… -> node
      const ids = [cur, ...k.v.via, k.v.node], pts = ids.map(i => this._npos(i, t));
      const seg = []; let tot = 0;
      for (let i = 1; i < pts.length; i++) { const l = Math.hypot(pts[i].x - pts[i - 1].x, pts[i].y - pts[i - 1].y); seg.push(l); tot += l; }
      let s = k.ease(clamp((t - k.t) / k.d)) * tot, i = 0;
      while (i < seg.length - 1 && s > seg[i]) { s -= seg[i]; i++; }
      const u = seg[i] ? clamp(s / seg[i]) : 1, x = lerp(pts[i].x, pts[i + 1].x, u), y = lerp(pts[i].y, pts[i + 1].y, u);
      let shape = null, node = null;
      for (const id of ids) { const sh = this._shape(id, t); if (inside(sh, x, y)) { shape = sh; node = id; break; } }
      return { x, y, shape, node };
    }
    // the curve of a reference at time t: {c (trimmed), raw (centre to centre), A, B}
    _geom(r, t) {
      const A = this._end(r.from, t), B = this._end(r.to, t);
      if (r.loop) {
        const lockId = this._nodeOf(this._endNode(r.to, t)), N = this._shape(lockId, t), k = this.k;
        const d = { up: [0, -1], down: [0, 1], left: [-1, 0], right: [1, 0] }[r.side] || [0, -1];
        const Lz = (r.loopLen != null ? r.loopLen * k : N.hh * 2 * 1.1);
        const bpt = dir => { const e = edge(N, dir[0], dir[1]); return [N.x + dir[0] * e, N.y + dir[1] * e]; };
        const fromChip = this.items.get(this._endNode(r.from, t)).kind === 'chip';
        let c;
        if (fromChip) {
          // out of the chip, straight through the lock's edge, around, and back into the edge on the chip's side
          const e = edge(A.shape, d[0], d[1]), S = [A.x + d[0] * e, A.y + d[1] * e];
          const pp = rot(d, Math.PI / 2), sg = Math.sign((A.x - N.x) * pp[0] + (A.y - N.y) * pp[1]) || 1;
          const Ep = bpt(rot(d, sg * 1.05)), d2 = rot(d, sg * 1.35), L1 = Lz + edge(N, d[0], d[1]) - ((A.x - N.x) * d[0] + (A.y - N.y) * d[1]);
          c = { type: 'C', p: [S, [S[0] + d[0] * L1, S[1] + d[1] * L1], [Ep[0] + d2[0] * Lz * 0.8, Ep[1] + d2[1] * Lz * 0.8], Ep] };
        } else {
          const S = bpt(rot(d, -0.55)), d1 = rot(d, -0.55), Ep = bpt(rot(d, 0.55)), d2 = rot(d, 0.55);
          c = { type: 'C', p: [S, [S[0] + d1[0] * Lz, S[1] + d1[1] * Lz], [Ep[0] + d2[0] * Lz, Ep[1] + d2[1] * Lz], Ep] };
        }
        return { c, raw: c, A, B };
      }
      const dx = B.x - A.x, dy = B.y - A.y, L = Math.hypot(dx, dy) || 1, b = r.bend.at(t) * this.k;
      const q = [(A.x + B.x) / 2 + dy / L * 2 * b, (A.y + B.y) / 2 - dx / L * 2 * b];
      const [ax, ay] = unit(q[0] - A.x, q[1] - A.y), [bx, by] = unit(q[0] - B.x, q[1] - B.y);
      const ea = edge(A.shape, ax, ay), eb = edge(B.shape, bx, by);
      const p0 = [A.x + ax * ea, A.y + ay * ea], p2 = [B.x + bx * eb, B.y + by * eb];
      // the trimmed curve keeps the bow of the whole one: its control point is offset from its own chord's middle
      const q2 = [(p0[0] + p2[0]) / 2 + q[0] - (A.x + B.x) / 2, (p0[1] + p2[1]) / 2 + q[1] - (A.y + B.y) / 2];
      return { c: { type: 'Q', p: [p0, q2, p2] }, raw: { type: 'Q', p: [[A.x, A.y], q, [B.x, B.y]] }, A, B };
    }

    // ---- the clock: places everything for time t
    _frame(t) {
      for (const r of this.items.values()) {
        if (r.kind === 'thread' || r.kind === 'lock' || r.kind === 'group') { const p = this._npos(r.id, t); r.wrap.style.transform = `translate(${p.x.toFixed(2)}px,${p.y.toFixed(2)}px)`; }
        else if (r.kind === 'chip') { const p = this._cpos(r, t); r.wrap.style.transform = `translate(${p.x.toFixed(2)}px,${p.y.toFixed(2)}px)`; }
      }
      for (const r of this.refs) {
        const G = this._geom(r, t); r._G = G;
        const d = curveD(G.c);
        r.path.setAttribute('d', d); r.maskPath.setAttribute('d', d); r.haloEl.setAttribute('d', d);
        const len = r.path.getTotalLength(), ds = dashes(len, r.a.at(t), r.b.at(t), r.dash.at(t));
        if (!ds) { r.path.style.strokeOpacity = 0; }
        else { r.path.style.strokeOpacity = 1; r.path.style.strokeDasharray = ds.array; r.path.style.strokeDashoffset = ds.offset; }
        const db = r.dbl.at(t);
        r.path.setAttribute('stroke-width', (r.width * (1 + 2 * db)).toFixed(2));
        r.maskPath.setAttribute('stroke-width', (r.width * db).toFixed(2));
        r.haloEl.setAttribute('stroke-width', r.width + 14);
      }
      for (const a of this.anchors) { const p = a.fn(t); if (p) a.wrap.style.transform = `translate(${p.x.toFixed(2)}px,${p.y.toFixed(2)}px)`; }
      for (const w of this.walks) this._walkFrame(w, t);
    }

    // ---- showing
    _ids(ids) { return ids === 'all' ? [...this.order] : [].concat(ids); }
    show(ids, at, { stagger = 0, dur } = {}) {
      this._ids(ids).forEach((id, i) => {
        const r = this.item(id); if (!r) return;
        const t = at + i * stagger;
        if (r.kind === 'ref') {
          r.a.add(t, 0, 0); r.b.add(t, 0, 0); r.b.add(t, dur ?? 0.6, 1);
          this.tl.set(r.g, { o: 1 }, t);
        } else {
          this.tl.set(r.body, { s: 0.86 }, 0);
          this.tl.to(r.body, { o: 1, s: 1, blur: 0 }, t, dur ?? 0.5, E.out5);
          if (r.chips) r.chips.forEach((c, j) => { const cr = this.items.get(c); if (!cr.late) { this.tl.set(cr.body, { s: 0.86 }, 0); this.tl.to(cr.body, { o: 1, s: 1 }, t + 0.12 + j * 0.06, 0.45, E.out5); } });
        }
      });
      return this;
    }
    showAll(at, { stagger = 0.12 } = {}) {
      let i = 0;
      for (const id of this.order) { const r = this.items.get(id); if (r.kind === 'chip' && !r.late) continue; if (r.kind === 'chip') continue; this.show(id, at + stagger * i++); }
      return this;
    }
    // what fades with an item at time t: its body and labels; for a lock, also its chips that are at home then
    _els(r, t) {
      const out = [r.kind === 'ref' ? r.g : r.body, ...(r.extra || [])];
      if (t != null && r.chips) for (const c of r.chips) { const cr = this.items.get(c); if (cr.track.last(t) === 'home') out.push(cr.body, ...cr.extra); }
      return out;
    }
    hide(ids, at, dur = 0.4) { const s = new Set(); for (const id of this._ids(ids)) { const r = this.item(id); if (r) for (const e of this._els(r, at)) if (!s.has(e)) { s.add(e); this.tl.to(e, { o: 0 }, at, dur, E.in); } } return this; }
    dim(ids, o, at, dur = 0.4) { const s = new Set(); for (const id of this._ids(ids)) { const r = this.item(id); if (r) for (const e of this._els(r, at)) if (!s.has(e)) { s.add(e); this.tl.to(e, { o }, at, dur); } } return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    fade(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
    out(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }

    // ---- references
    _colorAt(r, t) { let c = r.c0; for (const q of r.cols) if (q.t <= t) c = q.c; return c; }
    color(id, col, at, dur = 0.35) { const r = this.item(id); if (!r) return this; this.tl.to(r.path, { stroke: col }, at, dur); r.cols.push({ t: at, c: col }); r.cols.sort((a, b) => a.t - b.t); return this; }
    open(id, at) { return this.color(id, C.pat, at); }
    close(id, at) { return this.color(id, this.item(id).c0, at); }
    owner(id, at, { dur = 0.5, on = true } = {}) { this.item(id).dbl.add(at, dur, on ? 1 : 0); return this; }
    drop(id, at, { dur = 0.6, toward = 'from' } = {}) {
      const r = this.item(id);
      if (toward === 'to') r.a.add(at, dur, 1, E.in); else r.b.add(at, dur, 0, E.in);
      for (const e of r.extra) this.tl.to(e, { o: 0 }, at, 0.3, E.in);
      return this;
    }
    cycle(ids, at, { out = null, stagger = 0 } = {}) {
      [].concat(ids).forEach((id, i) => {
        const r = this.item(id); if (!r) return;
        const t = at + i * stagger, prev = this._colorAt(r, t - 1e-3);
        this.color(id, C.bad, t, 0.4);
        if (out != null) this.color(id, prev, out, 0.4);
      });
      return this;
    }
    waiting(id, at, { out = null } = {}) { const r = this.item(id); r.dash.add(at, 0.4, 1, E.out); if (out != null) r.dash.add(out, 0.4, 0, E.out); return this; }
    bend(id, b, at, { dur = 0.7 } = {}) { this.item(id).bend.add(at, dur, b); return this; }
    retarget(id, end, node, at, { via = [], dur = 0.9 } = {}) {
      const r = this.item(id); if (!r || !this.items.has(node)) { console.warn('picture: retarget', id, node); return this; }
      (end === 'to' ? r.to : r.from).add(at, dur, { node, via: [].concat(via) });
      return this;
    }
    // the reference that joins a and b at time t
    _between(a, b, t) {
      for (const r of this.refs) {
        const f = this._nodeOf(this._endNode(r.from, t)), g = this._nodeOf(this._endNode(r.to, t));
        if (f === a && g === b) return { r, fwd: true };
        if (f === b && g === a) return { r, fwd: false };
      }
      console.warn('picture: no line between', a, b); return null;
    }
    walk(nodes, at, { via, step = 0.7, times, dur, color = C.dim, trail = 'soft', marker = 'dot', offset = 0, out = null, r: dotR = 11 } = {}) {
      const steps = [];
      for (let i = 0; i + 1 < nodes.length; i++) {
        const t0 = times ? times[i] : at + i * step;
        let e;
        if (via && via[i]) { const rr = this.item(via[i]); e = { r: rr, fwd: this._nodeOf(this._endNode(rr.from, t0)) === nodes[i] }; }
        else e = this._between(nodes[i], nodes[i + 1], t0);
        if (!e) continue;
        const d = dur ?? step * 0.85;
        const tp = el(this.trailSvg, 'path');
        tp.setAttribute('fill', 'none'); tp.setAttribute('stroke-linecap', 'round'); tp.setAttribute('stroke-linejoin', 'round');
        if (trail === 'soft') { tp.style.stroke = alpha(color, 0.25); tp.setAttribute('stroke-width', 16 * Math.max(0.5, this.k)); }
        else { tp.style.stroke = color; tp.setAttribute('stroke-width', this.lw); }
        if (!trail) tp.style.display = 'none';
        steps.push({ r: e.r, fwd: e.fwd, t: t0, d, tp, a: nodes[i], b: nodes[i + 1] });
      }
      const dot = el(this.trailSvg, 'circle'); dot.setAttribute('r', dotR * Math.max(0.6, this.k)); dot.style.fill = color; dot.style.fillOpacity = 0;
      const head = el(this.trailSvg, 'path'); const hs = 16 * Math.max(0.6, this.k);
      head.setAttribute('d', `M ${-hs} ${-hs * 0.6} L 0 0 L ${-hs} ${hs * 0.6}`); head.setAttribute('fill', 'none'); head.setAttribute('stroke-width', this.lw);
      head.setAttribute('stroke-linecap', 'round'); head.setAttribute('stroke-linejoin', 'round'); head.style.stroke = color; head.style.strokeOpacity = 0;
      const w = { steps, dot, head, marker, offset, color };
      this.walks.push(w);
      if (out != null) for (const e of [dot, head, ...steps.map(s => s.tp)]) this.tl.to(e, { o: 0 }, out, 0.4);
      const last = steps[steps.length - 1];
      return { end: last ? last.t + last.d : at, trails: steps.map(s => s.tp), dot };
    }
    _walkFrame(w, t) {
      let mk = null;
      for (const s of w.steps) {
        if (t < s.t) { s.tp.setAttribute('d', ''); continue; }
        const u = E.io(clamp((t - s.t) / s.d));
        const G = s.r._G || this._geom(s.r, t), raw = G.raw;
        const sa = this._shape(s.a, t), sb = this._shape(s.b, t);
        const N = 40, pts = [];
        let nrm = [0, 0];
        if (w.offset) { const p0 = evalCurve(raw, 0), p1 = evalCurve(raw, 1); const [ux, uy] = unit(p1[0] - p0[0], p1[1] - p0[1]); nrm = s.fwd ? [uy, -ux] : [-uy, ux]; }
        for (let i = 0; i <= N; i++) {
          const v = (i / N) * u, q = evalCurve(raw, s.fwd ? v : 1 - v);
          if (inside(sa, q[0], q[1], 4) || inside(sb, q[0], q[1], 4)) continue;
          pts.push([q[0] + nrm[0] * w.offset, q[1] + nrm[1] * w.offset]);
        }
        s.tp.setAttribute('d', pts.length > 1 ? 'M ' + pts.map(q => q[0].toFixed(1) + ' ' + q[1].toFixed(1)).join(' L ') : '');
        if (t <= s.t + s.d) {
          const q = evalCurve(raw, s.fwd ? u : 1 - u);
          const vis = !inside(sa, q[0], q[1], 2) && !inside(sb, q[0], q[1], 2);
          mk = { x: q[0] + nrm[0] * w.offset, y: q[1] + nrm[1] * w.offset, vis, pts };
        }
      }
      if (w.marker === 'dot' && mk && mk.vis) { w.dot.setAttribute('cx', mk.x); w.dot.setAttribute('cy', mk.y); w.dot.style.fillOpacity = 1; }
      else w.dot.style.fillOpacity = 0;
      // an arrowhead at the front of the trail (it stays there when the step is done)
      if (w.marker === 'head') {
        let front = null;
        for (const s of w.steps) { if (t < s.t) break; const d = s.tp.getAttribute('d'); if (d) front = d; }
        if (front) {
          const nums = front.replace(/[ML]/g, ' ').trim().split(/\s+/).map(Number), n = nums.length;
          if (n >= 4) {
            const x = nums[n - 2], y = nums[n - 1], px = nums[Math.max(0, n - 8)], py = nums[Math.max(1, n - 7)];
            w.head.setAttribute('transform', `translate(${x} ${y}) rotate(${Math.atan2(y - py, x - px) * 180 / Math.PI})`); w.head.style.strokeOpacity = 1;
          }
        } else w.head.style.strokeOpacity = 0;
      }
    }

    // ---- nodes and chips
    move(id, x, y, at, { dur = 0.8 } = {}) { this.item(id).pos.add(at, dur, this.P(x, y)); return this; }
    moveChip(id, target, at, { dur = 0.7 } = {}) { const r = this.item(id); if (r) r.track.add(at, dur, target); return this; }
    chipText(id, text, at) { const r = this.item(id); if (r && r.textEl) flip(this.tl, r.textEl, text, at); return this; }
    nodeColor(id, col, at, dur = 0.4) { this.tl.to(this.item(id).outline, { border: col }, at, dur); return this; }
    can(id, at, { out = null, color = C.good } = {}) {
      const r = this.item(id), g = 14 * Math.max(0.6, this.k);
      const ring = box(r.body, -r.hw - g, -r.hh - g, { width: 2 * (r.hw + g) + 'px', height: 2 * (r.hh + g) + 'px', borderRadius: r.kind === 'thread' ? '50%' : `calc(${r.radius} + ${g}px)`, border: `4px solid ${color}` });
      this.tl.set(ring, { o: 0, s: 0.85 }, 0); this.tl.to(ring, { o: 1, s: 1 }, at, 0.5, E.out5);
      if (out != null) this.tl.to(ring, { o: 0 }, out, 0.35);
      return ring;
    }
    gone(id, at, { dur = 0.7, lines = true, chips = true } = {}) {
      const r = this.item(id); if (!r) return this;
      this.tl.to(r.body, { o: 0, s: 1.12, blur: 5 }, at, dur, E.out);
      for (const e of r.extra || []) this.tl.to(e, { o: 0 }, at, dur * 0.7);
      if (lines) for (const q of this.refs) {
        const f = this._nodeOf(this._endNode(q.from, at)), g = this._nodeOf(this._endNode(q.to, at));
        if (f === id || g === id) for (const e of this._els(q)) this.tl.to(e, { o: 0 }, at, dur * 0.8);
      }
      if (chips && r.chips) for (const c of r.chips) { const cr = this.items.get(c); if (cr.track.last(at) === 'home') this.tl.to(cr.body, { o: 0, blur: 4 }, at, dur, E.out); }
      return this;
    }
    _endNode(tr, t) { const v = tr.last(t); return typeof v === 'string' ? v : v.node; }
    pulse(id, at, { dur = 0.6 } = {}) {
      const r = this.item(id); if (!r) return this;
      if (r.kind === 'ref') { this.tl.to(r.haloEl, { o: 1 }, at, dur * 0.35, E.out); this.tl.to(r.haloEl, { o: 0 }, at + dur * 0.5, dur * 0.6, E.io); }
      else { this.tl.to(r.body, { s: 1.1 }, at, dur * 0.4, E.out); this.tl.to(r.body, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      return this;
    }
    // an element placed by the clock at fn(t), with its own origin
    _anchor(fn, origin = 'center', layer = this.labLay, rotDeg = 0) {
      const wrap = box(layer, 0, 0, { width: '0px', height: '0px' });
      const mid = box(wrap, 0, 0, { transform: ORIGIN[origin] + (rotDeg ? ` rotate(${rotDeg}deg)` : ''), transformOrigin: 'center center', position: 'absolute' });
      this.anchors.push({ wrap, fn });
      return mid;
    }
    _refPoint(r, u, t) {
      const G = this._geom(r, t), q = evalCurve(G.c, u), q2 = evalCurve(G.c, Math.min(1, u + 0.01)), q1 = evalCurve(G.c, Math.max(0, u - 0.01));
      return { x: q[0], y: q[1], tx: q2[0] - q1[0], ty: q2[1] - q1[1] };
    }
    label(id, text, at, { out = null, side, gap = 14, size = 32, color = C.dim, font = 'label', italic = false, dx = 0, dy = 0, along = 0.5 } = {}) {
      const r = this.item(id); if (!r) return null;
      const isRef = r.kind === 'ref';
      side = side || (isRef ? 'above' : 'below');
      let fn;
      if (isRef) {
        fn = t => {
          const p = this._refPoint(r, along, t), g = gap + this.lw * (1 + 2 * r.dbl.at(t)) / 2;
          const o = { above: [0, -g], below: [0, g], left: [-g, 0], right: [g, 0], center: [0, 0] }[side];
          return { x: p.x + o[0] + dx, y: p.y + o[1] + dy };
        };
      } else {
        fn = t => {
          const p = this._npos(id, t);
          const o = { above: [0, -r.hh - gap], below: [0, r.hh + gap], left: [-r.hw - gap, 0], right: [r.hw + gap, 0], center: [0, 0] }[side];
          return { x: p.x + o[0] + dx, y: p.y + o[1] + dy };
        };
      }
      const mid = this._anchor(fn, side);
      const st = font === 'mono' ? MONO(size) : font === 'serif' ? SERIF(size) : Object.assign(LABEL(size), { paddingLeft: LS + 'em' });
      const e = box(mid, 0, 0, Object.assign(st, { position: 'relative', whiteSpace: 'pre', color, fontStyle: italic ? 'italic' : 'normal', lineHeight: 1.15 }));
      partsLine(e, text);
      fadeIn(this.tl, e, at, 0.5, 8);
      if (out != null) this.tl.to(e, { o: 0 }, out, 0.3, E.in);
      r.extra.push(e);
      return e;
    }
    strike(id, at, { out = null, fade = null } = {}) {
      let bar, w;
      const mk = (mid, ww) => { const b = box(mid, 0, 0, { position: 'relative', width: ww + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' }); this.tl.set(b, { sx: 0, o: 0 }, 0); this.tl.set(b, { o: 1 }, at); this.tl.to(b, { sx: 1 }, at, 0.4, E.io); if (out != null) this.tl.to(b, { o: 0 }, out, 0.3); return b; };
      if (id === 'all') {
        const b = this.bounds(); w = b.x1 - b.x0 + 60;
        bar = mk(this._anchor(() => ({ x: b.cx, y: b.cy }), 'center'), w);
        if (fade != null) this.tl.to(this.svg, { o: fade }, at, 0.4), this.tl.to(this.nodeLay, { o: fade }, at, 0.4), this.tl.to(this.chipLay, { o: fade }, at, 0.4);
        return bar;
      }
      const r = this.item(id);
      if (r.kind === 'ref') {
        const p = this._refPoint(r, 0.5, at), ang = Math.atan2(p.ty, p.tx) * 180 / Math.PI + 90;
        bar = mk(this._anchor(t => this._refPoint(r, 0.5, t), 'center', this.labLay, ang), 70 * Math.max(0.6, this.k));
      } else bar = mk(this._anchor(t => this._npos(id, t), 'center'), 2 * r.hw + 40 * Math.max(0.6, this.k));
      r.extra.push(bar);
      if (fade != null) for (const e of this._els(r)) if (e !== bar) this.tl.to(e, { o: fade }, at, 0.4);
      return bar;
    }
  }
  function tl0(tl, e) { tl.set(e, { o: 0 }, 0); }

  // ---- presets ------------------------------------------------------------------------------------------------------
  const popts = (cx, cy, o) => ({ x: cx, y: cy, k: o.k ?? 1, cx: 0, cy: 0, r: o.r, size: o.size, line: o.line, names: o.names === false ? false : o.names });
  function double(tl, parent, cx, cy, o = {}) {
    const { gap = 520, bend = 70 } = o;
    const p = new Picture(tl, parent, popts(cx, cy, o));
    p.thread('t', -gap / 2, 0).lock('l', gap / 2, 0, { name: '' })
      .ref('a', 't', 'l', { bend }).ref('b', 't', 'l', { bend: -bend });
    return p;
  }
  function square(tl, parent, cx, cy, o = {}) {
    const { w = 400, h = 200 } = o;
    const p = new Picture(tl, parent, popts(cx, cy, o));
    p.thread('T1', -w, 0, { name: 'T₁' }).thread('T2', w, 0, { name: 'T₂' })
      .lock('l1', 0, -h, { name: 'ℓ₁' }).lock('l2', 0, h, { name: 'ℓ₂' })
      .ref('T1-l1', 'T1', 'l1').ref('T1-l2', 'T1', 'l2').ref('T2-l1', 'T2', 'l1').ref('T2-l2', 'T2', 'l2');
    return p;
  }
  const SUBS = '₀₁₂₃₄₅₆₇₈₉', sub = n => String(n).split('').map(d => SUBS[+d]).join('');
  function ringIds(n) {
    const nodes = [], refs = [];
    for (let i = 1; i <= n; i++) nodes.push('T' + i, 'l' + i);
    for (let i = 0; i < 2 * n; i++) refs.push('r' + i);
    return { nodes, refs };
  }
  function ring(tl, parent, cx, cy, o = {}) {
    const { n = 3, radius = 290, angle = -90 } = o;
    const p = new Picture(tl, parent, popts(cx, cy, o));
    const { nodes, refs } = ringIds(n);
    nodes.forEach((id, i) => {
      const a = (angle + i * 360 / (2 * n)) * Math.PI / 180, x = radius * Math.cos(a), y = radius * Math.sin(a), j = Math.floor(i / 2) + 1;
      if (i % 2 === 0) p.thread(id, x, y, { name: 'T' + sub(j) }); else p.lock(id, x, y, { name: 'ℓ' + sub(j) });
    });
    refs.forEach((id, i) => { const a = nodes[i], b = nodes[(i + 1) % nodes.length]; if (a[0] === 'T') p.ref(id, a, b); else p.ref(id, b, a); });
    return p;
  }
  function selfloop(tl, parent, cx, cy, o = {}) {
    const { size = 140, chip = true, side = 'up' } = o;
    const p = new Picture(tl, parent, popts(cx, cy, Object.assign({}, o, { size: undefined })));
    p.lock('l', 0, 0, { size, contents: chip ? [{ ref: true }] : null });
    p.ref('loop', chip ? 'l/0' : 'l', 'l', { side, loop: o.loop });
    return p;
  }

  // ---- pills and the reference's type --------------------------------------------------------------------------
  const PILL = {
    owner: { text: 'owner', color: () => C.ink, border: () => C.ink, bg: () => alpha(C.ink, 0) },
    client: { text: 'client', color: () => C.ink, border: () => C.ink, bg: () => alpha(C.ink, 0) },
    opened: { text: 'opened', color: () => C.pat, border: () => C.pat, bg: () => alpha(C.pat, 0.12) },
    closed: { text: 'closed', color: () => C.dim, border: () => alpha(C.dim, 0.8), bg: () => alpha(C.dim, 0) },
  };
  const pillW = {};
  function measurePill(size) {
    if (pillW[size]) return pillW[size];
    let w = 0;
    for (const t of ['owner', 'client', 'opened', 'closed']) {
      const m = document.createElement('span');
      Object.assign(m.style, LABEL(size), { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' });
      m.textContent = t; document.body.appendChild(m); w = Math.max(w, m.getBoundingClientRect().width); m.remove();
    }
    return (pillW[size] = Math.round(w + size * 1.2));
  }
  class Pill {
    constructor(tl, parent, cx, y, value, { size = 30 } = {}) {
      this.tl = tl; this.size = size; this.w = measurePill(size); this.h = Math.round(size * 1.6);
      const v = value == null ? null : value;
      const s = PILL[v || 'closed'];
      this.el = box(parent, cx - this.w / 2, y, { width: this.w + 'px', height: this.h + 'px', borderRadius: this.h / 2 + 'px', border: `2.5px solid ${s.border()}`, background: s.bg() });
      this.t = box(this.el, 0, 0, Object.assign(LABEL(size), { position: 'absolute', left: 0, top: 0, width: '100%', height: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', whiteSpace: 'pre', color: s.color(), paddingLeft: LS + 'em', lineHeight: 1 }), s.text);
      this.v = v; this.shown = false;
      tl.set(this.el, { o: 0 }, 0);
    }
    show(at) { if (this.v != null) { fadeIn(this.tl, this.el, at, 0.5, 10); this.shown = true; } return this; }
    set(value, at) {
      const tl = this.tl;
      if (value == null) { tl.to(this.el, { o: 0 }, at, 0.3); this.v = null; return this; }
      const s = PILL[value];
      if (this.v == null) {
        // not shown yet: take the new look at once and rise in
        tl.text(this.t, s.text, at); tl.set(this.t, { color: s.color() }, at); tl.set(this.el, { border: s.border(), bg: s.bg() }, at);
        tl.fromTo(this.el, { o: 0, y: 10 }, { o: 1, y: 0 }, at, 0.5, E.out5);
      } else {
        if (PILL[this.v].text !== s.text) flip(tl, this.t, s.text, at);
        tl.to(this.t, { color: s.color() }, at + 0.1, 0.35); tl.to(this.el, { border: s.border(), bg: s.bg() }, at + 0.1, 0.35);
      }
      this.v = value;
      return this;
    }
    hide(at) { this.tl.to(this.el, { o: 0 }, at, 0.3, E.in); return this; }
  }
  const pillValue = (kind, v) => v == null ? null : typeof v === 'string' ? v : kind === 'owner' ? (v ? 'owner' : 'client') : (v ? 'opened' : 'closed');
  function pill(parent, cx, y, value, { size = 30, tl, at } = {}) {
    const p = new Pill(tl, parent, cx, y, value === true || value === false ? null : value, { size });
    if (at != null) p.show(at);
    return p;
  }
  class RefTag {
    constructor(tl, parent, x, y, { size = 56, owner = null, opened = null, pillSize, at } = {}) {
      Object.assign(this, { tl, parent, x, y, size });
      this.opts = { size, pillSize };
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${x}px ${y}px` });
      const l = cline(this.g, x, y, [['Lock', C.bind], ['⟨τ⟩', null]], MONO(size));
      this.text = l.root; this.typeParts = l.parts;
      const ps = pillSize ?? (size < 48 ? 26 : 30);
      this.pillY = y + Math.round(size * 1.3) + 10;
      const pw = measurePill(ps), gap = 16;
      this.pills = {
        owner: new Pill(tl, this.g, x - (pw + gap) / 2, this.pillY, pillValue('owner', owner), { size: ps }),
        opened: new Pill(tl, this.g, x + (pw + gap) / 2, this.pillY, pillValue('opened', opened), { size: ps }),
      };
      this.bottom = this.pillY + this.pills.owner.h;
      this.width = Math.max(chars('Lock⟨τ⟩').length * charWidth(size), 2 * pw + gap);
      this.state = { owner, opened };
      tl.set(this.text, { o: 0 }, 0);
      if (at != null) this.show(at);
    }
    show(at) { fadeIn(this.tl, this.text, at, 0.5, 14); this.pills.owner.show(at + 0.15); this.pills.opened.show(at + 0.25); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    dim(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
    move(dx, dy, at, dur = 0.8) { this.tl.to(this.g, { x: dx, y: dy }, at, dur, E.io); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    set({ owner, opened } = {}, at) {
      if (owner !== undefined) { this.pills.owner.set(pillValue('owner', owner), at); this.state.owner = owner; }
      if (opened !== undefined) { this.pills.opened.set(pillValue('opened', opened), at + (owner !== undefined ? 0.08 : 0)); this.state.opened = opened; }
      return this;
    }
    pulse(which, at, { dur = 0.5 } = {}) {
      const e = which === 'type' ? this.text : this.pills[which].el;
      this.tl.to(e, { s: 1.08 }, at, dur * 0.4, E.out); this.tl.to(e, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io);
      return this;
    }
    split(at, dx, dy = 0, { left, right } = {}) {
      const R = new RefTag(this.tl, this.parent, this.x, this.y, Object.assign({}, this.opts, this.state));
      // the copy is there at once, exactly over this one, and then both move apart
      this.tl.set(R.text, { o: 1, y: 0 }, at);
      for (const k of ['owner', 'opened']) if (R.pills[k].v != null) { this.tl.set(R.pills[k].el, { o: 1 }, at); R.pills[k].shown = true; }
      this.move(-dx, dy, at, 0.8); R.move(dx, dy, at, 0.8);
      if (left) this.set(left, at + 0.5);
      if (right) R.set(right, at + 0.5);
      return [this, R];
    }
  }
  const refTag = (tl, parent, x, y, opts) => new RefTag(tl, parent, x, y, opts);

  // ---- a lock type with its two bits: LX.lockType, LX.typeLine ------------------------------------------------
  const isBitNum = v => v === 0 || v === 1 || v === '0' || v === '1';
  const bitText = v => (v == null ? '' : String(v));
  const bitColor = (v, lower) => (isBitNum(v) ? (lower && String(v) === '1' ? C.pat : C.code) : C.dim);
  // the sizes of a lock type (its whole width first, so that align and typeLine can place it)
  function ltMetrics({ size = 56, of = 'τ', a = null, b = null, entries, bitSize, bitChars } = {}) {
    const cw = charWidth(size), bs = bitSize ?? Math.max(28, Math.round(size * 0.66)), bcw = charWidth(bs);
    const ents = (entries || [{ of, a, b }]).map(e => Object.assign({ of: 'τ' }, e));
    const bw = Math.max(1, bitChars ?? 0, ...ents.flatMap(e => [chars(bitText(e.a)).length, chars(bitText(e.b)).length])) * bcw;
    const padL = Math.round(cw * 0.08), padR = Math.round(cw * 0.14), sepW = 2 * cw;   // sepW: ', '
    const width = 5 * cw + ents.reduce((s, e) => s + chars(e.of).length * cw + padL + bw + padR, 0) + sepW * (ents.length - 1) + cw;
    return { bs, bw, padL, padR, sepW, ents, width };
  }
  class LockType {
    constructor(tl, parent, x, y, { size = 56, of = 'τ', a = null, b = null, entries, align = 'left', at, bitSize, bitChars } = {}) {
      Object.assign(this, { tl, parent, size });
      const S = size, cw = charWidth(S);
      const { bs, bw, padL, padR, sepW, ents, width } = ltMetrics({ size, of, a, b, entries, bitSize, bitChars });
      this.bs = bs;
      const x0 = align === 'center' ? x - width / 2 : align === 'right' ? x - width : x;
      Object.assign(this, { x: x0, y, width, height: Math.round(S * 1.3), cx: x0 + width / 2 });
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${x0}px ${y}px` });
      const txt = (xx, t, col) => box(this.g, xx, y, Object.assign(MONO(S), { whiteSpace: 'pre', color: col }), t);
      this.lockEl = txt(x0, 'Lock', C.bind);
      const rest = [txt(x0 + 4 * cw, '⟨', C.code)];
      // the bits: the upper one raised, the lower one lowered, a gap between them, both in one column after the τ
      const m = y + 0.64 * S, gap = Math.max(0.125 * S, 5);
      const topU = m - gap - 0.835 * bs, topL = m + gap - 0.145 * bs;
      this.entries = [];
      let xx = x0 + 5 * cw;
      ents.forEach((e, i) => {
        const els = [];
        if (i > 0) { els.push(txt(xx, ',', C.code)); xx += sepW; }
        els.push(txt(xx, e.of, C.code)); rest.push(...els);
        const bx = xx + chars(e.of).length * cw + padL;
        const mk = (top, v, lower) => {
          const w = box(this.g, bx, top, { width: bw + 'px', height: bs + 'px', transformOrigin: 'center center' });
          const t = box(w, 0, 0, Object.assign(MONO(bs), { width: bw + 'px', textAlign: 'center', lineHeight: 1, whiteSpace: 'pre', color: bitColor(v, lower), transformOrigin: 'center center' }), bitText(v));
          return { wrap: w, text: t, v };
        };
        const ea = mk(topU, e.a, false), eb = mk(topL, e.b, true);
        els.push(ea.wrap, eb.wrap);
        this.entries.push({ of: e.of, x: xx, bx, bw, a: ea, b: eb, els });
        xx = bx + bw + padR;
      });
      rest.push(txt(xx, '⟩', C.code));
      this.rest = rest;
      tl.set(this.g, { o: 0 }, 0);
      if (at != null) this.show(at);
    }
    show(at, dur = 0.5) { fadeIn(this.tl, this.g, at, dur, 12); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    dim(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
    move(dx, dy, at, dur = 0.8) { this.tl.to(this.g, { x: dx, y: dy }, at, dur, E.io); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    bit(which, i = 0) { return this.entries[i][which]; }
    // a bit (or both) changes: it squeezes, takes its new value and colour, and pulses so that the change is seen
    set({ a, b } = {}, at, { i = 0 } = {}) {
      [['a', a, false], ['b', b, true]].forEach(([k, v, lower], j) => {
        if (v === undefined) return;
        const bt = this.entries[i][k], t = at + j * 0.12 * (a !== undefined && b !== undefined ? 1 : 0);
        flip(this.tl, bt.text, bitText(v), t, 0.4);
        this.tl.to(bt.text, { color: bitColor(v, lower) }, t + 0.16, 0.25);
        this.pulse(k, t + 0.3, { i });
        bt.v = v;
      });
      return this;
    }
    pulse(which, at, { i = 0, dur = 0.55, s = 1.45 } = {}) {
      const w = which === 'type' ? this.g : this.entries[i][which].wrap;
      this.tl.to(w, { s }, at, dur * 0.4, E.out); this.tl.to(w, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io);
      return this;
    }
    // stage rectangles: the whole type, or an entry's bit column ({x, y, w, h, cx, cy})
    rect() { return { x: this.x, y: this.y, w: this.width, h: this.height, cx: this.cx, cy: this.y + this.height / 2 }; }
    bitRect(i = 0) { const e = this.entries[i]; return { x: e.bx, y: this.y, w: e.bw, h: this.height, cx: e.bx + e.bw / 2, cy: this.y + this.height / 2 }; }
    entryX(i = 0) { const e = this.entries[i]; return e.x + charWidth(this.size) * chars(e.of).length / 2; }
  }
  const lockType = (tl, parent, x, y, opts) => new LockType(tl, parent, x, y, opts);
  // a typing set in one line: parts are strings (mono, ink; or [text, colour]) and lock types ({a, b, of, entries})
  class TypeLine {
    constructor(tl, parent, x, y, size, parts, { align = 'left', at, stagger = 0 } = {}) {
      Object.assign(this, { tl, size });
      const cw = charWidth(size);
      const specs = parts.map(p => (typeof p === 'string' || Array.isArray(p)) ? { str: [].concat(p) } : { lt: p });
      const tmp = specs.map(s => s.str ? chars(s.str[0]).length * cw : ltMetrics(Object.assign({ size }, s.lt)).width);
      const width = tmp.reduce((s, w) => s + w, 0);
      const x0 = align === 'center' ? x - width / 2 : align === 'right' ? x - width : x;
      Object.assign(this, { x: x0, y, width, height: Math.round(size * 1.3) });
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${x0}px ${y}px` });
      this.els = []; this.types = [];
      let xx = x0;
      specs.forEach((s, i) => {
        if (s.str) {
          const e = box(this.g, xx, y, Object.assign(MONO(size), { whiteSpace: 'pre', color: s.str[1] || C.code }), s.str[0]);
          this.els.push(e);
        } else {
          const t = new LockType(tl, this.g, xx, y, Object.assign({ size }, s.lt));
          tl.set(t.g, { o: 1 }, 0);
          this.els.push(t.g); this.types.push(t);
        }
        xx += tmp[i];
      });
      tl.set(this.g, { o: 0 }, 0);
      if (at != null) this.show(at);
    }
    show(at, dur = 0.5) { fadeIn(this.tl, this.g, at, dur, 12); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    dim(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
    rect() { return { x: this.x, y: this.y, w: this.width, h: this.height, cx: this.x + this.width / 2, cy: this.y + this.height / 2 }; }
  }
  const typeLine = (tl, parent, x, y, size, parts, opts) => new TypeLine(tl, parent, x, y, size, parts, opts);

  // ---- the title ------------------------------------------------------------------------------------------------
  const TITLE = ['Higher-Order Leak and', 'Deadlock Free Locks'], AUTHORS = ['Jules Jacobs · Stephanie Balzer', 'POPL 2023'];
  function titleCard(tl, root, { align = 'left', x = RAIL, y = 300, size = 110, at, at2, authorsAt, authorSize = 32, gap = 34 } = {}) {
    const mk = (text, yy, style, inset = 0) => align === 'left' ? box(root, x - inset, yy, Object.assign({ whiteSpace: 'pre' }, style), text) : cline(root, x, yy, [[text, null]], style).root;
    const lh = Math.round(size * 1.22);
    const lines = TITLE.map((t, i) => mk(t, y + i * lh, SERIF(size), size * 0.05));
    const ay = y + 2 * lh + gap;
    const authors = AUTHORS.map((t, i) => mk(t, ay + i * Math.round(authorSize * 1.65), LABEL(authorSize)));
    for (const e of [...lines, ...authors]) tl.set(e, { o: 0 }, 0);
    if (at != null) fadeIn(tl, lines[0], at, 0.8, 24);
    if (at != null || at2 != null) fadeIn(tl, lines[1], at2 ?? at + 0.5, 0.8, 24);
    if (authorsAt != null) authors.forEach((a, i) => fadeIn(tl, a, authorsAt + i * 0.25, 0.6, 10));
    return { lines, authors, bottom: ay + 2 * Math.round(authorSize * 1.65) };
  }

  // ---- rows -------------------------------------------------------------------------------------------------------
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

  window.LX = {
    CX, RAIL, LINE, LOCKS, LABEL, SERIF, MONO, cline, lline, clabel, cserif, note, strikeEl,
    svg: svgLayer, tick: tickM, cross: crossM, dpath, line, arc, strikeLine, cell, flip, circleD, ctext, dim,
    sub, code, Listing, Picture, double, square, ring, ringIds, selfloop, refTag, RefTag, pill, Pill,
    lockType, LockType, typeLine, TypeLine,
    titleCard, TITLE, AUTHORS, Rows,
  };
})();

// ==== src/scenes/a_open.js ====
// The opening (hook, roadmap, title) and the close (recap, end) of the video, built with LX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = LX;


  // ============================================ hook ==========================================================
  scene('hook', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    // "Here is a short program in Rust."
    const rust = LX.note(tl, root, RAIL, 130, 'Rust', cue('rust') - 0.2, null, { align: 'left' });
    // the caller, a line at each of its sentences; then the function it calls
    const caller = LX.code(tl, root, RAIL, 200, 42, ['let m1 = Arc::new(Mutex::new(1));', 'let m2 = m1.clone();', 'swap(&m1, &m2);']);
    caller.showLine(0, cue('m') - 0.2); caller.showLine(1, cue('two') - 0.2); caller.showLine(2, cue('swap') - 0.2);
    const fn = LX.code(tl, root, RAIL, 470, 36, ['fn swap(m1: &Mutex<i32>, m2: &Mutex<i32>) {', '    let mut g1 = m1.lock();', '    let mut g2 = m2.lock();', '    …', '}']);
    fn.show(cue('swap') + 1.0, { stagger: 0.08 });               // "a function that swaps"
    // "The compiler accepts it.": a tick and COMPILES to the right of the caller (level with its first line)
    const ty = caller.lineY(0) + caller.lh / 2, tx = RAIL + caller.width + 70;
    const tk = LX.tick(tl, svg, tx, ty, 44, cue('ok') + 0.6);
    const comp = LX.note(tl, root, tx + 50, ty - 19, 'compiles', cue('ok') + 0.7, cue('run') - 0.3, { align: 'left', color: C.good });
    tk.hide(cue('run') - 0.3);
    // "Run it, and it never finishes.": RUNNING, then three dots one after the other
    const run = LX.lline(root, tx - 22, ty - 19, ['running', ' .', ' .', ' .'], LX.LABEL(32));
    const tRun = cue('run');
    [-0.1, 0.9, 1.35, 1.8].forEach((d, i) => fadeIn(tl, run.parts[i], tRun + d, 0.4, 8));
    // "The function locks its first argument, and then its second. But they are the same lock, so the thread waits
    // for itself, forever.": the first lock line is taken (amber), the second waits (red)
    const tWhy = cue('why');
    fn.mark(1, null, C.pat, tWhy + 0.55);
    fn.mark(2, null, C.dim, tWhy + 2.3, { fill: 0.08, out: tWhy + 5.9 });
    caller.pulse(1, 'm2', tWhy + 4.1); caller.pulse(1, 'm1', tWhy + 4.1);   // "the same lock"
    fn.mark(2, null, C.bad, tWhy + 5.9);
    const wr = fn.rect(2, null);
    const waits = LX.note(tl, root, wr.x + wr.w + 40, wr.cy - 19, 'waits for itself', tWhy + 6.0, null, { align: 'left', color: C.bad });
    // "That is a deadlock."
    const dead = box(root, 1380, 300, Object.assign(LX.SERIF(88), { color: C.bad, whiteSpace: 'pre' }), 'deadlock');
    fadeIn(tl, dead, cue('dead') + 0.45, 0.6, 16);

    // "A similar program fails in another way": everything leaves; the second program
    const tLeak = cue('leak'), first = [rust, caller.root, fn.root, run.root, dead, waits, svg];
    for (const e of first) fadeOut(tl, e, tLeak - 0.35, 0.35);
    const leak = LX.code(tl, root, RAIL, 220, 36, [
      'struct X { x: Option<Arc<Mutex<X>>> }',
      'let m1 = Arc::new(Mutex::new(X { x: None }));',
      'let m2 = m1.clone();',
      'let mut g = m1.lock();',
      '*g = X { x: Some(m2) };',
      'drop(g);',
      'drop(m1);',
    ]);
    leak.show(tLeak + 0.1, { stagger: 0.07 });
    // "it stores the second reference inside the mutex itself"
    leak.mark(4, null, C.dim, tLeak + 2.95, { fill: 0.08 });
    // "Now the mutex keeps itself alive": a lock and a line from it back into it, red
    const tCyc = cue('cycle');
    const sl = LX.selfloop(tl, root, 1420, 500, { size: 120, chip: false });
    sl.color('loop', C.bad, 0, 0);
    sl.show('l', tCyc - 0.25); sl.show('loop', tCyc + 0.25, { dur: 0.9 });
    const lw = LX.cserif(root, 1420, 590, 'leak', 88, C.bad);
    fadeIn(tl, lw, tCyc + 0.65, 0.6, 16);
    const keeps = LX.note(tl, root, 1420, 712, 'it keeps itself alive', tCyc + 1.05, null);

    // "Rust's types rule out data races. They do not rule out deadlocks, or leaks."
    const tSafe = cue('safe');
    for (const e of [leak.root, sl.g, lw, keeps]) fadeOut(tl, e, tSafe - 0.35, 0.35);
    const svg2 = LX.svg(root);
    const rowsG = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const rowY = i => 300 + i * 130, RX = 880;
    const word = (i, text, at) => { const e = box(rowsG, RX - 800, rowY(i), Object.assign(LX.SERIF(60), { width: '800px', textAlign: 'right', whiteSpace: 'pre' }), text); fadeIn(tl, e, at, 0.6, 16); return e; };
    const lab = (i, text, at, color) => LX.note(tl, rowsG, RX + 120, rowY(i) + 18, text, at, null, { align: 'left', color });
    word(0, 'data races', tSafe + 1.45);
    const tk2 = LX.tick(tl, svg2, RX + 60, rowY(0) + 38, 44, tSafe + 1.95);
    lab(0, "ruled out by Rust's types", tSafe + 2.05, C.dim);
    word(1, 'deadlocks', tSafe + 3.7); lab(1, 'not ruled out', tSafe + 3.85, C.dim);
    word(2, 'leaks', tSafe + 4.65); lab(2, 'not ruled out', tSafe + 4.8, C.dim);
    // "This video is about a small model language with locks, in which the type checker rules out both."
    const tV = cue('video');
    for (const e of [rowsG, ...tk2.els]) { tl.to(e, { o: 0.3 }, tV - 0.1, 0.6); tl.to(e, { y: -140 }, tV - 0.1, 0.8, E.io); }
    const lang = LX.cserif(root, CX, 521, 'a small language with locks', 64);
    fadeIn(tl, lang, tV + 1.0, 0.7, 18);
    LX.note(tl, root, CX, 628, 'if it type-checks: no deadlock, no leak', tV + 4.3, null, { color: C.good });
    // "We will see the single rule behind it, the lock operations that keep the rule, and how it extends to programs
    // that need a cycle, like the dining philosophers.": what is coming, one label at each
    const tP = cue('promise');
    LX.note(tl, root, CX, 736, 'one rule', tP + 0.65, null, { color: C.ink });
    LX.note(tl, root, CX, 790, 'the operations that keep it', tP + 2.6, null, { color: C.ink });
    LX.note(tl, root, CX, 844, 'cycles on purpose: the dining philosophers', cue('end') + 1.6, null, { color: C.ink });
  });

  // ============================================ roadmap =======================================================
  scene('roadmap', ({ tl, root, cue }) => {
    const head = box(root, RAIL, 132, Object.assign(LX.LABEL(32), { color: C.ink }), 'in this video');
    fadeIn(tl, head, cue('coming') - 0.15, 0.5, 10);
    // the evidence column: the storyboard's x = 1100 would run into the longest title, which ends near 1125
    const rows = new LX.Rows(tl, root, { x: RAIL, y: 220, pitch: 94, size: 48, titleX: RAIL + 56 });
    const EX = 1170;
    const label = (i, text, at, color, size = 32, ls) => rows.evidence(i, box(root, EX, rows.mid(i) - size * 0.6, Object.assign(LX.LABEL(size), { color, whiteSpace: 'pre' }, ls ? { letterSpacing: ls } : {}), text), at);
    const mono = (i, text, at) => rows.evidence(i, box(root, EX, rows.mid(i) - 24, Object.assign(LX.MONO(36), { whiteSpace: 'pre' }), text), at);

    rows.row('What deadlocks and leaks have in common', cue('wrong') - 0.1);
    const loop = LX.selfloop(tl, root, EX + 30, rows.mid(0) + 18, { size: 40, chip: false, line: 2.5, loop: 36 });
    loop.color('loop', C.bad, 0, 0); loop.showAll(cue('wrong') + 1.4, { stagger: 0.2 }); rows.rows[0].add(loop.g);

    rows.row('One rule: no cycles', cue('inv') - 0.1);
    const ch = new LX.Picture(tl, root, { r: 16, size: 30, line: 2.5 });
    const y1 = rows.mid(1);
    ch.thread('a', EX + 16, y1).lock('l', EX + 96, y1).thread('b', EX + 176, y1).ref('x', 'a', 'l').ref('y', 'b', 'l');
    ch.showAll(cue('inv') + 1.7, { stagger: 0.1 }); rows.rows[1].add(ch.g);

    rows.row('The operations that keep the rule', cue('ops') - 0.1);
    mono(2, 'new  acquire  release  fork', cue('ops') + 0.6);

    rows.row('Who frees a lock', cue('own') - 0.1);
    mono(3, 'wait  drop', cue('own') + 0.5);

    rows.row('Programs', cue('prog') - 0.1);
    label(4, 'futures · shared data · channels', cue('prog') + 0.6, C.dim, 30, '0.1em');   // narrower, to fit the stage

    rows.row('The theorem', cue('thm') - 0.1);
    label(5, 'no deadlock, no leak', cue('thm') + 0.35, C.good);

    rows.row('Lock groups', cue('groups') - 0.1);
    const rg = LX.ring(tl, root, EX + 44, rows.mid(6), { radius: 37, r: 12, size: 22, line: 2.5, names: false });
    rg.showAll(cue('groups') + 0.35, { stagger: 0.04 }); rows.rows[6].add(rg.g);
  });

  // ============================================ title =========================================================
  scene('title', ({ tl, root, cue }) => {
    const t = cue('title');
    LX.titleCard(tl, root, { align: 'left', x: RAIL, y: 300, size: 110, at: t - 0.2, at2: t + 1.25, authorsAt: t + 2.3 });
  });

  // ============================================ recap =========================================================
  scene('recap', ({ tl, root, cue }) => {
    const rows = new LX.Rows(tl, root, { x: RAIL, y: 200, pitch: 108, size: 48, titleX: RAIL + 56 });
    const EX = 1440;

    // "Deadlocks and leaks are cycles"
    rows.row('Deadlocks and leaks are cycles', cue('r1') - 0.1);
    const loop = LX.selfloop(tl, root, EX + 30, rows.mid(0) + 18, { size: 40, chip: false, line: 2.5, loop: 36 });
    loop.color('loop', C.bad, 0, 0); loop.showAll(cue('r1') + 1.3, { stagger: 0.2 }); rows.rows[0].add(loop.g);

    // "So keep the picture of threads and locks free of cycles.": a small tree, and a tick
    rows.row('Keep the picture free of cycles', cue('r2') - 0.1);
    const y = rows.mid(1) - 10, tr = new LX.Picture(tl, root, { r: 13, size: 24, line: 2.5 });
    tr.thread('a', EX + 13, y).lock('b', EX + 68, y).thread('c', EX + 123, y).lock('d', EX + 178, y).thread('e', EX + 233, y)
      .lock('f', EX + 123, y + 44)
      .ref('ab', 'a', 'b').ref('cb', 'c', 'b').ref('cd', 'c', 'd').ref('ed', 'e', 'd').ref('cf', 'c', 'f');
    tr.showAll(cue('r2') + 0.7, { stagger: 0.06 }); rows.rows[1].add(tr.g);
    const svg = LX.svg(root);
    const tk = LX.tick(tl, svg, EX + 300, y + 4, 40, cue('r2') + 2.4);
    rows.rows[1].add(tk.els[0]);

    // "New and fork join each new thing to the picture in one place, so they keep it that way, and threads stay free
    // to lock in any order."
    rows.row('new and fork join in one place; lock in any order', cue('r3') - 0.1);
    const nf = LX.lline(root, EX, rows.mid(2) - 24, ['new', '  fork'], LX.MONO(36));
    fadeIn(tl, nf.parts[0], cue('r3') + 0.1, 0.5, 10); fadeIn(tl, nf.parts[1], cue('r3') + 0.7, 0.5, 10);
    rows.rows[2].add(nf.root);

    // "One owner for each lock, who waits for the clients, takes care of freeing."
    rows.row('One owner, who waits for the clients', cue('r4') - 0.1);
    rows.evidence(3, box(root, EX, rows.mid(3) - 24, Object.assign(LX.MONO(36), { whiteSpace: 'pre' }), 'wait'), cue('r4') + 1.65);

    // "Lock groups add local lock orders, where a cycle is needed."
    rows.row('Lock groups: local lock orders', cue('r5') - 0.1);
    const g = new LX.Picture(tl, root, { size: 30, line: 2.5 }), gy = rows.mid(4);
    g.group('g', EX + 90, gy, 180, 62).lock('a', EX + 40, gy, { group: 'g' }).lock('b', EX + 90, gy, { group: 'g' }).lock('c', EX + 140, gy, { group: 'g' });
    g.showAll(cue('r5') + 0.35, { stagger: 0.08 }); rows.rows[4].add(g.g);

    // "And all of it is checked locally, one operation at a time: a program that type-checks cannot deadlock, and
    // cannot leak.": the tick at "checked locally"
    rows.row('Checked locally: no deadlock, no leak', cue('r6') - 0.1);
    const tk6 = LX.tick(tl, svg, EX + 24, rows.mid(5), 48, cue('r6') + 1.1);
    rows.rows[5].add(tk6.els[0]);
  });

  // ============================================ end ===========================================================
  scene('end', ({ tl, root, cue }) => {
    const t = cue('title');
    const tc = LX.titleCard(tl, root, { align: 'center', x: CX, y: 290, size: 96, at: t - 0.2, at2: t + 1.15, authorsAt: t + 2.2 });
    // "The paper has the full type systems, the operational semantics, the encoding of channels, and a sketch of the
    // proofs, which are checked in full by machine.": each item at its words
    const y = tc.bottom + 46, tp = cue('paper');
    const l1 = LX.cline(root, CX, y, ['in the paper:', ' the type systems', ' · the semantics', ' · channels'], LX.LABEL(32));
    const l2 = LX.cline(root, CX, y + 54, ['a sketch of the proofs,', ' mechanized in Coq'], LX.LABEL(32));
    [[l1.parts[0], 0], [l1.parts[1], 1.05], [l1.parts[2], 2.6], [l1.parts[3], 4.95], [l2.parts[0], 6.2], [l2.parts[1], 8.0]]
      .forEach(([e, d]) => fadeIn(tl, e, tp - 0.1 + d, 0.5, 10));
    return { keep: true };
  });

})();

// ==== src/scenes/b.js ====
// What goes wrong (wrong_a, wrong_b, wrong_c) and the rule (rule_a), built with LX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = LX;

  // a dim, rounded box with a small caps label inside (wrong_c's "parts of the program")
  function partBox(root, cx, cy, w, h, text) {
    const b = box(root, cx - w / 2, cy - h / 2, { width: w + 'px', height: h + 'px', borderRadius: '22px', border: `3px solid ${alpha(C.dim, 0.55)}`, display: 'flex', alignItems: 'center', justifyContent: 'center' });
    const t = box(b, 0, 0, Object.assign(LX.LABEL(32), { position: 'relative', whiteSpace: 'pre', paddingLeft: '0.16em' }), text);
    return b;
  }

  // ============================================ wrong_a =======================================================
  scene('wrong_a', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    // "Look again at the swap.": the function at the left, the caller at the right
    const fnLines = [
      'fn swap(m1: &Mutex<i32>, m2: &Mutex<i32>) {',
      '    let mut g1 = m1.lock();',
      '    let mut g2 = m2.lock();',
      '    let tmp = *g1;',
      '    *g1 = *g2;',
      '    *g2 = tmp;',
      '    drop(g1); drop(g2)',
      '}',
    ];
    const tS = cue('swap');
    const fnHead = LX.note(tl, root, RAIL, 170, 'the function', tS - 0.2, null, { align: 'left' });
    const fn = LX.code(tl, root, RAIL, 232, 33, fnLines);
    fn.show(tS - 0.1, { stagger: 0.06 });
    const RX = 1090;   // the storyboard's 1080 left the function's last brace touching the caller
    const callHead = LX.note(tl, root, RX, 170, 'the caller', tS + 0.4, null, { align: 'left' });
    const caller = LX.code(tl, root, RX, 230, 37, ['let m1 = Arc::new(Mutex::new(1));', 'let m2 = m1.clone();', 'swap(&m1, &m2);']);
    caller.show(tS + 0.5, { stagger: 0.1 });

    // "The function is fine" / "The caller is fine too": a tick and FINE BY ITSELF under each panel, on one row
    const okY = 690;
    const tk1 = LX.tick(tl, svg, RAIL + 22, okY, 44, cue('fn') + 0.5);
    const ok1 = LX.note(tl, root, RAIL + 66, okY - 19, 'fine by itself', cue('fn') + 0.6, null, { align: 'left' });
    const tk2 = LX.tick(tl, svg, RX + 22, okY, 44, cue('call') + 0.6);
    const ok2 = LX.note(tl, root, RX + 66, okY - 19, 'fine by itself', cue('call') + 0.7, null, { align: 'left' });

    // "Only the combination fails.": a red bracket under both panels, TOGETHER: A DEADLOCK
    const bx0 = RAIL, bx1 = RX + caller.width, by = 770;
    const br = LX.dpath(tl, svg, `M ${bx0} ${by - 22} L ${bx0} ${by} L ${(bx0 + bx1) / 2 - 18} ${by} L ${(bx0 + bx1) / 2} ${by + 18} L ${(bx0 + bx1) / 2 + 18} ${by} L ${bx1} ${by} L ${bx1} ${by - 22}`, { stroke: C.bad, width: 3 });
    tl.set(br, { o: 1 }, cue('comp') + 0.2);
    tl.to(br, { draw: 1 }, cue('comp') + 0.2, 0.7, E.io);
    const tog = LX.note(tl, root, (bx0 + bx1) / 2, by + 34, 'together: a deadlock', cue('comp') + 0.7, null, { color: C.bad });

    // "To see it, draw a picture.": everything leaves
    const tG = cue('graph');
    for (const e of [fnHead, callHead, fn.root, caller.root, ok1, ok2, tog, svg]) fadeOut(tl, e, tG + 0.4, 0.4);

    // a thread, a lock, a reference
    const p = new LX.Picture(tl, root);
    p.thread('t', 700, 500).lock('l', 1220, 500).ref('a', 't', 'l').ref('b', 't', 'l', { bend: -70 });
    p.show('t', cue('t') + 0.1);
    p.label('t', 'a thread', cue('t') + 0.4, { out: cue('two') - 0.1 });
    p.show('l', cue('l') + 0.1);
    p.label('l', 'a lock', cue('l') + 0.4, { out: cue('two') - 0.1 });
    p.show('a', cue('e') + 0.2, { dur: 0.8 });
    p.label('a', 'a reference', cue('e') + 1.1, { out: cue('two') - 0.1 });
    // "Our thread holds two references to one lock: two lines between the same two points."
    const tT = cue('two');
    p.bend('a', 70, tT + 0.1, { dur: 0.7 });
    p.show('b', tT + 2.9, { dur: 0.8 });            // "two lines"
    p.label('a', 'm1', tT + 1.4, { font: 'mono', size: 36, color: C.bind });
    p.label('b', 'm2', tT + 3.5, { font: 'mono', size: 36, color: C.bind, side: 'below' });
    // "We count that as a cycle: you can go out along one line, and come back along the other."
    const tC = cue('cyc');
    p.cycle(['a', 'b'], tC + 0.8);
    LX.note(tl, root, 960, 690, 'a cycle', tC + 1.4, null, { color: C.bad });
    p.walk(['t', 'l', 't'], 0, { via: ['a', 'b'], times: [tC + 2.3, tC + 3.8], dur: 1.0, color: C.bad });
  });

  // ============================================ wrong_b =======================================================
  scene('wrong_b', ({ tl, root, cue }) => {
    // "The classic deadlock has two threads and two locks."
    const sq = LX.square(tl, root, 960, 480);
    const t0 = cue('classic');
    sq.show(['T1', 'T2'], t0 + 1.7, { stagger: 0.15 });
    sq.show(['l1', 'l2'], t0 + 2.6, { stagger: 0.15 });
    sq.show(['T1-l1', 'T1-l2', 'T2-l1', 'T2-l2'], t0 + 3.2, { stagger: 0.1 });
    // "One thread takes the first lock and then the second. The other takes the second and then the first."
    const tO = cue('ord');
    const ordNote = (x, a, b, align, at) => {
      const parts = [[a, C.bind], [' then ', C.dim], [b, C.bind]];
      const st = Object.assign(LX.MONO(36), { whiteSpace: 'pre' });
      const l = align === 'left' ? LX.lline(root, x, 480 - 24, parts, st) : LX.lline(root, x, 480 - 24, parts, Object.assign(st, {}));
      fadeIn(tl, l.root, at, 0.5, 10);
      return l.root;
    };
    const n1 = ordNote(240, 'ℓ₁', 'ℓ₂', 'left', tO + 0.2);
    const n2 = ordNote(1462, 'ℓ₂', 'ℓ₁', 'left', tO + 3.5);
    // "Each can end up holding one lock, and waiting for the other."
    const tSt = cue('stuck');
    sq.open('T1-l1', tSt + 0.8); sq.open('T2-l2', tSt + 0.8);
    sq.waiting('T1-l2', tSt + 2.4); sq.waiting('T2-l1', tSt + 2.4);
    sq.label('T1-l2', 'waiting', tSt + 2.6, { side: 'below', dx: -80, dy: 14 });
    sq.label('T2-l1', 'waiting', tSt + 2.6, { side: 'above', dx: 80, dy: -14 });
    // "In the picture: four lines that close a loop."
    const tQ = cue('sq');
    for (const e of [n1, n2]) fadeOut(tl, e, tQ - 0.2, 0.35);
    sq.cycle(['T1-l1', 'T2-l1', 'T2-l2', 'T1-l2'], tQ + 1.0, { stagger: 0.2 });
    LX.note(tl, root, 960, 461, 'a cycle', tQ + 1.8, cue('three') - 0.35, { color: C.bad });
    // "With three threads and three locks, any two threads share only one lock"
    const tTh = cue('three');
    sq.out(tTh - 0.35, 0.35);
    const rg = LX.ring(tl, root, 960, 480, { radius: 290 });
    const { nodes, refs } = LX.ringIds(3);
    rg.show(nodes.filter(n => n[0] === 'T'), tTh + 0.2, { stagger: 0.1 });
    rg.show(nodes.filter(n => n[0] === 'l'), tTh + 1.2, { stagger: 0.1 });
    rg.show(refs, tTh + 1.7, { stagger: 0.08 });
    const share = LX.note(tl, root, 960, 846, 'any two threads share only one lock', tTh + 2.1, null);
    // "and still they can wait for each other around a ring."
    rg.cycle(refs, cue('still') + 0.3, { stagger: 0.35 });
    // "And the leak: a lock whose contents hold a reference to the lock itself."
    const tL = cue('leak');
    rg.out(tL - 0.35, 0.35); fadeOut(tl, share, tL - 0.35, 0.35);
    const sl = LX.selfloop(tl, root, 960, 560, { size: 140, loop: 210 });
    sl.color('loop', C.bad, 0, 0);
    sl.show('l', tL + 1.2);
    sl.pulse('l/0', tL + 2.3);                       // "whose contents"
    // "Draw that reference as a line too. It goes from the lock back to itself."
    const tLp = cue('loop');
    sl.show('loop', tLp + 1.2, { dur: 1.1 });
    const lk = LX.note(tl, root, 960, 670, 'a leak', tLp + 2.6, null, { color: C.bad });
    // "Every one of these failures is a cycle.": a row of four small pictures, all red
    const tA = cue('all');
    fadeOut(tl, lk, tA - 0.3, 0.3);
    const RY = 470, k = 0.4;
    sl.to({ s: k, x: 1580 - 960, y: RY + 40 - 560 }, tA - 0.2, 0.8);
    // at its place, the shrunk drawing (its lines thinned by the scaling) hands over to a small one drawn at that size
    const sl2 = LX.selfloop(tl, root, 1580, RY + 40, { k, size: 140, loop: 210 });
    sl2.color('loop', C.bad, 0, 0);
    sl2.show(['l', 'loop'], tA + 0.6, { dur: 0.3 }); sl.out(tA + 0.75, 0.3);
    const d = LX.double(tl, root, 420, RY, { k });
    d.color('a', C.bad, 0, 0); d.color('b', C.bad, 0, 0);
    const s4 = LX.square(tl, root, 830, RY, { k });
    for (const id of ['T1-l1', 'T1-l2', 'T2-l1', 'T2-l2']) s4.color(id, C.bad, 0, 0);
    const r3 = LX.ring(tl, root, 1260, RY, { radius: 120, k: 1, r: 18, size: 34, line: 2.5, names: false });
    for (const id of refs) r3.color(id, C.bad, 0, 0);
    d.showAll(tA + 0.1, { stagger: 0.05 });
    s4.showAll(tA + 0.35, { stagger: 0.04 });
    r3.showAll(tA + 0.6, { stagger: 0.03 });
    LX.note(tl, root, 960, 640, 'every one is a cycle', tA + 1.4, null, { color: C.bad });
  });

  // ============================================ wrong_c =======================================================
  scene('wrong_c', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    // "The usual defence is a lock order: number all the locks in the program, and always take them in increasing
    // order.": a column of five locks, numbered from the bottom, an arrow going up beside them
    const tU = cue('usual'), COLX = 440, ys = [740, 620, 500, 380, 260];
    const col = new LX.Picture(tl, root, { size: 80 });
    ys.forEach((y, i) => col.lock('n' + i, COLX, y));
    col.show(ys.map((_, i) => 'n' + i), tU + 0.1, { stagger: 0.12 });
    ys.forEach((_, i) => col.label('n' + i, String(i + 1), tU + 2.8 + i * 0.18, { side: 'center', font: 'mono', size: 36, color: C.bind }));
    const ar = LX.line(tl, svg, COLX - 110, 770, COLX - 110, 230, { at: tU + 5.8, dur: 0.9, stroke: C.ink, head: 16 });
    const ord = LX.note(tl, root, RAIL, 146, 'a lock order: always in increasing order', tU + 1.6, null, { align: 'left' });
    // "That works, but the order is global: every part of the program has to respect the same order."
    const tGl = cue('global'), BX = 1360, bys = [300, 500, 700];
    const parts = bys.map((y, i) => { const b = partBox(root, BX, y, 560, 120, 'a part of the program'); fadeIn(tl, b, tGl + 0.1 + i * 0.15, 0.6, 14); return b; });
    const links = bys.map((y, i) => LX.line(tl, svg, BX - 284, y, COLX + 60, y, { at: tGl + 2.6 + i * 0.12, dur: 0.6, stroke: alpha(C.dim, 0.6), width: 2, head: 0 }));
    const glob = LX.note(tl, root, BX, 800, 'global: every part must respect it', tGl + 2.0, null);
    // "This paper does something else.": all of that leaves
    const tI = cue('idea') + 0.9;                 // late enough that the stage is not empty long before "It puts no restriction"
    col.out(tI, 0.4);
    for (const e of [svg, ord, glob, ...parts]) fadeOut(tl, e, tI, 0.4);
    // "It puts no restriction on how a thread uses the locks it has. It may take any of them, at any time, in any
    // order."
    const tUse = cue('use'), LXc = 520, RXc = 1400;
    const h1 = LX.cserif(root, LXc, 360, 'how a thread uses its locks', 52);
    fadeIn(tl, h1, tUse - 0.1, 0.7, 16);
    const g1 = LX.note(tl, root, LXc, 460, 'no restriction:', tUse + 0.4, null, { color: C.good });
    const g2 = LX.note(tl, root, LXc, 506, 'any lock, any time, any order', tUse + 4.8, null, { color: C.good });
    // "Instead, it restricts how references to locks spread."
    const tSp = cue('spread');
    for (const e of [h1, g1, g2]) tl.to(e, { o: 0.45 }, tSp + 0.6, 0.5);
    const h2 = LX.cserif(root, RXc, 360, 'how references spread', 52);
    fadeIn(tl, h2, tSp + 1.3, 0.7, 16);
    LX.note(tl, root, RXc, 460, 'restricted', tSp + 0.8, null, { color: C.ink });
  });

  // ============================================ rule_a ========================================================
  scene('rule_a', ({ tl, root, cue }) => {
    // "Draw the threads, the locks, and a line for every reference: from a thread to a lock, or from a lock's
    // contents to another lock."
    const p = new LX.Picture(tl, root);
    p.thread('T1', 500, 300, { name: 'T₁' }).thread('T2', 900, 300, { name: 'T₂' }).thread('T3', 1300, 300, { name: 'T₃' }).thread('T4', 1420, 560, { name: 'T₄' })
      .lock('l1', 700, 300, { name: 'ℓ₁' }).lock('l2', 1100, 300, { name: 'ℓ₂' })
      .lock('l3', 500, 540, { name: 'ℓ₃', contents: [{ ref: true }], nameSide: 'left' }).lock('l4', 1000, 560, { name: 'ℓ₄' })
      .ref('T1-l1', 'T1', 'l1').ref('T2-l1', 'T2', 'l1').ref('T2-l2', 'T2', 'l2').ref('T3-l2', 'T3', 'l2')
      .ref('T1-l3', 'T1', 'l3').ref('T4-l4', 'T4', 'l4').ref('l3-l4', 'l3/0', 'l4');
    const tD = cue('draw');
    p.show(['T1', 'T2', 'T3', 'T4'], tD + 0.3, { stagger: 0.15 });                 // "the threads"
    p.show(['l1', 'l2', 'l3', 'l4'], tD + 1.3, { stagger: 0.15 });                 // "the locks"
    p.show(['T1-l1', 'T2-l1', 'T2-l2', 'T3-l2', 'T1-l3', 'T4-l4'], tD + 2.4, { stagger: 0.35 });   // "a line for every reference"
    p.pulse('l3/0', tD + 6.6);                                                      // "a lock's contents"
    p.show('l3-l4', tD + 7.4, { dur: 0.8 });                                        // "to another lock"
    // "That picture must never contain a cycle."
    const no = LX.note(tl, root, 960, 172, 'no cycle', cue('no') + 1.2, null, { color: C.good });
    // "The paper calls the picture the sharing topology."
    const nm = box(root, 1290, 134, Object.assign(LX.SERIF(56), { whiteSpace: 'pre', width: '520px', textAlign: 'right' }), 'the sharing topology');
    fadeIn(tl, nm, cue('name') + 1.6, 0.7, 16);
    // c1, c2, c3: the picture dims; three small pictures in red, each struck
    const tC1 = cue('c1');
    p.fade(0.4, tC1 - 0.1); tl.to(no, { o: 0.4 }, tC1 - 0.1, 0.5); tl.to(nm, { o: 0.4 }, tC1 - 0.1, 0.5);
    const SY = 720;
    const small = [];
    const d = LX.double(tl, root, 380, SY, { k: 0.4 });
    d.color('a', C.bad, 0, 0); d.color('b', C.bad, 0, 0);
    const s4 = LX.square(tl, root, 960, SY, { k: 0.3 });
    for (const id of ['T1-l1', 'T1-l2', 'T2-l1', 'T2-l2']) s4.color(id, C.bad, 0, 0);
    const r3 = LX.ring(tl, root, 1540, SY, { radius: 84, r: 15, size: 28, line: 2.5, names: false });
    for (const id of LX.ringIds(3).refs) r3.color(id, C.bad, 0, 0);
    // the grey strike, drawn diagonally across a small picture (a horizontal bar would run along its lines and
    // read as one more line); the picture fades as it is struck
    const ssvg = LX.svg(root);
    const strikeAcross = (pic, at, w, h) => { const b = pic.bounds(); LX.strikeLine(tl, ssvg, b.cx - w / 2, b.cy + h / 2, b.cx + w / 2, b.cy - h / 2, at); pic.fade(0.55, at, 0.4); };
    const lab = (cx, lines, at) => lines.forEach((t, i) => LX.note(tl, root, cx, 826 + i * 38, t, at + i * 0.1, null));
    // "a thread never holds two references to the same lock"
    d.showAll(tC1 + 0.2, { stagger: 0.08 });
    lab(380, ['two references', 'to one lock'], cue('c1') + 6.3);
    strikeAcross(d, cue('c1') + 7.7, 300, 100);
    // "two threads never share more than one lock"
    const tC2 = cue('c2');
    s4.showAll(tC2 + 0.0, { stagger: 0.05 });
    lab(960, ['two threads sharing', 'two locks'], tC2 + 0.9);
    strikeAcross(s4, tC2 + 2.3, 340, 140);
    // "And it rules out the longer rings as well."
    const tC3 = cue('c3');
    r3.showAll(tC3 + 0.0, { stagger: 0.04 });
    lab(1540, ['a longer ring'], tC3 + 1.1);
    strikeAcross(r3, tC3 + 1.9, 220, 160);
  });
})();

// ==== src/scenes/c.js ====
// Why the rule works, and the operations that keep it: rule_b, rule_c, ops_a, ops_b, cool_free. Built with LX
// (common.js). Times inside a segment that are not cues are the words they belong to (from build/audio/<id>.json).
'use strict';
(function () {
  const { C, E, scene } = Film;
  const { CX, RAIL } = LX;
  const sub2 = ['₂', null, LX.SERIF(34)];             // a subscript inside a small caps label (the label font lacks it)

  // ============================================ rule_b ========================================================
  // "Why is that enough?": a waiting thread, the walk along the lines, and where it ends.
  scene('rule_b', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    const p = new LX.Picture(tl, root);
    p.thread('T1', 360, 480, { name: 'T₁' }).lock('l1', 660, 480, { name: 'ℓ₁' })
      .thread('T2', 960, 480, { name: 'T₂' }).lock('l2', 1260, 480, { name: 'ℓ₂' })
      .thread('T3', 1560, 480, { name: 'T₃' })
      .lock('l3', 960, 720, { name: 'ℓ₃' }).thread('T4', 1260, 720, { name: 'T₄' })
      .ref('a', 'T1', 'l1').ref('b', 'T2', 'l1').ref('c', 'T2', 'l2').ref('d', 'T3', 'l2')
      .ref('e', 'T2', 'l3').ref('f', 'T4', 'l3');
    // "Why is that enough?": the whole picture
    p.show(['T1', 'l1', 'T2', 'l2', 'T3'], cue('why') - 0.2, { stagger: 0.1 });
    p.show(['a', 'b', 'c', 'd'], cue('why') + 0.2, { stagger: 0.1 });
    p.show(['l3', 'T4'], cue('why') + 0.5, { stagger: 0.1 });
    p.show(['e', 'f'], cue('why') + 0.75, { stagger: 0.1 });

    // "Suppose a thread is waiting to acquire a lock."
    p.waiting('a', 3.3);
    p.label('T1', 'waiting', 3.4, { side: 'above' });
    // "Some other thread has acquired that lock.": the label sits higher than the nodes, so it clears ℓ₁ and T₂
    p.open('b', 6.4);
    const acq = p.label('b', ['acquired by T', sub2], 6.55, { size: 30, dy: -40, out: cue('next') + 2.4 });
    // "That thread is either able to run, or it is waiting too, for another lock." (its label to the right of
    // the top, clear of the arc drawn later between ℓ₁ and T₂)
    p.waiting('c', 10.9);
    p.label('T2', 'waiting', 11.0, { side: 'above', dx: 110 });
    p.open('d', 11.9);

    // "Follow the chain: thread, lock, thread, lock.": one step with each word
    p.pulse('T1', 14.55);
    const w = p.walk(['T1', 'l1', 'T2', 'l2', 'T3'], 14.85, { times: [14.85, 15.65, 16.45, 17.25], dur: 0.7, color: C.ink });   // ink: a dim band is lost over the amber and dashed lines

    // "And it never turns straight back": at T₂ an arrow that turns back toward ℓ₁, struck
    const back = LX.line(tl, svg, 925, 446, 694, 444, { at: 21.15, dur: 0.6, bend: 120, stroke: C.dim, width: 3 });
    const sb = LX.strikeLine(tl, svg, 794, 356, 828, 414, 22.2);
    const nsb = LX.note(tl, root, 810, 290, 'never straight back', 22.35, null);
    const tEnd = cue('end');
    back.hide(tEnd - 0.3); tl.to(sb, { o: 0 }, tEnd - 0.3, 0.3); fadeOut(tl, nsb, tEnd - 0.3, 0.3);

    // "In a picture without cycles, such a walk cannot go on forever."
    LX.note(tl, root, CX, 830, 'no cycle: the walk ends', 27.95, null, { color: C.good });
    // "It must end at a thread that can run."
    p.can('T3', 33.2);
    p.label('T3', 'can run', 33.55, { color: C.good, gap: 26 });
    // "So whoever is waiting is waiting, in the end, on something that can move.": green back along the trail
    p.walk(['T3', 'l2', 'T2', 'l1', 'T1'], 35.0, { step: 0.55, dur: 0.5, color: C.good, out: 37.6 });
    p.pulse('T3', 38.25);
    void w; void acq;
  });

  // ============================================ rule_c ========================================================
  // Locks are higher-order: lines from locks to locks; and handing a lock on.
  scene('rule_c', ({ tl, root, cue }) => {
    const p = new LX.Picture(tl, root);
    p.lock('L', 620, 480, { size: 180 }).chip('L/v', 'L', '42').chip('L/r', 'L', { ref: true })
      .lock('M', 1240, 480).ref('lm', 'L/r', 'M');
    // "Locks here are higher-order: a lock can hold any value, including references to other locks."
    p.show('L', cue('ho') - 0.2);
    p.show('L/v', 3.8); p.show('L/r', 5.55);
    const l1 = LX.cline(root, CX, 640, ['a lock holds any value,', ' also references to locks'], LX.LABEL(32));
    fadeIn(tl, l1.parts[0], 3.9, 0.5, 10); fadeIn(tl, l1.parts[1], 5.65, 0.5, 10);
    // "That is why the picture has lines from locks to locks."
    p.show('M', cue('edge') - 0.1);
    p.show('lm', 8.75, { dur: 0.7 });
    tl.to(l1.root, { o: 0.45 }, 9.1, 0.5);
    const l2 = LX.note(tl, root, CX, 700, 'a line from lock to lock', 9.2, null);
    // "The rule covers them too: no cycles."
    tl.to(l2, { o: 0.45 }, 13.2, 0.5);
    const l3 = LX.note(tl, root, CX, 760, 'no cycles, as before', 13.3, null, { color: C.good });
    const tPass = cue('pass');
    p.out(tPass - 0.35, 0.35);
    for (const e of [l1.root, l2, l3]) fadeOut(tl, e, tPass - 0.35, 0.35);

    // "It is also how a lock is handed from one thread to another."
    const q = new LX.Picture(tl, root);
    q.thread('T1', 560, 400, { name: 'T₁' }).lock('s', 960, 400, { name: 's' }).thread('T2', 1360, 400, { name: 'T₂' })
      .lock('l', 560, 700, { name: 'ℓ' })
      .ref('a', 'T1', 's').ref('b', 'T2', 's').ref('c', 'T1', 'l');
    q.show(['T1', 's', 'T2'], tPass + 0.1, { stagger: 0.12 });
    q.show(['a', 'b'], tPass + 0.5, { stagger: 0.12 });
    q.show('l', 15.75); q.show('c', 16.0);
    // "The first thread puts its reference into a lock that both threads share.": the end slides from T₁ to s
    q.retarget('c', 'from', 's', 19.55, { dur: 1.0 });
    // "The second thread takes it out.": on to T₂, and ℓ glides under it
    q.retarget('c', 'from', 'T2', 24.1, { dur: 1.0 });
    q.move('l', 1360, 700, 24.3, { dur: 1.0 });
    // "Each time, one end of a line moves along another line, and no cycle appears."
    q.pulse('c', 27.45);
    LX.note(tl, root, CX, 800, 'no cycle at any moment', 29.3, null, { color: C.good });
  });

  // ============================================ ops_a =========================================================
  // new, acquire, release; references are linear.
  scene('ops_a', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    const ops = ['new()', 'acquire(ℓ)', 'release(ℓ, v)'].map((s, i) => LX.code(tl, root, RAIL, 260 + i * 130, 56, [s]));
    const p = new LX.Picture(tl, root);
    p.thread('T', 1160, 480).lock('L', 1560, 480, { name: 'ℓ', nameSide: 'above' }).ref('l', 'T', 'L')
      .chip('v', 'L', 'v');

    // "New creates a lock. In the picture: a new square, with a single line to the thread that made it. No cycle."
    ops[0].show(cue('new') - 0.2);
    p.show('T', 5.9);
    p.show('L', 7.2);
    p.show('l', 8.5, { dur: 0.7 });
    const tk = LX.tick(tl, svg, 1238, 624, 44, 10.8);
    const nc = LX.note(tl, root, 1280, 605, 'no cycle', 10.9, null, { align: 'left' });
    tk.hide(cue('acq') - 0.2); fadeOut(tl, nc, cue('acq') - 0.2, 0.3);
    // "Acquire takes the lock, and hands over its contents."
    ops[1].show(cue('acq') - 0.2);
    p.show('v', cue('acq') + 0.1);
    p.open('l', 13.2);
    p.moveChip('v', 'T', 13.85);
    // "Release puts contents back, and gives the lock up."
    ops[2].show(cue('rel') - 0.2);
    p.moveChip('v', 'home', 16.4);
    p.close('l', 17.75);
    // "Neither creates a reference. Contents only move along a line that is already there."
    const nn = LX.note(tl, root, 1360, 605, 'no new line', 20.2, cue('lin') - 0.3);
    p.pulse('l', 23.1, { dur: 0.9 });

    // "And references are linear. A reference cannot be copied,": a sketched second line, struck
    const tLin = cue('lin');
    ops.forEach(o => o.dim('all', 0.4, tLin - 0.1));
    p.ref('copy', 'T', 'L', { dash: true, bend: -60 });
    p.show('copy', 27.15, { dur: 0.6 });
    p.strike('copy', 27.9);
    const cc = LX.note(tl, root, 1360, 640, 'a reference cannot be copied', 28.0, null);
    // "and it cannot be silently forgotten.": the real line fades for a moment, struck, and comes back
    const tF = cue('forget');
    p.hide('copy', tF - 0.15, 0.3); fadeOut(tl, cc, tF - 0.15, 0.3);
    const lg = p.item('l').g;
    tl.to(lg, { o: 0.3 }, 29.6, 0.4);
    const fb = p.strike('l', 29.9, { out: 30.95 });
    tl.to(lg, { o: 1 }, 30.95, 0.4);
    const nf = LX.note(tl, root, 1360, 605, 'nor silently forgotten', 30.0, cue('rust') - 0.2);
    // "So the second reference of the Rust program cannot be made."
    const rc = LX.code(tl, root, RAIL, 800, 40, ['let m2 = m1.clone();']);
    rc.show(31.7);
    rc.strike(0, 33.75);
    LX.note(tl, root, RAIL + rc.width + 60, 800 + rc.lh / 2 - 19, "the Rust program's second reference", 32.45, null, { align: 'left' });
    void nn; void fb; void nf;
  });

  // ============================================ ops_b =========================================================
  // fork: a new circle joined through exactly one lock.
  scene('ops_b', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    const p = new LX.Picture(tl, root);
    p.thread('P', 900, 420).lock('l', 1200, 420, { name: 'ℓ' }).lock('l2', 900, 700, { name: 'ℓ₂' })
      .thread('K', 1500, 420)
      .ref('pl', 'P', 'l').ref('pl2', 'P', 'l2').ref('kl', 'K', 'l');
    // "So how do two threads ever share a lock?": the parent with its two locks (the labels beside the circles:
    // under them run the lines to ℓ₂)
    const t0 = cue('fork');
    p.show(['P', 'l', 'l2'], t0 + 0.3, { stagger: 0.12 });
    p.show(['pl', 'pl2'], t0 + 0.65, { stagger: 0.12 });
    p.label('P', 'parent', t0 + 0.9, { side: 'left' });
    // "With fork."
    const code = LX.code(tl, root, RAIL, 220, 56, ['fork(ℓ, λℓ. …)']);
    code.show(cue('f') - 0.15);
    // "Fork starts a new thread, and gives it one new reference to one lock of the parent."
    p.show('K', 5.95);
    p.label('K', 'child', 6.1, { side: 'right' });
    p.show('kl', 7.6, { dur: 0.7 });
    const one = p.label('kl', 'one new reference', 8.1, { dy: -46, out: cue('pic') + 1.9 });
    // "In the picture: a new circle, joined to its parent through exactly one lock."
    const yB = 800;
    LX.note(tl, root, 1200, yB, 'joined through exactly one lock', 13.0, cue('give') - 0.2);
    p.pulse('l', 15.1);
    // "Anything else the child gets, the parent gives up.": the line to ℓ₂ slides over by way of ℓ
    p.retarget('pl2', 'from', 'K', cue('give') + 0.2, { via: ['l'], dur: 1.5 });
    p.move('l2', 1500, 700, cue('give') + 0.2, { dur: 1.5 });
    LX.note(tl, root, 1200, yB, 'handed over, not shared', 18.3, cue('tree') + 2.1);
    // "A new circle joined in one place can never close a cycle."
    const tk = LX.tick(tl, svg, 1080, yB + 20, 44, 22.2);
    const nc = LX.note(tl, root, 1122, yB, 'no cycle', 22.3, cue('two') + 0.7, { align: 'left', color: C.good });
    tk.hide(cue('two') + 0.7);
    // "If fork could share two locks at once, parent and child would be joined twice, and that is a cycle."
    p.ref('g', 'P', 'l2', { dash: true });
    p.move('l2', 1200, 700, 25.0, { dur: 0.8 });
    p.show('g', 25.5, { dur: 0.6 });
    p.cycle(['pl', 'kl', 'pl2', 'g'], 28.3, { out: 30.7 });
    LX.note(tl, root, 1200, yB, 'two shared locks: a cycle', 28.9, 30.6, { color: C.bad });
    // then the picture returns to the state after "give"
    p.hide('g', 30.7, 0.4);
    p.move('l2', 1500, 700, 30.75, { dur: 0.8 });
    // "So: one shared lock for each fork."
    LX.note(tl, root, 1200, yB, 'one shared lock for each fork', 31.55, null, { color: C.ink });
    void one; void nc;
  });

  // ============================================ cool_free =====================================================
  // No lock order: a thread takes its locks in any order. And the rule is checked locally: a frame (what the type
  // checker sees) moves over a larger picture, which is a tree as a whole.
  scene('cool_free', ({ tl, root, cue }) => {
    const p = new LX.Picture(tl, root);
    const D = 300, at = { up: [0, -D], right: [D, 0], down: [0, D], left: [-D, 0] };
    p.thread('T', 960, 480);
    for (const k in at) p.lock(k, 960 + at[k][0], 480 + at[k][1]).ref('r' + k, 'T', k);
    // "Notice what is missing."
    p.show('T', cue('notice') - 0.2);
    p.show(['up', 'right', 'down', 'left'], cue('notice') + 0.1, { stagger: 0.1 });
    p.show(['rup', 'rright', 'rdown', 'rleft'], cue('notice') + 0.35, { stagger: 0.1 });
    // "There is no lock order, and no rule about when a thread may acquire."
    const lo = LX.note(tl, root, RAIL, 170, 'lock order', 2.9, null, { align: 'left', color: C.ink });
    LX.strikeEl(tl, lo, 3.45);
    // "A thread may take any lock it holds, in any order, while holding any others.": right, up, left, down
    ['right', 'up', 'left', 'down'].forEach((k, i) => p.open('r' + k, 7.95 + i * 0.65));
    ['up', 'down', 'right', 'left'].forEach((k, i) => p.close('r' + k, 10.95 + i * 0.4));
    const an = LX.note(tl, root, RAIL, 230, 'any lock, in any order', 9.45, null, { align: 'left', color: C.good });

    // "And notice how the rule is enforced.": all of that leaves; a larger picture, a tree, drawn at 45 %
    const tLocal = cue('local'), tL1 = cue('l1'), tL2 = cue('l2'), tGlobal = cue('global');
    p.out(tLocal - 0.25, 0.4); fadeOut(tl, lo, tLocal - 0.25, 0.35); fadeOut(tl, an, tLocal - 0.25, 0.35);
    const NODES = [['thread', 'Ta', 380, 420], ['lock', 'La', 640, 380], ['thread', 'Tb', 900, 360], ['lock', 'Lb', 1180, 380],
      ['thread', 'Tc', 1460, 420], ['lock', 'Lc', 960, 600], ['thread', 'Td', 680, 730], ['thread', 'Te', 1240, 730],
      ['lock', 'Ld', 1700, 640], ['lock', 'Le', 380, 680]];
    const EDGES = [['Ta', 'La'], ['Tb', 'La'], ['Tb', 'Lb'], ['Tc', 'Lb'], ['Tb', 'Lc'], ['Td', 'Lc'], ['Te', 'Lc'], ['Tc', 'Ld'], ['Ta', 'Le']];
    // two copies of it: one at 45 %, and one at full strength that is seen only inside the frame
    const lay = box(root, 0, 0, { width: '1920px', height: '1080px' });
    const clip = box(root, 0, 0, { width: '1920px', height: '1080px' });
    const mk = parent => {
      const q = new LX.Picture(tl, parent);
      for (const [k, id, x, y] of NODES) q[k](id, x, y);
      for (const [a, b] of EDGES) q.ref(a + b, a, b);
      q.showAll(tLocal + 0.25, { stagger: 0.06 });
      return q;
    };
    const dimP = mk(lay); mk(clip);
    tl.set(lay, { o: 0.45 }, 0);
    // the frame: a rounded ink rectangle 300 x 260, which stops at Tb, then Ta, then Tc
    const STOPS = [[900, 360], [380, 420], [1460, 420]], FW = 300, FH = 260;
    const frame = box(root, 0, 0, { width: FW + 'px', height: FH + 'px', borderRadius: '26px', boxShadow: `inset 0 0 0 3px ${C.ink}` });
    const place = v => {
      const i = Math.min(Math.floor(v), STOPS.length - 2), u = v - i;
      const x = STOPS[i][0] + (STOPS[i + 1][0] - STOPS[i][0]) * u, y = STOPS[i][1] + (STOPS[i + 1][1] - STOPS[i][1]) * u;
      return [x - FW / 2, y - FH / 2];
    };
    tl.custom(frame, 'fr', (e, v) => {
      const [x, y] = place(v);
      e.style.left = x.toFixed(1) + 'px'; e.style.top = y.toFixed(1) + 'px';
      clip.style.clipPath = `inset(${y.toFixed(1)}px ${(1920 - x - FW).toFixed(1)}px ${(1080 - y - FH).toFixed(1)}px ${x.toFixed(1)}px round 26px)`;
    }, 0);
    tl.set(frame, { fr: 0 }, 0);
    // "The type checker never looks at the whole picture. It checks one operation at a time, in one thread at a time."
    tl.set(frame, { o: 0, s: 1.25 }, 0); tl.set(clip, { o: 0 }, 0);
    tl.to(frame, { o: 1, s: 1 }, 15.3, 0.7, E.out5); tl.to(clip, { o: 1 }, 15.3, 0.6);
    LX.note(tl, root, RAIL, 160, 'the type checker sees one operation at a time', 18.4, null, { align: 'left' });
    // the answers of the two checks: under the picture, with a green tick
    const svg = LX.svg(root);
    const check = (text, w, atL, atT, out) => {
      const x0 = CX - w / 2 + 30;
      const n = LX.note(tl, root, x0, 846, text, atL, out, { align: 'left' });
      const tk = LX.tick(tl, svg, x0 - 40, 864, 40, atT);
      tk.hide(out);
      return n;
    };
    // "Is a reference being copied, or forgotten?"
    check('no reference copied or forgotten', 760, 22.55, 24.5, 25.25);
    tl.to(frame, { fr: 1 }, 25.25, 0.9, E.io);                  // the frame glides to another thread
    // "Does this fork share more than one lock?"
    check('one shared lock for each fork', 690, 25.55, 27.5, 28.15);
    tl.to(frame, { fr: 2 }, 27.7, 0.9, E.io);                   // and to a third
    // "Yet together, these local checks keep a property of the whole program: no cycle, anywhere."
    tl.to(frame, { o: 0 }, 28.9, 0.5); tl.to(clip, { o: 0 }, 28.9, 0.5);
    tl.to(lay, { o: 1 }, 28.9, 0.6);
    LX.note(tl, root, CX, 846, 'local checks, a property of the whole: no cycle', 30.4, null, { color: C.good });
    void dimP;
  });
})();

// ==== src/scenes/d.js ====
// Who frees a lock (own_a, own_b, own_c) and the first programs (prog_a), built with LX (common.js).
'use strict';
(function () {
  const { C, E, scene } = Film;
  const { CX, RAIL } = LX;

  // ---- local helpers ----------------------------------------------------------------------------------------
  // the width of a small caps label (an estimate, for placing it beside a line)
  const labelW = (text, size) => [...text].length * size * 0.86;
  // a label beside the line `refId` (which joins nodes a and b), on the side `up` (the side facing up; for a
  // vertical line, the right), at a distance that keeps the whole label clear of the line
  function lineLabel(p, refId, a, b, text, at, { size = 32, color = C.dim, out = null, flip = false, gap = 16 } = {}) {
    const A = p.pos(a), B = p.pos(b);
    const L = Math.hypot(B.x - A.x, B.y - A.y) || 1, ux = (B.x - A.x) / L, uy = (B.y - A.y) / L;
    let nx = uy, ny = -ux;
    if (ny > 0.001 || (Math.abs(ny) <= 0.001 && nx < 0)) { nx = -nx; ny = -ny; }
    if (flip) { nx = -nx; ny = -ny; }
    const plain = Array.isArray(text) ? text.map(q => (Array.isArray(q) ? q[0] : q)).join('') : text;
    const hw = labelW(plain, size) / 2, hh = size * 0.6;
    const d = hw * Math.abs(nx) + hh * Math.abs(ny) + gap;
    return p.label(refId, text, at, { side: 'center', dx: nx * d, dy: ny * d, size, color, out });
  }
  // an element that is simply there from the start of a scene (for what continues from the scene before)
  const already = (tl, e) => { tl.set(e, { o: 1, y: 0 }, 0); return e; };
  // ---- the picture of own_a and own_b -----------------------------------------------------------------------
  // a lock ℓ at the centre holding a reference to another lock, three threads around it
  function ownPicture(tl, root) {
    const p = new LX.Picture(tl, root);
    p.thread('T1', 560, 300, { name: 'T₁' }).thread('T2', 1360, 300, { name: 'T₂' }).thread('T3', 960, 800, { name: 'T₃' })
      .lock('L', 960, 480, { name: 'ℓ', contents: [{ ref: true }] })
      .ref('r1', 'T1', 'L').ref('r2', 'T2', 'L').ref('r3', 'T3', 'L');
    return p;
  }
  const VERDICT = { x: 560, y: 620 };        // where the picture's verdicts go: the empty lower left

  // ============================================ own_a ==========================================================
  scene('own_a', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    const p = ownPicture(tl, root);
    // "That takes care of locking. What about getting rid of a lock?"
    const t0 = cue('free') - 0.25;
    p.show('L', t0); p.show(['T1', 'T2', 'T3'], t0 + 0.3, { stagger: 0.12 });
    p.show(['r1', 'r2', 'r3'], t0 + 0.75, { stagger: 0.12 });

    // "A thread cannot simply drop a lock it has acquired: everyone else would wait forever."
    const tO = cue('open');
    p.open('r1', tO + 0.15);
    p.drop('r1', tO + 2.45);                                  // after "acquired"
    const tW = tO + 3.1;                                     // "everyone else would wait forever"
    p.waiting('r2', tW, { out: cue('closed') - 0.5 }); p.waiting('r3', tW + 0.1, { out: cue('closed') - 0.5 });
    lineLabel(p, 'r2', 'T2', 'L', 'waiting', tW + 0.2, { out: cue('closed') - 0.6 });
    lineLabel(p, 'r3', 'T3', 'L', 'waiting', tW + 0.3, { out: cue('closed') - 0.6 });
    LX.note(tl, root, VERDICT.x, VERDICT.y, 'a deadlock', tO + 4.1, cue('closed') - 0.6, { color: C.bad });
    // the picture is restored: T₁'s line again, closed
    p.close('r1', cue('closed') - 0.6); p.show('r1', cue('closed') - 0.35);

    // "If every thread did that, the lock would be gone, and its contents with it."
    const tA = cue('all');
    p.drop('r1', tA + 0.3); p.drop('r2', tA + 0.75); p.drop('r3', tA + 1.2);
    p.dim(['T1', 'T2', 'T3'], 0.35, tA + 1.8);
    // "And the contents may be something that must not be thrown away: another lock, say."
    const tL = cue('lin');
    p.pulse('L/0', tL + 0.2); p.pulse('L/0', tL + 3.5);
    LX.note(tl, root, VERDICT.x, VERDICT.y, 'leaked, with its contents', tL + 0.5, cue('stuck') - 0.2, { color: C.bad });
    // "So dropping is wrong either way.": the picture is restored
    const tS = cue('stuck');
    p.dim(['T1', 'T2', 'T3'], 1, tS);
    p.show(['r1', 'r2', 'r3'], tS + 0.15, { stagger: 0.15 });

    // "The way out: among the references to a lock, exactly one is the owner. The others are clients."
    const tOw = cue('owner');
    ['r1', 'r2', 'r3'].forEach(r => p.pulse(r, tOw + 1.9));          // "among the references"
    p.owner('r1', tOw + 3.75);                                       // "exactly one"
    lineLabel(p, 'r1', 'T1', 'L', 'owner', tOw + 4.5, { gap: 6 });
    lineLabel(p, 'r2', 'T2', 'L', 'client', tOw + 6.6, { gap: 4 });
    lineLabel(p, 'r3', 'T3', 'L', 'client', tOw + 6.7);

    // "A client may drop its reference."
    const tC = cue('cl');
    p.drop('r2', tC + 0.8);
    const tk = LX.tick(tl, svg, 1445, 300, 44, tC + 1.3);
    const may = p.label('T2', 'a client may drop', tC + 1.4, { side: 'below' });
    // "The owner may not. It must wait."
    const tOwn = cue('ow');
    p.pulse('r1', tOwn + 0.15); p.pulse('r1', tOwn + 1.1);
    LX.note(tl, root, VERDICT.x, VERDICT.y, 'the owner must wait', tOwn + 1.5, null, { color: C.ink });
    // what own_b does not continue leaves at the end: T₂, which has dropped its reference, and its tick
    const tEnd = cue('ow') + 2.75;
    tk.hide(tEnd); tl.to(may, { o: 0 }, tEnd, 0.3); p.hide('T2', tEnd);
    return { keep: true };                                           // own_b goes on from this picture
  });

  // ============================================ own_b ==========================================================
  scene('own_b', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    const p = ownPicture(tl, root);
    // the picture exactly as own_a left it
    p.show(['L', 'T1', 'T3', 'L/0'], 0, { dur: 0 });
    p.show(['r1', 'r3'], 0, { dur: 0 }); p.owner('r1', 0, { dur: 0 });
    already(tl, lineLabel(p, 'r1', 'T1', 'L', 'owner', 0, { gap: 6 }));
    already(tl, lineLabel(p, 'r3', 'T3', 'L', 'client', 0));
    const must = already(tl, LX.note(tl, root, VERDICT.x, VERDICT.y, 'the owner must wait', 0, null, { color: C.ink }));
    fadeOut(tl, must, cue('wait') - 0.15, 0.35);

    // "The wait operation blocks until every client has dropped its reference."
    const tW = cue('wait');
    const wl = LX.cline(root, 560, 186, [['wait(', null], ['ℓ', C.bind], [')', null]], LX.MONO(40)).root;
    fadeIn(tl, wl, tW + 0.1, 0.5, 12);
    const blk = p.label('T1', 'blocked', tW + 0.5, { side: 'left', out: cue('ret') - 0.3 });
    p.drop('r3', tW + 3.05);                                     // "has dropped"
    p.hide('T3', tW + 3.9, 0.5);
    // "Then it removes the lock, and returns its contents to the owner."
    const tR = cue('ret');
    p.gone('L', tR + 1.1, { chips: false, lines: false });
    p.moveChip('L/0', 'T1', tR + 1.9, { dur: 1.0 });
    p.drop('r1', tR + 1.9, { dur: 1.0 });
    fadeOut(tl, wl, tR + 3.3, 0.35);
    // "Nothing is lost."
    const tN = cue('nothing');
    const tk = LX.tick(tl, svg, 790, 480, 44, tN + 0.05);
    const lost = LX.note(tl, root, 830, 462, 'nothing is lost', tN + 0.15, null, { align: 'left', color: C.ink });

    // "The type of a reference records two facts, as two bits.": the paper's lock type, its bits still variables
    const tT = cue('type');
    p.out(tT - 0.3); tk.hide(tT - 0.3); fadeOut(tl, lost, tT - 0.3, 0.3);
    const TS = 96, TY = 250;
    const head = LX.note(tl, root, CX, 168, 'the type of a reference', tT + 0.1, cue('rules') - 0.2);
    const ty = LX.lockType(tl, root, CX, TY, { size: TS, a: 'a', b: 'b', align: 'center' });
    ty.show(tT + 0.15);
    ty.pulse('a', tT + 3.1); ty.pulse('b', tT + 3.3);                         // "as two bits"
    // where the two bits are on the stage (the middle of each digit), and where their legends go
    const bitMid = (y, S, bs, lower) => { const m = y + 0.64 * S, g = Math.max(0.125 * S, 5); return lower ? m + g + 0.345 * bs : m - g - 0.345 * bs; };
    const LGX = ty.x + ty.width + 46, LGS = 30;
    const svgT = LX.svg(root);
    // a pill at the right of a bit, joined to it by a short dim line; it flips with the bit
    const pillAt = (lower, value, at) => {
      const yM = bitMid(TY, TS, ty.bs, lower);
      const q = LX.pill(root, 0, yM - 24, value, { tl });
      q.el.style.left = (LGX + 70) + 'px'; q.show(at);
      const ln = LX.line(tl, svgT, LGX - 22, yM, LGX + 58, yM, { at: at - 0.05, dur: 0.3, stroke: C.dim, width: 2, head: 0 });
      return { q, ln };
    };
    // "The upper bit is one for the owner, and zero for a client."
    const t1 = cue('b1');
    ty.pulse('a', t1 + 0.3);
    ty.set({ a: 1 }, t1 + 0.9);
    const pu = pillAt(false, 'owner', t1 + 1.4);
    ty.set({ a: 0 }, t1 + 2.3); pu.q.set('client', t1 + 2.45);
    const o1 = cue('b2') - 0.45;
    ty.set({ a: 'a' }, o1); tl.to(pu.q.el, { o: 0 }, o1, 0.3); pu.ln.hide(o1);
    const legU = LX.note(tl, root, LGX, bitMid(TY, TS, ty.bs, false) - LGS * 0.6, '1: owner · 0: client', o1 + 0.3, null, { align: 'left', size: LGS });
    // "The lower bit is one if the lock is opened, meaning acquired through this reference, and zero if it is closed."
    const t2 = cue('b2');
    ty.pulse('b', t2 + 0.15);
    ty.set({ b: 1 }, t2 + 0.9);
    const pl = pillAt(true, 'opened', t2 + 1.9);
    const ol = LX.note(tl, root, CX, 430, 'opened: acquired through this reference', t2 + 3.0, cue('rules') - 0.2);
    ty.set({ b: 0 }, t2 + 5.15); pl.q.set('closed', t2 + 5.3);
    const o2 = cue('rules') - 0.35;
    ty.set({ b: 'b' }, o2); tl.to(pl.q.el, { o: 0 }, o2, 0.3); pl.ln.hide(o2);
    const legL = LX.note(tl, root, LGX, bitMid(TY, TS, ty.bs, true) - LGS * 0.6,
      [['1: opened', C.pat], ' · 0: closed'], o2 + 0.3, null, { align: 'left', size: LGS });
    void head; void ol;

    // "With these two bits, every operation has a type.": the type goes up and shrinks, its legends with it; the
    // five typings appear at their words, and the bits each one speaks of pulse
    const tRu = cue('rules'), K = 64 / TS, ny = 150;
    const nx0 = CX - ty.width * K / 2 - 180;
    ty.to({ x: nx0 - ty.x, y: ny - TY, s: K }, tRu + 0.1, 0.8);
    const LGX2 = nx0 + ty.width * K + 40;
    tl.to(legU, { x: LGX2 - LGX, y: bitMid(ny, 64, ty.bs * K, false) - bitMid(TY, TS, ty.bs, false) }, tRu + 0.1, 0.8, E.io);
    tl.to(legL, { x: LGX2 - LGX, y: bitMid(ny, 64, ty.bs * K, true) - bitMid(TY, TS, ty.bs, true) }, tRu + 0.1, 0.8, E.io);
    const NAME_R = 520, COLON = 540, RS = 46, GX = 1330, rowY = i => 330 + 112 * i;
    function typing(i, name, parts, at) {
      const y = rowY(i);
      const n = box(root, NAME_R - 600, y, Object.assign(LX.MONO(RS), { width: '600px', textAlign: 'right', whiteSpace: 'pre' }), name);
      fadeIn(tl, n, at, 0.5, 12);
      return LX.typeLine(tl, root, COLON, y, RS, [': ', ...parts], { at: at + 0.1 });
    }
    // a dim gloss of two lines at most, each line at its own time, beside row i
    function gloss(i, lines) {
      const yMid = rowY(i) + RS * 0.64, lh = 36;
      lines.forEach(([t, at], k) => LX.note(tl, root, GX, yMid - (lines.length * lh) / 2 + k * lh - 2, t, at, null, { align: 'left', size: 28 }));
    }
    // "Acquire takes a reference whose lower bit is zero, and returns it with that bit set to one, together with
    // the contents."
    const a = cue('acq');
    const ac = typing(0, 'acquire', [{ a: 'a', b: 0 }, ' → ', { a: 'a', b: 1 }, ' × τ'], a - 0.1);
    ac.types[0].pulse('b', a + 2.4); ac.types[1].pulse('b', a + 5.05);
    gloss(0, [['closed to opened,', a + 5.1], ['with the contents', a + 6.3]]);
    // "Release takes a reference whose lower bit is one, and a value, and returns the reference with the bit back
    // at zero."
    const r = cue('rel');
    const rl = typing(1, 'release', [{ a: 'a', b: 1 }, ' × τ → ', { a: 'a', b: 0 }], r - 0.1);
    rl.types[0].pulse('b', r + 2.25); rl.types[1].pulse('b', r + 6.1);
    gloss(1, [['opened to closed', r + 6.1]]);
    // "Drop takes a closed client: zero, zero."
    const d = cue('drop');
    const dr = typing(2, 'drop', [{ a: 0, b: 0 }, ' → ()'], d - 0.1);
    gloss(2, [['a closed client', d + 1.0]]);
    dr.types[0].pulse('a', d + 2.3); dr.types[0].pulse('b', d + 2.6);
    // "The wait operation takes a closed owner: one, zero. It returns the contents."
    const w = cue('w');
    const wt = typing(3, 'wait', [{ a: 1, b: 0 }, ' → τ'], w + 0.1);
    gloss(3, [['a closed owner:', w + 1.7], ['the contents', w + 4.9]]);
    wt.types[0].pulse('a', w + 2.7); wt.types[0].pulse('b', w + 3.15);
    // "And new returns one, one: an opened owner. The lock is empty, and must be filled."
    const n = cue('new');
    const nw = typing(4, 'new', ['() → ', { a: 1, b: 1 }], n + 0.3);
    nw.types[0].pulse('a', n + 1.5); nw.types[0].pulse('b', n + 2.05);
    gloss(4, [['an opened owner,', n + 2.9], ['empty', n + 4.75]]);
  });

  // ============================================ own_c ==========================================================
  scene('own_c', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    // "Fork splits a reference in two, one for each thread, and it splits the bits as well.": fork's type at the
    // top; under it one lock type that splits into the parent's and the child's
    const tF = cue('fork');
    const ft = LX.typeLine(tl, root, CX, 160, 44, ['fork : ', { a: 'a₁+a₂', b: 'b₁+b₂' }, ' × (', { a: 'a₂', b: 'b₂' },
      ' → ()) → ', { a: 'a₁', b: 'b₁' }], { align: 'center', at: tF - 0.15 });
    const SY = 270, SS = 64, DX = 270;
    const orig = LX.lockType(tl, root, CX, SY, { size: SS, a: 'a₁+a₂', b: 'b₁+b₂', align: 'center' }).show(tF + 0.5);
    // the two halves come out of the original's place and move apart (they start apart enough not to print over
    // each other, and fade in as the original fades out)
    const L = LX.lockType(tl, root, CX - DX, SY, { size: SS, a: 'a₁', b: 'b₁', align: 'center' });
    const R = LX.lockType(tl, root, CX + DX, SY, { size: SS, a: 'a₂', b: 'b₂', align: 'center' });
    const tS = tF + 1.6;                                                         // "in two"
    orig.hide(tS, 0.25);
    for (const [t, sg] of [[L, 1], [R, -1]]) {
      tl.set(t.g, { x: sg * DX * 0.45, o: 0 }, 0);
      tl.to(t.g, { o: 1 }, tS + 0.3, 0.4); tl.to(t.g, { x: 0 }, tS, 0.8, E.io);
    }
    const pl = LX.note(tl, root, CX - DX, SY + 96, 'parent', tF + 2.6, null);  // "one for each thread"
    const cl = LX.note(tl, root, CX + DX, SY + 96, 'child', tF + 2.9, null);
    for (const t of [L, R]) { t.pulse('a', tF + 4.35); t.pulse('b', tF + 4.55); }   // "splits the bits"

    // the rows: a type, a drawn arrow, the two halves, the sum, a gloss
    const RS = 52, rowYs = [480, 600, 720], X0 = RAIL, AX0 = 430, AX1 = 520, HX = [550, 830], SUMX = 1120, GX = 1370;
    const rows = [];
    function frow(i, from, into, sum, gl, at, atArrow, atL, atR, atSum, which) {
      const y = rowYs[i];
      for (const r of rows) for (const e of r) tl.to(e, { o: 0.5 }, at - 0.15, 0.4);
      const s = LX.lockType(tl, root, X0, y, Object.assign({ size: RS }, from)).show(at);
      const ym = y + RS * 0.64;
      const ar = LX.line(tl, svg, AX0, ym, AX1, ym, { at: atArrow, dur: 0.4, stroke: C.dim });
      const h1 = LX.lockType(tl, root, HX[0], y, Object.assign({ size: RS }, into[0])).show(atL);
      const h2 = LX.lockType(tl, root, HX[1], y, Object.assign({ size: RS }, into[1])).show(atR);
      for (const t of [s, h1, h2]) t.pulse(which, atSum - 0.25);
      const sm = box(root, SUMX, ym - 36 * 0.65, Object.assign(LX.MONO(36), { whiteSpace: 'pre', color: C.dim }), sum);
      fadeIn(tl, sm, atSum, 0.5, 10);
      const g = gl.map(([t, tt], k) => LX.note(tl, root, GX, ym - (gl.length * 34) / 2 + k * 34 - 2, t, tt, null, { align: 'left', size: 28 }));
      rows.push([s.g, h1.g, h2.g, ar.path, ar.head, sm, ...g]);
    }
    // "The upper bits of the two halves add up to the upper bit of the original. So an owner splits into an owner
    // and a client, and a client into two clients."
    const tO = cue('o');
    for (const t of [L, R]) { tl.to(t.entries[0].b.wrap, { o: 0.35 }, tO, 0.4); t.pulse('a', tO + 0.3); }
    ft.types[0].pulse('a', tO + 2.55);                                          // "the upper bit of the original"
    frow(0, { a: 1, b: 0 }, [{ a: 1, b: 0 }, { a: 0, b: 0 }], '1 = 1 + 0', [['owner:', tO + 7.5], ['owner and client', tO + 7.6]],
      tO + 4.95, tO + 5.5, tO + 6.2, tO + 7.2, tO + 7.5, 'a');
    frow(1, { a: 0, b: 0 }, [{ a: 0, b: 0 }, { a: 0, b: 0 }], '0 = 0 + 0', [['client:', tO + 9.5], ['two clients', tO + 9.6]],
      tO + 8.1, tO + 8.45, tO + 8.8, tO + 9.05, tO + 9.45, 'a');
    // "The lower bits add up in the same way: if the reference was opened, exactly one of the two is opened, and
    // the duty to release goes with it."
    const tA = cue('a');
    for (const t of [L, R]) { tl.to(t.entries[0].b.wrap, { o: 1 }, tA + 0.05, 0.4); t.pulse('b', tA + 0.3); }
    ft.types[0].pulse('b', tA + 0.9);
    frow(2, { a: 1, b: 1 }, [{ a: 1, b: 0 }, { a: 0, b: 1 }], '1 = 0 + 1', [['the duty to release', tA + 6.6], ['goes with it', tA + 6.75]],
      tA + 3.3, tA + 3.85, tA + 4.3, tA + 4.75, tA + 5.75, 'b');
    void pl; void cl;

    // "So the type checker always knows, for each reference, who must release and who must wait."
    const tC = cue('check');
    LX.note(tl, root, CX, 850, 'the type checker knows who must release, and who must wait', tC + 0.1, cue('must') + 4.1, { color: C.ink });
    // "... those duties cannot be dropped on the floor. They can only be carried out, or handed to someone else."
    LX.note(tl, root, CX, 850, 'a duty is carried out, or handed on', cue('must') + 4.4, null, { color: C.ink });
  });

  // ============================================ prog_a =========================================================
  scene('prog_a', ({ tl, root, cue }) => {
    // "A lock with no clients is a mutable cell."
    const tRef = cue('ref');
    const cl = LX.note(tl, root, RAIL, 228, 'a mutable cell', tRef - 0.2, null, { align: 'left' });
    const code = LX.code(tl, root, RAIL, 300, 40, [
      'let ℓ = release(new(), 1) in',
      'let ℓ, n = acquire(ℓ) in',
      'let ℓ = release(ℓ, n + 1) in',
      'let n = wait(ℓ)',
    ]);
    code.show(tRef - 0.1, { stagger: 0.1 });
    const p = new LX.Picture(tl, root);
    p.thread('T', 1200, 480).lock('L', 1560, 480, { name: 'ℓ', contents: ['1'] }).ref('o', 'T', 'L', { owner: true });
    // the picture arrives with "What can be written this way?", so the stage is not empty before the code
    const tCell = cue('cell');
    p.show('T', tCell + 0.3); p.show('L', tCell + 0.55); p.show('o', tCell + 0.9);
    // "Acquire reads it, release writes it, and wait takes the value out for good."
    const tRw = cue('rw'), TX = 1380, TY = 580;
    code.light(1, tRw - 0.15);
    p.moveChip('L/0', 'T', tRw + 0.05); p.open('o', tRw + 0.05);
    LX.note(tl, root, TX, TY, 'read', tRw + 0.45, tRw + 1.3);
    const tWr = tRw + 1.45;                                    // "release writes it"
    code.light(2, tWr);
    p.chipText('L/0', '2', tWr + 0.05); p.moveChip('L/0', 'home', tWr + 0.4); p.close('o', tWr + 0.5);
    LX.note(tl, root, TX, TY, 'write', tWr + 0.6, tWr + 1.8);
    const tTk = tRw + 3.1;                                     // "and wait takes the value out"
    code.light(3, tTk);
    p.gone('L', tTk + 0.3, { chips: false, lines: false });
    p.moveChip('L/0', 'T', tTk + 0.35, { dur: 0.9 }); p.drop('o', tTk + 0.35, { dur: 0.9 });
    const take = LX.note(tl, root, TX, TY, 'take the value out', tTk + 0.7, null);

    // "With one client, it is a future."
    const tF = cue('fj');
    for (const e of [cl, take]) fadeOut(tl, e, tF - 0.3, 0.3);
    code.hide(tF - 0.3); p.out(tF - 0.3);
    const fl = LX.note(tl, root, RAIL, 200, 'a future', tF + 0.05, null, { align: 'left' });
    const fut = LX.code(tl, root, RAIL, 262, 38, [
      'let ℓ = fork(new(), λℓ. … drop(release(ℓ, v)) …) in',
      '…',
      'let v = wait(ℓ)',
    ]);
    fut.show(tF + 0.15, { stagger: 0.1 });

    // "The parent creates a lock, which is opened, and forks a child. Fork splits the reference: the parent keeps
    // the owner, closed, and the child gets the client, opened."
    const q = new LX.Picture(tl, root);
    q.thread('P', 1000, 580, { label: 'parent' }).lock('L', 1300, 700, { name: 'ℓ', nameSide: 'above' })
      .thread('K', 1600, 580, { label: 'child' })
      .ref('pr', 'P', 'L', { owner: true }).ref('kr', 'K', 'L', { color: C.pat });
    q.chip('v', 'L', 'v', { start: 'K' });
    const tP = cue('parent');
    q.show('P', tP + 0.1);
    fut.mark(0, 'new()', C.dim, tP + 1.25, { fill: 0.08, out: tP + 2.9 });
    q.show('L', tP + 1.3); q.show('pr', tP + 1.55);
    q.open('pr', tP + 2.0);                                     // "which is opened"
    fut.mark(0, 'fork', C.dim, tP + 2.9, { fill: 0.08, out: cue('child') - 0.2 });
    q.show('K', tP + 3.3);                                      // "and forks a child"
    const tSp = tP + 5.0;                                       // "Fork splits the reference"
    q.close('pr', tSp); q.show('kr', tSp);
    // the references' types above the threads: new() gives the parent Lock⟨τ¹₁⟩; fork splits it into the
    // parent's Lock⟨τ¹₀⟩ and the child's Lock⟨τ⁰₁⟩
    const typeY = 474;
    const ptype = LX.lockType(tl, root, 1000, typeY, { size: 34, a: 1, b: 1, align: 'center' }).show(tP + 1.6);
    ptype.pulse('b', tP + 2.05);                                // "which is opened"
    const ktype = LX.lockType(tl, root, 1600, typeY, { size: 34, a: 0, b: 1, align: 'center' }).show(tSp + 0.1);
    ptype.set({ b: 0 }, tSp);                                   // at the split, the opened bit goes to the child
    ptype.pulse('a', tP + 7.55); ptype.pulse('b', tP + 8.2);    // "the parent keeps the owner, closed"
    ktype.pulse('a', tP + 10.3); ktype.pulse('b', tP + 10.85);  // "and the child gets the client, opened"

    // "The child cannot drop its reference until it has released a value into the lock."
    const tC = cue('child');
    fut.mark(0, 'drop(release(ℓ, v))', C.dim, tC - 0.1, { fill: 0.08, out: cue('pw') - 0.2 });
    q.show('v', tC + 2.5);                                     // "released a value"
    q.moveChip('v', 'home', tC + 2.9, { dur: 0.8 });
    q.close('kr', tC + 3.6);
    ktype.set({ b: 0 }, tC + 3.55);                             // released: Lock⟨τ⁰₀⟩, which drop takes
    q.drop('kr', tC + 4.2); ktype.hide(tC + 4.3);
    q.dim('K', 0.4, tC + 4.6);
    // "That value is its result."
    const tRs = cue('res');
    q.pulse('v', tRs + 0.35);
    q.label('L', 'the result', tRs + 0.9, { side: 'below', out: cue('pw') - 0.2 });
    // "The parent calls wait, and gets it."
    const tW = cue('pw');
    fut.light(2, tW - 0.1);
    q.gone('L', tW + 0.85, { chips: false, lines: false });
    q.moveChip('v', 'P', tW + 1.0, { dur: 0.9 }); q.drop('pr', tW + 1.0, { dur: 0.9 });
    ptype.hide(tW + 1.0);                                       // wait has taken the parent's reference
    // "The child cannot finish without delivering, or handing that duty to someone else."
    LX.note(tl, root, CX, 850, 'the child cannot finish without delivering', cue('promise') + 0.1, null, { color: C.ink });
  });
})();

// ==== src/scenes/e.js ====
// More programs (shared data, the bank, the tree, channels) and the theorem (full reachability, the invariant),
// built with LX (common.js). Scenes: prog_b, prog_c, chan_a, chan_b, thm_a, thm_b.
'use strict';
(function () {
  const { C, E, scene } = Film;
  const { CX, RAIL } = LX;

  // a serif line, left edge at x (or right edge with align 'right'), rising in at `at`
  function serifAt(tl, root, x, y, text, size, at, { align = 'left', color = C.ink, dy = 16 } = {}) {
    const st = Object.assign(LX.SERIF(size), { whiteSpace: 'pre', color });
    const e = align === 'right' ? box(root, x - 1600, y, Object.assign(st, { width: '1600px', textAlign: 'right' }), text) : box(root, x, y, st, text);
    fadeIn(tl, e, at, 0.6, dy);
    return e;
  }
  // a closed smooth curve through points (Catmull-Rom as cubic Béziers)
  function closedCurve(P) {
    const n = P.length, f = v => v.toFixed(1);
    let d = `M ${f(P[0][0])} ${f(P[0][1])}`;
    for (let i = 0; i < n; i++) {
      const p0 = P[(i - 1 + n) % n], p1 = P[i], p2 = P[(i + 1) % n], p3 = P[(i + 2) % n];
      d += ` C ${f(p1[0] + (p2[0] - p0[0]) / 6)} ${f(p1[1] + (p2[1] - p0[1]) / 6)} ${f(p2[0] - (p3[0] - p1[0]) / 6)} ${f(p2[1] - (p3[1] - p1[1]) / 6)} ${f(p2[0])} ${f(p2[1])}`;
    }
    return d + ' Z';
  }

  // ============================================ prog_b ========================================================
  scene('prog_b', ({ tl, root, cue }) => {
    // "With several clients, it is shared data."
    const tShared = cue('shared'), tThree = cue('three'), tEach = cue('each'), tBank = cue('bank');
    const lab = LX.note(tl, root, RAIL, 220, 'shared data', tShared + 1.5, tBank - 0.3, { align: 'left' });

    // "The parent puts a value in a lock, forks three children with a client reference each, and waits."
    const sd = LX.code(tl, root, RAIL, 290, 36, [
      'let ℓ = release(new(), v) in',
      'let ℓ = fork(ℓ, λℓ. …) in',
      'let ℓ = fork(ℓ, λℓ. …) in',
      'let ℓ = fork(ℓ, λℓ. …) in',
      '…',
      'let w = wait(ℓ)',
    ]);
    const p = new LX.Picture(tl, root);
    p.thread('P', 1100, 300, { label: 'parent' }).lock('L', 1400, 480, { name: 'ℓ', contents: ['v'] })
      .thread('C1', 1700, 300, { label: 'child' }).thread('C2', 1700, 480, { label: 'child' }).thread('C3', 1700, 660, { label: 'child' })
      .ref('PL', 'P', 'L', { owner: true }).ref('c1', 'C1', 'L').ref('c2', 'C2', 'L').ref('c3', 'C3', 'L');
    p.show('P', tThree - 0.1);                                   // "The parent"
    sd.showLine(0, tThree + 0.45);                               // "puts a value in a lock"
    p.show('L', tThree + 0.85); p.show('PL', tThree + 1.3);
    [5.75, 6.4, 7.05].forEach((d, i) => {                        // "forks three children with a client reference each"
      sd.showLine(i + 1, d); sd.light(i + 1, d);
      p.show('C' + (i + 1), d + 0.05); p.show('c' + (i + 1), d + 0.3);
    });
    sd.showLine(4, 7.9); sd.light(4, 7.9);
    sd.showLine(5, 8.75); sd.light(5, 8.75);                     // "and waits"
    // "Each child may acquire and release as often as it likes.": one at a time, in no order
    sd.light([0, 1, 2, 3, 4, 5], tEach - 0.15);
    [['c2', 10.3], ['c1', 10.95], ['c3', 11.6], ['c2', 12.2], ['c3', 12.8], ['c1', 13.4]]
      .forEach(([id, t]) => { p.open(id, t); p.close(id, t + 0.48); });
    sd.hide(tBank - 0.3); p.out(tBank - 0.3);

    // "Here is a bank."
    LX.note(tl, root, RAIL, 220, 'a bank', tBank + 0.4, null, { align: 'left' });
    const tAcc = cue('acc'), tTr = cue('tr'), tNo = cue('noord'), tSafe = cue('safe');
    const b = new LX.Picture(tl, root);
    const AY = [230, 470, 710], BAL = ['90', '30', '60'];
    b.thread('B', 1310, 470, { label: 'bank' });
    AY.forEach((y, i) => b.lock('l' + (i + 1), 1530, y, { name: 'ℓ' + LX.sub(i + 1), contents: [BAL[i]], nameSide: 'below' }));
    AY.forEach((y, i) => b.thread('u' + (i + 1), 1725, y,   // its label clear of the stage's right edge
       { label: 'customer' }));
    AY.forEach((y, i) => b.ref('o' + (i + 1), 'B', 'l' + (i + 1), { owner: true }));
    AY.forEach((y, i) => b.ref('k' + (i + 1), 'u' + (i + 1), 'l' + (i + 1)));
    b.show('B', tBank + 0.3);
    // "Each account is a lock holding a balance, shared between the bank and one customer."
    const b1 = LX.code(tl, root, RAIL, 290, 30, [
      'let ℓ₁ = fork(release(new(), 0), λℓ₁. … customer 1 …) in',
      'let ℓ₂ = fork(release(new(), 0), λℓ₂. … customer 2 …) in',
      'let ℓ₃ = fork(release(new(), 0), λℓ₃. … customer 3 …) in',
      '…',
      'let ℓ₁, ℓ₂ = transaction(ℓ₁, ℓ₂, 50) in …',
    ], { paint: [['customer 1', C.dim], ['customer 2', C.dim], ['customer 3', C.dim]] });
    b1.show(tAcc + 0.1, { stagger: 0.12 });
    b.show(['l1', 'l2', 'l3'], tAcc + 0.75, { stagger: 0.15 });  // "is a lock holding a balance"
    b.show(['o1', 'o2', 'o3'], tAcc + 2.5, { stagger: 0.12 });   // "shared between the bank"
    b.show(['u1', 'u2', 'u3'], tAcc + 3.95, { stagger: 0.12 });  // "and one customer"
    b.show(['k1', 'k2', 'k3'], tAcc + 4.25, { stagger: 0.12 });

    // "To transfer money, the bank acquires two accounts, changes both balances, and releases them."
    b1.hide(tTr - 0.3, 0.3);
    // the long line of the first branch is broken after its comma, so that the listing can be set at 30 and stay
    // clear of the picture
    const tx = LX.code(tl, root, RAIL, 290, 30, [
      'transaction(ℓ₁, ℓ₂, amount) =',
      '  let ℓ₁, balance₁ = acquire(ℓ₁) in',
      '  let ℓ₂, balance₂ = acquire(ℓ₂) in',
      '  if balance₁ ≥ amount then',
      '    (release(ℓ₁, balance₁ - amount),',
      '     release(ℓ₂, balance₂ + amount))',
      '  else',
      '    (release(ℓ₁, balance₁), release(ℓ₂, balance₂))',
    ]);
    tx.show(tTr + 0.05, { stagger: 0.06 });
    tx.light(1, 23.25); b.open('o1', 23.35);                     // "the bank acquires"
    tx.light([1, 2], 23.85); b.open('o2', 23.95);                // "two accounts"
    tx.light([3, 4, 5], 24.95);                                     // "changes both balances"
    b.label('l1', '- 50', 25.05, { side: 'above', font: 'mono', size: 32, color: C.ink, out: 26.6 });
    b.label('l2', '+ 50', 25.05, { side: 'above', font: 'mono', size: 32, color: C.ink, out: 26.6 });
    b.chipText('l1/0', '40', 25.6); b.chipText('l2/0', '80', 26.05);
    b.close('o1', 26.7); b.close('o2', 26.95);                   // "and releases them"
    tx.light([0, 1, 2, 3, 4, 5, 6, 7], 27.4);
    // "It does not matter which it takes first.": the two acquires change places, and back
    tx.light([1, 2], tNo - 0.1);
    // (leave, then arrive in the other place, so that the two lines never print over each other)
    const exch = (t, d1, d2) => [[1, d1], [2, d2]].forEach(([k, d]) => {
      const e = tx.lineEls[k];
      tl.to(e, { o: 0 }, t, 0.22, E.in); tl.set(e, { y: d * tx.lh }, t + 0.24); tl.to(e, { o: 1 }, t + 0.26, 0.3, E.out5);
    });
    exch(tNo + 0.15, 1, -1);
    b.open('o2', tNo + 0.35); b.open('o1', tNo + 0.75);
    const r1 = tx.rect(1, null);
    LX.note(tl, root, r1.x + r1.w + 60, tx.lineY(1) + tx.lh - 19, 'either order', tNo + 0.55, null, { align: 'left' });
    exch(tNo + 1.45, 0, 0);
    b.close('o2', tNo + 1.75); b.close('o1', tNo + 1.95);
    // "Whatever the customers do, the picture has no cycle, so nothing can deadlock."
    tx.dim('all', 0.4, tSafe - 0.1, 0.5);
    LX.note(tl, root, CX, 850, 'no cycle: no deadlock, whatever the customers do', tSafe + 1.8, null, { color: C.good });
  });

  // ============================================ prog_c ========================================================
  // The tree. (Its narration ends after `conc`: the channels have their own scenes, chan_a and chan_b.)
  scene('prog_c', ({ tl, root, cue }) => {
    const tNode = cue('node'), tWalk = cue('walk'), tConc = cue('conc');
    // "Shared data can be recursive. In this tree, every node is a lock, holding a value and owning its children."
    const ty = LX.code(tl, root, RAIL, 136, 40, ['tree = Lock⟨1 + tree × τ × tree⟩']);
    ty.show(cue('tree') + 1.0);
    LX.note(tl, root, RAIL, 205, 'a node: empty, or a value and two children', tNode + 1.4, null, { align: 'left' });
    const p = new LX.Picture(tl, root);
    const N = { R: [960, 320], A: [660, 500], B: [1260, 500], A1: [510, 680], A2: [810, 680], B1: [1110, 680], B2: [1410, 680] };
    for (const [id, [x, y]] of Object.entries(N)) p.lock(id, x, y, { contents: ['v'] });
    const kids = [['R', 'A'], ['R', 'B'], ['A', 'A1'], ['A', 'A2'], ['B', 'B1'], ['B', 'B2']];
    for (const [a, c] of kids) p.ref(a + c, a, c, { owner: true });
    p.show('R', tNode + 0.4); p.show(['A', 'B'], tNode + 0.65, { stagger: 0.1 }); p.show(['A1', 'A2', 'B1', 'B2'], tNode + 0.95, { stagger: 0.08 });
    p.show(kids.map(([a, c]) => a + c), 6.85, { stagger: 0.08 });  // "and owning its children"

    // "A thread with a client reference to a node can step down the tree: it acquires the node, exchanges its
    // reference for a client reference to one of the children, and releases the node." (p. 10, `left`: the
    // thread's reference to the node is given away in the step, so it holds one reference at every moment)
    p.thread('T1', 360, 320, { name: 'T₁' }).ref('tR', 'T1', 'R');
    p.show('T1', tWalk + 0.1); p.show('tR', 9.15);              // "a client reference to a node"
    p.open('tR', 12.95);                                         // "it acquires the node"
    p.pulse('RA', 14.35, { dur: 0.8 });                          // "exchanges its reference"
    p.retarget('tR', 'to', 'A', 15.65, { dur: 1.9 });            // "for a client reference to one of the children"
    p.close('tR', 18.25);                                        // "and releases the node"

    // "So several threads can work in different parts of the tree at once.": each thread holds one reference; the
    // tree stays to the end of the scene
    p.thread('T2', 1620, 330, { name: 'T₂' }).ref('uB', 'T2', 'B');
    p.thread('T3', 960, 850, { name: 'T₃' }).ref('vB1', 'T3', 'B1');
    p.show('T2', 20.1); p.show('uB', 20.35);                     // "several threads"
    p.show('T3', 20.5); p.show('vB1', 20.75);
    [['tR', 21.2, 21.95], ['uB', 21.5, 22.5], ['vB1', 21.9, 22.7], ['tR', 22.5, 23.25]]   // "work in different parts ... at once"
      .forEach(([id, a, z]) => { p.open(id, a); p.close(id, z); });
    void tConc;
  });

  // ---- for the channels -------------------------------------------------------------------------------------
  const bitCol = (v, lower) => (lower && String(v) === '1' ? C.pat : C.code);
  // the two bits of a reference's type, stacked as in LX.lockType (upper raised, lower lowered), without the rest
  // of the type: a label on a reference of a Picture, so that it follows the line. -> {e, set({a, b}, at)}
  function bitsOn(tl, p, refId, a, b, at, opts = {}) {
    const bs = opts.bs || 30, cw = charWidth(bs), step = Math.round(0.69 * bs + 10);
    const e = p.label(refId, '', at, Object.assign({ font: 'mono', size: bs, gap: 12 }, opts));
    Object.assign(e.style, { width: Math.ceil(cw) + 'px', height: (step + bs) + 'px' });
    const mk = (top, v, lower) => box(e, 0, top, Object.assign(LX.MONO(bs), { width: Math.ceil(cw) + 'px', textAlign: 'center', lineHeight: 1, color: bitCol(v, lower), transformOrigin: 'center center' }), String(v));
    const ta = mk(0, a, false), tb = mk(step, b, true);
    return {
      e,
      set({ a: na, b: nb }, t) {
        if (na !== undefined) { LX.flip(tl, ta, String(na), t, 0.4); tl.to(ta, { color: bitCol(na, false) }, t + 0.16, 0.25); }
        if (nb !== undefined) { LX.flip(tl, tb, String(nb), t, 0.4); tl.to(tb, { color: bitCol(nb, true) }, t + 0.16, 0.25); }
      },
      pulse(t) { tl.to(e, { s: 1.3 }, t, 0.22, E.out); tl.to(e, { s: 1 }, t + 0.22, 0.35, E.io); },
    };
  }
  // A line that grows out of its lock toward the holder, or shrinks into its lock, would need the line's `a` end to
  // move, which LX.Picture draws with a stray segment (common.js `dashes`: for a > 0 the dash pattern repeats before
  // a). So both are done with a mirror: a reference with the same ends the other way round (lock -> holder), whose
  // `b` end moves; the real reference is swapped in or out at the moment the two look the same.
  // grow: the mirror is drawn from the lock to the holder, then the real reference replaces it
  function drawFromLock(tl, p, id, mirror, at, dur) {
    const m = p.item(mirror), r = p.item(id);
    m.a.add(at, 0, 0); m.b.add(at, 0, 0); m.b.add(at, dur, 1, E.io);
    tl.set(m.g, { o: 1 }, at); tl.set(m.g, { o: 0 }, at + dur);
    r.a.add(at + dur, 0, 0); r.b.add(at + dur, 0, 1); tl.set(r.g, { o: 1 }, at + dur);
  }
  // shrink: the real reference is replaced by the mirror, which retracts into the lock; the labels go
  function retract(tl, p, id, mirror, at, dur) {
    const m = p.item(mirror), r = p.item(id);
    tl.set(r.g, { o: 0 }, at);
    m.a.add(at, 0, 0); m.b.add(at, 0, 1); tl.set(m.g, { o: 1 }, at);
    m.b.add(at, dur, 0, E.io);
    for (const e of r.extra) tl.to(e, { o: 0 }, at, 0.3, E.in);
  }
  // a session type in mono, centred on cx, top at y: pieces [text, ...] in a row; the last one may be a small
  // lowered subscript ({sub: '!'}). -> the pieces' elements
  function sessionType(root, cx, y, size, pieces) {
    const cw = charWidth(size), sz = Math.round(size * 0.62), scw = charWidth(sz);
    const w = pieces.reduce((s, q) => s + (typeof q === 'string' ? q.length * cw : scw * 1.2), 0);
    let x = cx - w / 2;
    return pieces.map(q => {
      let e;
      if (typeof q === 'string') { e = box(root, x, y, Object.assign(LX.MONO(size), { whiteSpace: 'pre', transformOrigin: 'center center' }), q); x += q.length * cw; }
      else { e = box(root, x + scw * 0.2, y + size * 0.62, Object.assign(LX.MONO(sz), { whiteSpace: 'pre' }), q.sub); x += scw * 1.2; }
      return e;
    });
  }
  const pulseEl = (tl, e, at, s = 1.25) => { tl.to(e, { s }, at, 0.22, E.out); tl.to(e, { s: 1 }, at + 0.22, 0.4, E.io); };
  // a small drawing: a channel (a thick rounded bar), w wide, centred on (cx, cy)
  const chanBar = (root, cx, cy, w) => box(root, cx - w / 2, cy - 18, { width: w + 'px', height: '36px', borderRadius: '18px', boxShadow: `inset 0 0 0 3px ${C.ink}`, background: alpha(C.ink, 0.06) });

  // ============================================ chan_a ========================================================
  // Session types, and the future as a channel for one message.
  scene('chan_a', ({ tl, root, cue }) => {
    const tChan = cue('chan'), tSt = cue('st'), tFut = cue('fut'), tOne = cue('one');
    // "Message passing comes with all this, for free."
    LX.note(tl, root, RAIL, 200, 'message passing', tChan + 0.05, null, { align: 'left' });

    // "A session type describes a conversation over a channel: send a number, then receive a yes or no, then stop."
    const AX = 460, BX = 1460, Y = 420;
    const p = new LX.Picture(tl, root);
    p.thread('A', AX, Y, { name: 'A' }).thread('B', BX, Y, { name: 'B' });
    p.show('A', tSt + 0.05); p.show('B', tSt + 0.2);
    const bar = chanBar(root, (AX + BX) / 2, Y, BX - AX - 124);
    tl.set(bar, { o: 0, sx: 0.2 }, 0); tl.to(bar, { o: 1, sx: 1 }, 6.3, 0.6, E.out5);    // "over a channel"
    const TY = 292;
    const sa = sessionType(root, AX, TY, 44, ['!int', ' . ', '?bool', ' . ', 'End', { sub: '!' }]);
    fadeIn(tl, sa[0], 7.55, 0.5, 12);                              // "send a number"
    [sa[1], sa[2]].forEach(e => fadeIn(tl, e, 9.05, 0.5, 12));     // "then receive a yes or no"
    [sa[3], sa[4], sa[5]].forEach(e => fadeIn(tl, e, 10.85, 0.5, 12));   // "then stop"
    const sl = LX.note(tl, root, CX, 500, 'a session type: the conversation, seen from one end', 11.55, null);
    // "Each end of the channel has such a type, and the two fit together: where one end sends, the other receives."
    const sb = sessionType(root, BX, TY, 44, ['?int', ' . ', '!bool', ' . ', 'End', { sub: '?' }]);
    sb.forEach(e => fadeIn(tl, e, 13.55, 0.5, 12));                // "has such a type"
    pulseEl(tl, sa[0], 16.4); pulseEl(tl, sb[0], 16.4);           // "where one end sends,"
    pulseEl(tl, sa[2], 17.85); pulseEl(tl, sb[2], 17.85);         // "the other receives"

    // "Now recall the future. It is a channel for a single message.": A is the child, B the parent
    for (const e of [...sa, ...sb, sl]) fadeOut(tl, e, tFut - 0.3, 0.35);
    tl.to(bar, { o: 0, s: 1.03, blur: 4 }, tFut - 0.3, 0.45, E.in);
    p.lock('L', CX, Y, { name: 'ℓ', nameSide: 'above' })
      .ref('a', 'A', 'L', { color: C.pat }).ref('b', 'B', 'L', { owner: true });
    p.show('L', tFut + 0.1); p.show('a', tFut + 0.4); p.show('b', tFut + 0.55);
    LX.note(tl, root, CX, 500, 'the future', tFut + 0.85, tOne - 0.25);
    LX.note(tl, root, CX, 500, 'a channel for one message', tOne + 0.55, cue('bits') + 0.2);

    // "The thread with the opened client reference has to put a value in: it is the sender."
    const at = LX.lockType(tl, root, (AX + 46 + CX - 42) / 2, 352, { size: 36, a: 0, b: 1, align: 'center' }).show(24.9);
    at.pulse('b', 25.05); at.pulse('a', 25.45);                   // "opened", "client"
    p.chip('v', 'L', 'v', { start: 'A' });
    p.show('v', 26.6);                                              // "put a value in"
    p.moveChip('v', 'home', 27.0, { dur: 0.8 });
    p.close('a', 27.75); at.set({ b: 0 }, 27.7);                    // released: Lock⟨τ⁰₀⟩, which drop takes
    p.drop('a', 28.25); at.hide(28.35);
    p.label('A', 'sender', 28.7);
    // "The thread with the closed owner reference waits for that value: it is the receiver."
    const bt = LX.lockType(tl, root, (CX + 42 + BX - 46) / 2, 352, { size: 36, a: 1, b: 0, align: 'center' }).show(30.1);
    bt.pulse('b', 30.25); bt.pulse('a', 30.7);                    // "closed", "owner"
    p.gone('L', 32.1, { chips: false, lines: false });              // "waits for that value"
    p.moveChip('v', 'B', 32.25, { dur: 0.9 }); p.drop('b', 32.25, { dur: 0.9 });
    bt.hide(32.3);
    p.label('B', 'receiver', 33.85);

    // "So sending is a lock type with the bits zero, one, and receiving is a lock type with the bits one, zero."
    const LXR = 900, TX = 930, Y1 = 640, Y2 = 760, S = 48;
    const off = Math.round((S * 1.3 - 32 * 1.2) / 2);
    LX.note(tl, root, LXR, Y1 + off, 'send a value:', 35.2, null, { align: 'right' });
    const t1 = LX.typeLine(tl, root, TX, Y1, S, [{ a: 0, b: 1 }]).show(35.3);
    t1.types[0].pulse('a', 37.4); t1.types[0].pulse('b', 38.05);   // "zero, one"
    LX.note(tl, root, LXR, Y2 + off, 'receive a value:', 38.9, null, { align: 'right' });
    const t2 = LX.typeLine(tl, root, TX, Y2, S, [{ a: 1, b: 0 }]).show(39.0);
    t2.types[0].pulse('a', 41.25); t2.types[0].pulse('b', 41.72); // "one, zero"
  });

  // ============================================ chan_b ========================================================
  // A longer conversation: each message carries a reference to a fresh lock. The picture stays a chain at every
  // moment: A puts the value and the fresh lock's client reference into the old lock as one step (the paper does
  // it in a tiny forked thread, p. 14), so A never holds the old lock while it refers to the fresh one.
  scene('chan_b', ({ tl, root, cue }) => {
    const AX = 360, BX = 1560, Y = 380, MX = 960, DY = 640;
    const p = new LX.Picture(tl, root);
    p.thread('A', AX, Y, { name: 'A' }).thread('B', BX, Y, { name: 'B' })
      .lock('c', MX, Y, { name: 'c', nameSide: 'above' })
      .lock('d', AX, DY, { name: 'd', nameSide: 'below' })
      .lock('e', BX, DY, { name: 'e', nameSide: 'below' })
      .ref('Ac', 'A', 'c').ref('Bc', 'B', 'c', { owner: true })
      .ref('Ad', 'A', 'd', { owner: true }).ref('eB', 'B', 'e', { owner: true });
    // c's contents after the send: the value v and (at its left, toward d) the reference to d
    p.chip('v', 'c', 'v', { start: 'A' }).chip('cr', 'c', { ref: true });
    const cc = p.item('c'); cc.chips.reverse(); p._layoutChips(cc);
    p.ref('dk', 'cr', 'd');
    // d's contents in the second round: w and (at its right, toward e) the reference to e
    p.chip('w', 'd', 'w', { start: 'B' }).chip('er', 'd', { ref: true });
    p.ref('ek', 'er', 'e');
    // the mirrors (see drawFromLock): c -> A for A's old line, d -> cr and e -> er for the arriving references,
    // d -> B for B's line to d in the second round
    p.ref('Ac~', 'c', 'A').ref('dk~', 'd', 'cr').ref('ek~', 'e', 'er').ref('dk~2', 'd', 'B');
    for (const id of ['Ac', 'dk', 'ek', 'dk~', 'ek~']) p.color(id, C.pat, 0, 0);   // opened clients

    // "For a longer conversation, each message carries one more thing: a reference to a fresh lock, for the rest of
    // the conversation."
    p.show(['A', 'c', 'B'], 0.25, { stagger: 0.1 });
    p.show('Ac', 0.55); p.show('Bc', 0.7);
    const bAc = bitsOn(tl, p, 'Ac', 0, 1, 1.0), bBc = bitsOn(tl, p, 'Bc', 1, 0, 1.1);
    const chip = box(root, AX - 15, 505 - 15, { width: '30px', height: '30px', borderRadius: '7px', border: `3px solid ${C.bind}`, background: C.bg });
    fadeIn(tl, chip, 4.9, 0.5, 10);                                // "a reference to a fresh lock"
    const rest = LX.note(tl, root, AX + 44, 486, 'the rest of the conversation', 6.4, 9.5, { align: 'left' });

    // "To send, a thread creates the fresh lock, puts the value and one reference to that lock into the old lock,
    // and keeps the other reference."
    tl.to(chip, { y: DY - 505, s: 2.4, o: 0 }, 9.7, 0.5, E.in);      // the chip becomes the lock d
    p.show('d', 9.85);                                              // "creates the fresh lock"
    p.show('Ad', 10.25); p.color('Ad', C.pat, 10.25, 0);            // new(): an opened owner
    const bAd = bitsOn(tl, p, 'Ad', 1, 1, 10.6, { side: 'right', gap: 18, out: 22.45 });
    p.show('v', 12.0);                                              // "puts the value"
    p.close('Ad', 12.6); bAd.set({ b: 0 }, 12.6);                   // "and one reference": A keeps the closed owner
    drawFromLock(tl, p, 'dk', 'dk~', 12.7, 1.8);                           // the opened client goes toward the old lock
    p.close('Ac', 13.3); bAc.set({ b: 0 }, 13.3);                   // release into c ...
    p.moveChip('v', 'home', 13.5, { dur: 0.95 });                   // "into the old lock"
    retract(tl, p, 'Ac', 'Ac~', 13.55, 0.9);                               // ... and drop c
    p.show('cr', 14.35);
    const bdk = bitsOn(tl, p, 'dk', 0, 1, 14.4, { out: 24.0 });
    p.pulse('Ad', 15.75, { dur: 0.8 }); bAd.pulse(15.8);            // "and keeps the other reference"

    // "To receive, the other thread waits on the old lock. It gets the value, and its end of the new lock."
    p.pulse('Bc', 19.25, { dur: 0.8 });                             // "waits on the old lock"
    p.gone('c', 20.2, { chips: false, lines: false });
    p.hide('cr', 20.25, 0.3);
    p.drop('Bc', 20.3, { dur: 0.9 });                               // wait takes the owner's reference
    p.moveChip('v', 'B', 20.3, { dur: 0.9 });                       // "It gets the value,"
    p.retarget('dk', 'from', 'B', 20.35, { dur: 0.9 });             // "and its end of the new lock"
    p.hide('v', 21.85, 0.4);
    p.pulse('dk', 22.3, { dur: 0.8 });
    p.move('d', MX, Y, 22.6, { dur: 0.9 });                         // d takes c's place
    const bAd2 = bitsOn(tl, p, 'Ad', 1, 0, 23.5, { out: 24.0 });    // A will receive next; B (0 over 1) sends
    void bBc; void bdk; void bAd2;

    // "So a channel is a chain of locks, each used once.": the next message, from B, the same way
    p.show('e', 24.2); p.show('eB', 24.45); p.color('eB', C.pat, 24.45, 0);
    p.close('eB', 24.95);
    drawFromLock(tl, p, 'ek', 'ek~', 25.0, 1.1);
    p.show('w', 24.95);
    p.close('dk', 25.05);
    p.moveChip('w', 'home', 25.2, { dur: 0.85 });
    retract(tl, p, 'dk', 'dk~2', 25.25, 0.8);
    p.show('er', 26.0);
    const ch = LX.note(tl, root, CX, 830, 'a channel: a chain of locks, each used once', 25.35, 27.85);
    p.gone('d', 26.35, { chips: false, lines: false });             // A waits on d
    p.hide('er', 26.4, 0.3);
    p.drop('Ad', 26.45, { dur: 0.8 });
    p.moveChip('w', 'A', 26.45, { dur: 0.8 });
    p.retarget('ek', 'from', 'A', 26.5, { dur: 0.8 });
    p.hide('w', 27.3, 0.35);
    p.move('e', MX, Y, 27.2, { dur: 0.75 });
    void ch;

    // "And every session type is a lock type. Nothing has to be added to the type system."
    p.to({ y: -150 }, 28.0, 0.8); p.fade(0.35, 28.0);
    const S = 52;
    const l1 = LX.typeLine(tl, root, CX, 380, S, ['!τ.s  =  ', { of: '(s × τ)', a: 0, b: 1 }], { align: 'center' }).show(28.6);
    const l2 = LX.typeLine(tl, root, CX, 480, S, ['?τ.s  =  ', { of: '(s × τ)', a: 1, b: 0 }], { align: 'center' }).show(29.1);
    // the bar over the first s: the dual, the other end's view (drawn; there is no such character in the fonts)
    const lt = l1.types[0], scw = charWidth(S);
    box(l1.g, lt.entries[0].x + scw * 1.12, 380 + S * 0.31, { width: Math.round(scw * 0.76) + 'px', height: '3px', background: C.code, borderRadius: '2px' });
    const sn = Object.assign(LX.SERIF(36), { fontStyle: 'italic', textTransform: 'none', letterSpacing: '0', color: C.ink });
    const sl = LX.note(tl, root, CX, 580, ['session types are lock types · ', ['s', null, sn], ": the other end's view of ", ['s', null, sn]], 30.6, null);
    box(sl.children[1], 3, 9, { width: '13px', height: '2px', background: C.ink, borderRadius: '1px' });   // the s's bar, drawn
    void l2;

    // "So the guarantee covers channels too: programs with session types cannot deadlock, and channels can be stored
    // in locks, and locks sent over channels."
    LX.note(tl, root, CX, 670, 'the same guarantee: no deadlock, no leak', 33.95, null, { color: C.good });
    const RY = 790, D1 = 470, D2 = 1100;
    const d1 = box(root, D1 - 42, RY - 42, { width: '84px', height: '84px', borderRadius: '16px', border: `3px solid ${C.bind}` });
    box(d1, 14, 32, { width: '50px', height: '14px', borderRadius: '7px', boxShadow: `inset 0 0 0 3px ${C.ink}`, background: alpha(C.ink, 0.06) });
    fadeIn(tl, d1, 39.55, 0.5, 14);                                 // "channels can be stored in locks"
    LX.note(tl, root, D1 + 76, RY - 19, 'channels in locks', 39.65, null, { align: 'left' });
    const d2 = chanBar(root, D2, RY, 120);
    box(d2, 47, 5, { width: '26px', height: '26px', borderRadius: '6px', border: `3px solid ${C.bind}`, background: C.bg });
    fadeIn(tl, d2, 41.7, 0.5, 14);                                  // "and locks sent over channels"
    LX.note(tl, root, D2 + 90, RY - 19, 'locks over channels', 41.8, null, { align: 'left' });

    // "One caveat: done literally, every send starts a tiny thread, so a real implementation would still provide
    // channels directly."
    LX.note(tl, root, CX, 856, 'done literally: a tiny thread for every send', 45.15, null);
  });

  // ============================================ thm_a =========================================================
  scene('thm_a', ({ tl, root, cue }) => {
    const tThm = cue('thm'), tStart = cue('start'), tEvery = cue('every'), tCan = cue('can'), tOr = cue('or');
    const tReach = cue('reach'), tDl = cue('dl'), tLk = cue('lk'), tEmpty = cue('empty');
    // "Now the guarantee, stated properly."
    LX.note(tl, root, CX, 470, 'if it type-checks: no deadlock, no leak', tThm + 0.25, tStart - 0.35, { color: C.good });
    // "Take a program that type-checks, and run it for any number of steps."
    const st = serifAt(tl, root, RAIL, 180, 'a program that type-checks, run for any number of steps', 48, tStart + 0.4);

    // "Then every thread is in one of two situations."
    const p = new LX.Picture(tl, root);
    const Y = 420, Y2 = 600, Y3 = 780;
    p.thread('T1', 560, Y, { name: 'T₁' }).lock('l1', 760, Y, { name: 'ℓ₁' }).thread('T2', 960, Y, { name: 'T₂' })
      .lock('l2', 1160, Y, { name: 'ℓ₂' }).thread('T3', 1360, Y, { name: 'T₃' })
      .lock('l3', 960, Y2, { name: 'ℓ₃' }).thread('T4', 960, Y3, { name: 'T₄' })
      .lock('l4', 1360, Y2, { name: 'ℓ₄' }).thread('T5', 1360, Y3, { name: 'T₅' })
      .ref('a', 'T1', 'l1').ref('b', 'T2', 'l1').ref('c', 'T2', 'l2').ref('d', 'T3', 'l2')
      .ref('e', 'T2', 'l3').ref('f', 'T4', 'l3').ref('g', 'T3', 'l4').ref('h', 'T5', 'l4');
    p.showAll(tEvery + 0.1, { stagger: 0.08 });

    // "It can take a step."
    p.can('T3', tCan + 0.05); p.can('T5', tCan + 0.05);
    const cs = [p.label('T3', 'can step', tCan + 0.45, { side: 'right', gap: 30, color: C.good, out: tDl - 0.3 }),
      p.label('T5', 'can step', tCan + 0.45, { side: 'right', gap: 30, color: C.good, out: tDl - 0.3 })];
    // "Or it is waiting, and what it waits for leads, along a chain, to something that can take a step."
    p.label('T1', 'waiting', tOr + 0.8, { side: 'above', out: tDl - 0.3 });
    p.label('T2', 'waiting', tOr + 0.8, { side: 'above', out: tDl - 0.3 });
    p.label('T4', 'waiting', tOr + 0.8, { side: 'left', gap: 30, out: tDl - 0.3 });
    p.waiting('a', tOr + 0.9); p.waiting('c', tOr + 0.9); p.waiting('f', tOr + 0.9);
    p.walk(['T1', 'l1', 'T2', 'l2', 'T3'], 17.2, { step: 0.55, color: C.good, trail: 'line', marker: 'head', offset: 14, out: tDl - 0.3 });
    p.walk(['T4', 'l3', 'T2', 'l2', 'T3'], 17.45, { step: 0.55, color: C.good, trail: 'line', marker: 'head', offset: -14, out: tDl - 0.3 });

    // "The paper calls this full reachability."
    const fr = serifAt(tl, root, 1810, 262, 'full reachability', 56, tReach + 1.15, { align: 'right' });

    // "It rules out deadlock: not only the whole program being stuck, but any group of threads being stuck among
    // themselves.": a loop around T1, T2, T4 (a group stuck among themselves), struck
    const svg = LX.svg(root);
    const loop = LX.dpath(tl, svg, closedCurve([[468, 420], [530, 340], [760, 338], [960, 328], [1046, 380], [1050, 600],
      [1046, 790], [960, 848], [874, 790], [866, 600], [780, 514], [560, 510]]), { stroke: C.bad, width: 3, dash: '12 10' });
    tl.to(loop, { draw: 1 }, tDl + 0.2, 1.0, E.io);
    const sk = LX.strikeLine(tl, svg, 632, 556, 696, 474, tDl + 1.3);
    tl.to(loop, { o: 0.55 }, tDl + 1.3, 0.4);
    const gl = LX.note(tl, root, CX, 862, 'no group stuck among themselves', 28.65, null);
    for (const e of [loop, sk, gl]) fadeOut(tl, e, tLk - 0.25, 0.35, 0);

    // "The same holds for every lock, and that rules out leaks: no lock is ever cut off, with nothing left that can
    // reach it."
    for (const id of ['l1', 'l2', 'l3', 'l4']) p.pulse(id, 32.85);   // "every lock"
    const lone = new LX.Picture(tl, root);
    lone.lock('x', 1640, 600, { stroke: C.bad });
    lone.show('x', 34.95);                                       // "leaks"
    lone.strike('x', 36.85, { fade: 0.5 });                      // "cut off"
    const cl = LX.note(tl, root, 1640, 668, 'no lock cut off', 37.0, null);

    // "And when all threads have finished, no lock is left.": threads go one by one, each lock with its last line
    for (const e of [st, fr, cl]) fadeOut(tl, e, tEmpty - 0.25, 0.35);
    lone.out(tEmpty - 0.25, 0.35);
    [['T5', 0.05], ['T3', 0.4], ['l4', 0.65], ['T2', 0.85], ['l2', 1.1], ['T4', 1.25], ['l3', 1.5], ['T1', 1.65], ['l1', 1.9]]
      .forEach(([id, d]) => p.gone(id, tEmpty + d, { dur: 0.5 }));
    LX.note(tl, root, CX, 470, 'all threads finished: no lock left', 42.0, null, { color: C.good });
    void cs;
  });

  // ============================================ thm_b =========================================================
  scene('thm_b', ({ tl, root, cue }) => {
    const tProof = cue('proof'), tInv = cue('inv'), tPres = cue('pres'), tWalk = cue('walk'), tCoq = cue('coq');
    // a small picture: a tree of threads and locks (the second copy, after one step, has one more thread)
    const K = 0.5, CY = 390;
    const mini = (cx, extra) => {
      const m = new LX.Picture(tl, root, { x: cx, y: CY, k: K, cx: 0, cy: 0, r: 30, size: 54 });
      m.thread('a', -180, -55).lock('b', -60, -55).thread('c', 60, -55).lock('d', 180, -55)
        .lock('f', 60, 65).thread('g', 180, 65)
        .ref('ab', 'a', 'b').ref('cb', 'c', 'b').ref('cd', 'c', 'd').ref('cf', 'c', 'f').ref('gf', 'g', 'f');
      if (extra) m.thread('h', -60, 65).ref('hb', 'h', 'b');
      return m;
    };
    // "The proof follows the picture."
    const m1 = mini(1355, false);
    m1.showAll(tProof + 1.0, { stagger: 0.04 });
    // "An invariant says: everything is well typed, the picture has no cycle, and every lock has exactly one owner
    // and at most one opened reference."
    m1.fade(0.45, tInv - 0.1);
    const head = LX.note(tl, root, RAIL, 190, 'the invariant', tInv - 0.15, null, { align: 'left', color: C.ink });
    const rows = [['everything is well typed', 4.25], ['the picture has no cycle', 6.2], ['each lock: one owner, at most one opened reference', 8.2]]
      .map(([t, at], i) => serifAt(tl, root, RAIL, 280 + i * 110, t, 46, at));
    // "Every step of the program preserves it."
    m1.fade(1, tPres - 0.15);
    const svg = LX.svg(root);
    const m2 = mini(1705, true);
    const ar = LX.line(tl, svg, 1478, CY, 1582, CY, { at: tPres + 0.1, dur: 0.5 });
    const os = LX.note(tl, root, 1530, CY - 92, 'one step', tPres + 0.2, null);
    m2.showAll(tPres + 0.5, { stagger: 0.03 });
    const pv = LX.note(tl, root, 1530, CY + 70, 'preserved', 15.35, null, { color: C.good });

    // "And from the invariant, the walk we took earlier, from a waiting thread along the lines of the picture, always
    // ends at something that can step."
    for (const e of [...rows, head]) tl.to(e, { o: 0.5 }, tWalk + 1.4, 0.5);
    for (const e of [m1, m2]) e.fade(0.45, tWalk + 1.4);
    for (const e of [os, pv, svg]) tl.to(e, { o: 0.45 }, tWalk + 1.4, 0.5);
    void ar;
    const w = new LX.Picture(tl, root, { x: 1530, y: 640, k: 1, cx: 0, cy: 0, r: 30, size: 54 });
    w.thread('T1', -260, 0).lock('l1', -130, 0).thread('T2', 0, 0).lock('l2', 130, 0).thread('T3', 260, 0)
      .ref('a', 'T1', 'l1').ref('b', 'T2', 'l1').ref('c', 'T2', 'l2').ref('d', 'T3', 'l2');
    w.showAll(tWalk + 1.5, { stagger: 0.06 });                   // "the walk we took earlier"
    w.waiting('a', 20.0); w.waiting('c', 20.0);                  // "from a waiting thread"
    w.walk(['T1', 'l1', 'T2', 'l2', 'T3'], 20.75, { step: 0.55 });   // "along the lines of the picture"
    w.can('T3', 23.75);                                          // "something that can step"
    LX.note(tl, root, 1530, 702, 'so everything is reachable', 24.15, null);

    // "All of this is checked by machine, in a proof assistant."
    const svg2 = LX.svg(root);
    const lx = CX - 170;
    LX.tick(tl, svg2, lx - 44, 848, 44, tCoq + 0.95);
    LX.note(tl, root, lx, 829, 'mechanized in Coq', tCoq + 1.0, null, { align: 'left' });
  });
})();

// ==== src/scenes/f.js ====
// Lock groups (grp_a, grp_b, grp_c with grp_d) and the limits (limits), built with LX (common.js).
'use strict';
(function () {
  const { C, E, scene } = Film;
  const { CX, RAIL } = LX;

  // a mono text box with its left edge at x and its top at y
  const mono = (root, x, y, text, size, color) => box(root, x, y, Object.assign(LX.MONO(size), { whiteSpace: 'pre' }, color ? { color } : {}), text);

  // ============================================ grp_a =========================================================
  scene('grp_a', ({ tl, root, cue }) => {
    // "Two threads can never share two locks.": the classic square, all four lines red
    const tTwo = cue('two');
    const sq = new LX.Picture(tl, root);
    sq.thread('T1', 660, 480).thread('T2', 1260, 480).lock('A', 960, 300).lock('B', 960, 660)
      .ref('1A', 'T1', 'A').ref('1B', 'T1', 'B').ref('2A', 'T2', 'A').ref('2B', 'T2', 'B');
    for (const r of ['1A', '1B', '2A', '2B']) sq.color(r, C.bad, 0, 0);
    sq.show(['T1', 'T2'], cue('limit') + 0.3, { stagger: 0.1 });       // with "The rule has a price": no empty stage
    sq.show(['A', 'B'], tTwo + 1.1, { stagger: 0.1 });                 // "share two locks"
    sq.show(['1A', '2A', '1B', '2B'], tTwo + 1.5, { stagger: 0.1 });
    const notAllowed = LX.note(tl, root, CX, 800, 'not allowed', tTwo + 2.2, null);
    // "So a bank with two tellers, both working on the same accounts"
    sq.label('T1', 'teller 1', 7.9, { side: 'left' });
    sq.label('T2', 'teller 2', 8.05, { side: 'right' });
    sq.label('A', 'account a', 9.8, { side: 'above' });
    sq.label('B', 'account b', 9.95, { side: 'below' });

    // "Nor can the dining philosophers: threads around a table, each sharing a lock with each neighbour."
    const tPhil = cue('phil');
    sq.out(tPhil - 0.3); fadeOut(tl, notAllowed, tPhil - 0.3, 0.3);
    const rg = LX.ring(tl, root, 960, 500, { n: 5, radius: 300, names: false });
    const { nodes, refs } = LX.ringIds(5);
    rg.show(nodes.filter(n => n[0] === 'T'), 14.5, { stagger: 0.25 });     // "the dining philosophers: threads around a table"
    rg.show(nodes.filter(n => n[0] === 'l'), 17.6, { stagger: 0.08 });     // "each sharing a lock"
    rg.show(refs, 18.2, { stagger: 0.07 });                                 // "with each neighbour"
    // "That picture is a ring."
    const tRing = cue('ring');
    rg.cycle(refs, tRing + 0.1, { stagger: 0.07 });
    const aRing = LX.note(tl, root, 960, 482, 'a ring', tRing + 0.9, null, { color: C.bad });

    // "The second language in the paper allows this, with lock groups."
    const tExt = cue('ext');
    rg.fade(0.35, tExt - 0.1); tl.to(aRing, { o: 0.35 }, tExt - 0.1, 0.5);
    rg.out(24.35); fadeOut(tl, aRing, 24.35, 0.3);
    const title = LX.cserif(root, CX, 200, 'lock groups', 60);
    fadeIn(tl, title, 24.6, 0.7, 18);

    // "A lock group is a collection of locks behind a single reference."
    const tGrp = cue('grp');
    tl.to(title, { o: 0.45 }, tGrp, 0.5);
    const p = new LX.Picture(tl, root);
    p.group('g', 960, 440, 420, 200)
      .lock('a', 840, 440, { group: 'g' }).lock('b', 960, 440, { group: 'g' }).lock('c', 1080, 440, { group: 'g' })
      .thread('T1', 500, 440).thread('T2', 1420, 440)
      .ref('r1', 'T1', 'g').ref('r2', 'T2', 'g')
      .group('h', 1420, 720, 240, 120)
      .lock('d', 1370, 720, { group: 'h', size: 60 }).lock('e', 1470, 720, { group: 'h', size: 60 })
      .ref('r3', 'T2', 'h');
    p.show('g', tGrp - 0.2);
    p.show(['a', 'b', 'c'], 26.85, { stagger: 0.1 });                     // "a collection of locks"
    p.show('T1', 27.9); p.show('r1', 28.6);                              // "behind a single reference"
    const several = LX.note(tl, root, CX, 580, 'several locks behind one reference', 29.0, 32.3);
    // "Fork may share a whole group."
    const tFork = cue('fork');
    p.show('T2', tFork - 0.15); p.show('r2', tFork + 0.9);
    // "In the picture, the group is one square. Between groups, the rule is as before."
    const tPic = cue('pic');
    p.dim(['a', 'b', 'c'], 0.3, tPic + 0.3, 0.5);
    LX.note(tl, root, CX, 580, 'in the picture: one square', 33.75, null);
    p.show('h', 35.2); p.show(['d', 'e'], 35.3, { stagger: 0.08 }); p.show('r3', 35.75);
    LX.note(tl, root, CX, 832, 'between groups: no cycles, as before', 36.4, null, { color: C.good });
    void several;
  });

  // ============================================ grp_b =========================================================
  scene('grp_b', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    // "Inside a group, cycles are possible": one large group, three locks, two threads sharing two of them
    const p = new LX.Picture(tl, root, { cx: 960, cy: 360 });
    p.group('g', 960, 360, 900, 300)
      .lock('l1', 710, 360, { group: 'g' }).lock('l2', 960, 360, { group: 'g' }).lock('l3', 1210, 360, { group: 'g' })
      .thread('A', 960, 600).thread('B', 960, 770);
    const thin = { color: C.dim, width: 2.5 };
    p.ref('A1', 'A', 'l1', thin).ref('A3', 'A', 'l3', thin).ref('B1', 'B', 'l1', thin).ref('B3', 'B', 'l3', thin);
    const t0 = cue('inside');
    p.show('g', t0 - 0.2); p.show(['l1', 'l2', 'l3'], t0 - 0.05, { stagger: 0.08 });
    p.show(['A', 'B'], 1.5, { stagger: 0.12 });                          // "cycles"
    p.show(['A1', 'A3', 'B3', 'B1'], 2.0, { stagger: 0.14 });            // "are possible"
    const lab1 = LX.note(tl, root, CX, 846, 'inside a group, a cycle is possible', 2.9, cue('order') - 0.3);
    // "That something is a lock order, but a local one."
    const tOrd = cue('order');
    const lab2 = LX.note(tl, root, CX, 846, 'a local lock order', 8.2, null, { color: C.ink });
    void lab1;

    // "The type of a group reference lists its locks, in order.": the picture moves up, small and dim; the type
    const tList = cue('list');
    p.hide(['A', 'B', 'A1', 'A3', 'B1', 'B3'], tList - 0.3, 0.35);
    fadeOut(tl, lab2, tList - 0.3, 0.3);
    p.to({ s: 0.6, y: -110 }, tList - 0.1, 0.8); p.fade(0.4, tList - 0.1, 0.8);
    // the group's type, the paper's Lock_G⟨τ₁, …, τₙ⟩: every entry with its two bits (the upper ones variables:
    // owner or client does not matter here; the lower ones 0: all closed)
    const TY = 560, TS = 64;
    const gt = LX.lockType(tl, root, 1027, TY, { size: TS, align: 'center',
      entries: [1, 2, 3].map(i => ({ a: 'a' + LX.sub(i), b: 0 })) });
    const slots = [0, 1, 2].map(i => gt.entryX(i));
    const tType = tList + 0.6;                                             // "of a group reference"
    gt.show(tType);
    gt.entries.forEach((e, i) => e.els.forEach(x => fadeIn(tl, x, 11.1 + i * 0.25, 0.5, 14)));   // "lists its locks"
    LX.note(tl, root, 1027, 720, "the type lists the group's locks, in order, each with its bits", 12.3, 14.9);

    // "A lock may be acquired only if every lock after it in the list is closed."
    const tInc = cue('inc');
    gt.set({ b: 1 }, tInc - 0.1, { i: 1 });                             // the second lock is opened
    const acq = (x, at) => {
      const t = box(root, x - 200, 398, Object.assign(LX.MONO(32), { width: '400px', textAlign: 'center', whiteSpace: 'pre' }), 'acquire');
      fadeIn(tl, t, at, 0.4, 10);
      const a = LX.line(tl, svg, x, 446, x, 548, { at: at + 0.1, dur: 0.4 });
      return { t, a };
    };
    const bad = acq(slots[0], 14.2);                                       // "may be acquired"
    LX.strikeLine(tl, svg, slots[0] - 46, 520, slots[0] + 46, 470, 15.3, { out: cue('so') - 0.3 });   // "only if"
    tl.to(bad.t, { color: C.faint }, 15.3, 0.4);
    tl.to(bad.a.path, { o: 0.35 }, 15.3, 0.4); tl.to(bad.a.head, { o: 0.35 }, 15.3, 0.4);
    LX.note(tl, root, 1027, 720, 'not allowed: a later lock is opened', 15.5, cue('so') - 0.3);
    const good = acq(slots[2], 16.4);                                      // "every lock after it in the list is closed"
    const tk = LX.tick(tl, svg, slots[2] + 62, 492, 40, 17.0);
    gt.set({ b: 1 }, 17.35, { i: 2 });
    fadeOut(tl, bad.t, cue('so') - 0.3, 0.3); bad.a.hide(cue('so') - 0.3);

    // "So within a group, locks are taken in increasing order."
    const tSo = cue('so');
    LX.line(tl, svg, slots[0] - 40, 736, slots[2] + 40, 736, { at: 20.2, dur: 0.9, stroke: C.dim });   // "taken in increasing order"
    LX.note(tl, root, 1027, 756, 'taken in increasing order', 20.6, null);
    void tSo; void good; void tk;
    // "The wait operation has a stricter condition of the same kind."
    const tWait = cue('wait');
    LX.note(tl, root, CX, 846, 'wait: a stricter condition of the same kind', tWait + 0.1, cue('local') - 0.3);
    // "The order belongs to the group. There is no global order"
    const tLoc = cue('local');
    p.fade(1, tLoc + 0.1, 0.6);
    LX.note(tl, root, CX, 846, 'the order belongs to the group: no global order', tLoc + 0.4, null);
    void tOrd;
  });

  // ============================================ grp_c, grp_d ==================================================
  // One scene over both segments: grp_d goes on from grp_c's ring, the same picture at the same place.

  // the growing table (grp_d, from `grow` on), drawn by its own small renderer so that, as the whole figure shrinks
  // to stay on the stage, its outlines and lines keep a legible width (Picture would scale them with everything).
  // It looks exactly like the Picture's ring it takes over from: chopsticks are 56 px cyan squares, philosophers
  // circles of radius 34, both with 3 px outlines at full size, lines 2.5 px.
  // The model: a row is the items between two end chopsticks, [seg, chop, seg, chop, seg]; a seg is a philosopher
  // {p: id} or two parallel rows between the same two chopsticks {A: row, B: row}; the ring is
  // [seg, chop, seg, chop, …, seg, chop] (its last chopstick closes onto its first seg). Each philosopher knows
  // the chopstick it takes first (the earlier one in the group's order).
  function Lace(tl, root, { cx = 960, cy = 570, halfW = 820, halfH = 315 } = {}) {
    const clamp = v => Math.max(0, Math.min(1, v));
    const lerp = (a, b, u) => typeof a === 'number' ? a + (b - a) * u : { x: a.x + (b.x - a.x) * u, y: a.y + (b.y - a.y) * u };
    const track = v0 => ({ v0, keys: [],
      add(t, d, v) { this.keys.push({ t, d, v }); this.keys.sort((a, b) => a.t - b.t); },
      at(t) { let v = this.v0; for (const k of this.keys) { if (k.t > t) break; if (t >= k.t + k.d) { v = k.v; continue; } v = lerp(v, k.v, E.io(clamp((t - k.t) / k.d))); } return v; } });
    const g = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    tl.set(g, { o: 0 }, 0);
    const lsvg = svgLayer(g), nlay = box(g, 0, 0, { width: W + 'px', height: H + 'px' });
    const nodes = new Map(), lines = new Map(), drawn = [], scale = track(1);
    const first = {};
    let ring = [];

    function node(id, kind, pos, at) {
      const wrap = box(nlay, 0, 0, { width: '0px', height: '0px' });
      const body = box(wrap, 0, 0, { width: '0px', height: '0px' });
      const outline = box(body, 0, 0, { border: `3px solid ${kind === 'p' ? C.ink : C.bind}` });
      const rec = { id, kind, wrap, body, outline, pos: track(pos) };
      nodes.set(id, rec);
      tl.set(body, { o: 0 }, 0);
      if (at === 0) tl.set(body, { o: 1 }, 0);
      return rec;
    }
    function line(ph, ch, at, dur = 0.4) {
      const p = el(lsvg, 'path');
      p.setAttribute('fill', 'none'); p.setAttribute('stroke-linecap', 'round'); p.style.stroke = C.ink;
      const rec = { a: ph, b: ch, path: p };
      lines.set(ph + '|' + ch, rec); drawn.push(rec);
      tl.set(p, { o: 0 }, 0);
      if (at === 0) tl.set(p, { o: 1 }, 0); else tl.to(p, { o: 1 }, at, dur, E.out);
      return rec;
    }
    // how far a node's edge is from its centre in the direction (ux, uy), on the stage at scale s
    const reach = (n, ux, uy, s) => n.kind === 'p' ? 34 * s : (28 * s) / Math.max(Math.abs(ux), Math.abs(uy));
    function frame(t) {
      const s = scale.at(t), bw = Math.max(2, 3 * s), lw = Math.max(2, 2.5 * s);
      const P = new Map();
      for (const n of nodes.values()) {
        const p = n.pos.at(t); P.set(n.id, p);
        n.wrap.style.transform = `translate(${p.x.toFixed(2)}px,${p.y.toFixed(2)}px)`;
        const h = n.kind === 'p' ? 34 * s : 28 * s;
        Object.assign(n.outline.style, { left: -h + 'px', top: -h + 'px', width: 2 * h + 'px', height: 2 * h + 'px', borderWidth: bw + 'px',
          borderRadius: n.kind === 'p' ? '50%' : Math.round(Math.max(6, 2 * h * 0.19)) + 'px' });
      }
      for (const l of drawn) {
        const A = P.get(l.a), B = P.get(l.b), L = Math.hypot(B.x - A.x, B.y - A.y), ux = L > 0.5 ? (B.x - A.x) / L : 1, uy = L > 0.5 ? (B.y - A.y) / L : 0;
        const ea = reach(nodes.get(l.a), ux, uy, s) + 2, eb = reach(nodes.get(l.b), ux, uy, s) + 2;
        l.path.setAttribute('d', `M ${(A.x + ux * ea).toFixed(2)} ${(A.y + uy * ea).toFixed(2)} L ${(B.x - ux * eb).toFixed(2)} ${(B.y - uy * eb).toFixed(2)}`);
        l.path.setAttribute('stroke-width', lw.toFixed(2));
      }
    }
    const clk = box(g, 0, 0, { width: '0px', height: '0px' });
    tl.custom(clk, 'clock', (e, t) => frame(t), 0);
    tl.fromTo(clk, { clock: 0 }, { clock: 1e4 }, 0, 1e4, E.lin);

    // ---- the layout: every node on a stadium (two straight runs joined by half circles; a circle when ls = 0),
    // at a distance along it and an offset outwards from it; the two rows of a pair at offsets ±w around their
    // parent's (80, then 50), spread over the same stretch, so they run parallel and never cross
    const OFF = [80, 50, 32];
    const len = seg => seg.p ? 2 : Math.max(rowLen(seg.A), rowLen(seg.B));
    const rowLen = row => row.reduce((a, it) => a + (typeof it === 'string' ? 0 : len(it)), 0);
    function layout({ step, ls, shift = 0, ease = true }) {
      const tot = rowLen(ring), per = tot * step, re = (per - 4 * ls) / (2 * Math.PI), out = new Map();
      const pt = (u, d) => {
        u = ((u % per) + per) % per;
        let bx, by, nx, ny;
        const arc = (ccx, th) => { nx = Math.cos(th); ny = Math.sin(th); bx = ccx + re * nx; by = re * ny; };
        if (u < ls) { bx = u; by = -re; nx = 0; ny = -1; }
        else if (u < ls + Math.PI * re) arc(ls, -Math.PI / 2 + (u - ls) / re);
        else if (u < 3 * ls + Math.PI * re) { bx = ls - (u - ls - Math.PI * re); by = re; nx = 0; ny = 1; }
        else if (u < 3 * ls + 2 * Math.PI * re) arc(-ls, Math.PI / 2 + (u - 3 * ls - Math.PI * re) / re);
        else { bx = -ls + (u - 3 * ls - 2 * Math.PI * re); by = -re; nx = 0; ny = -1; }
        return { x: bx + d * nx, y: by + d * ny };
      };
      const place = (row, u0, u1, d, lvl) => {
        const k = (u1 - u0) / rowLen(row);
        let u = u0;
        for (const it of row) {
          if (typeof it === 'string') { out.set(it, pt(u, d)); continue; }
          if (it.p) { out.set(it.p, pt(u + k, d)); u += 2 * k; continue; }
          const L = len(it) * k;
          place(it.A, u, u + L, d + OFF[lvl], lvl + 1); place(it.B, u, u + L, d - OFF[lvl], lvl + 1);
          u += L;
        }
      };
      const u0 = -len(ring[0]) * step / 2 + shift * step;
      place(ring, u0, u0 + per, 0, 0);
      return ease ? relax(out) : out;
    }
    // the structural layout, eased: lines pull towards their length there (at least 92), nodes closer than 120
    // push apart, nodes push away from lines that pass close by, and every node is held loosely at its place
    function relax(home) {
      const ids = [...home.keys()], P = new Map(ids.map(id => [id, { x: home.get(id).x, y: home.get(id).y }]));
      const ls = [...lines.values()].map(l => ({ a: l.a, b: l.b, L: Math.max(92, Math.hypot(home.get(l.a).x - home.get(l.b).x, home.get(l.a).y - home.get(l.b).y)) }));
      for (let it = 0; it < 300; it++) {
        const F = new Map(ids.map(id => [id, { x: 0, y: 0 }]));
        const push = (id, fx, fy) => { const f = F.get(id); f.x += fx; f.y += fy; };
        for (const l of ls) {
          const a = P.get(l.a), b = P.get(l.b), dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy) || 1, f = 0.15 * (d - l.L);
          push(l.a, f * dx / d, f * dy / d); push(l.b, -f * dx / d, -f * dy / d);
        }
        for (let i = 0; i < ids.length; i++) for (let j = i + 1; j < ids.length; j++) {
          const a = P.get(ids[i]), b = P.get(ids[j]), dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy) || 1;
          if (d < 120) { const f = 0.25 * (120 - d); push(ids[i], -f * dx / d, -f * dy / d); push(ids[j], f * dx / d, f * dy / d); }
        }
        for (const l of ls) for (const id of ids) {
          if (id === l.a || id === l.b) continue;
          const a = P.get(l.a), b = P.get(l.b), q = P.get(id), dx = b.x - a.x, dy = b.y - a.y;
          const u = Math.max(0, Math.min(1, ((q.x - a.x) * dx + (q.y - a.y) * dy) / (dx * dx + dy * dy)));
          const cxp = a.x + u * dx, cyp = a.y + u * dy, ex = q.x - cxp, ey = q.y - cyp, d = Math.hypot(ex, ey) || 1;
          if (d < 64) { const f = 0.2 * (64 - d); push(id, f * ex / d, f * ey / d); push(l.a, -f * ex / d * (1 - u), -f * ey / d * (1 - u)); push(l.b, -f * ex / d * u, -f * ey / d * u); }
        }
        for (const id of ids) {
          const h = home.get(id), p = P.get(id), f = F.get(id);
          f.x += 0.02 * (h.x - p.x); f.y += 0.02 * (h.y - p.y);
          const m = Math.hypot(f.x, f.y), k = m > 6 ? 6 / m : 1;
          p.x += f.x * k; p.y += f.y * k;
        }
      }
      return P;
    }
    // the stage positions of a layout, shrunk (never grown) to fit the box; with a check that nothing overlaps
    function fit(lay, name) {
      let mx = 1, my = 1;
      for (const [id, p] of lay) { const r = nodes.get(id).kind === 'p' ? 34 : 28; mx = Math.max(mx, Math.abs(p.x) + r); my = Math.max(my, Math.abs(p.y) + r); }
      const s = Math.min(1, halfW / mx, halfH / my), st = new Map();
      for (const [id, p] of lay) st.set(id, { x: cx + s * p.x, y: cy + s * p.y });
      check(lay, name);
      return { s, st };
    }
    function check(lay, name) {
      const ids = [...lay.keys()], rad = id => nodes.get(id).kind === 'p' ? 34 : 34;
      for (let i = 0; i < ids.length; i++) for (let j = i + 1; j < ids.length; j++) {
        const a = lay.get(ids[i]), b = lay.get(ids[j]);
        if (Math.hypot(a.x - b.x, a.y - b.y) < rad(ids[i]) + rad(ids[j]) + 14) console.warn(`lace ${name}: ${ids[i]} and ${ids[j]} too close`);
      }
      const ls = [...lines.values()].filter(l => !l.gone);
      const segd = (p, a, b) => { const dx = b.x - a.x, dy = b.y - a.y, u = Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / (dx * dx + dy * dy))); return Math.hypot(a.x + u * dx - p.x, a.y + u * dy - p.y); };
      for (const l of ls) for (const id of ids) if (id !== l.a && id !== l.b && segd(lay.get(id), lay.get(l.a), lay.get(l.b)) < rad(id) + 6) console.warn(`lace ${name}: line ${l.a}-${l.b} runs through ${id}`);
      const cr = (p, q, r, s) => { const d = (a, b, c) => (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x); return d(p, q, r) * d(p, q, s) < 0 && d(r, s, p) * d(r, s, q) < 0; };
      for (let i = 0; i < ls.length; i++) for (let j = i + 1; j < ls.length; j++) {
        const A = ls[i], B = ls[j];
        if ([A.a, A.b].some(x => x === B.a || x === B.b)) continue;
        if (cr(lay.get(A.a), lay.get(A.b), lay.get(B.a), lay.get(B.b))) console.warn(`lace ${name}: lines ${A.a}-${A.b} and ${B.a}-${B.b} cross`);
      }
    }

    // where a philosopher sits: the array it is in, its index, and its two neighbouring chopsticks
    function find(pid) {
      let hit = null;
      const visit = (row, L, R, cyc) => row.forEach((it, i) => {
        if (typeof it === 'string' || hit) return;
        const l = i > 0 ? row[i - 1] : (cyc ? row[row.length - 1] : L), r = i < row.length - 1 ? row[i + 1] : R;
        if (it.p === pid) hit = { row, i, L: l, R: r };
        else if (it.A) { visit(it.A, l, r, false); visit(it.B, l, r, false); }
      });
      visit(ring, null, null, true);
      if (!hit) console.warn('lace: no philosopher', pid);
      return hit;
    }

    let cur = null;   // the stage positions now
    return {
      g,
      // the ring of grp_c's five philosophers, at rest where the Picture left it
      start(ringItems, firsts, params, at) {
        ring = ringItems; Object.assign(first, firsts);
        for (const it of ring) if (typeof it === 'string') node(it, 'c', { x: 0, y: 0 }, 0); else node(it.p, 'p', { x: 0, y: 0 }, 0);
        for (const it of ring) if (it.p) { const h = find(it.p); line(it.p, h.L, 0); line(it.p, h.R, 0); }
        const { s, st } = fit(layout(params), 'start');
        for (const [id, p] of st) nodes.get(id).pos.v0 = p;
        scale.v0 = s; cur = st;
        tl.set(g, { o: 1 }, at);
        return st;
      },
      // philosopher pid replaces itself by three (kind 'three') or by two parallel rows of three ('rows'), all
      // between its two chopsticks; it stays next to the chopstick it takes first. tag names the new nodes.
      replace(pid, kind, tag, params, at, dur) {
        const h = find(pid), a = first[pid], b = a === h.L ? h.R : h.L;
        const born = cur.get(pid), add = [];
        const row = (ph, t) => {
          const x1 = t + 'x1', x2 = t + 'x2', q1 = t + 'q1', q2 = t + 'q2';
          for (const [id, k] of [[x1, 'c'], [x2, 'c'], [q1, 'p'], [q2, 'p']]) add.push(node(id, k, born, null));
          if (ph !== pid) add.push(node(ph, 'p', born, null));
          first[ph] = a; first[q1] = x1; first[q2] = b;
          const ls = [[ph, x2], [q1, x1], [q1, x2], [q2, x1], [q2, b]];
          if (ph !== pid) ls.push([ph, a]);
          const r = [{ p: ph }, x2, { p: q1 }, x1, { p: q2 }];
          return { r: a === h.R ? r.reverse() : r, ls };
        };
        // pid keeps its line to the chopstick it takes first; its other line goes
        const old = lines.get(pid + '|' + b);
        tl.to(old.path, { o: 0 }, at - 0.05, 0.3, E.in); old.gone = true; lines.delete(pid + '|' + b);
        const A = row(pid, tag);
        let news = A.ls;
        if (kind === 'three') h.row.splice(h.i, 1, ...A.r);
        else { const B = row(tag + 'c', tag + 'c'); h.row[h.i] = { A: A.r, B: B.r }; news = news.concat(B.ls); }
        for (const [p, c] of news) line(p, c, at + dur * 0.55, dur * 0.45);
        const { s, st } = fit(layout(params), tag);
        for (const [id, p] of st) nodes.get(id).pos.add(at, dur, p);
        scale.add(at, dur, s);
        // the new ones come out of pid, already spread a little the way they will lie
        const pe = st.get(pid);
        for (const n of add) {
          const q = st.get(n.id); n.pos.v0 = { x: born.x + 0.5 * (q.x - pe.x), y: born.y + 0.5 * (q.y - pe.y) };
          tl.set(n.body, { s: 0.5 }, 0); tl.to(n.body, { o: 1, s: 1 }, at + dur * 0.2, dur * 0.7, E.out5);
        }
        cur = st;
        return { a, b, s };
      },
      pulse(id, at) { const n = nodes.get(id); tl.to(n.body, { s: 1.18 }, at, 0.25, E.out); tl.to(n.body, { s: 1 }, at + 0.25, 0.4, E.io); },
      pos: id => cur.get(id),
    };
  }

  scene(['grp_c', 'grp_d'], ({ tl, root, cue, seg }) => {
    const svg = LX.svg(root);
    // ---------------------------------------------------------------------------------------------- grp_c
    // the group: the storyboard's rectangle starts at x = 900, where the code's longest line still is: from 1060
    const GX0 = 1060, GX1 = 1800, GY0 = 200, GY1 = 800, GCX = (GX0 + GX1) / 2, GCY = (GY0 + GY1) / 2;
    const p = new LX.Picture(tl, root);
    p.group('g', GCX, GCY, GX1 - GX0, GY1 - GY0);
    // "Groups can grow and shrink while the program runs."
    const tDyn = cue('dyn');
    p.show('g', tDyn - 0.2);
    p.lock('tmp', GCX, 420, { size: 56 });
    p.show('tmp', 0.95); p.gone('tmp', 1.6);                                // "grow", "shrink"

    // "Here is the philosophers' table, for a number of philosophers chosen at run time."
    const tTab = cue('table');
    const title = LX.note(tl, root, RAIL, 180, 'the dining philosophers', tTab + 0.4, null, { align: 'left' });
    const code = LX.code(tl, root, RAIL, 240, 30, [
      'phil(0, ℓ) = dine(ℓ)',
      'phil(n + 1, ℓ) =',
      '  let ℓ = release[2](newlock[2](ℓ), 42) in',
      '  let ℓ = fork(ℓ, λℓ. dine(droplock[0](ℓ))) in',
      '  phil(n, droplock[1](ℓ))',
    ]);
    code.show(tTab + 0.5, { stagger: 0.1 });

    // the row: chopsticks c0..c4 at y = 420, philosophers P1..P4 under the gaps, P5 (the program itself) above
    const CY = 420, PY = 600, cxs = [1140, 1285, 1430, 1575, 1720];
    const CS = 56, PR = 34, thin = { width: 2.5 };
    cxs.forEach((x, i) => p.lock('c' + i, x, CY, { size: CS }));
    for (let i = 1; i <= 4; i++) p.thread('P' + i, (cxs[i - 1] + cxs[i]) / 2, PY, { r: PR });
    p.thread('P5', 1430, 280, { r: PR });
    // P_i sits between c_(i-1) and c_i: its line 'a' goes to the earlier one, 'b' to the later one; P5, who
    // closes the ring, has 'a' to c0 and 'b' to c4
    for (let i = 1; i <= 4; i++) p.ref(`P${i}a`, 'P' + i, 'c' + (i - 1), thin).ref(`P${i}b`, 'P' + i, 'c' + i, thin);
    p.ref('P5a', 'P5', 'c0', thin).ref('P5b', 'P5', 'c4', thin);

    // the program's view: a comb over the row, a tooth for each chopstick its reference sees
    const BY = 344, span = cxs[4] - cxs[0];
    const bar = box(root, cxs[0] - 2, BY - 2, { width: span + 4 + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: '2px center' });
    tl.set(bar, { o: 0, sx: 0 }, 0);
    const teeth = cxs.map(x => { const e = box(root, x - 2, BY - 2, { width: '4px', height: '38px', borderRadius: '2px', background: C.dim, transformOrigin: 'center top' }); tl.set(e, { o: 0, sy: 0 }, 0); return e; });
    const reachTo = (i, at, dur = 0.4) => tl.to(bar, { sx: (cxs[i] - cxs[0] + 4) / (span + 4) }, at, dur, E.io);
    const grab = (i, at) => { tl.set(teeth[i], { o: 1 }, at); tl.to(teeth[i], { sy: 1 }, at, 0.3, E.out5); };
    const letGo = (i, at) => { tl.to(teeth[i], { sy: 0 }, at, 0.3, E.in); tl.set(teeth[i], { o: 0 }, at + 0.3); };
    const view = box(root, cxs[0] - 2, BY - 56, Object.assign(LX.LABEL(32), { whiteSpace: 'pre' }), "the program's view");

    // "Each chopstick is a lock. Think of the chopsticks as a line."
    const tLine = cue('line');
    p.show(['c0', 'c1'], tLine + 0.2, { stagger: 0.15 });                  // "Each chopstick is a lock"
    p.show('P1', 11.5); p.show(['P1a', 'P1b'], 11.9, { stagger: 0.12 });   // "Think of the chopsticks as a line"

    // "The program adds a chopstick at the end of the line, and starts a philosopher between the last two."
    const tAdd = cue('add');
    code.light([1, 2, 3, 4], tAdd - 0.2, { others: 0.4 });
    code.light(2, 13.95);
    p.show('c2', 14.4);                                                     // "adds a chopstick"
    tl.set(bar, { o: 1 }, 15.15); reachTo(2, 15.15, 0.5);
    grab(0, 15.25); grab(1, 15.35); grab(2, 15.45);                        // "at the end of the line"
    fadeIn(tl, view, 15.55, 0.5, 10);
    code.light(3, 16.45);
    p.show('P2', 16.95); p.show(['P2a', 'P2b'], 17.8, { stagger: 0.25 }); // "a philosopher between the last two"

    // "Then it drops its reference to the one before last, and repeats."
    const tAg = cue('again');
    code.light(4, tAg - 0.2);
    letGo(1, 20.1);                                                         // "drops"
    const rep = (i, t) => {                                                 // add chopstick i and philosopher i
      p.show('c' + i, t);
      reachTo(i, t + 0.15, 0.35); grab(i, t + 0.3);
      p.show('P' + i, t + 0.4); p.show([`P${i}a`, `P${i}b`], t + 0.55, { stagger: 0.1, dur: 0.35 });
      letGo(i - 1, t + 1.0);
    };
    code.light([2, 3, 4], 22.3, { others: 0.4 });
    rep(3, 22.4); rep(4, 23.25);                                            // "and repeats"

    // "At the end, one more philosopher dines with the first chopstick and the last, and the line becomes a ring."
    const tClose = cue('close');
    tl.to(bar, { o: 0 }, 24.45, 0.4, E.in); for (const e of teeth) tl.to(e, { o: 0 }, 24.45, 0.4, E.in);
    fadeOut(tl, view, 24.45, 0.4);
    code.light(0, tClose + 0.6);
    p.show('P5', 24.9);                                                     // "one more philosopher"
    p.show('P5a', 26.55);                                                   // "the first chopstick"
    p.show('P5b', 27.6);                                                    // "and the last"
    // "the line becomes a ring": everything glides onto a circle, chopsticks and philosophers alternating; going
    // clockwise from the top: P5, c4, P4, c3, P3, c2, P2, c1, P1, c0
    const ringOrder = ['P5', 'c4', 'P4', 'c3', 'P3', 'c2', 'P2', 'c1', 'P1', 'c0'];
    const onRing = (ccx, ccy, R, at, dur) => ringOrder.forEach((id, i) => {
      const a = (-90 + 36 * i) * Math.PI / 180;
      p.move(id, ccx + R * Math.cos(a), ccy + R * Math.sin(a), at, { dur });
    });
    onRing(GCX, GCY, 230, 28.7, 1.4);

    // "Each philosopher's reference shows only two locks of the group."
    const tView = cue('view');
    const lit = ['P4', 'c3', 'c4', 'P4a', 'P4b'];
    const all = p.order.filter(id => id !== 'g' && id !== 'tmp' && p.item(id).kind !== 'chip');
    const rest = all.filter(id => !lit.includes(id));
    p.dim(rest, 0.3, tView + 0.15, 0.5);
    code.light(3, tView + 0.15);
    const sees = LX.note(tl, root, CX, 830, 'each reference sees two locks of the group', 31.3, null);
    p.pulse('c3', 32.7); p.pulse('c4', 32.7);                               // "two locks"

    // ---------------------------------------------------------------------------------------------- grp_d
    const D = seg('grp_d'), at = s => D + s;                                // at(s): s seconds into grp_d
    // the labels at the right of the ring, left-aligned at x = 1160, a line every 42 px
    const NX = 1160;
    const note = (lines, y, t, out, o = {}) => [].concat(lines).map((s, i) => LX.note(tl, root, NX, y + 42 * i, s, t + 0.08 * i, out, Object.assign({ align: 'left' }, o)));
    const dimEls = (els, o, t) => els.forEach(e => tl.to(e, { o }, t, 0.5));

    // "Why can this ring not deadlock?": the code and the group leave; the ring glides left and grows
    const tWhy = cue('why');
    code.hide(tWhy - 0.2); fadeOut(tl, title, tWhy - 0.2, 0.4); fadeOut(tl, sees, tWhy - 0.2, 0.4);
    p.hide('g', tWhy - 0.2, 0.5);
    p.dim(rest, 1, tWhy, 0.5);
    const RX = 760, RY = 500, RR = 280;
    onRing(RX, RY, RR, tWhy + 0.1, 1.2);

    // "The group's order is the order of the line: the first chopstick, the second, and so on.": the chopsticks
    // are numbered, 0 the first of the line
    const ordL = note(["the group's order:", 'the order of the line'], 200, at(3.4), null, { color: C.ink });
    const nums = [0, 1, 2, 3, 4].map(i => p.label('c' + i, String(i), [at(5.65), at(6.85), at(7.6), at(7.75), at(7.9)][i], { side: 'center', font: 'mono', size: 30, color: C.bind }));
    nums.forEach((e, i) => p.pulse('c' + i, [at(5.65), at(6.85), at(7.6), at(7.75), at(7.9)][i]));

    // "Every philosopher has to take the earlier one of its two chopsticks first.": a small arrowhead on the line
    // to the chopstick each must take first; P1..P4 first (P5's comes with "last")
    const heads = {};
    const ringPos = id => { const a = (-90 + 36 * ringOrder.indexOf(id)) * Math.PI / 180; return { x: RX + RR * Math.cos(a), y: RY + RR * Math.sin(a) }; };
    const head = (ph, ch, t) => {
      const A = ringPos(ph), B = ringPos(ch), L = Math.hypot(B.x - A.x, B.y - A.y), ux = (B.x - A.x) / L, uy = (B.y - A.y) / L;
      const e = 28 / Math.max(Math.abs(ux), Math.abs(uy)) + 3, tx = B.x - ux * e, ty = B.y - uy * e, bx = tx - ux * 20, by = ty - uy * 20;
      const h = el(svg, 'path');
      h.setAttribute('d', `M ${tx} ${ty} L ${bx - uy * 9} ${by + ux * 9} L ${bx + uy * 9} ${by - ux * 9} Z`);
      h.style.fill = C.ink; h.setAttribute('stroke', 'none');
      tl.set(h, { o: 0 }, 0); tl.to(h, { o: 1 }, t, 0.35, E.out);
      heads[ph] = h;
      return h;
    };
    const tEach = cue('each');
    dimEls(ordL, 0.45, tEach);
    const eachL = note('earlier chopstick first', 300, at(10.5), null);
    for (let i = 1; i <= 4; i++) head('P' + i, 'c' + (i - 1), at(10.6) + 0.18 * (i - 1));

    // "For a philosopher inside the line, that is the one on its left.": the four pulse one after the other; their
    // arrows all turn the same way round the ring
    for (let i = 1; i <= 4; i++) p.pulse('P' + i, at(13.7) + 0.3 * (i - 1));
    for (let i = 1; i <= 4; i++) p.pulse(`P${i}a`, at(16.45));

    // "But the philosopher who closed the ring sits between the last chopstick and the first. It has to take the
    // first one first: the one on its right."
    const tLast = cue('last');
    dimEls(eachL, 0.45, tLast);
    p.pulse('P5', at(17.95));
    p.pulse('c4', at(20.5)); p.pulse('c0', at(21.6));                      // "the last chopstick and the first"
    head('P5', 'c0', at(23.3));                                             // "take the first one first"
    p.pulse('P5a', at(25.15));                                              // "the one on its right"
    const lastL = note(['the one who closed the ring', 'reaches the other way'], 560, at(24.6), null, { color: C.ink });

    // "So one philosopher reaches the other way round, and the circle of waiting cannot close.": the attempt at a
    // deadlock. P1..P4 each take their first chopstick (0, 1, 2, 3 held); P5 waits for 0 and holds nothing, P1..P3
    // wait for their second; so chopstick 4 is free: P4 takes it and can eat.
    const tBreak = cue('break');
    dimEls(lastL, 0.45, tBreak);
    for (let i = 1; i <= 4; i++) { const t = tBreak + 0.15 + 0.3 * (i - 1); p.open(`P${i}a`, t); tl.to(heads['P' + i], { fill: C.pat }, t, 0.35); }
    p.waiting('P5a', at(28.1), { out: at(31.9) });                        // "reaches the other way"
    for (let i = 1; i <= 3; i++) p.waiting(`P${i}b`, at(28.4) + 0.15 * (i - 1), { out: at(31.9) });
    p.pulse('c4', at(29.0));                                                // chopstick 4 is free
    p.open('P4b', at(29.4));
    const canRing = p.can('P4', at(29.8), { out: at(31.9) });
    const canL = p.label('P4', 'can eat', at(29.9), { side: 'right', color: C.good, out: at(31.9) });
    const breakL = note(['the circle of waiting', 'cannot close'], 680, at(30.3), null, { color: C.ink });
    void canRing; void canL;

    // "That is a well-known remedy.": everything back to ink; the labels leave
    const tOld = cue('old');
    for (let i = 1; i <= 4; i++) { p.close(`P${i}a`, at(31.9)); tl.to(heads['P' + i], { fill: C.ink }, at(31.9), 0.35); }
    p.close('P4b', at(31.9));
    for (const e of [...ordL, ...eachL, ...lastL, ...breakL]) fadeOut(tl, e, at(31.9), 0.35);
    const oldL = note('a well-known remedy', 300, tOld + 0.6, at(35.3));

    // "What is new is that the type checker enforces it, with local checks only: each philosopher's type mentions
    // just its own two locks.": P4 and its two chopsticks light, and its type, a group reference to two of them
    const hereL = note(['here: enforced by the types,', 'with local checks'], 300, at(35.6), at(43.15), { color: C.ink });
    const lit4 = ['P4', 'c3', 'c4', 'P4a', 'P4b'];
    p.dim(all.filter(id => !lit4.includes(id)), 0.3, at(39.3), 0.5);
    dimEls(['P1', 'P2', 'P3', 'P5'].map(k => heads[k]), 0.3, at(39.3));
    const ty = LX.lockType(tl, root, NX, 420, { size: 44, entries: [{ of: 'int', a: 'a₁', b: 0 }, { of: 'int', a: 'a₂', b: 0 }] });
    ty.show(at(39.55));
    p.pulse('c3', at(41.8)); p.pulse('c4', at(42.1)); ty.pulse('type', at(41.9));   // "its own two locks"

    // "The table can even grow while they eat.": the labels, numbers and arrows leave; the ring moves back to the
    // centre of the stage, where the growing table takes it over
    const tGrow = cue('grow');
    ty.hide(tGrow - 0.15); void oldL; void hereL;
    for (const e of nums) tl.to(e, { o: 0 }, tGrow - 0.15, 0.3, E.in);
    for (const k in heads) tl.to(heads[k], { o: 0 }, tGrow - 0.15, 0.3, E.in);
    for (const id of all) tl.to(p.item(id).kind === 'ref' ? p.item(id).g : p.item(id).body, { o: 1 }, tGrow - 0.15, 0.5);   // not their labels
    const LXc = 960, LYc = 570;
    onRing(LXc, LYc, RR, tGrow + 0.1, 1.1);
    const tSwap = tGrow + 1.4;
    tl.set(p.g, { o: 0 }, tSwap);
    const lace = Lace(tl, root, { cx: LXc, cy: LYc });
    const ringItems = [{ p: 'P5' }, 'c4', { p: 'P4' }, 'c3', { p: 'P3' }, 'c2', { p: 'P2' }, 'c1', { p: 'P1' }, 'c0'];
    lace.start(ringItems, { P1: 'c0', P2: 'c1', P3: 'c2', P4: 'c3', P5: 'c0' }, { step: 176, ls: 0, ease: false }, tSwap);

    // "Change one line, and a philosopher who has eaten replaces itself by three.": top left, the change
    const tThree = cue('three'), CODE_Y = 150, CW = charWidth(34);
    const mono34 = (x, s, t) => { const e = box(root, x, CODE_Y, Object.assign(LX.MONO(34), { whiteSpace: 'pre' })); LX.lline(e, 0, 0, s, LX.MONO(34)); return fadeIn(tl, e, t, 0.5, 10); };
    const ell = ['ℓ', C.bind];
    const c1 = mono34(RAIL, ['dine(', ell, ')'], tThree - 0.15);
    const AX0 = RAIL + 7 * CW + 26, AX1 = AX0 + 70;
    LX.line(tl, svg, AX0, CODE_Y + 22, AX1, CODE_Y + 22, { at: at(46.5), dur: 0.35, head: 12 });
    const c2 = mono34(AX1 + 22, ['phil(2, ', ell, ')'], at(46.75));
    const changed = LX.note(tl, root, RAIL, 210, 'one line changed', at(47.0), null, { align: 'left' });
    lace.pulse('P3', at(47.5));                                             // "a philosopher who has eaten"
    lace.replace('P3', 'three', 'a', { step: 126, ls: 0 }, at(48.85), 0.9); // "replaces itself by three"

    // "Change it again, and it replaces itself by two rows of three, which share its two chopsticks."
    const tFrac = cue('frac');
    fadeOut(tl, c2, tFrac - 0.25, 0.25);
    const c3 = mono34(AX1 + 22, ['phil(2, fork(', ell, ', λ', ell, '. phil(2, ', ell, ')))'], tFrac + 0.05);
    lace.pulse('P5', at(52.3));
    const r2 = lace.replace('P5', 'rows', 'b', { step: 110, ls: 120 }, at(53.4), 1.0);   // "two rows of three"
    lace.pulse(r2.a, at(55.4)); lace.pulse(r2.b, at(55.4));                 // "share its two chopsticks"

    // "The table then grows in a branching pattern that nobody can predict, with chopsticks shared by more and
    // more philosophers.": more such replacements, each faster, at places nobody chose
    const wild = [['aq1', 'd', at(58.0), 0.9], ['bq1', 'e', at(59.3), 0.8], ['P5', 'f', at(60.45), 0.7], ['dq1', 'h', at(61.45), 0.6], ['P3', 'k', at(62.35), 0.55]];
    const wildP = [{ step: 104, ls: 260 }, { step: 100, ls: 380 }, { step: 98, ls: 470 }, { step: 96, ls: 560 }, { step: 94, ls: 640 }];
    wild.forEach(([pid, tag, t, d], i) => { lace.pulse(pid, t - 0.3); lace.replace(pid, 'rows', tag, wildP[i], t, d); });

    // "The same local checks still guarantee that it never deadlocks."
    const tStill = cue('still');
    for (const e of [c1, c3, changed, svg]) fadeOut(tl, e, tStill - 0.3, 0.3);
    const svg2 = LX.svg(root);
    LX.tick(tl, svg2, RAIL + 22, CODE_Y + 24, 44, tStill + 0.15);
    LX.note(tl, root, RAIL + 66, CODE_Y + 6, 'still no deadlock: the same local checks', tStill + 0.3, null, { align: 'left', color: C.good });
  });

  // ============================================ limits ========================================================
  scene('limits', ({ tl, root, cue }) => {
    const svg = LX.svg(root);
    LX.note(tl, root, RAIL, 130, 'limits', cue('lim') - 0.2, null, { align: 'left', color: C.ink });
    const DX = 200, LXX = 640, rowY = i => 260 + 160 * i;
    const rows = [];
    const label = (i, text, at) => {
      const lines = [].concat(text), lh = 40, y0 = rowY(i) - (lines.length * lh) / 2 + 1;
      const e = box(root, LXX, y0, { width: '1300px', height: lines.length * lh + 'px' });
      lines.forEach((t, k) => box(e, 0, k * lh, Object.assign(LX.LABEL(32), { color: C.ink, whiteSpace: 'pre', lineHeight: lh + 'px' }), t));
      fadeIn(tl, e, at, 0.5, 10);
      rows[i] = (rows[i] || []).concat(e);
      return e;
    };
    const add = (i, e) => { rows[i] = (rows[i] || []).concat(e); return e; };
    const stepBack = (i, at) => { for (let k = 0; k < i; k++) for (const e of rows[k] || []) tl.to(e, { o: 0.45 }, at, 0.5); };

    // "How many locks of a group one reference can see is fixed by its type."
    const tStat = cue('stat');
    const ty = LX.lockType(tl, root, DX, rowY(0) - 26, { size: 40, entries: [0, 1, 2].map(() => ({ a: 0, b: 0 })) });
    ty.show(tStat - 0.1); add(0, ty.g);
    label(0, ['how many locks a reference sees:', 'fixed by its type'], 4.9);

    // "Shared data cannot be an arbitrary acyclic graph: two paths to the same lock could become two references to it."
    const tDag = cue('dag');
    stepBack(1, tDag - 0.2);
    const dm = new LX.Picture(tl, root, { size: 36, line: 2.5, names: false });
    const y1 = rowY(1);
    dm.lock('t', 320, y1 - 62).lock('l', 240, y1).lock('r', 400, y1).lock('b', 320, y1 + 62)
      .ref('tl', 't', 'l').ref('tr', 't', 'r').ref('lb', 'l', 'b').ref('rb', 'r', 'b');
    dm.show(['t', 'l', 'r', 'b'], tDag - 0.1, { stagger: 0.08 });
    dm.show(['tl', 'lb'], 10.35, { stagger: 0.25 }); dm.show(['tr', 'rb'], 10.55, { stagger: 0.25 });   // "two paths"
    dm.pulse('b', 11.35);                                                   // "the same lock"
    add(1, dm.g);
    label(1, 'two paths to one lock: not expressible', 12.2);

    // "And there is no escape hatch yet, like Rust's unsafe: what it would have to promise is an open question."
    const tUn = cue('unsafe');
    stepBack(2, tUn - 0.2);
    label(2, 'no escape hatch yet: an open question', tUn + 0.4);
    add(2, fadeIn(tl, mono(root, DX, rowY(2) - 27, 'unsafe', 40), 17.2, 0.5, 12));

    // "The paper presents all this as a small model language, by choice"
    const tCalc = cue('calc');
    stepBack(3, tCalc - 0.2);
    const lam = box(root, DX, rowY(3) - 42, Object.assign(LX.SERIF(64), { whiteSpace: 'pre', lineHeight: 1.3 }), 'λ');
    add(3, fadeIn(tl, lam, tCalc + 0.1, 0.5, 12));
    label(3, 'a small model language, by choice', 23.4);
    void svg;
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
window.CAPTIONS = [[0.8, 3.16, "Here is a short program in Rust."], [3.2, 5.6, "It creates a lock, a mutex,"], [5.64, 7.24, "holding the number one."], [7.28, 10.04, "It makes a second reference to the same mutex,"], [10.08, 13.12, "and passes both to a function that swaps the contents"], [13.16, 14.76, "of two mutexes."], [14.8, 16.76, "The compiler accepts it."], [16.8, 19.0, "Run it, and it never finishes."], [19.04, 21.24, "The function locks its first argument,"], [21.28, 22.76, "and then its second."], [22.8, 24.44, "But they are the same lock,"], [24.48, 26.44, "so the thread waits for itself,"], [26.48, 27.48, "forever."], [27.52, 29.32, "That is a deadlock."], [29.36, 32.04, "A similar program fails in another way:"], [32.08, 34.76, "it stores the second reference inside the mutex"], [34.8, 35.96, "itself."], [36.0, 38.48, "Now the mutex keeps itself alive,"], [38.52, 40.84, "and its memory is never freed."], [40.88, 43.72, "Rust's types rule out data races."], [43.76, 45.48, "They do not rule out deadlocks,"], [45.52, 46.76, "or leaks."], [46.8, 49.32, "This video is about a small model language with"], [49.36, 52.68, "locks, in which the type checker rules out both."], [52.72, 55.24, "We will see the single rule behind it,"], [55.28, 57.48, "the lock operations that keep the rule,"], [57.52, 60.36, "and how it extends to programs that need a cycle,"], [60.4, 62.82, "like the dining philosophers."], [62.92, 64.72, "Here is what is coming."], [64.76, 68.16, "First, what deadlocks and leaks have in common."], [68.2, 69.68, "Then the rule:"], [69.72, 72.08, "a picture of the program that must never contain"], [72.12, 73.36, "a cycle."], [73.4, 76.48, "Then the lock operations, and why each one keeps"], [76.52, 77.8, "the rule."], [77.84, 79.76, "Then who frees a lock."], [79.8, 81.92, "Then programs written this way,"], [81.96, 84.0, "the theorem, and lock groups,"], [84.04, 87.1, "for when a cycle is what you want."], [87.52, 91.78, "Higher-order leak and deadlock free locks."], [93.78, 95.74, "Look again at the swap."], [95.78, 97.5, "The function is fine:"], [97.54, 100.58, "locking two mutexes and exchanging their contents"], [100.62, 102.62, "is a reasonable thing to do."], [102.66, 104.62, "The caller is fine too:"], [104.66, 107.42, "making a second reference is what references are"], [107.46, 107.98, "for."], [108.02, 110.38, "Only the combination fails."], [110.42, 113.22, "So a deadlock is not a mistake at one place in"], [113.26, 114.49, "the program."], [114.53, 116.62, "To see it, draw a picture."], [116.66, 118.7, "A circle for each thread."], [118.74, 120.7, "A square for each lock."], [120.74, 123.02, "A line when the thread holds a reference to the"], [123.06, 123.98, "lock."], [124.02, 127.1, "Our thread holds two references to one lock:"], [127.14, 129.74, "two lines between the same two points."], [129.78, 131.66, "We count that as a cycle:"], [131.7, 133.45, "you can go out along one line,"], [133.49, 136.1, "and come back along the other."], [136.14, 140.18, "The classic deadlock has two threads and two locks."], [140.22, 143.62, "One thread takes the first lock and then the second."], [143.66, 146.74, "The other takes the second and then the first."], [146.78, 148.9, "Each can end up holding one lock,"], [148.94, 150.86, "and waiting for the other."], [150.9, 152.02, "In the picture:"], [152.06, 154.74, "four lines that close a loop."], [154.78, 156.98, "With three threads and three locks,"], [157.02, 159.65, "any two threads share only one lock,"], [159.69, 162.42, "and still they can wait for each other around a"], [162.46, 163.06, "ring."], [163.1, 164.38, "And the leak:"], [164.42, 166.98, "a lock whose contents hold a reference to the lock"], [167.02, 168.18, "itself."], [168.22, 170.66, "Draw that reference as a line too."], [170.7, 173.7, "It goes from the lock back to itself."], [173.74, 177.42, "Every one of these failures is a cycle."], [177.46, 180.22, "The usual defence is a lock order:"], [180.26, 182.22, "number all the locks in the program,"], [182.26, 184.94, "and always take them in increasing order."], [184.98, 187.58, "That works, but the order is global:"], [187.62, 190.46, "every part of the program has to respect the same"], [190.5, 191.42, "order."], [191.46, 193.42, "This paper does something else."], [193.46, 196.3, "It puts no restriction on how a thread uses the"], [196.34, 197.66, "locks it has."], [197.7, 200.06, "It may take any of them, at any time,"], [200.1, 201.5, "in any order."], [201.54, 206.44, "Instead, it restricts how references to locks spread."], [208.26, 209.98, "The rule is this."], [210.02, 212.14, "Draw the threads, the locks,"], [212.18, 214.38, "and a line for every reference:"], [214.42, 217.62, "from a thread to a lock, or from a lock's contents"], [217.66, 219.02, "to another lock."], [219.06, 221.98, "That picture must never contain a cycle."], [222.02, 225.34, "The paper calls the picture the sharing topology."], [225.38, 228.06, "Counting each reference as its own line,"], [228.1, 231.86, "no cycle means, first, that a thread never holds"], [231.9, 234.22, "two references to the same lock."], [234.26, 236.86, "It means that two threads never share more than"], [236.9, 237.98, "one lock."], [238.02, 241.78, "And it rules out the longer rings as well."], [241.82, 243.62, "Why is that enough?"], [243.66, 246.94, "Suppose a thread is waiting to acquire a lock."], [246.98, 249.7, "Some other thread has acquired that lock."], [249.74, 251.86, "That thread is either able to run,"], [251.9, 254.82, "or it is waiting too, for another lock."], [254.86, 256.1, "Follow the chain:"], [256.14, 259.46, "thread, lock, thread, lock."], [259.5, 262.34, "Each step goes along a line of the picture."], [262.38, 264.58, "And it never turns straight back:"], [264.62, 267.26, "a thread that has acquired a lock is not waiting"], [267.3, 268.95, "for that same lock."], [268.99, 270.82, "In a picture without cycles,"], [270.86, 273.38, "such a walk cannot go on forever."], [273.42, 276.26, "It must end at a thread that can run."], [276.3, 278.55, "So whoever is waiting is waiting,"], [278.59, 282.38, "in the end, on something that can move."], [282.42, 284.82, "Locks here are higher-order:"], [284.86, 286.86, "a lock can hold any value,"], [286.9, 289.66, "including references to other locks."], [289.7, 292.7, "That is why the picture has lines from locks to"], [292.74, 293.37, "locks."], [293.41, 295.46, "The rule covers them too:"], [295.5, 296.86, "no cycles."], [296.9, 299.5, "It is also how a lock is handed from one thread"], [299.54, 300.7, "to another."], [300.74, 303.54, "The first thread puts its reference into a lock"], [303.58, 305.42, "that both threads share."], [305.46, 307.58, "The second thread takes it out."], [307.62, 310.94, "Each time, one end of a line moves along another"], [310.98, 314.2, "line, and no cycle appears."], [316.02, 318.06, "Now the operations."], [318.1, 320.06, "New creates a lock."], [320.1, 321.14, "In the picture:"], [321.18, 323.9, "a new square, with a single line to the thread"], [323.94, 325.02, "that made it."], [325.06, 326.38, "No cycle."], [326.42, 329.98, "Acquire takes the lock, and hands over its contents."], [330.02, 331.85, "Release puts contents back,"], [331.89, 333.7, "and gives the lock up."], [333.74, 335.66, "Neither creates a reference."], [335.7, 338.78, "Contents only move along a line that is already"], [338.82, 339.34, "there."], [339.38, 341.26, "And references are linear."], [341.3, 342.99, "A reference cannot be copied,"], [343.03, 345.5, "and it cannot be silently forgotten."], [345.54, 348.22, "So the second reference of the Rust program cannot"], [348.26, 350.18, "be made."], [350.22, 353.54, "So how do two threads ever share a lock?"], [353.58, 354.98, "With fork."], [355.02, 357.94, "Fork starts a new thread, and gives it one new"], [357.98, 360.58, "reference to one lock of the parent."], [360.62, 361.73, "In the picture:"], [361.77, 364.9, "a new circle, joined to its parent through exactly"], [364.94, 366.18, "one lock."], [366.22, 367.94, "Anything else the child gets,"], [367.98, 369.62, "the parent gives up."], [369.66, 372.7, "A new circle joined in one place can never close"], [372.74, 373.86, "a cycle."], [373.9, 376.42, "If fork could share two locks at once,"], [376.46, 378.9, "parent and child would be joined twice,"], [378.94, 380.74, "and that is a cycle."], [380.78, 381.46, "So:"], [381.5, 384.8, "one shared lock for each fork."], [384.92, 386.8, "Notice what is missing."], [386.84, 389.6, "There is no lock order, and no rule about when"], [389.64, 391.36, "a thread may acquire."], [391.4, 393.68, "A thread may take any lock it holds,"], [393.72, 397.04, "in any order, while holding any others."], [397.08, 399.6, "And notice how the rule is enforced."], [399.64, 402.48, "The type checker never looks at the whole picture."], [402.52, 404.88, "It checks one operation at a time,"], [404.92, 406.96, "in one thread at a time."], [407.0, 408.56, "Is a reference being copied,"], [408.6, 409.76, "or forgotten?"], [409.8, 412.48, "Does this fork share more than one lock?"], [412.52, 415.28, "Yet together, these local checks keep a property"], [415.32, 417.0, "of the whole program:"], [417.04, 420.06, "no cycle, anywhere."], [421.88, 423.92, "That takes care of locking."], [423.96, 426.24, "What about getting rid of a lock?"], [426.28, 429.44, "A thread cannot simply drop a lock it has acquired:"], [429.48, 431.68, "everyone else would wait forever."], [431.72, 434.24, "Can it drop a lock it has not acquired?"], [434.28, 437.25, "If every thread did that, the lock would be gone,"], [437.29, 439.04, "and its contents with it."], [439.08, 441.28, "And the contents may be something that must not"], [441.32, 442.56, "be thrown away:"], [442.6, 444.24, "another lock, say."], [444.28, 447.12, "So dropping is wrong either way."], [447.16, 448.48, "The way out:"], [448.52, 450.32, "among the references to a lock,"], [450.36, 452.64, "exactly one is the owner."], [452.68, 454.56, "The others are clients."], [454.6, 456.8, "A client may drop its reference."], [456.84, 458.36, "The owner may not."], [458.4, 460.6, "It must wait."], [460.64, 463.64, "The wait operation blocks until every client has"], [463.68, 465.32, "dropped its reference."], [465.36, 468.24, "Then it removes the lock, and returns its contents"], [468.28, 469.64, "to the owner."], [469.68, 471.08, "Nothing is lost."], [471.12, 473.96, "The type of a reference records two facts,"], [474.0, 475.24, "as two bits."], [475.28, 477.51, "The upper bit is one for the owner,"], [477.55, 479.44, "and zero for a client."], [479.48, 482.12, "The lower bit is one if the lock is opened,"], [482.16, 484.44, "meaning acquired through this reference,"], [484.48, 486.68, "and zero if it is closed."], [486.72, 490.2, "With these two bits, every operation has a type."], [490.24, 493.43, "Acquire takes a reference whose lower bit is zero,"], [493.47, 495.96, "and returns it with that bit set to one,"], [496.0, 497.88, "together with the contents."], [497.92, 500.76, "Release takes a reference whose lower bit is one,"], [500.8, 503.4, "and a value, and returns the reference with the"], [503.44, 505.16, "bit back at zero."], [505.2, 507.48, "Drop takes a closed client:"], [507.52, 508.84, "zero, zero."], [508.88, 511.56, "The wait operation takes a closed owner:"], [511.6, 513.0, "one, zero."], [513.04, 515.0, "It returns the contents."], [515.04, 517.83, "And new returns one, one:"], [517.87, 519.24, "an opened owner."], [519.28, 523.12, "The lock is empty, and must be filled."], [523.16, 525.68, "Fork splits a reference in two,"], [525.72, 528.48, "one for each thread, and it splits the bits as"], [528.52, 529.48, "well."], [529.52, 532.08, "The upper bits of the two halves add up to the"], [532.12, 534.0, "upper bit of the original."], [534.04, 537.25, "So an owner splits into an owner and a client,"], [537.29, 539.68, "and a client into two clients."], [539.72, 542.32, "The lower bits add up in the same way:"], [542.36, 544.0, "if the reference was opened,"], [544.04, 546.08, "exactly one of the two is opened,"], [546.12, 548.72, "and the duty to release goes with it."], [548.76, 550.88, "So the type checker always knows,"], [550.92, 554.2, "for each reference, who must release and who must"], [554.24, 554.72, "wait."], [554.76, 556.64, "And because references are linear,"], [556.68, 559.31, "those duties cannot be dropped on the floor."], [559.35, 560.99, "They can only be carried out,"], [561.03, 563.82, "or handed to someone else."], [565.64, 567.76, "What can be written this way?"], [567.8, 570.96, "A lock with no clients is a mutable cell."], [571.0, 574.0, "Acquire reads it, release writes it,"], [574.04, 576.92, "and wait takes the value out for good."], [576.96, 579.36, "With one client, it is a future."], [579.4, 581.15, "The parent creates a lock,"], [581.19, 583.92, "which is opened, and forks a child."], [583.96, 585.92, "Fork splits the reference:"], [585.96, 587.6, "the parent keeps the owner,"], [587.64, 590.24, "closed, and the child gets the client,"], [590.28, 591.12, "opened."], [591.16, 593.88, "The child cannot drop its reference until it has"], [593.92, 596.0, "released a value into the lock."], [596.04, 598.08, "That value is its result."], [598.12, 600.64, "The parent calls wait, and gets it."], [600.68, 603.12, "The child cannot finish without delivering,"], [603.16, 606.68, "or handing that duty to someone else."], [606.72, 609.96, "With several clients, it is shared data."], [610.0, 612.2, "The parent puts a value in a lock,"], [612.24, 615.16, "forks three children with a client reference each,"], [615.2, 616.52, "and waits."], [616.56, 619.24, "Each child may acquire and release as often as"], [619.28, 620.76, "it likes."], [620.8, 622.44, "Here is a bank."], [622.48, 625.08, "Each account is a lock holding a balance,"], [625.12, 628.0, "shared between the bank and one customer."], [628.04, 631.4, "To transfer money, the bank acquires two accounts,"], [631.44, 634.44, "changes both balances, and releases them."], [634.48, 637.08, "It does not matter which it takes first."], [637.12, 638.68, "Whatever the customers do,"], [638.72, 643.36, "the picture has no cycle, so nothing can deadlock."], [643.4, 645.92, "Shared data can be recursive."], [645.96, 648.64, "In this tree, every node is a lock,"], [648.68, 651.36, "holding a value and owning its children."], [651.4, 654.08, "A thread with a client reference to a node can"], [654.12, 655.84, "step down the tree:"], [655.88, 658.84, "it acquires the node, exchanges its reference for"], [658.88, 661.15, "a client reference to one of the children,"], [661.19, 662.8, "and releases the node."], [662.84, 665.28, "So several threads can work in different parts"], [665.32, 667.9, "of the tree at once."], [668.22, 670.42, "Message passing comes with all this,"], [670.46, 671.54, "for free."], [671.58, 674.54, "A session type describes a conversation over a"], [674.58, 675.38, "channel:"], [675.42, 678.66, "send a number, then receive a yes or no,"], [678.7, 679.94, "then stop."], [679.98, 682.39, "Each end of the channel has such a type,"], [682.43, 684.1, "and the two fit together:"], [684.14, 687.3, "where one end sends, the other receives."], [687.34, 689.26, "Now recall the future."], [689.3, 691.86, "It is a channel for a single message."], [691.9, 694.22, "The thread with the opened client reference has"], [694.26, 695.62, "to put a value in:"], [695.66, 697.14, "it is the sender."], [697.18, 699.62, "The thread with the closed owner reference waits"], [699.66, 700.82, "for that value:"], [700.86, 702.42, "it is the receiver."], [702.46, 705.78, "So sending is a lock type with the bits zero,"], [705.82, 708.98, "one, and receiving is a lock type with the bits"], [709.02, 711.42, "one, zero."], [711.46, 713.1, "For a longer conversation,"], [713.14, 715.66, "each message carries one more thing:"], [715.7, 717.47, "a reference to a fresh lock,"], [717.51, 719.5, "for the rest of the conversation."], [719.54, 722.54, "To send, a thread creates the fresh lock,"], [722.58, 725.42, "puts the value and one reference to that lock into"], [725.46, 728.54, "the old lock, and keeps the other reference."], [728.58, 731.98, "To receive, the other thread waits on the old lock."], [732.02, 735.18, "It gets the value, and its end of the new lock."], [735.22, 737.58, "So a channel is a chain of locks,"], [737.62, 739.02, "each used once."], [739.06, 741.82, "And every session type is a lock type."], [741.86, 744.46, "Nothing has to be added to the type system."], [744.5, 747.34, "So the guarantee covers channels too:"], [747.38, 750.3, "programs with session types cannot deadlock,"], [750.34, 752.46, "and channels can be stored in locks,"], [752.5, 754.86, "and locks sent over channels."], [754.9, 756.22, "One caveat:"], [756.26, 759.66, "done literally, every send starts a tiny thread,"], [759.7, 762.74, "so a real implementation would still provide channels"], [762.78, 764.68, "directly."], [766.5, 769.46, "Now the guarantee, stated properly."], [769.5, 771.5, "Take a program that type-checks,"], [771.54, 774.18, "and run it for any number of steps."], [774.22, 777.42, "Then every thread is in one of two situations."], [777.46, 779.18, "It can take a step."], [779.22, 782.46, "Or it is waiting, and what it waits for leads,"], [782.5, 785.58, "along a chain, to something that can take a step."], [785.62, 788.7, "The paper calls this full reachability."], [788.74, 790.46, "It rules out deadlock:"], [790.5, 792.94, "not only the whole program being stuck,"], [792.98, 796.38, "but any group of threads being stuck among themselves."], [796.42, 798.62, "The same holds for every lock,"], [798.66, 800.46, "and that rules out leaks:"], [800.5, 803.34, "no lock is ever cut off, with nothing left that"], [803.38, 804.38, "can reach it."], [804.42, 806.22, "And when all threads have finished,"], [806.26, 808.66, "no lock is left."], [808.7, 811.06, "The proof follows the picture."], [811.1, 812.66, "An invariant says:"], [812.7, 816.58, "everything is well typed, the picture has no cycle,"], [816.62, 820.1, "and every lock has exactly one owner and at most"], [820.14, 822.02, "one opened reference."], [822.06, 824.82, "Every step of the program preserves it."], [824.86, 827.94, "And from the invariant, the walk we took earlier,"], [827.98, 830.98, "from a waiting thread along the lines of the picture,"], [831.02, 833.78, "always ends at something that can step."], [833.82, 836.02, "All of this is checked by machine,"], [836.06, 838.56, "in a proof assistant."], [840.38, 842.38, "The rule has a price."], [842.42, 845.22, "Two threads can never share two locks."], [845.26, 847.22, "So a bank with two tellers,"], [847.26, 849.41, "both working on the same accounts,"], [849.45, 852.18, "cannot be written with a lock for each account."], [852.22, 854.26, "Nor can the dining philosophers:"], [854.3, 857.1, "threads around a table, each sharing a lock with"], [857.14, 858.26, "each neighbour."], [858.3, 860.42, "That picture is a ring."], [860.46, 862.98, "The second language in the paper allows this,"], [863.02, 864.42, "with lock groups."], [864.46, 867.1, "A lock group is a collection of locks behind a"], [867.14, 868.5, "single reference."], [868.54, 870.86, "Fork may share a whole group."], [870.9, 873.78, "In the picture, the group is one square."], [873.82, 877.66, "Between groups, the rule is as before."], [877.7, 880.38, "Inside a group, cycles are possible,"], [880.42, 883.26, "so something else must prevent deadlock."], [883.3, 885.34, "That something is a lock order,"], [885.38, 886.78, "but a local one."], [886.82, 889.74, "The type of a group reference lists its locks,"], [889.78, 890.78, "in order."], [890.82, 893.82, "A lock may be acquired only if every lock after"], [893.86, 895.98, "it in the list is closed."], [896.02, 898.86, "So within a group, locks are taken in increasing"], [898.9, 899.82, "order."], [899.86, 902.22, "The wait operation has a stricter condition of"], [902.26, 903.66, "the same kind."], [903.7, 905.9, "The order belongs to the group."], [905.94, 908.9, "There is no global order, and locks of different"], [908.94, 912.42, "groups can still be taken in any order."], [912.46, 915.94, "Groups can grow and shrink while the program runs."], [915.98, 917.91, "Here is the philosophers' table,"], [917.95, 921.14, "for a number of philosophers chosen at run time."], [921.18, 923.22, "Each chopstick is a lock."], [923.26, 925.46, "Think of the chopsticks as a line."], [925.5, 928.06, "The program adds a chopstick at the end of the"], [928.1, 931.02, "line, and starts a philosopher between the last"], [931.06, 931.54, "two."], [931.58, 934.53, "Then it drops its reference to the one before last,"], [934.57, 935.81, "and repeats."], [935.85, 938.62, "At the end, one more philosopher dines with the"], [938.66, 940.53, "first chopstick and the last,"], [940.57, 942.58, "and the line becomes a ring."], [942.62, 945.3, "Each philosopher's reference shows only two locks"], [945.34, 947.42, "of the group."], [947.46, 949.94, "Why can this ring not deadlock?"], [949.98, 952.62, "The group's order is the order of the line:"], [952.66, 954.65, "the first chopstick, the second,"], [954.69, 955.9, "and so on."], [955.94, 958.34, "Every philosopher has to take the earlier one of"], [958.38, 960.49, "its two chopsticks first."], [960.53, 962.46, "For a philosopher inside the line,"], [962.5, 964.62, "that is the one on its left."], [964.66, 967.34, "But the philosopher who closed the ring sits between"], [967.38, 969.66, "the last chopstick and the first."], [969.7, 971.9, "It has to take the first one first:"], [971.94, 973.58, "the one on its right."], [973.62, 976.35, "So one philosopher reaches the other way round,"], [976.39, 979.18, "and the circle of waiting cannot close."], [979.22, 981.34, "That is a well-known remedy."], [981.38, 984.38, "What is new is that the type checker enforces it,"], [984.42, 986.3, "with local checks only:"], [986.34, 989.78, "each philosopher's type mentions just its own two"], [989.82, 990.38, "locks."], [990.42, 993.18, "The table can even grow while they eat."], [993.22, 995.98, "Change one line, and a philosopher who has eaten"], [996.02, 998.22, "replaces itself by three."], [998.26, 1000.94, "Change it again, and it replaces itself by two"], [1000.98, 1004.38, "rows of three, which share its two chopsticks."], [1004.42, 1007.14, "The table then grows in a branching pattern that"], [1007.18, 1010.3, "nobody can predict, with chopsticks shared by more"], [1010.34, 1012.06, "and more philosophers."], [1012.1, 1015.06, "The same local checks still guarantee that it never"], [1015.1, 1016.92, "deadlocks."], [1017.04, 1018.52, "There are limits."], [1018.56, 1021.32, "How many locks of a group one reference can see"], [1021.36, 1023.45, "is fixed by its type."], [1023.49, 1026.92, "Shared data cannot be an arbitrary acyclic graph:"], [1026.96, 1030.12, "two paths to the same lock could become two references"], [1030.16, 1031.0, "to it."], [1031.04, 1033.08, "And there is no escape hatch yet,"], [1033.12, 1035.12, "like Rust's unsafe:"], [1035.16, 1038.2, "what it would have to promise is an open question."], [1038.24, 1041.64, "The paper presents all this as a small model language,"], [1041.68, 1044.52, "by choice, so that it does not depend on any one"], [1044.56, 1046.9, "existing language."], [1048.72, 1051.16, "Deadlocks and leaks are cycles:"], [1051.2, 1054.28, "in who holds which lock, and in which lock refers"], [1054.32, 1055.51, "to which."], [1055.55, 1058.2, "So keep the picture of threads and locks free of"], [1058.24, 1059.4, "cycles."], [1059.44, 1062.44, "New and fork join each new thing to the picture"], [1062.48, 1065.24, "in one place, so they keep it that way,"], [1065.28, 1068.76, "and threads stay free to lock in any order."], [1068.8, 1071.88, "One owner for each lock, who waits for the clients,"], [1071.92, 1073.72, "takes care of freeing."], [1073.76, 1076.15, "Lock groups add local lock orders,"], [1076.19, 1077.8, "where a cycle is needed."], [1077.84, 1079.88, "And all of it is checked locally,"], [1079.92, 1081.96, "one operation at a time:"], [1082.0, 1084.52, "a program that type-checks cannot deadlock,"], [1084.56, 1086.98, "and cannot leak."], [1087.2, 1090.76, "Higher-order leak and deadlock free locks."], [1090.8, 1093.28, "The paper has the full type systems,"], [1093.32, 1095.12, "the operational semantics,"], [1095.16, 1098.52, "the encoding of channels, and a sketch of the proofs,"], [1098.56, 1101.7, "which are checked in full by machine."]];
