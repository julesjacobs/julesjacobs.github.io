// Stable patterns: the teaser: the film's scripts in one file, made by tools/web.py.

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
// The teaser: about ninety seconds, for people who have not seen the paper. One story: the problem (many analyses),
// the claim (one algorithm, whose facts are patterns), one worked example, the same steps with other patterns, and
// what finding them together buys. {name} marks a cue, as in the film's narration.
window.NARRATION = [
  { id: 't_problem', chapter: '', pre: 0.5, post: 0.4, text:
    `{many}An optimizing compiler runs many analyses. {names}Constant propagation, value numbering, unboxing, closure analysis: {each}each is its own algorithm, with its own kind of fact. ` +
    `{one}We show that one algorithm does them all. {pat}Its facts are patterns, the kind that you write in a match expression.` },
  { id: 't_idea', chapter: '', pre: 0.4, post: 0.4, text:
    `{loop}Take this loop. {x}X starts as one, and each iteration passes two minus X. ` +
    `{write}We claim that X is always one, by writing the pattern one in place of the parameter. {subst}Under that claim, the body simplifies: two minus one is one. ` +
    `{check}Now check the claim against every call. Both pass one. {stable}So the pattern is stable: it holds on every iteration, {delete}and a parameter that is always one does not need to be passed.` },
  { id: 't_kinds', chapter: '', pre: 0.4, post: 0.4, text:
    `{cp}That was constant propagation. {change}Now change the pattern, and nothing else. {vn}A name used twice says that two arguments are always equal: value numbering. ` +
    `{unbox}A pair in a pattern says that the argument is always a pair, so the pair is never built: unboxing. ` +
    `{clo}And a function in a pattern says which function is always passed, so the call to it is direct.` },
  { id: 't_end', chapter: '', pre: 0.4, post: 3.5, text:
    `{together}Because they are all one pattern, they are found together. {four}In this loop, a constant, a dead branch, an option and a pair depend on one another. {gone}One pattern removes all four. ` +
    `{title}Stable patterns: one idea in place of many analyses. {more}The full film shows how the patterns are found, and why they are the best ones.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "t_problem",
   "chapter": "",
   "start": 0.0,
   "dur": 20.58,
   "pre": 0.5,
   "post": 0.4,
   "audio": 19.68,
   "cues": {
    "many": 0.5,
    "names": 4.1,
    "each": 9.06,
    "one": 12.98,
    "pat": 16.02
   }
  },
  {
   "id": "t_idea",
   "chapter": "",
   "start": 20.58,
   "dur": 30.96,
   "pre": 0.4,
   "post": 0.4,
   "audio": 30.16,
   "cues": {
    "loop": 0.4,
    "x": 1.92,
    "write": 7.2,
    "subst": 13.4,
    "check": 18.4,
    "stable": 22.8,
    "delete": 26.667
   }
  },
  {
   "id": "t_kinds",
   "chapter": "",
   "start": 51.54,
   "dur": 24.72,
   "pre": 0.4,
   "post": 0.4,
   "audio": 23.92,
   "cues": {
    "cp": 0.4,
    "change": 2.8,
    "vn": 5.68,
    "unbox": 11.28,
    "clo": 18.453
   }
  },
  {
   "id": "t_end",
   "chapter": "",
   "start": 76.26,
   "dur": 26.3,
   "pre": 0.4,
   "post": 3.5,
   "audio": 22.4,
   "cues": {
    "together": 0.4,
    "four": 4.24,
    "gone": 10.72,
    "title": 13.52,
    "more": 18.16
   }
  }
 ],
 "total": 102.56
};

// ==== src/scenes/teaser.js ====
// The teaser's four scenes, one story: the problem (many analyses, each its own algorithm), the claim (one
// algorithm, whose facts are patterns), one worked example on a small loop, the same steps with other patterns,
// and what finding them together buys. One thing on screen at a time, large type; the page draws captions under
// y = 930, so everything here stays between y = 120 and y = 880.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // ---- type helpers ---------------------------------------------------------------------------------------
  function measure(text, style) {
    const m = document.createElement('span');
    Object.assign(m.style, { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' }, style);
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return w;
  }
  const LS = 0.16;   // the labels' letter spacing, in em
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase' });
  // a label's visible width (letter spacing leaves a trailing gap after the last letter)
  const labelW = (text, size) => measure(text, LABEL(size)) - size * LS;
  const serifW = (text, size) => measure(text, { fontFamily: 'var(--serif)', fontSize: size + 'px', letterSpacing: '-0.005em' });
  const codeW = (n, size) => n * charWidth(size);
  // a small-caps label whose visible text is centred on cx
  function clabel(root, cx, y, text, size = 30, style = {}) {
    return label(root, cx - labelW(text, size) / 2, y, text, Object.assign({ fontSize: size + 'px' }, style));
  }
  // a serif line centred on cx
  function cserif(root, cx, y, text, size, style = {}) {
    return serif(root, cx - serifW(text, size) / 2, y, text, size, style);
  }
  // a neutral strike through a label (deletion is grey, never red): the text goes faint
  function strikeLabel(tl, root, e, x, y, w, at, size) {
    const u = box(root, x - 6, y + size * 0.6 - 1, { width: (w + 12) + 'px', height: '3px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center', opacity: 0 });
    tl.set(u, { sx: 0, o: 1 }, 0); tl.to(u, { sx: 1 }, at, 0.4, E.io);
    tl.to(e, { color: C.faint }, at, 0.4);
    return u;
  }
  // the neutral "look here" highlight
  const look = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out, pad: 8 });
  // a label that comes in at `at` and leaves at `out`
  function step(tl, root, x, y, text, at, out, style = {}) {
    const e = label(root, x, y, text, Object.assign({ fontSize: '34px' }, style));
    fadeIn(tl, e, at, 0.5, 10);
    if (out != null) fadeOut(tl, e, out, 0.3, -8);
    return e;
  }

  // ============================================ t_problem ======================================================
  scene('t_problem', ({ tl, root, cue }) => {
    const NS = 64, names = ['Constant propagation', 'Value numbering', 'Unboxing', 'Closure analysis'];
    const nameAt = [4.0, 5.42, 6.58, 7.62];
    const nw = Math.max(...names.map(n => serifW(n, NS))), padX = 44, bw = nw + 2 * padX;
    const bh = 94, stepY = 112, top = 290, cx = W / 2;
    const lineH = NS * 1.22;
    // the column lives in one layer, so that it can move aside as a whole
    const g = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    // "An optimizing compiler runs many analyses."
    const head = clabel(g, cx, top - 74, 'an optimizing compiler', 30);
    fadeIn(tl, head, cue('many') - 0.2, 0.6, 10);
    // "Constant propagation, value numbering, unboxing, closure analysis:" each at its word
    names.forEach((n, i) => fadeIn(tl, cserif(g, cx, top + i * stepY + (bh - lineH) / 2, n, NS), nameAt[i], 0.6, 16));
    // "each is its own algorithm, with its own kind of fact.": four boxes
    const tE = cue('each'), tO = cue('one');
    const frame = (y, h) => box(g, cx - bw / 2, y, { width: bw + 'px', height: h + 'px', borderRadius: '14px', boxShadow: `inset 0 0 0 2px ${alpha(C.dim, 0.7)}`, opacity: 0 });
    const boxes = names.map((_, i) => frame(top + i * stepY, bh));
    boxes.forEach((b, i) => { tl.set(b, { o: 0, s: 0.97 }, 0); tl.to(b, { o: 1, s: 1 }, tE - 0.1 + i * 0.14, 0.5, E.out5); });
    const tagY = top + 3 * stepY + bh + 34;
    const tag1 = clabel(g, cx, tagY, 'four algorithms, four kinds of fact', 30);
    fadeIn(tl, tag1, 10.9, 0.5, 10);
    // "We show that one algorithm does them all.": one box around all four
    const all = frame(top, 3 * stepY + bh);
    tl.set(all, { o: 0 }, 0); tl.to(all, { o: 1 }, tO + 0.1, 0.6, E.io);
    for (const b of boxes) tl.to(b, { o: 0 }, tO + 0.1, 0.6, E.io);
    fadeOut(tl, tag1, tO - 0.1, 0.3, -8);
    const tag2 = clabel(g, cx, tagY, 'one algorithm', 30, { color: C.ink });
    fadeIn(tl, tag2, tO + 0.25, 0.5, 10);
    // "Its facts are patterns, the kind that you write in a match expression."
    const tP = cue('pat'), S = 56;
    const src = '{k1|match|k} q {k2|with|k} {o|(|p}{s|s|b}{c|,|p} {one|1|p}{cl|)|p} {ar|→|x} {el|…|x}';
    const cwid = codeW(24, S), gap = 130, total = bw + gap + cwid, left = (W - total) / 2;
    tl.to(g, { x: left + bw / 2 - cx }, tP - 0.3, 0.8, E.io);
    tl.to(g, { o: 0.5 }, tP - 0.3, 0.8);
    const rx = left + bw + gap, cy0 = top + (3 * stepY + bh) / 2;
    const code = new Code(tl, root, rx, cy0 - 40, S);
    const lp = label(root, rx, cy0 - 110, 'its facts are patterns', { fontSize: '30px', color: C.ink });
    fadeIn(tl, lp, tP - 0.05, 0.5, 10);
    code.show(src, 16.75, { stagger: 0.015 });
    code.mark(['o', 's', 'c', 'one', 'cl'], C.pat, 17.75, { pad: 8 });
    const r = code.rect(['o', 's', 'c', 'one', 'cl']);
    const lpat = clabel(root, r.cx, code.y + code.lh + 18, 'a pattern', 30);
    fadeIn(tl, lpat, 17.9, 0.5, 10);
  });

  // ============================================ t_idea =========================================================
  scene('t_idea', ({ tl, root, cue }) => {
    const S = 56, y0 = 335;
    const code = new Code(tl, root, RAIL, y0, S), cw = code.cw, lh = code.lh;
    const svg = svgLayer(root);
    const MAIN = 'main(?i) = loop(i{mc|,} {m1|1})';
    const head = p => `loop(?i{hc|,} ${p}) =`;
    const S0 = [MAIN, head('{px|?x}'), '  if i == 0 then {x1|x} else loop(i - 1{rc|,} {two|2} {min|-} {x2|x})'].join('\n');
    const S1 = [MAIN, head('{px|1|p}'), '  if i == 0 then {x1|x} else loop(i - 1{rc|,} {two|2} {min|-} {x2|x})'].join('\n');
    const S2 = [MAIN, head('{px|1|p}'), '  if i == 0 then {x1|1|p} else loop(i - 1{rc|,} {two|2} {min|-} {x2|1|p})'].join('\n');
    const S3 = [MAIN, head('{px|1|p}'), '  if i == 0 then {x1|1|p} else loop(i - 1{rc|,} {r1|1|p})'].join('\n');
    const OUT = ['main(?i) = loop(i)', 'loop(?i) =', '  if i == 0 then {x1|1} else loop(i - 1)'].join('\n');
    // "Take this loop."
    code.show(S0, cue('loop') - 0.2, { stagger: 0.006 });
    // labels: beside the head, or under the code at its left edge; one at a time
    const besideX = RAIL + codeW(16, S), besideY = y0 + lh + (lh - 41) / 2, underY = y0 + 3 * lh + 34;
    // "X starts as one, and each iteration passes two minus X."
    look(code, ['px'], cue('x') - 0.1, 2.5);
    look(code, ['m1'], 2.6, 4.9);
    look(code, ['two', 'min', 'x2'], 5.1, 6.9);
    // "We claim that X is always one, by writing the pattern one in place of the parameter."
    const tW = cue('write');
    code.swap(S1, tW - 0.25, { dur: 0.5 });
    step(tl, root, besideX, besideY, 'the claim: x is always 1', tW + 0.1, cue('subst') - 0.4, { color: C.ink });
    code.mark(['px'], C.pat, 10.8, { out: cue('subst') - 0.4, pad: 8 });
    // "Under that claim, the body simplifies: two minus one is one."
    const tS = cue('subst');
    code.swap(S2, tS - 0.25, { dur: 0.5 });
    step(tl, root, RAIL, underY, 'simplify under the claim', tS + 0.1, cue('check') - 0.4, { color: C.ink });
    look(code, ['two', 'min', 'x2'], 15.95, 16.75);
    code.swap(S3, 16.7, { dur: 0.5 });
    // "Now check the claim against every call. Both pass one."
    const tC = cue('check'), tSt = cue('stable');
    step(tl, root, RAIL, underY, 'check every call', tC + 0.1, tSt - 0.35, { color: C.ink });
    const call0 = t => t.line === 0 && t.col >= 11, call1 = t => t.line === 2 && t.col >= 24;
    look(code, call0, 19.75, 21.1);
    look(code, call1, 19.9, 21.6);
    const ticks = [];
    [[['m1'], 21.15], [['r1'], 21.7]].forEach(([sel, t]) => {
      code.mark(sel, C.good, t - 0.05, { out: tSt - 0.3, pad: 8 });
      const r = code.rect(sel);
      const k = tick(tl, svg, r.x + r.w + 1.9 * cw, r.cy, 44, C.good, 6);
      tl.to(k, { draw: 1 }, t, 0.4, E.out); tl.to(k, { o: 0 }, tSt - 0.3, 0.3);
      ticks.push(k);
    });
    // "So the pattern is stable: it holds on every iteration,"
    const tD = cue('delete');
    code.mark(t => t.line === 1 && t.col <= 10, C.good, tSt - 0.1, { out: tD - 0.2, pad: 8 });
    step(tl, root, besideX, besideY, 'stable', tSt + 0.1, tD - 0.3, { color: C.good });
    // "and a parameter that is always one does not need to be passed."
    code.strike(['hc', 'px'], tD + 0.1, { out: 28.6 });
    code.strike(['mc', 'm1'], tD + 0.3, { out: 28.6 });
    code.strike(['rc', 'r1'], tD + 0.5, { out: 28.6 });
    code.swap(OUT, 28.6, { dur: 0.5 });
  });

  // ============================================ t_kinds ========================================================
  scene('t_kinds', ({ tl, root, cue }) => {
    const S = 60, NS = 52, GS = 30;
    const rows = [
      { src: 'loop(?i, {k|1|p})', gloss: 'always one', name: 'Constant propagation', at: [cue('cp') - 0.2, 0.55, 1.0] },
      { src: 'loop(?i, {qa|?a}, {a2|a|o})', gloss: 'always equal', name: 'Value numbering', at: [cue('vn') - 0.2, 6.95, 9.8] },
      { src: 'loop(?i, {k|(|p}?s{k2|,|p} {u|u|o}{k3|)|p})', gloss: 'always a pair', name: 'Unboxing', at: [cue('unbox') - 0.2, 12.5, 16.9] },
      { src: 'app({k|inc|p}{k1|⟨|p}{u|u|o}{k2|⟩|p})', gloss: 'always this function', name: 'Direct calls', at: [cue('clo') - 0.2, 19.9, 22.3] },
    ];
    const cwid = codeW(17, S), gw = Math.max(...rows.map(r => labelW(r.gloss, GS))), nw = Math.max(...rows.map(r => serifW(r.name, NS)));
    const gap = Math.min(90, (1720 - cwid - gw - nw) / 2);
    const x0 = (W - (cwid + gw + nw + 2 * gap)) / 2, gx = x0 + cwid + gap, nx = gx + gw + gap;
    const y0 = 330, stepY = 128;
    const rowEls = [];
    const codes = rows.map((r, i) => {
      const y = y0 + i * stepY;
      const c = new Code(tl, root, x0, y, S);
      c.show(r.src, r.at[0], { stagger: 0.012 });
      const gl = label(root, gx, y + (c.lh - GS * 1.2) / 2, r.gloss, { fontSize: GS + 'px' });
      fadeIn(tl, gl, r.at[1], 0.5, 10);
      const n = serif(root, nx, y + (c.lh - NS * 1.22) / 2, r.name, NS);
      fadeIn(tl, n, r.at[2], 0.6, 14);
      rowEls.push([c.root, gl, n]);
      // when the next row arrives, this one steps back a little
      if (i < rows.length - 1) for (const e of [c.root, gl, n]) tl.to(e, { o: 0.55 }, rows[i + 1].at[0] - 0.1, 0.4);
      return c;
    });
    // at the end, all four at full strength
    for (const es of rowEls.slice(0, 3)) for (const e of es) tl.to(e, { o: 1 }, 23.3, 0.5);
    // "Now change the pattern, and nothing else."
    const tC = cue('change');
    const lab = clabel(root, W / 2, y0 - 90, 'change the pattern. nothing else.', 30, { color: C.ink });
    fadeIn(tl, lab, tC - 0.1, 0.5, 10);
    fadeOut(tl, lab, cue('unbox') - 0.4, 0.3, -8);
    codes[0].mark(['k'], C.pat, 3.75, { out: 5.3, pad: 7 });
    // "A name used twice"
    look(codes[1], ['qa'], 6.0, 7.6);
    look(codes[1], ['a2'], 6.0, 7.6);
    // "always a pair"
    look(codes[2], ['k', 'k2', 'k3'], 13.75, 15.4);
  });

  // ============================================ t_end ==========================================================
  scene('t_end', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const cx = W / 2;
    // "Because they are all one pattern, they are found together."
    const tF = cue('four');
    const ft = clabel(root, cx, 480, 'found together', 40, { color: C.ink });
    fadeIn(tl, ft, cue('together') + 0.1, 0.6, 12);
    fadeOut(tl, ft, tF - 0.4, 0.3, -10);
    // "In this loop, a constant, a dead branch, an option and a pair depend on one another."
    const S = 84, h1 = 'loop(?i, ?a, ?x, ?q)', y1 = 240;
    const a = new Code(tl, root, cx - codeW(h1.length, S) / 2, y1, S), lh = a.lh;
    a.show(h1, tF - 0.15, { stagger: 0.02 });
    const LZ = 34, wy = y1 + lh + 60;
    const words = ['a constant', 'a dead branch', 'an option', 'a pair'];
    const at = [5.1, 5.95, 7.05, 8.1];
    const ww = words.map(t => labelW(t, LZ)), wgap = 90;
    const total = ww.reduce((s, w) => s + w, 0) + wgap * (words.length - 1);
    let x = cx - total / 2;
    const wc = [], gone = [];
    words.forEach((t, i) => {
      const e = label(root, x, wy, t, { fontSize: LZ + 'px', color: C.code });
      fadeIn(tl, e, at[i], 0.45, 10);
      wc.push(x + ww[i] / 2);
      gone.push([e, x]);
      x += ww[i] + wgap;
    });
    // "depend on one another": thin arcs between neighbours, under the words
    const arcs = [];
    const ay = wy + LZ * 1.25 + 14;
    for (let i = 0; i + 1 < words.length; i++) {
      const p = path(tl, svg, `M ${wc[i] + 10} ${ay} Q ${(wc[i] + wc[i + 1]) / 2} ${ay + 70} ${wc[i + 1] - 10} ${ay}`, { stroke: C.dim, width: 3 });
      tl.to(p, { draw: 1 }, 8.85 + i * 0.18, 0.5, E.io);
      arcs.push(p);
    }
    // "One pattern removes all four."
    const tG = cue('gone');
    for (const p of arcs) tl.to(p, { o: 0 }, tG - 0.2, 0.3);
    const strikes = gone.map(([e, wx], i) => strikeLabel(tl, root, e, wx, wy, ww[i], tG + 0.1 + i * 0.15, LZ));
    const ar = arrow(tl, svg, cx, ay - 4, cx, ay + 76, { stroke: C.dim, width: 3, head: 12 });
    drawArrow(tl, ar, tG + 0.4, 0.4);
    const h2 = 'loop(?i, ?s)', y2 = ay + 96;
    const b = new Code(tl, root, cx - codeW(h2.length, S) / 2, y2, S);
    b.show(h2, tG + 0.7, { stagger: 0.02 });
    const l2 = clabel(root, cx, y2 + lh + 10, 'one pattern: four parameters become two', 30);
    fadeIn(tl, l2, 11.4, 0.5, 10);
    // "Stable patterns: one idea in place of many analyses."
    const tT = cue('title');
    tl.to(svg, { o: 0 }, tT - 0.45, 0.35, E.in);   // the arcs and the arrow
    for (const c of [a, b]) c.hide(tT - 0.45, 0.35);
    for (const [e] of gone) fadeOut(tl, e, tT - 0.45, 0.35);
    for (const e of [l2]) fadeOut(tl, e, tT - 0.45, 0.35);
    for (const e of strikes) tl.to(e, { o: 0 }, tT - 0.45, 0.35, E.in);
    const t1 = cserif(root, cx, 330, 'Stable patterns', 120);
    fadeIn(tl, t1, tT - 0.15, 0.8, 24);
    const t2 = cserif(root, cx, 500, 'One idea in place of many analyses.', 52);
    fadeIn(tl, t2, 14.95, 0.7, 16);
    // "The full film shows how the patterns are found, and why they are the best ones."
    const tM = cue('more');
    const m1 = clabel(root, cx, 640, 'the full film: how the patterns are found,', 30);
    const m2 = clabel(root, cx, 688, 'and why they are the best ones', 30);
    fadeIn(tl, m1, tM - 0.1, 0.6, 10); fadeIn(tl, m2, tM + 0.05, 0.6, 10);
    return { keep: true };
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
window.CAPTIONS = [[0.5, 4.06, "An optimizing compiler runs many analyses."], [4.1, 6.66, "Constant propagation, value numbering,"], [6.7, 9.02, "unboxing, closure analysis:"], [9.06, 10.94, "each is its own algorithm,"], [10.98, 12.94, "with its own kind of fact."], [12.98, 15.98, "We show that one algorithm does them all."], [16.02, 18.82, "Its facts are patterns, the kind that you write"], [18.86, 20.94, "in a match expression."], [20.98, 22.46, "Take this loop."], [22.5, 26.14, "X starts as one, and each iteration passes two"], [26.18, 27.74, "minus X."], [27.78, 30.25, "We claim that X is always one,"], [30.29, 33.94, "by writing the pattern one in place of the parameter."], [33.98, 36.62, "Under that claim, the body simplifies:"], [36.66, 38.94, "two minus one is one."], [38.98, 41.78, "Now check the claim against every call."], [41.82, 43.34, "Both pass one."], [43.38, 45.02, "So the pattern is stable:"], [45.06, 47.21, "it holds on every iteration,"], [47.25, 49.86, "and a parameter that is always one does not need"], [49.9, 51.9, "to be passed."], [51.94, 54.3, "That was constant propagation."], [54.34, 57.18, "Now change the pattern, and nothing else."], [57.22, 60.38, "A name used twice says that two arguments are always"], [60.42, 61.42, "equal:"], [61.46, 62.78, "value numbering."], [62.82, 65.82, "A pair in a pattern says that the argument is always"], [65.86, 68.54, "a pair, so the pair is never built:"], [68.58, 69.95, "unboxing."], [69.99, 72.46, "And a function in a pattern says which function"], [72.5, 76.62, "is always passed, so the call to it is direct."], [76.66, 78.7, "Because they are all one pattern,"], [78.74, 80.46, "they are found together."], [80.5, 83.42, "In this loop, a constant, a dead branch,"], [83.46, 86.94, "an option and a pair depend on one another."], [86.98, 89.74, "One pattern removes all four."], [89.78, 91.34, "Stable patterns:"], [91.38, 94.38, "one idea in place of many analyses."], [94.42, 97.26, "The full film shows how the patterns are found,"], [97.3, 100.04, "and why they are the best ones."]];
