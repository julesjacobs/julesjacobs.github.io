// Paradoxes of Probabilistic Programming: a short film: the film's scripts in one file, made by tools/web.py.

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
// A short film (about two minutes) on "Paradoxes of Probabilistic Programming" (POPL 2021). One story: a program
// whose answer changes with the unit of measurement, why, what the answer should be, and the paper's fix.
// {name} marks a cue, as in the main film's narration.
window.NARRATION = [
  { id: 'p_hook', chapter: '', pre: 0.5, post: 0.4, text:
    `{prog}Here is a probabilistic program. {h}It draws a person's height, around one point seven meters. {coin}Then it flips a coin, {obs}and only if the coin comes up heads, it observes a measurement of two meters. ` +
    `{ask}What is the expected height? {m}Run it, and the answer is about one point eight one. {cm}Now write the same program in centimeters. {exp}We expect a hundred and eighty-one. {got}We get a hundred and seventy.` },
  { id: 'p_why', chapter: '', pre: 0.4, post: 0.4, text:
    `{why}Why? {weight}An inference algorithm runs the program many times, and gives each run a weight. {pdf}An observe multiplies the weight by a probability density. ` +
    `{units}But a density has a unit: this one is per meter. {skip}The runs that skip the observe have a weight with no unit. {add}The weighted average adds the two kinds, {wrong}and a sum of quantities with different units changes when the unit changes.` },
  { id: 'p_right', chapter: '', pre: 0.4, post: 0.4, text:
    `{right}So what should the answer be? {zero}A measurement of exactly two meters has probability zero. {reject}A run that takes that branch is almost never kept, {only}so only the runs that skip the observe count. ` +
    `{prior}The answer is the prior: one point seven meters, or a hundred and seventy centimeters.` },
  { id: 'p_fix', chapter: '', pre: 0.4, post: 0.4, text:
    `{fix}The paper's fix is to say what the event of probability zero is a limit of. {interval}Observe an interval around two meters, whose width shrinks to zero. ` +
    `{inf}Its probability is the density times the width: an infinitesimal probability, with no unit. {acc}The program is run by accumulating infinitesimal probabilities in place of densities, ` +
    `{less}and a run that observes less outweighs a run that observes more. {same}Now meters and centimeters agree.` },
  { id: 'p_end', chapter: '', pre: 0.4, post: 3.0, text:
    `{more}The same idea removes two more paradoxes, one of them in a program with no branch at all. {title}Paradoxes of Probabilistic Programming. {paper}The paper has the other paradoxes, the theorem, and an implementation in Julia.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "p_hook",
   "chapter": "",
   "start": 0.0,
   "dur": 26.98,
   "pre": 0.5,
   "post": 0.4,
   "audio": 26.08,
   "cues": {
    "prog": 0.5,
    "h": 2.98,
    "coin": 7.06,
    "obs": 8.74,
    "ask": 13.7,
    "m": 15.86,
    "cm": 19.46,
    "exp": 22.42,
    "got": 24.82
   }
  },
  {
   "id": "p_why",
   "chapter": "",
   "start": 26.98,
   "dur": 27.92,
   "pre": 0.4,
   "post": 0.4,
   "audio": 27.12,
   "cues": {
    "why": 0.4,
    "weight": 1.76,
    "pdf": 7.733,
    "units": 11.92,
    "skip": 16.0,
    "add": 20.187,
    "wrong": 22.8
   }
  },
  {
   "id": "p_right",
   "chapter": "",
   "start": 54.9,
   "dur": 19.28,
   "pre": 0.4,
   "post": 0.4,
   "audio": 18.48,
   "cues": {
    "right": 0.4,
    "zero": 2.48,
    "reject": 6.56,
    "only": 9.84,
    "prior": 13.04
   }
  },
  {
   "id": "p_fix",
   "chapter": "",
   "start": 74.18,
   "dur": 31.2,
   "pre": 0.4,
   "post": 0.4,
   "audio": 30.4,
   "cues": {
    "fix": 0.4,
    "interval": 5.76,
    "inf": 10.8,
    "acc": 17.68,
    "less": 23.52,
    "same": 28.0
   }
  },
  {
   "id": "p_end",
   "chapter": "",
   "start": 105.38,
   "dur": 18.6,
   "pre": 0.4,
   "post": 3,
   "audio": 15.2,
   "cues": {
    "more": 0.4,
    "title": 6.96,
    "paper": 10.08
   }
  }
 ],
 "total": 123.98
};

// ==== src/scenes/film.js ====
(function (addEventListener) {
// The five scenes of "Paradoxes of Probabilistic Programming", one story: a program whose answer changes with the
// unit of measurement (p_hook), why (p_why), what the answer should be (p_right), the paper's fix (p_fix), and the
// title (p_end). One thing on screen at a time, large type, everything between y = 120 and y = 900.
// Rows of text that must line up or centre are laid out by the browser (flex and grid boxes), so nothing depends on
// measuring a font before it has loaded; only their parts are animated.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;
  const LS = 0.16;   // the labels' letter spacing, in em

  // ---- type helpers ---------------------------------------------------------------------------------------
  // a plain div in the flow (not absolutely placed), for flex and grid rows
  function div(parent, style = {}, text) {
    const e = document.createElement('div');
    Object.assign(e.style, { position: 'relative' }, style);
    if (text !== undefined) { e.textContent = text; e._text0 = text; e._shown = text; }
    parent.appendChild(e);
    return e;
  }
  const SERIF = size => ({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, whiteSpace: 'pre', letterSpacing: '-0.005em' });
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase', color: C.dim, whiteSpace: 'pre' });
  // spans of text in colours: parts are strings (ink) or [text, colour] or [text, colour, extra style]
  function spans(e, parts) {
    for (const p of [].concat(parts)) {
      const [t, col, st] = typeof p === 'string' ? [p, null, null] : p;
      const s = document.createElement('span');
      s.textContent = t;
      if (col) s.style.color = col;
      if (st) Object.assign(s.style, st);
      e.appendChild(s);
    }
    return e;
  }
  // a serif line in the flow
  const rich = (parent, parts, size, style = {}) => spans(div(parent, Object.assign(SERIF(size), style)), parts);
  // a label in the flow
  const flabel = (parent, parts, size = 30, style = {}) => spans(div(parent, Object.assign(LABEL(size), style)), parts);
  // a full-width row whose items are centred side by side
  function crow(root, y, gap = 40, style = {}) {
    return box(root, 0, y, Object.assign({ width: W + 'px', display: 'flex', justifyContent: 'center', alignItems: 'center', columnGap: gap + 'px' }, style));
  }
  // a centred label (the padding makes up for the letter spacing after its last letter)
  function clab(root, y, parts, size = 30, style = {}) {
    return spans(box(root, 0, y, Object.assign(LABEL(size), { width: W + 'px', textAlign: 'center', paddingLeft: LS + 'em' }, style)), parts);
  }
  // a centred serif line
  function cser(root, y, parts, size, style = {}) {
    return spans(box(root, 0, y, Object.assign(SERIF(size), { width: W + 'px', textAlign: 'center' }, style)), parts);
  }
  // ε inside an upper-case label stays a lower-case epsilon
  const EPS = ['ε', C.pat, { textTransform: 'none' }];
  // a green tick, drawn in a small inline svg of its own (so that it sits after centred text)
  function itick(tl, parent, size, at) {
    const s = el(parent, 'svg');
    s.setAttribute('width', size * 1.3); s.setAttribute('height', size * 1.3);
    Object.assign(s.style, { position: 'relative', overflow: 'visible', flex: 'none' });
    const c = size * 0.65;
    const k = tick(tl, s, c, c, size, C.good, size / 9);
    tl.to(k, { draw: 1 }, at, 0.45, E.out);
    return s;
  }
  // the neutral "look here" highlight
  const look = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out, pad: 10 });
  // a label under some code, at its left edge, that comes and goes
  function step(tl, root, x, y, parts, at, out, size = 32, style = {}) {
    const e = spans(label(root, x, y, '', Object.assign({ fontSize: size + 'px' }, style)), parts);
    fadeIn(tl, e, at, 0.5, 10);
    if (out != null) fadeOut(tl, e, out, 0.3, -8);
    return e;
  }
  const lineOf = l => t => t.line === l;

  // A small table of runs: a label on the left, then "weight" and the weight. With plus, a row between the two
  // holds a plus in the weights' column, as in a sum written in a column.
  function runs(tl, root, y, rows, { plus = false, rowGap = 40 } = {}) {
    const g = box(root, 0, y, { width: W + 'px', display: 'grid', gridTemplateColumns: 'auto auto auto', justifyContent: 'center', alignItems: 'center', columnGap: '44px', rowGap: rowGap + 'px' });
    const out = { g, rows: [] };
    rows.forEach((r, i) => {
      if (i === 1 && plus) {
        div(g, {}); div(g, {});
        out.plus = rich(g, '+', 64, { justifySelf: 'start', lineHeight: 0.9, opacity: 0 });
      }
      const lab = flabel(g, r.label, 34, { justifySelf: 'end' });
      const w = rich(g, [['weight', C.dim]], 56, { justifySelf: 'start' });
      const v = rich(g, r.value, 56, { justifySelf: 'start' });
      out.rows.push([lab, w, v]);
    });
    return out;
  }

  // ============================================ p_hook =========================================================
  // A program whose answer changes with the unit. The program is centred; its meaning, and then the result, come
  // under it (a result in serif 96 does not fit beside a program at size 64).
  scene('p_hook', ({ tl, root, cue }) => {
    const S = 64, y0 = 188;
    const x0 = Math.round((W - 30 * charWidth(S)) / 2);
    const code = new Code(tl, root, x0, y0, S), lh = code.lh;
    const prog = (mu, sd, sdo, obs) => [
      `h = rand(Normal({mu|${mu}|n}, {sd|${sd}|n}))`,
      'if rand(Bernoulli({p|0.5|n}))',
      `  observe(Normal(h, {so|${sdo}|n}), {ob|${obs}|n})`,
      'end',
    ].join('\n');
    // "Here is a probabilistic program."
    code.show(prog('1.7', '0.5', '0.1', '2.0'), cue('prog') - 0.2, { stagger: 0.008 });
    // one line at a time, with its meaning under the code
    const underY = y0 + 4 * lh + 40;
    const tH = cue('h'), tC = cue('coin'), tO = cue('obs'), tA = cue('ask');
    look(code, lineOf(0), tH - 0.1, tC - 0.2);
    step(tl, root, x0, underY, 'a height, in meters', tH + 0.1, tC - 0.3, 34);
    look(code, lineOf(1), tC - 0.1, tO - 0.2);
    step(tl, root, x0, underY, 'a coin', tC + 0.1, tO - 0.3, 34);
    look(code, lineOf(2), tO - 0.1, tA - 0.3);
    step(tl, root, x0, underY, 'only on heads: a measurement of 2.0', tO + 0.1, tA - 0.3, 34);

    // under the program, the question and its answers
    const RY = 712;
    const ans = crow(root, RY, 0);
    const pre = rich(ans, 'E[h] ', 96);
    const slot = div(ans, { display: 'grid' });
    const q = rich(slot, '= ?', 96, { gridArea: '1 / 1', justifySelf: 'start' });
    const m = rich(slot, ['≈ ', ['1.81', C.pat], ' m'], 96, { gridArea: '1 / 1' });
    // "What is the expected height?"
    fadeIn(tl, pre, tA - 0.1, 0.6, 16); fadeIn(tl, q, tA - 0.1, 0.6, 16);
    // "Run it, and the answer is about one point eight one."
    const tM = cue('m') + 0.8;
    fadeOut(tl, q, tM - 0.3, 0.3, -12);
    fadeIn(tl, m, tM, 0.6, 16);
    // "Now write the same program in centimeters.": the result leaves, the numbers change
    const tCm = cue('cm');
    for (const e of [pre, m]) fadeOut(tl, e, tCm - 0.2, 0.35, -10);
    const tSw = tCm + 0.5;
    code.swap(prog('170', '50', '10', '200'), tSw, { dur: 0.5 });
    const changed = ['mu', 'sd', 'so', 'ob'];
    code.pulse(changed, tSw + 0.55, { dur: 0.9 });
    for (const id of changed) code.mark([id], C.dim, tSw + 0.5, { fill: 0.08, out: cue('exp') - 0.3, pad: 6 });
    // "We expect a hundred and eighty-one."
    const tE = cue('exp');
    const exp = clab(root, RY - 62, ['expected: ', ['181', C.ink], ' cm'], 36);
    fadeIn(tl, exp, tE - 0.1, 0.5, 10);
    // "We get a hundred and seventy."
    const tG = cue('got');
    const got = cser(root, RY, ['E[h] ≈ ', ['170', C.bad], ' cm'], 96);
    fadeIn(tl, got, tG - 0.1, 0.6, 16);
  });

  // ============================================ p_why ==========================================================
  // Why: a sum of a density, which has a unit, and a weight of one, which has none.
  scene('p_why', ({ tl, root, cue }) => {
    const S = 56, y0 = 245, X = 200;
    const code = new Code(tl, root, X, y0, S), lh = code.lh, cw = code.cw;
    code.show([
      'weight = 1',
      'h = rand(Normal({mu|1.7|n}, {sd|0.5|n}))',
      'if rand(Bernoulli({p|0.5|n}))',
      '  weight *= pdf(Normal(h, {so|0.1|n}), {ob|2.0|n})',
      'end',
    ].join('\n'), cue('weight') - 0.2, { stagger: 0.006 });
    const underY = y0 + 5 * lh + 30;
    // "An inference algorithm runs the program many times, and gives each run a weight."
    const tW = cue('weight'), tP = cue('pdf'), tU = cue('units'), tS = cue('skip');
    step(tl, root, X, underY, 'many runs, each with a weight', tW + 0.3, tP - 0.3, 34);
    look(code, lineOf(0), tW + 3.55, tP - 0.2);
    // "An observe multiplies the weight by a probability density."
    look(code, lineOf(3), tP - 0.1, tS - 0.2);
    step(tl, root, X, underY, 'a probability density', tP + 2.5, tS - 0.3, 34);
    // "But a density has a unit: this one is per meter."
    const unit = rich(box(root, X + 37 * cw + 36, y0 + 3 * lh + (lh - 56 * 1.22) / 2), [['3.5', C.pat], ' per meter'], 56);
    fadeIn(tl, unit, tU + 1.8, 0.6, 14);
    fadeOut(tl, unit, tS - 0.3, 0.3, -10);
    // "The runs that skip the observe have a weight with no unit.": the program steps back and up
    tl.to(code.root, { y: 130 - y0, o: 0.3 }, tS - 0.2, 0.8, E.io);
    const T0 = 625, T1 = 283;
    const T = runs(tl, root, T0, [
      { label: 'a run that observes', value: [['3.5', C.pat], ' / m'] },
      { label: 'a run that skips', value: '1' },
    ], { plus: true, rowGap: 10 });
    T.rows[0].forEach((e, i) => fadeIn(tl, e, tS + 0.1 + i * 0.06, 0.6, 14));
    T.rows[1].forEach((e, i) => fadeIn(tl, e, tS + 0.75 + i * 0.06, 0.6, 14));
    // "The weighted average adds the two kinds,": the program goes, the table rises, a plus joins its rows
    const tA = cue('add');
    code.hide(tA - 0.3, 0.4);
    tl.to(T.g, { y: T1 - T0 }, tA - 0.2, 0.8, E.io);
    tl.set(T.plus, { o: 0 }, 0); tl.to(T.plus, { o: 1 }, tA + 0.6, 0.4);
    const sums = crow(root, 572, 60);
    const s1 = rich(sums, [['3.5', C.pat], ' / m  +  1'], 72);
    const ne = rich(sums, '≠', 80, { color: C.bad });
    const s2 = rich(sums, [['0.035', C.pat], ' / cm  +  1'], 72);
    fadeIn(tl, s1, tA + 1.0, 0.6, 16);
    // "and a sum of quantities with different units changes when the unit changes."
    const tR = cue('wrong');
    fadeIn(tl, s2, tR + 1.3, 0.6, 16);
    fadeIn(tl, ne, tR + 2.3, 0.5, 10);
    const lab = clab(root, 702, 'the same runs, a different sum', 34);
    fadeIn(tl, lab, tR + 2.6, 0.5, 10);
  });

  // ============================================ p_right ========================================================
  // What the answer should be: runs that observe are kept with probability zero, so the answer is the prior.
  scene('p_right', ({ tl, root, cue }) => {
    const resY = 650;
    // "So what should the answer be?"
    const q = cser(root, 452, 'E[h] = ?', 96);
    fadeIn(tl, q, cue('right') - 0.1, 0.6, 16);
    fadeOut(tl, q, cue('zero') - 0.4, 0.35, -12);
    // "A measurement of exactly two meters has probability zero."
    const tZ = cue('zero');
    const pz = cser(root, 190, ['P(measurement = 2.0 exactly) = ', ['0', C.pat]], 64);
    fadeIn(tl, pz, tZ - 0.1, 0.6, 16);
    // "A run that takes that branch is almost never kept,": two rows of runs; the heads row is struck out.
    // Each row's note sits under its dots.
    const tR = cue('reject'), tO = cue('only'), tPr = cue('prior');
    const g = box(root, 0, 318, { width: W + 'px', display: 'grid', gridTemplateColumns: 'auto auto', justifyContent: 'center', alignItems: 'center', columnGap: '44px', rowGap: '2px' });
    const N = 12, D = 39, GAP = 30;
    const rowsEls = [], dotsOf = [];
    ['heads: observe', 'tails: skip'].forEach((name, r) => {
      const lab = flabel(g, name, 34, { justifySelf: 'end' });
      const cell = div(g, { display: 'flex', columnGap: GAP + 'px', padding: '14px 0' });
      const dots = [];
      for (let i = 0; i < N; i++) {
        const d = div(cell, { width: D + 'px', height: D + 'px', flex: 'none' });
        const dot = div(d, { position: 'absolute', left: 0, top: 0, width: D + 'px', height: D + 'px', borderRadius: '50%', background: C.code });
        dots.push({ d, dot });
      }
      div(g, {});
      const note = flabel(g, r === 0 ? 'kept with probability 0' : 'only these count', 34, { justifySelf: 'start', color: r === 0 ? C.dim : C.good, marginBottom: r === 0 ? '26px' : 0 });
      rowsEls.push({ lab, cell, note });
      dotsOf.push(dots);
      fadeIn(tl, lab, tR - 0.1 + r * 0.3, 0.5, 12);
      dots.forEach((x, i) => { tl.set(x.d, { o: 0, y: 12 }, 0); tl.to(x.d, { o: 1, y: 0 }, tR - 0.05 + r * 0.3 + i * 0.03, 0.5, E.out5); });
      tl.set(note, { o: 0 }, 0);
    });
    // the heads row's runs struck one after another: a grey line through each, and it goes faint
    dotsOf[0].forEach((x, i) => {
      const at = tR + 0.8 + i * 0.16;
      const bar = div(x.d, { position: 'absolute', left: '-9px', top: (D / 2 - 2) + 'px', width: (D + 18) + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
      tl.set(bar, { sx: 0 }, 0); tl.to(bar, { sx: 1 }, at, 0.25, E.io);
      tl.to(x.dot, { bg: C.faint }, at, 0.3);
    });
    fadeIn(tl, rowsEls[0].note, 9.0 - 0.15, 0.5, 10);
    // "so only the runs that skip the observe count.": the tails row lit green
    const mk = div(rowsEls[1].cell, { position: 'absolute', left: '-18px', top: '2px', right: '-18px', bottom: '2px', borderRadius: '14px', background: alpha(C.good, 0.14), boxShadow: `inset 0 0 0 1.5px ${alpha(C.good, 0.55)}`, transformOrigin: 'left center' });
    tl.set(mk, { o: 0, sx: 0.2 }, 0); tl.to(mk, { o: 1, sx: 1 }, tO + 0.15, 0.45, E.out5);
    rowsEls[1].cell.insertBefore(mk, rowsEls[1].cell.firstChild);
    fadeIn(tl, rowsEls[1].note, tO + 0.4, 0.5, 10);
    // "The answer is the prior: one point seven meters, or a hundred and seventy centimeters."
    for (const e of [pz, g]) tl.to(e, { o: 0.2 }, tPr - 0.2, 0.5);
    const res = crow(root, resY, 0);
    const r1 = rich(res, ['E[h] = ', ['1.7', C.pat], ' m'], 96);
    const r2 = rich(res, ['  =  ', ['170', C.pat], ' cm'], 96);
    const tk = div(res, { width: '100px', height: '100px', marginLeft: '16px' });
    itick(tl, tk, 70, tPr + 4.85);
    fadeIn(tl, r1, tPr + 1.6, 0.6, 16);
    fadeIn(tl, r2, tPr + 3.35, 0.6, 16);
    const lab = clab(root, resY + 136, 'the prior: the branch changes nothing', 34);
    fadeIn(tl, lab, tPr + 2.4, 0.5, 10);
  });

  // ============================================ p_fix ==========================================================
  // The fix: a probability-zero event is the limit of an interval; its probability, density times width, has no
  // unit; runs carry infinitesimal weights; meters and centimeters agree.
  scene('p_fix', ({ tl, root, cue }) => {
    const tF = cue('fix'), tI = cue('interval'), tN = cue('inf'), tAc = cue('acc'), tL = cue('less'), tS = cue('same');
    // "The paper's fix is to say what the event of probability zero is a limit of."
    const fx = clab(root, 485, 'the fix: say which limit', 44, { color: C.ink });
    fadeIn(tl, fx, tF + 0.1, 0.6, 12);
    fadeOut(tl, fx, tI - 0.35, 0.3, -10);

    // "Observe an interval around two meters, whose width shrinks to zero.": a bell curve over a number line,
    // large and centred; when the sums come it moves left at two thirds of its size (the lines keep their width,
    // the numbers their size)
    const pic = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const svg = svgLayer(pic);
    const grp = el(svg, 'g');
    const V0 = 1.65, V1 = 2.25, PW = 1080, KY = 108;
    const X = v => (v - V0) / (V1 - V0) * PW;
    const pdf = v => Math.exp(-0.5 * ((v - 1.95) / 0.1) ** 2) / (0.1 * Math.sqrt(2 * Math.PI));
    const Y = v => -pdf(v) * KY;
    const K = 2 / 3, BX = (W - PW) / 2, BY = 660, SX = 140, SY = 600;
    tl.custom(grp, 'u', (e, u) => e.setAttribute('transform', `translate(${lerp(BX, SX, u).toFixed(2)} ${lerp(BY, SY, u).toFixed(2)}) scale(${lerp(1, K, u).toFixed(4)})`), 0);
    tl.set(grp, { u: 0 }, 0);
    tl.to(grp, { u: 1 }, tN - 0.1, 0.8, E.io);
    const ns = p => { p.setAttribute('vector-effect', 'non-scaling-stroke'); return p; };
    const axis = ns(path(tl, grp, `M -24 0 L ${PW + 24} 0`, { stroke: C.dim, width: 3 }));
    tl.to(axis, { draw: 1 }, tI - 0.2, 0.6, E.io);
    let d = '';
    for (let i = 0; i <= 160; i++) { const v = V0 + (V1 - V0) * i / 160; d += (i ? ' L ' : 'M ') + X(v).toFixed(1) + ' ' + Y(v).toFixed(1); }
    const curve = ns(path(tl, grp, d, { stroke: C.ink, width: 4.5 }));
    tl.to(curve, { draw: 1 }, tI + 0.1, 0.9, E.io);
    // labels: placed for the large picture, then moved with it
    const follow = (e, lx, ly) => tl.to(e, { x: (SX + K * lx) - (BX + lx), y: (SY + ly) - (BY + ly) }, tN - 0.1, 0.8, E.io);
    [1.9, 2.0, 2.1].forEach((v, i) => {
      const t = ns(path(tl, grp, `M ${X(v)} -12 L ${X(v)} 12`, { stroke: C.dim, width: 3 }));
      tl.to(t, { draw: 1 }, tI + 0.2 + i * 0.08, 0.3);
      const n = box(pic, BX + X(v) - 60, BY + 22, Object.assign(SERIF(34), { width: '120px', textAlign: 'center', color: C.dim }), v.toFixed(1));
      fadeIn(tl, n, tI + 0.2 + i * 0.08, 0.5, 8);
      follow(n, X(v), 0);
    });
    // the band: the area under the curve over [2.0 - w/2, 2.0 + w/2], narrowing
    const band = ns(el(grp, 'path'));
    band.setAttribute('stroke-width', 2.5);
    Object.assign(band.style, { fill: alpha(C.dim, 0.4), stroke: alpha(C.ink, 0.75) });
    grp.insertBefore(band, grp.firstChild);
    const bandD = w => {
      const a = 2.0 - w / 2, b = 2.0 + w / 2, n = 16; let s = `M ${X(a).toFixed(2)} 0`;
      for (let i = 0; i <= n; i++) { const v = a + (b - a) * i / n; s += ` L ${X(v).toFixed(2)} ${Y(v).toFixed(2)}`; }
      return s + ` L ${X(b).toFixed(2)} 0 Z`;
    };
    tl.custom(band, 'w', (e, v) => e.setAttribute('d', bandD(v)), 0.1);
    tl.set(band, { w: 0.1, o: 0 }, 0);
    tl.to(band, { o: 1 }, 6.6, 0.5);
    tl.to(band, { w: 0.014 }, 9.0, 2.0, E.io);
    const wl = label(pic, BX + X(2.0) - 200, BY + 84, '', { fontSize: '34px', width: '400px', textAlign: 'center', paddingLeft: LS + 'em' });
    spans(wl, ['width ', EPS]);
    fadeIn(tl, wl, 8.7, 0.5, 10);
    follow(wl, X(2.0), 0);

    // "Its probability is the density times the width: an infinitesimal probability, with no unit."
    const F = box(root, 0, 330, { left: 'auto', right: '120px', display: 'grid', gridTemplateColumns: 'auto auto', alignItems: 'center', rowGap: '20px', columnGap: '18px' });
    const fa = rich(F, 'density × width', 56, { gridArea: '1 / 1', justifySelf: 'start', color: C.dim });
    const fb = rich(F, [['3.5', C.pat], ' / m × ', ['ε', C.pat], ' m  =  ', ['3.5 ε', C.pat]], 56, { gridArea: '2 / 1', justifySelf: 'end' });
    const fl = flabel(F, 'an infinitesimal probability:\nno unit', 34, { gridArea: '3 / 1', justifySelf: 'start', lineHeight: 1.3 });
    const fc = rich(F, [['0.035', C.pat], ' / cm × 100 ', ['ε', C.pat], ' cm  =  ', ['3.5 ε', C.pat]], 48, { gridArea: '4 / 1', justifySelf: 'end' });
    // the green link between the two results: a bracket and an equals sign
    const link = div(F, { gridArea: '2 / 2 / 5 / 3', alignSelf: 'stretch', display: 'flex', alignItems: 'center', margin: '33px 0 29px' });
    div(link, { alignSelf: 'stretch', width: '22px', border: `3px solid ${C.good}`, borderLeft: 'none', borderRadius: '0 14px 14px 0' });
    rich(link, '=', 60, { color: C.good, marginLeft: '12px' });
    fadeIn(tl, fa, tN + 1.4, 0.6, 14);
    fadeIn(tl, fb, tN + 2.5, 0.6, 14);
    fadeIn(tl, fl, tN + 3.4, 0.5, 10);
    tl.set(fc, { o: 0, y: 14 }, 0); tl.to(fc, { o: 0.6, y: 0 }, tN + 4.7, 0.6, E.out5);
    tl.set(link, { o: 0 }, 0); tl.to(link, { o: 1 }, tN + 5.5, 0.5);
    // the picture and the sums leave together
    for (const e of [pic, F]) tl.to(e, { o: 0, y: -12 }, tAc - 0.4, 0.35, E.in);

    // "The program is run by accumulating infinitesimal probabilities in place of densities,"
    const S = 72, cw = charWidth(S), cy = 510 - Math.round(S * 1.62) / 2;
    const old = new Code(tl, root, Math.round((W - 35 * cw) / 2), cy, S);
    old.show('weight *= pdf(Normal(h, {so|0.1|n}), {ob|2.0|n})', tAc - 0.15, { stagger: 0.008 });
    old.strike(t => t.col >= 10, tAc + 1.6);
    old.hide(tAc + 2.3, 0.3);
    const nw = new Code(tl, root, Math.round((W - 15 * cw) / 2), cy, S);
    nw.show('weight *= {a|3.5|p} {e|ε|p}', tAc + 2.55, { stagger: 0.01, rise: 0 });
    nw.hide(tL - 0.35, 0.3);

    // "and a run that observes less outweighs a run that observes more."
    const T = runs(tl, root, 312, [
      { label: 'a run that observes', value: [['3.5 ε', C.pat]] },
      { label: 'a run that skips', value: '1' },
    ]);
    T.rows[0].forEach((e, i) => fadeIn(tl, e, tL - 0.1 + i * 0.06, 0.6, 14));
    T.rows[1].forEach((e, i) => fadeIn(tl, e, tL + 0.25 + i * 0.06, 0.6, 14));
    const lim = cser(root, 540, [['ε', C.pat], ' → 0'], 64);
    fadeIn(tl, lim, tL + 1.1, 0.6, 14);
    for (const e of T.rows[0]) tl.to(e, { o: 0.25 }, tL + 1.75, 0.9, E.io);
    const lab = clab(root, 664, 'observing less outweighs observing more', 34);
    fadeIn(tl, lab, tL + 2.2, 0.5, 10);
    for (const e of [T.g, lim, lab]) tl.to(e, { o: 0 }, tS - 0.4, 0.35, E.in);

    // "Now meters and centimeters agree."
    const res = crow(root, 452, 0);
    const r1 = rich(res, [['1.7', C.pat], ' m  =  ', ['170', C.pat], ' cm'], 96);
    const tk = div(res, { width: '100px', height: '100px', marginLeft: '16px' });
    itick(tl, tk, 70, tS + 1.6);
    fadeIn(tl, r1, tS - 0.1, 0.7, 16);
  });

  // ============================================ p_end ==========================================================
  scene('p_end', ({ tl, root, cue }) => {
    const tM = cue('more'), tT = cue('title'), tP = cue('paper');
    // "The same idea removes two more paradoxes, one of them in a program with no branch at all."
    const panels = crow(root, 400, 50);
    const texts = [['different variables observed', 'in different branches'], ['a change of scale,', 'with no branch at all']];
    const pan = texts.map(ls => {
      const p = div(panels, { height: '220px', padding: '0 44px', borderRadius: '18px', boxShadow: `inset 0 0 0 2px ${alpha(C.dim, 0.6)}`, display: 'flex', flexDirection: 'column', justifyContent: 'center', alignItems: 'center', rowGap: '14px' });
      for (const l of ls) flabel(p, l, 34, { letterSpacing: '0.12em', paddingLeft: '0.12em', color: C.ink });
      return p;
    });
    fadeIn(tl, pan[0], tM + 1.3, 0.6, 14);
    fadeIn(tl, pan[1], tM + 3.25, 0.6, 14);
    for (const p of pan) fadeOut(tl, p, tT - 0.45, 0.35, -12);
    // "Paradoxes of Probabilistic Programming."
    const title = cser(root, 340, 'Paradoxes of Probabilistic Programming', 84);
    fadeIn(tl, title, tT - 0.1, 0.8, 22);
    const venue = clab(root, 470, 'popl 2021', 36);
    fadeIn(tl, venue, tT + 0.9, 0.6, 10);
    // "The paper has the other paradoxes, the theorem, and an implementation in Julia."
    const inp = clab(root, 598, 'in the paper', 32);
    fadeIn(tl, inp, tP - 0.1, 0.5, 10);
    const items = crow(root, 650, 0);
    const parts = ['the other paradoxes', ' · ', 'the theorem', ' · ', 'an implementation in julia'];
    const at = [tP + 0.95, tP + 2.2, tP + 2.6, tP + 3.85, tP + 3.85];
    parts.forEach((t, i) => {
      const e = flabel(items, t, 32);
      fadeIn(tl, e, at[i], 0.5, 10);
    });
    return { keep: true };
  });
})();

}).call(window, function (type, fn, opts) {
  if (type !== 'keydown' && type !== 'resize') window.addEventListener(type, fn, opts);
});

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
window.CAPTIONS = [[0.5, 2.94, "Here is a probabilistic program."], [2.98, 4.7, "It draws a person's height,"], [4.74, 7.02, "around one point seven meters."], [7.06, 10.06, "Then it flips a coin, and only if the coin comes"], [10.1, 13.66, "up heads, it observes a measurement of two meters."], [13.7, 15.82, "What is the expected height?"], [15.86, 18.38, "Run it, and the answer is about one point eight"], [18.42, 19.42, "one."], [19.46, 22.38, "Now write the same program in centimeters."], [22.42, 24.78, "We expect a hundred and eighty-one."], [24.82, 27.34, "We get a hundred and seventy."], [27.38, 28.7, "Why?"], [28.74, 32.22, "An inference algorithm runs the program many times,"], [32.26, 34.67, "and gives each run a weight."], [34.71, 38.18, "An observe multiplies the weight by a probability"], [38.22, 38.86, "density."], [38.9, 40.78, "But a density has a unit:"], [40.82, 42.94, "this one is per meter."], [42.98, 45.7, "The runs that skip the observe have a weight with"], [45.74, 47.13, "no unit."], [47.17, 49.74, "The weighted average adds the two kinds,"], [49.78, 52.7, "and a sum of quantities with different units changes"], [52.74, 55.26, "when the unit changes."], [55.3, 57.34, "So what should the answer be?"], [57.38, 60.46, "A measurement of exactly two meters has probability"], [60.5, 61.42, "zero."], [61.46, 64.7, "A run that takes that branch is almost never kept,"], [64.74, 67.9, "so only the runs that skip the observe count."], [67.94, 69.74, "The answer is the prior:"], [69.78, 72.62, "one point seven meters, or a hundred and seventy"], [72.66, 74.54, "centimeters."], [74.58, 77.9, "The paper's fix is to say what the event of probability"], [77.94, 79.9, "zero is a limit of."], [79.94, 82.54, "Observe an interval around two meters,"], [82.58, 84.94, "whose width shrinks to zero."], [84.98, 88.14, "Its probability is the density times the width:"], [88.18, 90.22, "an infinitesimal probability,"], [90.26, 91.82, "with no unit."], [91.86, 94.94, "The program is run by accumulating infinitesimal"], [94.98, 97.66, "probabilities in place of densities,"], [97.7, 100.58, "and a run that observes less outweighs a run that"], [100.62, 102.14, "observes more."], [102.18, 105.74, "Now meters and centimeters agree."], [105.78, 109.1, "The same idea removes two more paradoxes,"], [109.14, 112.3, "one of them in a program with no branch at all."], [112.34, 115.42, "Paradoxes of Probabilistic Programming."], [115.46, 117.69, "The paper has the other paradoxes,"], [117.73, 121.96, "the theorem, and an implementation in Julia."]];
