// Dataflow Facts as Stable Patterns: the film's scripts in one file, made by tools/web.py.

// ==== src/engine.js ====
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
// The narration, one entry per segment. {name} marks a cue: the moment in the audio where the word after it begins.
// The speech synthesizer gets the text without the marks; tools/tts.py turns the marks into times. Single-letter
// variables are written as capitals so that they are read as letters. The film is anonymous, as the paper is.
window.NARRATION = [
  // ---------------------------------------------------------------------------------------------- opening
  { id: 'hook', chapter: '', pre: 0.8, post: 0.9, text:
    `{loop}Here is a loop with four parameters. {out}The analysis in this film reduces it to this: two parameters, {gone}with the constant, the dead branch, the option and the pair all gone. ` +
    `{llvm}LLVM does not get all the way there. {stream}And here is a loop over a stream of closures. {counter}It can become a plain counting loop. ` +
    `{one}This film is about one analysis that finds both, {and}with no inlining, and no rule about streams.` },
  { id: 'roadmap', chapter: '', pre: 0.3, post: 0.9, text:
    `{coming}Here is what is coming. {idea}First the idea, on three small loops. {find}Then how the facts are found, {surprise}and a surprise: the textbook way to compute them is not good enough. ` +
    `{clo}Then functions and closures, where that stream becomes a counter. {dial}Then a dial, which turns the same analysis into a specializer, an inliner, or a partial evaluator. ` +
    `{end}And at the end, what is proved, and briefly, how it does in practice.` },
  { id: 'open', chapter: '', pre: 3.4, post: 0.6, text:
    `A compiler optimizes a program by {rewrite}rewriting it. {r1}Two minus one becomes one. {r2}X minus X becomes zero. {r3}The first field of a pair is what was put there. ` +
    `{local}These rules are local. {global}To make them fire across a whole program, the compiler needs global knowledge: ` +
    `{k1}that this parameter is always one, {k2}that these two are always equal, {k3}that this one is always a pair.` },

  { id: 'selfdep', chapter: 'A fact that depends on itself', pre: 1.9, post: 0.6, text:
    `{hard}Finding such facts is hard, because a fact can depend on itself. {look}In this loop, X starts as one, {passes}and every iteration passes two minus X. {if}That is one again, but only if X was one. {but}An analysis that claims only what it has already proved never sees this. {opt}An optimistic analysis assumes that X is one, because the first call passes one. {check}It checks that the loop's own call then passes one too, {holds}and keeps the fact.` },
  { id: 'optimistic', chapter: 'A fact that depends on itself', pre: 0.4, post: 0.9, text:
    `{many}Compilers have many optimistic analyses of this kind: {a1}constant propagation, {a2}value numbering, {a3}SSA construction, {a4}unboxing, {a5}contification, {a6}control-flow analysis of closures. {kind}Each finds one kind of fact, {after}and they run one after another.` },

  // ---------------------------------------------------------------------------------------------- the idea
  { id: 'idea_a', chapter: 'The idea', pre: 1.9, post: 0.5, text:
    `{one}The idea is this: every such fact can be written as a pattern, in the head of the block that it is about. {familiar}It is the pattern of pattern matching in functional programming, {clause}where a clause applies only to the calls whose arguments match its patterns. {notation}One piece of notation. {bound}Where a variable is bound, it has a question mark. We call that a binder. {used}Where it is used, it is plain.` },
  { id: 'idea_b', chapter: 'The idea', pre: 0.4, post: 0.5, text:
    `{back}Back to the loop. To state that X is always one, {write}write the pattern one in place of the binder. {subst}Substitute one for X in the body. ` +
    `{rewrite}Then rewrite with the compiler's local rules: two minus one folds to one. ` +
    `{read}Read as a definition by pattern matching, this clause defines the loop only for calls whose second argument is one. {other}For any other call, the match fails.` },
  { id: 'idea_c', chapter: 'The idea', pre: 0.4, post: 0.6, text:
    `{safe}So the clause is safe if no call ever fails to match. {two}The program has two calls of the loop. {first}Main's call passes one. ` +
    `{own}The loop's own call, in the rewritten body, passes one too. {both}Both match. ` +
    `{never}A match that never fails does not have to be performed: {nobody}the one need not be passed, and need not be tested for. {delete}Delete it. {left}What is left is a loop with one parameter.` },
  { id: 'idea_d', chapter: 'The idea', pre: 0.5, post: 0.6, text:
    `{recipe}That is the whole recipe. {write}Write a pattern in place of the parameters of every block, {specific}as specific as it can be while every call in the program still matches. ` +
    `{remove}Then remove the matching pieces. {block}A block is anything that is jumped to with arguments: a function, a loop, or a branch target.` },

  // ---------------------------------------------------------------------------------------------- many optimizations
  { id: 'vn', chapter: 'One idea, many optimizations', pre: 1.9, post: 0.6, text:
    `{round}This may seem a roundabout way to do constant propagation. But the same recipe goes much further. ` +
    `{loop}In this loop, the parameters A and B start equal, and change in step. {pattern}To state that B is always equal to A, write the plain name A as the pattern for B. ` +
    `{plain}A plain name in a pattern matches only the value of that variable: here, the parameter to its left. ` +
    `{subst}Substitute A for B, {fold}and the expression at the exit folds to A. {match}Both calls match: main passes zero twice, and the loop passes A plus one twice. ` +
    `{delete}Delete the match, and the third parameter is gone. {name}This is value numbering, around a loop.` },
  { id: 'unbox', chapter: 'One idea, many optimizations', pre: 0.5, post: 0.5, text:
    `{pair}Next, a loop that carries a pair. {always}Q is always a pair, and its second field is always main's U. ` +
    `{one}One pattern says both: a pair, with a binder S for the first field, and the plain name U for the second. {caller}A plain name may also be a variable of the caller, as U is here. ` +
    `{subst}Substitute it for Q, and the field accesses fold to S and U. {match}Both calls pass a pair that ends in U, so both match. {delete}Delete the match. ` +
    `{nopair}No pair is built any more. The loop is passed only the first field, {reads}and it reads U from main: the output nests the loop inside main, where U is in scope. ` +
    `{name}This is unboxing, together with copy propagation.` },
  { id: 'cool_same', chapter: 'One idea, many optimizations', pre: 0.5, post: 0.7, text:
    `{notice}Notice what did not change. {three}Constant propagation, value numbering and unboxing were the same steps: ` +
    `{steps}substitute the pattern, rewrite, check the calls, delete the match. {only}Only the pattern was different. {elegant}That economy is what we find elegant about the idea.` },
  { id: 'nocopy', chapter: 'One idea, many optimizations', pre: 0.5, post: 1.0, text:
    `{cp}And notice what did not happen: no code was copied. {think}Think of ordinary constant propagation. {finds}It finds which values are constants, {folds}and folds the code where it stands. {same}Patterns work in the same way, with more kinds of fact: {inplace}every block is simplified in place. {dial}Copies come only from a separate dial, specialization, which we turn later. {zero}With that dial at zero, there are none.` },

  // ---------------------------------------------------------------------------------------------- stable patterns
  { id: 'stable_a', chapter: 'Stable patterns', pre: 1.9, post: 0.6, text:
    `{which}Which patterns are safe to use? {call}We call them stable. {def}Patterns are stable if, once every block is rewritten under its pattern, ` +
    `{every}every call that remains matches the pattern of the block it calls. ` +
    `{ex}For the unboxing loop, this pattern is stable. {trivial}So is the pattern that says nothing. {not}But this one is not. ` +
    `{zero}It claims that the first field is always zero. {second}Under that claim, the loop's own call passes U in that place, not zero.` },
  { id: 'stable_b', chapter: 'Stable patterns', pre: 0.5, post: 1.0, text:
    `{fixed}Stability is a fixed-point condition, like an inductive invariant. {runtime}When the program runs, every call matches. ` +
    `{anyway}And that is true however the patterns were found. ` +
    `{check}A compiler can take patterns from anywhere, check in one pass that they are stable, and use them.` },

  // ---------------------------------------------------------------------------------------------- finding them
  { id: 'hard_a', chapter: 'Finding the patterns', pre: 1.9, post: 0.6, text:
    `{sofar}So far we wrote the patterns down and checked them. That is the easy part. ` +
    `{difficult}The difficult part is finding them, because a program has many stable patterns, and we want the most specific. ` +
    `{consider}Recall the loop from the start, with four parameters. {x}X is always one, {dead}so the last line never runs. {a}Because it never runs, A is always main's U. ` +
    `{q}And Q is always Some, of a pair whose second field is U. {depend}These facts depend on themselves, and on one another. {assumed}They have to be assumed before they can be confirmed.` },
  { id: 'hard_b', chapter: 'Finding the patterns', pre: 0.5, post: 1.0, text:
    `{six}Here are six stable patterns for this loop, from the least specific to the most. {p1}The first says nothing. {p2}The second is what conditional constant propagation finds. ` +
    `{p3}The third is what Lemerre's analysis finds. {p4}Then the option is unboxed, {p5}then the pair inside it. ` +
    `{p6}The last is the most specific: the second field of the pair is U. ` +
    `{none}None of the seven published analyses that we ran on this loop finds all of it, {llvm}and LLVM, at O three, finds all but the last step.` },

  // ---------------------------------------------------------------------------------------------- refutation
  { id: 'assume0', chapter: 'Refutation', pre: 1.9, post: 0.5, text:
    `{instead}We find the patterns by refutation. {assume}Assume the strongest thing that could be true: {exactly}a block's pattern is exactly the arguments of the calls that reach it. {then}Then let the program refute it.` },
  { id: 'ref1', chapter: 'Refutation', pre: 0.5, post: 0.5, text:
    `{r1}Round one. {first}Main's call is the first to reach the loop, so it is the loop's pattern: N, U, one, and Some of the pair zero, U. ` +
    `{simp}Simplify the body under it. {x1}X is one, so the test is decided, and the last line is dead. {fold}Two minus one folds to one, {fold2}and U plus, U minus U, folds to U. ` +
    `{call}One call is left. {check}Check it against the pattern, place by place. {d1}It differs in two places: N minus one against N, {d2}and U against zero. {refuted}The pattern is refuted.` },
  { id: 'ref2', chapter: 'Refutation', pre: 0.4, post: 0.5, text:
    `{keep}Only one thing is kept for the next round: {skel}a binder at each place where the call differed. We call this the skeleton. ` +
    `{discard}Everything else is discarded, including the values that the round computed, {because}because they were computed under a pattern that has just been refuted. ` +
    `{r2}Round two. {again}Assume again: main's call, with binders where the skeleton has them. {back}The U, the one, and the U in the pair come back, because main's call passes them. ` +
    `{simp}Simplify. {check}Check the call. {match}A binder matches anything, and the other places agree. {nothing}Nothing is refuted, {stable}so the patterns are stable.` },
  { id: 'ref3', chapter: 'Refutation', pre: 0.4, post: 0.5, text:
    `{delete}Now delete the matches. {binders}The loop's parameters are its two binders, {calls}and each call passes what matched them. ` +
    `{out}Four parameters have become two. The constant and the dead branch are gone, the option and the pair are never built, {u}and the loop reads U from main. ` +
    `{cycle}So the algorithm is: {c1}assume, {c2}simplify, {c3}check, {c4}and keep only the binders that a refutation forced. {c5}Repeat until a round refutes nothing. ` +
    `{term}A pattern can be refuted only finitely many times, so this terminates.` },
  { id: 'cool_rounds', chapter: 'Refutation', pre: 0.5, post: 1.0, text:
    `{notice}Notice what just happened. {four}Four facts that depend on themselves and on one another were found together, in two rounds, {rule}by one rule. {usual}Compilers usually have a separate analysis for each kind of fact, and run them one after another.` },

  // ---------------------------------------------------------------------------------------------- why start over
  { id: 'over1', chapter: 'Why start over?', pre: 1.9, post: 0.5, text:
    `{why}Now the surprising part. Why discard the round? {usual}The textbook way to compute a fixed point keeps what it has found, and repairs it. {miss}For patterns, that gives a correct answer, but not always the best one. ` +
    `{three}Here are three blocks. {m}Main calls F with one. {f}F passes its argument on to G. {g}And G tests it: if it is one, G calls F with two. ` +
    `{begin}Both methods begin in the same way. {f1}F is assumed to be F of one. {g1}Its body calls G of one, so G is assumed to be G of one. ` +
    `{test}Under that, the test is true, and G calls F of two, {refute}which does not match F of one.` },
  { id: 'over2', chapter: 'Why start over?', pre: 0.4, post: 0.6, text:
    `{repair}A repair in place now weakens F's pattern to a binder, and revisits F. {gx}F now calls G of X, {old}while G's pattern is still G of one. ` +
    `{join}One and X have nothing in common, so their join is a new binder. {stablebut}That is stable, but it is not the most specific. ` +
    `{stale}The one in G's old pattern was never a fact about G. It was F's X, under an assumption that has since been refuted.` },
  { id: 'over3', chapter: 'Why start over?', pre: 0.4, post: 0.6, text:
    `{ours}The algorithm keeps one thing from the first round: F's parameter must be a binder. {again}Then it starts again. ` +
    `{fx}F's body calls G of X. This is the first call to reach G, {gname}so G's pattern is the plain name X: G's argument is always F's X. {nest}G is passed nothing, and is nested inside F.` },
  { id: 'best', chapter: 'Why start over?', pre: 0.5, post: 0.5, text:
    `{inv}Why is the result of the restarts the most specific? {forced}Look at the one binder that was forced: F's parameter. {call}It was forced by the call F of two. {same}Under any stable patterns, that call is made too, perhaps with less specific arguments, and there it must match. {must}So any stable patterns have a binder there too, or above it. {nochoice}The binder was never a choice. {fresh}Everything else is assumed afresh in every round, as strongly as it can be. {order}And so the order in which the blocks are visited does not matter.` },
  { id: 'cool_best', chapter: 'Why start over?', pre: 0.5, post: 1.0, text:
    `{so}So the textbook method is not optimal for patterns, {order}and in some programs its answer depends on the order of the visits. {yet}Yet a most specific answer exists, {proved}and the restarts find it in any order. {lean}That is a theorem, checked in Lean.` },

  // ---------------------------------------------------------------------------------------------- functions and closures
  { id: 'cps', chapter: 'Functions and closures', pre: 1.9, post: 0.5, text:
    `{nothing}Nothing so far was special to loops. {style}For functions, we write programs in continuation-passing style. ` +
    `{extra}A function takes one more parameter, written after a semicolon: its continuation, the block to jump to with the result. {ret}Returning is a jump to it. ` +
    `{rest}What the caller does after the call becomes a separate block, K, which the caller passes. ` +
    `{jumps}Now a call, a return, a loop and a branch are all jumps, {rule}so one rule covers all control flow, within a function and across functions.` },
  { id: 'dup', chapter: 'Functions and closures', pre: 0.4, post: 0.6, text:
    `{once}This function is called from one place, so its pattern is that call, {cont}and its continuation is always K. ` +
    `{direct}Its return is then a direct jump to K. This is contification. {pair}That jump passes the pair Y, Y, so the pair is in K's pattern, ` +
    `{fold}and the difference of its two fields folds to zero. {never}So this pair is never built. {out}The whole program returns zero.` },
  { id: 'nocont', chapter: 'Functions and closures', pre: 0.4, post: 0.6, text:
    `{from}From here on, the examples are written without their continuations, {short}to keep them short.` },
  { id: 'clo', chapter: 'Functions and closures', pre: 0.5, post: 0.6, text:
    `{lambda}A lambda is treated in the same way. {inc}This one becomes a block, inc, with its free variable U in angle brackets. ` +
    `{closure}A block with those parameters supplied is a closure, and they are its captures. ` +
    `{data}A closure is data, so a pattern can match on it as on a pair: the block is the constructor, and the captures are its fields. ` +
    `{app}Here, app is always passed inc with main's U. {subst}Substitute that for F, {direct}and the call through F is a direct call of inc. {out}The output is one plus U. The closure is never built.` },
  { id: 'fold', chapter: 'Functions and closures', pre: 0.5, post: 0.6, text:
    `{fold}Here is a fold over a range of integers. {sum}Sum passes it a closure that has captured C. ` +
    `{every}Every call of fold passes that same closure, the recursive call included, {pat}so fold's pattern contains the closure, with binders only for S and I. ` +
    `{direct}The call through F is a direct call of scale. {out}The output is a loop over numbers that uses sum's C. {none}No closure is built, and no code was copied.` },
  { id: 'join', chapter: 'Functions and closures', pre: 0.5, post: 0.5, text:
    `{when}When several calls reach a block, its pattern is their join: {most}the most specific pattern that all of them match, with binders where they differ. {j1}Zero, zero and one, one join to a binder and then its name: the two arguments are equal. {j2}Zero, zero and one, two join to two binders.` },
  { id: 'stream', chapter: 'Functions and closures', pre: 0.5, post: 0.5, text:
    `{stream}In the last example, the closure changes on every iteration. {def}A stream is a closure that returns its first value and the stream of the rest. ` +
    `{from}From of A is the stream A, A plus one, and so on. {sum}Sum adds up the first values of a stream. ` +
    `{r1}In round one, sum's pattern is main's call, with the stream from one. {known}Under it, the call of G is direct, and its result is known: one, and the stream from two. ` +
    `{refute}So the recursive call passes from two, which refutes the pattern. {join}Both calls pass a closure of from, so the join keeps from, and puts a binder at its capture. ` +
    `{r2}In round two, the recursive call passes from of A plus one, and that matches. ` +
    `{out}Where the source passed a stream, the output passes only its counter. {var}The stream has become a loop variable.` },
  { id: 'cool_stream', chapter: 'Functions and closures', pre: 0.5, post: 0.6, text:
    `{look}This result deserves a second look. {stream}A stream of closures, each one building the next, became a counter. ` +
    `{norule}The analysis has no rule about streams, and no fusion framework. {join}All it did was join two closures of the same block, and keep what they share.` },
  { id: 'escape', chapter: 'Functions and closures', pre: 0.5, post: 0.5, text:
    `{esc}One more rule is needed. A closure escapes when we lose track of where it goes: {w1}the program returns it, {w2}passes it to code that we do not analyze, {w3}or passes it where a pattern has only a binder. {any}Whoever holds it may call it with any arguments. {fict}We count that as one more call of its block, with unknown arguments. {but}But only the arguments are unknown. {caps}What the closure captured was fixed where it was built, and the pattern keeps it. {ex}Here, the closure that is returned has captured another closure. {direct}Inside it, the call through F is still a direct call, and the inner closure is never built. {ho}This is what makes the analysis higher-order: knowledge enters a function's body through what it captured, wherever the function goes.` },
  { id: 'conv', chapter: 'Functions and closures', pre: 0.5, post: 0.8, text:
    `{what}Why not convert closures to records first, and then run a first-order analysis? {ans}Because of the escape rule. ` +
    `{lift}Our form is already close to closure conversion: a block takes its captures as parameters, like any others. {diff}The difference shows when a closure escapes. ` +
    `{ours}The calls that will be made are unknown, but we know that every one of them comes with these captures. ` +
    `{rec}After real closure conversion, a closure is a record: a pointer to its code, and the captured values. {code}The code is an ordinary function, with the record as one more parameter. ` +
    `{esc}When the record escapes, its code pointer escapes with it, {any}and a first-order analysis has to assume that someone may call the code with a totally unknown record. ` +
    `{tie}Nothing in the program says that the code only ever receives the record that it was stored in. ` +
    `{lost}So the environment is a binder, the call through F stays indirect, and the inner closure has to be built. ` +
    `{key}That is the cost of converting first: an unknown call with known captures becomes an unknown call with unknown captures. {so}So we analyze closures as closures, and lower them afterwards.` },
  { id: 'calls', chapter: 'Functions and closures', pre: 0.5, post: 1.0, text:
    `{same}An ordinary call and return is the same case. {k}Recall that what the caller does after a call is a block, K, and that the caller passes a closure of it. {cap}That closure captures the caller's local variables. ` +
    `{dup}When a function has one caller, as dup had, its return is a direct jump. {many}When it has several, its continuation is a binder, {esc}so each continuation that is passed to it escapes. ` +
    `{res}Its argument, the result of the call, is unknown. {keep}But its captures are kept: what the caller knew before the call, it still knows after it. ` +
    `{ex}Here, the pair is never built, although a call lies between making it and using it. {frame}And the closure that is built is the caller's stack frame. It no longer holds the pair. ` +
    `{one}So one mechanism analyzes across calls and returns, and through functions passed as values: {how}closures in patterns, and an escape rule that forgets only the arguments.` },

  // ---------------------------------------------------------------------------------------------- policies
  { id: 'pol1', chapter: 'Several patterns for a block', pre: 1.9, post: 0.5, text:
    `{twice}Here is the fold again, used twice: once to sum, and once to hash. {flow}With one pattern for each block, both calls flow into fold, and its pattern is their join. ` +
    `{binder}F is one lambda at the first call and another at the second, so the pattern has a binder there, and the call through F is not direct. ` +
    `{copies}Had the program been written with two copies of fold, each copy would again have one caller.` },
  { id: 'pol2', chapter: 'Several patterns for a block', pre: 0.4, post: 0.6, text:
    `{several}So we let a block have several patterns. {policy}A specialization policy says which part of a call is its context. ` +
    `{closure}With the closure policy, the context is the labels of the closures that the call passes. ` +
    `{versions}Calls with different contexts go to different versions of the block, {each}and each version has its own pattern. ` +
    `{rec}The recursive call passes the same closure, so it goes back to the same version, and the loop is specialized as a whole. ` +
    `{out}The output is two loops over numbers, as written by hand. {only}This is the only way in which a block is copied.` },
  { id: 'dial', chapter: 'Several patterns for a block', pre: 0.5, post: 0.5, text:
    `{dial}The policy works as a dial on the same fixed point. {d1}With one version for each block, it is a dataflow analysis. ` +
    `{d2}With a version for each closure passed, a specializer of higher-order functions. {d3}For each constructor passed, call-pattern specialization. ` +
    `{d4}For each call site, an inliner. {d5}And for each value of a marked parameter, a partial evaluator, ` +
    `{interp}which can specialize an interpreter away.` },
  { id: 'regex', chapter: 'Several patterns for a block', pre: 0.5, post: 0.7, text:
    `{last}Here is the last stop of the dial at work. {match}This matcher takes a regular expression and a string. {deriv}For each character, it takes the derivative of the expression, and goes on. ` +
    `{mark}Mark the expression as the parameter to specialize on. {versions}The matcher then gets a version for each expression that it is called with. {three}There are three. ` +
    `{away}In each of them, the derivative is computed away. {dfa}What is left is the automaton: one loop for each state.` },
  { id: 'cool_dial', chapter: 'Several patterns for a block', pre: 0.5, post: 1.0, text:
    `{point}Here is the point of the dial. {tools}Specializers, inliners and partial evaluators are usually separate tools, with separate machinery. ` +
    `{param}Here, each is one setting of a parameter, {same}on the analysis we already had.` },

  // ---------------------------------------------------------------------------------------------- theory
  { id: 'thm', chapter: 'What is proved', pre: 1.9, post: 0.6, text:
    `{lean}We proved three theorems in the Lean proof assistant, for a core language with constructors, closures and operations, and one pattern for each block. ` +
    `{t1}First: stable patterns hold when the program runs. At every step, the values of the running block are an instance of its pattern. ` +
    `{t2}Second: stable patterns are safe to use. The rewritten program halts with the same value as the original, or neither halts. ` +
    `{t3}Third: the algorithm finds the most specific stable patterns. Every run terminates, in any order of its steps, with patterns that are stable, and at least as specific as any other stable patterns.` },
  { id: 'thm2', chapter: 'What is proved', pre: 0.5, post: 1.0, text:
    `{about}The theorems are about the formalization in Lean. {tested}The reference implementation and the compiler's optimizer are tested, not verified. ` +
    `{pol}And the theorems are not proved for specialization policies. For some policies the third one fails. {future}A theory of policies is future work.` },

  // ---------------------------------------------------------------------------------------------- practice
  { id: 'use1', chapter: 'In practice', pre: 1.9, post: 0.6, text:
    `{brief}The interest of this work is the idea, not a benchmark, so the practical side only briefly. {compiler}In a compiler for a dependently typed language, this analysis is the only optimizer before LLVM. {twelve}We wrote twelve small programs with an abstraction, such as a fold, a stream, or a dictionary of functions. {nine}Nine of them compile to the same assembly as a loop written by hand.` },
  { id: 'mono', chapter: 'In practice', pre: 0.5, post: 0.7, text:
    `{mono}This compiler gets one more thing from the same analysis: monomorphization. {types}Types are ordinary values in its intermediate representation, ` +
    `{policy}so a specialization policy on type arguments gives a generic function a version for each type it is used at. {nopass}There is no separate monomorphization pass.` },
  { id: 'use2', chapter: 'In practice', pre: 0.5, post: 0.6, text:
    `{ports}Parts of the analysis are also ported to two mature optimizers, Flambda two and Chez Scheme. {some}They speed up some programs, {most}and leave most unchanged.` },
  { id: 'use3', chapter: 'In practice', pre: 0.5, post: 1.0, text:
    `{exp}And on small generated programs with constructors, each of seven published analyses misses the most specific patterns on about a quarter of the programs, or more. {miss}A miss is not an error: their results are correct. {ours}Our algorithm finds the most specific patterns on every program, as the third theorem says.` },

  // ---------------------------------------------------------------------------------------------- close
  { id: 'ir', chapter: 'In your compiler', pre: 1.9, post: 1.0, text:
    `{look}One last point, for compiler writers. The programs in this film look functional, but they are a low-level intermediate representation. {block}A definition is a basic block, {jump}and a call is a jump. ` +
    `{three}Here is the first loop written three ways: {w1}with assignments and jumps, {w2}in SSA form, {w3}and as blocks with arguments, as in MLIR or Cranelift. ` +
    `{phi}A block's parameters are the phi functions of SSA, {says}so the pattern one says that this phi is the constant one. ` +
    `{cps}With functions, the same blocks are a continuation-passing style representation. {fits}So the analysis fits a compiler that has either.` },
  { id: 'open1', chapter: 'Open problems', pre: 1.9, post: 0.6, text:
    `{open}The idea is young, and a lot is left to do. Here are six open problems. {tests}One: facts from tests. {ex}Inside the true branch of this test, X is zero. ` +
    `{but}But a pattern describes what calls pass, and the outcome of a test is not an argument. {how}Giving the branch a version that is passed what the test established does find such facts. ` +
    `{missing}What is missing is a most specific answer in that setting.` },
  { id: 'open2', chapter: 'Open problems', pre: 0.5, post: 0.6, text:
    `{heap}Two: values in the heap. {ex}A pattern knows a value only if some call passes it. {cells}The cells of a list, or a function stored inside a record, are never passed, {nothing}so the patterns say nothing about them.` },
  { id: 'open3', chapter: 'Open problems', pre: 0.5, post: 0.6, text:
    `{sets}Three: sets of closures. {one}A pattern holds one closure. {two}When closures of two different functions reach the same parameter, it becomes a binder, and calls through it are no longer direct. ` +
    `{flow}Flow analyses keep a set of functions there. {open}Patterns with such sets are open.` },
  { id: 'open4', chapter: 'Open problems', pre: 0.5, post: 0.6, text:
    `{pol}Four: a theory of policies. {single}With one pattern for each block, the most specific stable patterns exist, and that is proved. {some}With some policies they do not exist, and the result depends on the order. ` +
    `{which}Which policies keep a most specific answer, and why, is not known.` },
  { id: 'open5', chapter: 'Open problems', pre: 0.5, post: 0.6, text:
    `{inc}Five: restarting less. {whole}A refutation discards the whole round. {resume}Resuming from the block that was refuted gave the same result on every program we compared, with half the work. ` +
    `{open}An incremental algorithm with the same guarantee is open.` },
  { id: 'open6', chapter: 'Open problems', pre: 0.5, post: 1.0, text:
    `{prod}And six: a production compiler. {ports}Two partial ports exist. {whole}Taking the whole analysis into a mature optimizer, within its compile-time budget, has not been done. ` +
    `{each}Each of these is a project, and several are the size of a thesis.` },
  { id: 'close', chapter: 'In short', pre: 1.9, post: 6.5, text:
    `{recap}Constant propagation, value numbering, SSA construction, unboxing, contification and the control-flow analysis of closures are usually separate analyses. ` +
    `{unify}Stable patterns unify them. {exists}The most specific stable patterns exist, and refutation finds them: ` +
    `{assume}assume the best, {simplify}simplify under it, {weaken}and weaken only where a call contradicts the assumption. ` +
    `{clo}With a closure in a pattern, the analysis is interprocedural and higher-order. ` +
    `{several}With several patterns for a block, the same fixed point is a specializer, an inliner, or a partial evaluator. ` +
    `{back}And it is this one analysis that reduced the four-parameter loop to two, {counter}and turned the stream into a counter.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "hook",
   "chapter": "",
   "start": 0.0,
   "dur": 28.9,
   "pre": 0.8,
   "post": 0.9,
   "audio": 27.2,
   "cues": {
    "loop": 0.8,
    "out": 3.36,
    "gone": 7.92,
    "llvm": 12.8,
    "stream": 16.48,
    "counter": 19.44,
    "one": 21.92,
    "and": 25.12
   }
  },
  {
   "id": "roadmap",
   "chapter": "",
   "start": 28.9,
   "dur": 29.44,
   "pre": 0.3,
   "post": 0.9,
   "audio": 28.24,
   "cues": {
    "coming": 0.3,
    "idea": 1.98,
    "find": 5.42,
    "surprise": 7.34,
    "clo": 11.98,
    "dial": 16.38,
    "end": 23.66
   }
  },
  {
   "id": "open",
   "chapter": "",
   "start": 58.34,
   "dur": 29.84,
   "pre": 3.4,
   "post": 0.6,
   "audio": 25.84,
   "cues": {
    "rewrite": 5.88,
    "r1": 7.24,
    "r2": 9.88,
    "r3": 12.52,
    "local": 15.8,
    "global": 17.64,
    "k1": 22.6,
    "k2": 25.08,
    "k3": 27.36
   }
  },
  {
   "id": "selfdep",
   "chapter": "A fact that depends on itself",
   "start": 88.18,
   "dur": 33.86,
   "pre": 1.9,
   "post": 0.6,
   "audio": 31.36,
   "cues": {
    "hard": 1.9,
    "look": 7.02,
    "passes": 9.74,
    "if": 13.26,
    "but": 17.02,
    "opt": 21.98,
    "check": 28.06,
    "holds": 31.66
   }
  },
  {
   "id": "optimistic",
   "chapter": "A fact that depends on itself",
   "start": 122.04,
   "dur": 19.22,
   "pre": 0.4,
   "post": 0.9,
   "audio": 17.92,
   "cues": {
    "many": 0.4,
    "a1": 4.32,
    "a2": 5.92,
    "a3": 7.2,
    "a4": 8.8,
    "a5": 9.84,
    "a6": 11.04,
    "kind": 13.84,
    "after": 15.947
   }
  },
  {
   "id": "idea_a",
   "chapter": "The idea",
   "start": 141.26,
   "dur": 27.92,
   "pre": 1.9,
   "post": 0.5,
   "audio": 25.52,
   "cues": {
    "one": 1.9,
    "familiar": 9.18,
    "clause": 12.78,
    "notation": 17.98,
    "bound": 19.9,
    "used": 25.02
   }
  },
  {
   "id": "idea_b",
   "chapter": "The idea",
   "start": 169.18,
   "dur": 27.38,
   "pre": 0.4,
   "post": 0.5,
   "audio": 26.48,
   "cues": {
    "back": 0.4,
    "write": 4.36,
    "subst": 7.6,
    "rewrite": 10.56,
    "read": 16.56,
    "other": 24.16
   }
  },
  {
   "id": "idea_c",
   "chapter": "The idea",
   "start": 196.56,
   "dur": 27.0,
   "pre": 0.4,
   "post": 0.6,
   "audio": 26.0,
   "cues": {
    "safe": 0.4,
    "two": 4.56,
    "first": 7.2,
    "own": 9.36,
    "both": 13.68,
    "never": 15.013,
    "nobody": 18.4,
    "delete": 22.32,
    "left": 23.6
   }
  },
  {
   "id": "idea_d",
   "chapter": "The idea",
   "start": 223.56,
   "dur": 20.86,
   "pre": 0.5,
   "post": 0.6,
   "audio": 19.76,
   "cues": {
    "recipe": 0.5,
    "write": 2.66,
    "specific": 6.26,
    "remove": 11.22,
    "block": 13.78
   }
  },
  {
   "id": "vn",
   "chapter": "One idea, many optimizations",
   "start": 244.42,
   "dur": 45.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 43.44,
   "cues": {
    "round": 1.9,
    "loop": 8.54,
    "pattern": 14.06,
    "plain": 20.46,
    "subst": 27.3,
    "fold": 29.02,
    "match": 32.3,
    "delete": 39.02,
    "name": 42.22
   }
  },
  {
   "id": "unbox",
   "chapter": "One idea, many optimizations",
   "start": 290.36,
   "dur": 48.84,
   "pre": 0.5,
   "post": 0.5,
   "audio": 47.84,
   "cues": {
    "pair": 0.5,
    "always": 3.62,
    "one": 8.82,
    "caller": 16.5,
    "subst": 21.54,
    "match": 26.82,
    "delete": 31.22,
    "nopair": 32.66,
    "reads": 37.46,
    "name": 44.66
   }
  },
  {
   "id": "cool_same",
   "chapter": "One idea, many optimizations",
   "start": 339.2,
   "dur": 18.8,
   "pre": 0.5,
   "post": 0.7,
   "audio": 17.6,
   "cues": {
    "notice": 0.5,
    "three": 2.74,
    "steps": 7.78,
    "only": 12.66,
    "elegant": 14.74
   }
  },
  {
   "id": "nocopy",
   "chapter": "One idea, many optimizations",
   "start": 358.0,
   "dur": 29.02,
   "pre": 0.5,
   "post": 1,
   "audio": 27.52,
   "cues": {
    "cp": 0.5,
    "think": 5.14,
    "finds": 7.94,
    "folds": 10.287,
    "same": 12.9,
    "inplace": 16.9,
    "dial": 19.62,
    "zero": 25.3
   }
  },
  {
   "id": "stable_a",
   "chapter": "Stable patterns",
   "start": 387.02,
   "dur": 31.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 29.44,
   "cues": {
    "which": 1.9,
    "call": 4.38,
    "def": 6.22,
    "every": 10.86,
    "ex": 15.22,
    "trivial": 18.62,
    "not": 20.94,
    "zero": 22.7,
    "second": 25.98
   }
  },
  {
   "id": "stable_b",
   "chapter": "Stable patterns",
   "start": 418.96,
   "dur": 18.78,
   "pre": 0.5,
   "post": 1,
   "audio": 17.28,
   "cues": {
    "fixed": 0.5,
    "runtime": 5.22,
    "anyway": 8.5,
    "check": 11.78
   }
  },
  {
   "id": "hard_a",
   "chapter": "Finding the patterns",
   "start": 437.74,
   "dur": 38.66,
   "pre": 1.9,
   "post": 0.6,
   "audio": 36.16,
   "cues": {
    "sofar": 1.9,
    "difficult": 7.42,
    "consider": 14.7,
    "x": 18.54,
    "dead": 19.98,
    "a": 22.3,
    "q": 26.38,
    "depend": 31.18,
    "assumed": 34.78
   }
  },
  {
   "id": "hard_b",
   "chapter": "Finding the patterns",
   "start": 476.4,
   "dur": 34.7,
   "pre": 0.5,
   "post": 1,
   "audio": 33.2,
   "cues": {
    "six": 0.5,
    "p1": 5.86,
    "p2": 7.86,
    "p3": 11.94,
    "p4": 15.06,
    "p5": 17.06,
    "p6": 19.06,
    "none": 24.02,
    "llvm": 28.58
   }
  },
  {
   "id": "assume0",
   "chapter": "Refutation",
   "start": 511.1,
   "dur": 14.8,
   "pre": 1.9,
   "post": 0.5,
   "audio": 12.4,
   "cues": {
    "instead": 1.9,
    "assume": 4.62,
    "exactly": 7.527,
    "then": 11.82
   }
  },
  {
   "id": "ref1",
   "chapter": "Refutation",
   "start": 525.9,
   "dur": 38.04,
   "pre": 0.5,
   "post": 0.5,
   "audio": 37.04,
   "cues": {
    "r1": 0.5,
    "first": 1.94,
    "simp": 11.54,
    "x1": 13.86,
    "fold": 18.66,
    "fold2": 21.14,
    "call": 25.1,
    "check": 26.74,
    "d1": 29.7,
    "d2": 34.02,
    "refuted": 35.86
   }
  },
  {
   "id": "ref2",
   "chapter": "Refutation",
   "start": 563.94,
   "dur": 38.42,
   "pre": 0.4,
   "post": 0.5,
   "audio": 37.52,
   "cues": {
    "keep": 0.4,
    "skel": 3.28,
    "discard": 8.4,
    "because": 12.8,
    "r2": 16.96,
    "again": 18.32,
    "back": 23.2,
    "simp": 28.92,
    "check": 30.0,
    "match": 31.2,
    "nothing": 34.8,
    "stable": 36.16
   }
  },
  {
   "id": "ref3",
   "chapter": "Refutation",
   "start": 602.36,
   "dur": 33.62,
   "pre": 0.4,
   "post": 0.5,
   "audio": 32.72,
   "cues": {
    "delete": 0.4,
    "binders": 2.4,
    "calls": 4.96,
    "out": 7.76,
    "u": 15.04,
    "cycle": 17.52,
    "c1": 19.36,
    "c2": 20.24,
    "c3": 21.12,
    "c4": 21.867,
    "c5": 25.28,
    "term": 28.08
   }
  },
  {
   "id": "cool_rounds",
   "chapter": "Refutation",
   "start": 635.98,
   "dur": 16.86,
   "pre": 0.5,
   "post": 1,
   "audio": 15.36,
   "cues": {
    "notice": 0.5,
    "four": 2.42,
    "rule": 8.42,
    "usual": 9.94
   }
  },
  {
   "id": "over1",
   "chapter": "Why start over?",
   "start": 652.84,
   "dur": 45.28,
   "pre": 1.9,
   "post": 0.5,
   "audio": 42.88,
   "cues": {
    "why": 1.9,
    "usual": 6.14,
    "miss": 11.607,
    "three": 16.3,
    "m": 18.22,
    "f": 20.7,
    "g": 23.26,
    "begin": 28.22,
    "f1": 30.94,
    "g1": 33.5,
    "test": 38.22,
    "refute": 42.38
   }
  },
  {
   "id": "over2",
   "chapter": "Why start over?",
   "start": 698.12,
   "dur": 28.52,
   "pre": 0.4,
   "post": 0.6,
   "audio": 27.52,
   "cues": {
    "repair": 0.4,
    "gx": 6.4,
    "old": 8.4,
    "join": 11.44,
    "stablebut": 16.16,
    "stale": 19.6
   }
  },
  {
   "id": "over3",
   "chapter": "Why start over?",
   "start": 726.64,
   "dur": 24.44,
   "pre": 0.4,
   "post": 0.6,
   "audio": 23.44,
   "cues": {
    "ours": 0.4,
    "again": 6.72,
    "fx": 8.72,
    "gname": 13.6,
    "nest": 19.92
   }
  },
  {
   "id": "best",
   "chapter": "Why start over?",
   "start": 751.08,
   "dur": 34.84,
   "pre": 0.5,
   "post": 0.5,
   "audio": 33.84,
   "cues": {
    "inv": 0.5,
    "forced": 4.26,
    "call": 8.22,
    "same": 11.14,
    "must": 18.9,
    "nochoice": 23.22,
    "fresh": 25.46,
    "order": 30.58
   }
  },
  {
   "id": "cool_best",
   "chapter": "Why start over?",
   "start": 785.92,
   "dur": 17.58,
   "pre": 0.5,
   "post": 1,
   "audio": 16.08,
   "cues": {
    "so": 0.5,
    "order": 3.94,
    "yet": 8.18,
    "proved": 11.087,
    "lean": 13.94
   }
  },
  {
   "id": "cps",
   "chapter": "Functions and closures",
   "start": 803.5,
   "dur": 36.8,
   "pre": 1.9,
   "post": 0.5,
   "audio": 34.4,
   "cues": {
    "nothing": 1.9,
    "style": 4.86,
    "extra": 9.34,
    "ret": 17.9,
    "rest": 20.06,
    "jumps": 26.3,
    "rule": 31.02
   }
  },
  {
   "id": "dup",
   "chapter": "Functions and closures",
   "start": 840.3,
   "dur": 27.4,
   "pre": 0.4,
   "post": 0.6,
   "audio": 26.4,
   "cues": {
    "once": 0.4,
    "cont": 5.2,
    "direct": 8.28,
    "pair": 13.8,
    "fold": 18.747,
    "never": 22.32,
    "out": 24.32
   }
  },
  {
   "id": "nocont",
   "chapter": "Functions and closures",
   "start": 867.7,
   "dur": 6.52,
   "pre": 0.4,
   "post": 0.6,
   "audio": 5.52,
   "cues": {
    "from": 0.4,
    "short": 4.32
   }
  },
  {
   "id": "clo",
   "chapter": "Functions and closures",
   "start": 874.22,
   "dur": 37.1,
   "pre": 0.5,
   "post": 0.6,
   "audio": 36.0,
   "cues": {
    "lambda": 0.5,
    "inc": 3.42,
    "closure": 8.94,
    "data": 14.18,
    "app": 22.82,
    "subst": 27.1,
    "direct": 28.74,
    "out": 32.26
   }
  },
  {
   "id": "fold",
   "chapter": "Functions and closures",
   "start": 911.32,
   "dur": 29.42,
   "pre": 0.5,
   "post": 0.6,
   "audio": 28.32,
   "cues": {
    "fold": 0.5,
    "sum": 3.62,
    "every": 7.38,
    "pat": 12.42,
    "direct": 17.94,
    "out": 21.46,
    "none": 25.54
   }
  },
  {
   "id": "join",
   "chapter": "Functions and closures",
   "start": 940.74,
   "dur": 22.52,
   "pre": 0.5,
   "post": 0.5,
   "audio": 21.52,
   "cues": {
    "when": 0.5,
    "most": 4.82,
    "j1": 10.26,
    "j2": 17.86
   }
  },
  {
   "id": "stream",
   "chapter": "Functions and closures",
   "start": 963.26,
   "dur": 55.48,
   "pre": 0.5,
   "post": 0.5,
   "audio": 54.48,
   "cues": {
    "stream": 0.5,
    "def": 5.3,
    "from": 10.42,
    "sum": 15.54,
    "r1": 18.5,
    "known": 23.7,
    "refute": 30.5,
    "join": 35.14,
    "r2": 41.7,
    "out": 47.78,
    "var": 52.42
   }
  },
  {
   "id": "cool_stream",
   "chapter": "Functions and closures",
   "start": 1018.74,
   "dur": 18.38,
   "pre": 0.5,
   "post": 0.6,
   "audio": 17.28,
   "cues": {
    "look": 0.5,
    "stream": 3.22,
    "norule": 8.1,
    "join": 12.74
   }
  },
  {
   "id": "escape",
   "chapter": "Functions and closures",
   "start": 1037.12,
   "dur": 49.08,
   "pre": 0.5,
   "post": 0.5,
   "audio": 48.08,
   "cues": {
    "esc": 0.5,
    "w1": 6.34,
    "w2": 7.94,
    "w3": 10.74,
    "any": 14.3,
    "fict": 17.54,
    "but": 22.1,
    "caps": 24.5,
    "ex": 29.62,
    "direct": 33.78,
    "ho": 40.02
   }
  },
  {
   "id": "conv",
   "chapter": "Functions and closures",
   "start": 1086.2,
   "dur": 74.82,
   "pre": 0.5,
   "post": 0.8,
   "audio": 73.52,
   "cues": {
    "what": 0.5,
    "ans": 6.1,
    "lift": 8.26,
    "diff": 15.86,
    "ours": 18.927,
    "rec": 25.14,
    "code": 32.42,
    "esc": 37.14,
    "any": 41.007,
    "tie": 47.94,
    "lost": 53.54,
    "key": 61.22,
    "so": 69.54
   }
  },
  {
   "id": "calls",
   "chapter": "Functions and closures",
   "start": 1161.02,
   "dur": 59.98,
   "pre": 0.5,
   "post": 1,
   "audio": 58.48,
   "cues": {
    "same": 0.5,
    "k": 4.26,
    "cap": 11.46,
    "dup": 14.98,
    "many": 20.34,
    "esc": 23.62,
    "res": 27.14,
    "keep": 30.74,
    "ex": 36.58,
    "frame": 42.1,
    "one": 47.62,
    "how": 54.02
   }
  },
  {
   "id": "pol1",
   "chapter": "Several patterns for a block",
   "start": 1221.0,
   "dur": 28.56,
   "pre": 1.9,
   "post": 0.5,
   "audio": 26.16,
   "cues": {
    "twice": 1.9,
    "flow": 7.42,
    "binder": 13.82,
    "copies": 22.54
   }
  },
  {
   "id": "pol2",
   "chapter": "Several patterns for a block",
   "start": 1249.56,
   "dur": 36.04,
   "pre": 0.4,
   "post": 0.6,
   "audio": 35.04,
   "cues": {
    "several": 0.4,
    "policy": 3.28,
    "closure": 8.08,
    "versions": 13.6,
    "each": 17.6,
    "rec": 20.347,
    "out": 28.24,
    "only": 32.56
   }
  },
  {
   "id": "dial",
   "chapter": "Several patterns for a block",
   "start": 1285.6,
   "dur": 27.88,
   "pre": 0.5,
   "post": 0.5,
   "audio": 26.88,
   "cues": {
    "dial": 0.5,
    "d1": 4.46,
    "d2": 8.66,
    "d3": 14.02,
    "d4": 18.1,
    "d5": 20.607,
    "interp": 24.66
   }
  },
  {
   "id": "regex",
   "chapter": "Several patterns for a block",
   "start": 1313.48,
   "dur": 29.12,
   "pre": 0.5,
   "post": 0.7,
   "audio": 27.92,
   "cues": {
    "last": 0.5,
    "match": 3.62,
    "deriv": 7.06,
    "mark": 11.9,
    "versions": 15.38,
    "three": 19.78,
    "away": 20.98,
    "dfa": 24.42
   }
  },
  {
   "id": "cool_dial",
   "chapter": "Several patterns for a block",
   "start": 1342.6,
   "dur": 16.14,
   "pre": 0.5,
   "post": 1,
   "audio": 14.64,
   "cues": {
    "point": 0.5,
    "tools": 2.74,
    "param": 9.94,
    "same": 12.82
   }
  },
  {
   "id": "thm",
   "chapter": "What is proved",
   "start": 1358.74,
   "dur": 44.1,
   "pre": 1.9,
   "post": 0.6,
   "audio": 41.6,
   "cues": {
    "lean": 1.9,
    "t1": 12.22,
    "t2": 21.54,
    "t3": 30.06
   }
  },
  {
   "id": "thm2",
   "chapter": "What is proved",
   "start": 1402.84,
   "dur": 20.14,
   "pre": 0.5,
   "post": 1,
   "audio": 18.64,
   "cues": {
    "about": 0.5,
    "tested": 3.94,
    "pol": 9.62,
    "future": 16.26
   }
  },
  {
   "id": "use1",
   "chapter": "In practice",
   "start": 1422.98,
   "dur": 27.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 25.44,
   "cues": {
    "brief": 1.9,
    "compiler": 8.5,
    "twelve": 15.82,
    "nine": 23.02
   }
  },
  {
   "id": "mono",
   "chapter": "In practice",
   "start": 1450.92,
   "dur": 21.68,
   "pre": 0.5,
   "post": 0.7,
   "audio": 20.48,
   "cues": {
    "mono": 0.5,
    "types": 6.26,
    "policy": 10.34,
    "nopass": 17.78
   }
  },
  {
   "id": "use2",
   "chapter": "In practice",
   "start": 1472.6,
   "dur": 11.66,
   "pre": 0.5,
   "post": 0.6,
   "audio": 10.56,
   "cues": {
    "ports": 0.5,
    "some": 7.3,
    "most": 9.06
   }
  },
  {
   "id": "use3",
   "chapter": "In practice",
   "start": 1484.26,
   "dur": 22.46,
   "pre": 0.5,
   "post": 1,
   "audio": 20.96,
   "cues": {
    "exp": 0.5,
    "miss": 11.26,
    "ours": 15.06
   }
  },
  {
   "id": "ir",
   "chapter": "In your compiler",
   "start": 1506.72,
   "dur": 44.02,
   "pre": 1.9,
   "post": 1,
   "audio": 41.12,
   "cues": {
    "look": 1.9,
    "block": 11.02,
    "jump": 13.18,
    "three": 15.26,
    "w1": 18.22,
    "w2": 20.1,
    "w3": 21.82,
    "phi": 26.78,
    "says": 30.54,
    "cps": 34.7,
    "fits": 39.9
   }
  },
  {
   "id": "open1",
   "chapter": "Open problems",
   "start": 1550.74,
   "dur": 31.38,
   "pre": 1.9,
   "post": 0.6,
   "audio": 28.88,
   "cues": {
    "open": 1.9,
    "tests": 8.38,
    "ex": 11.1,
    "but": 15.02,
    "how": 20.9,
    "missing": 26.7
   }
  },
  {
   "id": "open2",
   "chapter": "Open problems",
   "start": 1582.12,
   "dur": 15.74,
   "pre": 0.5,
   "post": 0.6,
   "audio": 14.64,
   "cues": {
    "heap": 0.5,
    "ex": 3.54,
    "cells": 7.647,
    "nothing": 12.58
   }
  },
  {
   "id": "open3",
   "chapter": "Open problems",
   "start": 1597.86,
   "dur": 20.22,
   "pre": 0.5,
   "post": 0.6,
   "audio": 19.12,
   "cues": {
    "sets": 0.5,
    "one": 3.3,
    "two": 5.86,
    "flow": 13.86,
    "open": 17.22
   }
  },
  {
   "id": "open4",
   "chapter": "Open problems",
   "start": 1618.08,
   "dur": 20.86,
   "pre": 0.5,
   "post": 0.6,
   "audio": 19.76,
   "cues": {
    "pol": 0.5,
    "single": 3.3,
    "some": 10.047,
    "which": 15.02
   }
  },
  {
   "id": "open5",
   "chapter": "Open problems",
   "start": 1638.94,
   "dur": 18.38,
   "pre": 0.5,
   "post": 0.6,
   "audio": 17.28,
   "cues": {
    "inc": 0.5,
    "whole": 3.46,
    "resume": 6.58,
    "open": 13.78
   }
  },
  {
   "id": "open6",
   "chapter": "Open problems",
   "start": 1657.32,
   "dur": 17.98,
   "pre": 0.5,
   "post": 1,
   "audio": 16.48,
   "cues": {
    "prod": 0.5,
    "ports": 3.58,
    "whole": 5.94,
    "each": 12.66
   }
  },
  {
   "id": "close",
   "chapter": "In short",
   "start": 1675.3,
   "dur": 53.68,
   "pre": 1.9,
   "post": 6.5,
   "audio": 45.28,
   "cues": {
    "recap": 1.9,
    "unify": 13.58,
    "exists": 15.98,
    "assume": 20.86,
    "simplify": 22.06,
    "weaken": 23.5,
    "clo": 27.1,
    "several": 32.38,
    "back": 40.06,
    "counter": 45.02
   }
  }
 ],
 "total": 1728.98
};

// ==== src/scenes/s00_open.js ====
// Opening: the title, local rewrite rules and the global facts they need; then the first loop, whose fact
// depends on itself, seen pessimistically and optimistically; then the analyses compilers run for such facts.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // a small-caps label whose text changes at a moment (it blinks out and back)
  function relabel(tl, lab, text, at) {
    tl.to(lab, { o: 0 }, at - 0.2, 0.18, E.in);
    tl.text(lab, text, at);
    tl.to(lab, { o: 1 }, at, 0.35, E.out5);
  }

  // ---- open: three rewrite rules, then the facts that make them fire --------------------------------------
  scene('open', ({ tl, root, cue }) => {
    // the title, during the pre-roll
    const title = serif(root, RAIL, 440, 'Dataflow Facts as Stable Patterns', 96, { letterSpacing: '-0.012em' });
    const sub = label(root, RAIL + 4, 580, 'a summary of the paper');
    fadeIn(tl, title, 0.25, 0.8, 24); fadeIn(tl, sub, 0.6, 0.7, 12);
    // the narrator's first words are spoken over the title
    fadeOut(tl, title, cue('rewrite') - 0.7, 0.45); fadeOut(tl, sub, cue('rewrite') - 0.7, 0.45);

    // the rules: left sides on the rail, the arrows in one column, the right sides a beat after the left
    const S = 50, cw = charWidth(S);
    const rules = [
      { lhs: '2 - 1', rhs: '1', at: cue('r1'), land: 8.44 },          // "becomes"
      { lhs: 'x - x', rhs: '0', at: cue('r2'), land: 11.08 },         // "becomes"
      { lhs: '(a, b).0', rhs: 'a', at: cue('r3'), land: 14.12 },      // "is what was put there"
    ];
    const ry = [400, 520, 640];
    const ruleCodes = [];
    rules.forEach((r, i) => {
      const l = new Code(tl, root, RAIL, ry[i], S);
      l.show(r.lhs, r.at - 0.2, { stagger: 0.03 });
      const rr = new Code(tl, root, RAIL + 9.5 * cw, ry[i], S);
      rr.show(`{ar|→}   {o|${r.rhs}}`, r.land - 0.2, { stagger: 0.12, rise: 0 });
      tl.fromTo(rr.spans(['o'])[0], { x: 3 * cw - 30 }, { x: 3 * cw }, r.land - 0.08, 0.55, E.out5);
      ruleCodes.push(l, rr);
    });
    // "these rules are local": they step back and up, to make room for the program
    const tLocal = cue('local');
    for (const c of ruleCodes) { c.move(0, -200, tLocal - 0.2, 0.8); tl.to(c.root, { o: 0.55 }, tLocal - 0.2, 0.8, E.io); }

    // the facts: three block headers, each with its fact beside it
    const heads = [
      { src: 'loop(?i, {x|?x})', sel: ['x'], fact: 'always 1', at: cue('global') - 0.2, markAt: 22.88, factAt: 23.75 },
      { src: 'loop(?i, {a|?a}, {b|?b})', sel: ['a', 'b'], fact: 'always equal', at: cue('k2') - 0.2, markAt: 25.3, factAt: 25.9 },
      { src: 'loop(?i, {q|?q})', sel: ['q'], fact: 'always a pair', at: cue('k3') - 0.2, markAt: 27.55, factAt: 28.1 },
    ];
    const factX = RAIL + 16 * cw + 70;
    let prev = null;
    heads.forEach((h, i) => {
      const y = 625 + i * 108;
      const c = new Code(tl, root, RAIL, y, S);
      c.show(h.src, h.at, { stagger: 0.02 });
      const m = c.mark(h.sel, C.dim, h.markAt - 0.15, { fill: 0.08 });
      const f = label(root, factX, y + Math.round((c.lh - 30) / 2), h.fact);
      fadeIn(tl, f, h.factAt - 0.15, 0.5, 10);
      // the one before steps back
      if (prev) { tl.to(prev.m, { o: 0 }, h.at, 0.35); tl.to(prev.c.root, { o: 0.6 }, h.at, 0.5); tl.to(prev.f, { o: 0.6 }, h.at, 0.5); }
      prev = { c, m, f };
    });
  });

  // the first loop's place on the stage: the same in s01_idea.js
  const LOOP_Y = 420;

  // ---- selfdep: the first loop; x is 1 only if x is 1 ---------------------------------------------------------
  scene('selfdep', ({ tl, root, cue }) => {
    const S = 44, y0 = LOOP_Y;
    const code = new Code(tl, root, RAIL, y0, S), cw = code.cw, lh = code.lh;
    const svg = svgLayer(root);
    const L0 = 'main(?i) = loop(i, {c1|1})';
    const P1 = `${L0}\nloop(?i, {px|?x}) = if i == 0 then {x1|x} else loop(i - 1, {two|2} {min|-} {x2|x})`;
    const P2 = `${L0}\nloop(?i, {px|?x}) = if i == 0 then {x1|x} else loop(i - 1, {two|2} {min|-} {x2|1|p})`;
    const P3 = `${L0}\nloop(?i, {px|?x}) = if i == 0 then {x1|x} else loop(i - 1, {r|1})`;
    // the loop is read while the first sentence is spoken
    code.show(P1, cue('hard') + 0.2, { stagger: 0.008 });
    // the notation, before idea_a explains it: a legend under the program for a few seconds
    const legend = box(root, RAIL, y0 + 2 * lh + 40, { display: 'flex', alignItems: 'baseline', gap: '22px', whiteSpace: 'pre' });
    el(legend, 'span', { position: 'static', fontFamily: 'var(--mono)', fontSize: '36px', color: C.bind, fontVariantLigatures: 'none' }, '?x');
    el(legend, 'span', { position: 'static', fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim }, ':  a parameter, where it is bound');
    fadeIn(tl, legend, cue('hard') + 0.9, 0.6, 10); fadeOut(tl, legend, cue('hard') + 6.8, 0.4);

    // "in this loop, x starts as one, and every iteration passes two minus x"
    const tPass = cue('passes');
    code.mark(['c1'], C.dim, cue('look') - 0.15, { fill: 0.1, out: tPass - 0.15 });
    code.mark(['two', 'min', 'x2'], C.dim, tPass - 0.15, { fill: 0.1, out: cue('if') - 0.15 });

    // "that is one again, but only if x was one": a worked line under the program
    const wy = y0 + 2 * lh + 90;
    const work = new Code(tl, root, RAIL, wy, S);
    work.show('x = 1   ⟹   2 - x = 1', cue('if') - 0.15, { stagger: 0.015 });

    // "an analysis that claims only what it has already proved never sees this"
    const tBut = cue('but');
    const kind = label(root, RAIL, y0 - 80, 'pessimistic');
    fadeIn(tl, kind, tBut - 0.15, 0.5, 10);
    work.hide(tBut - 0.25, 0.3);
    const dimP = {}; for (const k of 'pbokvnxfdgr') dimP[k] = C.dim;
    const unk = new Code(tl, root, RAIL, wy, S, { palette: dimP });
    unk.show('x unknown   ⟹   2 - x unknown', tBut + 0.1, { stagger: 0.01, rise: 8 });

    // "an optimistic analysis assumes that x is one, because the first call passes one"
    const tOpt = cue('opt');
    relabel(tl, kind, 'optimistic', tOpt + 0.15);
    unk.hide(tOpt - 0.1, 0.35);
    code.mark(['px'], C.dim, 23.5, { fill: 0.1, out: 25.8 });
    const rx = code.rect(['px']);
    const as = label(root, rx.cx - 200, y0 + 2 * lh + 16, 'assume 1', { width: '400px', textAlign: 'center' });
    fadeIn(tl, as, 23.8, 0.5, 10);
    code.mark(['c1'], C.dim, 25.8, { fill: 0.1, out: cue('check') });
    // "it checks that the loop's own call then passes one too"
    const tChk = cue('check');
    code.swap(P2, tChk + 0.1, { dur: 0.5 });
    code.mark(['two', 'min', 'x2'], C.dim, 29.6, { fill: 0.1, out: 30.55 });
    code.swap(P3, 30.55, { dur: 0.5 });
    // "and keeps the fact"
    const tk = tick(tl, svg, RAIL + 53 * cw, y0 + 1.5 * lh, 30, C.good, 5);
    tl.to(tk, { draw: 1 }, cue('holds') - 0.15, 0.45, E.out);
  });

  // ---- optimistic: the analyses compilers run for such facts, one after another --------------------------------
  scene('optimistic', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const names = ['Constant propagation', 'Value numbering', 'SSA construction', 'Unboxing', 'Contification', 'Control-flow analysis of closures'];
    const ny0 = 284, ngap = 92, nx = 230;
    names.forEach((n, i) => { const e = serif(root, nx, ny0 + i * ngap, n, 52); fadeIn(tl, e, cue('a' + (i + 1)) - 0.2, 0.6, 18); });
    // "and they run one after another"
    const ar = arrow(tl, svg, RAIL + 12, ny0 + 22, RAIL + 12, ny0 + 5 * ngap + 50, { stroke: C.dim, width: 3, head: 13 });
    drawArrow(tl, ar, cue('after') - 0.15, 1.6);
  });
})();

// ==== src/scenes/s01_idea.js ====
// The idea: a fact is a pattern, as in pattern matching. On the first loop: write the pattern, substitute,
// rewrite, check the calls, delete the match. Then the recipe in one sentence.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // a small-caps label centred on a stage x
  const centred = (root, cx, y, text, style = {}) => label(root, cx - 200, y, text, Object.assign({ width: '400px', textAlign: 'center' }, style));
  // a step label whose text changes at a moment
  function relabel(tl, lab, text, at) {
    tl.to(lab, { o: 0 }, at - 0.2, 0.18, E.in);
    tl.text(lab, text, at);
    tl.to(lab, { o: 1 }, at, 0.35, E.out5);
  }

  // ---- idea_a: every such fact is a pattern, in a block's head; the notation ----------------------------------
  scene('idea_a', ({ tl, root, cue, dur }) => {
    const phrase = serif(root, RAIL, 470, '', 64);
    phrase.innerHTML = 'Every such fact is a <i>pattern</i>.';
    fadeIn(tl, phrase, cue('one') - 0.2, 0.8, 24);
    // "the pattern of pattern matching": the phrase steps back; the first loop arrives where idea_b continues it
    const tFam = cue('familiar');
    tl.to(phrase, { y: -180, o: 0.6 }, tFam - 0.2, 0.8, E.io);
    const S = 44, y0 = 420;   // the first loop's place, as in s00_open.js and idea_b
    const code = new Code(tl, root, RAIL, y0, S), lh = code.lh;
    code.show('main(?i) = loop(i, 1)\nloop(?i, {px|?x}) = if i == 0 then {x1|x} else loop(i - 1, {two|2} {min|-} {x2|x})', tFam - 0.15, { stagger: 0.004, byLine: 0.05 });
    const ly = y0 + 2 * lh + 16;
    const tNot = cue('notation'), tCl = cue('clause');
    // "in the head of the block that it is about" (said before the loop is there)
    const head = t => t.line === 1 && t.col <= 11;
    code.mark(head, C.dim, tFam + 0.6, { fill: 0.1, out: tCl - 0.15 });
    const lh1 = centred(root, code.rect(head).cx, ly, 'the head');
    fadeIn(tl, lh1, tFam + 0.8, 0.5, 10); fadeOut(tl, lh1, tCl - 0.15, 0.3);
    // "a clause applies only to the calls whose arguments match": the loop's two calls, in turn
    const call0 = t => t.line === 0 && t.col >= 11, call1 = t => t.line === 1 && t.col >= 37;
    code.mark(call0, C.dim, tCl - 0.15, { fill: 0.1, out: 14.45 });
    code.mark(call1, C.dim, 14.45, { fill: 0.1, out: tNot - 0.2 });
    const lc = centred(root, code.rect(call1).cx, ly, 'its calls');
    fadeIn(tl, lc, tCl + 0.1, 0.5, 10); fadeOut(tl, lc, tNot - 0.2, 0.3);
    // "where a variable is bound, it has a question mark. We call that a binder."
    const tEnd = dur - 1.0;
    code.mark(['?i@1.1'], C.bind, 20.8, { out: tEnd });
    code.mark(['px'], C.bind, 20.9, { out: tEnd });
    const lb = centred(root, code.rect(['?i@1.1', 'px']).cx, ly, 'binder');
    fadeIn(tl, lb, 23.85, 0.5, 10); fadeOut(tl, lb, tEnd, 0.3);
    // "where it is used, it is plain": the uses in the body
    const tUsed = cue('used'), uses = ['i@1.1', 'x1', 'i@1.2', 'x2'];
    uses.forEach((u, k) => code.mark([u], C.dim, 25.05 + k * 0.06, { fill: 0.1, out: tEnd }));
    const lu = centred(root, code.rect(['i@1.1', 'x2']).cx, ly, 'use');
    fadeIn(tl, lu, 25.25, 0.5, 10); fadeOut(tl, lu, tEnd, 0.3);
    // the program stays, unmarked, into idea_b; only the phrase leaves
    fadeOut(tl, phrase, tEnd, 0.4);
    return { keep: true };
  });

  // ---- idea_b + idea_c: the loop as a clause; check its calls; delete the match ---------------------------
  scene(['idea_b', 'idea_c'], ({ tl, root, cue, seg }) => {
    const S = 44, y0 = 420;  // the first loop's place, as in s00_open.js
    const Cs = seg('idea_c');
    const code = new Code(tl, root, RAIL, y0, S), cw = code.cw, lh = code.lh;
    const svg = svgLayer(root);
    const L0 = 'main(?i) = loop(i{mc|,} {m1|1})';
    const head = p => `loop(?i{hc|,} ${p}) = `;
    const B0 = `${L0}\n${head('{px|?x}')}if i == 0 then {x1|x} else loop(i - 1{rc|,} {two|2} {min|-} {x2|x})`;
    const B1 = `${L0}\n${head('{px|1|p}')}if i == 0 then {x1|x} else loop(i - 1{rc|,} {two|2} {min|-} {x2|x})`;
    const B2 = `${L0}\n${head('{px|1|p}')}if i == 0 then {x1|1|p} else loop(i - 1{rc|,} {two|2} {min|-} {x2|1|p})`;
    const B3 = `${L0}\n${head('{px|1|p}')}if i == 0 then {x1|1|p} else loop(i - 1{rc|,} {r1|1})`;
    const OUT = 'main(?i) = loop(i)\nloop(?i) = if i == 0 then 1 else loop(i - 1)';
    // on screen from the first frame: idea_a ends with this program in this place
    code.show(B0, 0, { dur: 0.01, rise: 0, stagger: 0, byLine: 0 });

    // "write the pattern one in place of the binder"
    code.swap(B1, cue('write') - 0.25, { dur: 0.5 });
    // "substitute one for x in the body"
    const tSub = cue('subst');
    code.swap(B2, tSub - 0.2, { dur: 0.5 });
    const step = label(root, RAIL, y0 + 2 * lh + 24, 'substitute');
    fadeIn(tl, step, tSub - 0.2, 0.5, 10);
    // "then rewrite with the compiler's local rules: two minus one folds to one"
    relabel(tl, step, 'rewrite', cue('rewrite') - 0.1);
    code.mark(['two', 'min', 'x2'], C.dim, 13.5, { fill: 0.08, out: 14.8 });
    code.swap(B3, 14.8, { dur: 0.5 });

    // "read as a definition by pattern matching, this clause defines the loop only for calls whose second
    // argument is one"
    const tRead = cue('read');
    tl.to(step, { o: 0 }, tRead - 0.2, 0.3, E.in);
    code.mark(t => t.line === 1 && t.col <= 12, C.dim, tRead - 0.1, { fill: 0.08, out: 21.9 });
    code.mark(['px'], C.pat, 21.9, { out: Cs - 0.35 });
    // "for any other call, the match fails": a call that is not in the program, its 7 under the pattern's 1
    const dimP = {}; for (const k of 'pbokvnxfdg') dimP[k] = C.dim;
    const other = new Code(tl, root, RAIL + cw, y0 + 2 * lh + 30, S, { palette: dimP });
    other.show('loop(5, {s|7})', cue('other') - 0.15, { stagger: 0.02 });
    other.color(['s'], C.bad, 25.75, 0.3);
    const ocr = other.rect(['s']);
    const crs = cross(tl, svg, RAIL + 12.4 * cw, ocr.cy, 22);
    crs.forEach(c => { tl.to(c, { draw: 1 }, 25.75, 0.3, E.out); tl.to(c, { o: 0 }, Cs - 0.35, 0.3); });
    other.hide(Cs - 0.35, 0.3);

    // ---- idea_c: check ----
    relabel(tl, step, 'check', cue('safe') - 0.1);
    // "the program has two calls of the loop"
    const call0 = t => t.line === 0 && t.col >= 11, call1 = t => t.line === 1 && t.col >= 36;
    const tNever = cue('never'), tick0 = Cs + 8.3, tick1 = Cs + 12.0;
    code.mark(call0, C.dim, cue('two') - 0.1, { fill: 0.08, out: tick0 - 0.1 });
    code.mark(call1, C.dim, cue('two') - 0.05, { fill: 0.08, out: cue('first') - 0.15 });
    // "main's call passes one"; "the loop's own call, in the rewritten body, passes one too"
    code.mark(call1, C.dim, cue('own') - 0.15, { fill: 0.08, out: tick1 - 0.1 });
    code.mark(['m1'], C.good, tick0 - 0.1, { out: tNever - 0.1 });
    const k0 = tick(tl, svg, RAIL + 22.6 * cw, y0 + 0.5 * lh, 30, C.good, 5);
    tl.to(k0, { draw: 1 }, tick0, 0.45, E.out);
    code.mark(['r1'], C.good, tick1 - 0.1, { out: tNever - 0.1 });
    const k1 = tick(tl, svg, RAIL + 51.6 * cw, y0 + 1.5 * lh, 30, C.good, 5);
    tl.to(k1, { draw: 1 }, tick1, 0.45, E.out);
    for (const k of [k0, k1]) tl.to(k, { o: 0 }, tNever - 0.1, 0.35);
    tl.to(step, { o: 0 }, tNever - 0.1, 0.3, E.in);

    // "the one need not be passed, and need not be tested for": the calls' ones, then the pattern's
    const tDel = cue('delete'), tGo = tDel - 0.2;
    code.strike(['mc', 'm1'], cue('nobody') + 0.1, { out: tGo });
    code.strike(['rc', 'r1'], cue('nobody') + 0.25, { out: tGo });
    code.strike(['hc', 'px'], Cs + 20.9, { out: tGo });
    // "delete it"
    code.swap(OUT, tGo, { dur: 0.5 });
    relabel(tl, step, 'delete the match', tDel - 0.1);
  });

  // ---- idea_d: the recipe -----------------------------------------------------------------------------------
  scene('idea_d', ({ tl, root, cue }) => {
    const S = 60, y0 = 350;
    const l1 = serif(root, RAIL, y0, 'Write a pattern in place of the parameters of every block,', S);
    const l2 = serif(root, RAIL, y0 + 84, 'as specific as it can be while every call still matches.', S);
    const l3 = serif(root, RAIL, y0 + 200, 'Then remove the matching pieces.', S);
    fadeIn(tl, l1, cue('write') - 0.2, 0.7, 20);
    fadeIn(tl, l2, cue('specific') - 0.2, 0.7, 20);
    fadeIn(tl, l3, cue('remove') - 0.2, 0.7, 20);
    // "a block is anything that is jumped to with arguments: a function, a loop, or a branch target"
    for (const l of [l1, l2, l3]) tl.to(l, { o: 0.6 }, 17.2, 0.6, E.io);
    const ly = y0 + 360, names = [['a function', 17.4], ['a loop', 18.25], ['a branch target', 19.0]];
    let x = RAIL;
    names.forEach(([n, at]) => {
      const e = label(root, x, ly, n);
      fadeIn(tl, e, at - 0.2, 0.5, 12);
      x += n.length * 19 + 110;
    });
  });
})();

// ==== src/scenes/s01b_lowlevel.js ====
// A late chapter, for compiler writers. The programs are a low-level IR: a definition is a basic block, a call a jump; the first loop written three ways
// (the paper's Section 2.1); a block's parameters are the phi functions of SSA; later the same blocks are a CPS IR.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;
  const look = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out });

  scene('ir', ({ tl, root, cue }) => {
    // ---- "The programs in this film look functional, but they are a low-level intermediate representation" --
    const S = 44, y0 = 420;
    const a = new Code(tl, root, RAIL, y0, S), lh = a.lh;
    a.show('main(?i) = loop(i, 1)\nloop(?i, ?x) = if i == 0 then x else loop(i - 1, 2 - x)', 4.7, { stagger: 0.008 });
    const forw = label(root, RAIL, y0 - 70, 'for compiler writers', { color: C.ink });
    fadeIn(tl, forw, cue('look') - 0.1, 0.5, 10); fadeOut(tl, forw, 7.2, 0.3, -8);
    const ir = label(root, RAIL, y0 - 70, 'a low-level intermediate representation');
    fadeIn(tl, ir, 7.7, 0.6, 10);
    // "A definition is a basic block"
    const tB = cue('block'), tJ = cue('jump'), t3 = cue('three');
    look(a, t => t.line === 0 && t.col < 8, tB + 0.05, tJ - 0.05); look(a, t => t.line === 1 && t.col < 12, tB + 0.25, tJ - 0.05);
    const lb = label(root, RAIL, y0 + 2 * lh + 22, 'a definition is a basic block');
    fadeIn(tl, lb, tB + 0.9, 0.5, 10); tl.to(lb, { o: 0.45 }, tJ, 0.4);
    // "and a call is a jump"
    look(a, t => t.line === 0 && t.col >= 11, tJ + 0.1, t3 - 0.45); look(a, t => t.line === 1 && t.col >= 37, tJ + 0.3, t3 - 0.45);
    const lj = label(root, RAIL + 620, y0 + 2 * lh + 22, 'a call is a jump');
    fadeIn(tl, lj, tJ + 0.75, 0.5, 10);
    // "Here is the first loop written three ways": this picture leaves
    a.hide(t3 - 0.35, 0.4); for (const e of [ir, lb, lj]) fadeOut(tl, e, t3 - 0.35, 0.35, -10);

    // ---- three ways ---------------------------------------------------------------------------------------
    const S3 = 36, cw = charWidth(S3), yC = 420, GAP = 96;
    const x1 = RAIL, x2 = x1 + 19 * cw + GAP, x3 = x2 + 22 * cw + GAP;
    const K = (id, w) => `{${id}|${w}|k}`, V = (id, w) => `{${id}|${w}|v}`;
    const SRC1 = ['   x := 1', `L: if i == 0 ${K('g1', 'goto')} E`, '   i := i - 1', '   x := 2 - x', `   ${K('g2', 'goto')} L`, `E: ${K('r1', 'return')} x`].join('\n');
    const SRC2 = [
      `L: ${V('i1', 'i₁')} = {fa|φ|k}(${V('i0', 'i₀')}, ${V('i2', 'i₂')})`,
      `   ${V('x1', 'x₁')} = {fb|φ|k}({one|1|n}, ${V('x2', 'x₂')})`,
      `   if ${V('i1b', 'i₁')} == 0 ${K('g3', 'goto')} E`,
      `   ${V('i2b', 'i₂')} = ${V('i1c', 'i₁')} - 1`,
      `   ${V('x2b', 'x₂')} = 2 - ${V('x1b', 'x₁')}; ${K('g4', 'goto')} L`,
      `E: ${K('r2', 'return')} ${V('x1c', 'x₁')}`].join('\n');
    const SRC3 = (x, b = 'x') => ['main(?i) = loop(i, 1)', `loop({pi|?i}, ${x}) =`, `  if i == 0 then {b1|${b}}`, `  else loop(i - 1, 2 - {b2|${b}})`].join('\n');
    const cols = [
      { x: x1, head: 'assignments and jumps', src: SRC1, at: cue('w1') },
      { x: x2, head: 'SSA', src: SRC2, at: cue('w2') },
      { x: x3, head: 'blocks with arguments', src: SRC3('{px|?x}'), at: cue('w3') },
    ].map(c => {
      const h = label(root, c.x, yC - 64, c.head); fadeIn(tl, h, c.at - 0.2, 0.5, 10);
      const code = new Code(tl, root, c.x, yC, S3); code.show(c.src, c.at - 0.1, { stagger: 0.006, byLine: 0.07 });
      return { h, code };
    });
    const [c1, c2, c3] = cols.map(c => c.code), lh3 = c1.lh;
    // "as in MLIR or Cranelift"
    const like = label(root, x3, yC + 4 * lh3 + 22, 'as in MLIR, Cranelift');
    fadeIn(tl, like, 23.8, 0.5, 10);
    // "A block's parameters are the phi functions of SSA"
    const tP = cue('phi'), tS = cue('says'), tK = cue('cps');
    look(c3, ['pi', 'px'], tP + 0.6, tS - 0.2);
    look(c2, t => t.line === 0 && t.col >= 8, tP + 1.45, tS - 0.2); look(c2, t => t.line === 1 && t.col >= 8, tP + 1.6, tS - 0.2);
    // "so the pattern one says that this phi is the constant one"
    c3.swap(SRC3('{px|1|p}', '1|p'), tS + 0.25, { dur: 0.5 });
    c3.mark(['px'], C.pat, tS + 0.8, { out: tK - 0.25 });
    c2.mark(t => t.line === 1 && t.col >= 3, C.pat, tS + 1.6, { out: tK - 0.25 });
    // "Later, for functions, the same blocks are a continuation-passing style representation"
    for (const c of [cols[0], cols[1]]) { tl.to(c.code.root, { o: 0.35 }, tK - 0.2, 0.5); tl.to(c.h, { o: 0.35 }, tK - 0.2, 0.5); }
    tl.to(like, { o: 0.35 }, tK - 0.2, 0.5);
    const later = label(root, RAIL, yC + 6 * lh3 + 56, 'with functions: the same blocks as a continuation-passing style IR', { color: C.ink });
    fadeIn(tl, later, 35.6, 0.6, 10);
    const across = label(root, RAIL, yC + 6 * lh3 + 104, 'the analysis fits a compiler that has either');
    fadeIn(tl, across, cue('fits') + 0.1, 0.6, 10);
  });
})();

// ==== src/scenes/s02_many.js ====
// One idea, many optimizations: the same recipe on two more loops (value numbering, unboxing), then a table of
// what each kind of pattern says and the classical analysis it is.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160, S = 44, Y0 = 320;

  // the step label under the code, at its left edge: one element whose text changes
  function steps(tl, root, y) {
    const tag = label(root, RAIL, y, '', { color: C.dim });
    tl.set(tag, { o: 0 }, 0);
    let shown = false;
    return {
      to(text, at) {
        if (shown) { tl.to(tag, { o: 0 }, at - 0.18, 0.15); }
        tl.text(tag, text, at - 0.03); tl.to(tag, { o: 1 }, at - 0.03, 0.3); shown = true;
      },
      out(at) { tl.to(tag, { o: 0 }, at, 0.3, E.in); },
    };
  }
  // a green tick just right of some tokens (the end of a call)
  function tickAfter(tl, svg, code, sel, at, out) {
    const r = code.rect(sel), x = r.x + r.w + 40, y = r.cy + 2;
    const t = tick(tl, svg, x, y, 34, C.good, 5);
    tl.to(t, { draw: 1 }, at, 0.35, E.out);
    tl.to(t, { o: 0 }, out, 0.3);
    return t;
  }
  // an arrow along a cubic curve, drawn with drawArrow/hideArrow like the engine's arrow()
  function curveArrow(tl, svg, x1, y1, c1x, c1y, c2x, c2y, x2, y2, { stroke = C.outer, width = 3, head = 11 } = {}) {
    const p = path(tl, svg, `M ${x1} ${y1} C ${c1x} ${c1y} ${c2x} ${c2y} ${x2} ${y2}`, { stroke, width });
    const ang = Math.atan2(y2 - c2y, x2 - c2x);
    const hd = el(svg, 'path');
    hd.setAttribute('d', `M ${-head} ${-head * 0.55} L 0 0 L ${-head} ${head * 0.55}`);
    hd.setAttribute('fill', 'none'); hd.setAttribute('stroke-width', width); hd.setAttribute('stroke-linecap', 'round'); hd.setAttribute('stroke-linejoin', 'round');
    hd.style.stroke = stroke; hd.style.opacity = 0;
    hd.setAttribute('transform', `translate(${x2} ${y2}) rotate(${ang * 180 / Math.PI})`);
    tl.set(hd, { o: 0 }, 0);
    p._head = hd;
    return p;
  }
  const look = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out });
  const nameOf = (tl, root, text, at) => { const n = serif(root, RAIL, Y0 + 400, text, 60); fadeIn(tl, n, at, 0.8, 22); return n; };

  // ---- value numbering --------------------------------------------------------------------------------------
  scene('vn', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const code = new Code(tl, root, RAIL, Y0, S), lh = code.lh;
    const M = 'main(?n) = loop(n, {m0a|0}, {m0b|0})';
    const A = `${M}\nloop(?i, {ha|?a}, {hb|?b}) =\n  if i == 0 then {ta|a} {tp|+} {tl|(}{ta2|a} {tm|-} {tb|b}{tr|)} else loop(i - 1, {xa|a} {xp|+} {x1|1}, {yb|b} {yp|+} {y1|1})`;
    const B = A.replace('{hb|?b}', '{hb|a|o}');
    const Cs = B.replace('{tb|b}', '{tb|a|o}').replace('{yb|b}', '{yb|a|o}');
    const D = `${M}\nloop(?i, {ha|?a}, {hb|a|o}) =\n  if i == 0 then {ta|a} else loop(i - 1, {xa|a} {xp|+} {x1|1}, {yb|a|o} {yp|+} {y1|1})`;
    const Eo = 'main(?n) = loop(n, {m0a|0})\nloop(?i, {ha|?a}) = if i == 0 then {ta|a} else loop(i - 1, {xa|a} {xp|+} {x1|1})';
    const st = steps(tl, root, Y0 + 3 * lh + 30);

    // "a roundabout way to do constant propagation": the first loop's clause head, which leaves at "But"
    const back = new Code(tl, root, RAIL, 430, 50);
    back.show('loop(?i, {one|1|p})', cue('round') - 0.05, { stagger: 0.02 });
    const cp = serif(root, RAIL, 540, 'Constant propagation', 60);
    fadeIn(tl, cp, 4.1, 0.7, 20);
    tl.to(back.root, { o: 0, y: -24 }, 5.7, 0.4, E.in); fadeOut(tl, cp, 5.75, 0.4, -20);

    // "In this loop": the program
    code.show(A, cue('loop') - 0.45, { stagger: 0.004, byLine: 0.06 });
    // "the parameters A and B", "start equal", "and change in step"
    look(code, ['ha'], 10.15, 11.15); look(code, ['hb'], 10.8, 11.15);
    look(code, ['m0a', ',@0.2', 'm0b'], 11.2, 12.3);
    look(code, ['xa', 'xp', 'x1'], 12.35, 13.9); look(code, ['yb', 'yp', 'y1'], 12.45, 13.9);
    // "To state that B is always equal to A": B; "write the plain name A as the pattern for B"
    look(code, ['hb'], 14.7, 16.65);
    code.swap(B, 16.7, { dur: 0.5 });
    code.mark(['hb'], C.outer, 17.25, { out: cue('plain') - 0.1 });
    // "A plain name in a pattern matches only the value of that variable: here, the parameter to its left"
    // a low arc under the head line, from the plain name back to ?a (the gap between the two lines holds it)
    const rb = code.rect(['hb']), ra = code.rect(['ha']);
    const ay = Y0 + lh + Math.round((lh + 44) / 2) + 2;
    const arc = curveArrow(tl, svg, rb.cx, ay, rb.cx - 8, ay + 30, ra.cx + 8, ay + 30, ra.cx, ay, { stroke: C.outer, width: 3, head: 10 });
    drawArrow(tl, arc, cue('plain') - 0.05, 0.6);
    hideArrow(tl, arc, 24.9, 0.25);
    code.mark(['ha'], C.bind, 25.1, { out: cue('subst') - 0.3 });
    // "Substitute A for B"
    st.to('substitute', cue('subst') - 0.1);
    code.swap(Cs, cue('subst') - 0.2, { dur: 0.5 });
    // "and the expression at the exit folds to A"
    st.to('rewrite', cue('fold') - 0.1);
    look(code, ['ta', 'tp', 'tl', 'ta2', 'tm', 'tb', 'tr'], cue('fold') - 0.05, 30.45);
    code.swap(D, 30.45, { dur: 0.5 });
    // "Both calls match: main passes zero twice, and the loop passes A plus one twice"
    st.to('check', cue('match') - 0.1);
    const tOff = cue('delete') - 0.1;
    tickAfter(tl, svg, code, [')@0.2'], cue('match') + 0.05, tOff);
    tickAfter(tl, svg, code, [')@2.1'], cue('match') + 0.25, tOff);
    code.mark(['m0a', ',@0.2', 'm0b'], C.good, 34.55, { out: tOff });
    code.mark(['xa', 'xp', 'x1'], C.good, 36.85, { out: tOff }); code.mark(['yb', 'yp', 'y1'], C.good, 36.95, { out: tOff });
    // "Delete the match, and the third parameter is gone"
    st.to('delete the match', cue('delete') - 0.1);
    const tGo = cue('delete') + 0.75;
    code.strike([',@0.2', 'm0b'], cue('delete') - 0.05, { out: tGo });
    code.strike([',@1.2', 'hb'], cue('delete') + 0.02, { out: tGo });
    code.strike([',@2.2', 'yb', 'yp', 'y1'], cue('delete') + 0.09, { out: tGo });
    code.swap(Eo, tGo, { dur: 0.5 });
    // "This is value numbering, around a loop"
    st.out(cue('name') - 0.2);
    nameOf(tl, root, 'Value numbering', 42.75);
  });

  // ---- unboxing ---------------------------------------------------------------------------------------------
  scene('unbox', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const code = new Code(tl, root, RAIL, Y0, S), lh = code.lh;
    const fa = (id, n) => `{${id}|q}{${id}d|.}{${id}n|${n}}`;
    const M = 'main({mu|?u}, ?n) = loop(n, {po|(}{p0|0}{pc|,} {pu|u}{pe|)})';
    const A = `${M}\nloop(?i, {hq|?q}) =\n  if i == 0 then ${fa('a0', 0)} + ${fa('a1', 1)} else loop(i - 1, {ro|(}${fa('b0', 0)} + ${fa('b1', 1)}{rc|,} ${fa('b2', 1)}{re|)})`;
    const head = 'loop(?i, {ho|(|p}{hs|?s}{hc|,} {hu|u|o}{he|)|p}) =';
    const B = A.replace('loop(?i, {hq|?q}) =', head);
    const Cs = `${M}\n${head}\n  if i == 0 then {s1|s} + {u1|u|o} else loop(i - 1, {ro|(}{s2|s} + {u2|u|o}{rc|,} {u3|u|o}{re|)})`;
    const D = 'main({mu|?u}, ?n) = loop(n, {p0|0})\nloop(?i, {hs|?s}) =\n  if i == 0 then {s1|s} + {u1|u|o} else loop(i - 1, {s2|s} + {u2|u|o})';
    const Eo = 'main({mu|?u}, ?n) = loop(n, {p0|0})\n  where loop(?i, {hs|?s}) =\n    if i == 0 then {s1|s} + {u1|u|o} else loop(i - 1, {s2|s} + {u2|u|o})';
    const st = steps(tl, root, Y0 + 3 * lh + 30);

    // "Next, a loop that carries a pair"
    code.show(A, cue('pair') - 0.2, { stagger: 0.004, byLine: 0.06 });
    // "Q is always a pair, and its second field is always main's U"
    look(code, ['hq'], 3.55, 4.5);
    look(code, ['po', 'p0', 'pc', 'pu', 'pe'], 4.55, 5.75);
    look(code, ['pu'], 5.8, 8.6);
    look(code, ['mu'], 7.05, 8.6);
    // "One pattern says both: a pair, with a binder S for the first field, and the plain name U for the second"
    code.swap(B, cue('one') - 0.25, { dur: 0.5 });
    look(code, ['ho', 'hs', 'hc', 'hu', 'he'], 9.2, 10.5);
    code.mark(['ho'], C.pat, 10.6, { out: 11.9 }); code.mark(['he'], C.pat, 10.6, { out: 11.9 });
    code.mark(['hs'], C.bind, 11.95, { out: 13.75 });
    code.mark(['hu'], C.outer, 13.9, { out: 21.3 });
    // "A plain name may also be a variable of the caller, as U is here": a link from the pattern's u up to main's ?u,
    // through the gap between the two lines
    const rh = code.rect(['hu']), rm = code.rect(['mu']);
    const ly1 = Y0 + lh + 2, ly2 = Y0 + lh - 6;
    const link = curveArrow(tl, svg, rh.cx - 6, ly1, rh.cx - 60, ly1 + 6, rm.cx + 70, ly2 + 10, rm.cx + 8, ly2, { stroke: C.outer, width: 3, head: 11 });
    drawArrow(tl, link, 18.7, 0.6);
    code.mark(['mu'], C.bind, 19.7, { out: 21.3 });
    hideArrow(tl, link, 21.3, 0.3);
    // "Substitute it for Q, and the field accesses fold to S and U"
    st.to('substitute', cue('subst') - 0.1);
    const acc = ['a0', 'a1', 'b0', 'b1', 'b2'];
    acc.forEach((id, k) => look(code, [id, id + 'd', id + 'n'], 23.2 + k * 0.04, 24.25));
    st.to('rewrite', 24.35);
    code.swap(Cs, 24.25, { dur: 0.5 });
    // "Both calls pass a pair that ends in U, so both match"
    st.to('check', cue('match') - 0.1);
    const tOff = cue('delete') - 0.1;
    code.mark(['po', 'p0', 'pc', 'pu', 'pe'], C.good, 27.8, { out: tOff });
    code.mark(['ro', 's2', '+@2.2', 'u2', 'rc', 'u3', 're'], C.good, 28.3, { out: tOff });
    tickAfter(tl, svg, code, [')@0.2'], 29.6, tOff);
    tickAfter(tl, svg, code, [')@2.1'], 29.75, tOff);
    // "Delete the match"
    st.to('delete the match', cue('delete') - 0.1);
    const tGo = cue('delete') + 0.95;
    [['po'], ['pc', 'pu', 'pe'], ['ho'], ['hc', 'hu', 'he'], ['ro'], ['rc', 'u3', 're']].forEach((g, k) => code.strike(g, cue('delete') - 0.05 + k * 0.05, { out: tGo }));
    // "No pair is built any more. The loop is passed only the first field"
    st.out(tGo);
    code.swap(D, tGo, { dur: 0.5 });
    look(code, ['p0'], 35.95, 37.3); look(code, ['hs'], 36.3, 37.3);
    // "and it reads U from main: the output nests the loop inside main, where U is in scope"
    code.mark(['u1'], C.outer, 37.75, { out: 40.1 }); code.mark(['u2'], C.outer, 37.8, { out: 40.1 });
    code.mark(['mu'], C.bind, 38.7, { out: 40.1 });
    code.swap(Eo, 40.2, { dur: 0.5 });
    // "This is unboxing, together with copy propagation"
    nameOf(tl, root, 'Unboxing, with copy propagation', 45.0);
  });

})();

// ==== src/scenes/s02b_nocopy.js ====
// No code is copied: as constant propagation folds the code where it stands, so do patterns of the other kinds.
// Copies come only from specialization, a dial that is at zero until the chapter on policies.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  scene('nocopy', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 44;
    // ---- constant propagation, on the first loop -----------------------------------------------------------
    const y1 = 250;
    const p1 = new Code(tl, root, RAIL, y1, S), lh = p1.lh;
    const none = serif(root, RAIL, y1 + 120, 'No code was copied.', 64);
    fadeIn(tl, none, 2.8, 0.6, 16); fadeOut(tl, none, cue('think') - 0.4, 0.35, -14);
    p1.show('main(?i) = loop(i, {m1|1})\nloop(?i, {px|?x}) = if i == 0 then x else loop(i - 1, 2 - x)', cue('think') - 0.1, { stagger: 0.006 });
    const n1 = label(root, RAIL, y1 - 62, 'constant propagation');
    fadeIn(tl, n1, cue('think') + 0.9, 0.5, 10);
    // "It finds which values are constants"
    p1.mark(['px'], C.pat, cue('finds') + 0.2, { out: cue('folds') - 0.05 });
    p1.mark(['m1'], C.dim, cue('finds') + 0.5, { fill: 0.08, out: cue('folds') - 0.05 });
    // "and folds the code where it stands"
    p1.swap('main(?i) = loop(i)\nloop(?i) = if i == 0 then 1 else loop(i - 1)', cue('folds') + 0.15, { dur: 0.5 });
    // "Nothing is copied"
    const k1 = label(root, RAIL, y1 + 2 * lh + 20, 'two blocks in, two blocks out', { color: C.ink });
    fadeIn(tl, k1, cue('folds') + 1.3, 0.5, 10);
    // ---- "Patterns work in the same way, with more kinds of fact": the unboxing loop ------------------------
    const tSame = cue('same'), tIn = cue('inplace');
    for (const e of [p1.root, n1, k1]) tl.to(e, { o: 0.45 }, tSame - 0.1, 0.5);
    const y2 = 560;
    const p2 = new Code(tl, root, RAIL, y2, S);
    p2.show('main(?u, ?n) = loop(n, (0, u))\nloop(?i, ?q) =\n  if i == 0 then q.0 + q.1 else loop(i - 1, (q.0 + q.1, q.1))', tSame + 0.1, { stagger: 0.004, byLine: 0.06 });
    const n2 = label(root, RAIL, y2 - 62, 'unboxing');
    fadeIn(tl, n2, 14.9, 0.5, 10);
    // "every block is simplified in place"
    p2.swap('main(?u, ?n) = loop(n, 0)\n  where loop(?i, ?s) =\n    if i == 0 then s + {u1|u|o} else loop(i - 1, s + {u2|u|o})', tIn + 0.6, { dur: 0.5 });
    const k2 = label(root, RAIL, y2 + 3 * lh + 20, 'two blocks in, two blocks out', { color: C.ink });
    fadeIn(tl, k2, 18.5, 0.5, 10);
    // ---- "Copies come only from a separate dial, specialization": the dial of the later chapter, at its first stop
    const tD = cue('dial'), tZ = cue('zero');
    const LX = 1520, top = 330, step = 105, ys = [0, 1, 2, 3, 4].map(i => top + i * step);
    const head = label(root, LX - 16, top - 96, 'specialization');
    fadeIn(tl, head, 22.1, 0.5, 10);
    const line = path(tl, svg, `M ${LX} ${ys[0] - 22} L ${LX} ${ys[4] + 22}`, { stroke: C.faint, width: 3 });
    tl.to(line, { draw: 1 }, tD + 1.3, 1.0, E.io);
    ys.forEach((y, i) => {
      const s = el(svg, 'circle'); s.setAttribute('cx', LX); s.setAttribute('cy', y); s.setAttribute('r', 7);
      s.style.fill = C.bg; s.style.stroke = C.dim; s.setAttribute('stroke-width', 3);
      tl.set(s, { o: 0 }, 0); tl.to(s, { o: 1 }, tD + 1.5 + i * 0.15, 0.4);
      if (i === 0) tl.to(s, { fill: C.ink, stroke: C.ink }, tZ + 0.2, 0.3);
    });
    const mk = el(svg, 'circle'); mk.setAttribute('cx', LX); mk.setAttribute('cy', ys[0]); mk.setAttribute('r', 15);
    mk.style.fill = 'none'; mk.style.stroke = C.ink; mk.setAttribute('stroke-width', 3.5);
    tl.set(mk, { o: 0 }, 0); tl.to(mk, { o: 1 }, tZ + 0.2, 0.4);
    const zero = label(root, LX + 40, ys[0] - 36, 'at zero:\nno copies', { color: C.ink, lineHeight: 1.5 });
    fadeIn(tl, zero, tZ + 0.9, 0.5, 10);
  });
})();

// ==== src/scenes/s03_stable.js ====
// Stable patterns: the definition, three candidate patterns for the unboxing loop, and why stability is enough.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  scene('stable_a', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    // "We call them stable"
    const word = serif(root, RAIL, 420, 'Stable', 170, { color: C.good, transformOrigin: '0 0' });
    fadeIn(tl, word, cue('call') + 0.45, 0.8, 26);
    // "Patterns are stable if ...": the word stays while the condition is set up, then goes up; "every call that remains matches the pattern of the block"
    tl.to(word, { y: -250, s: 0.42 }, cue('every') - 0.95, 0.75, E.io);
    const d1 = serif(root, RAIL, 300, 'Every call that remains matches the pattern', 52);
    const d2 = serif(root, RAIL, 366, 'of the block it calls.', 52);
    fadeIn(tl, d1, cue('every') - 0.1, 0.7, 20);
    fadeIn(tl, d2, 12.95, 0.7, 20);
    const tEx = cue('ex');
    tl.to(d1, { o: 0.55 }, tEx - 0.3, 0.5); tl.to(d2, { o: 0.55 }, tEx - 0.3, 0.5);

    // three candidates for the unboxing loop, in a column, with a verdict column to the right
    const S = 50, cy0 = 490, cgap = 96, vx = RAIL + 19 * charWidth(S);
    const cands = [
      'loop(?i, {o|(|p}?s, {u|u|o}{e|)|p})',
      'loop(?i, ?q)',
      'loop(?i, {o|(|p}{z|0|p}, {u|u|o}{e|)|p})',
    ];
    const at = [tEx - 0.15, cue('trivial') - 0.15, cue('not') - 0.15];
    const codes = cands.map((src, i) => { const c = new Code(tl, root, RAIL, cy0 + i * cgap, S); c.show(src, at[i], { stagger: 0.02 }); return c; });
    const verdict = (i, ok, t, text) => {
      const c = codes[i], y = cy0 + i * cgap + c.lh / 2;
      if (ok) { const k = tick(tl, svg, vx, y + 2, 30, C.good, 5); tl.to(k, { draw: 1 }, t, 0.35); }
      else cross(tl, svg, vx, y, 24, C.bad, 5).forEach(k => tl.to(k, { draw: 1 }, t, 0.3));
      const l = label(root, vx + 40, y - 16, text, { color: ok ? C.good : C.bad });
      fadeIn(tl, l, t + 0.05, 0.5, 10);
    };
    // "this pattern is stable", "So is the pattern that says nothing"
    verdict(0, true, 17.4, 'stable');
    verdict(1, true, 20.2, 'stable');
    // the first two step back while the third is talked about
    tl.to(codes[0].root, { o: 0.55 }, cue('not') - 0.2, 0.5); tl.to(codes[1].root, { o: 0.55 }, cue('not') - 0.2, 0.5);
    // "It claims that the first field is always zero"
    const tZ = 23.6;
    codes[2].mark(['z'], C.pat, tZ, { out: 29.85 });
    // its clause, under the column
    const K = new Code(tl, root, RAIL, cy0 + 3 * cgap + 34, 44);
    K.show('loop(?i, {ko|(|p}{k0|0|p}, {ku|u|o}{ke|)|p}) = if i == 0 then {b1|u|o} else loop(i - 1, ({c1|u|o}, {c2|u|o}))', 24.6, { stagger: 0.006 });
    // "Under that claim, the loop's own call passes U in that place, not zero"
    K.mark(['loop@0.2', '(@0.2', 'i@0.2', '-@0.1', '1@0.1', ',@0.3', '(@0.3', 'c1', ',@0.4', 'c2', ')@0.2', ')@0.3'], C.dim, 27.05, { fill: 0.08, out: 28.55 });
    K.mark(['c1'], C.bad, 28.6, { fill: 0.24 });
    K.mark(['k0'], C.bad, 29.95, { fill: 0.24 });
    codes[2].mark(['z'], C.bad, 29.95, { fill: 0.24 });
    verdict(2, false, 30.2, 'not stable');
  });

  scene('stable_b', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    // "Stability is a fixed-point condition, like an inductive invariant"
    const line = serif(root, RAIL, 340, 'A fixed-point condition, like an inductive invariant.', 56);
    fadeIn(tl, line, cue('fixed') - 0.2, 0.7, 20);
    // "When the program runs, every call matches"
    const run = label(root, RAIL, 440, 'when the program runs, every call matches');
    fadeIn(tl, run, cue('runtime') - 0.1, 0.6, 12);
    const tA = cue('anyway');
    tl.to(line, { o: 0.55 }, tA - 0.3, 0.5); tl.to(run, { o: 0.55 }, tA - 0.3, 0.5);
    // the flow: patterns from anywhere -> one pass: are they stable -> use them
    const bw = 440, bh = 150, ag = 110, by = 650;
    const texts = [['patterns,', 'from anywhere'], ['one pass:', 'are they stable'], ['use them']];
    // box 1 a moment after the line; boxes 2 and 3 at "check" and "use them"
    const times = [cue('fixed') + 1.5, 14.45, 16.95];
    texts.forEach((t, i) => {
      const x = RAIL + 30 + i * (bw + ag);
      const b = box(root, x, by, { width: bw + 'px', height: bh + 'px', borderRadius: '18px', background: alpha(C.panel, 0.9), boxShadow: `inset 0 0 0 1.5px ${C.line}`, display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center' });
      t.forEach(s => el(b, 'div', { position: 'relative', fontFamily: 'var(--sans)', fontSize: '28px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: i === 1 && s.includes('stable') ? C.good : C.ink, whiteSpace: 'pre', lineHeight: '44px' }, s));
      fadeIn(tl, b, times[i], 0.6, 18);
      if (i > 0) {
        const a = arrow(tl, svg, x - ag + 18, by + bh / 2, x - 18, by + bh / 2, { stroke: C.dim, width: 3, head: 12 });
        drawArrow(tl, a, times[i] - 0.25, 0.4);
      }
    });
  });
})();

// ==== src/scenes/s04_hard.js ====
// Finding the patterns: why the most specific stable patterns are hard to find. The four-parameter loop and its
// facts (hard_a), then its six stable patterns as a ladder, least specific first (hard_b).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const LOOK = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out });

  // ---- hard_a: the loop, and what is always true of its parameters ------------------------------------------
  scene('hard_a', ({ tl, root, cue }) => {
    // "The difficult part is finding them": the key phrase, alone, until the loop arrives
    const tD = cue('difficult'), tC = cue('consider');
    const kp = serif(root, 160, 500, 'Many stable patterns. We want the most specific.', 60);
    fadeIn(tl, kp, tD - 0.2, 0.8, 22);
    fadeOut(tl, kp, tC - 0.75, 0.4);

    const code = new Code(tl, root, 160, 290, 44);
    code.show(
      'main(?u, ?n) = loop(n, {mu|u}, {m1|1}, {ms|Some|f}{mp|(}{mp2|(}{m0|0}{mc|,} {mu2|u}{mq2|)}{mq|)})\n' +
      'loop(?i, {ha|?a}, {hx|?x}, {hq|?q}) =\n' +
      '  case q of None → 0 | Some((?s, ?t)) →\n' +
      '  if i == 0 then s + t\n' +
      '  else if x == 1 then\n' +
      '    loop(i - 1, {ra|a}, {r2|2} {rm|-} {rx|x}, Some((s + a, {t0|t} {tp|+} {tl|(}{t1|t} {tmi|-} {ta|a}{tr|)})))\n' +
      '  else loop(i - 1, i, 99, q)', tC - 0.3, { stagger: 0.0015, byLine: 0.03 });

    // "X is always one": the parameter, where its value comes in, and what the loop passes back
    // "Recall the loop from the start"
    const lfs = label(root, 160, 228, 'the loop from the start');
    fadeIn(tl, lfs, tC - 0.3, 0.5, 10);
    fadeOut(tl, lfs, cue('x') - 0.3, 0.3);

    const tX = cue('x'), tDead = cue('dead'), tA = cue('a'), tQ = cue('q'), tDep = cue('depend');
    LOOK(code, ['hx'], tX - 0.2, tX + 0.5);
    LOOK(code, ['m1'], tX + 0.4, tX + 1.0);
    LOOK(code, ['r2', 'rm', 'rx'], tX + 0.9, tDead + 0.2);
    // "so the last line never runs"
    code.fade(t => t.line === 6, 0.5, tDead - 0.1, 0.6);

    // "A is always main's U": the parameter, main's u, and the a that the remaining call passes
    // ("Because it never runs" comes first: "A is" is at a + 1.5, "main's" at a + 2.7, build/audio/hard_a.json)
    LOOK(code, ['ha'], tA + 1.3, tA + 2.6);
    LOOK(code, ['mu'], tA + 2.5, tA + 3.4);
    LOOK(code, ['ra'], tA + 3.3, tQ - 0.25);

    // "Q is always Some, of a pair whose second field is U"
    LOOK(code, ['hq'], tQ - 0.2, tQ + 0.7);
    LOOK(code, ['ms', 'mp', 'mp2', 'm0', 'mc', 'mu2', 'mq2', 'mq'], tQ + 1.0, tQ + 2.7);
    LOOK(code, ['t0', 'tp', 'tl', 't1', 'tmi', 'ta', 'tr'], tQ + 2.6, tDep - 0.25);

    // "These facts depend on themselves, and on one another": what the loop passes back is computed from
    // what it was given
    LOOK(code, ['r2', 'rm', 'rx'], tDep - 0.15, cue('assumed') + 1.6);
    LOOK(code, ['t0', 'tp', 'tl', 't1', 'tmi', 'ta', 'tr'], tDep + 0.35, cue('assumed') + 1.6);
    code.pulse(['rx'], tDep + 1.2, { dur: 0.7 });
    code.pulse(['t0', 't1', 'ta'], tDep + 2.4, { dur: 0.7 });
  });

  // ---- hard_b: the six stable patterns, from the least specific to the most --------------------------------
  scene('hard_b', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 44, cw = charWidth(S), lh = Math.round(S * 1.62), x0 = 160, top = 245, gap = 104;
    const ry = k => top + k * gap;
    const ROWS = [
      ['loop(?i, ?a, ?x, ?q)', 'says nothing', null],
      ['loop(?i, ?a, {n|1|p}, ?q)', 'conditional constant propagation', ['n']],
      ['loop(?i, {n|u|o}, {a1|1|p}, ?q)', "Lemerre's analysis", ['n']],
      ['loop(?i, {a2|u|o}, {a1|1|p}, {n0|Some|p}{n1|(|p}{n2|?p}{n3|)|p})', 'the option is unboxed', ['n0', 'n1', 'n2', 'n3']],
      ['loop(?i, {a2|u|o}, {a1|1|p}, {s0|Some|p}{s1|(|p}{n0|(|p}{n1|?s}, {n2|?t}{n3|)|p}{s3|)|p})', 'and the pair in it', ['n0', 'n1', 'n2', 'n3']],
      ['loop(?i, {a2|u|o}, {a1|1|p}, {s0|Some|p}{s1|(|p}{s2|(|p}?s, {n|u|o}{s4|)|p}{s3|)|p})', 'the most specific', ['n']],
    ];
    const ts = [cue('p1'), cue('p2'), cue('p3'), cue('p4'), cue('p5'), cue('p6')];
    const capX = x0 + 32 * cw;
    const rows = ROWS.map(([src, cap, fresh], k) => {
      const code = new Code(tl, root, x0, ry(k), S);
      code.show(src, k === 0 ? cue('six') + 0.3 : ts[k] - 0.25, { stagger: 0.01 });
      // the first row is on screen from "six"; at "p1" it is pointed at
      if (k === 0) code.mark(/.*/, C.dim, ts[0] - 0.15, { fill: 0.08, out: ts[1] - 0.3 });
      if (fresh) code.mark(fresh, C.dim, ts[k] + 0.25, { fill: 0.08, out: (ts[k + 1] ?? cue('none')) - 0.3 });
      const c = label(root, capX, ry(k) + lh / 2 - 15, cap, { fontSize: '26px', color: k === 5 ? C.ink : C.dim });
      fadeIn(tl, c, ts[k] + 0.05, 0.5, 10);
      return { code, cap: c };
    });

    // "from the least specific to the most": an arrow down the left, its label in a break of the line
    const tS = cue('six'), ax = 112, y0 = ry(0) + 8, y1 = ry(5) + lh - 8, my = (y0 + y1) / 2, half = 118;
    const seg1 = path(tl, svg, `M ${ax} ${y0} L ${ax} ${my - half - 12}`, { stroke: C.dim, width: 3 });
    const arr = arrow(tl, svg, ax, my + half + 12, ax, y1, { stroke: C.dim, width: 3, head: 12 });
    tl.to(seg1, { draw: 1 }, tS + 0.2, 0.5, E.io); drawArrow(tl, arr, tS + 1.3, 0.6);
    const ms = label(root, ax - 150, my - 15, 'more specific', { fontSize: '26px', width: '300px', textAlign: 'center' });
    tl.set(ms, { r: -90, o: 0 }, 0); tl.to(ms, { o: 1 }, tS + 0.5, 0.7);

    // "The last is the most specific": it stays bright, the others dim
    const t6 = cue('p6');
    for (let k = 0; k < 5; k++) { tl.to(rows[k].code.root, { o: 0.55 }, t6 - 0.1, 0.5); tl.to(rows[k].cap, { o: 0.55 }, t6 - 0.1, 0.5); }

    // "None of the seven published analyses ... finds all of it": the captions give way to a bracket over the
    // first three rows
    const tN = cue('none'), tL = cue('llvm');
    for (const r of rows) fadeOut(tl, r.cap, tN - 0.35, 0.3, 0);
    const bx = x0 + 31 * cw, by0 = ry(0) + 10, by1 = ry(2) + lh - 10;   // rows 1 to 3: none of the seven looks inside q
    const br = path(tl, svg, `M ${bx} ${by0} L ${bx + 18} ${by0} L ${bx + 18} ${by1} L ${bx} ${by1}`, { stroke: C.dim, width: 3 });
    tl.to(br, { draw: 1 }, tN - 0.1, 0.6, E.io);
    const bl = label(root, bx + 56, (by0 + by1) / 2 - 62, 'seven published analyses\nstop here or earlier', { fontSize: '26px', lineHeight: 1.6 });
    fadeIn(tl, bl, tN + 0.2, 0.6, 10);
    const bl2 = label(root, bx + 56, (by0 + by1) / 2 + 26, "from SCCP to Click's combined analysis", { fontSize: '26px', letterSpacing: '0.12em' });
    tl.set(bl2, { y: 10, o: 0 }, 0); tl.to(bl2, { y: 0, o: 0.72 }, tN + 1.2, 0.6, E.out5);
    // "and LLVM, at O three, finds all but the last step": row 5
    rows[4].code.mark(/.*/, C.dim, tL - 0.15, { fill: 0.08 });
    tl.to(rows[4].code.root, { o: 1 }, tL - 0.15, 0.4);
    const ll = label(root, bx + 56, ry(4) + lh / 2 - 15, 'LLVM -O3', { fontSize: '26px', color: C.ink });
    fadeIn(tl, ll, tL - 0.05, 0.5, 10);
  });
})();

// ==== src/scenes/s05_refute.js ====
// Refutation: the join, then two rounds of the algorithm on the four-parameter loop, the output, and the cycle.
// Colours: amber is assumed (a pattern), cyan a binder, violet a name from scope, red refuted, green confirmed.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;

  // the width of a line of small-caps text, measured off-stage
  function measure(text, style) {
    const m = document.createElement('span');
    Object.assign(m.style, { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' }, style);
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return w;
  }

  // ============================================ assume0 ========================================================
  scene('assume0', ({ tl, root, cue, seg }) => {
    const w = t => seg('assume0') + t;   // a word's time in the segment
    // "We find the patterns by refutation." The key phrase, in two halves so that the second can be lit
    const phrase = serif(root, 160, 300, '', 64);
    const half = t => { const e = document.createElement('span'); e.textContent = t; e.style.color = C.ink; phrase.appendChild(e); return e; };
    const p1 = half('Assume. '), p2 = half('Then let the program refute it.');
    fadeIn(tl, phrase, cue('instead') - 0.25, 0.8, 24);
    tl.to(p1, { color: C.dim }, cue('exactly') - 0.2, 0.5); tl.to(p2, { color: C.dim }, cue('exactly') - 0.2, 0.5);
    // "a block's pattern is exactly the arguments of the calls that reach it"
    const S = 44, cy = 580;
    const call = new Code(tl, root, 160, cy, S);
    call.show('loop(n, u, 1, Some((0, u)))', cue('exactly') - 0.1);
    const hx = 1040, svg = svgLayer(root), my = cy + call.lh / 2;
    const ar = arrow(tl, svg, 160 + 27 * call.cw + 30, my, hx - 30, my);
    drawArrow(tl, ar, w(9.3), 0.5);
    const head = new Code(tl, root, hx, cy, S);
    head.show('loop({n|n|o}, {u|u|o}, {1|1|p}, {S|Some|p}{a|((|p}{0|0|p}{c|,|p} {u2|u|o}{z|))|p})', w(9.7), { stagger: 0.01 });
    const lab = label(root, hx, cy - 46, 'the pattern is the call');
    fadeIn(tl, lab, w(10.2), 0.5, 10);
    // "Then let the program refute it."
    tl.to(p2, { color: C.ink }, cue('then') - 0.2, 0.5);
  });

  // ============================================ join ===========================================================
  scene('join', ({ tl, root, cue, seg }) => {
    const w = t => seg('join') + t;   // a word's time in the segment
    // "When several calls reach a block, its pattern is their join"
    const S = 50, cy1 = 380, cy2 = 620, jx = 960, jy = 500;
    const c1 = new Code(tl, root, 160, cy1, S), c2 = new Code(tl, root, 160, cy2, S);
    c1.show('f({a1|0}, {b1|0})', cue('when') - 0.2);
    c2.show('f({a2|1}, {b2|1})', cue('when') - 0.05);
    const svg = svgLayer(root);
    const lh = c1.lh, cwid = 7 * c1.cw;
    const ar1 = arrow(tl, svg, 160 + cwid + 40, cy1 + lh / 2, jx - 40, jy + lh / 2 - 14, { bend: -30 });
    const ar2 = arrow(tl, svg, 160 + cwid + 40, cy2 + lh / 2, jx - 40, jy + lh / 2 + 14, { bend: 30 });
    drawArrow(tl, ar1, w(3.4), 0.6); drawArrow(tl, ar2, w(3.5), 0.6);
    const jl = label(root, jx, jy - 44, 'the join');
    fadeIn(tl, jl, w(3.7), 0.5, 10);

    // "Zero, zero and one, one join to a binder and then its name"
    c1.mark(['a1', 'b1'], C.dim, w(10.15), { fill: 0.08, out: w(11.6) });
    c2.mark(['a2', 'b2'], C.dim, w(11.65), { fill: 0.08, out: w(13.1) });
    const j = new Code(tl, root, jx, jy, S);
    j.show('f({h1|?h},   {hz|)}', w(13.2), { stagger: 0.02 });
    j.morph('f({h1|?h}, {h2|h|o}{hz|)}', w(14.2), { dur: 0.5 });
    // "the two arguments are equal"
    j.mark(['h1', 'h2'], C.dim, w(15.35), { fill: 0.08, out: w(17.6) });

    // "Zero, zero and one, two join to two binders."
    c2.swap('f({a2|1}, {b2|2})', w(19.3));
    c2.mark(['b2'], C.dim, w(19.45), { fill: 0.08, out: w(21.6) });
    j.swap('f({h1|?h₁|b}, {h2|?h₂|b})', w(19.95));
  });

  // ======================================= ref1, ref2, ref3 ====================================================
  scene(['ref1', 'ref2', 'ref3'], ({ tl, root, cue, seg }) => {
    const A = t => seg('ref1') + t, B = t => seg('ref2') + t, D = t => seg('ref3') + t;   // word times
    const R1 = n => cue('ref1.' + n), R2 = n => cue('ref2.' + n), R3 = n => cue('ref3.' + n);
    const S = 40, x0 = 160, y0 = 170;
    const code = new Code(tl, root, x0, y0, S);
    const lh = code.lh;

    // ---- the program's states ------------------------------------------------------------------------------
    // sub maps a variable of the body to what the pattern puts there: [text, class]
    const V = sub => (id, v) => sub[v] ? `{${id}|${sub[v][0]}|${sub[v][1]}}` : `{${id}|${v}}`;
    const r1 = { i: ['n', 'o'], a: ['u', 'o'], x: ['1', 'p'], s: ['0', 'p'], t: ['u', 'o'] };
    const r2 = { a: ['u', 'o'], x: ['1', 'p'], t: ['u', 'o'] };
    // a fold is 0 (not yet), 1 (the folded tokens gone, a gap left), 2 (the gap closed)
    const ifLine = (sub, fs) => {
      const v = V(sub);
      const Sx = fs === 0 ? `${v('s1', 's')} {pl1|+} ${v('t1', 't')}` : fs === 1 ? `    ${v('t1', 't')}` : v('t1', 't');
      return `  {b_if|if} ${v('i1', 'i')} {b_eq|==} {b_0|0} {b_th|then} ${Sx}`;
    };
    const eifLine = sub => { const v = V(sub); return `  {el1|else} {ei|if} ${v('x1', 'x')} {eq|==} {one|1} {th|then}`; };
    const callBody = (sub, f1, fs, ft) => {
      const v = V(sub);
      const X = f1 === 0 ? `{two|2} {mx|-} ${v('x2', 'x')}` : f1 === 1 ? `    ${v('x2', 'x')}` : v('x2', 'x');
      const Sx = fs === 0 ? `${v('s5', 's')} {pl5|+} ${v('a5', 'a')}` : fs === 1 ? `    ${v('a5', 'a')}` : v('a5', 'a');
      const T = ft === 0 ? `${v('t5', 't')} {pl6|+} {op6|(}${v('t6', 't')} {mi6|-} ${v('a6', 'a')}{cl6|)}` : ft === 1 ? v('t5', 't') + ' '.repeat(10) : v('t5', 't');
      return `{lp|loop|f}{lpo|(}${v('i2', 'i')} {m2|-} {n2|1}{k1|,} ${v('a2', 'a')}{k2|,} ${X}{k3|,} {S5|Some|f}{pA|((}${Sx}{cm5|,} ${T}{pZ|))}{pZl|)}`;
    };
    const Q0 = '{q6|q}', Q1 = '{q6|Some|p}{q6a|((|p}{q60|0|p}{q6c|,|p} {q6u|u|o}{q6z|))|p}';
    const lastLine = (sub, q) => { const v = V(sub); return `  {el|else} {l6|loop|f}{l6o|(}${v('i3', 'i')} {l6m|-} {l6n|1}{l6k1|,} ${v('i4', 'i')}{l6k2|,} {nn|99}{l6k3|,} ${q}{l6z|)}`; };
    const CASE = '  case q of None → 0 | Some((?s, ?t)) →';
    const MAIN = 'main(?u, ?n) = loop({cn|n}{mk1|,} {cu|u}{mk2|,} {c1|1}{mk3|,} {cS|Some}{cpa|((}{c0|0}{cc|,} {cu2|u}{cpz|))}{mz|)}';
    const HSRC = '{lh|loop|f}{lho|(}{pi|?i}{hk1|,} {pa|?a}{hk2|,} {px|?x}{hk3|,} {pq|?q}{hz|)} {heq|=}';
    const HEAD = (i, s) => `{lh|loop|f}{lho|(}${i}{hk1|,} {pa|u|o}{hk2|,} {px|1|p}{hk3|,} {pq|Some|p}{pqa|((|p}${s}{pqc|,|p} {pt|u|o}{pqz|))|p}{hz|)} {heq|=}`;
    const H1 = HEAD('{pi|n|o}', '{p0|0|p}'), H2 = HEAD('{pi|?i}', '{p0|?s}');
    const J = (...ls) => ls.join('\n');
    const SRC = J(MAIN, HSRC, CASE, ifLine({}, 0), eifLine({}), '    ' + callBody({}, 0, 0, 0), lastLine({}, Q0));
    const R1head = J(MAIN, H1, CASE, ifLine({}, 0), eifLine({}), '    ' + callBody({}, 0, 0, 0), lastLine({}, Q0));
    const R1up = J(MAIN, H1, ifLine({}, 0), eifLine({}), '    ' + callBody({}, 0, 0, 0), lastLine({}, Q0));
    const R1sub = J(MAIN, H1, ifLine(r1, 0), eifLine(r1), '    ' + callBody(r1, 0, 0, 0), lastLine(r1, Q1));
    const R1dead = J(MAIN, H1, ifLine(r1, 0), '  {el1|else}', '    ' + callBody(r1, 0, 0, 0));
    const R1f1a = J(MAIN, H1, ifLine(r1, 0), '  {el1|else}', '    ' + callBody(r1, 1, 0, 0));
    const R1f1b = J(MAIN, H1, ifLine(r1, 0), '  {el1|else}', '    ' + callBody(r1, 2, 0, 0));
    const R1f2a = J(MAIN, H1, ifLine(r1, 1), '  {el1|else}', '    ' + callBody(r1, 2, 1, 1));
    const R1f2b = J(MAIN, H1, ifLine(r1, 2), '  {el1|else}', '    ' + callBody(r1, 2, 2, 2));
    const R1join = J(MAIN, H1, ifLine(r1, 2), '  {el1|else} ' + callBody(r1, 2, 2, 2));
    const R2head = J(MAIN, H2, CASE, ifLine({}, 0), eifLine({}), '    ' + callBody({}, 0, 0, 0), lastLine({}, Q0));
    const R2simp = J(MAIN, H2, ifLine(r2, 0), '  {el1|else} ' + callBody(r2, 2, 0, 2));

    // ---- the grid: the loop's five places ------------------------------------------------------------------
    const gx = 160, gy = 652, labelW = 220, colW = 230, gap = 12, rowH = 80, headH = 84;
    const cols = ['i', 'a', 'x', 's', 't'].map(h => ({ w: colW, head: h }));
    const grid = new Grid(tl, root, gx, gy, { cols, labelW, colW, gap, rowH, size: 38, headH });
    grid.heads.forEach(h => { h.style.top = '40px'; h.style.fontSize = '30px'; h.style.color = C.code; });
    const qHead = box(grid.root, grid.cx[3], 0, { width: (2 * colW + gap) + 'px', textAlign: 'center', fontFamily: 'var(--mono)', fontSize: '28px', color: C.dim, whiteSpace: 'pre' }, 'q = Some((s, t))');
    const places = label(root, gx + labelW, gy - 2, "the loop's places");
    const gridB = new Grid(tl, root, gx, gy + rowH + gap, { cols, labelW, gap, rowH, size: 38, headH });   // round 2's call, in the second row
    const rightX = gx + grid.width + 40;
    const verdictY = gy + headH + rowH + gap / 2 - 16;

    // the round, top right
    const chip = box(root, 1810 - 250, 160, { width: '250px', height: '62px', borderRadius: '31px', boxShadow: `inset 0 0 0 2px ${alpha(C.ink, 0.5)}`, display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 600, letterSpacing: '0.2em', color: C.ink, whiteSpace: 'pre' }, 'ROUND 1');
    tl.set(chip, { o: 0, y: -14 }, 0);
    // the step, under the code at its left edge
    const step = label(root, x0, 0, '');
    tl.set(step, { o: 0 }, 0);
    const under = n => y0 + n * lh + 8;
    const stepShow = (text, at, n) => { tl.to(step, { o: 0 }, at - 0.2, 0.2); tl.text(step, text, at); tl.set(step, { y: under(n) }, at); tl.to(step, { o: 1 }, at, 0.35); };
    const stepMove = (n, at, d = 0.6) => tl.to(step, { y: under(n) }, at, d, E.io);
    const stepHide = at => tl.to(step, { o: 0 }, at, 0.3);
    const bigLabels = g => { for (const r of g.rows.values()) r.lab.style.fontSize = '26px'; };
    const LOOK = (sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out });
    const cellPulse = (g, row, j, at) => { const b = g.rows.get(row).cells[j].b; tl.to(b, { s: 1.06 }, at, 0.25, E.out); tl.to(b, { s: 1 }, at + 0.25, 0.4, E.io); };

    // ======================================= round 1 ==========================================================
    code.show(SRC, 0.2, { stagger: 0.003, byLine: 0.05, dur: 0.45 });
    tl.to(chip, { o: 1, y: 0 }, R1('r1') - 0.15, 0.6, E.out5);
    // "Main's call is the first to reach the loop"
    const mainCall = t => t.line === 0 && t.col >= 15;
    LOOK(mainCall, R1('first') - 0.1, R1('simp') - 0.3);
    // the loop's places
    grid.showHead(A(3.6));
    fadeIn(tl, qHead, A(3.8), 0.5, 10);
    fadeIn(tl, places, A(3.6), 0.5, 10);
    fadeOut(tl, places, R1('simp') - 0.2, 0.3);
    // "so it is the loop's pattern: N, U, one, and Some of the pair zero, U"
    code.swap(R1head, A(5.3));
    grid.row('pat', 'pattern', A(5.5));
    const pat1 = [['n', C.outer, 'cn', 'pi', A(6.98)], ['u', C.outer, 'cu', 'pa', A(7.54)], ['1', C.pat, 'c1', 'px', A(8.18)],
      ['0', C.pat, 'c0', 'p0', A(9.94)], ['u', C.outer, 'cu2', 'pt', A(10.58)]];
    pat1.forEach(([txt, col, from, to, t], j) => {
      grid.cell('pat', j, txt, t - 0.1, { color: col }); grid.tint('pat', j, col, t - 0.1, { fill: 0.1, line: 0.5 });
      code.pulse([from], t - 0.15, { color: col, dur: 0.6 }); code.pulse([to], t - 0.05, { color: col, dur: 0.6 });
    });
    code.pulse(['cS', 'pq'], A(9.0), { color: C.pat, dur: 0.6 });

    // "Simplify the body under it": the case line goes (the pattern decides it), then the substitution
    code.fade(t => t.line === 0, 0.55, R1('simp') - 0.7, 0.5);
    code.fade(t => t.line === 2, 0, R1('simp') - 0.9, 0.25);
    code.morph(R1up, R1('simp') - 0.65, { dur: 0.45, stagger: 0 });
    code.swap(R1sub, R1('simp'), { dur: 0.5 });
    stepShow('simplify', R1('simp') + 0.45, 6);
    // "X is one, so the test is decided, and the last line is dead."
    LOOK(['x1', 'eq', 'one'], R1('x1') - 0.1, A(16.5));
    const st1 = code.strike(['ei', 'x1', 'eq', 'one', 'th'], A(16.55), { dur: 0.35 });
    const st2 = code.strike(t => t.line === 5, A(16.7), { dur: 0.45 });
    code.swap(R1dead, A(17.85), { dur: 0.5 });
    tl.to(st1, { o: 0 }, A(17.85), 0.25); tl.to(st2, { o: 0 }, A(17.85), 0.25);
    stepMove(5, A(17.85), 0.5);
    // "Two minus one folds to one"
    LOOK(['two', 'mx', 'x2'], R1('fold') - 0.1, A(19.6));
    code.morph(R1f1a, A(19.6), { dur: 0.25, stagger: 0 });
    code.morph(R1f1b, A(19.8), { dur: 0.45, stagger: 0 });
    // "and U plus, U minus U, folds to U" (and 0 + u, in both places)
    LOOK(['t5', 'pl6', 'op6', 't6', 'mi6', 'a6', 'cl6'], R1('fold2') + 0.2, A(23.25));
    code.morph(R1f2a, A(23.25), { dur: 0.25, stagger: 0 });
    code.morph(R1f2b, A(23.45), { dur: 0.45, stagger: 0 });
    // the call joins its else
    code.morph(R1join, A(24.15), { dur: 0.6, stagger: 0 });
    const lift = -90;
    tl.to(grid.root, { y: lift }, A(24.15), 0.6, E.io);
    tl.to(step, { o: 0 }, A(23.95), 0.2); tl.set(step, { y: under(4) }, A(24.3)); tl.to(step, { o: 1 }, A(24.75), 0.3);
    // "One call is left."
    const recCall = t => t.line === 3 && t.col >= 7;
    LOOK(recCall, R1('call') - 0.1, R2('discard') - 0.2);
    // "Check it against the pattern, place by place."
    stepShow('check', R1('check') - 0.1, 4);
    grid.row('call', 'call', R1('check') - 0.1);
    const call1 = ['n - 1', 'u', '1', 'u', 'u'];
    call1.forEach((a, j) => grid.cell('call', j, a, R1('check') + 0.15 + j * 0.12));
    [1, 2, 4].forEach((j, k) => { const t = A(28.15) + k * 0.28; grid.mark('call', j, true, t); grid.tint('call', j, C.good, t, { fill: 0.07, line: 0.45 }); });
    // "It differs in two places: N minus one against N, and U against zero."
    const refuteCol = (j, at) => {
      for (const r of ['pat', 'call']) { grid.tint(r, j, C.bad, at, { fill: 0.16, line: 0.9 }); grid.recolor(r, j, C.bad, at); }
      grid.mark('call', j, false, at);
    };
    refuteCol(0, R1('d1') - 0.1);
    cellPulse(grid, 'call', 0, A(31.7)); cellPulse(grid, 'pat', 0, A(33.3));
    refuteCol(3, R1('d2') - 0.1);
    cellPulse(grid, 'call', 3, A(34.1)); cellPulse(grid, 'pat', 3, A(34.85));
    // "The pattern is refuted."
    const refuted = label(root, rightX, verdictY + lift, 'refuted', { color: C.bad, fontSize: '28px' });
    fadeIn(tl, refuted, R1('refuted') - 0.1, 0.5, 10);
    fadeOut(tl, refuted, R2('discard') - 0.2, 0.3);

    // ======================================= between the rounds ===============================================
    // "a binder at each place where the call differed. We call this the skeleton."
    grid.row('skel', 'skeleton', R2('skel') - 0.1);
    const skel = grid.rows.get('skel');
    tl.set(skel.lab, { o: 0 }, R2('skel') - 0.1 + 0.001); tl.to(skel.lab, { o: 1, x: 0 }, B(7.15), 0.5, E.out5);
    grid.cell('skel', 0, '?i', B(3.35), { color: C.bind }); grid.tint('skel', 0, C.bind, B(3.35), { fill: 0.14, line: 0.8 });
    grid.cell('skel', 3, '?s', B(4.7), { color: C.bind }); grid.tint('skel', 3, C.bind, B(4.7), { fill: 0.14, line: 0.8 });
    [1, 2, 4].forEach((j, k) => grid.cell('skel', j, '·', B(5.3) + k * 0.06, { color: C.dim }));
    // "Everything else is discarded, including the values that the round computed"
    grid.hideRow('pat', R2('discard') - 0.2, { dur: 0.35 }); grid.hideRow('call', R2('discard') - 0.2, { dur: 0.35 });
    stepHide(R2('discard') - 0.2);
    const up = -2 * (rowH + gap), tUp = R2('discard') + 0.25;
    tl.to(skel.lab, { y: up }, tUp, 0.6, E.io);
    skel.cells.forEach(c => tl.to(c.b, { y: up }, tUp, 0.6, E.io));
    code.swap(MAIN, B(10.0), { dur: 0.8 });
    tl.to(grid.root, { y: 0 }, B(11.0), 0.8, E.io);
    // the program is the source again, before round 2
    code.swap(SRC, B(15.9), { dur: 0.6 });

    // ======================================= round 2 ==========================================================
    tl.to(chip, { sy: 0.05 }, R2('r2') - 0.3, 0.2, E.in); tl.text(chip, 'ROUND 2', R2('r2') - 0.1); tl.to(chip, { sy: 1 }, R2('r2') - 0.1, 0.35, E.back);
    // "Assume again: main's call, with binders where the skeleton has them."
    code.fade(t => t.line === 0, 1, R2('again') - 0.1, 0.4);
    tl.to(skel.lab, { o: 0 }, R2('again') - 0.3, 0.2); tl.text(skel.lab, 'pattern', R2('again') - 0.1); tl.to(skel.lab, { o: 1 }, R2('again') - 0.1, 0.3);
    LOOK(mainCall, B(19.5), B(28.3));
    code.swap(R2head, B(20.65), { dur: 0.5 });
    cellPulse(grid, 'skel', 0, B(21.6)); cellPulse(grid, 'skel', 3, B(21.75));
    code.pulse(['pi', 'p0'], B(21.6), { color: C.bind, dur: 0.6 });
    // "The U, the one, and the U in the pair come back, because main's call passes them."
    [[1, 'u', C.outer, 'cu', 'pa', B(23.44)], [2, '1', C.pat, 'c1', 'px', B(24.08)], [4, 'u', C.outer, 'cu2', 'pt', B(24.96)]].forEach(([j, txt, col, from, to, t]) => {
      grid.cell('skel', j, txt, t - 0.1, { color: col }); grid.tint('skel', j, col, t - 0.1, { fill: 0.1, line: 0.5 });
      code.pulse([from], t - 0.15, { color: col, dur: 0.6 }); code.pulse([to], t - 0.05, { color: col, dur: 0.6 });
    });
    // "Simplify."
    code.swap(R2simp, R2('simp') - 0.25, { dur: 0.5 });
    stepShow('simplify', R2('simp') + 0.05, 4);
    // "Check the call."
    stepShow('check', R2('check') - 0.1, 4);
    LOOK(recCall, R2('check') - 0.1, R3('delete') - 0.2);
    gridB.row('call2', 'call', R2('check') - 0.1);
    bigLabels(grid); bigLabels(gridB);
    const call2 = ['i - 1', 'u', '1', 's + u', 'u'];
    call2.forEach((a, j) => gridB.cell('call2', j, a, R2('check') + 0.1 + j * 0.1));
    // "A binder matches anything, and the other places agree."
    [[0, B(31.7)], [3, B(32.05)]].forEach(([j, t]) => { cellPulse(grid, 'skel', j, t - 0.15); gridB.mark('call2', j, true, t); gridB.tint('call2', j, C.good, t, { fill: 0.07, line: 0.45 }); });
    [1, 2, 4].forEach((j, k) => { const t = B(33.2) + k * 0.25; gridB.mark('call2', j, true, t); gridB.tint('call2', j, C.good, t, { fill: 0.07, line: 0.45 }); });
    // "so the patterns are stable"
    const stable = label(root, rightX, verdictY, 'stable', { color: C.good, fontSize: '28px' });
    fadeIn(tl, stable, R2('stable') - 0.1, 0.5, 10);

    // ======================================= the output =======================================================
    // "Now delete the matches." Everything but the binders' places is struck, in the head and in both calls.
    const tD = R3('delete');
    grid.hide(tD - 0.2, 0.45); gridB.hide(tD - 0.2, 0.45); tl.to(chip, { o: 0, y: -14 }, tD - 0.2, 0.4, E.in);
    tl.to(stable, { o: 0 }, tD - 0.2, 0.3);
    stepShow('delete the match', tD - 0.05, 4);
    const range = (line, a, b) => { const ca = code.tokens.get(a).tok.col, cb = code.tokens.get(b).tok.col; return t => t.line === line && t.col >= ca && t.col <= cb; };
    const strikes = [range(1, 'pa', 'pqa'), range(1, 'pqc', 'pqz'), range(0, 'cu', 'cpa'), range(0, 'cc', 'cpz'), range(3, 'a2', 'pA'), range(3, 'cm5', 'pZ')];
    // a strike that ends at its tokens' edges, so that the kept binder between two strikes stays clear
    strikes.forEach((sel, k) => {
      const r = code.rect(sel), at = tD + 0.15 + k * 0.08;
      const u = box(root, r.x + 3, r.y + lh * 0.5 - 1, { width: (r.w - 6) + 'px', height: '3px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
      tl.set(u, { sx: 0, o: 0 }, 0); tl.to(u, { sx: 1, o: 1 }, at, 0.35, E.io); tl.to(u, { o: 0 }, R3('binders') - 0.4, 0.35);
      code.color(sel, C.faint, at, 0.35);
    });
    // "The loop's parameters are its two binders, and each call passes what matched them."
    code.hide(R3('binders') - 0.4, 0.35); stepHide(R3('binders') - 0.4);
    const OUT = 'main(?u, ?n) = loop({on|n}{ok|,} {o0|0})\n  where loop({oi|?i}, {os|?s}) =\n    if i == 0 then s + {ou1|u|o} else loop({oa|i} - 1, {ob|s} + {ou2|u|o})';
    const out = new Code(tl, root, x0, 300, 50);
    out.show(OUT, R3('binders') - 0.2, { stagger: 0.004, byLine: 0.06 });
    out.pulse(['oi', 'os'], D(3.85), { color: C.bind, dur: 0.7 });
    out.mark(['on', 'ok', 'o0'], C.dim, D(5.5), { fill: 0.08, out: D(7.5) });
    out.mark(t => t.line === 2 && t.col >= 35 && t.col <= 46, C.dim, D(5.85), { fill: 0.08, out: D(7.5) });
    // "and the loop reads U from main"
    out.mark(['ou1'], C.outer, D(16.0), { out: R3('cycle') - 0.4 });
    out.mark(['ou2'], C.outer, D(16.1), { out: R3('cycle') - 0.4 });
    out.hide(R3('cycle') - 0.3, 0.4);
    // "Four parameters have become two": the loop's old head, dim, above the output, its loop( over the new one's
    const oy = 300 - out.lh - 40, ox = x0 + 8 * out.cw;
    const was = new Code(tl, root, ox, oy, 50);
    was.show('loop({wi|?i}, {wa|?a}, {wx|?x}, {wq|?q})', R3('out') - 0.15, { stagger: 0.01 });
    tl.set(was.root, { o: 0.6 }, 0);
    const wasL = label(root, x0, oy + (out.lh - 30) / 2, 'was');
    fadeIn(tl, wasL, R3('out') - 0.1, 0.5, 10);
    was.pulse(['wi', 'wa', 'wx', 'wq'], D(7.9), { color: C.bind, dur: 0.7 });
    out.pulse(['oi', 'os'], D(9.5), { color: C.bind, dur: 0.7 });
    was.hide(R3('cycle') - 0.3, 0.4); fadeOut(tl, wasL, R3('cycle') - 0.3, 0.4);

    // ======================================= the cycle ========================================================
    const words = ['Assume', 'Simplify', 'Check', 'Keep the forced binders'];
    const WS = 54, wst = { fontFamily: 'var(--serif)', fontSize: WS + 'px', letterSpacing: '-0.005em' };
    const ww = words.map(t => measure(t, wst));
    const agap = 120, total = ww.reduce((a, b) => a + b, 0) + agap * (words.length - 1);
    const cy = 395, my = cy + WS * 0.68, csvg = svgLayer(root);
    let cx = (W - total) / 2;
    const xs = [];
    const tc = [R3('cycle') + 0.3, R3('c2'), R3('c3'), R3('c4')];
    words.forEach((t, k) => {
      xs.push(cx);
      const e = serif(root, cx, cy, t, WS);
      fadeIn(tl, e, tc[k] - 0.15, 0.6, 16);
      if (k > 0) { const a = arrow(tl, csvg, cx - agap + 26, my, cx - 26, my, { stroke: C.dim, width: 3, head: 12 }); drawArrow(tl, a, tc[k] - 0.22, 0.3); }
      cx += ww[k] + agap;
    });
    // "Repeat until a round refutes nothing."
    const lastC = xs[3] + ww[3] / 2, firstC = xs[0] + ww[0] / 2, ry = cy + WS * 1.22 + 14;
    const back = arrow(tl, csvg, lastC, ry, firstC, ry, { bend: -170, stroke: C.dim, width: 3, head: 13 });
    drawArrow(tl, back, R3('c5') - 0.2, 0.8);
    const rep = label(root, (lastC + firstC) / 2 - 100, ry + 85 + 14, 'repeat', { width: '200px', textAlign: 'center' });
    fadeIn(tl, rep, R3('c5') + 0.2, 0.5, 10);
    // "A pattern can be refuted only finitely many times"
    const term = label(root, 0, ry + 200, 'a pattern is refuted only finitely often', { width: W + 'px', textAlign: 'center' });
    fadeIn(tl, term, R3('term') - 0.1, 0.6, 10);
  });
})();

// ==== src/scenes/s06_over.js ====
// Why start over? Three blocks on which repairing a round in place keeps a stale value: f is assumed f(1), so g
// is assumed g(1); the call f(2) refutes f(1). Repairing in place weakens f to f(?x) but keeps g's 1, which came
// from f's refuted assumption, and ends with g(?b). Starting again from the skeleton f(?x) gives g(x).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const S = 50, X0 = 160, Y0 = 330, CX = 1340;
  const lineH = () => Math.round(S * 1.62);
  const L = k => Y0 + k * lineH();
  const LOOK = (code, sel, at, out) => code.mark(sel, C.dim, at, { fill: 0.08, out });

  // a small piece of code that travels from (fx, fy) to its own place, arriving at at + dur
  function fly(tl, root, x, y, src, fx, fy, at, { dur = 0.8 } = {}) {
    const c = new Code(tl, root, x, y, S);
    c.show(src, at, { dur: 0.3, rise: 0, stagger: 0 });
    tl.fromTo(c.root, { x: fx - x, y: fy - y }, { x: 0, y: 0 }, at, dur, E.io);
    return c;
  }
  // the three blocks, one Code per line, all at their places
  function program(tl, root, at) {
    const p0 = new Code(tl, root, X0, L(0), S), p1 = new Code(tl, root, X0, L(1), S), p2 = new Code(tl, root, X0, L(2), S);
    const src = [
      'main() = {c|f}{c1|(}{c2|1}{c3|)}',
      'f(?x) = {g|g}{g1|(}{gx|x}{g2|)}',
      'g(?b) = if {b1|b} == 1 then {fc|f}{f1|(}{f2|2}{f3|)} else {b2|b}',
    ];
    [p0, p1, p2].forEach((p, k) => p.show(src[k], at[k]));
    return [p0, p1, p2];
  }
  const G_SRC = 'g(?b) = if {b1|b} == 1 then {fc|f}{f1|(}{f2|2}{f3|)} else {b2|b}';

  // ---- over1 + over2: begin alike, refute, then repair in place ---------------------------------------------
  scene(['over1', 'over2'], ({ tl, root, cue, seg }) => {
    const svg = svgLayer(root), cw = charWidth(S), lh = lineH();

    // "Why discard the round?"
    const tWhy = cue('why'), tThree = cue('three');
    const kp = serif(root, X0, 430, 'Why not repair the round?', 60);
    fadeIn(tl, kp, tWhy - 0.2, 0.8, 22);
    fadeOut(tl, kp, tThree - 0.5, 0.4);
    // "The textbook way ... keeps what it has found, and repairs it." "For patterns, that gives a correct answer,
    // but not always the best one."
    const uw = label(root, X0, 540, 'the textbook way: keep what was found, and repair it');
    fadeIn(tl, uw, cue('usual') - 0.2, 0.6, 10);
    fadeOut(tl, uw, tThree - 0.55, 0.4);
    const ms = label(root, X0, 590, 'correct, but not always the best');
    fadeIn(tl, ms, cue('miss') - 0.2, 0.6, 10);
    fadeOut(tl, ms, tThree - 0.55, 0.4);

    // "Here are three blocks", and what each does, one per cue
    const [p0, p1, p2] = program(tl, root, [tThree - 0.25, tThree - 0.1, tThree + 0.05]);
    LOOK(p0, ['c', 'c1', 'c2', 'c3'], cue('m') - 0.2, cue('f') - 0.3);
    LOOK(p1, ['g', 'g1', 'gx', 'g2'], cue('f') - 0.2, cue('g') - 0.3);
    LOOK(p2, t => t.col >= 8 && t.col <= 26, cue('g') - 0.2, cue('begin') - 0.4);

    // "Both methods begin in the same way": the column of assumed patterns
    const tB = cue('begin');
    const asm = label(root, CX, L(0) + lh / 2 - 15, 'assumed');
    fadeIn(tl, asm, tB - 0.15, 0.5, 10);

    // "F is assumed to be F of one": main's call, copied into the column
    const tF1 = cue('f1');
    LOOK(p0, ['c', 'c1', 'c2', 'c3'], tF1 - 0.35, cue('g1') - 0.6);
    const colF = fly(tl, root, CX, L(1), 'f({f1|1|p})', X0 + 9 * cw, L(0), tF1 - 0.2);

    // "Its body calls G of one": f's x is its pattern's 1
    const tG1 = cue('g1');
    colF.mark(['f1'], C.pat, tG1 - 0.35, { out: tG1 + 1.2 });
    p1.swap('f(?x) = {g|g}{g1|(}{gx1|1|p}{g2|)}', tG1 - 0.15, { dur: 0.5 });
    // "so G is assumed to be G of one": that call, copied into the column
    const tGa = tG1 + 2.0;   // "so G is assumed" (build/audio/over1.json)
    LOOK(p1, ['g', 'g1', 'gx1', 'g2'], tGa - 0.3, tGa + 1.0);
    // (it appears in place: a flight would cross g's line)
    const colG = new Code(tl, root, CX, L(2), S).show('g({g1|1|p})', tGa);

    // "Under that, the test is true, and G calls F of two"
    const tT = cue('test'), tR = cue('refute');
    p2.swap('g(?b) = if {b1x|1|p} == 1 then {fc|f}{f1|(}{f2|2}{f3|)} else {b2x|1|p}', tT - 0.25, { dur: 0.5 });
    LOOK(p2, t => t.col >= 11 && t.col <= 16, tT + 0.4, tT + 1.9);
    LOOK(p2, ['fc', 'f1', 'f2', 'f3'], tT + 1.9, seg('over2') + 0.2);

    // "which does not match F of one": the call, beside the pattern it fails to match
    const callX = CX + 6 * cw;
    const call = fly(tl, root, callX, L(1), 'f({c2|2})', X0 + 21 * cw, L(2), tR - 0.6, { dur: 0.7 });
    const xm = CX + 5 * cw, ym = L(1) + lh / 2;
    const cr = cross(tl, svg, xm, ym, 22);
    cr.forEach(c => tl.to(c, { draw: 1 }, tR + 0.15, 0.3));
    colF.mark(['f1'], C.bad, tR + 0.1, { out: seg('over2') + 0.1 });
    call.mark(['c2'], C.bad, tR + 0.1, { out: seg('over2') + 0.1 });
    const ref = label(root, callX, L(1) + lh - 4, 'refuted', { color: C.bad });
    fadeIn(tl, ref, tR + 0.25, 0.4, 8);

    // ---- over2: "A repair in place now weakens F's pattern to a binder, and revisits F" -------------------
    const tRep = cue('repair');
    const rip = label(root, CX, L(0) - 90, 'repair in place', { color: C.ink });
    fadeIn(tl, rip, tRep - 0.3, 0.5, 10);
    for (const c of cr) tl.to(c, { o: 0 }, tRep - 0.3, 0.3);
    call.hide(tRep - 0.3, 0.3); fadeOut(tl, ref, tRep - 0.3, 0.3);
    colF.swap('f(?x)', tRep - 0.1, { dur: 0.5 });
    p1.swap('f(?x) = {g|g}{g1|(}{gx|x}{g2|)}', tRep + 1.4, { dur: 0.5 });

    // "F now calls G of X, while G's pattern is still G of one"
    const tGx = cue('gx'), tOld = cue('old'), tJ = cue('join');
    const mGx = LOOK(p1, ['g', 'g1', 'gx', 'g2'], tGx - 0.2, tJ + 0.4);
    LOOK(colG, /.*/, tOld - 0.2, tJ + 0.4);

    // "One and X have nothing in common, so their join is a new binder"
    const JX = CX + 20, JY = L(3) + 30;
    const jx = new Code(tl, root, JX, JY, S).show('x', tJ - 0.15);   // in place, while f's g(x) is lit
    const j1 = fly(tl, root, JX + 6 * cw, JY, '{v|1|p}', CX + 2 * cw, L(2), tJ - 0.1);
    const jb = new Code(tl, root, JX + 2.5 * cw, JY + 190, S).show('?b', tJ + 2.3);
    const a1 = arrow(tl, svg, JX + 0.5 * cw, JY + lh - 4, JX + 3.0 * cw, JY + 190 + 6, { stroke: C.dim, width: 3 });
    const a2 = arrow(tl, svg, JX + 6.5 * cw, JY + lh - 4, JX + 4.0 * cw, JY + 190 + 6, { stroke: C.dim, width: 3 });
    drawArrow(tl, a1, tJ + 1.5, 0.5); drawArrow(tl, a2, tJ + 1.6, 0.5);
    colG.swap('g(?b)', tJ + 3.0, { dur: 0.5 });
    p2.swap(G_SRC, tJ + 3.3, { dur: 0.5 });

    // "That is stable, but it is not the most specific"
    const tSb = cue('stablebut'), tSt = cue('stale');
    for (const c of [jx, j1, jb]) c.hide(tSb - 0.35, 0.35);
    hideArrow(tl, a1, tSb - 0.35); hideArrow(tl, a2, tSb - 0.35);
    const st = label(root, CX, L(3) + 24, 'stable', { color: C.good });
    const nm = label(root, CX, L(3) + 64, 'not the most specific');
    fadeIn(tl, st, tSb - 0.1, 0.5, 10); fadeIn(tl, nm, tSb + 0.6, 0.5, 10);

    // "The one in G's old pattern was never a fact about G": the old 1, struck, beside g(?b)
    fadeOut(tl, st, tSt - 0.4, 0.3); fadeOut(tl, nm, tSt - 0.4, 0.3);
    const ghost = new Code(tl, root, CX + 8 * cw, L(2), S).show('{v|1|p}', tSt - 0.2);
    tl.to(ghost.root, { o: 0.75 }, tSt - 0.2, 0.01);
    ghost.strike(['v'], tSt + 0.4, { fade: false });
    // "It was F's X, under an assumption that has since been refuted": f(1), refuted, above it
    const tFx = tSt + 3.8;   // "It was F's X" (build/audio/over2.json)
    const gf = new Code(tl, root, CX + 6 * cw, L(1), S).show('f({v|1|p})', tFx - 0.2);
    tl.to(gf.root, { o: 0.6 }, tFx - 0.2, 0.01);
    const ga = arrow(tl, svg, CX + 8.5 * cw, L(1) + lh - 12, CX + 8.5 * cw, L(2) + 14, { stroke: C.dim, width: 3, head: 10 });
    drawArrow(tl, ga, tFx + 0.4, 0.4);
    gf.color(['v'], C.bad, tFx + 1.4, 0.4);
    const fra = label(root, CX, L(3) + 24, 'from a refuted\nassumption', { lineHeight: 1.5 });
    fadeIn(tl, fra, tFx + 1.4, 0.5, 10);
  });

  // ---- over3: start again from the skeleton ----------------------------------------------------------------
  scene('over3', ({ tl, root, cue }) => {
    const svg = svgLayer(root), cw = charWidth(S), lh = lineH();
    const [p0, p1, p2] = program(tl, root, [0, 0.02, 0.04]);
    const asm = label(root, CX, L(0) + lh / 2 - 15, 'assumed');
    fadeIn(tl, asm, 0, 0.4, 0);

    // "Refutation keeps one thing from the first round: F's parameter must be a binder"
    const tO = cue('ours');
    const colF = new Code(tl, root, CX, L(1), S).show('f({x|?x})', tO - 0.2);
    colF.mark(['x'], C.bind, tO + 1.6, { out: cue('again') - 0.3 });

    // "Then it starts again"
    const tA = cue('again');
    const sa = label(root, CX, L(0) - 90, 'start again', { color: C.ink });
    fadeIn(tl, sa, tA - 0.2, 0.5, 10);

    // "F's body calls G of X. This is the first call to reach G"
    const tFx = cue('fx'), tG = cue('gname');
    LOOK(p1, ['g', 'g1', 'gx', 'g2'], tFx - 0.2, tG + 0.6);
    // "so G's pattern is the plain name X: G's argument is always F's X"
    const colG = new Code(tl, root, CX, L(2), S, {});
    colG.show('g{p|(}{x|x|o}{q|)}', tG - 0.3, { dur: 0.3, rise: 0, stagger: 0 });
    tl.fromTo(colG.root, { x: X0 + 8 * cw - CX, y: L(1) - L(2) }, { x: 0, y: 0 }, tG - 0.3, 0.8, E.io);
    const vl = path(tl, svg, `M ${CX + 2.5 * cw} ${L(2) + 14} L ${CX + 2.9 * cw} ${L(1) + lh - 12}`, { stroke: C.outer, width: 3 });
    tl.to(vl, { draw: 1 }, tG + 1.0, 0.5, E.io);
    colG.mark(['x'], C.outer, tG + 1.3, { fill: 0.1 });

    // "G is passed nothing, and is nested inside F"
    const tN = cue('nest');
    p2.swap('  g({x|x|o}) = if {x1|x|o} == 1 then f(2) else {x2|x|o}', tN - 0.25, { dur: 0.5 });
    const pn = label(root, X0 + 2 * cw, L(3) + 18, 'passed nothing');
    fadeIn(tl, pn, tN + 0.4, 0.5, 10);
  });

  // ---- best: why the restarts give the most specific result, on the program as over3 left it ------------------
  scene('best', ({ tl, root, cue }) => {
    const svg = svgLayer(root), cw = charWidth(S), lh = lineH();
    const tI = cue('inv');
    const Y = 300, LB = k => Y + k * lh;
    const src = [
      'main() = f(1)',
      'f(?x) = g(x)',
      '  g({x|x|o}) = if {x1|x|o} == 1 then {fc|f}{f1|(}{f2|2}{f3|)} else {x2|x|o}',
    ];
    const prog = src.map((t, k) => new Code(tl, root, X0, LB(k), S).show(t, tI - 0.25 + k * 0.08));
    const asm = label(root, CX, LB(0) + lh / 2 - 15, 'assumed');
    fadeIn(tl, asm, tI - 0.1, 0.5, 10);
    const colF = new Code(tl, root, CX, LB(1), S).show('f({x|?x})', tI);
    const colG = new Code(tl, root, CX, LB(2), S).show('g({x|x|o})', tI + 0.08);

    // the labels: a column under the program, each new one below the last, the earlier ones dimmed
    const LX = X0, LY = LB(3) + 40, LG = 52;
    const said = [];
    const say = (k, text, at, color = C.dim) => {
      const e = label(root, LX, LY + k * LG, text, { color });
      fadeIn(tl, e, at, 0.5, 10);
      for (const p of said) tl.to(p, { o: 0.6 }, at, 0.4);
      said.push(e);
      return e;
    };

    // "Look at the one binder that was forced: F's parameter"
    const tF = cue('forced'), tC = cue('call'), tS = cue('same'), tM = cue('must'), tN = cue('nochoice'), tR = cue('fresh'), tO = cue('order');
    colF.mark(['x'], C.bind, tF - 0.2, { out: tR - 0.3 });
    say(0, 'the one binder that was forced', tF + 0.3);

    // "It was forced by the call F of two"
    prog[2].mark(['fc', 'f1', 'f2', 'f3'], C.dim, tC - 0.2, { fill: 0.08, out: tR - 0.3 });
    const fx0 = X0 + 26 * cw, fy0 = LB(2) + 12;
    const a1 = arrow(tl, svg, fx0, fy0, CX + 3 * cw, LB(1) + lh - 12, { bend: -50, stroke: C.dim, width: 3 });
    drawArrow(tl, a1, tC + 0.2, 0.6);

    // "Under any stable patterns, that call is made too ... and there it must match": a second column, under
    // the first (the right of the stage is too narrow for it)
    const OY = LB(3) + 24;
    const oh = label(root, CX, OY, 'any other\nstable patterns', { lineHeight: 1.45 });
    fadeIn(tl, oh, tS - 0.2, 0.5, 10);
    const OL = OY + 86;
    const colO = new Code(tl, root, CX, OL, S).show('f(  )', tS - 0.1);
    const ph = box(root, CX + 2 * cw + 3, OL + lh * 0.18, { width: (2 * cw - 6) + 'px', height: (lh * 0.64) + 'px', borderRadius: '8px', boxShadow: `inset 0 0 0 2px ${C.dim}` });
    fadeIn(tl, ph, tS, 0.5, 0);
    const a2 = arrow(tl, svg, fx0, LB(3) - 8, CX - 16, OL + lh / 2, { bend: -40, stroke: C.dim, width: 3 });
    drawArrow(tl, a2, tS + 0.6, 0.7);

    // "So any stable patterns have a binder there too, or above it"
    fadeOut(tl, ph, tM - 0.25, 0.3, 0);
    const ob = new Code(tl, root, CX + 2 * cw, OL, S).show('{x|?x}', tM - 0.1);
    ob.mark(['x'], C.bind, tM + 0.2, { out: tR - 0.3 });
    const obl = label(root, CX + 6 * cw, OL + lh / 2 - 30, 'a binder there too,\nor above it', { lineHeight: 1.45 });
    fadeIn(tl, obl, tM + 0.3, 0.5, 10);

    // "The binder was never a choice"
    say(1, 'the binder was never a choice', tN - 0.15, C.ink);

    // "Everything else is assumed afresh in every round": the rest of the first column
    for (const a of [a1, a2]) { tl.to(a, { o: 0.6 }, tR - 0.3, 0.4); tl.to(a._head, { o: 0.6 }, tR - 0.3, 0.4); }
    for (const e of [oh, obl, colO.root, ob.root]) tl.to(e, { o: 0.6 }, tR - 0.3, 0.4);
    colG.mark(/.*/, C.outer, tR - 0.15, { fill: 0.1 });
    say(2, 'everything else: assumed afresh every round', tR + 0.2);

    // "And so the order in which the blocks are visited does not matter"
    say(3, 'so any order of visits gives the same result', tO - 0.1, C.ink);
  });
})();

// ==== src/scenes/s07_cps.js ====
// Functions and closures. Continuation-passing style makes a return a jump, so the one rule that covers loops
// covers calls and returns (contification); a closure is a constructor tagged by its block, so a pattern can name
// the function (a direct call); an escape counts as one more call with unknown arguments.
// The code is the paper's (sections/3_closures.tex, Figure 1), on the rail at x = 160, size 50.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160, S = 50, LEAD = 2.0;
  const Y_CPS = 380;   // the dup program, in cps+dup and nocont: three lines and a label, centred in the stage

  // an arrow that stays hidden until it is drawn
  function arrowAt(tl, svg, x1, y1, x2, y2, opts, at, dur = 0.5) {
    const a = arrow(tl, svg, x1, y1, x2, y2, opts);
    tl.set(a, { o: 0 }, 0); tl.set(a, { o: 1 }, at); drawArrow(tl, a, at, dur);
    return a;
  }
  // a small-caps label that rises in and (unless out is null) leaves
  function tag(tl, root, x, y, text, at, out, style = {}) {
    const l = label(root, x, y, text, Object.assign({ fontSize: '26px' }, style));
    fadeIn(tl, l, at, 0.5, 10);
    if (out !== null) fadeOut(tl, l, out, 0.35, -8);
    return l;
  }
  // an arrow from under some tokens on one line to the top of some tokens on a later line: a jump
  function jump(tl, svg, code, from, to, at, { bend = -10, dur = 0.5 } = {}) {
    const a = code.rect(from), b = code.rect(to), lh = code.lh;
    return arrowAt(tl, svg, a.cx, a.y + lh * 0.86, b.cx, b.y + lh * 0.16, { bend, stroke: C.dim, width: 3, head: 12 }, at, dur);
  }
  // the y of a label set level with line l of a code block
  const level = (code, l, h = 30) => code.y + l * code.lh + (code.lh - h) / 2;

  // ---- cps + dup: returns are jumps; contification --------------------------------------------------------
  scene(['cps', 'dup'], ({ tl, root, cue, seg }) => {
    const svg = svgLayer(root);
    const y0 = Y_CPS;
    const code = new Code(tl, root, RAIL, y0, S, { leading: LEAD });
    const cw = code.cw;

    // "Nothing so far was special to loops": the direct-style program
    const M0 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {let|let} {pv|p} {peq|=} {dc|dup|f}{dco|(}{dy|y}{dcc|)} {in|in} {p0|p.0} {mi|-} {p1|p.1}';
    const D0 = '{dn|dup|f}{dno|(}{ds|?s}{dnc|)} {de|=} {b0|(}{s1|s}{bc|,} {s2|s}{b1|)}';
    code.show(M0 + '\n' + D0, cue('nothing') - 0.3, { stagger: 0.01 });

    // "A function takes one more parameter, written after a semicolon: its continuation"
    const D1 = '{dn|dup|f}{dno|(}{ds|?s}{dsc|;} {dr|?r}{dnc|)} {de|=} {b0|(}{s1|s}{bc|,} {s2|s}{b1|)}';
    const tE = cue('extra') + 0.7;
    code.morph(M0 + '\n' + D1, tE, { dur: 0.55 });
    code.mark(['dsc', 'dr'], C.bind, tE + 0.5, { out: cue('rest') - 0.3, fill: 0.12, pad: 6 });
    tag(tl, root, RAIL + 27 * cw, level(code, 1), 'continuation', cue('cps.extra') + 4.6, cue('rest') - 0.3);

    // "Returning is a jump to it"
    const D2 = '{dn|dup|f}{dno|(}{ds|?s}{dsc|;} {dr|?r}{dnc|)} {de|=} {rr|r|f}{ro|(}{b0|(}{s1|s}{bc|,} {s2|s}{b1|)}{rc|)}';
    const tR = cue('ret') - 0.25;
    code.morph(M0 + '\n' + D2, tR, { dur: 0.55 });

    // "What the caller does after the call becomes a separate block, K, which the caller passes"
    const tC = cue('rest') + 0.5;
    code.mark(['p0', 'mi', 'p1'], C.dim, tC, { out: tC + 1.5, fill: 0.08 });
    // the rest of main drops straight down (nothing is under it), then slides into k's line
    const M1 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {dc|dup|f}{dco|(}{dy|y}{dcc|)}';
    const K0 = ' '.repeat(29) + '{p0|p.0} {mi|-} {p1|p.1}';
    const tB = cue('rest') + 2.0;
    code.morph(M1 + '\n' + D2 + '\n' + K0, tB, { dur: 0.55 });
    const K1 = '{kn|k|f}{ko|(}{kp|?p}{kc|)} {ke|=} {p0|p.0} {mi|-} {p1|p.1}';
    code.morph(M1 + '\n' + D2 + '\n' + K1, tB + 0.6, { dur: 0.55 });
    // "which the caller passes"
    const M2 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {dc|dup|f}{dco|(}{dy|y}{dsc0|;} {kk|k}{dcc|)}';
    code.morph(M2 + '\n' + D2 + '\n' + K1, cue('rest') + 4.1, { dur: 0.5 });

    // "a call, a return, ... are all jumps": main jumps to dup, dup jumps to k through r
    const call = ['dc', 'dco', 'dy', 'dsc0', 'kk', 'dcc'];
    const a1 = jump(tl, svg, code, ['dc'], ['dn'], cue('jumps') + 0.6);
    const a2 = jump(tl, svg, code, ['rr'], ['kn'], cue('jumps') + 1.4);
    const rule = tag(tl, root, RAIL, y0 + 3 * code.lh + 30, 'everything is a jump', cue('jumps') + 3.7, cue('once') - 0.3);
    hideArrow(tl, a1, cue('once') - 0.3); hideArrow(tl, a2, cue('once') - 0.3);

    // "This function is called from one place, so its pattern is that call, and its continuation is always K"
    const tO = cue('once');
    code.mark(call, C.dim, tO - 0.1, { out: tO + 3.0, fill: 0.08 });
    // the head becomes the pattern and the body is substituted in the same step, so that no frame holds a
    // pattern over a body with unbound s and r
    const D4 = '{dn|dup|f}{dno|(}{hy|y|o}{dsc|;} {hk|k|p}{dnc|)} {de|=} {bk|k|p}{ro|(}{b0|(}{y1|y|o}{bc|,} {y2|y|o}{b1|)}{rc|)}';
    code.swap(M2 + '\n' + D4 + '\n' + K1, tO + 2.8, { dur: 0.5 });
    code.mark(['hk'], C.pat, cue('cont') + 0.2, { out: cue('direct') - 0.2, pad: 8 });

    // "Its return is then a direct jump to K. This is contification."
    const kcall = ['bk', 'ro', 'b0', 'y1', 'bc', 'y2', 'b1', 'rc'];
    code.mark(kcall, C.dim, cue('direct') + 0.9, { out: cue('direct') + 3.4, fill: 0.08 });
    const jk = jump(tl, svg, code, ['bk'], ['kn'], cue('direct') + 1.2);
    hideArrow(tl, jk, cue('pair') - 0.3);
    const name = serif(root, RAIL, y0 + 3 * code.lh + 30, 'Contification', 60);
    fadeIn(tl, name, cue('direct') + 3.7, 0.7, 20);
    fadeOut(tl, name, cue('pair') - 0.3, 0.35);

    // "That jump passes the pair Y, Y, so the pair is in K's pattern"
    const pairC = ['b0', 'y1', 'bc', 'y2', 'b1'];
    code.mark(pairC, C.dim, cue('pair') + 1.2, { out: cue('pair') + 4.4, fill: 0.08 });
    const K2 = '{kn|k|f}{ko|(}{kq0|(|p}{ky1|y|o}{kqc|,|p} {ky2|y|o}{kq1|)|p}{kc|)} {ke|=} {p0|p.0} {mi|-} {p1|p.1}';
    code.swap(M2 + '\n' + D4 + '\n' + K2, cue('pair') + 3.6, { dur: 0.5 });

    // "and the difference of its two fields folds to zero"
    const K3 = '{kn|k|f}{ko|(}{kq0|(|p}{ky1|y|o}{kqc|,|p} {ky2|y|o}{kq1|)|p}{kc|)} {ke|=} {g0|y|o} {mi|-} {g1|y|o}';
    code.swap(M2 + '\n' + D4 + '\n' + K3, cue('fold') - 0.1, { dur: 0.5 });
    const K4 = '{kn|k|f}{ko|(}{kq0|(|p}{ky1|y|o}{kqc|,|p} {ky2|y|o}{kq1|)|p}{kc|)} {ke|=} {z|0}';
    code.swap(M2 + '\n' + D4 + '\n' + K4, cue('fold') + 1.8, { dur: 0.5 });

    // "So this pair is never built": the pattern's pair, then the pair the jump would build
    const tN = cue('never');
    code.mark(['kq0', 'ky1', 'kqc', 'ky2', 'kq1'], C.pat, tN - 0.1, { out: cue('out') - 0.3 });
    code.strike(pairC, tN + 0.9, { out: cue('out') - 0.15 });

    // "The whole program returns zero"
    code.swap('{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {z0|0}', cue('out') - 0.1, { dur: 0.5 });
  });

  // ---- clo: a closure is data; a known closure is called directly ----------------------------------------
  // ---- nocont: from here on, the examples are written without their continuations ---------------------------
  scene('nocont', ({ tl, root, cue }) => {
    const code = new Code(tl, root, RAIL, Y_CPS, S, { leading: LEAD });
    const M = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {dc|dup|f}{dco|(}{dy|y}{dsc0|;} {kk|k}{dcc|)}';
    const D = '{dn|dup|f}{dno|(}{ds|?s}{dsc|;} {dr|?r}{dnc|)} {de|=} {rr|r|f}{ro|(}{b0|(}{s1|s}{bc|,} {s2|s}{b1|)}{rc|)}';
    const K = '{kn|k|f}{ko|(}{kp|?p}{kc|)} {ke|=} {p0|p.0} {mi|-} {p1|p.1}';
    code.show(M + '\n' + D + '\n' + K, cue('from') - 0.35, { stagger: 0.006, byLine: 0.06 });
    // "written without their continuations": the continuation parts are struck
    const tS = cue('from') + 1.9, tW = cue('from') + 3.0;
    const runs = [['dsc0', 'kk'], ['dsc', 'dr'], ['rr', 'ro'], ['rc'], t => t.line === 2];
    runs.forEach((r, i) => code.strike(r, tS + i * 0.1, { out: tW }));
    // the direct-style program shows through
    const M0 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {let|let} {pv|p} {peq|=} {dc|dup|f}{dco|(}{dy|y}{dcc|)} {in|in} {p0b|p.0} {mib|-} {p1b|p.1}';
    const D0 = '{dn|dup|f}{dno|(}{ds|?s}{dnc|)} {de|=} {b0|(}{s1|s}{bc|,} {s2|s}{b1|)}';
    code.swap(M0 + '\n' + D0, tW, { dur: 0.6 });
    tag(tl, root, RAIL, Y_CPS + 2 * code.lh + 30, 'from here on: written without continuations', tW + 0.4, null);
  });

  scene('clo', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const y0 = 320;
    const code = new Code(tl, root, RAIL, y0, S, { leading: LEAD });
    const cw = code.cw;

    // "A lambda is treated in the same way"
    const M0 = '{mn|main|f}{mo|(}{mu|?u}{mc|)} {me|=} {an|app|f}{ao|(}{lam|λ|v}{lx|?x}{dot|.} {bx|x} {pl|+} {bu|u}{ac|)}';
    const A0 = '{fn|app|f}{fo|(}{ff|?f}{fc|)} {fe|=} {cf|f|f}{c1o|(}{one|1}{c1c|)}';
    code.show(M0 + '\n' + A0, cue('lambda') - 0.3, { stagger: 0.01 });

    // "This one becomes a block, inc, with its free variable U in angle brackets": the λ's body drops straight
    // down (nothing is under it) and becomes inc's line; main passes inc⟨u⟩
    const M1 = '{mn|main|f}{mo|(}{mu|?u}{mc|)} {me|=} {an|app|f}{ao|(}{ci|inc|f}{cl|⟨}{cu|u}{cr|⟩}{ac2|)}';
    const I0 = ' '.repeat(16) + '{lx|?x}  {bx|x} {pl|+} {bu|u}';
    const tI = cue('inc') + 0.3;
    code.morph(M1 + '\n' + A0 + '\n' + I0, tI, { dur: 0.55 });
    const I1 = '{ii|inc|f}{il|⟨}{iu|?u}{ir|⟩}{io|(}{lx|?x}{icp|)} {ie|=} {bx|x} {pl|+} {bu|u}';
    code.morph(M1 + '\n' + A0 + '\n' + I1, tI + 0.65, { dur: 0.55 });
    const tA = cue('inc') + 3.6;
    code.mark(['il', 'iu', 'ir'], C.dim, tA, { out: tA + 1.5, fill: 0.08, pad: 6 });
    code.mark(['cl', 'cu', 'cr'], C.dim, tA + 0.1, { out: tA + 1.5, fill: 0.08, pad: 6 });

    // "A block with those parameters supplied is a closure, and they are its captures"
    const clo = ['ci', 'cl', 'cu', 'cr'];
    const tK = cue('closure');
    code.mark(clo, C.dim, tK + 0.3, { out: tK + 4.3, fill: 0.08, pad: 8 });
    const rc = code.rect(clo), ru = code.rect(['cu']);
    tag(tl, root, rc.x, y0 - 66, 'closure', tK + 2.6, tK + 4.3);
    code.mark(['cu'], C.dim, tK + 4.4, { out: cue('data') - 0.2, fill: 0.1, pad: 6 });
    tag(tl, root, ru.x - 6, y0 - 66, 'capture', tK + 4.4, cue('data') - 0.2);

    // "A closure is data, so a pattern can match on it as on a pair: the block is the constructor, and the
    // captures are its fields"
    const yA = 750, dimPal = { palette: { v: C.code, n: C.code, f: C.code } };
    const head = tag(tl, root, RAIL, yA - 70, 'a constructor and its fields', cue('data') + 1.0, cue('app') - 0.4);
    const pc = new Code(tl, root, RAIL, yA, 44, dimPal);
    pc.show('{q0|(}{qz|0}{qc|,} {qu|u}{q1|)}', cue('data') + 3.5);
    const cc = new Code(tl, root, RAIL + 400, yA, 44, dimPal);
    cc.show('{i|inc}{l|⟨}{u|u}{r|⟩}', cue('data') + 4.3);
    tag(tl, root, RAIL, yA + pc.lh + 4, 'pair', cue('data') + 3.6, cue('app') - 0.4);
    tag(tl, root, RAIL + 400, yA + cc.lh + 4, 'closure', cue('data') + 4.4, cue('app') - 0.4);
    const tCon = cue('data') + 5.0, tFld = cue('data') + 6.3;
    pc.mark(['q0'], C.dim, tCon, { out: tFld, fill: 0.1, pad: 4 }); pc.mark(['q1'], C.dim, tCon, { out: tFld, fill: 0.1, pad: 4 });
    cc.mark(['i'], C.dim, tCon, { out: tFld, fill: 0.1, pad: 6 });
    pc.mark(['qz', 'qc', 'qu'], C.dim, tFld, { out: cue('app') - 0.4, fill: 0.1, pad: 4 });
    cc.mark(['u'], C.dim, tFld, { out: cue('app') - 0.4, fill: 0.1, pad: 6 });
    pc.hide(cue('app') - 0.4, 0.35); cc.hide(cue('app') - 0.4, 0.35);

    // "Here, app is always passed inc with main's U"
    const tP = cue('app') + 0.3;
    const a1 = jump(tl, svg, code, clo, ['ff'], tP, { bend: -14 });
    const A1 = '{fn|app|f}{fo|(}{pi|inc|p}{pl2|⟨|p}{pu|u|o}{pr|⟩|p}{fc2|)} {fe2|=} {cf|f|f}{c1o|(}{one|1}{c1c|)}';
    code.swap(M1 + '\n' + A1 + '\n' + I1, tP + 0.6, { dur: 0.5 });
    hideArrow(tl, a1, tP + 0.7);

    // "Substitute that for F"
    const A2 = '{fn|app|f}{fo|(}{pi|inc|p}{pl2|⟨|p}{pu|u|o}{pr|⟩|p}{fc2|)} {fe2|=} {qi|inc|p}{ql|⟨|p}{qu|u|o}{qr|⟩|p}{c2o|(}{one2|1}{c2c|)}';
    code.swap(M1 + '\n' + A2 + '\n' + I1, cue('subst') - 0.2, { dur: 0.5 });

    // "and the call through F is a direct call of inc"
    const tD = cue('direct');
    const callI = ['qi', 'ql', 'qu', 'qr', 'c2o', 'one2', 'c2c'];
    const a2 = jump(tl, svg, code, callI, ['ii'], tD + 0.2, { bend: -14 });
    const I2 = '{ii|inc|f}{il|⟨}{ju|u|o}{ir|⟩}{io|(}{j1|1|p}{icp2|)} {ie2|=} {j2|1|p} {pl2b|+} {ju2|u|o}';
    code.swap(M1 + '\n' + A2 + '\n' + I2, tD + 1.6, { dur: 0.5 });
    tag(tl, root, RAIL + 27 * cw, level(code, 1), 'a direct call', tD + 1.8, cue('out') - 0.3);
    hideArrow(tl, a2, cue('out') - 0.3);

    // "The output is one plus U"
    code.swap('{mn|main|f}{mo|(}{mu|?u}{mc|)} {me|=} {o1|1} {op|+} {ou|u}', cue('out') - 0.2, { dur: 0.5 });
  });

  // ---- escape: a closure we lose track of is called with unknown arguments; its captures stay known ------------------------------
  scene('escape', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const yC = 340;
    // the region of code we do not analyze, made first so that the closure is drawn over it
    const bx = 1100, by = 250, bw = W - 110 - bx, bh = 290;
    const region = box(root, bx, by, { width: bw + 'px', height: bh + 'px', borderRadius: '22px', boxSizing: 'border-box', border: `2px dashed ${alpha(C.dim, 0.55)}`, background: alpha(C.faint, 0.35) });
    const regionL = label(root, bx + 30, by + 26, 'code we do not analyze', { fontSize: '26px' });
    const tR = cue('esc') + 2.3;
    tl.set(region, { o: 0 }, 0); tl.to(region, { o: 1 }, tR, 0.6, E.out5); fadeIn(tl, regionL, tR + 0.2, 0.5, 10);

    // "A closure escapes when we lose track of it"
    const clo = new Code(tl, root, RAIL, yC, S, { leading: LEAD });
    clo.show('{ci|inc|f}{cl|⟨}{cu|u}{cr|⟩}', cue('esc') - 0.2);
    const cw = clo.cw, lh = clo.lh;

    // "the program returns it, passes it to code that we do not analyze, or passes it where a pattern has only
    // a binder"
    const ys = [470, 530, 590];
    const w1 = tag(tl, root, RAIL, ys[0], 'returned', cue('w1') - 0.15, null);
    const w2 = tag(tl, root, RAIL, ys[1], 'passed to unknown code', cue('w2') - 0.15, null);
    const w3 = tag(tl, root, RAIL, ys[2], 'passed where a pattern has a binder', cue('w3') - 0.15, null);
    const ay = yC + lh / 2, cx = bx + 70;
    const carry = arrowAt(tl, svg, RAIL + 6 * cw + 30, ay, bx - 20, ay, { stroke: C.dim, width: 3, head: 12 }, cue('w2') + 0.1, 0.6);
    clo.move(cx - RAIL, 0, cue('w2') + 0.8, 0.9, E.io);
    hideArrow(tl, carry, cue('w2') + 1.4);
    // the third case, drawn: the closure flows into a block whose pattern has only a binder there
    const yU = 660, tU = cue('w3') + 0.4;
    const mc = new Code(tl, root, RAIL, yU, 44);
    mc.show('{ci|inc|f}{cl|⟨}{cu|u}{cr|⟩}', tU);
    const mu = new Code(tl, root, RAIL + 12 * mc.cw, yU, 44);
    mu.show('{un|use|f}{uo|(}{uf|?f}{uc|)}', tU + 0.2);
    mu.mark(['uf'], C.bind, tU + 1.2, { fill: 0.14, pad: 6 });
    const uy = yU + mc.lh / 2;
    const ua = arrowAt(tl, svg, RAIL + 6 * mc.cw + 22, uy, RAIL + 12 * mc.cw - 22, uy, { stroke: C.dim, width: 3, head: 12 }, tU + 0.7, 0.5);
    for (const w of [w1, w2, w3]) fadeOut(tl, w, cue('any') - 0.3, 0.35);
    mc.hide(cue('any') - 0.3, 0.35); mu.hide(cue('any') - 0.3, 0.35); hideArrow(tl, ua, cue('any') - 0.3, 0.35);

    // "Whoever holds it may call it with any arguments": the call comes back out, to the block inc
    const yB = 780;
    const blk = new Code(tl, root, RAIL, yB, S, { leading: LEAD });
    blk.show('{bn|inc|f}{bl|⟨}{bu|?u}{br|⟩}{bo|(}{bx|?x}{bc|)} {be|=} {x|x} {p|+} {u|u}', cue('any') - 0.1);
    const back = arrowAt(tl, svg, cx + 3 * cw, yC + lh * 0.8, RAIL + 1.5 * cw, yB + lh * 0.18, { bend: -120, stroke: C.dim, width: 3, head: 12 }, cue('any') + 0.6, 0.8);

    // "We count that as one more call of its block, with unknown arguments": the capture stays what it is; only
    // the argument is unknown
    const fx = 900, fy = 670;
    const fc = new Code(tl, root, fx, fy, 44, { palette: { d: C.dim } });
    fc.show('{i|inc|f}{l|⟨}{fu|u|o}{r|⟩}{o|(}{un|unknown|d}{c|)}', cue('fict') + 0.1, { rise: 10 });
    blk.mark(['bo', 'bx', 'bc'], C.bind, cue('fict') + 2.6, { out: cue('caps') + 3.0, fill: 0.12, pad: 6 });

    // "But only the arguments are unknown"
    const lY = fy + fc.lh + 14;
    tag(tl, root, fx, lY, 'only the arguments are unknown', cue('but') - 0.1, cue('caps') - 0.2, { color: C.ink });
    fc.mark(['un'], C.dim, cue('but') + 0.6, { out: cue('caps') - 0.2, fill: 0.08, pad: 6 });
    // "What the closure captured was fixed where it was built, and the pattern keeps it"
    fc.mark(['fu'], C.outer, cue('caps') + 0.8, { out: cue('ex') - 0.3, pad: 6 });
    tag(tl, root, fx, lY, 'fixed where the closure was built', cue('caps') + 1.6, cue('ex') - 0.3);
    blk.swap('{bn|inc|f}{bl|⟨}{bu2|u|o}{br2|⟩}{bo2|(}{bx2|?x}{bc2|)} {be2|=} {x2|x} {p2|+} {u2|u|o}', cue('caps') + 3.3, { dur: 0.5 });

    // "Here, the closure that is returned has captured another closure": the picture leaves, the example arrives
    const tX = cue('ex') - 0.3;
    for (const c of [clo, blk, fc]) c.hide(tX, 0.4);
    hideArrow(tl, back, tX, 0.4);
    tl.to(region, { o: 0 }, tX, 0.4, E.in); fadeOut(tl, regionL, tX, 0.4);
    const y0 = 300;
    const code = new Code(tl, root, RAIL, y0, S, { leading: LEAD });
    const L0 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {kn|mk|f}{ko|(}{in0|inner|f}{il0|⟨}{iy0|y}{ir0|⟩}{kc|)}';
    const L1 = '{inn|inner|f}{il1|⟨}{iy1|?y}{ir1|⟩}{io1|(}{iv|?v}{ic1|)} {ie|=} {v1|v} {ip|+} {y1|y}';
    const L2 = '{mkn|mk|f}{mko|(}{mkf|?f}{mkc|)} {mke|=} {on|outer|f}{ol|⟨}{of|f}{or|⟩}';
    const L3 = '{oun|outer|f}{oul|⟨}{ouf|?f}{our|⟩}{ouo|(}{ouz|?z}{ouc|)} {oue|=} {ff|f|f}{fo|(}{fz|z}{fc|)}';
    code.show([L0, L1, L2, L3].join('\n'), cue('ex') - 0.1, { stagger: 0.006, byLine: 0.08 });
    const tRet = cue('ex') + 1.2, tCap = cue('ex') + 2.1;
    code.mark(['on', 'ol', 'of', 'or'], C.dim, tRet, { out: tCap, fill: 0.08, pad: 8 });
    tag(tl, root, RAIL + 20 * code.cw, level(code, 2), 'returned: it escapes', tRet + 0.1, cue('direct') - 0.3);
    code.mark(['of'], C.dim, tCap, { out: cue('direct') - 0.3, fill: 0.1, pad: 6 });

    // "Inside it, the call through F is still a direct call, and the inner closure is never built"
    const L3a = '{oun|outer|f}{oul|⟨}{pi|inner|p}{pl|⟨|p}{py|?y}{pr|⟩|p}{our2|⟩}{ouo2|(}{ouz2|?z}{ouc2|)} {oue2|=} {bi|inner|p}{bl|⟨|p}{by|y}{br|⟩|p}{bo|(}{bz|z}{bc|)}';
    code.swap([L0, L1, L2, L3a].join('\n'), cue('direct') - 0.2, { dur: 0.5 });
    const L3b = '{oun|outer|f}{oul|⟨}{pi|inner|p}{pl|⟨|p}{py|?y}{pr|⟩|p}{our2|⟩}{ouo2|(}{ouz2|?z}{ouc2|)} {oue2|=} {z1|z} {pp|+} {yy|y}';
    code.swap([L0, L1, L2, L3b].join('\n'), cue('direct') + 2.3, { dur: 0.5 });
    const O0 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {on2|outer|f}{ol2|⟨}{oy|y}{or2|⟩}';
    const O1 = '{oun|outer|f}{oul|⟨}{oy1|?y}{our3|⟩}{ouo3|(}{ouz3|?z}{ouc3|)} {oue3|=} {z1b|z} {ppb|+} {yyb|y}';
    code.swap(O0 + '\n' + O1, cue('direct') + 4.9, { dur: 0.6 });
    tag(tl, root, RAIL, y0 + 2 * code.lh + 20, 'the inner closure is never built', cue('direct') + 5.3, cue('ho') + 2.6);

    // "knowledge enters a function's body through what it captured"
    const key = serif(root, RAIL, y0 + 2 * code.lh + 50, 'Knowledge enters a function through what it captured.', 52);
    fadeIn(tl, key, cue('ho') + 2.9, 0.8, 20);
    code.mark(['oul', 'oy1', 'our3'], C.dim, cue('ho') + 5.5, { fill: 0.08, pad: 6 });
  });
})();

// ==== src/scenes/s08_ho.js ====
// Higher-order: a closure in a pattern. The fold that every call passes the same closure (one round), and the
// stream whose closure changes on every iteration (two rounds: refuted, then stable).
// Code is the paper's (sections/3_closures.tex), on the rail at x = 160, size 44.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160, S = 44;

  // a closure's tokens with ids: name⟨capture⟩. pat: the closure is asserted by a pattern (amber), cap: the
  // capture's text and class
  const clo = (id, name, cap, { pat = false, capCls = '' } = {}) => {
    const p = pat ? '|p' : '';
    return `{${id}|${name}${p}}{${id}l|⟨${p}}{${id}c|${cap}${capCls ? '|' + capCls : ''}}{${id}r|⟩${p}}`;
  };
  const ids = (id, extra = []) => [id, id + 'l', id + 'c', id + 'r', ...extra];
  // a row of small-caps labels laid out by the browser, each piece animated on its own
  function labelRow(root, x, y, texts, { gap = 48, size = 26 } = {}) {
    const r = box(root, x, y, { display: 'flex', alignItems: 'baseline', gap: gap + 'px', whiteSpace: 'pre' });
    return texts.map(t => {
      const s = document.createElement('span');
      Object.assign(s.style, { position: 'relative', display: 'inline-block', fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim, whiteSpace: 'pre' });
      s.textContent = t; s._text0 = t; s._shown = t; r.appendChild(s);
      return s;
    });
  }
  // a disc with a tick (a match) or a cross (a refutation), centred at (cx, cy)
  function disc(tl, root, svg, cx, cy, ok, at, out) {
    const d = box(root, cx - 17, cy - 17, { width: '34px', height: '34px', borderRadius: '50%', background: ok ? C.good : C.bad });
    tl.set(d, { o: 0, s: 0.3 }, 0); tl.to(d, { o: 1, s: 1 }, at, 0.3, E.back);
    const marks = ok ? [tick(tl, svg, cx, cy, 11, C.bg, 3.5)] : cross(tl, svg, cx, cy, 11, C.bg, 3.5);
    svg.parentNode.appendChild(svg);   // the tick or cross is drawn over the disc
    marks.forEach(m => tl.to(m, { draw: 1 }, at + 0.15, 0.3, E.out));
    if (out != null) { tl.to(d, { o: 0 }, out, 0.3); marks.forEach(m => tl.to(m, { o: 0 }, out, 0.3)); }
    return d;
  }

  // ---- fold: every call passes the same closure ---------------------------------------------------------------
  scene('fold', ({ tl, root, cue }) => {
    const Y = 380;
    const code = new Code(tl, root, RAIL, Y, S);
    const lh = code.lh;

    const L0 = `sum(?c, ?n) = fold(${clo('k0', 'scale', 'c')}, 0, 1, n)`;
    const L1 = '{sd|scale|f}⟨?c⟩(?s, ?i) = s + c * i';
    const H0 = 'fold({hf|?f}, {hs|?s}, {hi|?i}, {hn|?n}) =';
    const B0 = '  if i > {bn|n} then s else fold({rf|f}, {cf|f}{cp|(}{cs|s}{cc|,} {ci|i}{cq|)}, i + 1, {rn|n})';
    // the pattern: the closure is asserted, n is sum's n
    const H1 = `fold(${clo('hk', 'scale', 'c', { pat: true, capCls: 'o' })}, {hs|?s}, {hi|?i}, {hn|n|o}) =`;
    // the body under it: f is the closure, so the call through f is a call of scale (the line wraps)
    const B1 = '  if i > {bn|n|o} then s\n' +
      `  else fold(${clo('rk', 'scale', 'c', { pat: true, capCls: 'o' })}, ${clo('ck', 'scale', 'c', { pat: true, capCls: 'o' })}{cp|(}{cs|s}{cc|,} {ci|i}{cq|)}, i + 1, {rn|n|o})`;
    const B3 = '  if i > {bn|n|o} then s\n' +
      `  else fold(${clo('rk', 'scale', 'c', { pat: true, capCls: 'o' })}, {e1|s} {e2|+} {e3|c|o} {e4|*} {e5|i}, i + 1, {rn|n|o})`;
    const OUT = 'sum(?c, ?n) = fold(0, 1)\n' +
      '  {wh|where} fold(?s, ?i) =\n' +
      '    if i > {on|n|o} then s else fold(s + {oc|c|o} * i, i + 1)';

    // "Here is a fold over a range of integers."
    code.show([L0, L1, H0, B0].join('\n'), cue('fold') - 0.3, { stagger: 0.008, byLine: 0.1 });
    // "Sum passes it a closure that has captured C."
    const tSum = cue('sum'), tEvery = cue('every'), tPat = cue('pat');
    code.mark(ids('k0'), C.dim, tSum - 0.15, { fill: 0.08, out: tPat - 0.35 });
    code.pulse(['k0c'], tSum + 1.9, { color: C.ink, dur: 0.7 });
    // "Every call of fold passes that same closure, the recursive call included"
    code.pulse(ids('k0'), tEvery - 0.1, { color: C.ink, dur: 0.8 });
    code.mark(['rf'], C.dim, tEvery + 3.3, { fill: 0.08, out: tPat - 0.35, pad: 8 });

    // "so fold's pattern contains the closure, with binders only for S and I"
    code.swap([L0, L1, H1, B1].join('\n'), tPat - 0.25);
    code.mark(ids('hk'), C.pat, tPat + 1.2, { fill: 0.12, out: tPat + 2.6 });
    code.mark(['hs'], C.bind, tPat + 3.9, { fill: 0.12, out: cue('direct') - 0.4, pad: 6 });
    code.mark(['hi'], C.bind, tPat + 4.4, { fill: 0.12, out: cue('direct') - 0.4, pad: 6 });

    // "The call through F is a direct call of scale": scale's body takes the call's place
    const tD = cue('direct');
    code.mark([...ids('ck'), 'cp', 'cs', 'cc', 'ci', 'cq'], C.dim, tD + 0.25, { fill: 0.08, out: tD + 1.9 });
    code.mark(t => t.line === 1, C.dim, tD + 1.9, { fill: 0.08, out: tD + 3.1 });
    code.swap([L0, L1, H1, B3].join('\n'), tD + 2.3);

    // "The output is a loop over numbers that uses sum's C."
    const tO = cue('out');
    code.swap(OUT, tO - 0.25);
    code.mark(['oc'], C.outer, tO + 2.5, { fill: 0.14, out: cue('none') - 0.2, pad: 6 });
    code.pulse(['?c@0.1'], tO + 2.6, { color: C.bind, dur: 0.8 });

    // "No closure is built, and no code was copied."
    const [noClo, noCopy] = labelRow(root, RAIL, Y + 3 * lh + 34, ['no closure', 'no copy'], { gap: 64 });
    const tN = cue('none');
    fadeIn(tl, noClo, tN - 0.15, 0.5, 10);
    fadeIn(tl, noCopy, tN + 1.4, 0.5, 10);
  });

  // ---- stream: the closure changes on every iteration ---------------------------------------------------------
  scene('stream', ({ tl, root, cue }) => {
    const Y = 310;
    const svg = svgLayer(root);
    const code = new Code(tl, root, RAIL, Y, S);
    const cw = code.cw, lh = code.lh;

    const L0 = `main(?n) = sum(${clo('m', 'from', '1')}{mc1|,} {mn|n}{mc2|,} {m0|0})`;
    const L1 = `{dn|from|f}{dl|⟨}{da|?a}{dr|⟩}{dp|(}{dq|)} {de|=} {d0|(}{d1|a}{d2|,} ${clo('dk', 'from', 'a + 1')}{d3|)}`;
    const H0 = 'sum(?g, ?i, ?acc) =';
    const B0 = '  if i == 0 then acc\n  else let p = g() in sum(p.1, i - 1, acc + p.0)';
    // round 1: the pattern is main's call
    const H1 = `sum(${clo('h', 'from', '1', { pat: true, capCls: 'p' })}, {hn|n|o}, {h0|0|p}) =`;
    const B1 = '  if {bn|n|o} == 0 then {b0|0|p}\n' +
      `  else let p = ${clo('g', 'from', '1', { pat: true, capCls: 'p' })}{gp|(}{gq|)} in sum(p.1, {rn|n|o} - 1, {r0|0|p} + p.0)`;
    // p is known: the let goes, and the recursive call is what is left
    const B1b = '  if {bn|n|o} == 0 then {b0|0|p}\n' +
      `  else sum(${clo('c', 'from', '2')}, {cn|n|o} {cm|-} {c1|1}, {ca|1})`;
    // round 2: a binder at the capture, and at i and acc
    const H2 = `sum(${clo('h', 'from', '?a', { pat: true })}, {hi|?i}, {hacc|?acc}) =`;
    const B2 = '  if i == 0 then acc\n' +
      `  else let p = ${clo('g', 'from', 'a', { pat: true })}{gp|(}{gq|)} in sum(p.1, i - 1, acc + p.0)`;
    const B2b = '  if i == 0 then acc\n' +
      `  else {cs|sum}{co|(}${clo('c', 'from', 'a + 1')}{cx|,} {ci1|i} {cm2|-} {c12|1}, {cac|acc} {cp2|+} {caa|a}{cz|)}`;
    const OUT = `main(?n) = sum({o1|1}, n, 0)\n` +
      '  {wh|where} sum({oa|?a}, ?i, ?acc) =\n' +
      '    if i == 0 then acc else sum({ra|a} {rp|+} {r1|1}, i - 1, acc + a)';

    // "In the last example, the closure changes on every iteration. A stream is a closure that returns its
    // first value and the stream of the rest."
    code.show([L0, L1].join('\n'), cue('stream') - 0.3, { stagger: 0.008, byLine: 0.12 });
    const tDef = cue('def');
    code.mark(t => t.line === 1, C.dim, tDef - 0.15, { fill: 0.08, out: tDef + 2.2 });
    code.mark(['d1'], C.dim, tDef + 2.3, { fill: 0.08, out: tDef + 3.3, pad: 8 });
    code.mark(ids('dk'), C.dim, tDef + 3.4, { fill: 0.08, out: cue('from') - 0.3 });

    // "From of A is the stream A, A plus one, and so on." (to the right of from's line, smaller)
    const tF = cue('from');
    const desc = new Code(tl, root, 1090, Y + lh + (lh - Math.round(40 * 1.62)) / 2, 40);
    desc.show('from⟨a⟩ =', tF - 0.1, { stagger: 0.01 });
    desc.morph('from⟨a⟩ = a,', tF + 1.9, { dur: 0.5 });
    desc.morph('from⟨a⟩ = a, a + 1,', tF + 2.5, { dur: 0.5 });
    desc.morph('from⟨a⟩ = a, a + 1, a + 2, …', tF + 3.6, { dur: 0.5 });
    desc.hide(cue('sum') - 0.4, 0.35);

    // "Sum adds up the first values of a stream."
    const tS = cue('sum');
    code.morph([L0, L1, H0, B0].join('\n'), tS - 0.25, { dur: 0.6, stagger: 0.002 });

    // the round's name, top right (as in the refutation of the loop)
    const chip = box(root, W - 150 - 250, Y + 4, { width: '250px', height: '62px', borderRadius: '31px', boxShadow: `inset 0 0 0 2px ${alpha(C.ink, 0.5)}`, display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 600, letterSpacing: '0.2em', color: C.ink, whiteSpace: 'pre' }, 'ROUND 1');
    tl.set(chip, { o: 0, y: -14 }, 0);

    // ---- round 1: "In round one, sum's pattern is main's call, with the stream from one."
    const tR1 = cue('r1');
    tl.to(chip, { o: 1, y: 0 }, tR1 - 0.15, 0.6, E.out5);
    const mainCall = t => t.line === 0 && t.col >= 11;
    code.mark(mainCall, C.dim, tR1 + 1.95, { fill: 0.08, out: tR1 + 2.9 });
    code.swap([L0, L1, H1, B1].join('\n'), tR1 + 2.45);
    code.mark(ids('h'), C.pat, tR1 + 3.75, { fill: 0.12, out: cue('known') - 0.3 });

    // "Under it, the call of G is direct, and its result is known: one, and the stream from two."
    const tK = cue('known');
    code.mark([...ids('g'), 'gp', 'gq'], C.dim, tK + 0.6, { fill: 0.08, out: tK + 3.5 });
    const pY = Y + 5 * lh + 24;
    const pl = new Code(tl, root, RAIL, pY, S);
    pl.show('p = (1, from⟨2⟩)', tK + 3.6, { stagger: 0.01 });

    // "So the recursive call passes from two, which refutes the pattern."
    const tRf = cue('refute');
    code.swap([L0, L1, H1, B1b].join('\n'), tRf - 0.25);
    tl.to(pl.root, { o: 0.55 }, tRf - 0.2, 0.4);
    const tFrom2 = tRf + 1.75, tRefutes = tRf + 2.85, tJ = cue('join');
    code.mark(ids('h'), C.bad, tFrom2, { fill: 0.14, out: tJ - 0.3 });
    code.mark(ids('c'), C.bad, tFrom2, { fill: 0.14, out: tJ - 0.3 });
    // the other two places disagree as well
    code.mark(['hn'], C.bad, tRefutes, { fill: 0.1, out: tJ - 0.3, pad: 6 });
    code.mark(['cn', 'cm', 'c1'], C.bad, tRefutes, { fill: 0.1, out: tJ - 0.3, pad: 6 });
    code.mark(['h0'], C.bad, tRefutes, { fill: 0.1, out: tJ - 0.3, pad: 6 });
    code.mark(['ca'], C.bad, tRefutes, { fill: 0.1, out: tJ - 0.3, pad: 6 });
    const callEnd = RAIL + 29 * cw, cy = Y + 4.5 * lh;
    disc(tl, root, svg, callEnd + 46, cy, false, tRefutes, tJ - 0.3);
    const refuted = label(root, callEnd + 90, cy - 17, 'refuted', { color: C.bad });
    fadeIn(tl, refuted, tRefutes + 0.05, 0.4, 8); fadeOut(tl, refuted, tJ - 0.3, 0.3);
    fadeOut(tl, pl.root, tJ - 0.3, 0.3);

    // "Both calls pass a closure of from, so the join keeps from, and puts a binder at its capture.": the join
    // picture, whole by the word; then what it keeps lights, then the binder
    const JS = 50, jcw = charWidth(JS), jlh = Math.round(JS * 1.62);
    const jx = 1100, jr = 1480, jmid = Y + 2.5 * lh, jy1 = jmid - 1.5 * jlh, jy2 = jmid + 0.5 * jlh, jyr = jmid - 0.5 * jlh;
    const ja = new Code(tl, root, jx, jy1, JS), jb = new Code(tl, root, jx, jy2, JS);
    ja.show('from⟨1⟩', tJ - 0.4, { stagger: 0.01, dur: 0.4 });
    jb.show('from⟨2⟩', tJ - 0.35, { stagger: 0.01, dur: 0.4 });
    const jEnd = jx + 7 * jcw + 22;
    const a1 = arrow(tl, svg, jEnd, jy1 + jlh * 0.55, jr - 20, jyr + jlh * 0.4, { stroke: C.dim, width: 3, head: 12 });
    const a2 = arrow(tl, svg, jEnd, jy2 + jlh * 0.45, jr - 20, jyr + jlh * 0.6, { stroke: C.dim, width: 3, head: 12 });
    drawArrow(tl, a1, tJ - 0.2, 0.4); drawArrow(tl, a2, tJ - 0.15, 0.4);
    const jc = new Code(tl, root, jr, jyr, JS);
    jc.show(`${clo('j', 'from', '?a', { pat: true })}`, tJ + 0.05, { stagger: 0.01, dur: 0.4 });
    const jl = label(root, jr, jyr - 38, 'the join');
    fadeIn(tl, jl, tJ + 0.05, 0.4, 8);
    jc.mark(['j', 'jl', 'jr'], C.pat, tJ + 3.1, { fill: 0.12, out: tJ + 4.4 });
    jc.mark(['jc'], C.bind, tJ + 4.5, { fill: 0.14, pad: 6 });
    const tR2 = cue('r2');
    for (const c of [ja, jb, jc]) c.hide(tR2 - 0.4, 0.35);
    hideArrow(tl, a1, tR2 - 0.4); hideArrow(tl, a2, tR2 - 0.4); fadeOut(tl, jl, tR2 - 0.4, 0.35);

    // ---- round 2: "In round two, the recursive call passes from of A plus one, and that matches."
    tl.to(chip, { sy: 0.05 }, tR2 - 0.35, 0.2, E.in); tl.text(chip, 'ROUND 2', tR2 - 0.15); tl.to(chip, { sy: 1 }, tR2 - 0.15, 0.35, E.back);
    code.swap([L0, L1, H2, B2].join('\n'), tR2 - 0.2);
    const pl2 = new Code(tl, root, RAIL, pY, S);
    pl2.show('p = (a, from⟨a + 1⟩)', tR2 + 0.5, { stagger: 0.01 });
    code.swap([L0, L1, H2, B2b].join('\n'), tR2 + 1.05);
    tl.to(pl2.root, { o: 0.55 }, tR2 + 1.1, 0.4);
    fadeOut(tl, pl2.root, tR2 + 2.3, 0.3);
    // the check, place by place: each argument of the call against the pattern's place, a tick under it
    const tO = cue('out'), tOff = tO - 0.15, tickY = Y + 5 * lh + 16;
    const places = [
      [ids('h'), ids('c'), [11, 22], tR2 + 2.65],
      [['hi'], ['ci1', 'cm2', 'c12'], [24, 29], tR2 + 3.45],
      [['hacc'], ['cac', 'cp2', 'caa'], [31, 38], tR2 + 4.05],
    ];
    for (const [head, arg, [c0, c1], t] of places) {
      code.mark(head, C.good, t, { fill: 0.12, out: tOff, pad: 6 });
      code.mark(arg, C.good, t, { fill: 0.12, out: tOff, pad: 6 });
      disc(tl, root, svg, RAIL + (c0 + c1) / 2 * cw, tickY, true, t + 0.15, tOff);
    }
    const stable = label(root, RAIL + 39 * cw + 34, Y + 4.5 * lh - 17, 'stable', { color: C.good });
    fadeIn(tl, stable, tR2 + 4.75, 0.4, 8); fadeOut(tl, stable, tOff, 0.3);

    // "Where the source passed a stream, the output passes only its counter."
    tl.to(chip, { o: 0, y: -14 }, tOff, 0.4, E.in);
    code.swap(OUT, tO - 0.1);
    const tV = cue('var'), tCtr = tO + 3.3;
    code.mark(['o1'], C.dim, tCtr, { fill: 0.1, out: tV - 0.25, pad: 8 });
    code.mark(['ra', 'rp', 'r1'], C.dim, tCtr + 0.1, { fill: 0.1, out: tV - 0.25 });

    // "The stream has become a loop variable."
    code.mark(['oa'], C.bind, tV - 0.15, { fill: 0.14, pad: 6 });
    const lv = label(root, RAIL, Y + 3 * lh + 34, 'the stream is a loop variable');
    fadeIn(tl, lv, tV + 0.1, 0.5, 10);
  });
})();

// ==== src/scenes/s09_policies.js ====
// Several patterns for a block. One pattern for a fold called with two closures knows almost nothing (pol1); a
// policy sends each call to a version of the block for its context, and each version is a loop over numbers
// (pol2). Then the policy as a dial: the same fixed point is a dataflow analysis, a specializer, an inliner, a
// partial evaluator (dial).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;

  // the width of a text in a given style, measured off the stage (scenes are built while their root is hidden)
  function textWidth(text, style) {
    const m = document.createElement('span');
    Object.assign(m.style, { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' }, style);
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return w;
  }
  const CAPS = { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em' };
  const LAM = { fontFamily: 'var(--mono)', fontSize: '32px', fontWeight: 500, letterSpacing: '0' };
  // a small-caps label with a closure's name in it, `λ₁`, in the code font and not upper-cased (upper case would
  // make it a Λ). parts: strings, and ['λ₁'] for the name. Returns the label, its name's span and its width.
  function lamLabel(parent, x, y, parts, { color = C.dim } = {}) {
    const e = label(parent, x, y, undefined, Object.assign({}, CAPS, { textTransform: 'none', color }));
    let lam = null, w = 0;
    for (const p of parts) {
      if (Array.isArray(p)) {
        lam = el(e, 'span', Object.assign({ position: 'relative', display: 'inline-block', padding: '0 6px', margin: '0 -6px', borderRadius: '8px', border: `1.5px solid ${alpha(C.dim, 0)}`, background: alpha(C.dim, 0), color: C.code }, LAM), p[0]);
        w += textWidth(p[0], LAM);
      } else { el(e, 'span', { position: 'static' }, p); w += textWidth(p, CAPS); }
    }
    return { e, lam, w };
  }
  // the neutral "look here" mark on a closure's name in a label
  function lookLam(tl, l, at, out) {
    tl.to(l.lam, { bg: alpha(C.dim, 0.1), border: alpha(C.dim, 0.6) }, at, 0.35);
    if (out !== null && out !== undefined) tl.to(l.lam, { bg: alpha(C.dim, 0), border: alpha(C.dim, 0) }, out, 0.35);
  }
  function look(code, sel, at, out, pad = 8) { return code.mark(sel, C.dim, at, { fill: 0.08, pad, out }); }
  // a block: a panel with its name in the code font
  function blockBox(parent, x, cy, w, h, name, S) {
    return box(parent, x, cy - h / 2, {
      width: w + 'px', height: h + 'px', borderRadius: '16px', background: alpha(C.panel, 0.92), boxShadow: `inset 0 0 0 1.5px ${C.line}`,
      display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--mono)', fontSize: S + 'px', fontWeight: 560,
      color: C.ink, whiteSpace: 'pre', fontVariantLigatures: 'none',
    }, name);
  }
  // a block's call of itself: leaves the right side of its box near the top, comes back near the bottom
  function selfLoop(tl, svg, X, T, B, { stroke = C.dim, width = 3, reach = 100, head = 12 } = {}) {
    const y1 = T + 20, y2 = B - 20, c1 = [X + reach, T - 34], c2 = [X + reach, B + 34];
    const p = path(tl, svg, `M ${X + 4} ${y1} C ${c1[0]} ${c1[1]} ${c2[0]} ${c2[1]} ${X + 6} ${y2}`, { stroke, width });
    const ang = Math.atan2(y2 - c2[1], X + 6 - c2[0]) * 180 / Math.PI;
    const h = el(svg, 'path');
    h.setAttribute('d', `M ${-head} ${-head * 0.55} L 0 0 L ${-head} ${head * 0.55}`);
    h.setAttribute('fill', 'none'); h.setAttribute('stroke-width', width); h.setAttribute('stroke-linecap', 'round'); h.setAttribute('stroke-linejoin', 'round');
    h.style.stroke = stroke; h.setAttribute('transform', `translate(${X + 6} ${y2}) rotate(${ang})`);
    tl.set(h, { o: 0 }, 0);
    p._head = h;
    return p;
  }
  function strokeTo(tl, a, color, at, dur = 0.3) { tl.to(a, { stroke: color }, at, dur); tl.to(a._head, { stroke: color }, at, dur); }

  // ===== pol1 + pol2: the fold used twice, its join, and its versions =====================================
  scene(['pol1', 'pol2'], ({ tl, root, cue, seg, dur }) => {
    const S = 40, X = 160, Y = 196, cw = charWidth(S);
    const P = seg('pol2');

    // ---- pol1: the program ----------------------------------------------------------------------------
    // in three pieces, so that each λ has an empty row under it for its name
    const tTwice = cue('twice'), tFlow = cue('flow'), tBinder = cue('binder'), tCopies = cue('copies');
    const G = 48;                                          // the row under a λ line
    const code = new Code(tl, root, X, Y, S), lh = code.lh;
    const codeH = new Code(tl, root, X, Y + 4 * lh + G, S), codeR = new Code(tl, root, X, Y + 5 * lh + 2 * G, S);
    const t0 = tTwice - 0.35;
    code.show(
      '{fd|fold|f}(?f, ?s, ?i, ?n) =\n' +
      '  if i > n then s else fold(f, f(s, i), i + 1, n)\n' +
      'stats(?n) =\n' +
      '  let p = fold({l1|λ|v}(?s, ?i). (s.0 + i, s.1 + i * i{l1e|)}, (0, 0), 1, n) in', t0, { stagger: 0.003, byLine: 0.06 });
    codeH.show('  let h = fold({l2|λ|v}(?h, ?i). h * 31 + {l2e|i}, 0, 1, n) in', t0 + 0.24, { stagger: 0.003 });
    codeR.show('  (p.1 - p.0) + h', t0 + 0.3, { stagger: 0.003 });
    const codes = [code, codeH, codeR];
    const all = t => true;
    // "once to sum, and once to hash": each λ lit in turn, with its name under it
    const r1 = code.rect(['l1']), r2 = codeH.rect(['l2']);
    const sum = lamLabel(root, r1.x, Y + 4 * lh + 2, [['λ₁'], '  SUMS']);
    const hash = lamLabel(root, r2.x, Y + 5 * lh + G + 2, [['λ₂'], '  HASHES']);
    look(code, ['l1', 'l1e'], 4.55, 6.0, 8); fadeIn(tl, sum.e, 4.7, 0.5, 10);
    const u1 = code.underline(['l1', 'l1e'], C.dim, 4.6, { dy: 4 });
    look(codeH, ['l2', 'l2e'], 5.95, tFlow - 0.25, 8); fadeIn(tl, hash.e, 6.1, 0.5, 10);
    const u2 = codeH.underline(['l2', 'l2e'], C.dim, 6.0, { dy: 4 });

    // ---- pol1: the diagram, one pattern for fold ----------------------------------------------------
    // everything in the diagram lives in dg, so that it can move up as a whole for pol2
    const dg = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const svg = svgLayer(dg);
    const CY = 830, BH = 92, sx = 160, sw = 210, fx = 800, fw = 210, BS = 44;
    const stB = blockBox(dg, sx, CY, sw, BH, 'stats', BS), foB = blockBox(dg, fx, CY, fw, BH, 'fold', BS);
    fadeIn(tl, stB, tFlow - 0.2, 0.6, 14); fadeIn(tl, foB, tFlow + 0.1, 0.6, 14);
    codes.forEach(c => c.fade(all, 0.55, tFlow - 0.2, 0.6)); tl.to(u1, { o: 0.55 }, tFlow - 0.2, 0.6); tl.to(u2, { o: 0.55 }, tFlow - 0.2, 0.6);
    tl.to(sum.e, { o: 0.6 }, tFlow - 0.2, 0.6); tl.to(hash.e, { o: 0.6 }, tFlow - 0.2, 0.6);
    const ax0 = sx + sw + 12, ax1 = fx - 14;
    const a1 = arrow(tl, svg, ax0, CY - 16, ax1, CY - 16, { bend: -56, stroke: C.dim, width: 3, head: 12 });
    const a2 = arrow(tl, svg, ax0, CY + 16, ax1, CY + 16, { bend: 56, stroke: C.dim, width: 3, head: 12 });
    const tBoth = 9.2;                                     // "both calls flow into fold"
    drawArrow(tl, a1, tBoth, 0.55); drawArrow(tl, a2, tBoth + 0.3, 0.55);
    const pw = textWidth('PASSES  ', CAPS) + textWidth('λ₁', LAM), mx = (ax0 + ax1) / 2;
    const pass1 = lamLabel(dg, mx - pw / 2, CY - 16 - 28 - 44, ['PASSES  ', ['λ₁']]);
    const pass2 = lamLabel(dg, mx - pw / 2, CY + 16 + 28 + 14, ['PASSES  ', ['λ₂']]);
    fadeIn(tl, pass1.e, tBoth + 0.35, 0.5, 8); fadeIn(tl, pass2.e, tBoth + 0.65, 0.5, 8);
    const loop0 = selfLoop(tl, svg, fx + fw, CY - BH / 2, CY + BH / 2, { stroke: C.dim, reach: 96 });
    drawArrow(tl, loop0, 10.9, 0.6);
    // "its pattern is their join"
    const patX = 1150;
    const pat = new Code(tl, dg, patX, CY - lh / 2, S);
    pat.show('fold({pf|?f}, {ps|?s}, {pi|?i}, {pn|n|o})', 12.3, { stagger: 0.02 });

    // ---- pol1: f is one λ, then another: a binder, and the call through f is not direct ---------------
    lookLam(tl, pass1, 14.15, 15.95); tl.to(pass1.e, { color: C.code }, 14.15, 0.3); tl.to(pass1.e, { color: C.dim }, 15.95, 0.35);
    lookLam(tl, pass2, 16.05, 17.75); tl.to(pass2.e, { color: C.code }, 16.05, 0.3); tl.to(pass2.e, { color: C.dim }, 17.75, 0.35);
    pat.mark(['pf'], C.bind, 17.95, { pad: 7, out: tCopies - 0.3 });
    const fsi = ['f@1.2', '(@1.2', 's@1.2', ',@1.2', 'i@1.2', ')@1.1'];
    // the call through f lights; the rest of the program stays dim
    code.fade(fsi, 1, 19.85, 0.4);
    look(code, fsi, 19.95, tCopies - 0.3, 8);
    const fr = code.rect(fsi);
    const notDirect = label(root, fr.x, Y + 2 * lh + 2, 'not a direct call', { fontSize: '26px' });
    fadeIn(tl, notDirect, 21.0, 0.5, 8); fadeOut(tl, notDirect, tCopies - 0.3, 0.35, 0);
    code.fade(fsi, 0.55, tCopies - 0.3, 0.4);

    // ---- pol1: had the program two copies of fold ------------------------------------------------------
    // a second copy, faint, under the first: where the versions will be
    const ghost = blockBox(dg, fx, CY + 130, fw, BH, 'fold', BS);
    ghost.style.boxShadow = `inset 0 0 0 2px ${C.dim}`; ghost.style.background = 'transparent'; ghost.style.color = C.dim;
    tl.set(ghost, { o: 0, y: -130 }, 0); tl.to(ghost, { o: 0.8 }, 24.3, 0.4); tl.to(ghost, { y: 0 }, 24.3, 0.8, E.io);

    // ---- pol2: several patterns; the policy ------------------------------------------------------------
    const tPolicy = cue('policy'), tClosure = cue('closure'), tVers = cue('versions'), tEach = cue('each');
    const tRec = cue('rec'), tOut = cue('out'), tOnly = cue('only');
    codes.forEach(c => c.hide(P - 0.1, 0.4)); fadeOut(tl, sum.e, P - 0.1, 0.35); fadeOut(tl, hash.e, P - 0.1, 0.35);
    tl.to(ghost, { o: 0 }, P - 0.1, 0.35);
    const DY = -210;
    tl.to(dg, { y: DY }, P + 0.2, 0.9, E.io);
    const phrase = serif(root, X, 250, '', 52);
    el(phrase, 'span', { position: 'static' }, 'A policy says which part of a call is its ');
    el(phrase, 'span', { position: 'static', fontStyle: 'italic' }, 'context');
    el(phrase, 'span', { position: 'static' }, '.');
    fadeIn(tl, phrase, tPolicy - 0.2, 0.8, 20);
    tl.to(phrase, { o: 0.6 }, tClosure - 0.1, 0.6);
    // "the context is the labels of the closures that the call passes"
    const tLabels = P + 10.4;
    lookLam(tl, pass1, tLabels, null); lookLam(tl, pass2, tLabels + 0.1, null);
    tl.to(pass1.e, { color: C.code }, tLabels, 0.3); tl.to(pass2.e, { color: C.code }, tLabels + 0.1, 0.3);

    // ---- pol2: different contexts, different versions -------------------------------------------------
    tl.to(pat.root, { o: 0, y: -12 }, tVers - 0.2, 0.4, E.in);
    hideArrow(tl, loop0, tVers - 0.2, 0.3);
    const tSplit = P + 15.45;                               // "different versions"
    const V = 130, vy = [CY - V, CY + V];
    const vB = ['fold₁', 'fold₂'].map((nm, i) => {
      const b = blockBox(dg, fx, CY, fw, BH, nm, BS);
      tl.set(b, { o: 0 }, 0); tl.to(b, { o: 1 }, tSplit, 0.3); tl.to(b, { y: vy[i] - CY }, tSplit, 0.8, E.io);
      return b;
    });
    tl.to(foB, { o: 0 }, tSplit, 0.25);
    hideArrow(tl, a1, tSplit - 0.1, 0.25); hideArrow(tl, a2, tSplit - 0.1, 0.25);
    const va = [arrow(tl, svg, ax0, CY - 16, ax1, vy[0] + 10, { stroke: C.dim, width: 3, head: 12 }),
                arrow(tl, svg, ax0, CY + 16, ax1, vy[1] - 10, { stroke: C.dim, width: 3, head: 12 })];
    drawArrow(tl, va[0], tSplit + 0.45, 0.5); drawArrow(tl, va[1], tSplit + 0.55, 0.5);
    // the labels go with their arrows: above the one that rises, below the one that falls
    tl.to(pass1.e, { x: -10, y: -84 }, tSplit, 0.8, E.io); tl.to(pass2.e, { x: -10, y: 84 }, tSplit, 0.8, E.io);
    tl.to(pass1.lam, { bg: alpha(C.dim, 0), border: alpha(C.dim, 0) }, tSplit + 0.9, 0.4);
    tl.to(pass2.lam, { bg: alpha(C.dim, 0), border: alpha(C.dim, 0) }, tSplit + 0.9, 0.4);
    tl.to(pass1.e, { color: C.dim }, tSplit + 0.9, 0.4); tl.to(pass2.e, { color: C.dim }, tSplit + 0.9, 0.4);
    // "and each version has its own pattern"
    const vp = [new Code(tl, dg, patX, vy[0] - lh / 2, S), new Code(tl, dg, patX, vy[1] - lh / 2, S)];
    vp[0].show('fold({k|λ₁|p}, {a|(|p}?a{c|,|p} ?b{b|)|p}, ?i, {n|n|o})', tEach - 0.2, { stagger: 0.008 });
    vp[1].show('fold({k|λ₂|p}, ?h, ?i, {n|n|o})', tEach + 0.1, { stagger: 0.008 });

    // ---- pol2: the recursive call goes back to its own version ------------------------------------------
    const loops = vy.map(y => selfLoop(tl, svg, fx + fw, y - BH / 2, y + BH / 2, { stroke: C.dim, reach: 96 }));
    drawArrow(tl, loops[0], tRec - 0.2, 0.5); drawArrow(tl, loops[1], tRec - 0.05, 0.5);
    vp[0].pulse(['k'], P + 22.15, { dur: 0.8 }); vp[1].pulse(['k'], P + 22.25, { dur: 0.8 });
    loops.forEach((l, i) => { strokeTo(tl, l, C.ink, P + 23.35 + i * 0.1); strokeTo(tl, l, C.dim, P + 25.0, 0.6); });

    // ---- pol2: the output ---------------------------------------------------------------------------------
    tl.to(dg, { o: 0, y: DY - 18 }, tOut - 0.75, 0.4, E.in);
    fadeOut(tl, phrase, tOut - 0.75, 0.4);
    const OY = 380;
    const out = new Code(tl, root, X, OY, S);
    out.show(
      'stats(?n) = {u1|fold₁|f}(0, 0, 1)\n' +
      '  where {d1|fold₁|f}(?a, ?b, ?i) = if i > n then {u2|fold₂|f}(0, 1)\n' +
      '                            else {r1|fold₁|f}(a + i, b + i * i, i + 1)\n' +
      '          where {d2|fold₂|f}(?h, ?i) = if i > n then (b - a) + h\n' +
      '                                else {r2|fold₂|f}(h * 31 + i, i + 1)', tOut - 0.35, { stagger: 0.002, byLine: 0.05 });
    // "two loops over numbers": one, then the other
    look(out, ['d1'], P + 29.0, P + 30.0); look(out, ['r1'], P + 29.0, P + 30.0);
    look(out, ['d2'], P + 30.0, P + 31.1); look(out, ['r2'], P + 30.0, P + 31.1);
    const only = label(root, X, OY + 5 * lh + 34, 'the only way a block is copied', { fontSize: '26px' });
    fadeIn(tl, only, tOnly - 0.15, 0.6, 12);
  });

  // ===== dial: one fixed point, five policies ============================================================
  scene('dial', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const tD = ['d1', 'd2', 'd3', 'd4', 'd5'].map(c => cue(c));
    const tName = [6.62, 10.85, 15.72, 19.25, 23.0];       // where each name is spoken
    const LX = 196, TX = 260, top = 228, step = 148, NS = 64;
    const rows = [
      ['a version per block', 'A dataflow analysis'],
      ['a version per closure passed', 'A higher-order specializer'],
      ['a version per constructor passed', 'Call-pattern specialization'],
      ['a version per call site', 'An inliner'],
      ['a version per value of a marked parameter', 'A partial evaluator'],
    ];
    const ry = rows.map((_, i) => top + i * step);          // each row's top: its label
    const dotY = ry.map(y => y + 40 + 39);                  // level with the middle of the name
    const head = label(root, 160, 164, 'the policy', { fontSize: '26px' });
    fadeIn(tl, head, cue('dial') - 0.1, 0.6, 10);
    // the line and its stops
    const line = path(tl, svg, `M ${LX} ${dotY[0] - 26} L ${LX} ${dotY[4] + 26}`, { stroke: C.faint, width: 3 });
    tl.to(line, { draw: 1 }, cue('dial') + 0.1, 1.2, E.io);
    const stops = dotY.map((y, i) => {
      const s = el(svg, 'circle'); s.setAttribute('cx', LX); s.setAttribute('cy', y); s.setAttribute('r', 7);
      s.style.fill = C.bg; s.style.stroke = C.dim; s.setAttribute('stroke-width', 3);
      tl.set(s, { o: 0 }, 0); tl.to(s, { o: 1 }, cue('dial') + 0.3 + i * 0.2, 0.4);
      return s;
    });
    // the marker: a ring that moves from stop to stop
    const mk = el(svg, 'circle'); mk.setAttribute('cx', 0); mk.setAttribute('cy', 0); mk.setAttribute('r', 15);
    mk.style.fill = 'none'; mk.style.stroke = C.ink; mk.setAttribute('stroke-width', 3.5);
    mk._init = { x: LX, y: dotY[0] };
    tl.set(mk, { x: LX, y: dotY[0], o: 0 }, 0);
    tl.to(mk, { o: 1 }, tD[0] - 0.25, 0.4);
    rows.forEach(([k, n], i) => {
      const a = label(root, TX, ry[i], k, { fontSize: '26px' });
      const b = serif(root, TX, ry[i] + 40, n, NS);
      fadeIn(tl, a, tD[i] - 0.15, 0.6, 12); fadeIn(tl, b, tName[i] - 0.2, 0.7, 16);
      tl.to(stops[i], { fill: C.ink, stroke: C.ink }, tD[i] - 0.05, 0.3);
      if (i > 0) {
        tl.to(mk, { y: dotY[i] }, tD[i] - 0.35, 0.65, E.io);
        tl.to(stops[i - 1], { fill: C.dim, stroke: C.dim }, tD[i] - 0.3, 0.4);
      }
      if (i < 4) { tl.to(a, { o: 0.6 }, tD[i + 1] - 0.3, 0.5); tl.to(b, { o: 0.55 }, tD[i + 1] - 0.3, 0.5); }
    });
    // the first stop is the dial at zero (as the chapter on the kinds of pattern promised): nothing is copied
    const nocopy = label(root, TX + 760, ry[0] + 40 + 24, 'no code is copied', { fontSize: '26px' });
    fadeIn(tl, nocopy, tName[0] + 0.9, 0.6, 10); tl.to(nocopy, { o: 0.6 }, tD[1] - 0.3, 0.5);
    // level with the last name, in the same column as the first stop's note
    const interp = label(root, TX + 760, ry[4] + 40 + 24, 'an interpreter is specialized away', { fontSize: '26px' });
    fadeIn(tl, interp, cue('interp') - 0.1, 0.6, 10);
  });
})();

// ==== src/scenes/s10_theory.js ====
// What is proved: three theorems in Lean, each read in turn (thm); then what they cover, and what they do not
// (thm2). One scene for the two segments, so that the titles can move up and stay.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const CAPS = { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim };

  // a label built from parts that arrive one after another (inline, so each starts where the last ended)
  function partsLabel(tl, parent, x, y, parts, style = {}) {
    const e = box(parent, x, y, Object.assign({}, CAPS, { whiteSpace: 'pre' }, style));
    const spans = parts.map(([text, at]) => {
      const s = el(e, 'span', { position: 'relative', display: 'inline-block' }, text);
      tl.set(s, { o: 0, y: 10 }, 0); tl.to(s, { o: 1, y: 0 }, at, 0.5, E.out5);
      return s;
    });
    return { e, spans };
  }

  scene(['thm', 'thm2'], ({ tl, root, cue, seg }) => {
    const svg = svgLayer(root);
    const X = 160;
    const t = ['t1', 't2', 't3'].map(c => cue(c));
    const Q = seg('thm2');

    // ---- thm: what was proved, and about what --------------------------------------------------------
    const tLean = cue('lean');
    const lean = label(root, X, 226, 'proved in Lean 4', Object.assign({}, CAPS, { color: C.code }));
    fadeIn(tl, lean, tLean - 0.2, 0.6, 10);
    // "for a core language with constructors, closures and operations, and one pattern for each block"
    const scope = partsLabel(tl, root, X, 272, [
      ['a core language:  ', 5.4], ['constructors,  ', 6.3], ['closures,  ', 7.3], ['operations', 8.05], ['   ·   one pattern per block', 9.5],
    ]);

    // ---- thm: the three theorems, one row each --------------------------------------------------------
    const titles = ['Stable patterns hold when the program runs.', 'Stable patterns are safe to use.', 'The algorithm finds the most specific stable patterns.'];
    const subs = [
      "at every step, the running block's values are an instance of its pattern",
      'the rewritten program halts with the same value, or neither halts',
      'every run terminates, in any order, with stable patterns at least as specific as any other',
    ];
    const tSub = [16.0, 24.5, 34.6];                     // "At every step", "The rewritten", "Every run"
    const RY = [370, 550, 730];
    const rows = titles.map((tt, i) => {
      const num = label(root, X, RY[i], 'theorem 5.' + (i + 1), CAPS);
      const ti = serif(root, X, RY[i] + 38, tt, 48);
      const sb = serif(root, X, RY[i] + 104, subs[i], 38, { fontStyle: 'italic', color: C.dim });
      fadeIn(tl, num, t[i] - 0.25, 0.6, 12); fadeIn(tl, ti, t[i] + 0.05, 0.7, 18);
      fadeIn(tl, sb, tSub[i] - 0.15, 0.7, 12);
      if (i < 2) {
        // the next theorem is read: this one dims, its gloss goes
        tl.to(num, { o: 0.55 }, t[i + 1] - 0.3, 0.5); tl.to(ti, { o: 0.55 }, t[i + 1] - 0.3, 0.5);
        fadeOut(tl, sb, t[i + 1] - 0.3, 0.4, 0);
      }
      return { num, ti, sb };
    });

    // ---- thm2: the titles move up, small; what the theorems are about ----------------------------------
    tl.to(lean, { o: 0 }, Q - 0.1, 0.4, E.in); tl.to(scope.e, { o: 0 }, Q - 0.1, 0.4, E.in);
    const topY = [230, 276, 322];
    rows.forEach((r, i) => {
      tl.to(r.num, { o: 0 }, Q - 0.1, 0.35, E.in);
      if (i === 2) fadeOut(tl, r.sb, Q - 0.1, 0.35, 0);
      r.ti.style.transformOrigin = 'left top';
      tl.to(r.ti, { y: topY[i] - (RY[i] + 38), s: 30 / 48, o: 0.6 }, Q + 0.05, 0.85, E.io);
    });
    const SY = [470, 610, 750], stateX = 1420;
    const items = [
      ['The Lean formalization', 'proved', Q + 1.75, Q + 2.85],
      ["The reference implementation · the compiler's optimizer", 'tested', Q + 3.95, Q + 7.2],
      ['Specialization policies', 'not proved', Q + 9.5, Q + 10.4],
    ];
    const its = items.map(([name, state, a, b], i) => {
      const n = serif(root, X, SY[i], name, 44);
      const s = label(root, stateX + (i === 0 ? 52 : 0), SY[i] + 12, state, CAPS);
      fadeIn(tl, n, a - 0.2, 0.7, 16); fadeIn(tl, s, b - 0.15, 0.5, 10);
      return { n, s };
    });
    // proved: a tick before the word, neutral (green is for a matching call and "stable")
    tl.set(its[0].s, { color: C.ink }, 0);
    const tk = tick(tl, svg, stateX + 18, SY[0] + 27, 30, C.ink, 4);
    tl.to(tk, { draw: 1 }, Q + 2.75, 0.4, E.out);
    tl.set(its[1].s, { color: C.dim }, 0); tl.set(its[2].s, { color: C.dim }, 0);
    // the row being talked about is bright, the ones before it dim
    tl.to(its[0].n, { o: 0.55 }, Q + 3.75, 0.5); tl.to(its[0].s, { o: 0.6 }, Q + 3.75, 0.5); tl.to(tk, { o: 0.6 }, Q + 3.75, 0.5);
    tl.to(its[1].n, { o: 0.55 }, Q + 9.4, 0.5); tl.to(its[1].s, { o: 0.7 }, Q + 9.4, 0.5);
    // "for some policies the third one fails": the third title lights for a moment
    tl.to(rows[2].ti, { o: 1 }, Q + 14.5, 0.4); tl.to(rows[2].ti, { o: 0.6 }, Q + 16.0, 0.5);
    const fut = label(root, X, SY[2] + 74, 'future work', CAPS);
    fadeIn(tl, fut, cue('future') - 0.15, 0.6, 10);
  });
})();

// ==== src/scenes/s11_practice.js ====
// In practice, briefly: the idea is the point. use1: a compiler whose only optimizer is this analysis (twelve
// programs written twice, nine the same assembly). use2: two ports, some programs faster, most unchanged. use3: the
// constructors half of the paper's Figure 6, how often seven published analyses find the most specific patterns,
// and ours below them.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;

  // an inline piece of a row of text (a flex child the timeline can move)
  function piece(parent, text, style = {}) {
    const s = document.createElement('span');
    Object.assign(s.style, { position: 'relative', display: 'inline-block', whiteSpace: 'pre' }, style);
    s.textContent = text; s._text0 = text; s._shown = text;
    parent.appendChild(s);
    return s;
  }

  // the three settings, one row of small-caps headings at the top; `lit` is the setting being talked about
  // (the mono scene in s14_more.js copies these positions and sizes)
  const HEADS = ["1 · A compiler's only optimizer", '2 · Ports to mature optimizers', '3 · An experiment'];
  function headings(tl, root, lit, { at = 0, stagger = 0, dimAt = null } = {}) {
    return HEADS.map((t, i) => {
      const h = box(root, [160, 760, 1360][i], 190, { whiteSpace: 'pre', fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim }, t);
      const on = i === lit;
      if (dimAt === null) {
        // already known: in place from the start, the current one bright
        tl.set(h, { o: 0, color: on ? C.ink : C.dim }, 0);
        tl.to(h, { o: on ? 1 : 0.55 }, at, 0.4, E.out5);
      } else {
        // first arrival: one after another, all neutral; then the current one stays and the others step back
        tl.set(h, { o: 0, y: 14, color: C.code }, 0);
        tl.to(h, { o: 1, y: 0 }, at + i * stagger, 0.6, E.out5);
        if (on) tl.to(h, { color: C.ink }, dimAt, 0.5);
        else tl.to(h, { o: 0.55, color: C.dim }, dimAt, 0.5);
      }
      return h;
    });
  }

  // an arrow as a piece of a row of text
  function arrowPiece(tl, row, w = 140, h = 44) {
    const aw = piece(row, '', { width: (w + 90) + 'px', height: h + 'px' });
    const asv = el(aw, 'svg'); asv.setAttribute('width', w + 90); asv.setAttribute('height', h);
    Object.assign(asv.style, { position: 'absolute', left: 0, top: 0, overflow: 'visible' });
    return arrow(tl, asv, 45, h / 2, 45 + w, h / 2, { stroke: C.dim, width: 3.5, head: 14 });
  }
  const capsRow = (root, y, size, extra = {}) => box(root, 0, y, Object.assign({ width: W + 'px', display: 'flex', justifyContent: 'center', alignItems: 'center', whiteSpace: 'pre', fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim }, extra));

  // ---- use1: a compiler whose only optimizer is this analysis ---------------------------------------------------
  // word times (seconds into the segment) from build/audio/use1.json
  scene('use1', ({ tl, root, cue }) => {
    const tBrief = cue('brief'), tComp = cue('compiler'), tTw = cue('twelve'), tNine = cue('nine');
    const at = (w) => w;   // word times are already on the segment's clock (the scene starts with the segment)
    headings(tl, root, 0, { at: tBrief - 0.25, stagger: 0.3, dimAt: tComp - 0.2 });

    // the key phrase: the idea is the point
    const key = serif(root, 0, 500, 'The idea is the point; the practice, briefly.', 52, { width: W + 'px', textAlign: 'center' });
    fadeIn(tl, key, tBrief + 0.1, 0.8, 22);
    fadeOut(tl, key, tComp - 0.45, 0.4);

    // "in a compiler for a dependently typed language, this analysis is the only optimizer before LLVM"
    const pipe = capsRow(root, 500, 26);
    const stageBox = (text, bright) => piece(pipe, text, { padding: '24px 34px', borderRadius: '14px', background: alpha(C.panel, 0.9),
      boxShadow: `inset 0 0 0 ${bright ? 2.5 : 1.5}px ${bright ? C.ink : C.dim}`, color: bright ? C.ink : C.dim });
    const b1 = stageBox('A dependently typed language', false), a1 = arrowPiece(tl, pipe, 90);
    const b2 = stageBox('This analysis', true), a2 = arrowPiece(tl, pipe, 90);
    const b3 = stageBox('LLVM', false);
    fadeIn(tl, b1, tComp + 0.05, 0.6, 14);       // "a compiler for a dependently typed language"
    drawArrow(tl, a1, at(11.42) - 0.45, 0.4);
    fadeIn(tl, b2, at(11.42) - 0.2, 0.6, 14);     // "this analysis"
    drawArrow(tl, a2, at(14.38) - 0.45, 0.4);
    fadeIn(tl, b3, at(14.38) - 0.2, 0.6, 14);     // "LLVM"
    tl.to(pipe, { o: 0, y: -12 }, tTw - 0.45, 0.4, E.in);

    // twelve programs, each a column of two tiles: with an abstraction (top), by hand (bottom)
    const N = 12, TW = 92, TH = 96, PITCH = 104, GW = 11 * PITCH + TW, LW = 384, X0 = Math.round((W - GW) / 2 + LW / 2), Y1 = 440, Y2 = Y1 + TH + 18;
    const top = label(root, X0, 370, 'Twelve programs, written twice', { fontSize: '26px' });
    fadeIn(tl, top, at(16.3) - 0.2, 0.6, 12);     // "twelve"
    const rowLab = (y, text, t) => {
      const l = label(root, X0 - LW, y + TH / 2 - 17, text, { width: (LW - 36) + 'px', textAlign: 'right', fontSize: '26px' });
      fadeIn(tl, l, t, 0.6, 0); tl.set(l, { x: -12 }, 0); tl.to(l, { x: 0 }, t, 0.6, E.out5);
      return l;
    };
    rowLab(Y1, 'With an abstraction', at(17.9) - 0.25);   // "with an abstraction"
    rowLab(Y2, 'By hand', at(17.9) + 0.45);
    const tile = (x, y, t) => {
      const b = box(root, x, y, { width: TW + 'px', height: TH + 'px', borderRadius: '14px', background: alpha(C.panel, 0.95), boxShadow: `inset 0 0 0 1.5px ${C.line}` });
      tl.set(b, { o: 0, s: 0.9 }, 0); tl.to(b, { o: 1, s: 1 }, t, 0.5, E.out5);
      const ring = box(b, 0, 0, { width: '100%', height: '100%', borderRadius: '14px', boxShadow: `inset 0 0 0 2px ${alpha(C.good, 0.8)}` });
      tl.set(ring, { o: 0 }, 0);
      return { b, ring };
    };
    const svg = svgLayer(root);
    const cols = [];
    for (let i = 0; i < N; i++) {
      const x = X0 + i * PITCH;
      cols.push({ x, a: tile(x, Y1, at(16.3) - 0.1 + i * 0.05), b: tile(x, Y2, at(17.9) + 0.45 + i * 0.05) });
    }
    // "nine of them compile to the same assembly": nine columns confirmed, three stay neutral
    const tN = tNine - 0.1;
    cols.forEach((c, i) => {
      if (i >= 9) { for (const t of [c.a, c.b]) tl.to(t.b, { o: 0.75 }, tN + 0.5, 0.5); return; }
      const t = tN + i * 0.07;
      for (const t2 of [c.a, c.b]) { tl.to(t2.b, { bg: alpha(C.good, 0.14) }, t, 0.4); tl.to(t2.ring, { o: 1 }, t, 0.4); }
      const k = tick(tl, svg, c.x + TW / 2, Y2 + TH + 46, 34, C.good, 5);
      tl.to(k, { draw: 1 }, t + 0.15, 0.35, E.out);
    });
    const same = label(root, X0, Y2 + TH + 100, 'Same assembly', { width: (8 * PITCH + TW) + 'px', textAlign: 'center', fontSize: '26px' });
    fadeIn(tl, same, at(24.5) - 0.25, 0.6, 10);   // "same assembly"
  });

  // ---- use2: two ports: some programs faster, most unchanged -----------------------------------------------------
  scene('use2', ({ tl, root, cue }) => {
    const tSome = cue('some'), tMost = cue('most');
    headings(tl, root, 1, { at: 0 });
    const LX = 600, RX = 1320, CWID = 700;
    const centred = (e, cx) => { e.style.left = (cx - CWID / 2) + 'px'; e.style.width = CWID + 'px'; e.style.textAlign = 'center'; return e; };

    const to = label(root, 0, 390, 'Ported to', { width: W + 'px', textAlign: 'center' });
    fadeIn(tl, to, cue("ports") + 0.1, 0.6, 10);   // "parts of the analysis are also ported"
    const fl = centred(serif(root, 0, 450, 'Flambda 2 (OxCaml)', 64), LX);
    const cz = centred(serif(root, 0, 450, 'Chez Scheme', 64), RX);
    fadeIn(tl, fl, 4.9 - 0.2, 0.7, 20);           // "Flambda two"
    fadeIn(tl, cz, 6.02 - 0.2, 0.7, 20);          // "Chez Scheme"

    const some = label(root, 0, 610, 'Some programs faster', { width: W + 'px', textAlign: 'center', fontSize: '28px', color: C.ink });
    fadeIn(tl, some, tSome + (8.14 - 7.3) - 0.25, 0.6, 12);   // "some"
    const most = label(root, 0, 666, 'Most unchanged', { width: W + 'px', textAlign: 'center', fontSize: '28px', color: C.ink });
    fadeIn(tl, most, tMost + (9.46 - 9.06) - 0.25, 0.6, 12);  // "most"
    tl.to(some, { color: C.dim }, tMost + 0.15, 0.5);
  });

  // ---- use3: programs with constructors: how often seven published analyses find the most specific patterns -----
  scene('use3', ({ tl, root, cue }) => {
    const tExp = cue('exp'), tMiss = cue('miss'), tOurs = cue('ours');
    headings(tl, root, 2, { at: 0 });

    const ROWS = [
      ["Click's combined analysis", 70], ['Lemerre', 76], ['Flambda 2', 61], ['Braun et al.', 60],
      ["Cooper and Simpson's SCC", 59], ["Simpson's RPO", 59], ['SCCP', 58],
    ];
    const NX = 160, NR = 720, GX = 754, SCALE = 9, BH = 26, Y0 = 372, PITCH = 74, NH = 54, NS = 44;

    // what the chart is: its heading, on two lines
    const head = label(root, NX, 252, 'Programs with constructors:\nshare where the most specific patterns are found (%)', { lineHeight: '36px' });
    fadeIn(tl, head, tExp + (2.86 - 0.5) - 0.25, 0.6, 10);   // "with constructors"

    const bar = (y, v, color, t, numColor = C.code) => {
      const cy = y + NH / 2;
      const b = box(root, GX, cy - BH / 2, { width: v * SCALE + 'px', height: BH + 'px', borderRadius: '4px', background: color, transformOrigin: 'left center' });
      tl.set(b, { sx: 0, o: 0 }, 0); tl.set(b, { o: 1 }, t); tl.to(b, { sx: 1 }, t, 0.8, E.io);
      const n = box(root, GX + v * SCALE + 16, cy - 23, { fontFamily: 'var(--sans)', fontSize: '38px', fontWeight: 500, lineHeight: '46px', color: numColor, fontVariantNumeric: 'tabular-nums', whiteSpace: 'pre' }, String(v));
      tl.set(n, { o: 0, x: -8 }, 0); tl.to(n, { o: 1, x: 0 }, t + 0.7, 0.4, E.out5);
      return { b, n };
    };

    // the seven names as the sentence begins, their bars at "seven published analyses"
    const tBars = tExp + (4.18 - 0.5) - 0.2;
    const rows = ROWS.map(([name, v], i) => {
      const y = Y0 + i * PITCH;
      const nm = serif(root, NX, y, name, NS, { width: (NR - NX) + 'px', textAlign: 'right', color: C.code });
      fadeIn(tl, nm, tExp - 0.2 + i * 0.1, 0.6, 14);
      return { nm, ...bar(y, v, C.key, tBars + i * 0.08) };
    });

    // "a miss is not an error": where our row will be
    const yO = Y0 + 7 * PITCH + 26;
    const miss = label(root, GX, yO + NH / 2 - 17, 'A miss is not an error', { fontSize: '28px' });
    fadeIn(tl, miss, tMiss - 0.2, 0.6, 10);
    fadeOut(tl, miss, tOurs - 0.55, 0.35);

    // ours, set apart: full, in green
    const tO = tOurs - 0.2;
    const on = serif(root, NX, yO, 'Ours', NS, { width: (NR - NX) + 'px', textAlign: 'right', color: C.ink });
    fadeIn(tl, on, tO, 0.6, 14);
    bar(yO, 100, C.good, tO + 0.15);
    const thm = label(root, NX, yO + NH / 2 - 16, 'Theorem 5.3', { width: (NR - NX - 130) + 'px', textAlign: 'right', fontSize: '26px' });
    fadeIn(tl, thm, tOurs + (19.7 - 15.06) - 0.25, 0.6, 8);   // "the third theorem"
    rows.forEach(r => { for (const e of [r.nm, r.b, r.n]) tl.to(e, { o: 0.65 }, tO, 0.6); });
  });
})();

// ==== src/scenes/s12_close.js ====
// What is left, and the close: the six analyses of the opening become one idea, its most specific pattern, the
// loop that finds it, and what a closure and several patterns add. The film ends on the title.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // an inline piece of a row (a flex child the timeline can move)
  function piece(parent, text, style = {}) {
    const s = document.createElement('span');
    Object.assign(s.style, { position: 'relative', display: 'inline-block', whiteSpace: 'pre' }, style);
    s.textContent = text; s._text0 = text; s._shown = text;
    parent.appendChild(s);
    return s;
  }
  const LABEL = { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim };
  function labelRow(root, x, y, gap) {
    return box(root, x, y, { display: 'flex', alignItems: 'baseline', gap: gap + 'px', whiteSpace: 'pre' });
  }

  // ---- close ------------------------------------------------------------------------------------------------
  scene('close', ({ tl, root, cue, dur, info }) => {
    // the six names of the opening, a column on the rail, each as it is said
    const names = ['Constant propagation', 'Value numbering', 'SSA construction', 'Unboxing', 'Contification', 'Control-flow analysis of closures'];
    // when each is said, from the recording (the segment has one cue for the six)
    const said = [1.9, 3.5, 4.7, 6.38, 7.46, 8.74].map(t => t - 1.9 + cue('recap'));
    const tU = cue('unify'), PY = 330;
    names.forEach((n, i) => {
      const y = 300 + i * 74;
      const e = serif(root, RAIL, y, n, 48, { transformOrigin: 'left center' });
      fadeIn(tl, e, said[i] - 0.2, 0.6, 18);
      // "usually separate analyses": nothing new. "Stable patterns unify them.": they gather into one phrase
      tl.to(e, { y: PY + 10 - y, s: 0.7 }, tU - 0.35, 0.6, E.io);
      tl.to(e, { o: 0 }, tU - 0.35, 0.5, E.lin);
    });
    const phrase = serif(root, RAIL, PY, 'Stable patterns', 72);
    fadeIn(tl, phrase, tU + 0.1, 0.7, 16);

    // "The most specific stable patterns exist": the film's loop, its most specific pattern
    const P = 56, pat = new Code(tl, root, RAIL, 480, P), plh = pat.lh;
    const tX = cue('exists');
    pat.show('loop(?i, {u1|u|o}, {x1|1|p}, {sm|Some|p}{s0|(|p}{s1|(|p}?s{s2|,|p} {u2|u|o}{s3|)|p}{s4|)|p})', tX - 0.15, { stagger: 0.01, rise: 16 });

    // "assume the best, simplify under it, and weaken only where a call contradicts the assumption"
    // the film's takeaway, in serif: the word being said is ink, the ones before it step back
    const words = labelRow(root, RAIL, 480 + plh + 24, 22);
    const cs = ['assume', 'simplify', 'weaken'].map(c => cue(c));
    const SERIF = { fontFamily: 'var(--serif)', fontSize: '46px', lineHeight: 1.22, letterSpacing: '-0.005em', color: C.ink };
    [['Assume', 0], ['·', 1], ['Simplify', 1], ['·', 2], ['Weaken only where refuted', 2]].forEach(([t, k]) => {
      const p = piece(words, t, SERIF), dot = t === '·';
      tl.set(p, { o: 0, y: 12, color: dot ? C.dim : C.ink }, 0); tl.to(p, { o: 1, y: 0 }, cs[k] - 0.15, 0.6, E.out5);
      if (!dot) tl.to(p, { color: C.dim }, k < 2 ? cs[k + 1] - 0.15 : cue('clo') - 1.0, 0.4);
    });
    const tC = cue('clo');
    tl.to(words, { o: 0, y: -10 }, tC - 0.35, 0.35, E.in);

    // "With a closure in a pattern, the analysis is interprocedural and higher-order."
    pat.swap('app({ai|inc|p}{al|⟨|p}{au|u|o}{ar|⟩|p})', tC - 0.2);
    const l1 = label(root, RAIL, 480 + plh + 34, 'interprocedural and higher-order');
    fadeIn(tl, l1, tC + 0.8, 0.5, 10);
    const tS = cue('several');
    fadeOut(tl, l1, tS - 0.35, 0.3);

    // "With several patterns for a block, the same fixed point is a specializer, an inliner, or a partial
    // evaluator."
    pat.swap('fold({f1|λ₁|p}, {p0|(|p}?a{pc|,|p} ?b{p1|)|p}, ?i, {n1|n|o})\nfold({f2|λ₂|p}, ?h, ?i, {n2|n|o})', tS - 0.2);
    const kinds = labelRow(root, RAIL, 480 + 2 * plh + 34, 0);
    [['a specializer', 3.52], [', an inliner', 4.64], [', a partial evaluator', 5.88]].forEach(([t, dt]) => {
      const p = piece(kinds, t, LABEL);
      fadeIn(tl, p, tS + dt - 0.2, 0.5, 10);
    });

    // "And it is this one analysis that reduced the four-parameter loop to two, and turned the stream into a
    // counter.": the cold open's two results, before and after, heads only
    const tB = cue('back'), tK = cue('counter');
    pat.hide(tB - 0.3, 0.35); tl.to(kinds, { o: 0, y: -10 }, tB - 0.3, 0.35, E.in);
    const svg = svgLayer(root), B = 50, bcw = charWidth(B), blh = Math.round(B * 1.62);
    const bx = RAIL + 20 * bcw + 140, rows = [];
    [['loop(?i, ?a, ?x, ?q)', 'loop(?i, ?s)', tB - 0.1, tB + 4.1], ['sum(from⟨1⟩, n, 0)', 'sum(1, n, 0)', tK - 0.15, tK + 1.5]].forEach(([a, b, ta, tb], i) => {
      const y = 480 + i * (blh + 24);
      const before = new Code(tl, root, RAIL, y, B), after = new Code(tl, root, bx, y, B);
      before.show(a, ta, { stagger: 0.01 });
      const ar = arrow(tl, svg, RAIL + 20 * bcw + 36, y + blh / 2, bx - 36, y + blh / 2, { stroke: C.dim, width: 3, head: 12 });
      drawArrow(tl, ar, tb - 0.2, 0.35);
      after.show(b, tb, { stagger: 0.01 });
      rows.push(before, after, ar);
    });

    // the end: everything but the phrase leaves, the phrase settles in the middle of the frame, and the title
    // arrives under it. It starts just after the last word and is finished 1.5 s later; the rest of the
    // post-roll holds it to the last frame
    const post = info.segs[info.segs.length - 1].post, tE = dur - post + 0.4;
    for (const r of rows) { if (r.hide) r.hide(tE, 0.4); else hideArrow(tl, r, tE, 0.4); }
    const down = 432 - PY;
    tl.to(phrase, { y: down }, tE + 0.15, 0.9, E.io);
    const title = serif(root, RAIL, 432 + 104, 'Dataflow Facts as Stable Patterns', 40, { color: alpha(C.ink, 0.72) });
    fadeIn(tl, title, tE + 0.65, 0.8, 14);
    return { keep: true };
  });
})();

// ==== src/scenes/s13_signposts.js ====
// The cold open (a before and an after, twice) and five short signposts that say what is notable about what was
// just shown. The signposts share one look: a WORTH NOTICING tag at the top of a block centred on the rail, the
// evidence under it, large, and at most one line in ink that is the verdict.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // the width of a line of text, measured off-stage
  function measure(text, style) {
    const m = document.createElement('span');
    Object.assign(m.style, { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' }, style);
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return w;
  }
  const LABEL = { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase' };
  const labelW = (text, size = 26) => measure(text, Object.assign({}, LABEL, { fontSize: size + 'px' })) - size * 0.16;
  const serifW = (text, size) => measure(text, { fontFamily: 'var(--serif)', fontSize: size + 'px', letterSpacing: '-0.005em' });

  // the signpost's tag, in ink, at the top of the block
  function tag(tl, root, y, at, text = 'worth noticing') {
    const t = label(root, RAIL, y, text, { color: C.ink, fontSize: '26px' });
    fadeIn(tl, t, at, 0.6, 10);
    return t;
  }
  // a round chip, as in the refutation scenes
  function chip(root, x, y, text) {
    return box(root, x, y, { width: '230px', height: '62px', borderRadius: '31px', boxShadow: `inset 0 0 0 2px ${alpha(C.ink, 0.5)}`, display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--sans)', fontSize: '24px', fontWeight: 600, letterSpacing: '0.2em', color: C.ink, whiteSpace: 'pre' }, text);
  }
  // a disc with a tick, centred at (cx, cy)
  function okDisc(tl, root, svg, cx, cy, at) {
    const d = box(root, cx - 22, cy - 22, { width: '44px', height: '44px', borderRadius: '50%', background: C.good });
    tl.set(d, { o: 0, s: 0.3 }, 0); tl.to(d, { o: 1, s: 1 }, at, 0.3, E.back);
    svg.parentNode.appendChild(svg);
    const m = tick(tl, svg, cx, cy, 15, C.bg, 4);
    tl.to(m, { draw: 1 }, at + 0.15, 0.3, E.out);
    return d;
  }
  // a small-caps label struck through (deletion is neutral: a grey line, the text goes faint)
  function strikeLabel(tl, root, e, x, y, text, at, size = 26) {
    const w = labelW(text, size);
    const u = box(root, x - 6, y + size * 0.6 - 1, { width: (w + 12) + 'px', height: '3px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center', opacity: 0 });
    tl.set(u, { sx: 0, o: 1 }, 0); tl.to(u, { sx: 1 }, at, 0.4, E.io);
    tl.to(e, { color: C.faint }, at, 0.4);
    return u;
  }

  // ============================================ hook ===========================================================
  scene('hook', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 40;
    // ---- the four-parameter loop and its output ------------------------------------------------------------
    const y1 = 215;
    const src = new Code(tl, root, RAIL, y1, S), lh = src.lh, cw = src.cw;
    src.show([
      'main(?u, ?n) = loop(n, u, {c1|1}, {s0|Some}{s1|(}{s2|(}{s3|0}{s4|,} {s5|u}{s6|)}{s7|)})',
      'loop(?i, ?a, ?x, ?q) =',
      '  case q of None → 0 | Some((?s, ?t)) →',
      '  if i == 0 then s + t',
      '  else if x == 1 then',
      '    loop(i - 1, a, 2 - x, Some((s + a, t + (t - a))))',
      '  else loop(i - 1, i, 99, q)',
    ].join('\n'), cue('loop') - 0.45, { stagger: 0.003, byLine: 0.05 });
    const SOME = ['s0', 's1', 's2', 's3', 's4', 's5', 's6', 's7'], DEAD = t => t.line === 6;
    // the notation is not explained until later: a small legend beside the program while it arrives
    const gx = 1210, gy = y1 + lh + 8;
    const leg = new Code(tl, root, gx, gy, S).show('?x {c|:|d}', 1.0, { stagger: 0.02 });
    const g1 = label(root, gx + 5 * cw, gy + (lh - 31) / 2 - 18, 'a parameter,'), g2 = label(root, gx + 5 * cw, gy + (lh - 31) / 2 + 18, 'where it is bound');
    fadeIn(tl, g1, 1.15, 0.5, 8); fadeIn(tl, g2, 1.25, 0.5, 8);
    leg.hide(7.0, 0.4); fadeOut(tl, g1, 7.0, 0.4); fadeOut(tl, g2, 7.0, 0.4);
    // "An optimizer could reduce it to this"
    const tOut = cue('out');
    const ay0 = y1 + 7 * lh + 14, ay1 = ay0 + 64;
    const down = arrow(tl, svg, RAIL + 18, ay0, RAIL + 18, ay1, { stroke: C.dim, width: 3, head: 11 });
    drawArrow(tl, down, tOut - 0.4, 0.45);
    const becomes = label(root, RAIL + 56, ay0 + 18, 'becomes');
    fadeIn(tl, becomes, tOut - 0.3, 0.5, 8);
    const y2 = ay1 + 18;
    const out = new Code(tl, root, RAIL, y2, S);
    out.show('main(?u, ?n) = loop(n, 0)\n  where loop({oi|?i}{oc|,} {os|?s}) = if i == 0 then s + {u1|u|o} else loop(i - 1, s + {u2|u|o})', tOut - 0.15, { stagger: 0.003, byLine: 0.06 });
    // "two parameters"
    out.mark(['oi', 'oc', 'os'], C.bind, 6.6, { out: 7.8, pad: 8 });
    // "with the constant, the dead branch, the option and the pair all gone"
    src.mark(['c1'], C.dim, 8.05, { fill: 0.08, out: 8.85, pad: 7 });
    src.mark(DEAD, C.dim, 8.9, { fill: 0.08, out: 9.9, pad: 7 });
    src.mark(SOME, C.dim, 9.95, { fill: 0.08, out: 11.5, pad: 7 });
    src.color(['c1', ...SOME], C.faint, 11.6, 0.5); src.color(DEAD, C.faint, 11.6, 0.5);
    // "LLVM does not get all the way there"
    const llvm = label(root, RAIL + 25 * cw + 70, y2 + (lh - 31) / 2, 'llvm -O3 stops one step short');
    fadeIn(tl, llvm, cue('llvm') - 0.1, 0.5, 8);
    // ---- the stream and its counter ------------------------------------------------------------------------
    const tS = cue('stream');
    for (const c of [src, out]) c.hide(tS - 0.75, 0.4);
    hideArrow(tl, down, tS - 0.75, 0.4); fadeOut(tl, becomes, tS - 0.75, 0.4); fadeOut(tl, llvm, tS - 0.75, 0.4);
    const y3 = 170;
    const st = new Code(tl, root, RAIL, y3, S);
    st.show([
      'main(?n) = sum(from⟨1⟩, n, 0)',
      'from⟨?a⟩() = (a, from⟨a + 1⟩)',
      'sum(?g, ?i, ?acc) =',
      '  if i == 0 then acc',
      '  else let p = g() in sum(p.1, i - 1, acc + p.0)',
    ].join('\n'), tS - 0.35, { stagger: 0.003, byLine: 0.05 });
    // "It can become a plain counting loop."
    const tC = cue('counter');
    const by0 = y3 + 5 * lh + 14, by1 = by0 + 64;
    const down2 = arrow(tl, svg, RAIL + 18, by0, RAIL + 18, by1, { stroke: C.dim, width: 3, head: 11 });
    drawArrow(tl, down2, tC - 0.4, 0.45);
    const becomes2 = label(root, RAIL + 56, by0 + 18, 'becomes');
    fadeIn(tl, becomes2, tC - 0.3, 0.5, 8);
    const y4 = by1 + 18;
    const cnt = new Code(tl, root, RAIL, y4, S);
    cnt.show('main(?n) = sum(1, n, 0)\n  where sum(?a, ?i, ?acc) =\n    if i == 0 then acc else sum({a1|a} {a2|+} {a3|1}, i - 1, acc + a)', tC - 0.15, { stagger: 0.003, byLine: 0.05 });
    // "a plain counting loop"
    cnt.mark(['a1', 'a2', 'a3'], C.dim, 20.2, { fill: 0.08, out: 21.7, pad: 7 });
    // "This film is about one analysis that finds both"
    const tO = cue('one'), tA = cue('and');
    // everything dims but the counter's head, so that the pair is easy to recognise when the film comes back to it
    for (const e of [st.root, down2, down2._head, becomes2]) tl.to(e, { o: 0.45 }, tO - 0.3, 0.5);
    cnt.fade(t => !(t.line === 1 && t.text !== 'where' && t.text !== '='), 0.45, tO - 0.3, 0.5);
    const ky = y4 + 3 * lh + 52;
    const phrase = serif(root, RAIL, ky, 'One analysis finds both.', 60);
    fadeIn(tl, phrase, tO - 0.15, 0.8, 22);
    // "with no inlining, and no rule about streams"
    const ly = ky + 104;
    const n1 = label(root, RAIL, ly, 'no inlining');
    const n2 = label(root, RAIL + labelW('no inlining') + 64, ly, 'no rule about streams');
    fadeIn(tl, n1, tA + 0.1, 0.5, 10); fadeIn(tl, n2, 26.3, 0.5, 10);
  });

  // ============================================ cool_same ======================================================
  scene('cool_same', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 50, top = 310;
    tag(tl, root, top, cue('notice') - 0.2);
    // three clause heads, each with its optimization's name under it
    const hy = top + 90, xs = [RAIL, 655, 1270];
    const heads = [
      'loop(?i, {p|1|p})',
      'loop(?i, ?a, {p|a|o})',
      'loop(?i, {p|(|p}{q1|?s}{q2|,} {q3|u|o}{q4|)|p})',
    ];
    const names = ['Constant propagation', 'Value numbering', 'Unboxing'];
    const at = [2.6, 4.15, 5.35];
    const codes = heads.map((h, i) => new Code(tl, root, xs[i], hy, S).show(h, at[i], { stagger: 0.01 }));
    names.forEach((n, i) => fadeIn(tl, serif(root, xs[i], hy + codes[i].lh + 4, n, 44), at[i] + 0.15, 0.7, 14));
    // the four steps, each at its word, with arrows between them
    const sy = hy + codes[0].lh + 4 + 150;
    const steps = ['substitute', 'rewrite', 'check', 'delete the match'], st = [7.65, 9.1, 9.95, 11.1];
    const gap = 110;
    let x = RAIL;
    steps.forEach((s, i) => {
      const e = label(root, x, sy, s, { color: C.ink, fontSize: '28px' });
      const w = labelW(s, 28);
      if (i > 0) {
        const a = arrow(tl, svg, x - gap + 24, sy + 17, x - 24, sy + 17, { stroke: C.dim, width: 3, head: 10 });
        drawArrow(tl, a, st[i] - 0.25, 0.35);
      }
      fadeIn(tl, e, st[i], 0.5, 10);
      x += w + gap;
    });
    // "Only the pattern was different."
    const tO = cue('only');
    codes[0].mark(['p'], C.pat, tO - 0.1, { pad: 6 });
    codes[1].mark(['p'], C.outer, tO + 0.1, { pad: 6 });
    codes[2].mark(['p', 'q1', 'q2', 'q3', 'q4'], C.pat, tO + 0.3, { pad: 6 });
    // "That economy is what we find elegant about the idea."
    const kp = serif(root, RAIL, sy + 110, 'One idea. Only the pattern changes.', 56, { color: C.ink });
    fadeIn(tl, kp, cue('elegant') - 0.2, 0.8, 22);
  });

  // ============================================ cool_rounds ====================================================
  scene('cool_rounds', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 56, top = 330;
    tag(tl, root, top, cue('notice') - 0.2);
    // the most specific pattern
    const py = top + 70;
    const p = new Code(tl, root, RAIL, py, S), cw = p.cw, lh = p.lh;
    p.show('loop(?i, {u1|u|o}, {k|1|p}, {so|Some|p}{a|(|p}{b|(|p}?s, {u2|u|o}{c|)|p}{d|)|p})', cue('four') - 0.2, { stagger: 0.01 });
    // four facts, each on a tick under its part, in the order of the pattern: three level in one row, and the
    // constant's on a longer tick in a second row (its tick runs between the first row's labels)
    const ty0 = py + lh - 4, row1 = ty0 + 40, row2 = row1 + 58;
    const colX = c => RAIL + c * cw;
    const tU1 = colX(9.5), tK = colX(12.5), tS = colX(15) + 8, tU2 = colX(25.5);
    const wI = labelW('invariant'), wC = labelW('constant · dead branch'), wB = labelW('unboxed'), wF = labelW('invariant field');
    const parts = [
      { tx: tU1, ly: row1, text: 'invariant', x: Math.min(tU1 - wI / 2, tK - 26 - wI) },
      { tx: tK, ly: row2, text: 'constant · dead branch', x: tK - wC / 2 },
      { tx: tS, ly: row1, text: 'unboxed', x: Math.max(tS - wB / 2, tK + 26) },
      { tx: tU2, ly: row1, text: 'invariant field', x: Math.min(tU2 - wF / 2, tU2 + 40 - wF) },
    ];
    const ta = [2.65, 3.35, 4.05, 4.75];
    parts.forEach((q, i) => {
      // Some(( has a short bracket under it, its tick from the bracket's left end
      const d = i === 2 ? `M ${colX(21) - 6} ${ty0} L ${q.tx} ${ty0} L ${q.tx} ${q.ly + 2}` : `M ${q.tx} ${ty0} L ${q.tx} ${q.ly + 2}`;
      const tk = path(tl, svg, d, { stroke: alpha(C.dim, 0.6), width: 2.5 });
      tl.to(tk, { draw: 1 }, ta[i] - 0.15, 0.35, E.io);
      const e = label(root, q.x, q.ly + 8, q.text);
      fadeIn(tl, e, ta[i], 0.5, 8);
    });
    // "in two rounds, by one rule"
    const cy = row2 + 100;
    const r1 = chip(root, RAIL, cy, 'ROUND 1'), r2 = chip(root, RAIL + 254, cy, 'ROUND 2');
    fadeIn(tl, r1, 7.45, 0.5, 10); fadeIn(tl, r2, 7.85, 0.5, 10);
    const rule = label(root, RAIL + 254 + 230 + 56, cy + 15, 'one rule', { color: C.ink });
    fadeIn(tl, rule, cue('rule') - 0.1, 0.5, 10);
    // "Compilers usually have a separate analysis for each kind of fact, and run them one after another."
    const tU = cue('usual'), UX = 1330;
    const uh = label(root, UX, py + 6, 'usually');
    fadeIn(tl, uh, tU - 0.1, 0.5, 10);
    const un = ['Constant propagation', 'Dead-branch elimination', 'Loop-invariant detection', 'Unboxing'];
    const ny = py + 62;
    un.forEach((n, i) => fadeIn(tl, serif(root, UX, ny + i * 60, n, 40, { color: C.dim }), tU + 0.1 + i * 0.15, 0.6, 12));
    const l1 = label(root, UX, ny + 4 * 60 + 30, 'one analysis each,');
    fadeIn(tl, l1, 11.85, 0.5, 8);
    const l2 = label(root, UX, ny + 4 * 60 + 72, 'run one after another');
    fadeIn(tl, l2, 14.45, 0.5, 8);
    // one after another: a straight arrow down the names
    const down = arrow(tl, svg, UX - 28, ny + 12, UX - 28, ny + 4 * 60 - 12, { stroke: C.dim, width: 3, head: 11 });
    drawArrow(tl, down, 14.5, 0.9);
  });

  // ============================================ cool_best ======================================================
  scene('cool_best', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 72, top = 320;
    tag(tl, root, top, cue('so') - 0.2, 'the surprise');
    const RX = 1180, hy = top + 92, cy = hy + 46;
    const la = label(root, RAIL, hy, 'repair in place'), lb = label(root, RX, hy, 'start again');
    fadeIn(tl, la, 0.4, 0.5, 10); fadeIn(tl, lb, 0.65, 0.5, 10);
    const ca = new Code(tl, root, RAIL, cy, S).show('{g|g}{p|(}{b|?b}{q|)}', 0.5);
    const cb = new Code(tl, root, RX, cy, S).show('{g|g}{p|(}{x|x|o}{q|)}', 0.75);
    const lh = ca.lh, cw = ca.cw;
    // "So the textbook method is not optimal for patterns, and in some programs its answer depends on the order"
    ca.mark(['g', 'p', 'b', 'q'], C.dim, 0.8, { fill: 0.08, out: cue('yet') - 0.2, pad: 12 });
    const ly = cy + lh + 24;
    const a1 = label(root, RAIL, ly, 'correct, not the best'), a2 = label(root, RAIL, ly + 50, 'can depend on the order');
    fadeIn(tl, a1, 2.25, 0.5, 8); fadeIn(tl, a2, cue('order') - 0.1, 0.5, 8);
    // "Yet a most specific answer exists, and the restarts find it in any order."
    const tY = cue('yet');
    for (const e of [la, a1, a2, ca.root]) tl.to(e, { o: 0.55 }, tY - 0.2, 0.5);
    cb.mark(['g', 'p', 'x', 'q'], C.dim, tY - 0.1, { fill: 0.08, pad: 12 });
    okDisc(tl, root, svg, RX + 4 * cw + 70, cy + lh / 2, 8.85);
    const b1 = label(root, RX, ly, 'the most specific'), b2 = label(root, RX, ly + 50, 'in any order');
    fadeIn(tl, b1, 8.9, 0.5, 8); fadeIn(tl, b2, 12.35, 0.5, 8);
    // "That is a theorem, checked in Lean."
    const lean = label(root, RAIL, ly + 170, 'theorem 5.3 · checked in lean', { color: C.ink });
    fadeIn(tl, lean, cue('lean') - 0.1, 0.5, 10);
  });

  // ============================================ cool_stream ====================================================
  scene('cool_stream', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 50, top = 300;
    tag(tl, root, top, cue('look') - 0.2);
    const hy = top + 70;
    const a = new Code(tl, root, RAIL, hy, S), cw = a.cw, lh = a.lh;
    a.show('sum(from⟨1⟩, n, 0)', cue('stream') - 0.2, { stagger: 0.01 });
    const ax0 = RAIL + 18 * cw + 40, ax1 = ax0 + 130, RX = ax1 + 40;
    const ar = arrow(tl, svg, ax0, hy + lh / 2, ax1, hy + lh / 2, { stroke: C.dim, width: 3, head: 12 });
    drawArrow(tl, ar, 6.4, 0.5);
    const b = new Code(tl, root, RX, hy, S);
    b.show('sum(1, n, 0)', 6.7, { stagger: 0.01 });
    const ly = hy + lh + 14;
    const la = label(root, RAIL, ly, 'a stream of closures'), lb = label(root, RX, ly, 'a counter');
    fadeIn(tl, la, 3.3, 0.5, 8); fadeIn(tl, lb, 7.5, 0.5, 8);
    // "The analysis has no rule about streams, and no fusion framework."
    const ny = ly + 100;
    const t1 = 'a rule about streams', t2 = 'a fusion framework', x2 = RAIL + labelW(t1) + 80;
    const n1 = label(root, RAIL, ny, t1, { color: C.code }), n2 = label(root, x2, ny, t2, { color: C.code });
    fadeIn(tl, n1, 9.2, 0.5, 8); fadeIn(tl, n2, 11.1, 0.5, 8);
    strikeLabel(tl, root, n1, RAIL, ny, t1, 9.9);
    strikeLabel(tl, root, n2, x2, ny, t2, 12.1);
    // "All it did was join two closures of the same block, and keep what they share."
    const tJ = cue('join');
    for (const e of [a.root, b.root, ar, ar._head, la, lb]) tl.to(e, { o: 0.55 }, tJ - 0.2, 0.5);
    const jy1 = ny + 90, jy2 = jy1 + 120, jyr = (jy1 + jy2) / 2, jr = 760;
    const j1 = new Code(tl, root, RAIL, jy1, S).show('from⟨1⟩', 13.5, { stagger: 0.01 });
    const j2 = new Code(tl, root, RAIL, jy2, S).show('from⟨2⟩', 13.7, { stagger: 0.01 });
    const jEnd = RAIL + 7 * cw + 30;
    const a1 = arrow(tl, svg, jEnd, jy1 + lh * 0.55, jr - 30, jyr + lh * 0.42, { stroke: C.dim, width: 3, head: 10 });
    const a2 = arrow(tl, svg, jEnd, jy2 + lh * 0.45, jr - 30, jyr + lh * 0.58, { stroke: C.dim, width: 3, head: 10 });
    drawArrow(tl, a1, 14.1, 0.5); drawArrow(tl, a2, 14.2, 0.5);
    const jc = new Code(tl, root, jr, jyr, S).show('{f|from|p}{l|⟨|p}{c|?a}{r|⟩|p}', 14.6, { stagger: 0.01 });
    const jl = label(root, jr + 9 * cw + 50, jyr + (lh - 31) / 2, 'the join of two closures');
    fadeIn(tl, jl, 14.8, 0.5, 8);
    // "and keep what they share"
    jc.mark(['f'], C.pat, 16.0, { pad: 6 });
  });

  // ============================================ cool_dial ======================================================
  scene('cool_dial', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const top = 350, NS = 56;
    tag(tl, root, top, cue('point') - 0.2);
    // three tools, each usually a separate one
    const names = ['A specializer', 'An inliner', 'A partial evaluator'], cx = [720, 1120, 1530], at = [2.6, 3.72, 4.68];
    const uy = top + 80, ny = uy + 92, lineY = ny + 130;
    names.forEach((n, i) => {
      const w = serifW(n, NS);
      fadeIn(tl, serif(root, cx[i] - w / 2, ny, n, NS), at[i], 0.7, 16);
      const u1 = 'usually a', u2 = 'separate tool';
      const e1 = label(root, cx[i] - labelW(u1) / 2, uy, u1), e2 = label(root, cx[i] - labelW(u2) / 2, uy + 36, u2);
      for (const e of [e1, e2]) { fadeIn(tl, e, 6.85 + i * 0.12, 0.5, 8); fadeOut(tl, e, cue('param') - 0.4, 0.35); }
    });
    // "Here, each is one setting of a parameter": a line with a stop under each name, and one at the left
    const tP = cue('param'), x0 = 290, stops = [x0, ...cx];
    const df1 = 'a dataflow', df2 = 'analysis';
    const d1 = label(root, x0 - labelW(df1) / 2, ny + 4, df1), d2 = label(root, x0 - labelW(df2) / 2, ny + 40, df2);
    fadeIn(tl, d1, tP + 0.1, 0.5, 8); fadeIn(tl, d2, tP + 0.15, 0.5, 8);
    const line = path(tl, svg, `M ${x0 - 50} ${lineY} L ${cx[2] + 50} ${lineY}`, { stroke: C.faint, width: 3 });
    tl.to(line, { draw: 1 }, tP - 0.2, 0.8, E.io);
    const dots = stops.map((x, i) => {
      const s = el(svg, 'circle'); s.setAttribute('cx', x); s.setAttribute('cy', lineY); s.setAttribute('r', 8);
      s.style.fill = C.bg; s.style.stroke = C.dim; s.setAttribute('stroke-width', 3);
      tl.set(s, { o: 0 }, 0); tl.to(s, { o: 1 }, tP - 0.1 + i * 0.12, 0.4);
      return s;
    });
    // the marker: a ring that slides from stop to stop
    const mk = el(svg, 'circle'); mk.setAttribute('cx', 0); mk.setAttribute('cy', 0); mk.setAttribute('r', 17);
    mk.style.fill = 'none'; mk.style.stroke = C.ink; mk.setAttribute('stroke-width', 3.5);
    mk._init = { x: x0, y: lineY };
    tl.set(mk, { x: x0, y: lineY, o: 0 }, 0);
    tl.to(mk, { o: 1 }, tP - 0.1, 0.4);
    const visit = [tP - 0.1, 11.0, 11.55, 12.1];
    stops.forEach((x, i) => {
      if (i > 0) { tl.to(mk, { x }, visit[i] - 0.45, 0.55, E.io); tl.to(dots[i - 1], { fill: C.bg, stroke: C.dim }, visit[i] - 0.4, 0.3); }
      tl.to(dots[i], { fill: C.ink, stroke: C.ink }, visit[i], 0.3);
    });
    // "on the analysis we already had"
    const same = label(root, RAIL, lineY + 56, 'one parameter of the same analysis', { color: C.ink });
    fadeIn(tl, same, cue('same') - 0.1, 0.5, 10);
  });
})();

// ==== src/scenes/s14_more.js ====
// Two more examples of a specialization policy. regex: the last stop of the dial, a version per value of a marked
// parameter, turns a matcher by derivatives into its automaton. mono: in the compiler of the first setting, a policy
// on type arguments is monomorphization.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // the width of a text in a given style, measured off the stage
  function textWidth(text, style) {
    const m = document.createElement('span');
    Object.assign(m.style, { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' }, style);
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return w;
  }
  const CAPS = { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em' };
  const MONO = { fontFamily: 'var(--mono)', fontSize: '30px', fontWeight: 500, letterSpacing: '0', fontVariantLigatures: 'none' };
  // a small-caps label with a piece of code in it, not upper-cased: parts are strings, and [text] for code
  function codeLabel(parent, x, y, parts, { color = C.dim } = {}) {
    const e = label(parent, x, y, undefined, Object.assign({}, CAPS, { textTransform: 'none', color }));
    let w = 0;
    for (const p of parts) {
      if (Array.isArray(p)) { el(e, 'span', Object.assign({ position: 'static', color: C.code }, MONO), p[0]); w += textWidth(p[0], MONO); }
      else { el(e, 'span', { position: 'static', textTransform: 'uppercase' }, p); w += textWidth(p.toUpperCase(), CAPS); }
    }
    return { e, w };
  }
  // tokens of one line between the columns of a piece of its text
  function within(src, li, piece) {
    const line = src.split('\n')[li].replace(/\{[^}|]*\|([^}|]*)(?:\|[^}]*)?\}/g, '$1');
    const i = line.indexOf(piece), c0 = [...line.slice(0, i)].length, c1 = c0 + [...piece].length;
    return t => t.line === li && t.col >= c0 && t.col < c1;
  }
  function look(code, sel, at, out, pad = 8) { return code.mark(sel, C.dim, at, { fill: 0.08, pad, out }); }

  // ===== regex: a matcher by derivatives, specialized on its expression, is the automaton =====================
  scene('regex', ({ tl, root, cue }) => {
    const tLast = cue('last'), tMatch = cue('match'), tDeriv = cue('deriv'), tMark = cue('mark'), tVers = cue('versions');
    const tThree = cue('three'), tAway = cue('away'), tDfa = cue('dfa');
    const S = 40, Y = 410;

    // the dial's last stop, as it was named there
    const stop = label(root, RAIL, 250, 'a version per value of a marked parameter');
    fadeIn(tl, stop, tLast - 0.2, 0.6, 10);

    // ---- the matcher ------------------------------------------------------------------------------------------
    const SRC =
      'match({r|?r}, {s|?s}) = case s of\n' +
      '  Nil → nullable(r)\n' +
      '  Cons(?c, ?t) → match(deriv(r, c), t)\n' +
      'main(?s) = match(Star(Seq(Chr(a), Chr(b))), s)';
    const code = new Code(tl, root, RAIL, Y, S), lh = code.lh;
    code.show(SRC, tMatch - 0.25, { stagger: 0.004, byLine: 0.07 });
    // "a regular expression and a string"
    code.mark(['r'], C.dim, 4.8, { fill: 0.08, pad: 7, out: 5.95 });
    code.mark(['s'], C.dim, 5.95, { fill: 0.08, pad: 7, out: 7.0 });
    const mainEnd = code.x + 47 * code.cw;
    const expr = codeLabel(root, mainEnd + 48, Y + 3 * lh + (lh - 32) / 2, ['the expression  ', ['(ab)*']]);
    fadeIn(tl, expr.e, 5.2, 0.6, 8);
    // "it takes the derivative of the expression"
    const derivSel = within(SRC, 2, 'deriv(r, c)'), nullSel = within(SRC, 1, 'nullable(r)');
    look(code, derivSel, 8.75, tMark - 0.3);
    // "mark the expression as the parameter to specialize on"
    code.mark(['r'], C.pat, tMark - 0.1, { pad: 7 });
    const rr = code.rect(['r']);
    const spec = label(root, rr.x - 8, Y - 50, 'specialize on this', { color: C.ink });
    fadeIn(tl, spec, tMark + 0.2, 0.6, 10);

    // ---- the versions: one for each expression the matcher is called with ------------------------------------
    const CY = 810, CHW = 200, CHH = 70, GAP = 36;
    const vl = label(root, RAIL, CY - 52, 'versions');
    fadeIn(tl, vl, tVers + 0.9, 0.5, 8);
    const EXPRS = ['(ab)*', 'b(ab)*', '∅'];
    const tChip = [16.45, 17.6, 18.45];                    // "version", "expression", "called"
    const chips = EXPRS.map((t, i) => {
      const x = RAIL + i * (CHW + GAP);
      const c = box(root, x, CY, {
        width: CHW + 'px', height: CHH + 'px', borderRadius: '14px', background: alpha(C.panel, 0.95), boxShadow: `inset 0 0 0 1.5px ${C.line}`,
        display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--mono)', fontSize: S + 'px', fontWeight: 500,
        color: C.ink, whiteSpace: 'pre', fontVariantLigatures: 'none', transformOrigin: 'left center',
      }, t);
      tl.set(c, { o: 0, y: 16 }, 0); tl.to(c, { o: 1, y: 0 }, tChip[i] - 0.15, 0.6, E.out5);
      return { c, x };
    });
    // "there are three"
    chips.forEach((ch, i) => { tl.to(ch.c, { bg: alpha(C.dim, 0.2) }, tThree - 0.1 + i * 0.12, 0.3); tl.to(ch.c, { bg: alpha(C.panel, 0.95) }, tThree + 0.6 + i * 0.12, 0.5); });

    // ---- "in each of them, the derivative is computed away" ----------------------------------------------------
    code.fade(t => true, 0.5, tAway - 0.1, 0.5);
    for (const e of [expr.e, spec]) tl.to(e, { o: 0.45 }, tAway - 0.1, 0.5);
    code.strike(derivSel, 21.95, { dur: 0.45 });
    code.strike(nullSel, 22.4, { dur: 0.45 });

    // ---- the automaton ---------------------------------------------------------------------------------------
    const tGo = tDfa - 0.45;
    code.hide(tGo, 0.4); fadeOut(tl, expr.e, tGo, 0.4); fadeOut(tl, spec, tGo, 0.4); fadeOut(tl, vl, tGo, 0.4);
    const OS = 34, OY = 500, SC = 0.7, OX = RAIL + Math.round(CHW * SC) + 24;
    const out = new Code(tl, root, OX, OY, OS), olh = out.lh;
    out.show(
      'main(?s) = {a1|m₁|f}(s)\n' +
      '{h1|m₁|f}(?s) = case s of Nil → 1 | Cons(a, ?t) → {c12|m₂|f}(t) | Cons(b, ?t) → {c10|m₀|f}(t)\n' +
      '{h2|m₂|f}(?s) = case s of Nil → 0 | Cons(a, ?t) → {c20|m₀|f}(t) | Cons(b, ?t) → {c21|m₁|f}(t)\n' +
      '{h0|m₀|f}(?s) = case s of Nil → 0 | Cons(a, ?t) → {c00|m₀|f}(t) | Cons(b, ?t) → {c01|m₀|f}(t)', tDfa - 0.2, { stagger: 0.003, byLine: 0.08 });
    // each version's chip goes to the start of its state's line
    chips.forEach((ch, i) => {
      const cy = OY + (i + 1) * olh + olh / 2;
      tl.to(ch.c, { x: RAIL - ch.x, y: cy - CHH / 2 - CY, s: SC }, tDfa - 0.55 + i * 0.05, 0.75, E.io);
    });
    const auto = label(root, RAIL, OY + 4 * olh + 46, 'the automaton: one loop per state', { color: C.ink });
    fadeIn(tl, auto, 25.35, 0.6, 10);
    // "one loop for each state": the states' heads, one after another
    ['h1', 'h2', 'h0'].forEach((h, i) => look(out, [h], 26.55 + i * 0.45, i < 2 ? 27.0 + i * 0.45 : 28.4, 6));
  });

  // ===== mono: a policy on type arguments is monomorphization ===============================================
  // the three settings of the chapter, as s11_practice.js has them; the first is bright
  const HEADS = ["1 · A compiler's only optimizer", '2 · Ports to mature optimizers', '3 · An experiment'];
  function headings(tl, root, lit) {
    return HEADS.map((t, i) => {
      const h = box(root, [160, 760, 1360][i], 190, { whiteSpace: 'pre', fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase', color: C.dim }, t);
      const on = i === lit;
      tl.set(h, { o: 0, color: on ? C.ink : C.dim }, 0);
      tl.to(h, { o: on ? 1 : 0.55 }, 0, 0.4, E.out5);
      return h;
    });
  }
  // a block: a panel with its name in the code font
  function blockBox(parent, x, cy, w, h, name, S) {
    return box(parent, x, cy - h / 2, {
      width: w + 'px', height: h + 'px', borderRadius: '16px', background: alpha(C.panel, 0.92), boxShadow: `inset 0 0 0 1.5px ${C.line}`,
      display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--mono)', fontSize: S + 'px', fontWeight: 560,
      color: C.ink, whiteSpace: 'pre', fontVariantLigatures: 'none',
    }, name);
  }

  scene('mono', ({ tl, root, cue }) => {
    const tMono = cue('mono'), tTypes = cue('types'), tPol = cue('policy'), tNo = cue('nopass');
    const svg = svgLayer(root);
    headings(tl, root, 0);
    const name = serif(root, RAIL, 290, 'Monomorphization', 60);
    fadeIn(tl, name, 4.1, 0.7, 20);                        // "monomorphization"

    // ---- the generic block's head; its type is a parameter like any other ------------------------------------
    const S = 44, CY = 680, BH = 92, BS = 40;
    const head = new Code(tl, root, RAIL, CY - 36, S), lh = head.lh;
    head.show('length({T|?T}, ?xs)', tTypes - 0.25, { stagger: 0.02 });
    head.mark(['T'], C.bind, tTypes + 0.15, { pad: 7, out: tPol - 0.2 });
    const ord = label(root, RAIL, CY - 36 + lh + 18, 'a type is an ordinary value');
    fadeIn(tl, ord, 6.75, 0.6, 10);                        // "ordinary values"
    fadeOut(tl, ord, tPol - 0.25, 0.35);

    // ---- the policy: a caller passes two types; the block is reached with each ------------------------------
    const sx = RAIL, sw = 210, fx = 760, fw = 370, patX = 1180;
    const mainB = blockBox(root, sx, CY, sw, BH, 'main', BS), genB = blockBox(root, fx, CY, fw, BH, 'length', BS);
    // the head moves beside its block, as the block's pattern
    head.move(patX - RAIL, (CY - lh / 2) - (CY - 36), tPol - 0.15, 0.8);
    fadeIn(tl, mainB, tPol + 0.15, 0.6, 14); fadeIn(tl, genB, tPol + 0.35, 0.6, 14);
    tl.to(name, { o: 0.55 }, tPol, 0.6);
    const ax0 = sx + sw + 12, ax1 = fx - 14;
    const a1 = arrow(tl, svg, ax0, CY - 16, ax1, CY - 16, { bend: -56, stroke: C.dim, width: 3, head: 12 });
    const a2 = arrow(tl, svg, ax0, CY + 16, ax1, CY + 16, { bend: 56, stroke: C.dim, width: 3, head: 12 });
    const tArg = 12.3;                                     // "type arguments"
    drawArrow(tl, a1, tArg, 0.55); drawArrow(tl, a2, tArg + 0.3, 0.55);
    const mx = (ax0 + ax1) / 2;
    const pw1 = textWidth('PASSES  ', CAPS) + textWidth('Int', MONO), pw2 = textWidth('PASSES  ', CAPS) + textWidth('Float', MONO);
    const pass1 = codeLabel(root, mx - pw1 / 2, CY - 16 - 28 - 46, ['passes  ', ['Int']]);
    const pass2 = codeLabel(root, mx - pw2 / 2, CY + 16 + 28 + 12, ['passes  ', ['Float']]);
    fadeIn(tl, pass1.e, tArg + 0.4, 0.5, 8); fadeIn(tl, pass2.e, tArg + 0.7, 0.5, 8);
    // "a generic function"
    head.mark(t => true, C.dim, 13.95, { fill: 0.08, pad: 8, out: 15.0 });

    // ---- a version for each type ------------------------------------------------------------------------------
    const tSplit = 15.1;                                   // "a version"
    const V = 140, vy = [CY - V, CY + V];
    const vB = ['length[Int]', 'length[Float]'].map((nm, i) => {
      const b = blockBox(root, fx, CY, fw, BH, nm, BS);
      tl.set(b, { o: 0 }, 0); tl.to(b, { o: 1 }, tSplit, 0.3); tl.to(b, { y: vy[i] - CY }, tSplit, 0.8, E.io);
      return b;
    });
    tl.to(genB, { o: 0 }, tSplit, 0.25);
    head.hide(tSplit - 0.1, 0.35);
    hideArrow(tl, a1, tSplit - 0.1, 0.25); hideArrow(tl, a2, tSplit - 0.1, 0.25);
    const va = [arrow(tl, svg, ax0, CY - 16, ax1, vy[0] + 10, { stroke: C.dim, width: 3, head: 12 }),
                arrow(tl, svg, ax0, CY + 16, ax1, vy[1] - 10, { stroke: C.dim, width: 3, head: 12 })];
    drawArrow(tl, va[0], tSplit + 0.45, 0.5); drawArrow(tl, va[1], tSplit + 0.55, 0.5);
    tl.to(pass1.e, { x: -10, y: -84 }, tSplit, 0.8, E.io); tl.to(pass2.e, { x: -10, y: 84 }, tSplit, 0.8, E.io);
    // "for each type it is used at": each version's pattern
    const vp = [new Code(tl, root, patX, vy[0] - lh / 2, S), new Code(tl, root, patX, vy[1] - lh / 2, S)];
    vp[0].show('length({k|Int|p}, ?xs)', 15.55, { stagger: 0.01 });
    vp[1].show('length({k|Float|p}, ?xs)', 15.9, { stagger: 0.01 });

    // ---- "there is no separate monomorphization pass" ---------------------------------------------------------
    const no = label(root, RAIL, 960, 'no separate monomorphization pass', { color: C.ink });
    fadeIn(tl, no, tNo - 0.15, 0.6, 12);
  });
})();

// ==== src/scenes/s15_roadmap.js ====
// After the cold open and before the title: what the film is going to show, as six rows that arrive at their
// words. Each row is a stop of the film, with one small piece of evidence from it.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  scene('roadmap', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const head = label(root, RAIL, 190, 'in this film', { color: C.ink });
    fadeIn(tl, head, cue('coming') - 0.1, 0.5, 10);
    const top = 280, step = 112, NX = RAIL, TX = RAIL + 70, EX = 930, S = 40;
    const rows = [
      { cue: 'idea', title: 'The idea, on three loops' },
      { cue: 'find', title: 'How the facts are found' },
      { cue: 'surprise', title: 'A surprise' },
      { cue: 'clo', title: 'Functions and closures' },
      { cue: 'dial', title: 'A dial' },
      { cue: 'end', title: 'Proofs, and practice' },
    ];
    const els = rows.map((r, i) => {
      const y = top + i * step, at = cue(r.cue);
      const num = label(root, NX, y + 20, String(i + 1));
      const t = serif(root, TX, y, r.title, 52);
      fadeIn(tl, num, at - 0.15, 0.5, 12); fadeIn(tl, t, at - 0.1, 0.6, 16);
      return { y, at, parts: [num, t] };
    });
    const ev = (i, e, at, dy = 16) => { fadeIn(tl, e, at, 0.5, dy); els[i].parts.push(e); return e; };
    const code = (i, src, at, dx = 0) => {
      const c = new Code(tl, root, EX + dx, els[i].y - 2, S); c.show(src, at, { stagger: 0.01 }); els[i].parts.push(c.root); return c;
    };
    // 1 the idea: a pattern in place of a parameter
    code(0, 'loop(?i, {one|1|p})', 3.6);
    // 2 how the facts are found: assume, refute, repeat
    ev(1, label(root, EX, els[1].y + 18, 'assume  ·  refute  ·  repeat', { color: C.ink }), 6.3);
    // 3 a surprise: the textbook way is not good enough
    const c3 = code(2, 'g(?b)', 8.9);
    const not = ev(2, label(root, EX + 6 * c3.cw + 30, els[2].y + 18, 'textbook: correct, not the best'), 9.6);
    // 4 functions and closures: the stream becomes a counter
    const c4 = code(3, 'sum(from⟨1⟩, n, 0)', 14.2);
    const ax = EX + 18 * c4.cw + 22, ay = els[3].y + c4.lh / 2;
    const arr = arrow(tl, svg, ax, ay, ax + 70, ay, { stroke: C.dim, width: 3 }); drawArrow(tl, arr, 15.1, 0.35);
    els[3].parts.push(arr, arr._head);
    code(3, 'sum(1, n, 0)', 15.5, 18 * c4.cw + 114);
    // 5 a dial: a specializer, an inliner, a partial evaluator
    [['specializer', 0, 19.5], ['inliner', 290, 20.8], ['partial evaluator', 500, 22.0]].forEach(([n, dx, at]) => ev(4, label(root, EX + dx, els[4].y + 18, n, { color: C.ink }), at));
    // 6 what is proved, and what it does
    ev(5, label(root, EX, els[5].y + 18, 'proved in Lean', { color: C.ink }), 25.2);
    ev(5, label(root, EX + 360, els[5].y + 18, 'in practice, briefly', { color: C.ink }), 26.9);
    // the row being read is bright; the ones before it step back
    els.forEach((r, i) => { if (i < 5) for (const e of r.parts) tl.to(e, { o: 0.6 }, els[i + 1].at - 0.25, 0.5); });
  });
})();

// ==== src/scenes/s16_open.js ====
// Open problems: six of them, as a numbered list on the rail that builds up, and beside it one small panel per
// problem that shows exactly what is missing. The panel is replaced when the next problem starts.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160;

  // the width of a line of text, measured off-stage
  function measure(text, style) {
    const m = document.createElement('span');
    Object.assign(m.style, { position: 'absolute', visibility: 'hidden', whiteSpace: 'pre' }, style);
    m.textContent = text; document.body.appendChild(m);
    const w = m.getBoundingClientRect().width; m.remove();
    return w;
  }
  const LABEL = { fontFamily: 'var(--sans)', fontSize: '26px', fontWeight: 560, letterSpacing: '0.16em', textTransform: 'uppercase' };
  const labelW = text => measure(text, LABEL) - 26 * 0.16;
  const serifW = (text, size) => measure(text, { fontFamily: 'var(--serif)', fontSize: size + 'px', letterSpacing: '-0.005em' });

  scene(['open1', 'open2', 'open3', 'open4', 'open5', 'open6'], ({ tl, root, cue, seg }) => {
    const svg = svgLayer(root);
    const at = (s, t) => seg(s) + t;              // a word's time within its segment
    const Q = (s, n) => cue(s + '.' + n);
    const S = 40, PX = 860, P0 = 330, OPENY = 770;

    // a label with words in the code font: parts are strings, or [code] for a piece of code
    function mlabel(x, y, parts, style = {}) {
      const e = label(root, x, y, '', style);
      for (const p of parts) {
        const s = document.createElement('span');
        if (Array.isArray(p)) Object.assign(s.style, { fontFamily: 'var(--mono)', textTransform: 'none', letterSpacing: '0', fontSize: '34px', lineHeight: '26px', fontWeight: 450, color: C.code });
        s.textContent = Array.isArray(p) ? p[0] : p;
        e.appendChild(s);
      }
      return e;
    }
    // what each panel is made of, so that it can leave as one
    const panels = [[], [], [], [], [], []];
    const put = (k, ...es) => { panels[k].push(...es); return es[0]; };
    const putArrow = (k, a) => { panels[k].push(a, a._head); return a; };
    const putCode = (k, c) => { panels[k].push(c.root); return c; };
    const open = (k, text, t) => put(k, fadeIn(tl, label(root, PX, OPENY, text, { color: C.ink }), t - 0.15, 0.6, 12));

    // ---- the list --------------------------------------------------------------------------------------------
    const head = label(root, RAIL, 212, 'six open problems', { color: C.ink });
    fadeIn(tl, head, Q('open1', 'open') - 0.1, 0.6, 10);   // after the chapter card has gone
    const top = 290, step = 100;
    const rowCues = [Q('open1', 'tests'), Q('open2', 'heap'), Q('open3', 'sets'), Q('open4', 'pol'), Q('open5', 'inc'), Q('open6', 'prod')];
    const titles = ['Facts from tests', 'Values in the heap', 'Sets of closures', 'A theory of policies', 'Restarting less', 'A production compiler'];
    const rows = titles.map((t, i) => {
      const y = top + i * step, a = rowCues[i];
      const num = label(root, RAIL, y + 16, String(i + 1));
      const tt = serif(root, RAIL + 56, y, t, 48);
      fadeIn(tl, num, a - 0.2, 0.5, 12); fadeIn(tl, tt, a - 0.15, 0.6, 16);
      return [num, tt];
    });
    // the row being read is bright; the ones before it step back
    rows.forEach((r, i) => { if (i < 5) for (const e of r) tl.to(e, { o: 0.6 }, rowCues[i + 1] - 0.3, 0.5); });
    // each panel leaves just before the next problem is named
    panels.forEach((p, k) => { p.leave = k < 5 ? rowCues[k + 1] - 0.55 : Q('open6', 'each') - 0.35; });

    // ==== 1 facts from tests ======================================================================================
    {
      const k = 0, ex = Q('open1', 'ex');
      const f = putCode(k, new Code(tl, root, PX, P0, S));
      f.show('f(?x) =\n  if x == 0 then g(x) else h(x)', ex - 0.2, { stagger: 0.008 });
      const lh = f.lh, cw = f.cw;
      // "Inside the true branch of this test, X is zero."
      f.mark(['x@1.1', '==@1.1', '0@1.1'], C.dim, at('open1', 12.85), { fill: 0.08, out: at('open1', 13.45), pad: 7 });
      f.mark(['x@1.2'], C.dim, at('open1', 13.45), { fill: 0.08, out: Q('open1', 'but') - 0.2, pad: 7 });
      const here = put(k, mlabel(PX + 17 * cw, P0 + 2 * lh + 2, ['here ', ['x'], ' is 0']));
      fadeIn(tl, here, at('open1', 13.55), 0.5, 10);
      tl.to(here, { o: 0.6 }, Q('open1', 'but') - 0.2, 0.4);
      // "But a pattern describes what calls pass": the pattern the analysis has for g
      const gy = P0 + 3.4 * lh;
      const g = putCode(k, new Code(tl, root, PX, gy, S));
      g.show('{g|g|f}{po|(}{a|?x}{pc|)}', Q('open1', 'but') - 0.15);
      const gl = put(k, mlabel(PX + 5 * cw + 44, gy + (lh - 31) / 2, ['the call passes ', ['x'], ', not 0']));
      fadeIn(tl, gl, Q('open1', 'but') + 0.15, 0.5, 10);
      // "Giving the branch a version that is passed what the test established"
      tl.to(gl, { o: 0, y: -10 }, at('open1', 21.4), 0.25, E.in);
      g.swap('{g|g|f}{po|(}{a|0|p}{pc|)}', at('open1', 21.6), { dur: 0.5 });
      const ver = put(k, label(root, PX + 5 * cw + 44, gy + (lh - 31) / 2, 'a version for the branch finds it'));
      fadeIn(tl, ver, at('open1', 21.75), 0.5, 10);
      f.mark(['x@1.1', '==@1.1', '0@1.1'], C.dim, at('open1', 23.25), { fill: 0.08, out: at('open1', 24.6), pad: 7 });
      open(k, 'open: a most specific answer there', Q('open1', 'missing'));
    }

    // ==== 2 values in the heap ====================================================================================
    {
      const k = 1, ex = Q('open2', 'ex');
      const w = putCode(k, new Code(tl, root, PX, P0, S));
      w.show('walk({xs|xs})', ex - 0.2);
      const cw = w.cw, lh = w.lh;
      const xc = PX + 6 * cw, by = P0 + lh + 70, bw = 120, bh = 90, gap = 90;
      const down = putArrow(k, arrow(tl, svg, xc, P0 + lh + 4, xc, by - 10, { stroke: C.dim, width: 3, head: 11 }));
      drawArrow(tl, down, ex + 0.25, 0.35);
      const cells = [];
      ['1', '2', '3'].forEach((v, i) => {
        const x = xc - bw / 2 + i * (bw + gap), t0 = ex + 0.5 + i * 0.18;
        const b = put(k, box(root, x, by, { width: bw + 'px', height: bh + 'px', borderRadius: '14px', boxSizing: 'border-box', border: `2px solid ${alpha(C.dim, 0.6)}`, background: alpha(C.panel, 0.9), display: 'flex', alignItems: 'center', justifyContent: 'center', fontFamily: 'var(--mono)', fontSize: S + 'px', color: C.code }, v));
        fadeIn(tl, b, t0, 0.5, 12); cells.push(b);
        const a = putArrow(k, arrow(tl, svg, x + bw + 10, by + bh / 2, x + bw + gap - 12, by + bh / 2, { stroke: C.dim, width: 3, head: 11 }));
        drawArrow(tl, a, t0 + 0.12, 0.3);
      });
      const nil = put(k, box(root, xc - bw / 2 + 3 * (bw + gap), by + (bh - lh) / 2, { fontFamily: 'var(--mono)', fontSize: S + 'px', lineHeight: lh + 'px', color: C.code, whiteSpace: 'pre' }, 'Nil'));
      fadeIn(tl, nil, ex + 1.1, 0.5, 12);
      // "only if some call passes it"
      w.mark(['xs'], C.dim, at('open2', 6.2), { fill: 0.08, out: Q('open2', 'cells') - 0.2, pad: 7 });
      // "The cells of a list ... are never passed"
      for (const b of cells) tl.to(b, { bg: alpha(C.dim, 0.13), border: alpha(C.dim, 0.9) }, Q('open2', 'cells') - 0.1, 0.4);
      const never = put(k, label(root, xc - bw / 2, by + bh + 30, 'never passed to a block'));
      fadeIn(tl, never, Q('open2', 'cells') + 0.1, 0.5, 10);
      open(k, 'open: patterns for what a call does not pass', Q('open2', 'nothing'));
    }

    // ==== 3 sets of closures ======================================================================================
    {
      const k = 2, one = Q('open3', 'one'), two = Q('open3', 'two');
      const ya = P0 + 20, yb = ya + 130;
      const c1 = putCode(k, new Code(tl, root, PX, ya, S));
      c1.show('{u0|use|f}{u1|(}{u2|inc⟨|p}{u3|u|o}{u4|⟩|p}{u5|)}', one - 0.2);
      const cw = c1.cw, lh = c1.lh;
      const oneL = put(k, label(root, PX + 11 * cw + 44, ya + (lh - 31) / 2, 'one closure: a direct call'));
      fadeIn(tl, oneL, one + 0.2, 0.5, 10);
      fadeOut(tl, oneL, two - 0.25, 0.35);
      // "When closures of two different functions reach the same parameter": two calls, one block
      c1.color(['u2', 'u3', 'u4'], C.code, two - 0.2, 0.5);
      const c2 = putCode(k, new Code(tl, root, PX, yb, S));
      c2.show('use(dbl⟨u⟩)', at('open3', 6.2));
      const ux = 1340, uy = (ya + yb) / 2;
      const u = putCode(k, new Code(tl, root, ux, uy, S));
      const ax0 = PX + 11 * cw + 24, ax1 = ux - 22;
      const a1 = putArrow(k, arrow(tl, svg, ax0, ya + lh / 2, ax1, uy + lh / 2 - 12, { stroke: C.dim, width: 3, head: 11 }));
      const a2 = putArrow(k, arrow(tl, svg, ax0, yb + lh / 2, ax1, uy + lh / 2 + 12, { stroke: C.dim, width: 3, head: 11 }));
      drawArrow(tl, a1, at('open3', 7.7), 0.4); drawArrow(tl, a2, at('open3', 7.8), 0.4);
      u.show('use({f|?f})', at('open3', 8.75));
      u.pulse(['f'], at('open3', 10.05), { color: C.bind });
      const ly = yb + lh + 50;
      const bin = put(k, label(root, PX, ly, 'two functions: a binder'));
      fadeIn(tl, bin, at('open3', 10.1), 0.5, 10);
      // "Flow analyses keep a set of functions there."
      fadeOut(tl, bin, Q('open3', 'flow') - 0.25, 0.35);
      const dimPal = { p: C.dim, b: C.dim, o: C.dim, k: C.dim, n: C.dim, f: C.dim, v: C.dim, x: C.dim };
      // the binder's place shows the set instead
      u.hide(at('open3', 14.75), 0.3);
      const set = putCode(k, new Code(tl, root, ux, uy, S, { palette: dimPal }));
      set.show('use({inc, dbl}⟨u⟩)', at('open3', 15.0));
      const flow = put(k, label(root, PX, ly, 'a flow analysis keeps the set'));
      fadeIn(tl, flow, at('open3', 15.1), 0.5, 10);
      open(k, 'open: patterns that hold a set', Q('open3', 'open'));
    }

    // ==== 4 a theory of policies ==================================================================================
    {
      const k = 3, single = Q('open4', 'single'), some = Q('open4', 'some');
      const LX = PX, RX = 1350, hy = P0 + 50, r1 = hy + 82, r2 = r1 + 40;
      const lh1 = put(k, serif(root, LX, hy, 'One pattern per block', 42));
      fadeIn(tl, lh1, single - 0.15, 0.5, 10);
      const la = put(k, label(root, LX, r1, 'a most specific answer'));
      fadeIn(tl, la, at('open4', 5.4), 0.5, 10);
      const lb = put(k, label(root, LX, r2, 'theorem 5.3'));
      fadeIn(tl, lb, at('open4', 8.6), 0.5, 10);
      const tk = put(k, tick(tl, svg, LX + labelW('theorem 5.3') + 40, r2 + 15, 26, C.ink, 4));
      tl.set(tk, { o: 1 }, 0); tl.to(tk, { draw: 1 }, at('open4', 9.25), 0.35, E.out);
      for (const e of [lh1, la, lb, tk]) tl.to(e, { o: 0.6 }, some - 0.3, 0.5);
      const rh = put(k, serif(root, RX, hy, 'Some policies', 42));
      fadeIn(tl, rh, some - 0.15, 0.5, 10);
      const ra = put(k, label(root, RX, r1, 'no most specific answer'));
      fadeIn(tl, ra, at('open4', 11.2), 0.5, 10);
      const rb = put(k, label(root, RX, r2, 'the order decides'));
      fadeIn(tl, rb, at('open4', 13.55), 0.5, 10);
      open(k, 'open: which policies keep one, and why', Q('open4', 'which'));
    }

    // ==== 5 restarting less =======================================================================================
    {
      const k = 4, whole = Q('open5', 'whole'), resume = Q('open5', 'resume');
      const words = ['Assume', 'Simplify', 'Check', 'Keep the forced binders'], WS = 34, gap = 64;
      const ww = words.map(t => serifW(t, WS));
      const ry = 500, my = ry + WS * 0.66, xs = [];
      let x = PX;
      words.forEach((t, i) => {
        xs.push(x);
        const e = put(k, serif(root, x, ry, t, WS));
        fadeIn(tl, e, whole - 0.2 + i * 0.12, 0.5, 12);
        if (i > 0) { const a = putArrow(k, arrow(tl, svg, x - gap + 14, my, x - 14, my, { stroke: C.dim, width: 2.5, head: 10 })); drawArrow(tl, a, whole - 0.1 + i * 0.12, 0.3); }
        x += ww[i] + gap;
      });
      const cx = i => xs[i] + ww[i] / 2;
      // "A refutation discards the whole round."
      const by = ry + WS * 1.22 + 12;
      const back = putArrow(k, arrow(tl, svg, cx(3), by, cx(0), by, { bend: -110, stroke: C.dim, width: 3, head: 12 }));
      drawArrow(tl, back, at('open5', 4.3), 0.7);
      const rest = put(k, label(root, cx(0) + 40, by + 55 + 26, 'a refutation restarts the round'));
      fadeIn(tl, rest, at('open5', 4.9), 0.5, 10);
      for (const e of [back, back._head, rest]) tl.to(e, { o: 0.55 }, resume - 0.3, 0.5);
      // "Resuming from the block that was refuted"
      const ay = ry - 8;
      const short = putArrow(k, arrow(tl, svg, cx(3), ay, cx(1), ay, { bend: 90, stroke: C.ink, width: 3, head: 12 }));
      drawArrow(tl, short, resume - 0.2, 0.6);
      const ls = ['resume at the refuted block:', 'same result on the programs we compared,', 'half the work'];
      const lt = [resume + 0.3, at('open5', 8.85), at('open5', 12.3)];
      ls.forEach((t, i) => put(k, fadeIn(tl, label(root, PX, ay - 45 - 40 - (2 - i) * 42 - 31, t), lt[i], 0.5, 10)));
      open(k, 'open: incremental, with the same guarantee', Q('open5', 'open'));
    }

    // ==== 6 a production compiler =================================================================================
    {
      const k = 5, ports = Q('open6', 'ports'), whole = Q('open6', 'whole');
      const pw = Math.ceil(labelW('a partial port')) + 56, ph = 104, py = [P0 + 30, P0 + 30 + ph + 40];
      const card = (x, y, w, h, linesT, dashed) => {
        const b = box(root, x, y, { width: w + 'px', height: h + 'px', borderRadius: '16px', boxSizing: 'border-box', border: `2px ${dashed ? 'dashed' : 'solid'} ${alpha(C.dim, dashed ? 0.75 : 0.6)}`, background: dashed ? 'transparent' : alpha(C.panel, 0.9), display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', gap: '6px' });
        linesT.forEach((t, i) => { const l = label(b, 0, 0, t, { color: i === linesT.length - 1 && !dashed ? C.ink : C.dim }); l.style.position = 'static'; });
        return b;
      };
      ['flambda 2', 'chez scheme'].forEach((n, i) => {
        const b = put(k, card(PX, py[i], pw, ph, ['a partial port', n]));
        fadeIn(tl, b, ports - 0.15 + i * 0.25, 0.5, 12);
      });
      const dl = ['the whole analysis', 'in a mature optimizer,', 'within its', 'compile-time budget'];
      const dw = Math.ceil(Math.max(...dl.map(labelW))) + 64, dh = 2 * ph + 40, dx = PX + pw + 110, dy = py[0];
      const big = put(k, card(dx, dy, dw, dh, dl, true));
      fadeIn(tl, big, whole + 0.1, 0.6, 12);
      py.forEach((y, i) => {
        const a = putArrow(k, arrow(tl, svg, PX + pw + 14, y + ph / 2, dx - 16, dy + dh / 2 + (i ? 16 : -16), { stroke: C.dim, width: 3, head: 11 }));
        drawArrow(tl, a, whole - 0.15 + i * 0.1, 0.45);
      });
      const nd = put(k, label(root, dx, dy + dh + 28, 'not done yet', { color: C.ink }));
      fadeIn(tl, nd, at('open6', 11.0), 0.5, 10);
      // "Each of these is a project": the list comes back whole
      const each = Q('open6', 'each');
      rows.forEach(r => { for (const e of r) tl.to(e, { o: 1 }, each - 0.1, 0.5); });
      const end = serif(root, RAIL, top + 6 * step + 30, 'Six projects. Several are thesis-sized.', 52);
      fadeIn(tl, end, each + 0.25, 0.7, 16);
    }

    // the panels leave
    panels.forEach(p => { for (const e of p) tl.to(e, { o: 0 }, p.leave, 0.35, E.in); });
  });
})();

// ==== src/scenes/s17_calls.js ====
// Two scenes that follow escape. conv: our form is nearly closure conversion; the one difference is the escape
// rule (an unknown call with known captures, where a converted closure's code gets an unknown record). calls: an
// ordinary call and return is the same case (the continuation is a closure of the caller's block K).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const RAIL = 160, LEAD = 2.0;

  function arrowAt(tl, svg, x1, y1, x2, y2, opts, at, dur = 0.5) {
    const a = arrow(tl, svg, x1, y1, x2, y2, opts);
    tl.set(a, { o: 0 }, 0); tl.set(a, { o: 1 }, at); drawArrow(tl, a, at, dur);
    return a;
  }
  // a cubic arrow (for a path that has to go around code), drawn at `at`
  function curveAt(tl, svg, pts, at, dur = 0.7) {
    const [[x0, y0], [x1, y1], [x2, y2], [x3, y3]] = pts;
    const p = path(tl, svg, `M ${x0} ${y0} C ${x1} ${y1} ${x2} ${y2} ${x3} ${y3}`, { stroke: C.dim, width: 3 });
    const head = 12, ang = Math.atan2(y3 - y2, x3 - x2);
    const h = el(svg, 'path');
    h.setAttribute('d', `M ${-head} ${-head * 0.55} L 0 0 L ${-head} ${head * 0.55}`);
    h.setAttribute('fill', 'none'); h.setAttribute('stroke-width', 3); h.setAttribute('stroke-linecap', 'round'); h.setAttribute('stroke-linejoin', 'round');
    h.style.stroke = C.dim; h.setAttribute('transform', `translate(${x3} ${y3}) rotate(${ang * 180 / Math.PI})`);
    p._head = h; tl.set(h, { o: 0 }, 0);
    tl.set(p, { o: 0 }, 0); tl.set(p, { o: 1 }, at); drawArrow(tl, p, at, dur);
    return p;
  }
  function tag(tl, root, x, y, text, at, out, style = {}) {
    const l = label(root, x, y, text, Object.assign({ fontSize: '26px' }, style));
    fadeIn(tl, l, at, 0.5, 10);
    if (out !== null) fadeOut(tl, l, out, 0.35, -8);
    return l;
  }
  const level = (code, l, h = 30) => code.y + l * code.lh + (code.lh - h) / 2;

  // ---- conv: our form is nearly closure conversion; the difference is the escape rule --------------------------
  scene('conv', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 42, HEAD = 280, LBL = 390, R0 = 440, CALL = 680;
    const dimPal = { palette: { d: C.dim } };

    // "This form is already close to closure conversion": our two lines
    const ours = new Code(tl, root, RAIL, R0, S, { leading: LEAD });
    const cw = ours.cw, lh = ours.lh, ROW = R0 + 2 * lh + 4, CL = CALL + lh + 4, CL2 = CL + 38;
    const RX = RAIL + 30 * cw;
    if (RX + 31 * cw > W - 110) console.warn('conv: the right column is too wide');
    // "Why not convert closures to records first ...? Because of the escape rule."
    const head = serif(root, RAIL, HEAD, 'Why not closure conversion first?', 56);
    fadeIn(tl, head, cue('what') - 0.2, 0.7, 20);
    fadeOut(tl, head, cue('key') - 0.35, 0.35);
    tag(tl, root, RAIL, HEAD + 86, 'because of the escape rule', cue('ans') - 0.1, cue('lift') - 0.3);

    // "Our form is already close to closure conversion": our two lines
    const oursL = tag(tl, root, RAIL, LBL, 'our form', cue('lift') - 0.1, null);
    const O0 = '{mn|mk|f}{mo|(}{mf|?f}{mc|)} {me|=} {on|outer|f}{ol|⟨}{of|f}{or|⟩}';
    const O1 = '{oun|outer|f}{oul|⟨}{ouf|?f}{our|⟩}{ouo|(}{ouz|?z}{ouc|)} {oue|=} {ff|f|f}{fo|(}{fz|z}{fc|)}';
    ours.show(O0 + '\n' + O1, cue('lift') + 0.1, { stagger: 0.01 });

    // "a block takes its captures as parameters, like any others"
    const tL = cue('lift') + 4.0;
    ours.mark(['oul', 'ouf', 'our'], C.dim, tL, { out: cue('diff') - 0.3, fill: 0.08, pad: 6 });
    ours.mark(['ouo', 'ouz', 'ouc'], C.dim, tL, { out: cue('diff') - 0.3, fill: 0.08, pad: 6 });
    tag(tl, root, RAIL, ROW, 'captures are parameters too', tL + 0.2, cue('diff') - 0.3);


    // "The difference shows when a closure escapes. The calls that will be made are unknown, but ... every one of
    // them comes with these captures": the closure in mk escapes; its extra call has unknown arguments and the
    // captures it was built with
    const tO = cue('ours');
    ours.mark(['on', 'ol', 'of', 'or'], C.dim, cue('diff') + 1.0, { out: tO + 0.2, fill: 0.08, pad: 6 });
    const oc = new Code(tl, root, RAIL, CALL, S, Object.assign({ leading: LEAD }, dimPal));
    oc.show('{on|outer|f}{ol|⟨}{ii|inner|p}{il|⟨|p}{iy|y|o}{ir|⟩|p}{or|⟩}{oo|(}{un|unknown|d}{ocl|)}', tO + 0.2, { rise: 10 });
    tag(tl, root, RAIL + 16 * cw, CL, 'unknown call', tO + 1.6, cue('rec') - 0.3);
    tag(tl, root, RAIL + 5 * cw, CL2, 'known captures', tO + 4.7, cue('rec') - 0.3);
    oc.mark(['ol', 'ii', 'il', 'iy', 'ir', 'or'], C.dim, tO + 4.6, { out: cue('rec') - 0.3, fill: 0.08, pad: 6 });
    // the left side steps back while the right side is built
    const tBack = cue('rec') - 0.2;
    for (const e of [ours.root, oc.root, oursL]) tl.to(e, { o: 0.45 }, tBack, 0.5);

    // "After real closure conversion, a closure is a record: a pointer to its code, and the captured values"
    const tR = cue('rec');
    const cvL = tag(tl, root, RX, LBL, 'after closure conversion', tR - 0.1, cue('esc') + 0.0);
    const cv = new Code(tl, root, RX, R0, S, { leading: LEAD });
    const C0 = '{rn|mk|f}{ro|(}{rf|?f}{rc|)} {re|=} {r0|(}{rcode|outer_code}{rcm|,} {rv|f}{r1|)}';
    cv.show(C0, tR + 1.6, { stagger: 0.01 });
    const fy = R0 + lh * 0.95;
    cv.mark(['rcode'], C.dim, tR + 3.0, { out: tR + 4.9, fill: 0.08, pad: 6 });
    tag(tl, root, cv.rect(['rcode']).x, fy, 'code pointer', tR + 3.1, tR + 4.9);
    cv.mark(['rv'], C.dim, tR + 5.0, { out: cue('code') - 0.3, fill: 0.1, pad: 8 });
    tag(tl, root, cv.rect(['rv']).x - 8, fy, 'captured value', tR + 5.1, cue('code') - 0.3);

    // "The code is an ordinary function, with the record as one more parameter"
    const C1 = '{cn|outer_code|f}{co|(}{cenv|?env}{ccm|,} {cz|?z}{cc|)} {ce|=} {cev|env.f}{cfo|(}{cfz|z}{cfc|)}';
    cv.morph(C0 + '\n' + C1, cue('code') - 0.15, { dur: 0.55 });
    cv.mark(['cenv'], C.bind, cue('code') + 2.9, { out: cue('esc') - 0.3, fill: 0.14, pad: 6 });

    // "When the record escapes, its code pointer escapes with it"
    const tE = cue('esc');
    const rec = ['r0', 'rcode', 'rcm', 'rv', 'r1'];
    cv.mark(rec, C.dim, tE + 0.15, { out: tE + 1.5, fill: 0.08, pad: 6 });
    tag(tl, root, RX, LBL, 'the record escapes', tE + 0.35, cue('any') + 0.3);
    cv.mark(['rcode'], C.dim, tE + 1.6, { out: cue('any') + 0.3, fill: 0.1, pad: 6 });

    // "and we would have to assume that someone may call the code with a totally unknown record": its extra call,
    // level with ours
    const tA = cue('any');
    const cc = new Code(tl, root, RX, CALL, S, Object.assign({ leading: LEAD }, dimPal));
    cc.show('{n|outer_code|f}{o|(}{u1|unknown|d}{m|,} {u2|unknown|d}{c|)}', tA + 0.6, { rise: 10 });
    tag(tl, root, RX, CL, 'unknown call, unknown record', tA + 3.4, cue('tie') - 0.3);

    // "Nothing in the program says that the code only ever receives the record that it was stored in"
    const tT = cue('tie') + 0.3;
    const ra = cv.rect(['rcode']), rb = cv.rect(['rv']), ty = R0 + lh * 0.2;
    const tie = path(tl, svg, `M ${ra.cx} ${ty} Q ${(ra.cx + rb.cx) / 2} ${ty - 44} ${rb.cx} ${ty}`, { stroke: C.dim, width: 2, dash: '5 7' });
    tl.set(tie, { o: 0 }, 0); tl.to(tie, { o: 1 }, tT, 0.5); tl.to(tie, { o: 0 }, cue('lost') - 0.3, 0.35);
    tag(tl, root, RX, LBL, 'stored together; nothing says so', tT + 0.1, cue('lost') - 0.3);

    // "So the environment is a binder, the call through F stays indirect, and the inner closure has to be built"
    const tS = cue('lost');
    cv.mark(['cn', 'co', 'cenv', 'ccm', 'cz', 'cc'], C.dim, tS + 0.1, { out: tS + 2.3, fill: 0.08, pad: 6 });
    tag(tl, root, RX, ROW, 'its pattern', tS + 0.2, tS + 2.3);
    cv.pulse(['cenv'], tS + 1.0, { color: C.bind });
    cv.mark(['cev', 'cfo', 'cfz', 'cfc'], C.dim, tS + 2.4, { out: cue('key') - 0.3, fill: 0.08, pad: 6 });
    tag(tl, root, cv.rect(['cev']).x, ROW, 'indirect call', tS + 2.5, tS + 4.5);
    tag(tl, root, RX, ROW, 'the inner closure is built', tS + 4.6, cue('key') - 0.3);
    // ours, for contrast: its pattern holds the closure, and the call through f is gone
    const O1b = '{oun|outer|f}{oul|⟨}{pi|inner|p}{pl|⟨|p}{py|?y}{pr|⟩|p}{our2|⟩}{ouo2|(}{ouz2|?z}{ouc2|)} {oue2|=} {zz|z} {zp|+} {zy|y|o}';
    ours.swap(O0 + '\n' + O1b, tS + 0.2, { dur: 0.5 });

    // "That is the cost of converting first: an unknown call with known captures becomes an unknown call with
    // unknown captures"
    const tK = cue('key');
    tl.to(ours.root, { o: 0.35 }, tK - 0.2, 0.5); tl.to(cv.root, { o: 0.35 }, tK - 0.2, 0.5); tl.to(oursL, { o: 0.35 }, tK - 0.2, 0.5);
    tl.to(oc.root, { o: 1 }, tK - 0.2, 0.5);
    lines(tl, root, RAIL, HEAD - 68, ['Known captures become', 'unknown captures.'], tK + 0.1, { size: 56, gap: 1.22 });
    oc.mark(['ol', 'ii', 'il', 'iy', 'ir', 'or'], C.dim, tK + 4.0, { fill: 0.08, pad: 6 });
    tag(tl, root, RAIL + 5 * cw, CL, 'known captures', tK + 4.1, null);
    cc.mark(['u1'], C.dim, tK + 6.4, { fill: 0.08, pad: 6 });
    tag(tl, root, cc.rect(['u1']).x, CL, 'unknown captures', tK + 6.5, null);

    // "So we analyze closures as closures, and lower them afterwards"
    tag(tl, root, RAIL, CL + 64, 'analyze closures as closures. lower them afterwards.', cue('so') - 0.1, null, { color: C.ink });
  });

  // ---- calls: an ordinary call and return is the same case ----------------------------------------------------
  scene('calls', ({ tl, root, cue }) => {
    const svg = svgLayer(root);
    const S = 50, y0 = 380;
    const code = new Code(tl, root, RAIL, y0, S, { leading: LEAD });
    const cw = code.cw, lh = code.lh;

    // "An ordinary call and return is the same case": the direct-style program
    const D0 = '{mn|main|f}{mo|(}{my|?y}{mc|)} {me|=} {l1|let} {pv|p} {pe|=} {q0|(}{qy|y}{qc|,} {q1|1}{qr|)} {in1|in}';
    const D1 = ' '.repeat(11) + '{l2|let} {rv|r} {re|=} {gn|get|f}{go|(}{gy|y}{gc|)} {in2|in}';
    const D2 = ' '.repeat(11) + '{ur|r} {up|+} {pp|p.1}';
    code.show([D0, D1, D2].join('\n'), cue('same') - 0.2, { stagger: 0.008 });

    // "what the caller does after a call is a block, K, and ... the caller passes a closure of it"
    const tk = cue('k');
    code.mark(['ur', 'up', 'pp'], C.dim, tk + 1.0, { out: tk + 2.4, fill: 0.08, pad: 6 });
    const M = '{mn|main|f}{mo|(}{my|?y}{ms|;} {mr|?ret}{mc|)} {me|=} {gn|get|f}{go|(}{gy|y}{gs|;} {kk|k|f}{kl|⟨}{q0|(}{qy|y}{qc|,} {q1|1}{qr|)}{kc|,} {kr|ret}{kg|⟩}{gc|)}';
    const K0 = '{kn|k|f}{knl|⟨}{kp|?p}{kpc|,} {kpr|?ret}{kng|⟩}{ko|(}{kx|?r}{kcp|)} {ke|=} {rt|ret|f}{rto|(}{ur|r} {up|+} {pp|p.1}{rtc|)}';
    code.swap(M + '\n' + K0, tk + 2.6, { dur: 0.5 });
    const clo = ['kk', 'kl', 'q0', 'qy', 'qc', 'q1', 'qr', 'kc', 'kr', 'kg'];
    code.mark(clo, C.dim, tk + 5.2, { out: cue('cap') + 0.1, fill: 0.08, pad: 6 });

    // "That closure captures the caller's local variables"
    const caps = ['q0', 'qy', 'qc', 'q1', 'qr', 'kc', 'kr'];
    code.mark(caps, C.dim, cue('cap') + 0.2, { out: cue('dup') - 0.3, fill: 0.1, pad: 6 });
    tag(tl, root, code.rect(caps).x, y0 - 44, "the caller's locals", cue('cap') + 0.3, cue('dup') - 0.3);

    // "When a function has one caller, as dup had, its return is a direct jump"
    tag(tl, root, RAIL, level(code, 2), 'one caller, as dup had: the return is a direct jump', cue('dup') + 0.1, cue('many') - 0.4);

    // "When it has several, its continuation is a binder"
    const G = '{gd|get|f}{gdo|(}{gi|?i}{gds|;} {gk|?k}{gdc|)} {gde|=} {gdots|…}';
    const gl = new Code(tl, root, RAIL, y0 + 2 * lh, S, { leading: LEAD });
    gl.show(G, cue('many') - 0.15);
    const gx = RAIL + 17 * cw;
    tag(tl, root, gx, level(code, 2), 'several callers', cue('many') + 0.5, cue('many') + 2.1);
    gl.mark(['gk'], C.bind, cue('many') + 2.2, { out: cue('res') - 0.3, fill: 0.14, pad: 6 });
    tag(tl, root, gx, level(code, 2), 'a binder', cue('many') + 2.3, cue('esc') + 1.0);

    // "so each continuation that is passed to it escapes": the closure flows into ?k, and counts as one more call
    // of k with an unknown argument
    const tE = cue('esc');
    const rk = gl.rect(['gk']), x0 = RAIL + 34 * cw;
    const yb = y0 + 2 * lh + lh * 0.82;
    const ea = curveAt(tl, svg, [[x0, y0 + lh * 0.84], [x0, y0 + 3.7 * lh], [rk.cx + 10, y0 + 3.7 * lh], [rk.cx, yb]], tE + 0.15, 0.8);
    tag(tl, root, RAIL + 18 * cw, y0 + 3.5 * lh, 'it escapes', tE + 0.8, tE + 2.4);
    hideArrow(tl, ea, tE + 2.4, 0.35);
    const fc = new Code(tl, root, RAIL, y0 + 3 * lh + 10, 44, { palette: { d: C.dim } });
    fc.show('{k|k|f}{l|⟨}{p0|(}{y|y|o}{pc|,} {p1|1}{pr|)}{c|,} {r|ret|o}{g|⟩}{o|(}{un|unknown|d}{cc|)}', tE + 2.7, { rise: 10 });

    // "Its argument, the result of the call, is unknown": k's head becomes its pattern, and p is substituted
    const tR = cue('res');
    gl.hide(tR - 0.3, 0.35);
    const K1 = '{kn|k|f}{knl|⟨}{h0|(|p}{hy|?y}{hc|,|p} {h1|1|p}{hr|)|p}{kpc|,} {kpr|?ret}{kng|⟩}{ko|(}{kx|?r}{kcp|)} {ke|=} {rt|ret|f}{rto|(}{ur|r} {up|+} {s0|(}{sy|y}{sc|,} {s1|1}{sr|).1}{rtc|)}';
    code.swap(M + '\n' + K1, tR - 0.2, { dur: 0.5 });
    code.mark(['ko', 'kx', 'kcp'], C.bind, tR + 1.3, { out: cue('keep') - 0.3, fill: 0.14, pad: 6 });
    fc.mark(['un'], C.dim, tR + 1.4, { out: cue('keep') - 0.3, fill: 0.08, pad: 6 });
    tag(tl, root, code.rect(['kx']).x - 30, level(code, 2), 'the result: unknown', tR + 1.5, cue('keep') - 0.3);

    // "But its captures are kept: what the caller knew before the call, it still knows after it"
    const tK = cue('keep');
    fc.hide(tK - 0.3, 0.35);
    code.mark(['h0', 'hy', 'hc', 'h1', 'hr'], C.pat, tK + 0.1, { out: cue('ex') - 0.3, pad: 6 });
    tag(tl, root, code.rect(['h0']).x, level(code, 2), 'known before the call, known after it', tK + 0.3, cue('ex') - 0.3);

    // "Here, the pair is never built, although a call lies between making it and using it"
    const tX = cue('ex');
    const K2 = '{kn|k|f}{knl|⟨}{h0|(|p}{hy|?y}{hc|,|p} {h1|1|p}{hr|)|p}{kpc|,} {kpr|?ret}{kng|⟩}{ko|(}{kx|?r}{kcp|)} {ke|=} {rt|ret|f}{rto|(}{ur|r} {up|+} {f1|1}{rtc|)}';
    code.swap(M + '\n' + K2, tX - 0.2, { dur: 0.5 });
    const O0 = '{mn|main|f}{mo|(}{my|?y}{ms|;} {mr|?ret}{mc|)} {me|=} {gn|get|f}{go|(}{gy|y}{gs|;} {kk|k|f}{kl|⟨}{okr|ret}{kg2|⟩}{gc2|)}';
    const O1 = '{kn|k|f}{knl|⟨}{okp|?ret}{kng2|⟩}{ko2|(}{kx2|?r}{kcp2|)} {ke2|=} {rt2|ret|f}{rto2|(}{ur2|r} {up2|+} {f2|1}{rtc2|)}';
    code.swap(O0 + '\n' + O1, tX + 0.9, { dur: 0.6 });
    tag(tl, root, RAIL, y0 - 44, 'output', tX + 1.0, cue('one') - 0.3);
    tag(tl, root, RAIL, level(code, 2), 'the pair is never built', tX + 1.5, cue('one') - 0.3);
    code.mark(['gn'], C.dim, tX + 2.8, { out: cue('frame') - 0.2, fill: 0.08, pad: 6 });

    // "And the closure that is built is the caller's stack frame. It no longer holds the pair."
    const tF = cue('frame');
    const fr = ['kk', 'kl', 'okr', 'kg2'];
    code.mark(fr, C.dim, tF + 0.1, { out: cue('one') - 0.3, fill: 0.1, pad: 6 });
    const fx = RAIL + 33 * cw;
    tag(tl, root, fx, level(code, 0), "the caller's stack frame", tF + 0.2, cue('one') - 0.3);
    tag(tl, root, fx, level(code, 1), 'without the pair', tF + 3.0, cue('one') - 0.3);

    // "So one mechanism analyzes across calls and returns, and through functions passed as values: closures in
    // patterns, and an escape rule that forgets only the arguments"
    const tO = cue('one');
    code.hide(tO - 0.3, 0.4);
    const key = serif(root, RAIL, 430, 'One mechanism, for calls, returns and functions as values.', 52);
    fadeIn(tl, key, tO + 0.2, 0.8, 20);
    tag(tl, root, RAIL, 560, 'closures in patterns', cue('how') - 0.1, null);
    tag(tl, root, RAIL, 606, 'an escape rule that forgets only the arguments', cue('how') + 1.0, null);
  });
})();

// ==== src/film.js ====
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
window.CAPTIONS = [[0.8, 3.32, "Here is a loop with four parameters."], [3.36, 6.68, "The analysis in this film reduces it to this:"], [6.72, 8.88, "two parameters, with the constant,"], [8.92, 12.76, "the dead branch, the option and the pair all gone."], [12.8, 16.44, "LLVM does not get all the way there."], [16.48, 19.4, "And here is a loop over a stream of closures."], [19.44, 21.88, "It can become a plain counting loop."], [21.92, 25.08, "This film is about one analysis that finds both,"], [25.12, 28.9, "with no inlining, and no rule about streams."], [29.2, 30.84, "Here is what is coming."], [30.88, 34.28, "First the idea, on three small loops."], [34.32, 36.2, "Then how the facts are found,"], [36.24, 37.48, "and a surprise:"], [37.52, 40.84, "the textbook way to compute them is not good enough."], [40.88, 42.84, "Then functions and closures,"], [42.88, 45.24, "where that stream becomes a counter."], [45.28, 48.36, "Then a dial, which turns the same analysis into"], [48.4, 50.52, "a specializer, an inliner,"], [50.56, 52.52, "or a partial evaluator."], [52.56, 54.68, "And at the end, what is proved,"], [54.72, 58.42, "and briefly, how it does in practice."], [61.74, 65.54, "A compiler optimizes a program by rewriting it."], [65.58, 68.18, "Two minus one becomes one."], [68.22, 70.82, "X minus X becomes zero."], [70.86, 74.1, "The first field of a pair is what was put there."], [74.14, 75.94, "These rules are local."], [75.98, 78.42, "To make them fire across a whole program,"], [78.46, 80.9, "the compiler needs global knowledge:"], [80.94, 83.38, "that this parameter is always one,"], [83.42, 85.66, "that these two are always equal,"], [85.7, 88.48, "that this one is always a pair."], [90.08, 92.32, "Finding such facts is hard,"], [92.36, 95.16, "because a fact can depend on itself."], [95.2, 97.88, "In this loop, X starts as one,"], [97.92, 101.4, "and every iteration passes two minus X."], [101.44, 105.16, "That is one again, but only if X was one."], [105.2, 108.12, "An analysis that claims only what it has already"], [108.16, 110.12, "proved never sees this."], [110.16, 113.69, "An optimistic analysis assumes that X is one,"], [113.73, 116.2, "because the first call passes one."], [116.24, 118.92, "It checks that the loop's own call then passes"], [118.96, 122.34, "one too, and keeps the fact."], [122.44, 125.28, "Compilers have many optimistic analyses of this"], [125.32, 126.32, "kind:"], [126.36, 129.2, "constant propagation, value numbering,"], [129.24, 131.84, "SSA construction, unboxing,"], [131.88, 135.84, "contification, control-flow analysis of closures."], [135.88, 137.95, "Each finds one kind of fact,"], [137.99, 141.34, "and they run one after another."], [143.16, 144.96, "The idea is this:"], [145.0, 147.76, "every such fact can be written as a pattern,"], [147.8, 150.4, "in the head of the block that it is about."], [150.44, 152.96, "It is the pattern of pattern matching in functional"], [153.0, 155.84, "programming, where a clause applies only to the"], [155.88, 159.2, "calls whose arguments match its patterns."], [159.24, 161.12, "One piece of notation."], [161.16, 162.8, "Where a variable is bound,"], [162.84, 164.4, "it has a question mark."], [164.44, 166.24, "We call that a binder."], [166.28, 169.54, "Where it is used, it is plain."], [169.58, 170.98, "Back to the loop."], [171.02, 173.5, "To state that X is always one,"], [173.54, 176.74, "write the pattern one in place of the binder."], [176.78, 179.7, "Substitute one for X in the body."], [179.74, 182.82, "Then rewrite with the compiler's local rules:"], [182.86, 185.7, "two minus one folds to one."], [185.74, 188.26, "Read as a definition by pattern matching,"], [188.3, 191.22, "this clause defines the loop only for calls whose"], [191.26, 193.3, "second argument is one."], [193.34, 196.92, "For any other call, the match fails."], [196.96, 200.52, "So the clause is safe if no call ever fails to"], [200.56, 201.08, "match."], [201.12, 203.72, "The program has two calls of the loop."], [203.76, 205.88, "Main's call passes one."], [205.92, 208.6, "The loop's own call, in the rewritten body,"], [208.64, 210.2, "passes one too."], [210.24, 211.53, "Both match."], [211.57, 214.92, "A match that never fails does not have to be performed:"], [214.96, 216.95, "the one need not be passed,"], [216.99, 218.84, "and need not be tested for."], [218.88, 220.12, "Delete it."], [220.16, 223.94, "What is left is a loop with one parameter."], [224.06, 226.18, "That is the whole recipe."], [226.22, 229.34, "Write a pattern in place of the parameters of every"], [229.38, 232.42, "block, as specific as it can be while every call"], [232.46, 234.74, "in the program still matches."], [234.78, 237.3, "Then remove the matching pieces."], [237.34, 240.66, "A block is anything that is jumped to with arguments:"], [240.7, 244.8, "a function, a loop, or a branch target."], [246.32, 250.23, "This may seem a roundabout way to do constant propagation."], [250.27, 252.92, "But the same recipe goes much further."], [252.96, 256.71, "In this loop, the parameters A and B start equal,"], [256.75, 258.44, "and change in step."], [258.48, 261.24, "To state that B is always equal to A,"], [261.28, 264.84, "write the plain name A as the pattern for B."], [264.88, 267.68, "A plain name in a pattern matches only the value"], [267.72, 269.08, "of that variable:"], [269.12, 271.68, "here, the parameter to its left."], [271.72, 275.08, "Substitute A for B, and the expression at the exit"], [275.12, 276.68, "folds to A."], [276.72, 278.36, "Both calls match:"], [278.4, 281.88, "main passes zero twice, and the loop passes A plus"], [281.92, 283.4, "one twice."], [283.44, 286.6, "Delete the match, and the third parameter is gone."], [286.64, 290.74, "This is value numbering, around a loop."], [290.86, 293.94, "Next, a loop that carries a pair."], [293.98, 297.46, "Q is always a pair, and its second field is always"], [297.5, 299.14, "main's U."], [299.18, 301.02, "One pattern says both:"], [301.06, 304.1, "a pair, with a binder S for the first field,"], [304.14, 306.82, "and the plain name U for the second."], [306.86, 309.94, "A plain name may also be a variable of the caller,"], [309.98, 311.86, "as U is here."], [311.9, 315.22, "Substitute it for Q, and the field accesses fold"], [315.26, 317.14, "to S and U."], [317.18, 319.94, "Both calls pass a pair that ends in U,"], [319.98, 321.54, "so both match."], [321.58, 322.98, "Delete the match."], [323.02, 325.3, "No pair is built any more."], [325.34, 327.78, "The loop is passed only the first field,"], [327.82, 330.1, "and it reads U from main:"], [330.14, 332.82, "the output nests the loop inside main,"], [332.86, 334.98, "where U is in scope."], [335.02, 339.6, "This is unboxing, together with copy propagation."], [339.7, 341.9, "Notice what did not change."], [341.94, 345.38, "Constant propagation, value numbering and unboxing"], [345.42, 346.94, "were the same steps:"], [346.98, 349.26, "substitute the pattern, rewrite,"], [349.3, 351.82, "check the calls, delete the match."], [351.86, 353.9, "Only the pattern was different."], [353.94, 356.38, "That economy is what we find elegant about the"], [356.42, 358.28, "idea."], [358.5, 360.94, "And notice what did not happen:"], [360.98, 363.1, "no code was copied."], [363.14, 365.9, "Think of ordinary constant propagation."], [365.94, 368.25, "It finds which values are constants,"], [368.29, 370.86, "and folds the code where it stands."], [370.9, 372.86, "Patterns work in the same way,"], [372.9, 374.86, "with more kinds of fact:"], [374.9, 377.58, "every block is simplified in place."], [377.62, 380.14, "Copies come only from a separate dial,"], [380.18, 383.26, "specialization, which we turn later."], [383.3, 387.0, "With that dial at zero, there are none."], [388.92, 391.36, "Which patterns are safe to use?"], [391.4, 393.2, "We call them stable."], [393.24, 396.64, "Patterns are stable if, once every block is rewritten"], [396.68, 399.84, "under its pattern, every call that remains matches"], [399.88, 402.2, "the pattern of the block it calls."], [402.24, 405.6, "For the unboxing loop, this pattern is stable."], [405.64, 407.92, "So is the pattern that says nothing."], [407.96, 409.68, "But this one is not."], [409.72, 412.96, "It claims that the first field is always zero."], [413.0, 416.08, "Under that claim, the loop's own call passes U"], [416.12, 419.34, "in that place, not zero."], [419.46, 422.02, "Stability is a fixed-point condition,"], [422.06, 424.14, "like an inductive invariant."], [424.18, 427.42, "When the program runs, every call matches."], [427.46, 430.7, "And that is true however the patterns were found."], [430.74, 433.58, "A compiler can take patterns from anywhere,"], [433.62, 435.9, "check in one pass that they are stable,"], [435.94, 437.64, "and use them."], [439.64, 443.31, "So far we wrote the patterns down and checked them."], [443.35, 445.12, "That is the easy part."], [445.16, 447.2, "The difficult part is finding them,"], [447.24, 450.0, "because a program has many stable patterns,"], [450.04, 452.4, "and we want the most specific."], [452.44, 454.24, "Recall the loop from the start,"], [454.28, 456.24, "with four parameters."], [456.28, 460.0, "X is always one, so the last line never runs."], [460.04, 464.08, "Because it never runs, A is always main's U."], [464.12, 467.68, "And Q is always Some, of a pair whose second field"], [467.72, 468.88, "is U."], [468.92, 470.96, "These facts depend on themselves,"], [471.0, 472.48, "and on one another."], [472.52, 476.78, "They have to be assumed before they can be confirmed."], [476.9, 479.58, "Here are six stable patterns for this loop,"], [479.62, 482.22, "from the least specific to the most."], [482.26, 484.22, "The first says nothing."], [484.26, 487.1, "The second is what conditional constant propagation"], [487.14, 488.3, "finds."], [488.34, 491.42, "The third is what Lemerre's analysis finds."], [491.46, 493.42, "Then the option is unboxed,"], [493.46, 495.42, "then the pair inside it."], [495.46, 497.61, "The last is the most specific:"], [497.65, 500.38, "the second field of the pair is U."], [500.42, 502.82, "None of the seven published analyses that we ran"], [502.86, 504.94, "on this loop finds all of it,"], [504.98, 511.08, "and LLVM, at -O3, finds all but the last step."], [513.0, 515.68, "We find the patterns by refutation."], [515.72, 518.59, "Assume the strongest thing that could be true:"], [518.63, 521.4, "a block's pattern is exactly the arguments of the"], [521.44, 522.88, "calls that reach it."], [522.92, 526.36, "Then let the program refute it."], [526.4, 527.8, "Round one."], [527.84, 530.6, "Main's call is the first to reach the loop,"], [530.64, 532.84, "so it is the loop's pattern:"], [532.88, 536.44, "N, U, one, and Some of the pair zero,"], [536.48, 537.4, "U."], [537.44, 539.72, "Simplify the body under it."], [539.76, 542.55, "X is one, so the test is decided,"], [542.59, 544.52, "and the last line is dead."], [544.56, 547.0, "Two minus one folds to one,"], [547.04, 550.96, "and U plus, U minus U, folds to U."], [551.0, 552.6, "One call is left."], [552.64, 554.04, "Check it against the pattern,"], [554.08, 555.56, "place by place."], [555.6, 557.64, "It differs in two places:"], [557.68, 561.72, "N minus one against N, and U against zero."], [561.76, 564.3, "The pattern is refuted."], [564.34, 567.18, "Only one thing is kept for the next round:"], [567.22, 570.22, "a binder at each place where the call differed."], [570.26, 572.3, "We call this the skeleton."], [572.34, 573.98, "Everything else is discarded,"], [574.02, 576.7, "including the values that the round computed,"], [576.74, 578.94, "because they were computed under a pattern that"], [578.98, 580.86, "has just been refuted."], [580.9, 582.22, "Round two."], [582.26, 583.5, "Assume again:"], [583.54, 586.3, "main's call, with binders where the skeleton has"], [586.34, 587.1, "them."], [587.14, 590.75, "The U, the one, and the U in the pair come back,"], [590.79, 592.82, "because main's call passes them."], [592.86, 593.9, "Simplify."], [593.94, 595.1, "Check the call."], [595.14, 596.83, "A binder matches anything,"], [596.87, 598.7, "and the other places agree."], [598.74, 602.72, "Nothing is refuted, so the patterns are stable."], [602.76, 604.72, "Now delete the matches."], [604.76, 607.28, "The loop's parameters are its two binders,"], [607.32, 610.08, "and each call passes what matched them."], [610.12, 612.48, "Four parameters have become two."], [612.52, 614.96, "The constant and the dead branch are gone,"], [615.0, 617.36, "the option and the pair are never built,"], [617.4, 619.84, "and the loop reads U from main."], [619.88, 621.68, "So the algorithm is:"], [621.72, 625.6, "assume, simplify, check, and keep only the binders"], [625.64, 627.6, "that a refutation forced."], [627.64, 630.4, "Repeat until a round refutes nothing."], [630.44, 633.84, "A pattern can be refuted only finitely many times,"], [633.88, 636.44, "so this terminates."], [636.48, 638.36, "Notice what just happened."], [638.4, 641.56, "Four facts that depend on themselves and on one"], [641.6, 643.32, "another were found together,"], [643.36, 645.88, "in two rounds, by one rule."], [645.92, 648.44, "Compilers usually have a separate analysis for"], [648.48, 652.82, "each kind of fact, and run them one after another."], [654.74, 656.78, "Now the surprising part."], [656.82, 658.94, "Why discard the round?"], [658.98, 661.86, "The textbook way to compute a fixed point keeps"], [661.9, 664.41, "what it has found, and repairs it."], [664.45, 666.89, "For patterns, that gives a correct answer,"], [666.93, 669.1, "but not always the best one."], [669.14, 671.02, "Here are three blocks."], [671.06, 673.5, "Main calls F with one."], [673.54, 676.06, "F passes its argument on to G."], [676.1, 677.74, "And G tests it:"], [677.78, 681.02, "if it is one, G calls F with two."], [681.06, 683.74, "Both methods begin in the same way."], [683.78, 686.3, "F is assumed to be F of one."], [686.34, 689.74, "Its body calls G of one, so G is assumed to be"], [689.78, 691.02, "G of one."], [691.06, 693.26, "Under that, the test is true,"], [693.3, 696.7, "and G calls F of two, which does not match F of"], [696.74, 698.48, "one."], [698.52, 701.72, "A repair in place now weakens F's pattern to a"], [701.76, 704.48, "binder, and revisits F."], [704.52, 708.08, "F now calls G of X, while G's pattern is still"], [708.12, 709.52, "G of one."], [709.56, 711.84, "One and X have nothing in common,"], [711.88, 714.24, "so their join is a new binder."], [714.28, 717.68, "That is stable, but it is not the most specific."], [717.72, 721.2, "The one in G's old pattern was never a fact about"], [721.24, 721.6, "G."], [721.64, 724.64, "It was F's X, under an assumption that has since"], [724.68, 726.94, "been refuted."], [727.04, 730.52, "The algorithm keeps one thing from the first round:"], [730.56, 733.32, "F's parameter must be a binder."], [733.36, 735.32, "Then it starts again."], [735.36, 737.72, "F's body calls G of X."], [737.76, 740.2, "This is the first call to reach G,"], [740.24, 743.24, "so G's pattern is the plain name X:"], [743.28, 746.52, "G's argument is always F's X."], [746.56, 751.38, "G is passed nothing, and is nested inside F."], [751.58, 755.3, "Why is the result of the restarts the most specific?"], [755.34, 757.86, "Look at the one binder that was forced:"], [757.9, 759.26, "F's parameter."], [759.3, 762.18, "It was forced by the call F of two."], [762.22, 763.94, "Under any stable patterns,"], [763.98, 767.06, "that call is made too, perhaps with less specific"], [767.1, 769.94, "arguments, and there it must match."], [769.98, 772.98, "So any stable patterns have a binder there too,"], [773.02, 774.26, "or above it."], [774.3, 776.5, "The binder was never a choice."], [776.54, 779.7, "Everything else is assumed afresh in every round,"], [779.74, 781.62, "as strongly as it can be."], [781.66, 784.18, "And so the order in which the blocks are visited"], [784.22, 786.38, "does not matter."], [786.42, 789.82, "So the textbook method is not optimal for patterns,"], [789.86, 792.54, "and in some programs its answer depends on the"], [792.58, 794.06, "order of the visits."], [794.1, 796.97, "Yet a most specific answer exists,"], [797.01, 799.82, "and the restarts find it in any order."], [799.86, 803.48, "That is a theorem, checked in Lean."], [805.4, 808.32, "Nothing so far was special to loops."], [808.36, 811.76, "For functions, we write programs in continuation-passing"], [811.8, 812.8, "style."], [812.84, 815.2, "A function takes one more parameter,"], [815.24, 817.28, "written after a semicolon:"], [817.32, 820.76, "its continuation, the block to jump to with the"], [820.8, 821.36, "result."], [821.4, 823.52, "Returning is a jump to it."], [823.56, 826.64, "What the caller does after the call becomes a separate"], [826.68, 829.76, "block, K, which the caller passes."], [829.8, 833.68, "Now a call, a return, a loop and a branch are all"], [833.72, 837.12, "jumps, so one rule covers all control flow,"], [837.16, 840.66, "within a function and across functions."], [840.7, 843.3, "This function is called from one place,"], [843.34, 845.46, "so its pattern is that call,"], [845.5, 848.54, "and its continuation is always K."], [848.58, 851.86, "Its return is then a direct jump to K."], [851.9, 854.06, "This is contification."], [854.1, 856.1, "That jump passes the pair Y,"], [856.14, 859.01, "Y, so the pair is in K's pattern,"], [859.05, 862.58, "and the difference of its two fields folds to zero."], [862.62, 864.58, "So this pair is never built."], [864.62, 868.06, "The whole program returns zero."], [868.1, 870.7, "From here on, the examples are written without"], [870.74, 874.52, "their continuations, to keep them short."], [874.72, 877.6, "A lambda is treated in the same way."], [877.64, 879.91, "This one becomes a block, inc,"], [879.95, 883.12, "with its free variable U in angle brackets."], [883.16, 886.39, "A block with those parameters supplied is a closure,"], [886.43, 888.36, "and they are its captures."], [888.4, 891.64, "A closure is data, so a pattern can match on it"], [891.68, 892.84, "as on a pair:"], [892.88, 894.68, "the block is the constructor,"], [894.72, 897.0, "and the captures are its fields."], [897.04, 901.28, "Here, app is always passed inc with main's U."], [901.32, 904.44, "Substitute that for F, and the call through F is"], [904.48, 906.44, "a direct call of inc."], [906.48, 908.68, "The output is one plus U."], [908.72, 911.7, "The closure is never built."], [911.82, 914.9, "Here is a fold over a range of integers."], [914.94, 918.66, "Sum passes it a closure that has captured C."], [918.7, 921.83, "Every call of fold passes that same closure,"], [921.87, 923.7, "the recursive call included,"], [923.74, 926.37, "so fold's pattern contains the closure,"], [926.41, 929.22, "with binders only for S and I."], [929.26, 932.74, "The call through F is a direct call of scale."], [932.78, 935.86, "The output is a loop over numbers that uses sum's"], [935.9, 936.82, "C."], [936.86, 941.12, "No closure is built, and no code was copied."], [941.24, 943.44, "When several calls reach a block,"], [943.48, 945.52, "its pattern is their join:"], [945.56, 948.64, "the most specific pattern that all of them match,"], [948.68, 950.96, "with binders where they differ."], [951.0, 955.08, "Zero, zero and one, one join to a binder and then"], [955.12, 956.08, "its name:"], [956.12, 958.56, "the two arguments are equal."], [958.6, 963.66, "Zero, zero and one, two join to two binders."], [963.76, 967.12, "In the last example, the closure changes on every"], [967.16, 968.52, "iteration."], [968.56, 971.68, "A stream is a closure that returns its first value"], [971.72, 973.64, "and the stream of the rest."], [973.68, 976.28, "From of A is the stream A,"], [976.32, 978.76, "A plus one, and so on."], [978.8, 981.72, "Sum adds up the first values of a stream."], [981.76, 984.84, "In round one, sum's pattern is main's call,"], [984.88, 986.92, "with the stream from one."], [986.96, 989.48, "Under it, the call of G is direct,"], [989.52, 991.24, "and its result is known:"], [991.28, 993.72, "one, and the stream from two."], [993.76, 996.44, "So the recursive call passes from two,"], [996.48, 998.36, "which refutes the pattern."], [998.4, 1000.84, "Both calls pass a closure of from,"], [1000.88, 1003.72, "so the join keeps from, and puts a binder at its"], [1003.76, 1004.92, "capture."], [1004.96, 1008.28, "In round two, the recursive call passes from of"], [1008.32, 1011.0, "A plus one, and that matches."], [1011.04, 1012.84, "Where the source passed a stream,"], [1012.88, 1015.64, "the output passes only its counter."], [1015.68, 1019.2, "The stream has become a loop variable."], [1019.24, 1021.92, "This result deserves a second look."], [1021.96, 1025.28, "A stream of closures, each one building the next,"], [1025.32, 1026.8, "became a counter."], [1026.84, 1029.47, "The analysis has no rule about streams,"], [1029.51, 1031.44, "and no fusion framework."], [1031.48, 1034.67, "All it did was join two closures of the same block,"], [1034.71, 1037.5, "and keep what they share."], [1037.62, 1039.7, "One more rule is needed."], [1039.74, 1042.38, "A closure escapes when we lose track of where it"], [1042.42, 1043.42, "goes:"], [1043.46, 1046.3, "the program returns it, passes it to code that"], [1046.34, 1049.42, "we do not analyze, or passes it where a pattern"], [1049.46, 1051.38, "has only a binder."], [1051.42, 1054.62, "Whoever holds it may call it with any arguments."], [1054.66, 1057.34, "We count that as one more call of its block,"], [1057.38, 1059.18, "with unknown arguments."], [1059.22, 1061.58, "But only the arguments are unknown."], [1061.62, 1064.14, "What the closure captured was fixed where it was"], [1064.18, 1066.7, "built, and the pattern keeps it."], [1066.74, 1069.34, "Here, the closure that is returned has captured"], [1069.38, 1070.86, "another closure."], [1070.9, 1073.82, "Inside it, the call through F is still a direct"], [1073.86, 1077.1, "call, and the inner closure is never built."], [1077.14, 1080.14, "This is what makes the analysis higher-order:"], [1080.18, 1082.54, "knowledge enters a function's body through what"], [1082.58, 1086.66, "it captured, wherever the function goes."], [1086.7, 1089.54, "Why not convert closures to records first,"], [1089.58, 1092.26, "and then run a first-order analysis?"], [1092.3, 1094.42, "Because of the escape rule."], [1094.46, 1097.86, "Our form is already close to closure conversion:"], [1097.9, 1100.53, "a block takes its captures as parameters,"], [1100.57, 1102.02, "like any others."], [1102.06, 1105.09, "The difference shows when a closure escapes."], [1105.13, 1107.65, "The calls that will be made are unknown,"], [1107.69, 1110.54, "but we know that every one of them comes with these"], [1110.58, 1111.3, "captures."], [1111.34, 1113.35, "After real closure conversion,"], [1113.39, 1115.17, "a closure is a record:"], [1115.21, 1118.58, "a pointer to its code, and the captured values."], [1118.62, 1120.69, "The code is an ordinary function,"], [1120.73, 1123.3, "with the record as one more parameter."], [1123.34, 1126.34, "When the record escapes, its code pointer escapes"], [1126.38, 1129.82, "with it, and a first-order analysis has to assume"], [1129.86, 1133.26, "that someone may call the code with a totally unknown"], [1133.3, 1134.1, "record."], [1134.14, 1136.58, "Nothing in the program says that the code only"], [1136.62, 1139.7, "ever receives the record that it was stored in."], [1139.74, 1141.94, "So the environment is a binder,"], [1141.98, 1144.66, "the call through F stays indirect,"], [1144.7, 1147.38, "and the inner closure has to be built."], [1147.42, 1149.86, "That is the cost of converting first:"], [1149.9, 1152.74, "an unknown call with known captures becomes an"], [1152.78, 1155.7, "unknown call with unknown captures."], [1155.74, 1158.26, "So we analyze closures as closures,"], [1158.3, 1161.2, "and lower them afterwards."], [1161.52, 1165.24, "An ordinary call and return is the same case."], [1165.28, 1168.2, "Recall that what the caller does after a call is"], [1168.24, 1171.4, "a block, K, and that the caller passes a closure"], [1171.44, 1172.44, "of it."], [1172.48, 1175.96, "That closure captures the caller's local variables."], [1176.0, 1177.72, "When a function has one caller,"], [1177.76, 1181.32, "as dup had, its return is a direct jump."], [1181.36, 1184.6, "When it has several, its continuation is a binder,"], [1184.64, 1188.12, "so each continuation that is passed to it escapes."], [1188.16, 1190.47, "Its argument, the result of the call,"], [1190.51, 1191.72, "is unknown."], [1191.76, 1193.56, "But its captures are kept:"], [1193.6, 1195.56, "what the caller knew before the call,"], [1195.6, 1197.56, "it still knows after it."], [1197.6, 1199.64, "Here, the pair is never built,"], [1199.68, 1202.28, "although a call lies between making it and using"], [1202.32, 1203.08, "it."], [1203.12, 1205.56, "And the closure that is built is the caller's stack"], [1205.6, 1206.28, "frame."], [1206.32, 1208.6, "It no longer holds the pair."], [1208.64, 1212.55, "So one mechanism analyzes across calls and returns,"], [1212.59, 1215.0, "and through functions passed as values:"], [1215.04, 1218.36, "closures in patterns, and an escape rule that forgets"], [1218.4, 1220.98, "only the arguments."], [1222.9, 1225.66, "Here is the fold again, used twice:"], [1225.7, 1228.38, "once to sum, and once to hash."], [1228.42, 1230.3, "With one pattern for each block,"], [1230.34, 1232.38, "both calls flow into fold,"], [1232.42, 1234.78, "and its pattern is their join."], [1234.82, 1237.66, "F is one lambda at the first call and another at"], [1237.7, 1240.7, "the second, so the pattern has a binder there,"], [1240.74, 1243.5, "and the call through F is not direct."], [1243.54, 1245.82, "Had the program been written with two copies of"], [1245.86, 1249.92, "fold, each copy would again have one caller."], [1249.96, 1252.8, "So we let a block have several patterns."], [1252.84, 1256.0, "A specialization policy says which part of a call"], [1256.04, 1257.6, "is its context."], [1257.64, 1260.52, "With the closure policy, the context is the labels"], [1260.56, 1263.12, "of the closures that the call passes."], [1263.16, 1266.12, "Calls with different contexts go to different versions"], [1266.16, 1269.87, "of the block, and each version has its own pattern."], [1269.91, 1272.72, "The recursive call passes the same closure,"], [1272.76, 1274.88, "so it goes back to the same version,"], [1274.92, 1277.76, "and the loop is specialized as a whole."], [1277.8, 1280.24, "The output is two loops over numbers,"], [1280.28, 1282.08, "as written by hand."], [1282.12, 1285.98, "This is the only way in which a block is copied."], [1286.1, 1290.02, "The policy works as a dial on the same fixed point."], [1290.06, 1291.94, "With one version for each block,"], [1291.98, 1294.22, "it is a dataflow analysis."], [1294.26, 1296.46, "With a version for each closure passed,"], [1296.5, 1299.58, "a specializer of higher-order functions."], [1299.62, 1301.34, "For each constructor passed,"], [1301.38, 1303.66, "call-pattern specialization."], [1303.7, 1306.17, "For each call site, an inliner."], [1306.21, 1308.62, "And for each value of a marked parameter,"], [1308.66, 1312.46, "a partial evaluator, which can specialize an interpreter"], [1312.5, 1313.94, "away."], [1313.98, 1317.06, "Here is the last stop of the dial at work."], [1317.1, 1320.5, "This matcher takes a regular expression and a string."], [1320.54, 1323.02, "For each character, it takes the derivative of"], [1323.06, 1325.34, "the expression, and goes on."], [1325.38, 1327.94, "Mark the expression as the parameter to specialize"], [1327.98, 1328.82, "on."], [1328.86, 1331.58, "The matcher then gets a version for each expression"], [1331.62, 1333.22, "that it is called with."], [1333.26, 1334.42, "There are three."], [1334.46, 1337.86, "In each of them, the derivative is computed away."], [1337.9, 1340.02, "What is left is the automaton:"], [1340.06, 1342.88, "one loop for each state."], [1343.1, 1345.3, "Here is the point of the dial."], [1345.34, 1349.06, "Specializers, inliners and partial evaluators are"], [1349.1, 1352.5, "usually separate tools, with separate machinery."], [1352.54, 1355.38, "Here, each is one setting of a parameter,"], [1355.42, 1358.72, "on the analysis we already had."], [1360.64, 1363.96, "We proved three theorems in the Lean proof assistant,"], [1364.0, 1366.16, "for a core language with constructors,"], [1366.2, 1369.4, "closures and operations, and one pattern for each"], [1369.44, 1370.92, "block."], [1370.96, 1371.64, "First:"], [1371.68, 1374.84, "stable patterns hold when the program runs."], [1374.88, 1377.44, "At every step, the values of the running block"], [1377.48, 1380.24, "are an instance of its pattern."], [1380.28, 1380.96, "Second:"], [1381.0, 1383.36, "stable patterns are safe to use."], [1383.4, 1386.04, "The rewritten program halts with the same value"], [1386.08, 1388.76, "as the original, or neither halts."], [1388.8, 1389.75, "Third:"], [1389.79, 1393.48, "the algorithm finds the most specific stable patterns."], [1393.52, 1396.87, "Every run terminates, in any order of its steps,"], [1396.91, 1398.52, "with patterns that are stable,"], [1398.56, 1403.22, "and at least as specific as any other stable patterns."], [1403.34, 1406.74, "The theorems are about the formalization in Lean."], [1406.78, 1409.3, "The reference implementation and the compiler's"], [1409.34, 1412.42, "optimizer are tested, not verified."], [1412.46, 1415.14, "And the theorems are not proved for specialization"], [1415.18, 1416.18, "policies."], [1416.22, 1419.06, "For some policies the third one fails."], [1419.1, 1422.96, "A theory of policies is future work."], [1424.88, 1427.4, "The interest of this work is the idea,"], [1427.44, 1431.44, "not a benchmark, so the practical side only briefly."], [1431.48, 1434.36, "In a compiler for a dependently typed language,"], [1434.4, 1438.76, "this analysis is the only optimizer before LLVM."], [1438.8, 1441.99, "We wrote twelve small programs with an abstraction,"], [1442.03, 1445.96, "such as a fold, a stream, or a dictionary of functions."], [1446.0, 1448.52, "Nine of them compile to the same assembly as a"], [1448.56, 1451.3, "loop written by hand."], [1451.42, 1454.54, "This compiler gets one more thing from the same"], [1454.58, 1455.22, "analysis:"], [1455.26, 1457.14, "monomorphization."], [1457.18, 1461.22, "Types are ordinary values in its intermediate representation,"], [1461.26, 1464.66, "so a specialization policy on type arguments gives"], [1464.7, 1467.54, "a generic function a version for each type it is"], [1467.58, 1468.66, "used at."], [1468.7, 1472.88, "There is no separate monomorphization pass."], [1473.1, 1476.26, "Parts of the analysis are also ported to two mature"], [1476.3, 1479.86, "optimizers, Flambda two and Chez Scheme."], [1479.9, 1481.62, "They speed up some programs,"], [1481.66, 1484.64, "and leave most unchanged."], [1484.76, 1487.92, "And on small generated programs with constructors,"], [1487.96, 1491.04, "each of seven published analyses misses the most"], [1491.08, 1494.32, "specific patterns on about a quarter of the programs,"], [1494.36, 1495.48, "or more."], [1495.52, 1497.36, "A miss is not an error:"], [1497.4, 1499.28, "their results are correct."], [1499.32, 1502.16, "Our algorithm finds the most specific patterns"], [1502.2, 1506.62, "on every program, as the third theorem says."], [1508.62, 1511.62, "One last point, for compiler writers."], [1511.66, 1514.18, "The programs in this film look functional,"], [1514.22, 1517.7, "but they are a low-level intermediate representation."], [1517.74, 1519.86, "A definition is a basic block,"], [1519.9, 1521.94, "and a call is a jump."], [1521.98, 1524.9, "Here is the first loop written three ways:"], [1524.94, 1526.78, "with assignments and jumps,"], [1526.82, 1530.5, "in SSA form, and as blocks with arguments,"], [1530.54, 1533.46, "as in MLIR or Cranelift."], [1533.5, 1537.22, "A block's parameters are the phi functions of SSA,"], [1537.26, 1540.34, "so the pattern one says that this phi is the constant"], [1540.38, 1541.38, "one."], [1541.42, 1544.74, "With functions, the same blocks are a continuation-passing"], [1544.78, 1546.58, "style representation."], [1546.62, 1550.72, "So the analysis fits a compiler that has either."], [1552.64, 1556.2, "The idea is young, and a lot is left to do."], [1556.24, 1559.08, "Here are six open problems."], [1559.12, 1559.88, "One:"], [1559.92, 1561.8, "facts from tests."], [1561.84, 1564.36, "Inside the true branch of this test,"], [1564.4, 1565.72, "X is zero."], [1565.76, 1568.49, "But a pattern describes what calls pass,"], [1568.53, 1571.6, "and the outcome of a test is not an argument."], [1571.64, 1573.96, "Giving the branch a version that is passed what"], [1574.0, 1577.4, "the test established does find such facts."], [1577.44, 1580.88, "What is missing is a most specific answer in that"], [1580.92, 1582.5, "setting."], [1582.62, 1583.54, "Two:"], [1583.58, 1585.62, "values in the heap."], [1585.66, 1588.74, "A pattern knows a value only if some call passes"], [1588.78, 1589.73, "it."], [1589.77, 1592.54, "The cells of a list, or a function stored inside"], [1592.58, 1594.66, "a record, are never passed,"], [1594.7, 1598.24, "so the patterns say nothing about them."], [1598.36, 1599.36, "Three:"], [1599.4, 1601.12, "sets of closures."], [1601.16, 1603.68, "A pattern holds one closure."], [1603.72, 1606.0, "When closures of two different functions reach"], [1606.04, 1608.83, "the same parameter, it becomes a binder,"], [1608.87, 1611.68, "and calls through it are no longer direct."], [1611.72, 1615.04, "Flow analyses keep a set of functions there."], [1615.08, 1618.46, "Patterns with such sets are open."], [1618.58, 1619.42, "Four:"], [1619.46, 1621.34, "a theory of policies."], [1621.38, 1623.42, "With one pattern for each block,"], [1623.46, 1626.33, "the most specific stable patterns exist,"], [1626.37, 1628.09, "and that is proved."], [1628.13, 1630.49, "With some policies they do not exist,"], [1630.53, 1633.06, "and the result depends on the order."], [1633.1, 1635.9, "Which policies keep a most specific answer,"], [1635.94, 1639.24, "and why, is not known."], [1639.44, 1640.52, "Five:"], [1640.56, 1642.36, "restarting less."], [1642.4, 1645.48, "A refutation discards the whole round."], [1645.52, 1648.2, "Resuming from the block that was refuted gave the"], [1648.24, 1651.0, "same result on every program we compared,"], [1651.04, 1652.68, "with half the work."], [1652.72, 1655.56, "An incremental algorithm with the same guarantee"], [1655.6, 1657.7, "is open."], [1657.82, 1658.9, "And six:"], [1658.94, 1660.86, "a production compiler."], [1660.9, 1663.22, "Two partial ports exist."], [1663.26, 1666.5, "Taking the whole analysis into a mature optimizer,"], [1666.54, 1668.42, "within its compile-time budget,"], [1668.46, 1669.94, "has not been done."], [1669.98, 1671.78, "Each of these is a project,"], [1671.82, 1675.28, "and several are the size of a thesis."], [1677.2, 1679.96, "Constant propagation, value numbering,"], [1680.0, 1682.72, "SSA construction, unboxing,"], [1682.76, 1685.64, "contification and the control-flow analysis of"], [1685.68, 1688.84, "closures are usually separate analyses."], [1688.88, 1691.24, "Stable patterns unify them."], [1691.28, 1694.04, "The most specific stable patterns exist,"], [1694.08, 1696.12, "and refutation finds them:"], [1696.16, 1698.76, "assume the best, simplify under it,"], [1698.8, 1702.36, "and weaken only where a call contradicts the assumption."], [1702.4, 1704.12, "With a closure in a pattern,"], [1704.16, 1707.64, "the analysis is interprocedural and higher-order."], [1707.68, 1709.72, "With several patterns for a block,"], [1709.76, 1712.28, "the same fixed point is a specializer,"], [1712.32, 1715.32, "an inliner, or a partial evaluator."], [1715.36, 1719.08, "And it is this one analysis that reduced the four-parameter"], [1719.12, 1723.46, "loop to two, and turned the stream into a counter."]];
