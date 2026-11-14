// StacKAT: Infinite State Network Verification: the video: the film's scripts in one file, made by tools/web.py.

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
// The full-length film on "StacKAT: Infinite State Network Verification" (PLDI 2025). One story: a network is a
// program and verification is program equivalence (NetKAT); real packets need a stack, which makes the state space
// infinite; StacKAT adds push and pop; three laws about them become three steps on a finite automaton, after which
// equivalent programs have equal automata; then headers, cost, counterexamples and axioms.
// {name} marks a cue. "Stack Cat" and "Net Cat" are written as they are spoken (src/caption-fixes.json has their
// spelling); single letters are capitals so that they are read as letters. No person is named in the narration.
window.NARRATION = [
  // ------------------------------------------------------------------------------------------------ opening
  { id: 'hook', chapter: '', pre: 0.8, post: 0.7, text:
    `{two}Here are two small programs. Each one acts on a stack. {p1}The first pushes the value A some number of times, and then pops it some number of times. ` +
    `{star}The star is the star of regular expressions. It means some number of times: zero, one, two, or more. {notwhile}It is not a loop that keeps running. {trace}Like a regular expression, the program generates sequences of pushes and pops, called traces. {run}Each trace is one way the program can run. ` +
    `{p2}The second program does one or the other: only pushes, or only pops. {eq}The two are equivalent: on every stack, they can do exactly the same things. {how}How could a machine check that? {inf}A stack can be arbitrarily deep, so there are infinitely many stacks to try. ` +
    `{film}This video is about a language for networks, called Stack Cat, in which that question always has an answer. {hand}By the end, we will have checked these two programs by hand, {algo}and we will know an algorithm that checks any such equivalence automatically.` },
  { id: 'roadmap', chapter: '', pre: 0.3, post: 0.8, text:
    `{coming}Here is what is coming. {net}First, how a network becomes a program, and a question about it becomes a question of equivalence. {stack}Then why real packets need a stack. ` +
    `{lang}Then the language, and three laws about push and pop. {proc}Then the main part: a procedure in three steps, one for each law, that decides equivalence using only finite automata. ` +
    `{rest}And at the end: headers, cost, counterexamples, and axioms.` },
  { id: 'title', chapter: '', pre: 0.6, post: 1.0, text:
    `{title}Stack Cat: {sub}infinite state network verification.` },

  // ------------------------------------------------------------------------------------------------ networks as programs
  { id: 'net_a', chapter: 'Networks as programs', pre: 1.9, post: 0.6, text:
    `{net}A network is made of switches. {pkt}A packet arrives with a header: a few fields, such as a destination and a port. {rule}A switch looks at some fields, changes some, and sends the packet on to a neighbor. ` +
    `{prog}Net Cat is a language that reads all of this as a program. {field}A field is a variable. {test}A match is a test: it lets the packet through if a field has a given value, and drops it otherwise. ` +
    `{assign}An action is an assignment of a constant to a field. {move}Even the packet's location is a field. Moving it to switch B is an assignment: switch becomes B.` },
  { id: 'net_b', chapter: 'Networks as programs', pre: 0.4, post: 0.6, text:
    `{ops}Programs are combined in three ways. {seq}A dot runs one program and then another. {plus}A plus is a choice: the packet goes both ways, as when a switch forwards it to two neighbors. {star}A star repeats a program any number of times. ` +
    `{const}And there are two constant programs. The program written one passes every packet unchanged. The program written zero drops every packet. {whole}The whole network is then one program: test which switch the packet is on, run that switch's program, and repeat.` },
  { id: 'net_c', chapter: 'Networks as programs', pre: 0.4, post: 0.9, text:
    `{mean}What does a program mean? {rel}It relates each input packet to the packets that can come out: none, one, or several. {equiv}Two programs are equivalent if they relate the same inputs to the same outputs. ` +
    `{why}Equivalence is what verification needs. {reach}To ask whether any packet can get from switch A to switch B: start at A, run the network, and test for B. {zero}If that program is equivalent to zero, no packet gets through. ` +
    `{dec}For Net Cat, a machine can always answer, because a packet has finitely many fields, with finitely many values. {fin}There are only finitely many packets, so a program is a finite-state system.` },

  // ------------------------------------------------------------------------------------------------ why a stack
  { id: 'stack_a', chapter: 'Why a stack', pre: 1.9, post: 0.6, text:
    `{real}Real packets are not that simple. {bytes}On the wire, a packet is a sequence of bytes. {parse}A switch must parse it: take bytes off the front, and put them into fields. ` +
    `{route}In source routing, the packet carries its whole route, and each switch takes off the next hop. {tele}Telemetry adds a record at every hop. {tun}A tunnel wraps the packet in new headers, and unwraps it later. ` +
    `{all}Every one of these adds or removes at the front of the packet. {st}That is a stack.` },
  { id: 'stack_b', chapter: 'Why a stack', pre: 0.4, post: 0.9, text:
    `{nobound}And a stack has no fixed depth. A route can be arbitrarily long. {infinite}So there are infinitely many packets, {gone}and the argument that made Net Cat decidable is gone. ` +
    `{worse}It looks worse than that. {cfl}A machine with a stack and an input can recognize context-free languages, and whether two context-free languages are equal is undecidable. {q}So is there any hope?` },

  // ------------------------------------------------------------------------------------------------ the language
  { id: 'lang_a', chapter: 'StacKAT', pre: 1.9, post: 0.6, text:
    `{pk}In Stack Cat, a packet has two parts: a header, as before, and a stack. {ops}The language adds two operations. {push}Push puts a value on top of the stack. {pop}Pop takes a value off the top, but only if it is the value named. ` +
    `{ok}Pop three, on a stack with three on top, removes it. {bad}Pop five, on the same stack, drops the packet. {empty}So does a pop on an empty stack. {guard}A pop is a test and an action in one.` },
  { id: 'lang_b', chapter: 'StacKAT', pre: 0.4, post: 0.6, text:
    `{sugar}These two are enough. {route}Source routing is one line: pop the top of the stack into the switch field. {short}That is shorthand for a choice: pop one and go to switch one, or pop two and go to switch two, and so on. ` +
    `{finite}That works because there are finitely many values. {parse}Parsing a header pops into one field after another. {tele}And telemetry is a push.` },
  { id: 'laws', chapter: 'StacKAT', pre: 0.5, post: 0.7, text:
    `{mean}A program still relates input packets to output packets, and equivalence is as before. {but}But push and pop interact, and three laws say how. ` +
    `{l1}One. Push a value and then pop the same value: nothing has happened. That is equivalent to the program one. {l2}Two. Push a value and then pop a different value: the pop fails. That is equivalent to zero. ` +
    `{l3}The third is subtle. Pop a value and then push it back. {not1}That is not equivalent to the program one, because it drops every packet that does not have that value on top. {le}But when it does not drop the packet, it changes nothing. ` +
    `{abs}So a choice between the program one and this pop-then-push is just the program one.` },
  { id: 'puzzle', chapter: 'StacKAT', pre: 0.5, post: 0.6, text:
    `{back}Now back to the two programs from the start. {p1}Push A any number of times, then pop A any number of times. {cancel}By the first law, each push cancels against a pop. {net}If there were more pushes, some pushes are left. If there were more pops, some pops are left. ` +
    `{p2}That is what the second program does. {eq}So they are equivalent. {p3}Here is a third program: push A an even number of times, then pop it an even number of times. {neq}It is not equivalent to the first. ` +
    `{wit}The first can take a stack that holds a single A, and empty it. The third cannot. {goal}We want a machine to tell such cases apart, for any two programs.` },
  { id: 'cool_surprise', chapter: 'StacKAT', pre: 0.5, post: 0.9, text:
    `{ans}And it can. {dec}Equivalence of Stack Cat programs is decidable. {surprise}This is the surprising part. {unb}The stack is unbounded, and programs may use it in any way they like, {yet}yet the question can always be answered. ` +
    `{key}What makes it possible is that a program has no input other than the packet itself. {scratch}The stack is not working memory for reading some other input. It is the input, and it is the output.` },

  // ------------------------------------------------------------------------------------------------ the decision procedure
  { id: 'proc_a', chapter: 'Deciding equivalence', pre: 1.9, post: 0.6, text:
    `{start}We start with programs that only push and pop. Headers come back later. {regex}Such a program is a regular expression, whose letters are pushes and pops. {traces}Each word it matches is a trace: one sequence of pushes and pops that the program can perform. ` +
    `{aut}A regular expression can be turned into a finite automaton that accepts exactly its traces, {compare}and a machine can compare two finite automata. {problem}But the traces are not the meaning. ` +
    `{ex}Take a choice between the program one, and a pop followed by a push of the same value. It has two traces. The program one alone has a single trace, the empty one. Yet by the third law, they mean the same. {plan}So before comparing, we bring each automaton to a normal form, in three steps, one for each law.` },
  { id: 'step1', chapter: 'Deciding equivalence', pre: 0.5, post: 0.6, text:
    `{s1}Step one is to cancel. It uses the first law. {path}Wherever the automaton can do a push and then a pop of the same value, possibly with silent steps in between, {eps}add a shortcut between the same two states that does nothing. {rep}Repeat until nothing new appears. ` +
    `{ex}In our automaton, the loop pushes A, and the next edge pops A. So we add a silent edge beside them. {lang}The automaton now accepts every trace it had, and also every trace in which matching pushes and pops have been cancelled.` },
  { id: 'step2', chapter: 'Deciding equivalence', pre: 0.5, post: 0.6, text:
    `{s2}Step two is to filter. {look}Take a trace in which a push is followed directly by a pop. {two}If the two values differ, the trace drops every packet, by the second law. It contributes nothing. ` +
    `{same}If they are the same, step one has already added the trace without them. It is redundant. {filter}So we keep only the traces with no such pair: all pops come before all pushes. {inter}On automata, that is an intersection with the automaton for pops, then pushes: a standard construction. ` +
    `{res}For our program, the result has two branches: pops only, or pushes only. {p2}And that is exactly the automaton of the second program. {done}The two programs from the start of the video are equivalent, and this time a procedure has checked it.` },
  { id: 'cool_two', chapter: 'Deciding equivalence', pre: 0.5, post: 0.8, text:
    `{note}Notice what we did. {fin}We changed a finite automaton, and compared it with another. {agree}When two automata agree after these steps, the programs are equivalent. {more}But when they disagree, we cannot conclude anything yet. Two steps are not always enough.` },
  { id: 'step3_a', chapter: 'Deciding equivalence', pre: 0.5, post: 0.6, text:
    `{third}Here is the first program with its halves swapped: pop A any number of times, then push A any number of times. {eq}It is equivalent to the other two. ` +
    `{stuck}But steps one and two leave its automaton as it is. {still}It still accepts a pop followed by a push, which the others do not. {law}This is the third law at work: a pop and then a push of the same value is hidden inside the program one. ` +
    `{cant}We cannot simply delete such a pair. On its own, a pop and then a push still drops some packets. Deleting is only right when the trace without the pair is also there. {add}So again we add instead. {ins}In every trace, between the pops and the pushes, insert a pop and a push of the same value. Do it for every value, and again and again.` },
  { id: 'step3_b', chapter: 'Deciding equivalence', pre: 0.6, post: 0.8, text:
    `{mean}Why is this the right thing to add? {read}Think about what a trace of pops and then pushes says. Take: pop one, push four. {says}It says: a stack with a one on top becomes the same stack with a four on top. {below}Whatever lies below is untouched. So this single trace stands for many pairs of stacks. ` +
    `{spell}Now insert a pop and a push of a two. The new trace says the same thing, but only for stacks that have a two below. {sound}That is a special case of what we had, so adding it changes nothing in meaning. ` +
    `{exact}With every insertion added, there is one trace for each whole input stack, together with its whole output stack. {then}And then two programs have the same traces exactly when they relate the same stacks.` },
  { id: 'step3_c', chapter: 'Deciding equivalence', pre: 0.5, post: 0.6, text:
    `{prob}There is a problem. {nest}The inserted pairs nest, like brackets: pop A, pop B, push B, push A. {notreg}No finite automaton accepts such a language. {trick}The way out is to change how a trace is read. ` +
    `{mid}Start in the middle, where the pops end and the pushes begin, and read outwards, {pairs}one pop and one push at a time, as a pair. {zip}We call this zipping. {letter}Each pair is one letter of a new alphabet. {ex}Here is a trace, and here it is zipped. ` +
    `{doneph}When one side runs out, a placeholder fills in. {lossless}Nothing is lost: a zipped trace can be unzipped again. {front}Now the inserted pairs are no longer in the middle. They are at the front, one after another. {loop}And that is just a loop at the start.` },
  { id: 'step3_d', chapter: 'Deciding equivalence', pre: 0.5, post: 0.6, text:
    `{auto}An automaton can be zipped too. The zipped automaton starts in the middle of a run of the original. {back}Each of its steps goes one step backwards through the pops, and one step forwards through the pushes. {z3}Here is the zipped automaton of the swapped program. ` +
    `{z1}And here is the one for the first program, after steps one and two. {differ}They differ in one loop: the swapped program can begin with matching pairs. {pre}Step three puts a loop of matching pairs on the start state of every automaton. ` +
    `{same}For the swapped program, that changes nothing. For the first, it adds the missing loop. Now the two accept the same language. {eq}So the swapped program is equivalent to the first two.` },
  { id: 'thm', chapter: 'Deciding equivalence', pre: 0.6, post: 0.9, text:
    `{thm}That is the whole procedure. {t1}Turn each program into an automaton. {t2}Cancel: add shortcuts where a push meets its pop. {t3}Filter: keep the traces that pop before they push. {t4}Zip, and put the loop of matching pairs in front. ` +
    `{iff}Then two programs are equivalent if and only if the two automata accept the same language. {note}Every step is an elementary construction on finite automata. {inf}The infinitely many stacks never had to be listed.` },

  // ------------------------------------------------------------------------------------------------ headers, cost, counterexamples
  { id: 'full_a', chapter: 'Headers, cost, counterexamples', pre: 1.9, post: 0.6, text:
    `{hdr}Now put the header fields back. {state}A state of the automaton becomes a pair: the current header, and the part of the program still to run. {finite}There are finitely many headers, and only finitely many parts of the program can be reached, so it is still a finite automaton. ` +
    `{tests}Tests and assignments become silent steps that check or change the header. {pp}Pushes and pops stay as letters. {pairs}Then, for every header at the start and every header at the end, take the traces between them, and normalize as before. ` +
    `{thm}Two programs are equivalent exactly when all of these agree.` },
  { id: 'full_b', chapter: 'Headers, cost, counterexamples', pre: 0.4, post: 0.6, text:
    `{ex}For example, this loop has two branches. The first needs the field F to be one, and pushes a one. The second sets F to two, and pushes a two. {c1}Start with F equal to one, and end with F equal to one: the loop can only have pushed ones. {c2}From two to two, only twos. ` +
    `{each}Each pair of headers is compared on its own.` },
  { id: 'cost', chapter: 'Headers, cost, counterexamples', pre: 0.5, post: 0.6, text:
    `{cost}What does this cost? {ps}Without headers, the problem is complete for polynomial space, the same as for regular expressions. {exp}With headers, it is complete for exponential space, when programs may use any number of fields. ` +
    `{impl}The implementation, which runs in a web browser, goes through the pairs of headers one by one. That is its bottleneck. {sym}A symbolic procedure is future work.` },
  { id: 'cex', chapter: 'Headers, cost, counterexamples', pre: 0.5, post: 0.9, text:
    `{cex}When two programs are not equivalent, the procedure says why. {word}The two automata differ on some word. {unzip}Unzip it. Its pops spell an input stack, and its pushes spell an output stack. ` +
    `{pair}With the two headers, that is an input packet and an output packet {differ}that one program relates, and the other does not. {ex}For the program with even numbers of pushes and pops, one such pair is: a stack holding a single A going in, and the empty stack coming out.` },

  // ------------------------------------------------------------------------------------------------ axioms
  { id: 'ax', chapter: 'Axioms', pre: 1.9, post: 0.9, text:
    `{ax}One more result. {alg}The laws can be used as axioms, to prove equivalences by algebra. {ka}Start from Klay-nee algebra, the standard axioms for regular expressions. {a1}Add the first law, {a2}and the second. ` +
    `{comp1}These are complete for the first two steps. {a3}For the third law, what is proved uses an extra family of rules, more complicated than the law. {comp2}With them, every equivalence between programs that push and pop has a proof from the axioms. ` +
    `{open}Whether the third law by itself would be enough is an open question. The authors conjecture that it is not.` },

  // ------------------------------------------------------------------------------------------------ close
  { id: 'recap', chapter: 'Looking back', pre: 1.9, post: 0.7, text:
    `{r1}A network is a program, and questions about it are questions of equivalence. {r2}Real packets need a stack, which makes the state space infinite. {r3}Stack Cat adds push and pop, ` +
    `{r4}and three laws about them become three steps on a finite automaton: cancel, filter, zip. {r5}After those steps, equivalent programs have automata that accept the same language, and so equivalence is decidable. {r6}That is a foundation for checking networks that parse, tunnel, and route by a stack.` },
  { id: 'end', chapter: 'Looking back', pre: 0.5, post: 3.0, text:
    `{title}Stack Cat: infinite state network verification. {paper}The paper and its appendix have the proofs, the constructions in full, the complexity bounds, and the axiomatization.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "hook",
   "chapter": "",
   "start": 0.0,
   "dur": 64.86,
   "pre": 0.8,
   "post": 0.7,
   "audio": 63.36,
   "cues": {
    "two": 0.8,
    "p1": 5.36,
    "star": 11.44,
    "notwhile": 19.88,
    "trace": 22.4,
    "run": 28.64,
    "p2": 31.84,
    "eq": 37.04,
    "how": 42.24,
    "inf": 44.32,
    "film": 49.52,
    "hand": 56.24,
    "algo": 59.787
   }
  },
  {
   "id": "roadmap",
   "chapter": "",
   "start": 64.86,
   "dur": 30.62,
   "pre": 0.3,
   "post": 0.8,
   "audio": 29.52,
   "cues": {
    "coming": 0.3,
    "net": 2.14,
    "stack": 8.7,
    "lang": 11.74,
    "proc": 16.06,
    "rest": 24.54
   }
  },
  {
   "id": "title",
   "chapter": "",
   "start": 95.48,
   "dur": 5.84,
   "pre": 0.6,
   "post": 1,
   "audio": 4.24,
   "cues": {
    "title": 0.6,
    "sub": 1.92
   }
  },
  {
   "id": "net_a",
   "chapter": "Networks as programs",
   "start": 101.32,
   "dur": 39.22,
   "pre": 1.9,
   "post": 0.6,
   "audio": 36.72,
   "cues": {
    "net": 1.9,
    "pkt": 4.22,
    "rule": 9.98,
    "prog": 15.5,
    "field": 19.42,
    "test": 21.34,
    "assign": 28.22,
    "move": 31.74
   }
  },
  {
   "id": "net_b",
   "chapter": "Networks as programs",
   "start": 140.54,
   "dur": 35.24,
   "pre": 0.4,
   "post": 0.6,
   "audio": 34.24,
   "cues": {
    "ops": 0.4,
    "seq": 3.28,
    "plus": 6.56,
    "star": 13.2,
    "const": 16.827,
    "whole": 26.8
   }
  },
  {
   "id": "net_c",
   "chapter": "Networks as programs",
   "start": 175.78,
   "dur": 43.14,
   "pre": 0.4,
   "post": 0.9,
   "audio": 41.84,
   "cues": {
    "mean": 0.4,
    "rel": 2.48,
    "equiv": 8.96,
    "why": 13.84,
    "reach": 16.907,
    "zero": 24.8,
    "dec": 29.2,
    "fin": 36.96
   }
  },
  {
   "id": "stack_a",
   "chapter": "Why a stack",
   "start": 218.92,
   "dur": 31.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 29.44,
   "cues": {
    "real": 1.9,
    "bytes": 4.46,
    "parse": 7.74,
    "route": 12.86,
    "tele": 18.86,
    "tun": 21.66,
    "all": 25.98,
    "st": 29.9
   }
  },
  {
   "id": "stack_b",
   "chapter": "Why a stack",
   "start": 250.86,
   "dur": 25.46,
   "pre": 0.4,
   "post": 0.9,
   "audio": 24.16,
   "cues": {
    "nobound": 0.4,
    "infinite": 5.6,
    "gone": 7.973,
    "worse": 11.653,
    "cfl": 13.28,
    "q": 22.8
   }
  },
  {
   "id": "lang_a",
   "chapter": "StacKAT",
   "start": 276.32,
   "dur": 31.86,
   "pre": 1.9,
   "post": 0.6,
   "audio": 29.36,
   "cues": {
    "pk": 1.9,
    "ops": 8.06,
    "push": 10.62,
    "pop": 13.82,
    "ok": 18.54,
    "bad": 22.46,
    "empty": 26.22,
    "guard": 28.62
   }
  },
  {
   "id": "lang_b",
   "chapter": "StacKAT",
   "start": 308.18,
   "dur": 25.72,
   "pre": 0.4,
   "post": 0.6,
   "audio": 24.72,
   "cues": {
    "sugar": 0.4,
    "route": 2.4,
    "short": 7.76,
    "finite": 16.08,
    "parse": 19.627,
    "tele": 23.04
   }
  },
  {
   "id": "laws",
   "chapter": "StacKAT",
   "start": 333.9,
   "dur": 47.04,
   "pre": 0.5,
   "post": 0.7,
   "audio": 45.84,
   "cues": {
    "mean": 0.5,
    "but": 6.74,
    "l1": 11.14,
    "l2": 18.9,
    "l3": 26.1,
    "not1": 30.26,
    "le": 36.98,
    "abs": 40.5
   }
  },
  {
   "id": "puzzle",
   "chapter": "StacKAT",
   "start": 380.94,
   "dur": 42.38,
   "pre": 0.5,
   "post": 0.6,
   "audio": 41.28,
   "cues": {
    "back": 0.5,
    "p1": 3.673,
    "cancel": 8.42,
    "net": 12.26,
    "p2": 18.14,
    "eq": 20.5,
    "p3": 22.54,
    "neq": 29.38,
    "wit": 31.7,
    "goal": 37.46
   }
  },
  {
   "id": "cool_surprise",
   "chapter": "StacKAT",
   "start": 423.32,
   "dur": 28.44,
   "pre": 0.5,
   "post": 0.9,
   "audio": 27.04,
   "cues": {
    "ans": 0.5,
    "dec": 1.86,
    "surprise": 5.3,
    "unb": 7.647,
    "yet": 12.26,
    "key": 15.06,
    "scratch": 20.26
   }
  },
  {
   "id": "proc_a",
   "chapter": "Deciding equivalence",
   "start": 451.76,
   "dur": 53.3,
   "pre": 1.9,
   "post": 0.6,
   "audio": 50.8,
   "cues": {
    "start": 1.9,
    "regex": 7.26,
    "traces": 12.38,
    "aut": 19.02,
    "compare": 25.1,
    "problem": 28.54,
    "ex": 31.047,
    "plan": 45.58
   }
  },
  {
   "id": "step1",
   "chapter": "Deciding equivalence",
   "start": 505.06,
   "dur": 34.46,
   "pre": 0.5,
   "post": 0.6,
   "audio": 33.36,
   "cues": {
    "s1": 0.5,
    "path": 4.98,
    "eps": 11.7,
    "rep": 15.62,
    "ex": 18.26,
    "lang": 25.94
   }
  },
  {
   "id": "step2",
   "chapter": "Deciding equivalence",
   "start": 539.52,
   "dur": 47.9,
   "pre": 0.5,
   "post": 0.6,
   "audio": 46.8,
   "cues": {
    "s2": 0.5,
    "look": 2.82,
    "two": 6.82,
    "same": 13.62,
    "filter": 19.54,
    "inter": 25.34,
    "res": 32.1,
    "p2": 37.54,
    "done": 41.3
   }
  },
  {
   "id": "cool_two",
   "chapter": "Deciding equivalence",
   "start": 587.42,
   "dur": 18.34,
   "pre": 0.5,
   "post": 0.8,
   "audio": 17.04,
   "cues": {
    "note": 0.5,
    "fin": 2.18,
    "agree": 6.26,
    "more": 11.22
   }
  },
  {
   "id": "step3_a",
   "chapter": "Deciding equivalence",
   "start": 605.76,
   "dur": 52.3,
   "pre": 0.5,
   "post": 0.6,
   "audio": 51.2,
   "cues": {
    "third": 0.5,
    "eq": 9.38,
    "stuck": 11.7,
    "still": 15.62,
    "law": 20.5,
    "cant": 27.86,
    "add": 39.78,
    "ins": 42.18
   }
  },
  {
   "id": "step3_b",
   "chapter": "Deciding equivalence",
   "start": 658.06,
   "dur": 48.92,
   "pre": 0.6,
   "post": 0.8,
   "audio": 47.52,
   "cues": {
    "mean": 0.6,
    "read": 3.2,
    "says": 9.64,
    "below": 15.16,
    "spell": 21.8,
    "sound": 30.08,
    "exact": 35.16,
    "then": 42.6
   }
  },
  {
   "id": "step3_c",
   "chapter": "Deciding equivalence",
   "start": 706.98,
   "dur": 48.54,
   "pre": 0.5,
   "post": 0.6,
   "audio": 47.44,
   "cues": {
    "prob": 0.5,
    "nest": 1.98,
    "notreg": 9.26,
    "trick": 12.5,
    "mid": 15.78,
    "pairs": 20.9,
    "zip": 24.5,
    "letter": 26.46,
    "ex": 29.46,
    "doneph": 32.34,
    "lossless": 35.94,
    "front": 39.86,
    "loop": 45.567
   }
  },
  {
   "id": "step3_d",
   "chapter": "Deciding equivalence",
   "start": 755.52,
   "dur": 45.1,
   "pre": 0.5,
   "post": 0.6,
   "audio": 44.0,
   "cues": {
    "auto": 0.5,
    "back": 7.3,
    "z3": 13.78,
    "z1": 17.3,
    "differ": 22.02,
    "pre": 27.38,
    "same": 32.58,
    "eq": 41.06
   }
  },
  {
   "id": "thm",
   "chapter": "Deciding equivalence",
   "start": 800.62,
   "dur": 32.7,
   "pre": 0.6,
   "post": 0.9,
   "audio": 31.2,
   "cues": {
    "thm": 0.6,
    "t1": 2.68,
    "t2": 5.56,
    "t3": 9.8,
    "t4": 14.2,
    "iff": 17.88,
    "note": 24.28,
    "inf": 28.44
   }
  },
  {
   "id": "full_a",
   "chapter": "Headers, cost, counterexamples",
   "start": 833.32,
   "dur": 39.94,
   "pre": 1.9,
   "post": 0.6,
   "audio": 37.44,
   "cues": {
    "hdr": 1.9,
    "state": 4.3,
    "finite": 11.02,
    "tests": 19.5,
    "pp": 24.78,
    "pairs": 27.66,
    "thm": 35.38
   }
  },
  {
   "id": "full_b",
   "chapter": "Headers, cost, counterexamples",
   "start": 873.26,
   "dur": 24.92,
   "pre": 0.4,
   "post": 0.6,
   "audio": 23.92,
   "cues": {
    "ex": 0.4,
    "c1": 11.84,
    "c2": 18.72,
    "each": 21.44
   }
  },
  {
   "id": "cost",
   "chapter": "Headers, cost, counterexamples",
   "start": 898.18,
   "dur": 26.22,
   "pre": 0.5,
   "post": 0.6,
   "audio": 25.12,
   "cues": {
    "cost": 0.5,
    "ps": 2.46,
    "exp": 8.82,
    "impl": 15.22,
    "sym": 22.98
   }
  },
  {
   "id": "cex",
   "chapter": "Headers, cost, counterexamples",
   "start": 924.4,
   "dur": 32.76,
   "pre": 0.5,
   "post": 0.9,
   "audio": 31.36,
   "cues": {
    "cex": 0.5,
    "word": 4.98,
    "unzip": 7.94,
    "pair": 14.34,
    "differ": 18.58,
    "ex": 21.993
   }
  },
  {
   "id": "ax",
   "chapter": "Axioms",
   "start": 957.16,
   "dur": 40.4,
   "pre": 1.9,
   "post": 0.9,
   "audio": 37.6,
   "cues": {
    "ax": 1.9,
    "alg": 3.58,
    "ka": 8.78,
    "a1": 13.98,
    "a2": 15.287,
    "comp1": 16.78,
    "a3": 19.58,
    "comp2": 26.14,
    "open": 32.46
   }
  },
  {
   "id": "recap",
   "chapter": "Looking back",
   "start": 997.56,
   "dur": 35.88,
   "pre": 1.9,
   "post": 0.7,
   "audio": 33.28,
   "cues": {
    "r1": 1.9,
    "r2": 7.26,
    "r3": 11.9,
    "r4": 14.38,
    "r5": 21.58,
    "r6": 29.58
   }
  },
  {
   "id": "end",
   "chapter": "Looking back",
   "start": 1033.44,
   "dur": 15.66,
   "pre": 0.5,
   "post": 3,
   "audio": 12.16,
   "cues": {
    "title": 0.5,
    "paper": 4.9
   }
  }
 ],
 "total": 1049.1
};

// ==== src/scenes/common.js ====
// Shared pieces of the StacKAT film, as window.SX. Loaded after engine.js, before the scene files. Everything here
// only builds elements and puts keys on the scene's timeline `tl`; nothing is visible until a time says so.
// Coordinates are stage pixels (1920 x 1080). Colours follow SCENES.md: amber C.pat = the stack and push/pop, cyan
// C.bind = header fields and tests/assignments on them, green C.good = established, red C.bad = dropped/refuted.
//
// ---- constants -----------------------------------------------------------------------------------------------
//   SX.CX = 960 (stage centre), SX.RAIL = 160 (the left rail), SX.LINE = 3 (drawing line width).
//
// ---- type ----------------------------------------------------------------------------------------------------
//   SX.LABEL(size) / SX.SERIF(size) / SX.MONO(size): style objects (small caps sans in C.dim, serif in C.ink, mono
//     in C.code without ligatures). Pass them to box(), or Object.assign(SX.LABEL(32), {color: C.ink}).
//   SX.cline(root, cx, y, parts, style) -> {root, parts}: one line centred on cx, top at y, made of parts
//     [[text, colour|null], ...]; each part is its own inline span (fade, strike or colour it by itself).
//   SX.lline(root, x, y, parts, style) -> {root, parts}: the same, left edge at x.
//   SX.clabel(root, cx, y, text, size=32, colour) -> el   centred small caps label.
//   SX.cserif(root, cx, y, text, size=56, colour) -> el   centred serif line.
//   SX.note(tl, root, x, y, text, at, out, {size=32, color=C.dim, align='center'|'left', dy=10}) -> el
//     a label that rises in at `at` and leaves at `out` (out may be null: it stays). x is its centre, or its
//     left edge with align 'left'.
//   SX.strikeEl(tl, el, at, {out, faint=true}) -> {line, undo(at)}: the neutral grey strike through an element
//     (a span of cline, a label); its text goes C.faint. undo(at) takes the strike back and restores the colour.
//
// ---- small drawings ------------------------------------------------------------------------------------------
//   SX.svg(root): an SVG layer over the whole stage (engine's svgLayer).
//   SX.tick(tl, svg, x, y, size=48, at, {color=C.good, width=6}) -> {els, hide(at)}  a tick drawn in at `at`.
//   SX.cross(tl, svg, x, y, size=40, at, {color=C.bad, width=6}) -> {els, hide(at)}  a cross drawn in at `at`.
//   SX.dpath(tl, svg, d, {stroke=C.ink, width=3, dash}) -> path el with a `draw` key (0..1) also when dashed
//     (a dashed path is drawn through a mask). Draw with tl.to(p, {draw: 1}, at, dur, E.io); fade with {o}.
//   SX.line(tl, svg, x1, y1, x2, y2, {at, dur=0.5, bend=0, dash, stroke=C.ink, width=3, head=14}) -> {path, head,
//     hide(at)}: an arrow (head=0: a plain line) drawn in at `at` (omit `at` to draw it yourself). bend > 0 bends
//     it to the right of the direction of travel (below for a left-to-right arrow), as engine.arrowPath.
//   SX.arc(tl, svg, x1, x2, y, depth, {at, dur=0.5, stroke=C.ink, width=3, dash, up=false}) -> path
//     a round arc from (x1, y) to (x2, y), bulging `depth` px down (or up), for joining letters of a trace.
//   SX.cell(parent, x, y, w, h, text, {stroke, color, font, radius, width}) -> box el, its text el in ._t
//   SX.flip(tl, textEl, text, at, dur=0.45): a cell's text squeezes, changes, comes back.
//   SX.circleD(x, y, r): an SVG path string for a circle.
//   SX.ctext(parent, cx, cy, text, style, h): a box with text centred on (cx, cy), h px high.
//   SX.dim(tl, els, o, at, dur=0.5): opacity of many elements (or of things with a .root / .g).
//
// ---- programs and traces: SX.prog ----------------------------------------------------------------------------
//   const p = SX.prog(tl, parent, x, y, size, text, {align='left'|'center', at, stagger=0.03, colors, fields})
//   Sets `text` (one line) in mono on a character grid: x, y is the top-left (with align 'center', x is the
//   centre). `push(..)`/`pop(..)` and bare `push`/`pop` are amber (an argument that is a field, e.g. pop(sw), is
//   cyan inside); a test or assignment on a field (`sw==1`, `f := 2`, `dst == 7`) is cyan; `done` is C.dim; a
//   zipped letter `(pop(2), push(3))` / `(done, push(3))` is one part; everything else (`·`, `+`, `*`, `≡`, names,
//   `1`, `0`, brackets) is ink. opts.colors {text: colour} overrides by a part's exact text ({'≡': C.good}).
//   Nothing shows until p.show(at) (or opts.at). Spaces are kept: write traces as 'push(a)  push(a)  pop(a)'.
//   p.parts: [{el, text, kind ('op' push/pop, 'pair' zipped letter, 'field', 'name', 'sym'), col, len}]
//   p.letters: indices of the parts that are letters (push/pop/zipped pairs), in order; p.letter(k) = p.letters[k].
//   A selector `sel` is: an index, an array of indices, a string (every part with that text), a RegExp on the
//   text, a function(part, i), {from, to} (an index range, inclusive), or 'all' (the default where optional).
//   p.show(at, {sel, stagger, rise=14, dur=0.5})      parts rise in, left to right.
//   p.hideParts(sel, at, dur=0.35)                     parts leave upwards.   p.hide(at, dur=0.45)  the whole line.
//   p.dim(sel, o, at, dur=0.4)                          opacity of parts (0.4 = dimmed);  p.light(sel, at) back to 1.
//   p.color(sel, colour, at, dur) / p.recolor(sel, at)  recolour parts / back to their own colours.
//   p.pulse(sel, at, {scale=1.08, dur=0.5})             a part grows a little and back, with a soft neutral box.
//   p.mark(sel, colour, at, {out, fill=0.12, pad=8})    a soft box behind parts in their meaning's colour, or the
//                                                       neutral one with colour C.dim, fill 0.08. Returns the box.
//   p.strike(sel, at, {out, dur=0.4, fade=true}) -> {line, undo(at)}  the grey strike; tokens go C.faint.
//   p.flip(i, text, at)                                 part i squeezes and reads `text` (keep the length).
//   p.append(text, at, {gap=1, stagger}) -> [indices]   more parts after the end (gap spaces), rising in at `at`.
//   p.rect(sel, pad=0) -> {x, y, w, h, cx, cy}          stage rectangle at the build position (moves not included).
//   p.colX(c): stage x of column c.  p.width, p.cw, p.lh, p.cols, p.root.
//   p.to({x, y, s, o}, at, dur=0.8, ease=E.io)          move/scale/fade the whole line (x, y are offsets from where
//                                                       it was built; scale is about its left edge, or its centre
//                                                       with align 'center').
//   Only Fira Code and Source Serif 4 ship with the player. Fira Code has ≡ ≢ ≠ ≤ ∩ ∪ ∈ ∅ ⟨ ⟩ → ↕ … · and ₀–₉;
//   neither font has ⟦ ⟧ ⇒ ⇔ ≫ ⇅, and ⟺ is drawn with SX.iff(size). Never name another font family.
//
// ---- the stack: SX.Stack -------------------------------------------------------------------------------------
//   const s = new SX.Stack(tl, parent, cx, bottom, {items=[] (top first: ['3','1','2'] is [3, 1, 2]), w=96, h=84,
//     gap=10, size=44, rest=false (a taller dim "…" cell at the bottom: the unknown rest), label, labelSize=32,
//     labelColor=C.dim, ghost=false (a dashed amber outline where the bottom cell goes: the empty stack)})
//   The pile of amber cells, centred on cx, its bottom edge at y = bottom; it grows upwards; the label sits under
//   it (bottom + 22 .. bottom + 62). The tick or cross of ok()/fail() needs 80 px right of the pile. Call the
//   methods in time order (they keep count of the cells).
//   s.show(at, {stagger=0.08})   the cells (bottom first), the rest cell, the ghost, the label rise in.
//   s.push(text, at) -> cell     a cell comes down from above onto the top; settled at at + 0.55.
//   s.pop(at) -> cell            the top lifts off and fades (gone by at + 0.5).
//   s.fail(at) -> {els, hide(at)} the top cell shakes once (6 px, no bounce) and a red cross is drawn to its right
//                                (where ok() puts its tick); for an empty stack, over the ghost outline. The cell
//                                stays: pop it or hide it yourself.
//   s.ok(at) -> {els, hide(at)}  a green tick to the right of the top of the pile.
//   s.flip(i, text, at)          the text of cell i (0 = top) changes.
//   s.reset(items, at)           the cells fade out and `items` (top first) fade in instead.
//   s.dim(o, at, dur) / s.hide(at, dur) / s.move(dx, dy, at, dur=0.8) / s.to(props, at, dur, ease) on the group.
//   s.topY() stage y of the top edge of the pile; s.slotRect(i) the rectangle of cell i (0 = top) as it is now
//   counted; s.cells (bottom first), s.labelEl, s.restEl, s.ghostEl, s.g (the group).
//
// ---- automata: SX.Automaton ----------------------------------------------------------------------------------
//   const A = new SX.Automaton(tl, parent, {r=46, size=36 (edge labels), nameSize=34, cx, cy (centre for scale)})
//   A.state(id, x, y, {name=id, start=false, startFrom='left'|'up', startLen=90}) -> A   a circle with its name
//     (serif italic; write subscripts as e₀). Its start arrow belongs to the state and is drawn with it.
//   A.edge(id, from, to, label, {bend=0, side=+1|-1 (which side of the edge the label goes; default: the outside
//     of the bend, or above), dx, dy (label nudge)}) -> A   an arrow between two states, label beside its middle.
//   A.loop(id, state, label, {side='up'|'down'|'left'|'right', dx, dy}) -> A   a self-loop with its label.
//   A.silent(id, from, to, {bend=0, tag (a small caps label, e.g. 'SILENT'), dx, dy}) -> A   dashed, unlabelled.
//   Ids are strings of your choice; the presets use: states 'e', 'e0', 'e1', 'e2' (and 's', 't' for the two-state
//   automaton, 'T', 'L', 'R' for the zipped ones), edges 'from>to', loops 'state@', silent edges 'from~to'.
//   A.draw(id, at, dur=0.5)      draws one element in (a state: circle, name, start arrow; an edge or loop: the
//                                line, its head, then its label). Settled at at + dur + 0.2.
//   A.drawAll(at, {stagger=0.35, except=[], dur=0.5}) -> end time   every element in the order it was added.
//   A.pulse(id, at, {dur=0.6})   the label (or the state's name) grows a little in a soft neutral box, and back.
//   A.mark(id, at, {out, color=C.dim, fill=0.1}) -> el   a soft box behind an edge label / a ring around a state.
//   A.dimEl(id, o, at, dur=0.4) / A.remove(id, at, dur=0.35)    one element's opacity / it leaves.
//   A.dim(o, at, dur) / A.hide(at, dur) / A.move(dx, dy, at, dur=0.8) / A.scale(s, at, dur=0.8)
//   A.to({x, y, s, o}, at, dur, ease) on the whole automaton (scale about opts.cx, cy: the preset's centre).
//   A.travel(id, at, dur=0.8, {reverse=false, color=C.ink, r=11, out}) -> dot   a filled dot moves along an edge
//                                (against the arrow with reverse); it stays at the end until `out`.
//   A.pos(stateId) -> {x, y} stage centre of a state (build position). A.bounds() -> {x0, y0, x1, y1} of
//   everything (estimated from the label lengths). A.el(id) the element record {paths, heads, labels, ...}.
//   Presets (opts: {value='a', size, k=1 (scale of the whole picture, applied as a transform), silent / loop
//   flags below}); each returns an Automaton laid out around (cx, cy); nothing is drawn until you draw it:
//   SX.A1(tl, parent, cx, cy, {silent=false})  e (start) loop push(a); e>e0 pop(a); e0 loop pop(a);
//                                               silent 'e~e0' (an arc under the pop edge) when silent: true.
//                                               ~ 700 x 330 px.
//   SX.A2(tl, parent, cx, cy)  e (start); e>e1 pop(a) up-right, e1@ pop(a) above; e>e2 push(a) down-right,
//                              e2@ push(a) below.  ~ 640 x 650 px.
//   SX.A3(tl, parent, cx, cy)  e (start), e0, e1 in a row, 360 apart; e>e0 pop(a); e0@ pop(a); e0>e1 push(a);
//                              e1@ push(a); e>e1 push(a) an arc below.  ~ 960 x 400 px.
//   SX.PP(tl, parent, cx, cy)  pops, then pushes: s (start) loop pop; s>t push; t loop push.  ~ 560 x 330 px.
//   SX.Z3(tl, parent, cx, cy)  zipped, a tree: T (start, top) loop (pop(a), push(a)); T>L (done, push(a)),
//                              L@ (done, push(a)) below; T>R (pop(a), done), R@ (pop(a), done) below. Labels 34.
//                              States unnamed (opts.names {T, L, R} to name them). ~ 760 x 680 px.
//   SX.Z1(tl, parent, cx, cy, {loop=false})  the same without T's loop; with loop: true the loop 'T@' exists
//                              (draw it later with A.draw('T@', t); drawAll(at, {except: ['T@']}) leaves it out).
//
// ---- the packet header and the title -------------------------------------------------------------------------
//   SX.packetHeader(tl, parent, x, y, fields, {w=150, h=90, gap=14, size=44, names=32}) -> header
//     fields [['sw', 'A'], ['dst', '7'], ...]: cells with their cyan names above (x, y is the top-left of the
//     names; cells start 50 px lower). header.show(at), .flip(i, text, at), .tint(i, at, out) (a neutral tint),
//     .pulse(i, at), .dim(o, at), .hide(at), .move(dx, dy, at, dur), .to(props, at, dur), .vals (cell els),
//     .names, .width, .height, .g, .cellRect(i).
//   SX.titleCard(tl, root, {align='center'|'left', x (centre or left edge), y, size=150, subSize=56, at, subAt,
//     authorsAt, authorSize=32}) -> {title, sub, authors: [line1, line2], bottom}: "StacKAT", the subtitle
//     "Infinite State Network Verification" and the two author lines (the second ends "PLDI 2025"). A time left
//     out means that part is not shown.
//
// ---- rows (roadmaps, recaps, the theorem's list) -------------------------------------------------------------
//   const rows = new SX.Rows(tl, root, {x=160, y, pitch, size=56, numbers=true, titleX=x + 70, back=0.6})
//   rows.row(title, at, {num}) -> row {y, at, parts, add(el), num, title}: a numbered serif row rising in; when a
//     later row arrives, the earlier rows (with everything add()ed to them) step back to opacity `back`.
//   rows.evidence(i, el, at, dy=14) fades `el` in at `at` and adds it to row i.  rows.mid(i): the y of row i's
//     middle (for evidence of another size).  rows.all(): every element.
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
  // a path with a `draw` key, dashed or not
  function dpath(tl, svg, d, { stroke = C.ink, width = LINE, dash } = {}) {
    if (!dash) return path(tl, svg, d, { stroke, width });
    const id = 'sxm' + (++maskN);
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

  // ---- StacKAT text: tokens and their colours -----------------------------------------------------------------
  const SUB = '₀-₉';
  const FIELDS = ['sw', 'dst', 'port', 'f', 'h', 'src', 'f₁', 'f₂', 'f₃', 'h₁', 'h₂'];
  const RE = new RegExp([
    `(\\((?:pop\\([^()]*\\)|done),\\s*(?:push\\([^()]*\\)|done)\\))`,             // 1 a zipped letter
    `((?:push|pop)\\([^()]*\\))`,                                                   // 2 push(..) / pop(..)
    `([A-Za-z_][\\w${SUB}']*\\s*(?:==|:=)\\s*[A-Za-z0-9_${SUB}']+)`,                // 3 a test or an assignment
    `(\\s+)`,                                                                       // 4 space
    `([A-Za-z0-9_${SUB}']+)`,                                                       // 5 a name or a number
    `(.)`,                                                                          // 6 a symbol
  ].join('|'), 'gu');
  // the coloured pieces of a part: [[text, colour], ...]
  function pieces(text, kind, fields) {
    if (kind === 'op') {
      const m = text.match(/^(push|pop)\((.*)\)$/u);
      if (!m) return [[text, C.pat]];
      const argCol = fields.includes(m[2]) ? C.bind : C.pat;
      return [[m[1] + '(', C.pat], [m[2], argCol], [')', C.pat]];
    }
    if (kind === 'pair') {
      const out = [];
      const re = /(push\([^()]*\)|pop\([^()]*\))|(done)|([^]+?)(?=push\(|pop\(|done|$)/gu; let m;
      while ((m = re.exec(text)) && m[0]) out.push([m[0], m[1] ? C.pat : m[2] ? C.dim : C.code]);
      return out;
    }
    if (kind === 'field') return [[text, C.bind]];
    if (text === 'done') return [[text, C.dim]];
    if (text === 'push' || text === 'pop') return [[text, C.pat]];
    return [[text, C.code]];
  }
  function tokens(text, fields = FIELDS) {
    const out = []; let m, col = 0; RE.lastIndex = 0;
    while ((m = RE.exec(text))) {
      const len = [...m[0]].length;
      if (m[4] !== undefined) { col += len; continue; }
      const kind = m[1] ? 'pair' : m[2] ? 'op' : m[3] ? 'field' : m[5] ? 'name' : 'sym';
      out.push({ text: m[0], kind, col, len, pieces: pieces(m[0], kind, fields) });
      col += len;
    }
    return { toks: out, cols: col };
  }
  // fill an element with coloured spans for `text` (no grid: for edge labels)
  function richText(e, text, fields = FIELDS, colors = {}) {
    const { toks } = tokens(text, fields); let col = 0;
    for (const t of toks) {
      if (t.col > col) e.appendChild(document.createTextNode(' '.repeat(t.col - col)));
      for (const [s, c] of t.pieces) { const sp = document.createElement('span'); sp.textContent = s; sp.style.color = colors[t.text] || c; e.appendChild(sp); }
      col = t.col + t.len;
    }
    return e;
  }

  // ---- prog -------------------------------------------------------------------------------------------------------
  class Prog {
    constructor(tl, parent, x, y, size, text, opts = {}) {
      this.tl = tl; this.size = size; this.opts = opts; this.fields = opts.fields || FIELDS; this.colors = opts.colors || {};
      this.cw = charWidth(size); this.lh = Math.round(size * 1.3);
      const { toks, cols } = tokens(text, this.fields);
      this.cols = cols; this.width = cols * this.cw;
      this.x = opts.align === 'center' ? x - this.width / 2 : x; this.y = y;
      this.root = box(parent, this.x, y, { width: this.width + 'px', height: this.lh + 'px', transformOrigin: opts.align === 'center' ? 'center center' : 'left center' });
      this.marks = box(this.root, 0, 0);
      this.layer = box(this.root, 0, 0);
      this.parts = []; this.letters = [];
      for (const t of toks) this._add(t);
      if (opts.at != null) this.show(opts.at, { stagger: opts.stagger });
    }
    _make(t) {
      const e = box(this.layer, t.col * this.cw, 0, Object.assign(MONO(this.size), { lineHeight: this.lh + 'px', whiteSpace: 'pre', opacity: 0 }));
      const subs = t.pieces.map(([s, c]) => { const sp = document.createElement('span'); sp.textContent = s; sp._col = this.colors[t.text] || c; sp.style.color = sp._col; e.appendChild(sp); return sp; });
      return { el: e, subs, text: t.text, kind: t.kind, col: t.col, len: t.len };
    }
    _add(t) {
      const p = this._make(t); this.tl.set(p.el, { o: 0 }, 0);
      this.parts.push(p);
      if (p.kind === 'op' || p.kind === 'pair' || p.text === 'push' || p.text === 'pop') this.letters.push(this.parts.length - 1);
      return this.parts.length - 1;
    }
    letter(k) { return this.letters[k]; }
    ids(sel = 'all') {
      const n = this.parts.length, all = [...Array(n).keys()];
      if (sel === 'all') return all;
      if (typeof sel === 'number') return [sel];
      if (typeof sel === 'string') { const r = all.filter(i => this.parts[i].text === sel); if (!r.length) console.warn('prog: no part', sel); return r; }
      if (sel instanceof RegExp) return all.filter(i => sel.test(this.parts[i].text));
      if (typeof sel === 'function') return all.filter(i => sel(this.parts[i], i));
      if (Array.isArray(sel)) return sel;
      if (sel && sel.from != null) return all.filter(i => i >= sel.from && i <= (sel.to ?? n - 1));
      return [];
    }
    els(sel) { return this.ids(sel).map(i => this.parts[i].el); }
    show(at, { sel = 'all', stagger = 0.03, rise = 14, dur = 0.5 } = {}) {
      this.ids(sel).forEach((i, k) => { const e = this.parts[i].el; this.tl.set(e, { y: rise, o: 0 }, 0); this.tl.to(e, { y: 0, o: 1 }, at + k * stagger, dur, E.out5); });
      return this;
    }
    hideParts(sel, at, dur = 0.35) { for (const e of this.els(sel)) this.tl.to(e, { o: 0, y: -10 }, at, dur, E.in); return this; }
    hide(at, dur = 0.45) { this.tl.to(this.root, { o: 0 }, at, dur, E.in); return this; }
    dim(sel, o, at, dur = 0.4) { for (const e of this.els(sel)) this.tl.to(e, { o }, at, dur); return this; }
    light(sel, at, dur = 0.4) { return this.dim(sel, 1, at, dur); }
    color(sel, col, at, dur = 0.35) { for (const i of this.ids(sel)) for (const s of this.parts[i].subs) this.tl.to(s, { color: col }, at, dur); return this; }
    recolor(sel, at, dur = 0.45) { for (const i of this.ids(sel)) for (const s of this.parts[i].subs) this.tl.to(s, { color: s._col }, at, dur); return this; }
    pulse(sel, at, { scale = 1.08, dur = 0.5 } = {}) {
      for (const e of this.els(sel)) { this.tl.to(e, { s: scale }, at, dur * 0.4, E.out); this.tl.to(e, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      this.mark(sel, C.dim, at, { fill: 0.1, out: at + dur, dur: dur * 0.4 });
      return this;
    }
    rect(sel, pad = 0) {
      const ps = this.ids(sel).map(i => this.parts[i]);
      const c0 = Math.min(...ps.map(p => p.col)), c1 = Math.max(...ps.map(p => p.col + p.len));
      const x = this.x + c0 * this.cw - pad, w = (c1 - c0) * this.cw + 2 * pad;
      return { x, y: this.y - pad * 0.4, w, h: this.lh + pad * 0.8, cx: x + w / 2, cy: this.y + this.lh / 2 };
    }
    colX(c) { return this.x + c * this.cw; }
    mark(sel, color, at, { dur = 0.4, pad = 8, out = null, fill = 0.12 } = {}) {
      const r = this.rect(sel, pad);
      const m = box(this.marks, r.x - this.x, this.lh * 0.08 - pad * 0.4, { width: r.w + 'px', height: (this.lh * 0.84 + pad * 0.8) + 'px', borderRadius: '10px', background: alpha(color, fill), boxShadow: `inset 0 0 0 1.5px ${alpha(color, 0.5)}`, transformOrigin: 'left center' });
      this.tl.set(m, { sx: 0.2, o: 0 }, 0); this.tl.to(m, { sx: 1, o: 1 }, at, dur, E.out5);
      if (out != null) this.tl.to(m, { o: 0 }, out, 0.35);
      return m;
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
    flip(i, text, at, dur = 0.45) {
      const old = this.parts[i], { toks } = tokens(text, this.fields);
      const t = toks[0] || { text, kind: 'name', len: [...text].length, pieces: [[text, C.code]] };
      const n = this._make(Object.assign({}, t, { col: old.col }));
      this.tl.set(n.el, { o: 0 }, 0);
      this.tl.to(old.el, { sy: 0.05 }, at, dur * 0.4, E.in); this.tl.set(old.el, { o: 0 }, at + dur * 0.4);
      this.tl.set(n.el, { o: 1, sy: 0.05 }, at + dur * 0.4); this.tl.to(n.el, { sy: 1 }, at + dur * 0.4, dur * 0.6, E.out);
      this.parts[i] = n;
      return n;
    }
    append(text, at, { gap = 1, stagger = 0.03 } = {}) {
      const { toks, cols } = tokens(text, this.fields), base = this.cols + gap, idx = [];
      for (const t of toks) idx.push(this._add(Object.assign({}, t, { col: t.col + base })));
      this.cols = base + cols; this.width = this.cols * this.cw; this.root.style.width = this.width + 'px';
      this.show(at, { sel: idx, stagger });
      return idx;
    }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.root, props, at, dur, ease); return this; }
  }
  const prog = (tl, parent, x, y, size, text, opts) => new Prog(tl, parent, x, y, size, text, opts);

  // ---- the stack ----------------------------------------------------------------------------------------------
  class Stack {
    constructor(tl, parent, cx, bottom, { items = [], w = 96, h = 84, gap = 10, size = 44, rest = false, restH, label, labelSize = 32, labelColor = C.dim, ghost = false } = {}) {
      Object.assign(this, { tl, cx, bottom, w, h, gap, size });
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${cx}px ${bottom}px` });
      this.restH = rest ? (restH || Math.round(h * 1.35)) : 0;
      this.base = bottom - (rest ? this.restH + gap : 0);   // the bottom edge of slot 0
      this.cells = []; this.initial = [];
      if (rest) {
        this.restEl = cell(this.g, cx - w / 2, bottom - this.restH, w, this.restH, '…', { stroke: C.pat, color: C.dim, font: MONO(Math.round(size * 1.4)) });
        tl.set(this.restEl, { o: 0 }, 0);
      }
      if (ghost) {
        this.ghostEl = box(this.g, cx - w / 2, this.base - h, { width: w + 'px', height: h + 'px', borderRadius: '14px', border: `3px dashed ${alpha(C.pat, 0.7)}` });
        tl.set(this.ghostEl, { o: 0 }, 0);
      }
      [...items].reverse().forEach(t => { const c = this._make(t, this.cells.length); tl.set(c, { o: 0 }, 0); this.cells.push(c); this.initial.push(c); });
      if (label) {
        this.labelEl = clabel(this.g, cx, bottom + 22, label, labelSize, labelColor);
        tl.set(this.labelEl, { o: 0 }, 0);
      }
      this.svg = svgLayer(this.g);
    }
    slotY(i) { return this.base - this.h - i * (this.h + this.gap); }
    _make(text, i) { return cell(this.g, this.cx - this.w / 2, this.slotY(i), this.w, this.h, text, { stroke: C.pat, font: MONO(this.size) }); }
    show(at, { stagger = 0.08 } = {}) {
      let k = 0;
      if (this.restEl) fadeIn(this.tl, this.restEl, at + stagger * k++, 0.5, 14);
      if (this.ghostEl) fadeIn(this.tl, this.ghostEl, at + stagger * k++, 0.5, 14);
      for (const c of this.initial) fadeIn(this.tl, c, at + stagger * k++, 0.5, 14);
      if (this.labelEl) fadeIn(this.tl, this.labelEl, at + stagger * k + 0.1, 0.5, 10);
      return this;
    }
    push(text, at) {
      const c = this._make(text, this.cells.length); this.cells.push(c);
      this.tl.set(c, { y: -90, o: 0 }, 0); this.tl.to(c, { y: 0 }, at, 0.55, E.out5); this.tl.to(c, { o: 1 }, at, 0.3, E.out);
      return c;
    }
    pop(at) {
      const c = this.cells.pop();
      if (!c) { console.warn('Stack.pop: empty'); return null; }
      this.tl.to(c, { y: -80 }, at, 0.5, E.in); this.tl.to(c, { o: 0 }, at + 0.1, 0.4, E.in);
      return c;
    }
    topY() { return this.cells.length ? this.slotY(this.cells.length - 1) : this.base - this.h; }
    slotRect(i) { const j = this.cells.length - 1 - i; const y = this.slotY(Math.max(0, j)); return { x: this.cx - this.w / 2, y, w: this.w, h: this.h, cx: this.cx, cy: y + this.h / 2 }; }
    fail(at) {
      const c = this.cells[this.cells.length - 1];
      if (c) { this.tl.to(c, { x: 6 }, at, 0.08, E.out); this.tl.to(c, { x: -6 }, at + 0.08, 0.1, E.io); this.tl.to(c, { x: 0 }, at + 0.18, 0.1, E.io); }
      // beside the top cell, where a tick would go; on the ghost outline of an empty stack
      const y = this.topY() + this.h / 2, x = c ? this.cx + this.w / 2 + 50 : this.cx;
      return crossM(this.tl, this.svg, x, y, c ? 40 : Math.min(this.w, this.h) * 0.62, at + 0.15, { width: 7 });
    }
    ok(at) { return tickM(this.tl, this.svg, this.cx + this.w / 2 + 50, this.topY() + this.h / 2, 48, at, { width: 7 }); }
    flip(i, text, at) { const c = this.cells[this.cells.length - 1 - i]; flip(this.tl, c._t, text, at); return this; }
    reset(items, at) {
      for (const c of this.cells) this.tl.to(c, { o: 0 }, at, 0.3, E.in);
      this.cells = [];
      [...items].reverse().forEach(t => { const c = this._make(t, this.cells.length); this.tl.set(c, { o: 0 }, 0); this.tl.to(c, { o: 1 }, at + 0.3, 0.4); this.cells.push(c); });
      return this;
    }
    dim(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    move(dx, dy, at, dur = 0.8) { this.tl.to(this.g, { x: dx, y: dy }, at, dur, E.io); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
  }

  // ---- automata -------------------------------------------------------------------------------------------------
  class Automaton {
    constructor(tl, parent, { r = 46, size = 36, nameSize = 34, cx = CX, cy = H / 2 } = {}) {
      Object.assign(this, { tl, r, size, nameSize, cx, cy });
      this.g = box(parent, 0, 0, { width: W + 'px', height: H + 'px', transformOrigin: `${cx}px ${cy}px` });
      this.svg = svgLayer(this.g);
      this.lay = box(this.g, 0, 0, { width: W + 'px', height: H + 'px' });
      this.states = new Map(); this.items = new Map(); this.order = [];
      this.lh = Math.round(size * 1.3);
      this.boxes = [];   // label rectangles, for bounds()
    }
    _item(id, rec) { if (this.items.has(id)) console.warn('automaton: duplicate id', id); rec.id = id; rec.paths = rec.paths || []; rec.heads = rec.heads || []; rec.labels = rec.labels || []; this.items.set(id, rec); this.order.push(id); return rec; }
    el(id) { const r = this.items.get(id); if (!r) console.warn('automaton: no element', id); return r; }
    pos(id) { const s = this.states.get(id); return { x: s.x, y: s.y }; }
    // a label of `text` centred on (x, y); returns {e, w, h}
    _label(text, x, y, { size = this.size, style } = {}) {
      const h = Math.round(size * 1.3), w = [...text].length * charWidth(size);
      const e = box(this.lay, x - w / 2 - 20, y - h / 2, Object.assign(MONO(size), { width: (w + 40) + 'px', height: h + 'px', lineHeight: h + 'px', textAlign: 'center', whiteSpace: 'pre', transformOrigin: 'center center' }, style || {}));
      if (style && style.textTransform) e.textContent = text; else richText(e, text);
      this.tl.set(e, { o: 0 }, 0);
      this.boxes.push({ x0: x - w / 2, y0: y - h / 2, x1: x + w / 2, y1: y + h / 2 });
      return { e, w, h, x, y };
    }
    state(id, x, y, { name = id, start = false, startFrom = 'left', startLen = 90 } = {}) {
      const r = this.r;
      this.states.set(id, { x, y });
      const c = path(this.tl, this.svg, circleD(x, y, r), { stroke: C.ink, width: LINE });
      const nm = box(this.lay, x - 100, y - r, Object.assign(SERIF(this.nameSize), { width: '200px', height: 2 * r + 'px', display: 'flex', alignItems: 'center', justifyContent: 'center', fontStyle: 'italic', whiteSpace: 'pre', transformOrigin: 'center center' }), name);
      this.tl.set(nm, { o: 0 }, 0);
      const rec = { kind: 'state', paths: [c], labels: name ? [nm] : [], x, y };
      if (!name) nm.remove();
      if (start) {
        const [x1, y1, x2, y2] = startFrom === 'up' ? [x, y - r - startLen - 6, x, y - r - 6] : [x - r - startLen - 6, y, x - r - 6, y];
        const a = line(this.tl, this.svg, x1, y1, x2, y2, {});
        rec.start = a;
        this.boxes.push({ x0: Math.min(x1, x2), y0: Math.min(y1, y2) - 8, x1: Math.max(x1, x2), y1: Math.max(y1, y2) + 8 });
      }
      this.boxes.push({ x0: x - r, y0: y - r, x1: x + r, y1: y + r });
      this._item(id, rec);
      return this;
    }
    // where a label of size w x h goes beside the point (mx, my) on the side given by the unit normal (nx, ny)
    _beside(mx, my, nx, ny, w, h, gap = 10) { const d = Math.abs(nx) * w / 2 + Math.abs(ny) * h / 2 + gap; return [mx + nx * d, my + ny * d]; }
    _edge(id, from, to, label, { bend = 0, side, dx = 0, dy = 0, dash, tag } = {}) {
      const A = this.states.get(from), B = this.states.get(to), r = this.r;
      const ux = B.x - A.x, uy = B.y - A.y, L = Math.hypot(ux, uy) || 1;
      const mx = (A.x + B.x) / 2, my = (A.y + B.y) / 2;
      // the control point: `bend` px to the right of the direction of travel (as engine.arrowPath)
      const qx = mx - uy / L * bend, qy = my + ux / L * bend;
      const dir = (px, py, tx, ty) => { const l = Math.hypot(tx - px, ty - py) || 1; return [(tx - px) / l, (ty - py) / l]; };
      const [ax, ay] = dir(A.x, A.y, qx, qy), [bx, by] = dir(B.x, B.y, qx, qy);
      const s = [A.x + ax * (r + 6), A.y + ay * (r + 6)], e = [B.x + bx * (r + 6), B.y + by * (r + 6)];
      const p = dpath(this.tl, this.svg, `M ${s[0]} ${s[1]} Q ${qx} ${qy} ${e[0]} ${e[1]}`, { stroke: C.ink, width: LINE, dash });
      const h = headEl(this.svg, e[0], e[1], Math.atan2(e[1] - qy, e[0] - qx)); this.tl.set(h, { o: 0 }, 0);
      const rec = { kind: dash ? 'silent' : 'edge', paths: [p], heads: [h], labels: [], from, to };
      // the curve's middle, and the normal on the label's side
      const cmx = 0.25 * s[0] + 0.5 * qx + 0.25 * e[0], cmy = 0.25 * s[1] + 0.5 * qy + 0.25 * e[1];
      // the label's side: the outside of a bend; for a straight edge, above it (left of it, if it is vertical)
      let nx = uy / L, ny = -ux / L;
      if (bend) { const b = Math.sign(bend); nx = -uy / L * b; ny = ux / L * b; }
      else if (ny > 1e-6 || (Math.abs(ny) <= 1e-6 && nx > 0)) { nx = -nx; ny = -ny; }
      if (side === -1) { nx = -nx; ny = -ny; }
      if (label) {
        const w = [...label].length * charWidth(this.size), hh = this.lh;
        const [lx, ly] = this._beside(cmx, cmy, nx, ny, w, hh);
        rec.labels.push(this._label(label, lx + dx, ly + dy).e);
      }
      if (tag) {
        const tw = [...tag].length * 30 * 0.78;
        const [lx, ly] = this._beside(cmx, cmy, nx, ny, tw, 36, 12);
        const t = clabel(this.lay, lx + dx, ly - 18 + dy, tag, 30);
        this.tl.set(t, { o: 0 }, 0); rec.labels.push(t);
        this.boxes.push({ x0: lx - tw / 2, y0: ly - 18, x1: lx + tw / 2, y1: ly + 18 });
      }
      this.boxes.push({ x0: Math.min(s[0], e[0], cmx), y0: Math.min(s[1], e[1], cmy), x1: Math.max(s[0], e[0], cmx), y1: Math.max(s[1], e[1], cmy) });
      this._item(id, rec);
      return this;
    }
    edge(id, from, to, label, opts = {}) { return this._edge(id, from, to, label, opts); }
    silent(id, from, to, opts = {}) { return this._edge(id, from, to, null, Object.assign({}, opts, { dash: '13 11' })); }
    loop(id, st, label, { side = 'up', dx = 0, dy = 0 } = {}) {
      const S = this.states.get(st), r = this.r;
      const rot = { up: 0, right: Math.PI / 2, down: Math.PI, left: -Math.PI / 2 }[side];
      // the loop drawn upwards (as in film.js), then turned
      const a0 = -2.05 + rot, a1 = -1.09 + rot, P = (a, rr) => [S.x + rr * Math.cos(a), S.y + rr * Math.sin(a)];
      const [x0, y0] = P(a0, r + 4), [x1, y1] = P(a1, r + 4), [c0x, c0y] = P(a0 - 0.25, r + 120), [c1x, c1y] = P(a1 + 0.25, r + 120);
      const p = path(this.tl, this.svg, `M ${x0} ${y0} C ${c0x} ${c0y} ${c1x} ${c1y} ${x1} ${y1}`, { stroke: C.ink, width: LINE });
      const h = headEl(this.svg, x1, y1, Math.atan2(y1 - c1y, x1 - c1x)); this.tl.set(h, { o: 0 }, 0);
      const rec = { kind: 'loop', paths: [p], heads: [h], labels: [], state: st };
      // the apex of the loop, about r + 58 from the centre; the label beyond it
      const ux = Math.cos(rot - Math.PI / 2), uy = Math.sin(rot - Math.PI / 2), apex = r + 60;
      if (label) {
        const w = [...label].length * charWidth(this.size);
        const [lx, ly] = this._beside(S.x + ux * apex, S.y + uy * apex, ux, uy, w, this.lh, 6);
        rec.labels.push(this._label(label, lx + dx, ly + dy).e);
      }
      this.boxes.push({ x0: S.x + ux * apex - 60, y0: S.y + uy * apex - 60, x1: S.x + ux * apex + 60, y1: S.y + uy * apex + 60 });
      this._item(id, rec);
      return this;
    }
    draw(id, at, dur = 0.5) {
      const r = this.el(id); if (!r) return this;
      const tl = this.tl;
      for (const p of r.paths) tl.to(p, { draw: 1 }, at, dur, E.io);
      for (const h of r.heads) tl.fromTo(h, { o: 0 }, { o: 1 }, at + dur * 0.75, dur * 0.25);
      if (r.kind === 'state') { for (const l of r.labels) fadeIn(tl, l, at + dur * 0.4, 0.45, 6); if (r.start) { tl.to(r.start.path, { draw: 1 }, at + dur * 0.5, 0.4, E.io); tl.fromTo(r.start.head, { o: 0 }, { o: 1 }, at + dur * 0.5 + 0.3, 0.1); } }
      else for (const l of r.labels) fadeIn(tl, l, at + dur * 0.55, 0.45, 8);
      return this;
    }
    drawAll(at, { stagger = 0.35, except = [], dur = 0.5 } = {}) {
      let t = at;
      for (const id of this.order) { if (except.includes(id)) continue; this.draw(id, t, dur); t += stagger; }
      return t - stagger + dur + 0.2;
    }
    _all(id) { const r = this.el(id); if (!r) return []; return [...r.paths, ...r.heads, ...r.labels, ...(r.start ? [r.start.path, r.start.head] : []), ...(r.marks || [])]; }
    dimEl(id, o, at, dur = 0.4) { for (const e of this._all(id)) this.tl.to(e, { o }, at, dur); return this; }
    remove(id, at, dur = 0.35) { for (const e of this._all(id)) this.tl.to(e, { o: 0 }, at, dur, E.in); return this; }
    mark(id, at, { out = null, color = C.dim, fill = 0.1, dur = 0.4 } = {}) {
      const r = this.el(id); let m;
      if (r.kind === 'state') {
        const rr = this.r + 14;
        m = box(this.lay, r.x - rr, r.y - rr, { width: 2 * rr + 'px', height: 2 * rr + 'px', borderRadius: '50%', background: alpha(color, fill), boxShadow: `inset 0 0 0 2.5px ${alpha(color, 0.6)}` });
      } else {
        const l = r.labels[0]; if (!l) return null;
        const x = parseFloat(l.style.left), y = parseFloat(l.style.top), w = parseFloat(l.style.width), h = parseFloat(l.style.height);
        m = box(this.lay, x + 8, y + 2, { width: (w - 16) + 'px', height: (h - 4) + 'px', borderRadius: '10px', background: alpha(color, fill), boxShadow: `inset 0 0 0 1.5px ${alpha(color, 0.5)}` });
      }
      this.lay.insertBefore(m, this.lay.firstChild);
      this.tl.set(m, { o: 0, s: 0.9 }, 0); this.tl.to(m, { o: 1, s: 1 }, at, dur, E.out5);
      if (out != null) this.tl.to(m, { o: 0 }, out, 0.35);
      (r.marks = r.marks || []).push(m);
      return m;
    }
    pulse(id, at, { dur = 0.6 } = {}) {
      const r = this.el(id); if (!r) return this;
      for (const l of r.labels) { this.tl.to(l, { s: 1.08 }, at, dur * 0.4, E.out); this.tl.to(l, { s: 1 }, at + dur * 0.4, dur * 0.6, E.io); }
      this.mark(id, at, { out: at + dur, dur: dur * 0.4 });
      return this;
    }
    travel(id, at, dur = 0.8, { reverse = false, color = C.ink, r = 11, out = null } = {}) {
      const rec = this.el(id), p = rec.paths[0], len = p._len;
      const d = el(this.svg, 'circle'); d.setAttribute('r', r); d.style.fill = color;
      const place = v => { const q = p.getPointAtLength(len * (reverse ? 1 - v : v)); d.setAttribute('cx', q.x); d.setAttribute('cy', q.y); };
      place(0);
      this.tl.custom(d, 'u', (e, v) => place(v), 0);
      this.tl.set(d, { o: 0 }, 0); this.tl.to(d, { o: 1 }, at, 0.2); this.tl.to(d, { u: 1 }, at, dur, E.io);
      if (out != null) this.tl.to(d, { o: 0 }, out, 0.3);
      return d;
    }
    bounds() {
      const b = this.boxes; return { x0: Math.min(...b.map(q => q.x0)), y0: Math.min(...b.map(q => q.y0)), x1: Math.max(...b.map(q => q.x1)), y1: Math.max(...b.map(q => q.y1)) };
    }
    dim(o, at, dur = 0.5) { this.tl.to(this.g, { o }, at, dur); return this; }
    hide(at, dur = 0.4) { this.tl.to(this.g, { o: 0 }, at, dur, E.in); return this; }
    move(dx, dy, at, dur = 0.8) { this.tl.to(this.g, { x: dx, y: dy }, at, dur, E.io); return this; }
    scale(s, at, dur = 0.8) { this.tl.to(this.g, { s }, at, dur, E.io); return this; }
    to(props, at, dur = 0.8, ease = E.io) { this.tl.to(this.g, props, at, dur, ease); return this; }
  }

  // ---- presets: the film's automata, the same layout everywhere ---------------------------------------------------
  function mk(tl, parent, cx, cy, opts, size = 36) {
    const A = new Automaton(tl, parent, { cx, cy, size: opts.size || size });
    if (opts.k && opts.k !== 1) tl.set(A.g, { s: opts.k }, 0);
    return A;
  }
  const P = v => ({ pu: `push(${v})`, po: `pop(${v})` });
  function A1(tl, parent, cx, cy, opts = {}) {
    const A = mk(tl, parent, cx, cy, opts), { pu, po } = P(opts.value || 'a');
    const y = cy + 15;
    A.state('e', cx - 210, y, { name: 'e', start: true }).loop('e@', 'e', pu)
      .state('e0', cx + 230, y, { name: 'e₀' }).edge('e>e0', 'e', 'e0', po).loop('e0@', 'e0', po);
    if (opts.silent) A.silent('e~e0', 'e', 'e0', { bend: 150 });
    return A;
  }
  function A2(tl, parent, cx, cy, opts = {}) {
    const A = mk(tl, parent, cx, cy, opts), { pu, po } = P(opts.value || 'a');
    A.state('e', cx - 190, cy, { name: 'e', start: true })
      .state('e1', cx + 190, cy - 150, { name: 'e₁' }).edge('e>e1', 'e', 'e1', po).loop('e1@', 'e1', po)
      .state('e2', cx + 190, cy + 150, { name: 'e₂' }).edge('e>e2', 'e', 'e2', pu, { side: -1 }).loop('e2@', 'e2', pu, { side: 'down' });
    return A;
  }
  function A3(tl, parent, cx, cy, opts = {}) {
    const A = mk(tl, parent, cx, cy, opts), { pu, po } = P(opts.value || 'a');
    const y = cy - 10;
    A.state('e', cx - 360, y, { name: 'e', start: true })
      .state('e0', cx, y, { name: 'e₀' }).edge('e>e0', 'e', 'e0', po).loop('e0@', 'e0', po)
      .state('e1', cx + 360, y, { name: 'e₁' }).edge('e0>e1', 'e0', 'e1', pu).loop('e1@', 'e1', pu)
      .edge('e>e1', 'e', 'e1', pu, { bend: 230 });
    return A;
  }
  function PP(tl, parent, cx, cy, opts = {}) {
    const A = mk(tl, parent, cx, cy, opts);
    const y = cy + 15;
    A.state('s', cx - 170, y, { name: opts.names ? opts.names.s : '', start: true }).loop('s@', 's', 'pop')
      .state('t', cx + 190, y, { name: opts.names ? opts.names.t : '' }).edge('s>t', 's', 't', 'push').loop('t@', 't', 'push');
    return A;
  }
  function zipped(tl, parent, cx, cy, opts, withLoop) {
    const A = mk(tl, parent, cx, cy, opts, 34), v = opts.value || 'a', n = opts.names || {};
    const pp = `(pop(${v}), push(${v}))`, dp = `(done, push(${v}))`, pd = `(pop(${v}), done)`;
    const ty = cy - 150, by = cy + 170;
    A.state('T', cx, ty, { name: n.T || '', start: true });
    if (withLoop) A.loop('T@', 'T', pp);
    A.state('L', cx - 215, by, { name: n.L || '' }).edge('T>L', 'T', 'L', dp).loop('L@', 'L', dp, { side: 'down' })
      .state('R', cx + 215, by, { name: n.R || '' }).edge('T>R', 'T', 'R', pd).loop('R@', 'R', pd, { side: 'down' });
    return A;
  }
  const Z3 = (tl, parent, cx, cy, opts = {}) => zipped(tl, parent, cx, cy, opts, true);
  const Z1 = (tl, parent, cx, cy, opts = {}) => zipped(tl, parent, cx, cy, opts, !!opts.loop);

  // ---- the packet header --------------------------------------------------------------------------------------
  function packetHeader(tl, parent, x, y, fields, { w = 150, h = 90, gap = 14, size = 44, names = 32 } = {}) {
    const n = fields.length, width = n * w + (n - 1) * gap, height = h + 50;
    const g = box(parent, x, y, { width: width + 'px', height: height + 'px' });
    const nameEls = [], vals = fields.map(([name, v], i) => {
      nameEls.push(ctext(g, i * (w + gap) + w / 2, 20, name, Object.assign(MONO(names), { color: C.bind }), 44));
      return cell(g, i * (w + gap), 50, w, h, v, { font: MONO(size) });
    });
    tl.set(g, { o: 0 }, 0);
    return {
      g, vals, names: nameEls, width, height,
      show(at) { fadeIn(tl, g, at, 0.6, 16); return this; },
      flip(i, text, at) { flip(tl, vals[i]._t, text, at); return this; },
      tint(i, at, out) { tl.to(vals[i], { bg: alpha(C.dim, 0.14) }, at, 0.3); if (out != null) tl.to(vals[i], { bg: alpha(C.dim, 0) }, out, 0.4); return this; },
      pulse(i, at) { tl.to(vals[i], { s: 1.08 }, at, 0.2, E.out); tl.to(vals[i], { s: 1 }, at + 0.2, 0.35, E.io); this.tint(i, at, at + 0.6); return this; },
      dim(o, at, dur = 0.5) { tl.to(g, { o }, at, dur); return this; },
      hide(at, dur = 0.4) { tl.to(g, { o: 0 }, at, dur, E.in); return this; },
      move(dx, dy, at, dur = 0.8) { tl.to(g, { x: dx, y: dy }, at, dur, E.io); return this; },
      to(props, at, dur = 0.8, ease = E.io) { tl.to(g, props, at, dur, ease); return this; },
      cellRect(i) { return { x: x + i * (w + gap), y: y + 50, w, h, cx: x + i * (w + gap) + w / 2, cy: y + 50 + h / 2 }; },
    };
  }

  // ---- the title ----------------------------------------------------------------------------------------------
  const AUTHORS = ['Jules Jacobs · Nate Foster · Tobias Kappé · Dexter Kozen', 'Lily Saada · Alexandra Silva · Jana Wagemaker · PLDI 2025'];
  function titleCard(tl, root, { align = 'center', x = CX, y = 300, size = 150, subSize = 56, at, subAt, authorsAt, authorSize = 32, gap = 34 } = {}) {
    const mk = (text, yy, style) => align === 'left' ? box(root, x - (style.letterSpacing ? 0 : size * 0.06), yy, Object.assign({ whiteSpace: 'pre' }, style), text) : cline(root, x, yy, [[text, null]], style).root;
    const title = mk('StacKAT', y, SERIF(size));
    const sy = y + Math.round(size * 1.22) + 4;
    const sub = mk('Infinite State Network Verification', sy, SERIF(subSize));
    const ay = sy + Math.round(subSize * 1.22) + gap + 10;
    const authors = AUTHORS.map((t, i) => mk(t, ay + i * Math.round(authorSize * 1.65), LABEL(authorSize)));
    if (align === 'left') { sub.style.left = (x - subSize * 0.04) + 'px'; authors.forEach(a => { a.style.left = x + 'px'; }); }
    for (const e of [title, sub, ...authors]) tl.set(e, { o: 0 }, 0);
    if (at != null) fadeIn(tl, title, at, 0.8, 24);
    if (subAt != null) fadeIn(tl, sub, subAt, 0.7, 16);
    if (authorsAt != null) authors.forEach((a, i) => fadeIn(tl, a, authorsAt + i * 0.25, 0.6, 10));
    return { title, sub, authors, bottom: ay + 2 * Math.round(authorSize * 1.65) };
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
      // evidence added after a later row was built still steps back with its row
      row.add = e => { const x = rootOf(e); parts.push(x); if (row.backAt != null) this.tl.to(x, { o: this.back }, row.backAt, 0.5); return e; };
      this.rows.push(row);
      return row;
    }
    evidence(i, e, at, dy = 14) { fadeIn(this.tl, rootOf(e), at, 0.5, dy); this.rows[i].add(e); return e; }
    all() { return this.rows.flatMap(r => r.parts); }
  }

  // "if and only if", drawn: neither shipped font has a usable ⟺ (Fira Code's is one cell wide, Source Serif has
  // none), and a glyph from a system font would differ between devices. Returns an inline SVG element about 1.7 em
  // wide in the current text colour; put it into a part of a line: `const l = SX.cline(root, cx, y, [['e₁ ≡ e₂  '],
  // ['', null], ['  L(A₁) = L(A₂)']], SX.MONO(60)); l.parts[1].appendChild(SX.iff(60));`
  function iff(size, color) {
    const NS = 'http://www.w3.org/2000/svg', w = size * 1.7, h = size * 0.7, g = size * 0.11, a = size * 0.26, sw = Math.max(2.5, size * 0.055);
    const s = document.createElementNS(NS, 'svg');
    s.setAttribute('width', w); s.setAttribute('height', h); s.setAttribute('viewBox', `0 0 ${w} ${h}`);
    Object.assign(s.style, { display: 'inline-block', verticalAlign: 'middle', overflow: 'visible', position: 'relative', top: (-size * 0.04) + 'px' });
    const m = h / 2, d = `M ${a * 0.9} ${m - g} L ${w - a * 0.9} ${m - g} M ${a * 0.9} ${m + g} L ${w - a * 0.9} ${m + g} ` +
      `M ${a} ${m - a} L ${sw} ${m} L ${a} ${m + a} M ${w - a} ${m - a} L ${w - sw} ${m} L ${w - a} ${m + a}`;
    const p = document.createElementNS(NS, 'path');
    p.setAttribute('d', d); p.setAttribute('fill', 'none'); p.setAttribute('stroke', color || 'currentColor'); p.setAttribute('stroke-width', sw);
    p.setAttribute('stroke-linecap', 'round'); p.setAttribute('stroke-linejoin', 'round');
    s.appendChild(p);
    return s;
  }

  window.SX = {
    iff, CX, RAIL, LINE, LABEL, SERIF, MONO, cline, lline, clabel, cserif, note, strikeEl,
    svg: svgLayer, tick: tickM, cross: crossM, dpath, line, arc, cell, flip, circleD, ctext, dim,
    tokens, richText, prog, Prog, Stack, Automaton, A1, A2, A3, PP, Z1, Z3, packetHeader, titleCard, AUTHORS, Rows,
  };
})();

// ==== src/scenes/a_open.js ====
// The opening (hook, roadmap, title) and the close (recap, end) of the StacKAT film, built with SX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = SX;

  // ============================================ hook ==========================================================
  scene('hook', ({ tl, root, cue }) => {
    // "Here are two small programs.": P1 and P2 on one line, a wide gap between them
    const S = 56, cw = charWidth(S), N = 18, GAP = 300;
    const x1 = Math.round((W - (2 * N * cw + GAP)) / 2), x2 = Math.round(x1 + N * cw + GAP), py = 250 - Math.round(S * 1.3 / 2);
    const tTwo = cue('two');
    const P1 = SX.prog(tl, root, x1, py, S, 'push(a)* · pop(a)*');
    const P2 = SX.prog(tl, root, x2, py, S, 'push(a)* + pop(a)*');
    P1.show(tTwo - 0.1); P2.show(tTwo + 0.25);
    const c1 = x1 + N * cw / 2, c2 = x2 + N * cw / 2, bottom = 820, BIG = { w: 108, h: 92, size: 48 };

    // "The first pushes the value A some number of times, and then pops it some number of times."
    const tP1 = cue('p1'), tStar = cue('star'), tNot = cue('notwhile'), tTr = cue('trace'), tRun = cue('run');
    P2.to({ o: 0.4 }, tP1 - 0.2, 0.5);
    P1.pulse(P1.letter(0), tP1 + 0.55);                       // "pushes"
    P1.pulse(P1.letter(1), tP1 + 3.6);                        // "pops"

    // "The star is the star of regular expressions. It means some number of times: zero, one, two, or more. It is
    // not a loop that keeps running.": the two stars are marked, and what they mean is said under the program
    P1.parts.forEach((q, k) => { if (q.text === '*') P1.mark(k, C.dim, tStar + 0.1, { out: tTr - 0.3, fill: 0.1 }); });
    SX.note(tl, root, x1, 346, 'the star of regular expressions', tStar + 1.2, tTr - 0.3, { size: 34, align: 'left' });
    SX.note(tl, root, x1, 400, 'some number of times: 0, 1, 2, …', tStar + 3.75, tTr - 0.3, { size: 34, color: C.ink, align: 'left' });
    SX.note(tl, root, x1, 454, 'not a loop that keeps running', tNot - 0.1, tTr - 0.3, { size: 34, align: 'left' });

    // "Like a regular expression, the program generates sequences of pushes and pops, called traces.": three of them
    const TS = 44, ty = k => 410 + k * 92;
    const traces = ['push(a)  push(a)  push(a)  pop(a)  pop(a)', 'push(a)  pop(a)  pop(a)', 'pop(a)'].map((t, k) => {
      const tr = SX.prog(tl, root, x1, ty(k), TS, t); tr.show(tTr + 2.1 + k * 0.6, { stagger: 0.04 }); return tr;
    });
    SX.note(tl, root, x1, 346, 'some of its traces', tTr + 4.7, tP2x() - 0.3, { size: 34, align: 'left' });
    // "Each trace is one way the program can run.": the first trace, run on a stack
    traces[0].mark('all', C.dim, tRun - 0.15, { out: tP2x() - 0.3, fill: 0.08 });
    traces[1].dim('all', 0.4, tRun - 0.15); traces[2].dim('all', 0.4, tRun - 0.15);
    const s1 = new SX.Stack(tl, root, 1560, bottom, Object.assign({ items: ['b'], label: 'one way to run' }, BIG));
    s1.show(tRun - 0.3);
    [0.25, 0.65, 1.05].forEach((d, k) => { s1.push('a', tRun + d); traces[0].pulse(traces[0].letter(k), tRun + d); });
    [1.6, 2.1].forEach((d, k) => { s1.pop(tRun + d); traces[0].pulse(traces[0].letter(3 + k), tRun + d); });
    function tP2x() { return cue('p2'); }

    // "The second program does one or the other: only pushes, or only pops."
    const tP2 = cue('p2');
    s1.hide(tP2 - 0.3); traces.forEach(tr => tr.hide(tP2 - 0.3, 0.3));
    P1.to({ o: 0.4 }, tP2 - 0.2, 0.5); P2.to({ o: 1 }, tP2 - 0.2, 0.5);
    const sa = new SX.Stack(tl, root, c2 - 180, bottom, Object.assign({ items: ['b'], label: 'only pushes' }, BIG));
    sa.show(tP2 + 2.35);
    sa.push('a', tP2 + 2.65); sa.push('a', tP2 + 3.1);
    P2.pulse(P2.letter(0), tP2 + 2.65);
    const sb = new SX.Stack(tl, root, c2 + 180, bottom, Object.assign({ items: ['a', 'a', 'b'], label: 'only pops' }, BIG));
    sb.show(tP2 + 3.6);
    sb.pop(tP2 + 3.95); sb.pop(tP2 + 4.35);
    P2.pulse(P2.letter(1), tP2 + 3.95);

    // "They are equivalent": both bright, a green ≡ in the gap; the stacks leave
    const tEq = cue('eq');
    sa.hide(tEq - 0.35); sb.hide(tEq - 0.35);
    P1.to({ o: 1 }, tEq - 0.25, 0.5);
    const eq = SX.prog(tl, root, CX, 250 - Math.round(84 * 1.3 / 2), 84, '≡', { align: 'center', colors: { '≡': C.good } });
    tl.set(eq.parts[0].el, { s: 0.6 }, 0);
    eq.show(tEq + 0.45, { rise: 0 }); tl.to(eq.parts[0].el, { s: 1 }, tEq + 0.45, 0.5, E.out5);   // at "equivalent"

    // "A stack can be arbitrarily deep, so there are infinitely many stacks to try."
    const tInf = cue('inf');
    const g = box(root, 0, 0, { width: W + 'px', height: '1080px' });
    const piles = [];
    for (let k = 0; k < 7; k++) {
      const st = new SX.Stack(tl, g, 230 + k * 215, 800, { items: Array(k + 1).fill('a'), w: 64, h: 56, gap: 8, size: 32 });
      st.show(tInf - 0.15 + k * 0.24, { stagger: 0.04 });
      piles.push(st);
    }
    const dots = box(g, 1610, 660, Object.assign(SX.MONO(84), { color: C.pat, width: '160px', textAlign: 'center' }), '…');
    fadeIn(tl, dots, tInf + 1.6, 0.5, 10);
    const infl = SX.clabel(g, CX, 832, 'infinitely many stacks', 32);
    fadeIn(tl, infl, tInf + 2.65, 0.5, 10);

    // "This video is about a language for networks, called Stack Cat"
    const tF = cue('film');
    tl.to(g, { o: 0 }, tF - 0.3, 0.4, E.in);
    const lang = SX.clabel(root, CX, 640, 'a language for networks', 32);
    fadeIn(tl, lang, tF + 1.15, 0.5, 10);
    const name = SX.cserif(root, CX, 420, 'StacKAT', 130);
    fadeIn(tl, name, tF + 2.7, 0.7, 20);
    // "By the end, we will have checked these two programs by hand, and we will know an algorithm that checks any
    // such equivalence automatically.": the two promises, each at its words
    SX.note(tl, root, CX, 740, 'by the end: these two, checked by hand', cue('hand') + 0.2, null, { size: 34, align: 'center', color: C.ink });
    SX.note(tl, root, CX, 794, 'and an algorithm that checks any two programs', cue('algo') + 0.5, null, { size: 34, align: 'center', color: C.ink });
  });

  // ============================================ roadmap =======================================================
  scene('roadmap', ({ tl, root, cue }) => {
    const head = box(root, RAIL, 180, Object.assign(SX.LABEL(32), { color: C.ink }), 'in this video');
    fadeIn(tl, head, cue('coming') - 0.15, 0.5, 10);
    const rows = new SX.Rows(tl, root, { x: RAIL, y: 270, pitch: 124, size: 56, titleX: RAIL + 70 });
    const EX = 1130, S = 40;
    const code = (i, text, at) => {
      const p = SX.prog(tl, root, EX, rows.mid(i) - Math.round(S * 1.3 / 2), S, text);
      p.show(at, { stagger: 0.02 }); rows.rows[i].add(p.root); return p;
    };
    const ink = (i, text, at) => rows.evidence(i, box(root, EX, rows.mid(i) - 20, Object.assign(SX.LABEL(32), { color: C.ink }), text), at);

    rows.row('Networks as programs', cue('net') - 0.1);
    code(0, 'sw==a · net · sw==b ≡ 0', cue('net') + 4.9);
    rows.row('Why a stack', cue('stack') - 0.1);
    const cells = box(root, EX, rows.mid(1) - 30, { width: '400px', height: '60px' });
    [0, 1, 2].forEach(k => SX.cell(cells, k * 72, 0, 60, 60, '', { stroke: C.pat }));
    box(cells, 3 * 72 + 2, -16, Object.assign(SX.MONO(60), { color: C.dim }), '…');
    rows.evidence(1, cells, cue('stack') + 1.75);
    rows.row('The language, and three laws', cue('lang') - 0.1);
    code(2, 'push(v) · pop(v) ≡ 1', cue('lang') + 2.55);
    rows.row('Three steps on a finite automaton', cue('proc') - 0.1);
    ink(3, 'cancel · filter · zip', cue('proc') + 2.3);
    rows.row('Headers, cost, counterexamples, axioms', cue('rest') - 0.1);
  });

  // ============================================ title =========================================================
  scene('title', ({ tl, root, cue }) => {
    SX.titleCard(tl, root, { align: 'left', x: RAIL, y: 300, size: 170, subSize: 60, at: cue('title') - 0.2, subAt: cue('sub') - 0.2, authorsAt: cue('sub') + 0.9 });
  });

  // ============================================ recap =========================================================
  scene('recap', ({ tl, root, cue }) => {
    const rows = new SX.Rows(tl, root, { x: RAIL, y: 200, pitch: 112, size: 50, titleX: RAIL + 70 });
    const EX = 1000, S = 40, lh = Math.round(S * 1.3);
    const at = (i, text, t, opts) => { const p = SX.prog(tl, root, EX, rows.mid(i) - lh / 2, S, text, opts); rows.rows[i].add(p.root); return p; };

    rows.row('A network is a program', cue('r1') - 0.1);
    at(0, 'sw==a · net · sw==b ≡ 0').show(cue('r1') + 3.55, { stagger: 0.02 });

    rows.row('A stack: infinitely many packets', cue('r2') - 0.1);
    const cells = box(root, EX, rows.mid(1) - 30, { width: '400px', height: '60px' });
    [0, 1, 2].forEach(k => SX.cell(cells, k * 72, 0, 60, 60, '', { stroke: C.pat }));
    box(cells, 3 * 72 + 2, -16, Object.assign(SX.MONO(60), { color: C.dim }), '…');
    rows.evidence(1, cells, cue('r2') + 1.0);

    rows.row('StacKAT: push and pop', cue('r3') - 0.1);
    const pp = at(2, 'push(n)   pop(n)');
    pp.show(cue('r3') + 0.9, { sel: 0 }); pp.show(cue('r3') + 1.8, { sel: 1 });

    rows.row('Three laws, three steps', cue('r4') - 0.1);
    const st = SX.lline(root, EX, rows.mid(3) - 20, [['cancel', null], [' · filter', null], [' · zip', null]], Object.assign(SX.LABEL(32), { color: C.ink }));
    rows.rows[3].add(st.root);
    [4.45, 5.25, 5.95].forEach((d, k) => fadeIn(tl, st.parts[k], cue('r4') + d, 0.5, 10));

    rows.row('Equivalence is decidable', cue('r5') - 0.1);
    const th = SX.lline(root, EX, rows.mid(4) - lh / 2, [['e₁ ≡ e₂  ', null], ['', null], ['  L(A₁) = L(A₂)', null]], SX.MONO(S));
    th.parts[1].appendChild(SX.iff(S));   // drawn: no shipped font has a usable ⟺
    rows.evidence(4, th.root, cue('r5') + 3.45);
    const svg = SX.svg(root);
    const tk = SX.tick(tl, svg, EX + 28 * charWidth(S) + 34, rows.mid(4), 44, cue('r5') + 6.5);
    rows.rows[4].add(tk.els[0]);

    rows.row('A foundation for networks that parse, tunnel and route by a stack', cue('r6') - 0.1);
  });

  // ============================================ end ===========================================================
  scene('end', ({ tl, root, cue }) => {
    const tc = SX.titleCard(tl, root, { align: 'center', x: CX, y: 255, size: 150, subSize: 56, at: cue('title') - 0.2, subAt: cue('title') + 1.15, authorsAt: cue('title') + 2.4 });
    const y = tc.bottom + 64, t = cue('paper');
    const l1 = SX.lline(root, 0, y, [['in the paper and its appendix:', null], [' the proofs', null]], SX.LABEL(32));
    const l2 = SX.lline(root, 0, y + 54, [['the constructions', null], [' · complexity', null], [' · the axiomatization', null]], SX.LABEL(32));
    // centred lines whose parts arrive one by one
    for (const l of [l1, l2]) Object.assign(l.root.style, { left: (CX - 1200) + 'px', width: '2400px', textAlign: 'center', paddingLeft: '0.16em' });
    fadeIn(tl, l1.parts[0], t - 0.1, 0.5, 10);
    [[l1.parts[1], 6.94], [l2.parts[0], 7.62], [l2.parts[1], 9.58], [l2.parts[2], 11.14]].forEach(([e, w]) => fadeIn(tl, e, t + (w - 4.9) - 0.2, 0.5, 10));
    return { keep: true };
  });
})();

// ==== src/scenes/b.js ====
// Networks as programs (net_a, net_b, net_c) and why a stack (stack_a + stack_b, one scene, so that the pile of
// cells stays on screen across the two segments). Built with SX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = SX;

  // ---- local helpers ------------------------------------------------------------------------------------------
  // A small caps label made of parts [text, colour, how]: how 'case' keeps the case (NetKAT, a switch named a),
  // 'mono' sets the part in Fira Code (for × and other symbols the system sans may lack). x is the left edge, or
  // the centre with align 'center'.
  function lab(root, x, y, parts, { size = 32, color = C.dim, align = 'left' } = {}) {
    const ps = parts.map(p => [p[0], p[1] || null]);
    const st = Object.assign(SX.LABEL(size), { color });
    const l = align === 'center' ? SX.cline(root, x, y, ps, st) : SX.lline(root, x, y, ps, st);
    parts.forEach((p, i) => {
      const s = l.parts[i];
      if (p[2] === 'case') Object.assign(s.style, { textTransform: 'none', letterSpacing: '0.02em' });
      if (p[2] === 'mono') Object.assign(s.style, { fontFamily: 'var(--mono)', letterSpacing: '0', fontWeight: 450, fontSize: '1.25em', lineHeight: '0.9', margin: '0 0.12em' });
    });
    return l;
  }
  // Fira Code has the subscript digits but no subscript letters: a part 'ₙ' of a prog becomes a lowered small n.
  function subLetters(p) {
    for (const part of p.parts) if (part.text === 'ₙ') {
      const sp = part.subs[0];
      sp.textContent = 'n';
      Object.assign(sp.style, { fontSize: '0.64em', position: 'relative', top: '0.3em', marginLeft: '0.04em' });
    }
    return p;
  }
  // Fira Code centres a subscript digit in a whole cell, so e₁ reads as "e ₁": pull each subscript towards the
  // letter before it (the grid is kept: the space is given back after it).
  function tightEl(sp) {
    const t = sp.textContent;
    if (!/[₀-₉]/u.test(t)) return sp;
    sp.textContent = '';
    for (const ch of t) {
      const c = document.createElement('span'); c.textContent = ch;
      Object.assign(c.style, { position: 'relative', left: /[₀-₉]/u.test(ch) ? '-0.09em' : '0.07em' });
      sp.appendChild(c);
    }
    return sp;
  }
  function tightSubs(p) { for (const part of p.parts) for (const sp of part.subs) tightEl(sp); return p; }
  // a neutral soft box (the "look here" highlight) at a stage rectangle
  function softBox(tl, root, x, y, w, h, at, out) {
    const m = box(root, x, y, { width: w + 'px', height: h + 'px', borderRadius: '16px', background: alpha(C.dim, 0.08), boxShadow: `inset 0 0 0 1.5px ${alpha(C.dim, 0.5)}` });
    tl.set(m, { o: 0, s: 0.94 }, 0); tl.to(m, { o: 1, s: 1 }, at, 0.4, E.out5);
    if (out != null) tl.to(m, { o: 0 }, out, 0.35);
    return m;
  }

  // ============================================ net_a =========================================================
  scene('net_a', ({ tl, root, cue }) => {
    // "A network is made of switches.": a host, switches A, B, C, a host, in a row (as the short video's s_hook)
    const Y = 330, HX = [280, 1640], SXS = [660, 960, 1260], HR = 50, SW = 190, SH = 136;
    const g = box(root, 0, 0, { width: W + 'px', height: '1080px', transformOrigin: `${CX}px ${Y}px` });
    const svg = svgLayer(g);
    const t0 = cue('net') - 0.15;
    HX.forEach((x, i) => tl.to(path(tl, svg, SX.circleD(x, Y, HR), { stroke: C.ink, width: SX.LINE }), { draw: 1 }, t0 + i * 0.9, 0.6, E.io));
    SXS.forEach((x, i) => {
      const b = SX.cell(g, x - SW / 2, Y - SH / 2, SW, SH, 'ABC'[i], { font: SX.SERIF(72), radius: 22 });
      tl.set(b, { o: 0, s: 0.96 }, 0); tl.to(b, { o: 1, s: 1 }, t0 + 0.15 + i * 0.22, 0.5, E.out5);
    });
    const ends = [[HX[0] + HR, SXS[0] - SW / 2], [SXS[0] + SW / 2, SXS[1] - SW / 2], [SXS[1] + SW / 2, SXS[2] - SW / 2], [SXS[2] + SW / 2, HX[1] - HR]];
    ends.forEach(([a, b], i) => tl.to(path(tl, svg, `M ${a} ${Y} L ${b} ${Y}`, { stroke: C.ink, width: SX.LINE }), { draw: 1 }, t0 + 0.25 + i * 0.2, 0.5, E.io));

    // "A packet arrives with a header: a few fields, such as a destination and a port."
    const pk = SX.packetHeader(tl, g, 0, Y + 100, [['sw', 'A'], ['dst', '7'], ['port', '1']], { w: 150, h: 100, gap: 16, size: 52, names: 34 });
    pk.g.style.left = (SXS[0] - pk.width / 2) + 'px';
    pk.show(cue('pkt') + 0.0);
    pk.pulse(1, 7.75); pk.pulse(2, 8.8);

    // "A switch looks at some fields, changes some, and sends the packet on to a neighbor."
    const tint = (i, a, b) => pk.tint(i, a, b);
    tint(1, 10.9, 11.8);
    tint(2, 11.85, 12.7); pk.flip(2, '2', 11.9);
    pk.move(SXS[1] - SXS[0], 0, 13.0, 0.7); pk.flip(0, 'B', 13.3);

    // "NetKAT is a language that reads all of this as a program.": the drawing goes up and shrinks
    const tP = cue('prog'), K = 0.7, DY = 205 - Y;
    tl.to(g, { s: K, y: DY }, tP - 0.25, 0.7, E.io);
    const nl = lab(root, CX, 398, [['NetKAT', null, 'case'], [': the network as a program']], { align: 'center' }).root;
    fadeIn(tl, nl, tP - 0.1, 0.5, 10);

    // the rows: the thing in mono 56 at x = 360, its label at x = 900
    const S = 56, lh = Math.round(S * 1.3), RY = [485, 590, 695, 800];
    const rows = [];
    const row = (i, text, label, at, colors) => {
      const p = SX.prog(tl, root, 360, RY[i], S, text, { colors });
      p.show(at, { stagger: 0.03 });
      const l = SX.note(tl, root, 900, RY[i] + lh / 2 - 19, label, at + 0.1, null, { align: 'left' });
      for (const r of rows) for (const e of r) tl.to(e, { o: 0.45 }, at - 0.15, 0.5);
      rows.push([p.root, l]);
      return p;
    };
    // "A field is a variable."
    row(0, 'dst', 'a field is a variable', cue('field') + 0.15, { dst: C.bind });
    pk.pulse(1, cue('field') + 0.35);
    // "A match is a test: it lets the packet through if a field has a given value, and drops it otherwise."
    row(1, 'dst == 7', 'a test: pass, or drop', cue('test') - 0.1);
    // "An action is an assignment of a constant to a field."
    row(2, 'port := 2', 'an assignment', cue('assign') - 0.05);
    // "Even the packet's location is a field. Moving it to switch B is an assignment: switch becomes B."
    pk.pulse(0, 32.6);
    const mv = row(3, 'sw := B', 'moving is an assignment', 34.2);
    pk.pulse(0, 37.0);
    mv.pulse('all', 37.0);
  });

  // ============================================ net_b =========================================================
  scene('net_b', ({ tl, root, cue }) => {
    // a column: the expression in mono 60 at x = 420, its label at x = 800, pitch 120 from y = 200
    const S = 60, lh = Math.round(S * 1.3), Y = i => 200 + i * 120;
    const items = [
      ['e₁ · e₂', 'one, then the other', cue('seq') - 0.15],
      ['e₁ + e₂', 'a choice: both ways', cue('plus') - 0.15],
      ['e*', 'any number of times', cue('star') - 0.15],
      ['1', 'pass every packet', 20.1],     // "The program written one passes every packet"
      ['0', 'drop every packet', 24.1],     // "The program written zero drops every packet"
    ];
    const tOps = cue('ops') - 0.1, tW = cue('whole');
    const lit = [];
    items.forEach(([text, label, at], i) => {
      const p = tightSubs(SX.prog(tl, root, 420, Y(i), S, text));
      // "Programs are combined in three ways.": the three ways come in dimmed, each lights at its word
      if (i < 3) { p.show(tOps + i * 0.15); p.dim('all', 0.35, tOps + 0.5 + i * 0.15, 0.01); p.light('all', at, 0.4); }
      else p.show(at);
      const l = SX.note(tl, root, 800, Y(i) + lh / 2 - 19, label, at + 0.1, null, { align: 'left' });
      for (const [q, m] of lit) { q.dim('all', 0.45, at - 0.1, 0.4); tl.to(m, { o: 0.45 }, at - 0.1, 0.4); }
      lit.push([p, l]);
      for (const e of [p.root, l]) tl.to(e, { o: 0 }, tW - 0.45, 0.35, E.in);
    });
    // "And there are two constant programs.": nothing until each is named

    // "The whole network is then one program: test which switch the packet is on, run that switch's program, and
    // repeat."
    const NS = 52, nlh = Math.round(NS * 1.3), ncw = charWidth(NS);
    const L = ['( sw==1 · p₁', '+ sw==2 · p₂', '+ …', '+ sw==n · pₙ )*'];
    const bx = Math.round(CX - 15 * ncw / 2), by = 400;
    const head = SX.clabel(root, CX, by - 76, 'the whole network', 32);
    fadeIn(tl, head, tW - 0.15, 0.5, 10);
    const ls = L.map((t, i) => tightSubs(subLetters(SX.prog(tl, root, bx, by + i * nlh, NS, t))).show(tW + 0.05 + i * 0.12, { stagger: 0.02 }));
    // the tests, then the switches' programs, then the star
    ls.forEach(p => p.pulse(/^sw==/, 29.3));
    ls.forEach(p => p.pulse(/^p/, 31.6));
    ls[3].pulse([...ls[3].ids(')'), ...ls[3].ids('*')], 33.9);
  });

  // ============================================ net_c =========================================================
  scene('net_c', ({ tl, root, cue }) => {
    // "It relates each input packet to the packets that can come out: none, one, or several."
    const tR = cue('rel'), tE = cue('equiv');
    const hd = SX.clabel(root, CX, 170, 'a program relates inputs to outputs', 32);
    fadeIn(tl, hd, tR - 0.1, 0.5, 10);
    const HO = { w: 90, h: 64, gap: 10, size: 36, names: 30 };
    const ROWS = [330, 540, 750], OX = 900;
    const pk = (x, cy, vals) => SX.packetHeader(tl, root, x, cy - 50 - HO.h / 2, [['sw', vals[0]], ['dst', '7'], ['port', vals[1]]], HO);
    const inp = pk(200, 540, ['A', '1']);
    inp.show(tR + 0.05);
    const svg = SX.svg(root);
    const x1 = 200 + inp.width + 30, gone = [hd, inp.g, svg];
    const outs = [[[], 'none', 6.2], [[['B', '2']], 'one', 6.85], [[['B', '2'], ['C', '2']], 'several', 7.5]];
    outs.forEach(([ps, label, at], i) => {
      const y = ROWS[i];
      SX.line(tl, svg, x1, 540, OX - 40, y, { at: at - 0.05, dur: 0.45 });
      ps.forEach((v, k) => { const h = pk(OX + k * (inp.width + 30), y, v); h.show(at + 0.15 + k * 0.12); gone.push(h.g); });
      const lx = OX + ps.length * (inp.width + 30) + (ps.length ? 10 : 0);   // after what came out
      const l = SX.note(tl, root, lx, y - 19, label, at + 0.05, null, { align: 'left' });
      gone.push(l);
    });
    for (const e of gone) tl.to(e, { o: 0 }, tE - 0.45, 0.35, E.in);

    // "Two programs are equivalent if they relate the same inputs to the same outputs."
    const eq = tightSubs(SX.prog(tl, root, CX, 460 - 52, 80, 'e₁ ≡ e₂', { align: 'center' }));
    eq.show(tE - 0.15, { stagger: 0.06 });
    const same = SX.clabel(root, CX, 540, 'the same inputs to the same outputs', 32);
    fadeIn(tl, same, 11.05, 0.5, 10);
    // "Equivalence is what verification needs.": it moves up
    const tWhy = cue('why');
    fadeOut(tl, same, tWhy - 0.3, 0.3);
    eq.to({ s: 56 / 80, y: (170 + 73 / 2) - 460 }, tWhy - 0.25, 0.65);

    // "start at A, run the network, and test for B": the program arrives piece by piece, a label under each
    const S = 64, lh = Math.round(S * 1.3), Y0 = 360;
    const rp = SX.prog(tl, root, CX, Y0, S, 'sw==a  ·  net  ·  sw==b  ≡  0', { align: 'center' });
    const pieces = [[[0], 'start at ', 'a', 20.85], [[1, 2], 'run the network', null, 21.95], [[3, 4], 'test for ', 'b', 23.3]];
    const plabs = pieces.map(([sel, text, v, at]) => {
      rp.show(at, { sel, stagger: 0.08 });
      const r = rp.rect(sel.slice(-1));
      const l = lab(root, r.cx, Y0 + lh + 18, v ? [[text], [v, null, 'case']] : [[text]], { align: 'center' }).root;
      fadeIn(tl, l, at + 0.1, 0.5, 10);
      return l;
    });
    tl.to(eq.root, { o: 0.45 }, 20.7, 0.5);
    // "If that program is equivalent to zero, no packet gets through."
    rp.show(25.6, { sel: [5, 6], stagger: 0.12 });
    for (const l of plabs) fadeOut(tl, l, 26.75, 0.3);
    const none = SX.clabel(root, CX, Y0 + lh + 18, 'no packet gets through', 32);
    fadeIn(tl, none, 27.05, 0.5, 10);

    // "because a packet has finitely many fields, with finitely many values."
    const fv = lab(root, CX, Y0 + lh + 110, [['finitely many fields '], ['×', null, 'mono'], [' finitely many values']], { align: 'center' });
    fadeIn(tl, fv.parts[0], 33.05, 0.5, 10);
    fadeIn(tl, fv.parts[1], 34.65, 0.5, 10); fadeIn(tl, fv.parts[2], 34.75, 0.5, 10);
    // "There are only finitely many packets, so a program is a finite-state system."
    const fp = SX.clabel(root, CX, Y0 + lh + 190, 'finitely many packets', 32);
    fadeIn(tl, fp, 37.45, 0.5, 10);
    for (const e of [rp.root, none, fv.root]) tl.to(e, { o: 0.5 }, 37.3, 0.5);
    const dec = SX.cserif(root, CX, Y0 + lh + 270, 'Decidable.', 72, C.good);
    fadeIn(tl, dec, 40.5, 0.6, 14);
  });

  // ============================================ stack_a + stack_b =============================================
  scene(['stack_a', 'stack_b'], ({ tl, root, cue, seg }) => {
    const CW = 120, CH = 96, GAP = 14, STEP = CW + GAP, RY = 382, MONO = SX.MONO(48);
    // a packet's cells in a row, the front on the left; each cell has an amber outline that comes in at `st`
    const mk = (text, x0) => {
      const c = SX.cell(root, x0, RY, CW, CH, text, { font: MONO, radius: 14 });
      tightEl(c._t);
      c._amber = box(c, 0, 0, { width: CW + 'px', height: CH + 'px', borderRadius: '14px', boxShadow: `inset 0 0 0 ${SX.LINE}px ${C.pat}` });
      tl.set(c._amber, { o: 0 }, 0);
      c._x0 = x0;
      return c;
    };
    class Row {
      constructor(x0) { this.x0 = x0; this.cells = []; }
      place(at, d = 0.5) { this.cells.forEach((c, i) => { if (!c) return; const x = this.x0 + i * STEP - c._x0; if (c._at !== x) { tl.to(c, { x }, at, d, E.io); c._at = x; } }); }
      append(text, at) { const i = this.cells.length, c = mk(text, this.x0 + i * STEP); c._at = 0; this.cells.push(c); fadeIn(tl, c, at, 0.5, 14); return c; }
      // a cell put on the front: the others make room, it comes down into place
      push(text, at) {
        this.cells.unshift(null); this.place(at, 0.45);
        const c = mk(text, this.x0); c._at = 0; this.cells[0] = c;
        tl.set(c, { y: -90, o: 0 }, 0); tl.to(c, { y: 0 }, at + 0.2, 0.5, E.out5); tl.to(c, { o: 1 }, at + 0.2, 0.3);
        return c;
      }
      // the front cell lifts off (or is taken: the caller moves it); the others close up
      pop(at, take = false) {
        const c = this.cells.shift();
        if (!take) { tl.to(c, { y: -80 }, at, 0.5, E.in); tl.to(c, { o: 0 }, at + 0.1, 0.4, E.in); }
        this.place(at + 0.3);
        return c;
      }
    }
    // a cell flies from the front of the row into a header field, and the field reads its text
    // a cell flies from the front of the row into a header field (up into the gap between them, across, and up
    // into the field), and the field reads its text
    const fly = (c, hdr, i, text, at) => {
      const r = hdr.cellRect(i), lift = -(CH + 2);
      const dx = r.cx - (c._x0 + CW / 2), dy = r.cy - (RY + CH / 2);
      tl.to(c, { y: lift }, at, 0.35, E.io);
      tl.to(c, { x: dx }, at + 0.3, 0.45, E.io);
      tl.to(c, { y: dy, sx: r.w / CW, sy: r.h / CH }, at + 0.7, 0.3, E.io);
      tl.text(hdr.vals[i]._t, text, at + 1.0);
      tl.to(c, { o: 0 }, at + 0.95, 0.12);
    };
    // the label under the row: one at a time
    const LY = RY + CH + 34;
    const say = (parts, at, out) => { const l = lab(root, CX, LY, parts, { align: 'center' }).root; fadeIn(tl, l, at, 0.5, 10); if (out != null) fadeOut(tl, l, out, 0.3); return l; };

    // "On the wire, a packet is a sequence of bytes."
    const tB = cue('bytes'), tPa = cue('parse'), tRo = cue('route'), tTe = cue('tele'), tTu = cue('tun'), tAl = cue('all'), tSt = cue('st');
    const bytes = new Row(Math.round(CX - (8 * STEP - GAP) / 2));
    ['45', '00', '00', '3c', '1c', '46', '40', '00'].forEach((t, i) => bytes.append(t, tB - 0.15 + i * 0.07));
    say([['on the wire: bytes']], tB - 0.1, tPa - 0.3);

    // "A switch must parse it: take bytes off the front, and put them into fields."
    const HX = 640;
    const hdr = SX.packetHeader(tl, root, HX, 140, [['f₁', ''], ['f₂', ''], ['sw', '']], { w: 130, h: 90, gap: 14, size: 44, names: 34 });
    hdr.names.forEach(tightEl);   // f₁, not "f ₁"
    hdr.show(tPa - 0.1);
    say([['parsing']], tPa + 0.1, tRo - 0.3);
    fly(bytes.pop(9.45, true), hdr, 0, '45', 9.45);
    fly(bytes.pop(10.4, true), hdr, 1, '00', 10.4);

    // "In source routing, the packet carries its whole route, and each switch takes off the next hop."
    for (const c of bytes.cells) tl.to(c, { o: 0 }, tRo - 0.35, 0.35, E.in);
    for (const i of [0, 1]) { tl.to(hdr.vals[i], { o: 0.4 }, tRo - 0.2, 0.5); tl.to(hdr.names[i], { o: 0.4 }, tRo - 0.2, 0.5); }
    const row = new Row(HX);
    ['B', 'C', 'D'].forEach((t, i) => row.append(t, tRo + 0.05 + i * 0.1));
    say([['source routing: the route']], tRo + 0.2, tTe - 0.3);
    fly(row.pop(17.0, true), hdr, 2, 'B', 17.0);

    // "Telemetry adds a record at every hop."
    say([['telemetry']], tTe - 0.05, tTu - 0.3);
    row.push('t₁', 19.3); row.push('t₂', 20.25);
    // "A tunnel wraps the packet in new headers, and unwraps it later." (an outer IP header begins 45 00)
    say([['a tunnel']], tTu - 0.05, 25.75);
    row.push('00', 22.1); row.push('45', 22.85);
    row.pop(24.3); row.pop(24.85);

    // "Every one of these adds or removes at the front of the packet."
    const fm = softBox(tl, root, HX - 16, RY - 16, CW + 32, CH + 32, 28.25, tSt - 0.5);
    say([['always at the front']], 28.3, tSt - 0.5);

    // "That is a stack.": the cells get the amber outline and swing to an upright pile, the front on top
    hdr.hide(tSt - 0.5, 0.4);
    const PX = 300, BOT = 880, PSTEP = CH + 12, slotY = i => BOT - CH - i * PSTEP;
    const pile = row.cells.slice();          // front first
    const n = pile.length;
    pile.forEach((c, j) => {
      const i = n - 1 - j;                    // slot from the bottom
      tl.to(c._amber, { o: 1 }, tSt - 0.4, 0.5);
      // down to its height first (a staircase), then across: no two cells pass over each other
      tl.to(c, { y: slotY(i) - RY }, tSt - 0.4, 0.4, E.io);
      tl.to(c, { x: PX - CW / 2 - c._x0 }, tSt - 0.05, 0.5, E.io);
    });
    const stl = SX.note(tl, root, PX + CW / 2 + 60, slotY(1) + CH / 2 - 19, 'a stack', tSt + 0.4, seg('stack_b') + 0.25, { align: 'left' });

    // ---- stack_b: "And a stack has no fixed depth. A route can be arbitrarily long."
    const T = seg('stack_b');
    const more = [];
    [0.3, 0.95, 1.6].forEach((d, k) => {
      const i = n + k, c = SX.cell(root, PX - CW / 2, slotY(i), CW, CH, '', { stroke: C.pat, font: MONO, radius: 14 });
      tl.set(c, { y: -90, o: 0 }, 0); tl.to(c, { y: 0 }, T + d, 0.55, E.out5); tl.to(c, { o: 1 }, T + d, 0.3);
      more.push(c);
    });
    // its top fades into "…" (turned upright)
    tl.to(more[2], { o: 0 }, T + 3.5, 0.6); tl.to(more[1], { o: 0.55 }, T + 3.5, 0.6);
    const dots = box(root, PX - 60, slotY(n + 2) + 6, Object.assign(SX.MONO(64), { color: C.dim, width: '120px', height: '84px', lineHeight: '84px', textAlign: 'center' }), '…');
    tl.set(dots, { r: 90 }, 0);
    fadeIn(tl, dots, T + 3.7, 0.6, 0);
    const pileEls = [...pile, more[0], more[1], dots];   // more[2] has gone into the dots

    // "So there are infinitely many packets, and the argument that made NetKAT decidable is gone."
    const XR = 1130;
    const inf = SX.clabel(root, XR, 380, 'infinitely many packets', 40, C.ink);
    fadeIn(tl, inf, T + 6.0, 0.5, 10);
    const dl = SX.cline(root, XR, 450, [['Decidable.', C.good]], SX.SERIF(72));
    fadeIn(tl, dl.root, T + 9.45, 0.6, 12);
    SX.strikeEl(tl, dl.parts[0], T + 10.95);
    // "It looks worse than that."
    for (const e of pileEls) tl.to(e, { o: e === more[1] ? 0.25 : 0.4 }, T + 11.5, 0.6);
    // "A machine with a stack and an input can recognize context-free languages, and whether two context-free
    // languages are equal is undecidable."
    for (const e of [inf, dl.root]) fadeOut(tl, e, T + 13.0, 0.35);
    const l1 = SX.cline(root, XR, 360, [['a stack + an input', null], ['  →  context-free languages', null]], SX.SERIF(52));
    fadeIn(tl, l1.parts[0], T + 13.85, 0.6, 12);
    fadeIn(tl, l1.parts[1], T + 16.5, 0.6, 12);
    const l2 = SX.cline(root, XR, 470, [['L₁ = L₂ ?', null]], SX.SERIF(52));
    fadeIn(tl, l2.root, T + 18.45, 0.6, 12);
    const und = SX.clabel(root, XR, 580, 'undecidable', 32, C.ink);
    fadeIn(tl, und, T + 21.2, 0.5, 10);
    // "So is there any hope?": nothing new
  });
})();

// ==== src/scenes/c.js ====
// StacKAT, the language (lang_a, lang_b), its three laws (laws), the two programs again (puzzle), and why
// equivalence is decidable at all (cool_surprise). Built with SX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = SX;
  const lhOf = s => Math.round(s * 1.3);

  // a small caps label, left edge at x (local: SX.note with align 'left')
  const lnote = (tl, root, x, y, text, at, out, opts = {}) => SX.note(tl, root, x, y, text, at, out, Object.assign({ align: 'left' }, opts));

  // ============================================ lang_a ========================================================
  scene('lang_a', ({ tl, root, cue }) => {
    const B = 700, HX = 598, DX = 360;                         // stack bottom; header's left; the move at `ops`
    const SCX = HX + 478 + 150 + 48;                          // the stack's centre, right of the header
    const LY = 722;                                           // the labels under the packet

    // "In Stack Cat, a packet has two parts: a header, as before, and a stack."
    const tPk = cue('pk');
    const hdr = SX.packetHeader(tl, root, HX, 516, [['sw', 'A'], ['dst', '7'], ['port', '1']]);
    hdr.show(tPk + 1.25);                                     // "packet"
    const hl = SX.note(tl, root, HX + 239, LY, 'a header', tPk + 3.15, null);
    const s = new SX.Stack(tl, root, SCX, B, { items: ['1', '2'], label: 'a stack' });
    s.show(tPk + 4.8);                                        // "stack"

    // "The language adds two operations.": the header dims, the packet makes room; push(n), pop(n) on the left
    const tOps = cue('ops');
    hdr.dim(0.4, tOps - 0.2); hdr.move(DX, 0, tOps - 0.2); s.move(DX, 0, tOps - 0.2);
    fadeOut(tl, hl, tOps - 0.25, 0.3); tl.to(s.labelEl, { o: 0 }, tOps - 0.25, 0.3);
    const S = 64, PY = 360, lh = lhOf(S);
    const pu = SX.prog(tl, root, RAIL, PY, S, 'push(n)');
    const po = SX.prog(tl, root, RAIL, PY + 120, S, 'pop(n)');
    pu.show(tOps + 0.75); po.show(tOps + 0.95);

    // "Push puts a value on top of the stack."
    const tPu = cue('push');
    pu.flip(0, 'push(3)', tPu - 0.2);
    po.dim('all', 0.4, tPu - 0.2);
    s.push('3', tPu + 0.75);

    // "Pop takes a value off the top, but only if it is the value named."
    const tPo = cue('pop');
    po.light('all', tPo - 0.2); pu.dim('all', 0.4, tPo - 0.2);
    const only = lnote(tl, root, RAIL, PY + 120 + lh + 22, 'only if it is the value named', tPo + 2.05, null);

    // "Pop three, on a stack with three on top, removes it."
    const tOk = cue('ok');
    po.flip(0, 'pop(3)', tOk - 0.2);
    tl.to(only, { o: 0.45 }, tOk - 0.2, 0.4);
    s.pop(tOk + 2.55);                                        // "removes"
    const tick = s.ok(tOk + 2.9);

    // "Pop five, on the same stack, drops the packet."
    const tBad = cue('bad');
    tick.hide(tBad - 0.45); fadeOut(tl, only, tBad - 0.45, 0.3);
    s.push('3', tBad - 0.45);
    po.flip(0, 'pop(5)', tBad - 0.2);
    s.fail(tBad + 1.95);                                      // "drops"
    for (const e of [...s.cells]) tl.to(e, { o: 0.25 }, tBad + 2.1, 0.5);
    hdr.dim(0.25, tBad + 2.1);
    const dr1 = SX.note(tl, root, SCX + DX, LY, 'dropped', tBad + 2.0, null, { color: C.bad });

    // "So does a pop on an empty stack."
    const tEm = cue('empty');
    hdr.hide(tEm - 0.3); s.hide(tEm - 0.3); fadeOut(tl, dr1, tEm - 0.3, 0.3);
    const ECX = 1150;                                          // the empty stack: in the middle of the free space
    const s2 = new SX.Stack(tl, root, ECX, B, { ghost: true, label: 'empty' });
    s2.show(tEm - 0.1);
    po.flip(0, 'pop(3)', tEm + 0.28);                         // "pop"
    s2.fail(tEm + 1.0);                                       // "empty stack"
    SX.note(tl, root, ECX, LY + 58, 'dropped', tEm + 1.25, null, { color: C.bad });

    // "A pop is a test and an action in one."
    const tG = cue('guard');
    po.pulse('all', tG - 0.05);
    SX.note(tl, root, CX, 850, 'a test and an action in one', tG + 0.6, null, { color: C.ink });
  });

  // ============================================ lang_b ========================================================
  scene('lang_b', ({ tl, root, cue }) => {
    // "These two are enough.": the two operations again
    const two = SX.prog(tl, root, CX, 450, 64, 'push(n)    pop(n)', { align: 'center' });
    two.show(cue('sugar') - 0.15, { stagger: 0.2 }); two.hide(cue('route') - 0.35, 0.35);

    // "Source routing is one line: pop the top of the stack into the switch field."
    const tR = cue('route');
    const lab1 = SX.note(tl, root, CX, 142, 'source routing', tR - 0.15, null);
    const route = SX.prog(tl, root, CX, 260 - Math.round(lhOf(72) / 2), 72, 'pop(sw)', { align: 'center' });
    route.show(tR + 0.85);                                    // "one line"

    // "That is shorthand for a choice: pop one and go to switch one, or pop two ..., and so on."
    const tS = cue('short');
    const lab2 = SX.note(tl, root, CX, 374, 'shorthand for', tS + 0.25, null);
    const sh = SX.prog(tl, root, CX, 434, 48, 'pop(1) · sw:=1  +  pop(2) · sw:=2  +  …', { align: 'center' });
    sh.show(tS + 2.05, { sel: { from: 0, to: 2 }, stagger: 0.12 });   // "pop one and go to switch one"
    sh.show(tS + 4.3, { sel: 3 });                                     // "or"
    sh.show(tS + 4.85, { sel: { from: 4, to: 6 }, stagger: 0.12 });   // "pop two"
    sh.show(tS + 6.95, { sel: { from: 7, to: 8 }, stagger: 0.15 });   // "and so on"

    // "That works because there are finitely many values."
    const tF = cue('finite');
    const lab3 = SX.note(tl, root, CX, 528, 'finitely many values', tF + 1.1, null);

    // "Parsing a header pops into one field after another."
    const tP = cue('parse');
    SX.dim(tl, [lab1, route, lab2, sh, lab3], 0.4, tP - 0.2, 0.5);
    const LX = 560, RX = 1360, Y = 640, S = 56;
    SX.note(tl, root, LX, Y + lhOf(S) + 20, 'parsing', tP - 0.15, null);
    const pa = SX.prog(tl, root, LX, Y, S, 'pop(f₁) · pop(f₂)', { align: 'center' });
    pa.show(tP + 0.5, { sel: 0 }); pa.show(tP + 1.85, { sel: { from: 1, to: 2 }, stagger: 0.1 });

    // "And telemetry is a push."
    const tT = cue('tele');
    SX.note(tl, root, RX, Y + lhOf(S) + 20, 'telemetry', tT + 0.15, null);
    SX.prog(tl, root, RX, Y, S, 'push(n)', { align: 'center' }).show(tT + 1.05);
  });

  // ============================================ laws ==========================================================
  scene('laws', ({ tl, root, cue }) => {
    // "... and equivalence is as before."
    const tM = cue('mean');
    const eq = SX.prog(tl, root, CX, 450 - Math.round(lhOf(80) / 2), 80, 'e₁ ≡ e₂', { align: 'center' });
    eq.show(tM + 3.75, { stagger: 0.08 }); eq.hide(cue('but') - 0.3, 0.35);

    // "But push and pop interact, and three laws say how."
    SX.note(tl, root, RAIL, 130, 'three laws', cue('but') + 2.1, null, { align: 'left' });

    const RY = [250, 450, 650], LX = 260, S = 56, lh = lhOf(S), cw = charWidth(S), SCX = 1290;
    const ST = { w: 72, h: 62, gap: 10, size: 36, rest: true }, SH = 78;   // SH: half the height of a rest cell and one cell
    const rows = [[], [], []];
    const law = (i, text, opts) => { const p = SX.prog(tl, root, LX, RY[i] - lh / 2, S, text, opts); rows[i].push(p.root); return p; };
    const num = (i, at) => rows[i].push(lnote(tl, root, RAIL, RY[i] - 20, String(i + 1), at, null));
    const stack = (i, items) => { const s = new SX.Stack(tl, root, SCX, RY[i] + SH, Object.assign({ items }, ST)); rows[i].push(s.g); return s; };
    const back = (i, at) => { for (let k = 0; k < i; k++) SX.dim(tl, rows[k], 0.5, at, 0.5); };
    const dropped = (i, s, at) => rows[i].push(lnote(tl, root, SCX + ST.w / 2 + 92, s.topY() + ST.h / 2 - 20, 'dropped', at, null, { color: C.bad }));

    // "One. Push a value and then pop the same value: nothing has happened. That is equivalent to the program one."
    const t1 = cue('l1');
    num(0, t1 - 0.1);
    const L1 = law(0, 'push(v) · pop(v) ≡ 1', { colors: { '≡': C.good } });
    L1.show(t1 + 0.55, { sel: 0 }); L1.show(t1 + 1.85, { sel: [1, 2], stagger: 0.1 });
    const s1 = stack(0, []);
    s1.show(t1 + 0.6); s1.push('v', t1 + 1.1); s1.pop(t1 + 2.05);
    // the tick beside the rest cell, which is the stack's top again (s1.ok would put it over the empty slot)
    SX.tick(tl, s1.svg, SCX + ST.w / 2 + 50, s1.bottom - s1.restH / 2, 48, t1 + 3.4, { width: 7 });   // "nothing has happened"
    L1.show(t1 + 5.3, { sel: [3, 4], stagger: 0.12 });        // "equivalent to the program one"

    // "Two. Push a value and then pop a different value: the pop fails. That is equivalent to zero."
    const t2 = cue('l2');
    back(1, t2 - 0.15); num(1, t2 - 0.1);
    const L2 = law(1, 'push(v) · pop(w) ≡ 0', { colors: { '≡': C.good } });
    L2.show(t2 + 0.6, { sel: 0 }); L2.show(t2 + 1.7, { sel: [1, 2], stagger: 0.1 });
    const ne = box(root, LX + 22 * cw, RY[1] - lhOf(44) / 2, Object.assign(SX.MONO(44), { color: C.dim, whiteSpace: 'pre' }), 'v ≠ w');
    rows[1].push(ne);
    fadeIn(tl, ne, t2 + 2.25, 0.5, 12);                       // "different"
    const s2 = stack(1, []);
    s2.show(t2 + 0.65); s2.push('v', t2 + 0.95);
    s2.fail(t2 + 3.55);                                       // "fails"
    dropped(1, s2, t2 + 3.8);
    L2.show(t2 + 5.35, { sel: [3, 4], stagger: 0.12 });       // "equivalent to zero"

    // "The third is subtle. Pop a value and then push it back."
    const t3 = cue('l3');
    back(2, t3 - 0.15); num(2, t3 - 0.1);
    const L3 = law(2, 'pop(v) · push(v) + 1 ≡ 1', { colors: { '≡': C.good } });
    L3.show(t3 + 1.5, { sel: 0 }); L3.show(t3 + 2.75, { sel: [1, 2], stagger: 0.1 });

    // "That is not equivalent to the program one, because it drops every packet that does not have that value on top."
    const tN = cue('not1');
    const neq = SX.prog(tl, root, LX + 17 * cw, RY[2] - lh / 2, S, '≢ 1', { colors: { '≢': C.bad } });
    rows[2].push(neq.root);
    neq.show(tN + 0.2, { stagger: 0.12 });
    const s3 = stack(2, ['w']);
    s3.show(tN + 2.35);                                       // "because"
    const x3 = s3.fail(tN + 3.0);                             // "drops"

    // "But when it does not drop the packet, it changes nothing."
    const tL = cue('le');
    x3.hide(tL - 0.2); s3.flip(0, 'v', tL - 0.15);
    s3.pop(tL + 0.85); s3.push('v', tL + 1.6);
    s3.ok(tL + 2.05);                                         // "changes nothing"

    // "So a choice between the program one and this pop-then-push is just the program one."
    const tA = cue('abs');
    neq.hide(tA - 0.2, 0.35);
    L3.show(tA + 1.2, { sel: [3, 4], stagger: 0.12 });        // "the program one"
    L3.show(tA + 3.65, { sel: [5, 6], stagger: 0.12 });       // "is just the program one"
  });

  // ============================================ puzzle ========================================================
  scene('puzzle', ({ tl, root, cue }) => {
    const S = 60, cw = charWidth(S), TS = 48, LBX = 900;
    // "Push A any number of times, then pop A any number of times."
    const tP1 = cue('p1');
    const P1 = SX.prog(tl, root, RAIL, 170, S, 'push(a)* · pop(a)*');
    P1.show(tP1 - 0.2);
    const T1 = SX.prog(tl, root, RAIL, 330, TS, 'push(a)  push(a)  push(a)  pop(a)  pop(a)');
    T1.show(tP1 + 0.55, { sel: [0, 1, 2], stagger: 0.25 }); T1.show(tP1 + 2.3, { sel: [3, 4], stagger: 0.25 });

    // "By the first law, each push cancels against a pop."
    const tC = cue('cancel');
    T1.strike([2, 3], tC + 1.45, { out: tC + 2.05 }); T1.hideParts([2, 3], tC + 2.05);
    T1.strike(1, tC + 2.4, { out: tC + 3.0 }); T1.strike(4, tC + 2.4, { out: tC + 3.0 });
    T1.hideParts([1, 4], tC + 3.0);                           // apart: one strike each

    // "If there were more pushes, some pushes are left. If there were more pops, some pops are left."
    const tN = cue('net');
    const tlY = (y) => y + Math.round(lhOf(TS) / 2) - 20;
    const n1 = lnote(tl, root, LBX, tlY(330), 'more pushes: pushes are left', tN + 0.35, null);
    const T2 = SX.prog(tl, root, RAIL, 450, TS, 'push(a)  pop(a)  pop(a)');
    T2.show(tN + 2.8, { stagger: 0.2 });                      // "If there were more pops"
    T2.strike([0, 1], tN + 4.1, { out: tN + 4.7 }); T2.hideParts([0, 1], tN + 4.7);
    const n2 = lnote(tl, root, LBX, tlY(450), 'more pops: pops are left', tN + 5.05, null);

    // "That is what the second program does."
    const tP2 = cue('p2');
    T1.hide(tP2 - 0.3, 0.35); T2.hide(tP2 - 0.3, 0.35); fadeOut(tl, n1, tP2 - 0.3, 0.35); fadeOut(tl, n2, tP2 - 0.3, 0.35);
    const P2 = SX.prog(tl, root, RAIL + 2 * cw, 300, S, 'push(a)* + pop(a)*');
    P2.show(tP2 + 0.4);

    // "So they are equivalent.": a green ≡ at the left margin of the second line
    const tEq = cue('eq');
    const eq = SX.prog(tl, root, RAIL, 300, S, '≡', { colors: { '≡': C.good } });
    tl.set(eq.parts[0].el, { s: 0.6 }, 0);
    eq.show(tEq - 0.2, { rise: 0 }); tl.to(eq.parts[0].el, { s: 1 }, tEq - 0.2, 0.5, E.out5);

    // "Here is a third program: push A an even number of times, then pop it an even number of times."
    const tP3 = cue('p3');
    SX.dim(tl, [P1, P2, eq], 0.45, tP3 - 0.2, 0.5);
    const S3 = 52, cw3 = charWidth(S3), Y3 = 480;
    const PE = SX.prog(tl, root, RAIL + 2 * cw3, Y3, S3, '(push(a) · push(a))* · (pop(a) · pop(a))*');
    PE.show(tP3 + 1.75, { sel: { from: 0, to: 5 } });        // "push A an even number"
    PE.show(tP3 + 4.3, { sel: { from: 6, to: 12 } });        // "then pop it an even number"

    // "It is not equivalent to the first."
    const tNe = cue('neq');
    SX.prog(tl, root, RAIL, Y3, S3, '≢', { colors: { '≢': C.bad } }).show(tNe + 0.1);
    lnote(tl, root, RAIL, Y3 + lhOf(S3) + 18, 'not equivalent to the first', tNe + 0.35, null, { color: C.bad });

    // "The first can take a stack that holds a single A, and empty it. The third cannot."
    const tW = cue('wit');
    const LCX = 700, RCX = 1220, B = 800;
    SX.prog(tl, root, LCX, 640, 36, 'push(a)* · pop(a)*', { align: 'center' }).show(tW - 0.05, { stagger: 0.02 });
    const sl = new SX.Stack(tl, root, LCX, B, { items: ['a'], ghost: true });
    sl.show(tW + 1.0);                                        // "stack"
    sl.pop(tW + 3.05);                                        // "empty it"
    sl.ok(tW + 3.45);
    SX.note(tl, root, LCX, B + 22, 'emptied', tW + 3.55, null, { color: C.good });
    SX.note(tl, root, RCX, 650, 'the even program', tW + 4.0, null);   // "The third"
    const sr = new SX.Stack(tl, root, RCX, B, { items: ['a'] });
    sr.show(tW + 4.05);
    sr.fail(tW + 4.75);                                       // "cannot"
    SX.note(tl, root, RCX, B + 22, 'cannot', tW + 5.0, null);
    // "We want a machine to tell such cases apart, for any two programs.": nothing new
  });

  // ============================================ cool_surprise =================================================
  scene('cool_surprise', ({ tl, root, cue }) => {
    // "Equivalence of Stack Cat programs is decidable."
    const tD = cue('dec');
    const dec = SX.cserif(root, CX, 350, 'Decidable.', 130, C.good);
    dec.style.transformOrigin = 'center top';
    fadeIn(tl, dec, tD + 2.05, 0.7, 20);                      // "decidable"

    // "The stack is unbounded, and programs may use it in any way they like,"
    const tU = cue('unb');
    const u1 = SX.note(tl, root, CX - 380, 590, 'an unbounded stack', tU - 0.05, null);
    const u2 = SX.note(tl, root, CX + 380, 590, 'used without restriction', tU + 2.15, null);   // "may use it"
    // "yet the question can always be answered.": nothing new

    // "What makes it possible is that a program has no input other than the packet itself."
    const tK = cue('key');
    fadeOut(tl, u1, tK - 0.3, 0.3); fadeOut(tl, u2, tK - 0.3, 0.3);
    tl.to(dec, { y: 130 - 350, s: 72 / 130 }, tK - 0.25, 0.8, E.io);
    const svg = SX.svg(root);
    const BX = 740, BY = 470, BW = 440, BH = 240, MY = BY + BH / 2;
    const pb = box(root, BX, BY, { width: BW + 'px', height: BH + 'px', borderRadius: '18px', boxShadow: `inset 0 0 0 3px ${C.ink}` });
    SX.ctext(pb, BW / 2, BH / 2, 'program', Object.assign(SX.LABEL(36), { color: C.ink }), 60);
    fadeIn(tl, pb, tK + 1.55, 0.6, 14);                       // "a program"
    const ST = { items: ['', ''], rest: true }, ICX = 440, OCX = 1480, SB = 740;
    const sIn = new SX.Stack(tl, root, ICX, SB, Object.assign({ label: 'in' }, ST));
    sIn.show(tK + 2.35);                                      // "input"
    SX.line(tl, svg, ICX + 48 + 24, MY, BX - 24, MY, { at: tK + 2.6 });
    SX.line(tl, svg, BX + BW + 24, MY, OCX - 48 - 24, MY, { at: tK + 3.4 });
    const sOut = new SX.Stack(tl, root, OCX, SB, Object.assign({ label: 'out' }, ST));
    sOut.show(tK + 3.7);                                      // "the packet itself"

    // "The stack is not working memory for reading some other input. It is the input, and it is the output."
    const tS = cue('scratch');
    const N = 5, CW = 84, CH = 70, G = 14, RW = N * CW + (N - 1) * G, RX = CX - RW / 2, RY = 330;
    const row = box(root, RX, RY, { width: RW + 'px', height: CH + 'px' });
    for (let k = 0; k < N; k++) box(row, k * (CW + G), 0, { width: CW + 'px', height: CH + 'px', borderRadius: '12px', border: `3px dashed ${C.ink}`, boxSizing: 'border-box' });
    fadeIn(tl, row, tS + 1.9, 0.5, 12);                       // "reading some other input"
    const rl = SX.note(tl, root, CX, RY - 58, 'a separate input', tS + 1.95, null);
    // the neutral grey strike through the row (local: SX.strikeEl wants a text span)
    const bar = box(root, RX - 16, RY + CH / 2 - 2, { width: (RW + 32) + 'px', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
    tl.set(bar, { sx: 0, o: 0 }, 0); tl.set(bar, { o: 1 }, tS + 2.7); tl.to(bar, { sx: 1 }, tS + 2.7, 0.45, E.io);
    tl.to(row, { o: 0.35 }, tS + 2.7, 0.45); tl.to(rl, { o: 0.5 }, tS + 2.7, 0.45);
    SX.note(tl, root, CX, 850, 'the stack is the input and the output', tS + 4.15, null);   // "It is the input"
  });
})();

// ==== src/scenes/d.js ====
// Deciding equivalence, steps one and two: proc_a, step1, and step2 with cool_two (one scene, so that the
// equation of step2 stays on screen through cool_two). Built with SX (common.js).
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const { CX, RAIL } = SX;
  const K = 1.05;   // the scale of A1 and A2 in this file: edge labels 36 * 1.05 = 37.8 px

  // a label in ink or dim, left edge at x, vertically centred on cy
  const lab = (root, x, cy, text, color = C.dim, size = 32) => box(root, x, cy - size * 0.62, Object.assign(SX.LABEL(size), { color, whiteSpace: 'pre' }), text);
  // a centred mono line of one colour (for ≡ ≠ = ∩)
  const sign = (root, cx, cy, text, size, color) => SX.ctext(root, cx, cy, text, Object.assign(SX.MONO(size), { color }), Math.round(size * 1.3));

  // the step header: "STEP n · NAME" in ink on the rail, the law right of it (mono 44)
  function header(tl, root, step, law, atLabel, atLaw) {
    const cy = 178;
    const l = lab(root, RAIL, cy, step, C.ink);
    fadeIn(tl, l, atLabel, 0.5, 10);
    const p = SX.prog(tl, root, 620, cy - Math.round(44 * 1.3 / 2), 44, law, { colors: { '≡': C.good } });
    p.show(atLaw);
    return { l, p };
  }

  // a small automaton glyph: two circles and an arrow, centred on (cx, cy), drawn in at `at`
  function glyph(tl, svg, cx, cy, at) {
    const r = 22, d = 58;
    const a = path(tl, svg, SX.circleD(cx - d, cy, r), { stroke: C.ink, width: 3 });
    const b = path(tl, svg, SX.circleD(cx + d, cy, r), { stroke: C.ink, width: 3 });
    tl.to(a, { draw: 1 }, at, 0.4, E.io); tl.to(b, { draw: 1 }, at + 0.15, 0.4, E.io);
    const ar = SX.line(tl, svg, cx - d + r + 6, cy, cx + d - r - 6, cy, { at: at + 0.3, dur: 0.35, head: 11 });
    return [a, b, ar.path, ar.head];
  }

  // ============================================ proc_a ========================================================
  scene('proc_a', ({ tl, root, cue }) => {
    // "We start with programs that only push and pop.": P1 on the rail
    const tS = cue('start');
    const P1 = SX.prog(tl, root, RAIL, 170, 60, 'push(a)* · pop(a)*');
    P1.show(tS - 0.25);
    const pcy = 170 + Math.round(60 * 1.3) / 2, lx = RAIL + P1.width + 64;
    const l1 = lab(root, lx, pcy, 'push and pop only');
    fadeIn(tl, l1, 3.3, 0.5, 10);
    // "Such a program is a regular expression": the label changes
    const tR = cue('regex');
    fadeOut(tl, l1, 8.3, 0.3, -8);
    const l2 = lab(root, lx, pcy, 'a regular expression');
    fadeIn(tl, l2, 8.45, 0.5, 10);

    // "Each word it matches is a trace": a column of traces
    const tT = cue('traces'), TS = 44, TY = 300, PITCH = 78, tlh = Math.round(TS * 1.3);
    const empty = box(root, RAIL, TY, Object.assign(SX.MONO(TS), { color: C.dim, lineHeight: tlh + 'px', whiteSpace: 'pre' }), '(empty)');
    fadeIn(tl, empty, tT - 0.15, 0.5, 12);
    const trs = ['push(a)', 'push(a)  pop(a)', 'push(a)  push(a)  pop(a)', 'pop(a)  pop(a)'].map((t, i) => {
      const p = SX.prog(tl, root, RAIL, TY + (i + 1) * PITCH, TS, t);
      p.show(tT + 0.25 + i * 0.4, { stagger: 0.05 });
      return p;
    });
    const more = box(root, RAIL, TY + 5 * PITCH, Object.assign(SX.MONO(TS), { color: C.dim, lineHeight: tlh + 'px' }), '…');
    fadeIn(tl, more, tT + 1.9, 0.5, 12);
    const l3 = box(root, RAIL, TY + 6 * PITCH + 4, Object.assign(SX.LABEL(32), { whiteSpace: 'pre' }), 'its traces');
    fadeIn(tl, l3, 14.2, 0.5, 10);
    const traceEls = [empty, ...trs.map(p => p.root), more, l3];

    // "A regular expression can be turned into a finite automaton": the traces dim; A1 on the right
    const tA = cue('aut');
    SX.dim(tl, traceEls, 0.4, tA - 0.1);
    const A = SX.A1(tl, root, 1300, 500, { k: K });
    A.draw('e', 21.25); A.draw('e@', 21.75); A.draw('e>e0', 22.3); A.draw('e0', 22.55); A.draw('e0@', 23.1);
    const b = A.bounds();
    const l4 = SX.clabel(root, 1300, 500 + (b.y1 - 500) * K + 50, 'a finite automaton', 32);
    fadeIn(tl, l4, 21.4, 0.5, 10);
    // "and a machine can compare two finite automata": nothing new
    // "But the traces are not the meaning.": everything dims
    const tP = cue('problem');
    const all = [P1.root, l2, ...traceEls, A.g, l4];
    SX.dim(tl, all, 0.3, tP - 0.1);

    // "Take a choice between the program one, and a pop followed by a push of the same value."
    const tE = cue('ex');
    for (const e of all) tl.to(e, { o: 0 }, tE - 0.3, 0.4, E.in);
    const S = 52, lh = Math.round(S * 1.3), XP = 445, XS = 1330, Y1 = 290, Y2 = 500;
    const r1 = SX.prog(tl, root, XP, Y1, S, '1 + pop(v) · push(v)', { align: 'center' });
    r1.show(32.45, { sel: 0 }); r1.show(33.05, { sel: { from: 1 }, stagger: 0.3 });
    const dimEmpty = { '(': C.dim, 'empty': C.dim, ')': C.dim };
    // "It has two traces."
    const s1 = SX.prog(tl, root, XS, Y1, S, '{ (empty),  pop(v) push(v) }', { align: 'center', colors: dimEmpty });
    s1.show(36.75, { stagger: 0.03 });
    // "The program one alone has a single trace, the empty one."
    const r2 = SX.prog(tl, root, XP, Y2, S, '1', { align: 'center' });
    r2.show(38.7);
    const s2 = SX.prog(tl, root, XS, Y2, S, '{ (empty) }', { align: 'center', colors: dimEmpty });
    s2.show(40.0, { stagger: 0.03 });
    const mid = (Y1 + lh + Y2) / 2;
    const ne = sign(root, XS, mid, '≠', 64, C.ink);
    fadeIn(tl, ne, 41.05, 0.5, 8);
    const ld = SX.clabel(root, XS, Y2 + lh + 50, 'different traces', 32);
    fadeIn(tl, ld, 41.2, 0.5, 10);
    // "Yet by the third law, they mean the same."
    const eq = sign(root, XP, mid, '≡', 64, C.good);
    fadeIn(tl, eq, 43.9, 0.5, 8);
    const lm = SX.clabel(root, XP, Y2 + lh + 50, 'the same meaning', 32);
    fadeIn(tl, lm, 44.05, 0.5, 10);
    // "... in three steps, one for each law."
    const lp = SX.clabel(root, CX, 790, 'three steps: one for each law', 32, C.ink);
    fadeIn(tl, lp, 49.95, 0.5, 10);
  });

  // ============================================ step1 =========================================================
  scene('step1', ({ tl, root, cue }) => {
    // "Step one is to cancel. It uses the first law."
    header(tl, root, 'step 1 · cancel', 'push(v) · pop(v) ≡ 1', cue('s1') - 0.2, 3.3);

    // "Wherever the automaton can do a push and then a pop of the same value, possibly with silent steps"
    const Q = new SX.Automaton(tl, root, { cx: CX, cy: 400 });
    const xs = [420, 780, 1140, 1500];
    xs.forEach((x, i) => Q.state('q' + (i + 1), x, 400, { name: 'q' + '₁₂₃₄'[i] }));
    Q.edge('q1>q2', 'q1', 'q2', 'push(v)').silent('q2~q3', 'q2', 'q3', { tag: 'silent' }).edge('q3>q4', 'q3', 'q4', 'pop(v)');
    Q.silent('q1~q4', 'q1', 'q4', { bend: 250 });
    const tP = cue('path');
    ['q1', 'q2', 'q3', 'q4'].forEach((id, i) => Q.draw(id, tP + 0.1 + i * 0.15, 0.45));
    Q.draw('q1>q2', 6.5); Q.draw('q3>q4', 7.25); Q.draw('q2~q3', 9.75, 0.6);
    // "add a shortcut between the same two states that does nothing."
    Q.draw('q1~q4', cue('eps') + 0.05, 0.8);
    // "Repeat until nothing new appears."
    const lr = SX.clabel(root, CX, 640, 'repeat until nothing new', 32);
    fadeIn(tl, lr, cue('rep') - 0.15, 0.5, 10);

    // "In our automaton, the loop pushes A, and the next edge pops A. So we add a silent edge beside them."
    const tX = cue('ex');
    Q.hide(tX - 0.3); fadeOut(tl, lr, tX - 0.3, 0.3);
    const A = SX.A1(tl, root, CX, 450, { k: K, silent: true });
    A.drawAll(tX + 0.05, { stagger: 0.18, except: ['e~e0'], dur: 0.45 });
    A.pulse('e@', 19.55); A.mark('e@', 19.55, { out: 24.6 });
    A.pulse('e>e0', 21.3); A.mark('e>e0', 21.3, { out: 24.6 });
    A.draw('e~e0', 23.75, 0.8);

    // "The automaton now accepts every trace it had, and also every trace in which matching pushes and pops
    // have been cancelled."
    const S = 48, cw = charWidth(S), lh = Math.round(S * 1.3), TY = 690;
    const n1 = 24, n2 = 7, gap = 54, aw = 110, tot = (n1 + n2) * cw + 2 * gap + aw, x0 = Math.round(CX - tot / 2);
    const tr = SX.prog(tl, root, x0, TY, S, 'push(a)  push(a)  pop(a)');
    tr.show(27.65, { stagger: 0.06 });
    tr.strike([tr.letter(1), tr.letter(2)], 30.75);
    const svg = SX.svg(root), ax = x0 + n1 * cw + gap;
    SX.line(tl, svg, ax, TY + lh / 2, ax + aw, TY + lh / 2, { at: 31.4, dur: 0.4 });
    const res = SX.prog(tl, root, ax + aw + gap, TY, S, 'push(a)');
    res.show(31.6);
    const la = SX.clabel(root, CX, TY + lh + 30, 'also accepted now', 32);
    fadeIn(tl, la, 31.85, 0.5, 10);
  });

  // ============================================ step2 + cool_two =============================================
  scene(['step2', 'cool_two'], ({ tl, root, cue, seg }) => {
    const c = n => cue('step2.' + n), T2 = seg('cool_two');
    // "Step two is to filter." (the law arrives with "by the second law")
    const hd = header(tl, root, 'step 2 · filter', 'push(v) · pop(w) ≡ 0', c('s2') - 0.2, 10.6);

    // "Take a trace in which a push is followed directly by a pop."
    const S = 52, lh = Math.round(S * 1.3);
    const t1 = SX.prog(tl, root, CX, 300, S, '…  push(v)  pop(w)  …', { align: 'center' });
    t1.show(c('look') + 0.1, { stagger: 0.06 });
    const pair1 = [t1.letter(0), t1.letter(1)];
    t1.mark(pair1, C.dim, 3.85, { fill: 0.08, out: 11.75 });
    // "If the two values differ, the trace drops every packet, by the second law. It contributes nothing."
    t1.flip(pair1[0], 'push(a)', 7.3); t1.flip(pair1[1], 'pop(b)', 7.45);
    const l1 = SX.clabel(root, CX, 300 + lh + 26, 'drops every packet', 32);
    fadeIn(tl, l1, 8.8, 0.5, 10);
    t1.strike('all', 11.75);

    // "If they are the same, step one has already added the trace without them. It is redundant."
    const tSm = c('same');
    SX.dim(tl, [t1.root, l1], 0.4, tSm - 0.1);
    const Y2 = 490;
    const t2 = SX.prog(tl, root, CX, Y2, S, '…  push(a)  pop(a)  …', { align: 'center' });
    t2.show(14.0, { stagger: 0.06 });
    t2.mark([t2.letter(0), t2.letter(1)], C.dim, 14.3, { fill: 0.08, out: 18.15 });
    const l2 = SX.clabel(root, CX, Y2 + lh + 26, 'already there without the pair', 32);
    fadeIn(tl, l2, 15.6, 0.5, 10);
    t2.strike('all', 18.15);

    // "So we keep only the traces with no such pair: all pops come before all pushes."
    const tF = c('filter');
    for (const e of [t1.root, l1, t2.root, l2]) fadeOut(tl, e, tF - 0.3, 0.35);
    const FY = 400;
    const f = SX.prog(tl, root, CX, FY, 56, 'pop … pop  push … push', { align: 'center' });
    f.show(tF + 0.2, { stagger: 0.05 });
    const lf = SX.clabel(root, CX, FY + Math.round(56 * 1.3) + 30, 'keep: pops, then pushes', 32);
    fadeIn(tl, lf, 22.45, 0.5, 10);

    // "On automata, that is an intersection with the automaton for pops, then pushes"
    const tI = c('inter');
    f.hide(tI - 0.3, 0.35); fadeOut(tl, lf, tI - 0.3, 0.3);
    const A1 = SX.A1(tl, root, 520, 520, { k: K, silent: true });
    A1.drawAll(tI + 0.05, { stagger: 0.1, dur: 0.4 });
    const cap = sign(root, 950, 535, '∩', 96, C.ink);
    fadeIn(tl, cap, 26.6, 0.5, 10);
    const PP = SX.PP(tl, root, 1400, 520);
    PP.draw('s', 27.75); PP.draw('s@', 28.4); PP.draw('s>t', 29.2); PP.draw('t', 29.45); PP.draw('t@', 29.9);

    // "For our program, the result has two branches: pops only, or pushes only."
    const tRs = c('res');
    A1.hide(tRs - 0.3); PP.hide(tRs - 0.3); fadeOut(tl, cap, tRs - 0.3, 0.3);
    for (const e of [hd.l, hd.p.root]) tl.to(e, { o: 0 }, tRs - 0.3, 0.4, E.in);
    const AY = 585, XL = 590, XR = 1390;
    const L = SX.A2(tl, root, XL, AY, { k: K });
    L.draw('e', 33.2); L.draw('e>e1', 34.85); L.draw('e1', 35.0); L.draw('e1@', 35.45);
    L.draw('e>e2', 36.1); L.draw('e2', 36.25); L.draw('e2@', 36.65);
    // the programs above the automata; they become the two sides of the equation (group g, moved in cool_two)
    const EY = 200, PS = 44, ES = 60, PY = EY - Math.round(PS * 1.3) / 2;
    const g = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const ll = SX.clabel(root, XL, PY - 46, 'after steps 1 and 2', 32);
    fadeIn(tl, ll, tRs + 0.1, 0.5, 10);
    const pl = SX.prog(tl, g, XL, PY, PS, 'push(a)* · pop(a)*', { align: 'center' });
    pl.show(tRs + 0.4, { stagger: 0.03 });
    // "And that is exactly the automaton of the second program."
    const R = SX.A2(tl, root, XR, AY, { k: K });
    R.drawAll(c('p2') - 0.1, { stagger: 0.12, dur: 0.4 });
    const eqs = sign(root, 950, AY, '=', 96, C.good);
    fadeIn(tl, eqs, 38.55, 0.5, 8);
    const pr = SX.prog(tl, g, XR, PY, PS, 'push(a)* + pop(a)*', { align: 'center' });
    pr.show(39.7, { stagger: 0.03 });

    // "The two programs from the start of the video are equivalent, and this time a procedure has checked it."
    // The automata dim; the two programs grow and move together into one line, mono 60; a green ≡ between.
    const tD = c('done'), cw = charWidth(ES), sc = ES / PS;
    SX.dim(tl, [L.g, R.g, eqs], 0.35, tD - 0.2);
    fadeOut(tl, ll, tD - 0.2, 0.35);
    pl.to({ x: (CX - 11.5 * cw) - XL, s: sc }, 41.7, 0.8);
    pr.to({ x: (CX + 11.5 * cw) - XR, s: sc }, 41.85, 0.8);
    const eq = sign(g, CX, EY, '≡', ES, C.good);
    fadeIn(tl, eq, 43.55, 0.5, 8);
    const gs = SX.svg(g);
    SX.tick(tl, gs, CX + 20.5 * cw + 66, EY, 52, 46.15);

    // cool_two. "Notice what we did.": the automata leave; the equation goes down to y = 300
    const k = n => cue('cool_two.' + n);
    const tN = k('note');
    for (const e of [L.g, R.g, eqs]) tl.to(e, { o: 0 }, tN - 0.3, 0.45, E.in);
    tl.to(g, { y: 300 - EY }, tN - 0.1, 0.8, E.io);
    // "We changed a finite automaton, and compared it with another.": nothing new
    // "When two automata agree after these steps, the programs are equivalent."
    const svg = SX.svg(root), RX = 380, RY1 = 560, RY2 = 720;
    const row = (cy, at, s, col, text, atSign, atLabel) => {
      const els = [...glyph(tl, svg, RX, cy, at), ...glyph(tl, svg, RX + 290, cy, at + 0.2)];
      const sg = sign(root, RX + 145, cy, s, 72, col);
      fadeIn(tl, sg, atSign, 0.5, 8);
      const lb = lab(root, RX + 470, cy, text);
      fadeIn(tl, lb, atLabel, 0.5, 10);
      return [...els, sg, lb];
    };
    const row1 = row(RY1, T2 + 6.45, '=', C.good, 'agree after two steps: equivalent', T2 + 7.35, T2 + 7.6);
    // "But when they disagree, we cannot conclude anything yet. Two steps are not always enough."
    SX.dim(tl, row1, 0.45, k('more') + 0.2);
    row(RY2, k('more') + 0.3, '≠', C.ink, 'disagree: not yet known', T2 + 11.6, T2 + 11.75);
  });
})();

// ==== src/scenes/e.js ====
// Deciding equivalence, step three: the third law, the pop-push insertion, what a trace says about stacks,
// zipping (a trace read from the middle outwards), the zipped automata, and the theorem. Built with SX (common.js).
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = SX;

  // ---- local helpers ---------------------------------------------------------------------------------------
  const lhOf = size => Math.round(size * 1.3);
  const topFor = (cy, size) => cy - lhOf(size) / 2;          // the top of a mono line centred on cy
  // a soft neutral box ("look here") on the stage, at a rectangle
  function ringBox(tl, parent, r, at, { out = null, pad = 8, radius = 16, color = C.dim, fill = 0.08 } = {}) {
    const m = box(parent, r.x - pad, r.y - pad, { width: (r.w + 2 * pad) + 'px', height: (r.h + 2 * pad) + 'px', borderRadius: radius + 'px', background: alpha(color, fill), boxShadow: `inset 0 0 0 2px ${alpha(color, 0.55)}` });
    tl.set(m, { o: 0, s: 0.94 }, 0); tl.to(m, { o: 1, s: 1 }, at, 0.4, E.out5);
    if (out != null) tl.to(m, { o: 0 }, out, 0.35);
    return m;
  }
  // a label left-aligned at x (top y), rising in at `at`
  const leftLabel = (tl, root, x, y, text, at, out, opts = {}) => SX.note(tl, root, x, y, text, at, out, Object.assign({ align: 'left' }, opts));

  // A trace whose letters are separate elements, so that pairs can be dropped into its middle. letters: texts in
  // their final order; layout(present, gaps) centres the letters that are present on cx; a gap keeps room for
  // letters that are not there yet. Each letter is an SX.prog of one part (so it has the film's colours).
  function Trace(tl, root, cx, cy, size, letters, { sep = 2 } = {}) {
    const cw = charWidth(size), y = topFor(cy, size);
    const ls = letters.map(t => ({ t, len: [...t].length, p: SX.prog(tl, root, 0, y, size, t) }));
    // columns of each letter when the letters in `room` take their place (present or a gap)
    const place = room => {
      const idx = ls.map((_, i) => i).filter(i => room.includes(i));
      const total = idx.reduce((s, i) => s + ls[i].len, 0) + sep * (idx.length - 1);
      let x = cx - total * cw / 2; const xs = {};
      for (const i of idx) { xs[i] = x; x += (ls[i].len + sep) * cw; }
      return xs;
    };
    let cur = null;
    return {
      ls, cw, y, lh: lhOf(size),
      // put the letters at the layout `room` (the first call places them; later calls move them)
      layout(room, at, dur = 0.7) {
        const xs = place(room);
        for (const i in xs) {
          const p = ls[i].p;
          if (!cur) { p.root.style.left = xs[i] + 'px'; p.x = xs[i]; p._x0 = xs[i]; }
          else if (p._x0 == null) { p.root.style.left = xs[i] + 'px'; p.x = xs[i]; p._x0 = xs[i]; }
          else tl.to(p.root, { x: xs[i] - p._x0 }, at, dur, E.io);
        }
        cur = xs; return xs;
      },
      xs: room => place(room),
      show(i, at, rise = 14) { ls[i].p.show(at, { rise }); },
      hide(at) { for (const l of ls) l.p.hide(at); },
      dim(o, at) { for (const l of ls) tl.to(l.p.root, { o }, at, 0.5); },
    };
  }

  // ============================================ step3_a =======================================================
  scene('step3_a', ({ tl, root, cue }) => {
    // "Here is the first program with its halves swapped: pop A any number of times, then push A any number of times."
    const S = 60, py = topFor(170, S);
    const P3 = SX.prog(tl, root, RAIL, py, S, 'pop(a)* · push(a)*');
    P3.show(cue('third') - 0.2);
    const A = SX.A3(tl, root, 680, 540);
    // the automaton builds as the program is read: the pops, then the pushes
    A.draw('e', 3.85); A.draw('e>e0', 4.2); A.draw('e0', 4.4); A.draw('e0@', 4.9);
    A.draw('e0>e1', 6.6); A.draw('e1', 6.8); A.draw('e1@', 7.3); A.draw('e>e1', 7.75);
    P3.pulse(P3.letter(0), 3.95); P3.pulse(P3.letter(1), 6.65);

    // "It is equivalent to the other two."
    const tEq = cue('eq');
    const eqx = RAIL + P3.width + 34, S2 = 40;
    const others = SX.prog(tl, root, eqx, topFor(170, S2) + 4, S2, '≡ push(a)* · pop(a)* ≡ push(a)* + pop(a)*', { colors: { '≡': C.good } });
    others.show(tEq - 0.15, { stagger: 0.02 });

    // "But steps one and two leave its automaton as it is."
    const LX = 1250;
    const l1a = leftLabel(tl, root, LX, 400, 'step 1:', 11.85, cue('still') - 0.35);
    const l1b = leftLabel(tl, root, LX, 442, 'nothing to cancel', 11.95, cue('still') - 0.35);
    const l2a = leftLabel(tl, root, LX, 530, 'step 2:', 12.7, cue('still') - 0.35);
    const l2b = leftLabel(tl, root, LX, 572, 'already pops, then pushes', 12.8, cue('still') - 0.35);

    // "It still accepts a pop followed by a push, which the others do not."
    const tr = SX.prog(tl, root, LX, topFor(460, 52), 52, 'pop(a) push(a)');
    tr.show(16.65, { sel: 0 }); tr.show(17.55, { sel: 1 });
    A.pulse('e>e0', 16.7); A.pulse('e0>e1', 17.6);
    const acc = leftLabel(tl, root, LX, 525, 'accepted here', 16.0, null);
    const notb = leftLabel(tl, root, LX, 572, 'not by the other two', 18.4, null);

    // "This is the third law at work: a pop and then a push of the same value is hidden inside the program one."
    const tLaw = cue('law');
    A.dim(0.35, tLaw + 0.3); SX.dim(tl, [tr, acc, notb], 0.35, tLaw + 0.3);
    const law = SX.prog(tl, root, RAIL, topFor(290, 48), 48, 'pop(v) · push(v) + 1 ≡ 1', { colors: { '≡': C.good } });
    law.show(21.0, { stagger: 0.02 });
    law.pulse({ from: 0, to: 2 }, 22.95, { scale: 1.05, dur: 0.8 });
    law.pulse(law.parts.length - 1, 26.4, { dur: 0.7 });

    // "We cannot simply delete such a pair."
    const tCant = cue('cant');
    A.hide(tCant - 0.4); SX.dim(tl, [tr, acc, notb], 0, tCant - 0.4, 0.4);
    P3.to({ o: 0.45 }, tCant - 0.3, 0.5); others.to({ o: 0.45 }, tCant - 0.3, 0.5); law.to({ o: 0.45 }, tCant - 0.3, 0.5);
    const pair = SX.prog(tl, root, CX, topFor(500, 56), 56, 'pop(a) push(a)', { align: 'center' });
    pair.show(tCant - 0.1);
    const st = pair.strike('all', 28.75, { dur: 0.6 });
    st.undo(29.75);
    const cant = SX.note(tl, root, CX, 585, 'cannot just delete', 29.7, null);

    // "So again we add instead."
    const tAdd = cue('add');
    pair.hide(tAdd - 0.1); fadeOut(tl, cant, tAdd - 0.1, 0.35);

    // "In every trace, between the pops and the pushes, insert a pop and a push of the same value.
    //  Do it for every value, and again and again."
    const T = Trace(tl, root, CX, 500, 52, ['pop(1)', 'pop(v)', 'pop(u)', 'push(u)', 'push(v)', 'push(4)']);
    T.layout([0, 5], 0);
    T.show(0, 42.05); T.show(5, 42.15);
    T.layout([0, 1, 4, 5], 43.25);                       // between the pops and the pushes: a gap
    // the pair drops in from above, in a neutral mark
    const xs2 = T.xs([0, 1, 4, 5]), dropY = -70;
    const m1r = { x: xs2[1], y: T.y, w: xs2[4] + 7 * T.cw - xs2[1], h: T.lh };
    const m1 = ringBox(tl, root, m1r, 45.3, { out: 48.45, pad: 10 });
    tl.set(m1, { y: dropY }, 0); tl.to(m1, { y: 0 }, 45.3, 0.6, E.out5);
    T.show(1, 45.2, dropY); T.show(4, 45.25, dropY);
    // again: a second pair into the middle of that
    T.layout([0, 1, 2, 3, 4, 5], 48.45);
    const xs4 = T.xs([0, 1, 2, 3, 4, 5]);
    const m2r = { x: xs4[2], y: T.y, w: xs4[3] + 7 * T.cw - xs4[2], h: T.lh };
    const m2 = ringBox(tl, root, m2r, 49.35, { pad: 10 });
    tl.set(m2, { y: dropY }, 0); tl.to(m2, { y: 0 }, 49.35, 0.6, E.out5);
    T.show(2, 49.25, dropY); T.show(3, 49.3, dropY);
    SX.note(tl, root, CX, 610, 'insert, for every value, again and again', 48.3, null);
  });

  // ============================================ step3_b =======================================================
  scene('step3_b', ({ tl, root, cue }) => {
    const S = 52, R1 = 232, R2 = 600;
    const SK = { w: 96, h: 80, size: 44, gap: 10, rest: true, restH: 104 };
    const sx1 = 1420, sx2 = 1680, svg = SX.svg(root);
    const arrowAt = (yMid, at) => SX.line(tl, svg, sx1 + SK.w / 2 + 26, yMid, sx2 - SK.w / 2 - 26, yMid, { at, dur: 0.45 });

    // "Take: pop one, push four."
    const t1 = SX.prog(tl, root, RAIL, topFor(R1, S), S, 'pop(1) · push(4)');
    t1.show(6.65, { stagger: 0.03 });
    t1.pulse(0, 7.4); t1.pulse(2, 8.25);

    // "It says: a stack with a one on top becomes the same stack with a four on top."
    const b1 = R1 + 97;   // stacks of row 1: [1, …] and [4, …]; 194 px high, centred on the row
    const s1a = new SX.Stack(tl, root, sx1, b1, Object.assign({ items: ['1'] }, SK));
    const s1b = new SX.Stack(tl, root, sx2, b1, Object.assign({ items: ['4'] }, SK));
    s1a.show(10.45); const a1 = arrowAt(R1, 12.05); s1b.show(13.6);

    // "Whatever lies below is untouched."
    const rest1 = [s1a, s1b].map(s => ringBox(tl, root, { x: s.cx - SK.w / 2, y: b1 - s.restH, w: SK.w, h: s.restH }, 15.95, { pad: 7 }));
    const below = SX.note(tl, root, (sx1 + sx2) / 2, b1 + 20, 'anything below,', 16.05, null);
    const below2 = SX.note(tl, root, (sx1 + sx2) / 2, b1 + 62, 'untouched', 16.15, null);

    // "Now insert a pop and a push of a two. The new trace says the same thing, but only for stacks that have a two below."
    const tSp = cue('spell');
    SX.dim(tl, [t1, s1a, s1b, a1.path, a1.head, below, below2, ...rest1], 0.5, tSp - 0.1);
    const t2 = SX.prog(tl, root, RAIL, topFor(R2, S), S, 'pop(1) · pop(2) · push(2) · push(4)');
    t2.show(tSp - 0.1, { sel: [0, 1, 6] });
    t2.show(22.6, { sel: [2, 3, 4, 5], rise: -60, dur: 0.6 });
    t2.mark({ from: 2, to: 4 }, C.dim, 22.7, { fill: 0.08 });
    const b2 = R2 + 142;   // [1, 2, …] and [4, 2, …]: 284 px high, centred on the row
    const s2a = new SX.Stack(tl, root, sx1, b2, Object.assign({ items: ['1', '2'] }, SK));
    const s2b = new SX.Stack(tl, root, sx2, b2, Object.assign({ items: ['4', '2'] }, SK));
    s2a.show(24.9); arrowAt(R2, 25.5); s2b.show(25.75);
    const twos = [s2a, s2b].map(s => ringBox(tl, root, s.slotRect(1), 28.6, { pad: 7, out: 34.9 }));

    // "That is a special case of what we had, so adding it changes nothing in meaning."
    SX.note(tl, root, RAIL, 400, 'a special case of the first', 29.95, null, { align: 'left' });

    // "With every insertion added, there is one trace for each whole input stack, together with its whole output stack."
    const tEx = cue('exact');
    const rows = [...root.children].filter(e => e !== svg && !twos.includes(e));
    for (const e of rows) tl.to(e, { o: 0.45 }, tEx - 0.15, 0.5);
    tl.to(svg, { o: 0.45 }, tEx - 0.15, 0.5);
    const ink = Object.assign({}, { color: C.ink });
    SX.note(tl, root, CX, 778, 'one trace for each whole stack in, and whole stack out', 37.25, null, ink);

    // "And then two programs have the same traces exactly when they relate the same stacks."
    const l = SX.cline(root, CX, 832, [['the same traces', null], ['   ', null], ['   the same stacks related', null]], SX.SERIF(52));
    l.parts[1].appendChild(SX.iff(52));
    fadeIn(tl, l.parts[0], 44.3, 0.6, 12); fadeIn(tl, l.parts[1], 45.35, 0.5, 0); fadeIn(tl, l.parts[2], 46.25, 0.6, 12);
  });

  // ============================================ step3_c =======================================================
  scene('step3_c', ({ tl, root, cue }) => {
    const S = 56, svg = SX.svg(root), Y1 = 280, Y2 = 480;
    const under = p => p.y + p.lh + 6;    // where arcs start, under a line

    // "The inserted pairs nest, like brackets: pop A, pop B, push B, push A."
    const n = SX.prog(tl, root, CX, topFor(Y1, S), S, 'pop(a)  pop(b)  push(b)  push(a)', { align: 'center' });
    n.show(cue('nest') - 0.15, { stagger: 0.05 });
    [5.1, 5.95, 6.9, 7.9].forEach((t, k) => n.pulse(n.letter(k), t));
    const L = k => n.rect(n.letter(k)).cx;
    const na1 = SX.arc(tl, svg, L(1), L(2), under(n), 50, { at: 7.25 });
    const na2 = SX.arc(tl, svg, L(0), L(3), under(n), 100, { at: 8.25, dur: 0.6 });
    // "No finite automaton accepts such a language."
    const nr = SX.note(tl, root, CX, 480, 'no finite automaton accepts this', cue('notreg') - 0.15, null);
    // "The way out is to change how a trace is read."
    const tTr = cue('trick');
    n.hide(tTr - 0.2); fadeOut(tl, nr, tTr - 0.2, 0.4); for (const a of [na1, na2]) tl.to(a, { o: 0 }, tTr - 0.2, 0.4);

    // "Start in the middle, where the pops end and the pushes begin, and read outwards,"
    const tr = SX.prog(tl, root, CX, topFor(Y1, S), S, 'pop(1) · pop(2) · push(3) · push(4)', { align: 'center' });
    tr.show(cue('mid') - 0.2, { stagger: 0.03 });
    const dot = 3, mx = tr.rect(dot).cx;      // the · between pop(2) and push(3)
    const tick = SX.line(tl, svg, mx, tr.y - 22, mx, tr.y + tr.lh + 14, { head: 0, width: 4, at: 16.15, dur: 0.35 });
    tr.dim(dot, 0, 16.15, 0.3);
    const midL = SX.note(tl, root, mx, tr.y - 76, 'the middle', 16.15, cue('zip') - 0.2);
    // "one pop and one push at a time, as a pair."
    const T = k => tr.rect(tr.letter(k)).cx;
    const a1 = SX.arc(tl, svg, T(1), T(2), under(tr), 48, { at: cue('pairs') - 0.15 });
    const a2 = SX.arc(tl, svg, T(0), T(3), under(tr), 96, { at: 21.85, dur: 0.6 });

    // "We call this zipping."
    const zl = box(root, RAIL, 142, Object.assign(SX.LABEL(32), { color: C.ink, whiteSpace: 'pre' }), 'step 3 · zip');
    fadeIn(tl, zl, cue('zip') - 0.15, 0.5, 10);

    // "Here is a trace, and here it is zipped."
    const tEx = cue('ex');
    for (const a of [a1, a2]) tl.to(a, { o: 0.3 }, tEx - 0.1, 0.4);
    tr.pulse('all', tEx, { scale: 1.03 });
    const z = SX.prog(tl, root, CX, topFor(Y2, S), S, '(pop(2), push(3)) · (pop(1), push(4))', { align: 'center' });
    z.show(30.8, { sel: 0 }); tl.to(a1, { o: 1 }, 30.8, 0.3);
    tr.mark([2, 3, 4], C.dim, 30.8, { fill: 0.08, out: 31.6 });
    z.show(31.6, { sel: [1, 2] }); tl.to(a2, { o: 1 }, 31.6, 0.3);
    tr.mark('pop(1)', C.dim, 31.6, { fill: 0.08, out: 32.0 }); tr.mark('push(4)', C.dim, 31.6, { fill: 0.08, out: 32.0 });

    // "When one side runs out, a placeholder fills in."
    const tD = cue('doneph');
    tr.hide(tD - 0.25, 0.35); z.hide(tD - 0.25, 0.35); tick.hide(tD - 0.25); for (const a of [a1, a2]) tl.to(a, { o: 0 }, tD - 0.25, 0.35);
    const d1 = SX.prog(tl, root, CX, topFor(Y1, S), S, 'pop(1) · push(2) · push(3)', { align: 'center' });
    const d2 = SX.prog(tl, root, CX, topFor(Y2, S), S, '(pop(1), push(2)) · (done, push(3))', { align: 'center' });
    d1.show(tD + 0.1, { stagger: 0.03 }); d2.show(tD + 0.45, { stagger: 0.06 });
    // `done` is a part of its zipped letter: a neutral mark on the word itself
    const dl = d2.parts[2], dW = d2.cw * 4, dX = d2.x + (dl.col + 1) * d2.cw;
    ringBox(tl, root, { x: dX, y: d2.y + 6, w: dW, h: d2.lh - 12 }, 33.95, { pad: 6, radius: 10, out: 35.6 });

    // "Nothing is lost: a zipped trace can be unzipped again."
    const ud = SX.prog(tl, root, CX, topFor((Y1 + Y2) / 2 + 4, 64), 64, '↕', { align: 'center' });
    ud.show(cue('lossless') - 0.15, { rise: 0 });

    // "Now the inserted pairs are no longer in the middle. They are at the front, one after another."
    const tF = cue('front');
    d1.hide(tF - 0.25, 0.35); d2.hide(tF - 0.25, 0.35);
    const f1 = SX.prog(tl, root, CX, topFor(Y1, S), S, 'pop(1) · pop(v) · push(v) · push(4)', { align: 'center' });
    const f2 = SX.prog(tl, root, CX, topFor(Y2, S), S, '(pop(v), push(v)) · (pop(1), push(4))', { align: 'center' });
    f1.show(tF + 0.1, { stagger: 0.03 });
    f1.mark({ from: 2, to: 4 }, C.dim, 40.15, { fill: 0.08 });
    f2.show(41.3, { stagger: 0.06 });
    f2.mark(0, C.dim, 43.15, { fill: 0.08 });
    SX.note(tl, root, CX, 560, 'the inserted pair is at the front', 43.15, null);

    // "And that is just a loop at the start."
    const A = new SX.Automaton(tl, root, { size: 36 });
    A.state('s', CX, 830, { name: '', start: true }).loop('s@', 's', '(pop(v), push(v))');
    A.draw('s', cue('loop') - 0.15); A.draw('s@', 46.25);
  });

  // ============================================ step3_d =======================================================
  scene('step3_d', ({ tl, root, cue }) => {
    // "An automaton can be zipped too. The zipped automaton starts in the middle of a run of the original."
    const A = SX.A3(tl, root, CX, 470);
    A.drawAll(cue('auto') - 0.1, { stagger: 0.12, dur: 0.45 });
    A.mark('e0', 4.4, { out: 5.2 }); A.mark('e', 5.15, { out: 5.75 }); A.mark('e1', 5.7, { out: 6.3 });
    A.mark('e0', 6.25, { out: cue('z3') - 0.3 });
    const startL = SX.note(tl, root, CX, 720, 'start in the middle: at any state', 4.4, cue('back') - 0.2);

    // "Each of its steps goes one step backwards through the pops, and one step forwards through the pushes."
    const e0 = A.pos('e0'), e = A.pos('e'), e1 = A.pos('e1');
    A.travel('e>e0', 9.1, 0.9, { reverse: true, out: cue('z3') - 0.3 });
    SX.note(tl, root, (e.x + e0.x) / 2 - 60, 720, 'backwards through the pops', 9.1, null);
    A.travel('e0>e1', 11.5, 0.9, { out: cue('z3') - 0.3 });
    SX.note(tl, root, (e0.x + e1.x) / 2 + 60, 776, 'forwards through the pushes', 11.5, null);

    // "Here is the zipped automaton of the swapped program."
    const tZ3 = cue('z3');
    const keep = new Set();
    const ZL = 520, ZR = 1430, ZY = 545;
    const z3 = SX.Z3(tl, root, ZL, ZY);
    const z1 = SX.Z1(tl, root, ZR, ZY, { loop: true });
    keep.add(z3.g); keep.add(z1.g);
    // everything before this leaves
    const before = [...root.children].filter(x => !keep.has(x));
    tl.to(A.g, { o: 0 }, tZ3 - 0.3, 0.35, E.in);
    const S = 40;
    const n3 = SX.prog(tl, root, ZL, topFor(150, S), S, 'pop(a)* · push(a)*', { align: 'center' });
    const n1 = SX.prog(tl, root, ZR, topFor(150, S), S, 'push(a)* · pop(a)*', { align: 'center' });
    z3.drawAll(14.15, { stagger: 0.2 }); n3.show(14.2);
    z1.drawAll(cue('z1') + 0.05, { stagger: 0.2, except: ['T@'] }); n1.show(cue('z1') + 0.1);
    for (const x of before) if (x !== A.g) tl.to(x, { o: 0 }, tZ3 - 0.3, 0.35, E.in);

    // "They differ in one loop: the swapped program can begin with matching pairs."
    const tD = cue('differ');
    z3.pulse('T@', 22.65, { dur: 0.8 });
    const m3 = z3.mark('T@', 22.65, { out: cue('pre') - 0.2 });
    const one = SX.note(tl, root, CX, 262, 'one loop', 22.55, cue('pre') - 0.2);
    z3.pulse('T@', 25.6, { dur: 0.7 });

    // "Step three puts a loop of matching pairs on the start state of every automaton."
    z1.draw('T@', 28.3, 0.6);
    z3.pulse('T@', 30.9, { dur: 0.7 });

    // "For the swapped program, that changes nothing. For the first, it adds the missing loop. Now the two accept the same language."
    z1.pulse('T@', 36.5, { dur: 0.8 });
    const eq = SX.prog(tl, root, CX, topFor(ZY + 20, 96), 96, '=', { align: 'center', colors: { '=': C.good } });
    eq.show(39.4, { rise: 0 });

    // "So the swapped program is equivalent to the first two."
    const tEq = cue('eq');
    for (const x of [z3, z1]) { x.to({ o: 0.35 }, tEq - 0.25, 0.5); x.dimEl('T>L', 0.12, tEq - 0.25, 0.5); x.dimEl('T>R', 0.12, tEq - 0.25, 0.5); }   // the edges the equation lies across go fainter still
    for (const x of [n3, n1]) x.to({ o: 0.35 }, tEq - 0.25, 0.5);
    eq.hide(tEq - 0.25, 0.35);
    const M = 52, cw = charWidth(M);
    const w1 = 41 * cw, x0 = CX - w1 / 2;
    const q1 = SX.prog(tl, root, x0, topFor(500, M), M, 'pop(a)* · push(a)*  ≡  push(a)* · pop(a)*', { colors: { '≡': C.good } });
    const q2 = SX.prog(tl, root, x0 + 20 * cw, topFor(500, M) + lhOf(M) + 18, M, '≡  push(a)* + pop(a)*', { colors: { '≡': C.good } });
    q1.show(tEq - 0.15, { stagger: 0.02 });
    q2.show(42.95, { stagger: 0.02 });
    SX.tick(tl, SX.svg(root), x0 + w1 + 60, topFor(500, M) + lhOf(M) * 1.5 + 9, 52, 43.5);
  });

  // ============================================ thm ===========================================================
  scene('thm', ({ tl, root, cue }) => {
    const rows = new SX.Rows(tl, root, { x: RAIL, y: 190, pitch: 110, size: 56, back: 0.6 });
    const LS = 40;
    const law = (i, text, at) => {
      const p = SX.prog(tl, root, 900, rows.mid(i) - lhOf(LS) / 2, LS, text, { colors: { '≡': C.good } });
      p.show(at, { stagger: 0.02 }); rows.rows[i].add(p.root); return p;
    };
    // "Turn each program into an automaton."
    rows.row('An automaton for each program', cue('t1') - 0.15, { num: '' });
    // "Cancel: add shortcuts where a push meets its pop."
    rows.row('Cancel', cue('t2') - 0.15, { num: '1' });
    law(1, 'push(v) · pop(v) ≡ 1', 7.6);
    // "Filter: keep the traces that pop before they push."
    rows.row('Filter', cue('t3') - 0.15, { num: '2' });
    law(2, 'push(v) · pop(w) ≡ 0', 11.75);
    // "Zip, and put the loop of matching pairs in front."
    rows.row('Zip', cue('t4') - 0.15, { num: '3' });
    law(3, 'pop(v) · push(v) + 1 ≡ 1', 15.25);

    // "Then two programs are equivalent if and only if the two automata accept the same language."
    const tI = cue('iff');
    for (const e of rows.all()) tl.to(e, { o: 0.45 }, tI - 0.2, 0.5);
    const M = 60, cy = 752;
    const th = SX.cline(root, CX, cy - lhOf(M) / 2, [['e₁ ≡ e₂', null], ['   ', null], ['', null], ['   ', null], ['L(A₁) = L(A₂)', null]], SX.MONO(M));
    th.parts[2].appendChild(SX.iff(M));
    const bw = 1160, bh = 140;
    const frame = box(root, CX - bw / 2, cy - bh / 2, { width: bw + 'px', height: bh + 'px', borderRadius: '14px', boxShadow: `inset 0 0 0 2px ${C.line}` });
    fadeIn(tl, frame, tI - 0.15, 0.6, 0);
    SX.note(tl, root, CX, cy - bh / 2 - 50, 'theorem', tI - 0.15, null);
    fadeIn(tl, th.parts[0], 18.2, 0.5, 10);
    fadeIn(tl, th.parts[2], 19.85, 0.5, 0);
    fadeIn(tl, th.parts[4], 21.3, 0.5, 10);

    // "Every step is an elementary construction on finite automata."
    SX.note(tl, root, CX, cy + bh / 2 + 20, 'elementary constructions on finite automata', cue('note') - 0.15, null);
  });
})();

// ==== src/scenes/f.js ====
// Headers, cost, counterexamples, axioms (full_a, full_b, cost, cex, ax) of the StacKAT film, built with SX.
'use strict';
(function () {
  const { W, C, E, scene } = Film;
  const { CX, RAIL } = SX;
  const lh = size => Math.round(size * 1.3);

  // a left-aligned label (small caps) with its own style; text is written lower case (the style uppercases it)
  const lbl = (root, x, y, text, { size = 32, color = C.dim } = {}) => box(root, x, y, Object.assign(SX.LABEL(size), { color, whiteSpace: 'pre' }), text);
  // a label right-aligned so that it ends at x
  const rlbl = (root, x, y, text, { size = 32, color = C.dim } = {}) => box(root, x - 1000, y, Object.assign(SX.LABEL(size), { color, whiteSpace: 'pre', width: '1000px', textAlign: 'right' }), text);
  // a pulse of a whole element (grows a little and back)
  const pulseEl = (tl, e, at, s = 1.06) => { tl.to(e, { s }, at, 0.22, E.out); tl.to(e, { s: 1 }, at + 0.22, 0.4, E.io); };

  // ============================================ full_a ========================================================
  scene('full_a', ({ tl, root, cue }) => {
    // "A state of the automaton becomes a pair: the current header, and the part of the program still to run."
    const tS = cue('state');
    // "Now put the header fields back.": a packet's header, until the pair arrives (the stage was empty here)
    const back = SX.packetHeader(tl, root, SX.CX - 239, 400, [['sw', 'A'], ['dst', '7'], ['port', '1']]);
    back.show(cue('hdr') + 0.1); back.hide(tS + 1.2);
    const BIG = 96, st = SX.prog(tl, root, CX, 220 - lh(BIG) / 2, BIG, '⟨h, e⟩', { align: 'center', colors: { h: C.bind } });
    st.show(5.85, { stagger: 0.05 });
    const hx = st.colX(1.5), ex = st.colX(4.5);
    const lH = rlbl(root, hx + 34, 312, 'the header now');
    const lE = lbl(root, ex - 34, 312, 'the program still to run');
    fadeIn(tl, lH, 7.05, 0.5, 10); st.pulse(st.ids('h'), 7.05);
    fadeIn(tl, lE, 8.3, 0.5, 10); st.pulse(st.ids('e'), 8.3);

    // "There are finitely many headers, and only finitely many parts of the program can be reached"
    const lF = lbl(root, st.x + st.width + 70, 220 - 20, 'finitely many');
    fadeIn(tl, lF, cue('finite') + 0.15, 0.5, 10);

    // "Tests and assignments become silent steps that check or change the header."
    const tT = cue('tests');
    for (const e of [lH, lE, lF]) fadeOut(tl, e, tT - 0.4, 0.3, -8);
    st.to({ y: 150 - 220, s: 56 / BIG }, tT - 0.3, 0.7);

    // the transitions (paper Fig. 8): state, arrow, state; mono 44, pitch 100 from y = 330
    const S = 44, cw = charWidth(S), X0 = 470, AX0 = X0 + 12 * cw + 46, AX1 = AX0 + 240, X1 = AX1 + 46;
    const rows = [], col = box(root, 0, 0, { width: W + 'px', height: '1080px' }), csvg = SX.svg(col);
    const row = (i, left, right, at, { arrowAt = at + 0.35, dash = false, op } = {}) => {
      const y = 330 + i * 100, my = y + lh(S) / 2;
      const L = SX.prog(tl, col, X0, y, S, left, { colors: { h: C.bind } });
      const R = SX.prog(tl, col, X1, y, S, right, { colors: { h: C.bind } });
      L.show(at);
      const a = SX.line(tl, csvg, AX0, my, AX1, my, { at: arrowAt, dur: 0.5, dash: dash ? '13 11' : undefined });
      R.show(arrowAt + 0.35);
      const els = [L.root, R.root, a.path, a.head];
      if (op) {
        const o = SX.prog(tl, col, (AX0 + AX1) / 2, my - 10 - lh(36), 36, op, { align: 'center' });
        o.show(arrowAt + 0.15); els.push(o.root);
      }
      rows.push(els);
      return { L, R, a, y, my };
    };
    const r1 = row(0, '⟨h, f==v⟩', '⟨h, 1⟩', tT - 0.2, { arrowAt: 21.05, dash: true });
    const r2 = row(1, '⟨h, f:=v⟩', '⟨h[f:=v], 1⟩', 20.0, { arrowAt: 21.25, dash: true });
    // "that check": the condition of the test step, dim, after its row
    const cond = box(col, X1 + 6 * cw + 60, r1.my - 22, Object.assign(SX.LABEL(32), { whiteSpace: 'pre' }), 'if ');
    const cm = document.createElement('span');
    Object.assign(cm.style, { fontFamily: 'var(--mono)', fontSize: '36px', textTransform: 'none', letterSpacing: '0', fontVariantLigatures: 'none' });
    cm.textContent = 'h(f) = v'; cond.appendChild(cm);
    fadeIn(tl, cond, 22.45, 0.5, 10); rows[0].push(cond);
    // "or change the header"
    r2.R.pulse({ from: 1, to: 4 }, 23.1);

    // "Pushes and pops stay as letters."
    const tP = cue('pp');
    rows.slice(0, 2).flat().forEach(e => tl.to(e, { o: 0.4 }, tP - 0.25, 0.5));
    row(2, '⟨h, push(v)⟩', '⟨h, 1⟩', tP - 0.2, { arrowAt: tP + 0.05, op: 'push(v)' });
    row(3, '⟨h, pop(v)⟩', '⟨h, 1⟩', 25.2, { arrowAt: 25.4, op: 'pop(v)' });

    // "Then, for every header at the start and every header at the end, take the traces between them, and normalize"
    const tPr = cue('pairs');
    tl.to(st.root, { o: 0.4 }, tPr - 0.25, 0.5);
    rows.slice(2).flat().forEach(e => tl.to(e, { o: 0.4 }, tPr - 0.25, 0.5));
    rows.slice(0, 2).flat().forEach(e => tl.to(e, { o: 0.3 }, tPr - 0.25, 0.5));
    // the column makes room for what comes under it
    tl.to(col, { y: -50 }, tPr - 0.25, 0.8, E.io);
    const lP = SX.clabel(root, CX, 800, 'for every pair of headers: normalize', 32);
    fadeIn(tl, lP, tPr - 0.1, 0.5, 10);
    const tr = SX.cline(root, CX, 716, [['the traces from ', null], ['h₁', C.bind], [' to ', null], ['h₂', C.bind]], SX.SERIF(52));
    fadeIn(tl, tr.root, 31.75, 0.6, 14);

    // "Two programs are equivalent exactly when all of these agree."
    const lT = SX.clabel(root, CX, 858, 'equivalent exactly when all of them agree', 32, C.ink);
    fadeIn(tl, lT, cue('thm') - 0.15, 0.5, 10);
  });

  // ============================================ full_b ========================================================
  scene('full_b', ({ tl, root, cue }) => {
    // "For example, this loop has two branches."
    const S = 56, p = SX.prog(tl, root, CX, 220 - lh(S) / 2, S, '(f==1 · push(1) + f:=2 · push(2))*', { align: 'center' });
    p.show(cue('ex') - 0.15, { stagger: 0.025 });
    const b1 = { from: 1, to: 3 }, b2 = { from: 5, to: 7 };
    // "The first needs the field F to be one, and pushes a one."
    p.dim(b2, 0.35, 3.5); p.pulse(1, 5.15); p.pulse(3, 6.55);
    // "The second sets F to two, and pushes a two."
    p.light(b2, 7.9); p.dim(b1, 0.35, 7.9); p.pulse(5, 8.6); p.pulse(7, 10.25);
    p.light(b1, 11.5);

    // a row: "f = n  →  f = n" (serif, the f's cyan) and the traces push(n)* (mono)
    const SR = 52, RX = 1010, MX = 1090;
    const mkRow = (n, y, t1, t2, t3) => {
      const l = SX.lline(root, RX - 1000, y, [['f', C.bind], [` = ${n}`, null], ['   →   ', null], ['f', C.bind], [` = ${n}`, null]],
        Object.assign(SX.SERIF(SR), { width: '1000px', textAlign: 'right' }));
      [0, 1].forEach(k => fadeIn(tl, l.parts[k], t1, 0.5, 12));
      [2, 3, 4].forEach(k => fadeIn(tl, l.parts[k], t2, 0.5, 12));
      const tr = SX.prog(tl, root, MX, y + Math.round(SR * 1.22) / 2 - lh(S) / 2, S, `push(${n})*`);
      tr.show(t3);
      return [l.root, tr.root];
    };
    // "Start with F equal to one, and end with F equal to one: the loop can only have pushed ones."
    const row1 = mkRow(1, 450, cue('c1') - 0.15, 13.9, 17.1);
    // "From two to two, only twos."
    const tC2 = cue('c2');
    row1.forEach(e => tl.to(e, { o: 0.45 }, tC2 - 0.25, 0.5));
    const row2 = mkRow(2, 590, tC2 - 0.15, 19.1, 19.8);
    // "Each pair of headers is compared on its own."
    const tE = cue('each');
    row1.forEach(e => tl.to(e, { o: 1 }, tE - 0.2, 0.5));
    const l = SX.clabel(root, CX, 740, 'each pair is compared on its own', 32);
    fadeIn(tl, l, tE - 0.15, 0.5, 10);
  });

  // ============================================ cost ==========================================================
  scene('cost', ({ tl, root, cue }) => {
    const LX = 520, RX = 1400;
    // "Without headers, the problem is complete for polynomial space, the same as for regular expressions."
    const tPs = cue('ps');
    const l1 = SX.clabel(root, LX, 300, 'push and pop only', 32);
    fadeIn(tl, l1, tPs - 0.15, 0.5, 10);
    const s1 = SX.cserif(root, LX, 352, 'PSPACE-complete', 72);
    fadeIn(tl, s1, 3.75, 0.7, 16);
    const d1 = SX.clabel(root, LX, 470, 'as for regular expressions', 32);
    fadeIn(tl, d1, 6.75, 0.5, 10);
    // "With headers, it is complete for exponential space, when programs may use any number of fields."
    const tX = cue('exp');
    SX.dim(tl, [l1, s1, d1], 0.45, tX - 0.25);
    const l2 = SX.clabel(root, RX, 300, 'with any number of header fields', 32);
    fadeIn(tl, l2, tX - 0.15, 0.5, 10);
    const s2 = SX.cserif(root, RX, 352, 'EXPSPACE-complete', 72);
    fadeIn(tl, s2, 9.9, 0.7, 16);
    // "The implementation ... goes through the pairs of headers one by one."
    const tI = cue('impl');
    SX.dim(tl, [l2, s2], 0.45, tI - 0.25);
    const i1 = SX.clabel(root, CX, 680, 'the implementation enumerates pairs of headers', 32, C.ink);
    fadeIn(tl, i1, tI - 0.15, 0.5, 10);
    // "A symbolic procedure is future work."
    const i2 = SX.clabel(root, CX, 744, 'future work: a symbolic procedure', 32);
    fadeIn(tl, i2, cue('sym') - 0.15, 0.5, 10);
  });

  // ============================================ cex ===========================================================
  scene('cex', ({ tl, root, cue }) => {
    const svg = SX.svg(root);
    // "When two programs are not equivalent, the procedure says why."
    const S = 44, top = SX.prog(tl, root, CX, 130, S, 'push(a)* · pop(a)*  ≢  (push(a) · push(a))* · (pop(a) · pop(a))*', { align: 'center', colors: { '≢': C.bad } });
    const ne = top.ids('≢')[0];
    top.show(cue('cex') - 0.15, { sel: { from: 0, to: ne - 1 }, stagger: 0.02 });
    top.show(1.0, { sel: { from: ne + 1 }, stagger: 0.015 });
    top.show(1.6, { sel: ne, rise: 0 });
    const r1 = top.rect({ from: 0, to: ne - 1 }), r2 = top.rect({ from: ne + 1 });

    // "The two automata differ on some word."
    const WS = 60, word = SX.prog(tl, root, CX, 330 - lh(WS) / 2, WS, '(pop(a), done)', { align: 'center' });
    word.show(6.75, { rise: 16 });
    const wl = SX.clabel(root, CX, 384, 'a word one automaton accepts', 32);
    fadeIn(tl, wl, 7.0, 0.5, 10);

    // "Unzip it. Its pops spell an input stack, and its pushes spell an output stack."
    const tU = cue('unzip');
    const ar = SX.line(tl, svg, CX, 440, CX, 500, { at: tU - 0.2, dur: 0.4 });
    const po = SX.prog(tl, root, CX, 510, WS, 'pop(a)', { align: 'center' });
    po.show(tU + 0.05);
    const BOT = 800, INX = 640, OUTX = 1280;
    const sIn = new SX.Stack(tl, root, INX, BOT, { items: ['a'], label: 'pops: the input stack' });
    sIn.show(9.3);
    const sOut = new SX.Stack(tl, root, OUTX, BOT, { items: [], ghost: true, label: 'pushes: the output stack' });
    sOut.show(11.85);

    // "With the two headers, that is an input packet and an output packet"
    const tP = cue('pair');
    word.hide(tP - 0.3); po.hide(tP - 0.3); ar.hide(tP - 0.3);
    fadeOut(tl, wl, tP - 0.3, 0.3, -8);
    fadeOut(tl, sIn.labelEl, tP - 0.3, 0.3, -8); fadeOut(tl, sOut.labelEl, tP - 0.3, 0.3, -8);
    // the packets: [h₁][in stack]  →  [h₂][out stack], bottoms at y = 640
    const NB = 600, CWD = 96, CH = 84, G = 18, ARW = 200;
    const pw = CWD + G + 96, x0 = Math.round(CX - (2 * pw + ARW + 80) / 2);
    const inCx = x0 + CWD + G + 48, h2x = x0 + pw + 40 + ARW + 40, outCx = h2x + CWD + G + 48;
    sIn.move(inCx - INX, NB - BOT, tP - 0.2, 0.8); sOut.move(outCx - OUTX, NB - BOT, tP - 0.2, 0.8);
    const hcell = (x, name, at) => {
      // the subscript as a lowered smaller digit: Fira Code's ₁ is too small to read in a cell
      const c = SX.cell(root, x, NB - CH, CWD, CH, 'h', { stroke: C.bind, color: C.bind, font: SX.MONO(44) });
      const sub = document.createElement('span');
      Object.assign(sub.style, { fontSize: '28px', position: 'relative', top: '12px' });
      sub.textContent = name; c._t.appendChild(sub);
      fadeIn(tl, c, at, 0.5, 12); return c;
    };
    const h1 = hcell(x0, '1', 14.6), h2 = hcell(h2x, '2', 15.0);
    const pl = SX.clabel(root, CX, NB + 34, 'an input packet, and an output packet', 32);
    fadeIn(tl, pl, 16.0, 0.5, 10);
    SX.line(tl, svg, x0 + pw + 40, NB - CH / 2, x0 + pw + 40 + ARW, NB - CH / 2, { at: 16.95, dur: 0.5 });

    // "that one program relates, and the other does not."
    const ty = 236;
    SX.tick(tl, svg, r1.cx - 150, ty, 44, 18.95);
    const rl = lbl(root, r1.cx - 105, ty - 20, 'relates them');
    fadeIn(tl, rl, 19.05, 0.5, 10);
    SX.cross(tl, svg, r2.cx - 110, ty, 36, 20.45);
    const dl = lbl(root, r2.cx - 70, ty - 20, 'does not');
    fadeIn(tl, dl, 20.55, 0.5, 10);

    // "one such pair is: a stack holding a single A going in, and the empty stack coming out."
    pulseEl(tl, sIn.g, 27.4); pulseEl(tl, sOut.g, 29.75);
  });

  // ============================================ ax ============================================================
  scene('ax', ({ tl, root, cue }) => {
    const svg = SX.svg(root);
    // "The laws can be used as axioms, to prove equivalences by algebra.": the three laws again, until Kleene
    // algebra arrives (the stage was empty through these two sentences)
    SX.note(tl, root, SX.CX, 250, 'the three laws', cue('alg') - 0.15, cue('ka') - 0.5, { align: 'center' });
    ['push(v) · pop(v) ≡ 1', 'push(v) · pop(w) ≡ 0', 'pop(v) · push(v) + 1 ≡ 1'].forEach((t, i) => {
      const p = SX.prog(tl, root, SX.CX, 340 + i * 110, 52, t, { align: 'center', colors: { '≡': C.good } });
      p.show(cue('alg') - 0.1 + i * 0.3, { stagger: 0.015 }); p.hide(cue('ka') - 0.5);
    });
    // "Start from Kleene algebra, the standard axioms for regular expressions."
    const ka = box(root, RAIL - 4, 180, Object.assign(SX.SERIF(72), { whiteSpace: 'pre' }), 'Kleene algebra');
    fadeIn(tl, ka, 9.15, 0.7, 16);
    const kl = lbl(root, RAIL, 282, 'the axioms of regular expressions');
    fadeIn(tl, kl, 10.7, 0.5, 10);

    // rows: "+" on the rail, the law at x = 240
    const S = 52, FX = 240, plus = (y, at) => { const p = SX.prog(tl, root, RAIL, y, S, '+'); p.show(at); return p.root; };
    // "Add the first law,"
    const tA1 = cue('a1');
    const p1 = plus(400, tA1 - 0.15);
    const a1 = SX.prog(tl, root, FX, 400, S, 'push(v) · pop(v) = 1'); a1.show(tA1 - 0.1, { stagger: 0.02 });
    // "and the second."
    const tA2 = cue('a2');
    const p2 = plus(500, tA2 - 0.25);
    const a2 = SX.prog(tl, root, FX, 500, S, 'push(v) · pop(w) = 0'); a2.show(tA2 - 0.2, { stagger: 0.02 });
    const vw = SX.prog(tl, root, FX + a2.width + 44, 500 + (lh(S) - lh(40)) / 2, 40, 'v ≠ w');
    for (const q of vw.parts) for (const s of q.subs) { s.style.color = C.dim; s._col = C.dim; }
    vw.show(tA2 + 0.15);

    // "These are complete for the first two steps.": a bracket, a tick, a label (on two lines)
    const tC1 = cue('comp1'), BX = 1110, TX = 1200, LX = 1250;
    const br = SX.dpath(tl, svg, `M ${BX} 404 L ${BX + 18} 404 L ${BX + 18} 564 L ${BX} 564`, { width: 3 });
    tl.to(br, { draw: 1 }, tC1 - 0.2, 0.5, E.io);
    const t1 = SX.tick(tl, svg, TX, 484, 44, tC1 + 0.1);
    const c1 = box(root, LX, 484 - 40, Object.assign(SX.LABEL(32), { whiteSpace: 'pre' }), 'complete for\nsteps 1 and 2');
    fadeIn(tl, c1, tC1 + 0.2, 0.5, 10);

    // "For the third law, what is proved uses an extra family of rules, more complicated than the law."
    const tA3 = cue('a3');
    const first = [p1, a1.root, p2, a2.root, vw.root, br, ...t1.els, c1];
    SX.dim(tl, first, 0.45, tA3 - 0.2);
    const p3 = plus(640, 21.85);
    const a3 = lbl(root, FX, 640 + lh(S) / 2 - 20, 'a family of rules for the third law', { color: C.ink });
    fadeIn(tl, a3, 21.9, 0.5, 10);

    // "With them, every equivalence between programs that push and pop has a proof from the axioms."
    const tC2 = cue('comp2'), my3 = 640 + lh(S) / 2;
    const t2 = SX.tick(tl, svg, TX, my3, 44, tC2 - 0.1);
    const c2 = box(root, LX, my3 - 40, Object.assign(SX.LABEL(32), { whiteSpace: 'pre' }), 'complete for\npush and pop');
    fadeIn(tl, c2, tC2, 0.5, 10);

    // "Whether the third law by itself would be enough is an open question. The authors conjecture that it is not."
    const tO = cue('open');
    SX.dim(tl, [p3, a3, ...t2.els, c2], 0.45, tO - 0.2);
    tl.to(ka, { o: 0.45 }, tO - 0.2, 0.5); tl.to(kl, { o: 0.45 }, tO - 0.2, 0.5);
    const OS = 48, law = SX.prog(tl, root, FX, 770 - lh(OS) / 2, OS, 'pop(v) · push(v) ≤ 1');
    law.show(32.75, { stagger: 0.02 });
    const en = lbl(root, FX + law.width + 50, 770 - 20, 'enough by itself?');
    fadeIn(tl, en, 34.3, 0.5, 10);
    const op = SX.lline(root, FX, 836, [['open', null], [' · conjectured not', null]], SX.LABEL(32));
    fadeIn(tl, op.parts[0], 35.3, 0.5, 10);
    fadeIn(tl, op.parts[1], 37.4, 0.5, 10);
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
window.CAPTIONS = [[0.8, 3.0, "Here are two small programs."], [3.04, 5.32, "Each one acts on a stack."], [5.36, 8.84, "The first pushes the value A some number of times,"], [8.88, 11.4, "and then pops it some number of times."], [11.44, 14.68, "The star is the star of regular expressions."], [14.72, 17.08, "It means some number of times:"], [17.12, 19.84, "zero, one, two, or more."], [19.88, 22.36, "It is not a loop that keeps running."], [22.4, 23.96, "Like a regular expression,"], [24.0, 27.24, "the program generates sequences of pushes and pops,"], [27.28, 28.6, "called traces."], [28.64, 31.8, "Each trace is one way the program can run."], [31.84, 34.44, "The second program does one or the other:"], [34.48, 37.0, "only pushes, or only pops."], [37.04, 38.6, "The two are equivalent:"], [38.64, 42.2, "on every stack, they can do exactly the same things."], [42.24, 44.28, "How could a machine check that?"], [44.32, 46.52, "A stack can be arbitrarily deep,"], [46.56, 49.48, "so there are infinitely many stacks to try."], [49.52, 52.04, "This video is about a language for networks,"], [52.08, 54.92, "called StacKAT, in which that question always"], [54.96, 56.2, "has an answer."], [56.24, 58.76, "By the end, we will have checked these two programs"], [58.8, 61.64, "by hand, and we will know an algorithm that checks"], [61.68, 65.06, "any such equivalence automatically."], [65.16, 66.96, "Here is what is coming."], [67.0, 69.97, "First, how a network becomes a program,"], [70.01, 73.52, "and a question about it becomes a question of equivalence."], [73.56, 76.56, "Then why real packets need a stack."], [76.6, 80.28, "Then the language, and three laws about push and"], [80.32, 80.88, "pop."], [80.92, 82.32, "Then the main part:"], [82.36, 84.32, "a procedure in three steps,"], [84.36, 87.44, "one for each law, that decides equivalence using"], [87.48, 89.36, "only finite automata."], [89.4, 91.04, "And at the end:"], [91.08, 93.2, "headers, cost, counterexamples,"], [93.24, 95.66, "and axioms."], [96.08, 97.36, "StacKAT:"], [97.4, 101.22, "infinite state network verification."], [103.22, 105.5, "A network is made of switches."], [105.54, 107.58, "A packet arrives with a header:"], [107.62, 111.26, "a few fields, such as a destination and a port."], [111.3, 113.26, "A switch looks at some fields,"], [113.3, 116.78, "changes some, and sends the packet on to a neighbor."], [116.82, 119.5, "NetKAT is a language that reads all of this as"], [119.54, 120.7, "a program."], [120.74, 122.62, "A field is a variable."], [122.66, 124.3, "A match is a test:"], [124.34, 126.86, "it lets the packet through if a field has a given"], [126.9, 129.5, "value, and drops it otherwise."], [129.54, 133.02, "An action is an assignment of a constant to a field."], [133.06, 135.66, "Even the packet's location is a field."], [135.7, 138.3, "Moving it to switch B is an assignment:"], [138.34, 140.9, "switch becomes B."], [140.94, 143.78, "Programs are combined in three ways."], [143.82, 147.06, "A dot runs one program and then another."], [147.1, 148.9, "A plus is a choice:"], [148.94, 150.74, "the packet goes both ways,"], [150.78, 153.7, "as when a switch forwards it to two neighbors."], [153.74, 157.33, "A star repeats a program any number of times."], [157.37, 159.83, "And there are two constant programs."], [159.87, 163.9, "The program written one passes every packet unchanged."], [163.94, 167.3, "The program written zero drops every packet."], [167.34, 169.94, "The whole network is then one program:"], [169.98, 172.26, "test which switch the packet is on,"], [172.3, 173.94, "run that switch's program,"], [173.98, 176.14, "and repeat."], [176.18, 178.22, "What does a program mean?"], [178.26, 181.02, "It relates each input packet to the packets that"], [181.06, 182.14, "can come out:"], [182.18, 184.7, "none, one, or several."], [184.74, 187.14, "Two programs are equivalent if they relate the"], [187.18, 189.58, "same inputs to the same outputs."], [189.62, 192.65, "Equivalence is what verification needs."], [192.69, 195.42, "To ask whether any packet can get from switch A"], [195.46, 196.78, "to switch B:"], [196.82, 198.94, "start at A, run the network,"], [198.98, 200.54, "and test for B."], [200.58, 202.94, "If that program is equivalent to zero,"], [202.98, 204.94, "no packet gets through."], [204.98, 208.06, "For NetKAT, a machine can always answer,"], [208.1, 210.54, "because a packet has finitely many fields,"], [210.58, 212.7, "with finitely many values."], [212.74, 215.02, "There are only finitely many packets,"], [215.06, 219.0, "so a program is a finite-state system."], [220.82, 223.34, "Real packets are not that simple."], [223.38, 226.62, "On the wire, a packet is a sequence of bytes."], [226.66, 228.46, "A switch must parse it:"], [228.5, 231.74, "take bytes off the front, and put them into fields."], [231.78, 234.74, "In source routing, the packet carries its whole"], [234.78, 237.74, "route, and each switch takes off the next hop."], [237.78, 240.54, "Telemetry adds a record at every hop."], [240.58, 243.18, "A tunnel wraps the packet in new headers,"], [243.22, 244.86, "and unwraps it later."], [244.9, 247.58, "Every one of these adds or removes at the front"], [247.62, 248.78, "of the packet."], [248.82, 251.22, "That is a stack."], [251.26, 253.86, "And a stack has no fixed depth."], [253.9, 256.42, "A route can be arbitrarily long."], [256.46, 258.79, "So there are infinitely many packets,"], [258.83, 261.94, "and the argument that made NetKAT decidable is"], [261.98, 262.47, "gone."], [262.51, 264.1, "It looks worse than that."], [264.14, 267.5, "A machine with a stack and an input can recognize"], [267.54, 270.66, "context-free languages, and whether two context-free"], [270.7, 273.62, "languages are equal is undecidable."], [273.66, 276.4, "So is there any hope?"], [278.22, 281.3, "In StacKAT, a packet has two parts:"], [281.34, 284.34, "a header, as before, and a stack."], [284.38, 286.9, "The language adds two operations."], [286.94, 290.1, "Push puts a value on top of the stack."], [290.14, 292.34, "Pop takes a value off the top,"], [292.38, 294.82, "but only if it is the value named."], [294.86, 297.58, "Pop three, on a stack with three on top,"], [297.62, 298.74, "removes it."], [298.78, 300.9, "Pop five, on the same stack,"], [300.94, 302.5, "drops the packet."], [302.54, 304.9, "So does a pop on an empty stack."], [304.94, 308.48, "A pop is a test and an action in one."], [308.58, 310.54, "These two are enough."], [310.58, 312.7, "Source routing is one line:"], [312.74, 315.9, "pop the top of the stack into the switch field."], [315.94, 318.14, "That is shorthand for a choice:"], [318.18, 320.38, "pop one and go to switch one,"], [320.42, 323.05, "or pop two and go to switch two,"], [323.09, 324.22, "and so on."], [324.26, 327.77, "That works because there are finitely many values."], [327.81, 331.18, "Parsing a header pops into one field after another."], [331.22, 334.28, "And telemetry is a push."], [334.4, 337.32, "A program still relates input packets to output"], [337.36, 340.6, "packets, and equivalence is as before."], [340.64, 342.76, "But push and pop interact,"], [342.8, 345.0, "and three laws say how."], [345.04, 345.72, "One."], [345.76, 348.6, "Push a value and then pop the same value:"], [348.64, 350.04, "nothing has happened."], [350.08, 352.76, "That is equivalent to the program one."], [352.8, 353.56, "Two."], [353.6, 356.28, "Push a value and then pop a different value:"], [356.32, 357.8, "the pop fails."], [357.84, 359.96, "That is equivalent to zero."], [360.0, 361.64, "The third is subtle."], [361.68, 364.12, "Pop a value and then push it back."], [364.16, 366.68, "That is not equivalent to the program one,"], [366.72, 369.16, "because it drops every packet that does not have"], [369.2, 370.84, "that value on top."], [370.88, 372.79, "But when it does not drop the packet,"], [372.83, 374.36, "it changes nothing."], [374.4, 378.2, "So a choice between the program one and this pop-then-push"], [378.24, 381.22, "is just the program one."], [381.44, 384.57, "Now back to the two programs from the start."], [384.61, 386.68, "Push A any number of times,"], [386.72, 389.32, "then pop A any number of times."], [389.36, 393.16, "By the first law, each push cancels against a pop."], [393.2, 394.52, "If there were more pushes,"], [394.56, 396.12, "some pushes are left."], [396.16, 399.04, "If there were more pops, some pops are left."], [399.08, 401.4, "That is what the second program does."], [401.44, 403.44, "So they are equivalent."], [403.48, 405.4, "Here is a third program:"], [405.44, 407.8, "push A an even number of times,"], [407.84, 410.28, "then pop it an even number of times."], [410.32, 412.6, "It is not equivalent to the first."], [412.64, 415.24, "The first can take a stack that holds a single"], [415.28, 416.76, "A, and empty it."], [416.8, 418.36, "The third cannot."], [418.4, 421.0, "We want a machine to tell such cases apart,"], [421.04, 423.7, "for any two programs."], [423.82, 425.14, "And it can."], [425.18, 428.58, "Equivalence of StacKAT programs is decidable."], [428.62, 430.93, "This is the surprising part."], [430.97, 433.94, "The stack is unbounded, and programs may use it"], [433.98, 437.06, "in any way they like, yet the question can always"], [437.1, 438.34, "be answered."], [438.38, 440.9, "What makes it possible is that a program has no"], [440.94, 443.54, "input other than the packet itself."], [443.58, 446.18, "The stack is not working memory for reading some"], [446.22, 447.38, "other input."], [447.42, 451.84, "It is the input, and it is the output."], [453.66, 457.06, "We start with programs that only push and pop."], [457.1, 458.98, "Headers come back later."], [459.02, 461.62, "Such a program is a regular expression,"], [461.66, 464.1, "whose letters are pushes and pops."], [464.14, 466.58, "Each word it matches is a trace:"], [466.62, 469.46, "one sequence of pushes and pops that the program"], [469.5, 470.74, "can perform."], [470.78, 473.46, "A regular expression can be turned into a finite"], [473.5, 476.82, "automaton that accepts exactly its traces,"], [476.86, 480.26, "and a machine can compare two finite automata."], [480.3, 482.77, "But the traces are not the meaning."], [482.81, 485.01, "Take a choice between the program one,"], [485.05, 488.18, "and a pop followed by a push of the same value."], [488.22, 490.02, "It has two traces."], [490.06, 492.85, "The program one alone has a single trace,"], [492.89, 494.18, "the empty one."], [494.22, 497.3, "Yet by the third law, they mean the same."], [497.34, 500.34, "So before comparing, we bring each automaton to"], [500.38, 502.98, "a normal form, in three steps,"], [503.02, 505.44, "one for each law."], [505.56, 507.76, "Step one is to cancel."], [507.8, 510.0, "It uses the first law."], [510.04, 512.48, "Wherever the automaton can do a push and then a"], [512.52, 515.64, "pop of the same value, possibly with silent steps"], [515.68, 518.72, "in between, add a shortcut between the same two"], [518.76, 520.64, "states that does nothing."], [520.68, 523.28, "Repeat until nothing new appears."], [523.32, 526.05, "In our automaton, the loop pushes A,"], [526.09, 528.32, "and the next edge pops A."], [528.36, 530.96, "So we add a silent edge beside them."], [531.0, 534.08, "The automaton now accepts every trace it had,"], [534.12, 537.08, "and also every trace in which matching pushes and"], [537.12, 539.9, "pops have been cancelled."], [540.02, 542.3, "Step two is to filter."], [542.34, 545.1, "Take a trace in which a push is followed directly"], [545.14, 546.3, "by a pop."], [546.34, 549.5, "If the two values differ, the trace drops every"], [549.54, 551.26, "packet, by the second law."], [551.3, 553.1, "It contributes nothing."], [553.14, 556.06, "If they are the same, step one has already added"], [556.1, 557.5, "the trace without them."], [557.54, 559.02, "It is redundant."], [559.06, 562.14, "So we keep only the traces with no such pair:"], [562.18, 564.82, "all pops come before all pushes."], [564.86, 567.98, "On automata, that is an intersection with the automaton"], [568.02, 569.82, "for pops, then pushes:"], [569.86, 571.58, "a standard construction."], [571.62, 574.62, "For our program, the result has two branches:"], [574.66, 577.02, "pops only, or pushes only."], [577.06, 580.14, "And that is exactly the automaton of the second"], [580.18, 580.78, "program."], [580.82, 583.22, "The two programs from the start of the video are"], [583.26, 586.06, "equivalent, and this time a procedure has checked"], [586.1, 587.72, "it."], [587.92, 589.56, "Notice what we did."], [589.6, 591.75, "We changed a finite automaton,"], [591.79, 593.64, "and compared it with another."], [593.68, 596.6, "When two automata agree after these steps,"], [596.64, 598.6, "the programs are equivalent."], [598.64, 601.56, "But when they disagree, we cannot conclude anything"], [601.6, 602.44, "yet."], [602.48, 605.86, "Two steps are not always enough."], [606.26, 609.82, "Here is the first program with its halves swapped:"], [609.86, 612.14, "pop A any number of times,"], [612.18, 615.1, "then push A any number of times."], [615.14, 617.42, "It is equivalent to the other two."], [617.46, 620.38, "But steps one and two leave its automaton as it"], [620.42, 621.34, "is."], [621.38, 624.25, "It still accepts a pop followed by a push,"], [624.29, 626.22, "which the others do not."], [626.26, 628.46, "This is the third law at work:"], [628.5, 631.58, "a pop and then a push of the same value is hidden"], [631.62, 633.58, "inside the program one."], [633.62, 636.22, "We cannot simply delete such a pair."], [636.26, 639.62, "On its own, a pop and then a push still drops some"], [639.66, 640.7, "packets."], [640.74, 643.58, "Deleting is only right when the trace without the"], [643.62, 645.5, "pair is also there."], [645.54, 647.9, "So again we add instead."], [647.94, 651.1, "In every trace, between the pops and the pushes,"], [651.14, 654.14, "insert a pop and a push of the same value."], [654.18, 658.44, "Do it for every value, and again and again."], [658.66, 661.22, "Why is this the right thing to add?"], [661.26, 663.9, "Think about what a trace of pops and then pushes"], [663.94, 664.86, "says."], [664.9, 665.5, "Take:"], [665.54, 667.66, "pop one, push four."], [667.7, 668.62, "It says:"], [668.66, 671.58, "a stack with a one on top becomes the same stack"], [671.62, 673.18, "with a four on top."], [673.22, 675.82, "Whatever lies below is untouched."], [675.86, 679.82, "So this single trace stands for many pairs of stacks."], [679.86, 682.98, "Now insert a pop and a push of a two."], [683.02, 685.21, "The new trace says the same thing,"], [685.25, 688.1, "but only for stacks that have a two below."], [688.14, 690.46, "That is a special case of what we had,"], [690.5, 693.18, "so adding it changes nothing in meaning."], [693.22, 695.02, "With every insertion added,"], [695.06, 698.06, "there is one trace for each whole input stack,"], [698.1, 700.62, "together with its whole output stack."], [700.66, 704.14, "And then two programs have the same traces exactly"], [704.18, 707.16, "when they relate the same stacks."], [707.48, 708.92, "There is a problem."], [708.96, 712.16, "The inserted pairs nest, like brackets:"], [712.2, 716.2, "pop A, pop B, push B, push A."], [716.24, 719.44, "No finite automaton accepts such a language."], [719.48, 722.72, "The way out is to change how a trace is read."], [722.76, 725.32, "Start in the middle, where the pops end and the"], [725.36, 727.84, "pushes begin, and read outwards,"], [727.88, 730.24, "one pop and one push at a time,"], [730.28, 731.44, "as a pair."], [731.48, 733.4, "We call this zipping."], [733.44, 736.4, "Each pair is one letter of a new alphabet."], [736.44, 739.28, "Here is a trace, and here it is zipped."], [739.32, 742.88, "When one side runs out, a placeholder fills in."], [742.92, 744.08, "Nothing is lost:"], [744.12, 746.8, "a zipped trace can be unzipped again."], [746.84, 749.76, "Now the inserted pairs are no longer in the middle."], [749.8, 752.51, "They are at the front, one after another."], [752.55, 755.9, "And that is just a loop at the start."], [756.02, 758.7, "An automaton can be zipped too."], [758.74, 761.1, "The zipped automaton starts in the middle of a"], [761.14, 762.78, "run of the original."], [762.82, 765.46, "Each of its steps goes one step backwards through"], [765.5, 769.26, "the pops, and one step forwards through the pushes."], [769.3, 772.78, "Here is the zipped automaton of the swapped program."], [772.82, 775.1, "And here is the one for the first program,"], [775.14, 777.5, "after steps one and two."], [777.54, 779.26, "They differ in one loop:"], [779.3, 782.86, "the swapped program can begin with matching pairs."], [782.9, 785.66, "Step three puts a loop of matching pairs on the"], [785.7, 788.06, "start state of every automaton."], [788.1, 790.94, "For the swapped program, that changes nothing."], [790.98, 793.74, "For the first, it adds the missing loop."], [793.78, 796.54, "Now the two accept the same language."], [796.58, 799.54, "So the swapped program is equivalent to the first"], [799.58, 801.0, "two."], [801.22, 803.26, "That is the whole procedure."], [803.3, 806.14, "Turn each program into an automaton."], [806.18, 807.18, "Cancel:"], [807.22, 810.38, "add shortcuts where a push meets its pop."], [810.42, 811.42, "Filter:"], [811.46, 814.78, "keep the traces that pop before they push."], [814.82, 818.46, "Zip, and put the loop of matching pairs in front."], [818.5, 821.9, "Then two programs are equivalent if and only if"], [821.94, 824.86, "the two automata accept the same language."], [824.9, 827.82, "Every step is an elementary construction on finite"], [827.86, 829.02, "automata."], [829.06, 833.4, "The infinitely many stacks never had to be listed."], [835.22, 837.58, "Now put the header fields back."], [837.62, 840.38, "A state of the automaton becomes a pair:"], [840.42, 842.86, "the current header, and the part of the program"], [842.9, 844.3, "still to run."], [844.34, 846.3, "There are finitely many headers,"], [846.34, 848.86, "and only finitely many parts of the program can"], [848.9, 852.78, "be reached, so it is still a finite automaton."], [852.82, 855.9, "Tests and assignments become silent steps that"], [855.94, 858.06, "check or change the header."], [858.1, 860.94, "Pushes and pops stay as letters."], [860.98, 863.86, "Then, for every header at the start and every header"], [863.9, 866.57, "at the end, take the traces between them,"], [866.61, 868.66, "and normalize as before."], [868.7, 871.5, "Two programs are equivalent exactly when all of"], [871.54, 873.62, "these agree."], [873.66, 876.9, "For example, this loop has two branches."], [876.94, 879.81, "The first needs the field F to be one,"], [879.85, 881.3, "and pushes a one."], [881.34, 885.06, "The second sets F to two, and pushes a two."], [885.1, 887.14, "Start with F equal to one,"], [887.18, 889.38, "and end with F equal to one:"], [889.42, 891.94, "the loop can only have pushed ones."], [891.98, 894.66, "From two to two, only twos."], [894.7, 898.56, "Each pair of headers is compared on its own."], [898.68, 900.6, "What does this cost?"], [900.64, 903.52, "Without headers, the problem is complete for polynomial"], [903.56, 906.96, "space, the same as for regular expressions."], [907.0, 910.24, "With headers, it is complete for exponential space,"], [910.28, 913.36, "when programs may use any number of fields."], [913.4, 916.32, "The implementation, which runs in a web browser,"], [916.36, 919.28, "goes through the pairs of headers one by one."], [919.32, 921.12, "That is its bottleneck."], [921.16, 924.78, "A symbolic procedure is future work."], [924.9, 927.26, "When two programs are not equivalent,"], [927.3, 929.34, "the procedure says why."], [929.38, 932.3, "The two automata differ on some word."], [932.34, 933.74, "Unzip it."], [933.78, 935.95, "Its pops spell an input stack,"], [935.99, 938.7, "and its pushes spell an output stack."], [938.74, 941.66, "With the two headers, that is an input packet and"], [941.7, 944.59, "an output packet that one program relates,"], [944.63, 946.35, "and the other does not."], [946.39, 948.82, "For the program with even numbers of pushes and"], [948.86, 951.26, "pops, one such pair is:"], [951.3, 953.98, "a stack holding a single A going in,"], [954.02, 957.24, "and the empty stack coming out."], [959.06, 960.7, "One more result."], [960.74, 963.05, "The laws can be used as axioms,"], [963.09, 965.9, "to prove equivalences by algebra."], [965.94, 967.82, "Start from Kleene algebra,"], [967.86, 971.1, "the standard axioms for regular expressions."], [971.14, 973.9, "Add the first law, and the second."], [973.94, 976.7, "These are complete for the first two steps."], [976.74, 979.74, "For the third law, what is proved uses an extra"], [979.78, 983.26, "family of rules, more complicated than the law."], [983.3, 986.26, "With them, every equivalence between programs that"], [986.3, 989.58, "push and pop has a proof from the axioms."], [989.62, 992.3, "Whether the third law by itself would be enough"], [992.34, 994.14, "is an open question."], [994.18, 997.64, "The authors conjecture that it is not."], [999.46, 1002.54, "A network is a program, and questions about it"], [1002.58, 1004.78, "are questions of equivalence."], [1004.82, 1006.7, "Real packets need a stack,"], [1006.74, 1009.42, "which makes the state space infinite."], [1009.46, 1011.9, "StacKAT adds push and pop,"], [1011.94, 1014.78, "and three laws about them become three steps on"], [1014.82, 1016.54, "a finite automaton:"], [1016.58, 1019.1, "cancel, filter, zip."], [1019.14, 1022.46, "After those steps, equivalent programs have automata"], [1022.5, 1024.41, "that accept the same language,"], [1024.45, 1027.1, "and so equivalence is decidable."], [1027.14, 1029.66, "That is a foundation for checking networks that"], [1029.7, 1033.72, "parse, tunnel, and route by a stack."], [1033.94, 1035.26, "StacKAT:"], [1035.3, 1038.3, "infinite state network verification."], [1038.34, 1040.94, "The paper and its appendix have the proofs,"], [1040.98, 1042.7, "the constructions in full,"], [1042.74, 1047.08, "the complexity bounds, and the axiomatization."]];
