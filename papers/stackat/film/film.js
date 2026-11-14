// StacKAT: a short video: the film's scripts in one file, made by tools/web.py.

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
// A short film (about two minutes) on "StacKAT: Infinite State Network Verification" (PLDI 2025). One story: networks
// as programs, why a stack breaks the finite-state argument, the two new operations, and the decision procedure.
// {name} marks a cue. "Stack Cat" and "Net Cat" are written as they are spoken; src/caption-fixes.json has their spelling.
window.NARRATION = [
  { id: 's_hook', chapter: '', pre: 0.5, post: 0.4, text:
    `{net}A network forwards packets by rules: match some header fields, rewrite some, and send the packet on. {prog}Net Cat reads those rules as a program. A field is a variable, a rule is an if statement, and a path through the network is a loop. ` +
    `{verify}A question about the network, such as whether one host can reach another, then becomes a question about programs: {equiv}are these two programs equivalent? {dec}For Net Cat this can be decided, because a packet has finitely many fields, with finitely many values.` },
  { id: 's_limit', chapter: '', pre: 0.4, post: 0.4, text:
    `{but}But real packets also carry a stack. {route}In source routing, a packet carries its whole path, and each router pops the next hop. {tele}Telemetry pushes a record at every hop. {parse}And parsing a packet pops its bytes one by one. ` +
    `{unb}A stack has no bound, {inf}so there are infinitely many packets, and the finite-state argument is gone.` },
  { id: 's_lang', chapter: '', pre: 0.4, post: 0.4, text:
    `{lang}Stack Cat adds two operations to Net Cat. {push}Push puts a value on the stack. {pop}Pop removes the top value, and drops the packet if it is a different one. ` +
    `{same}So push and then pop of the same value does nothing, {diff}and push and then pop of different values drops the packet. {q}With loops, a program can push and pop without bound. Can we still decide whether two programs are equivalent?` },
  { id: 's_result', chapter: '', pre: 0.4, post: 0.4, text:
    `{yes}Surprisingly, yes. {auto}A program becomes a finite automaton, whose transitions are labelled with pushes and pops. {norm}Three steps bring it to a normal form: {s1}cancel each push that meets its pop, {s2}keep only the runs that pop before they push, {s3}and zip the two halves together. ` +
    `{thm}Two programs are equivalent exactly when their normal forms accept the same language. {cex}When they are not, the procedure gives a counterexample.` },
  { id: 's_end', chapter: '', pre: 0.4, post: 3.0, text:
    `{title}Stack Cat: infinite state network verification. {paper}The paper has the decision procedure, its complexity, and a complete axiomatization.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "s_hook",
   "chapter": "",
   "start": 0.0,
   "dur": 33.38,
   "pre": 0.5,
   "post": 0.4,
   "audio": 32.48,
   "cues": {
    "net": 0.5,
    "prog": 7.7,
    "verify": 17.14,
    "equiv": 23.94,
    "dec": 26.26
   }
  },
  {
   "id": "s_limit",
   "chapter": "",
   "start": 33.38,
   "dur": 23.28,
   "pre": 0.4,
   "post": 0.4,
   "audio": 22.48,
   "cues": {
    "but": 0.4,
    "route": 3.52,
    "tele": 9.6,
    "parse": 12.64,
    "unb": 16.32,
    "inf": 18.16
   }
  },
  {
   "id": "s_lang",
   "chapter": "",
   "start": 56.66,
   "dur": 26.56,
   "pre": 0.4,
   "post": 0.4,
   "audio": 25.76,
   "cues": {
    "lang": 0.4,
    "push": 3.76,
    "pop": 6.24,
    "same": 11.12,
    "diff": 14.72,
    "q": 18.64
   }
  },
  {
   "id": "s_result",
   "chapter": "",
   "start": 83.22,
   "dur": 29.44,
   "pre": 0.4,
   "post": 0.4,
   "audio": 28.64,
   "cues": {
    "yes": 0.4,
    "auto": 2.64,
    "norm": 8.8,
    "s1": 11.52,
    "s2": 14.24,
    "s3": 17.28,
    "thm": 19.6,
    "cex": 25.12
   }
  },
  {
   "id": "s_end",
   "chapter": "",
   "start": 112.66,
   "dur": 13.64,
   "pre": 0.4,
   "post": 3,
   "audio": 10.24,
   "cues": {
    "title": 0.4,
    "paper": 4.72
   }
  }
 ],
 "total": 126.3
};

// ==== src/scenes/film.js ====
(function (addEventListener) {
// StacKAT, a two-minute film in five scenes, one story: a network is a program, and verification is program
// equivalence, decidable for finitely many packets; a stack makes the packets infinite; StacKAT adds push and pop;
// equivalence is still decidable, through a normal form of automata. One thing on screen at a time, large type;
// the player draws captions under y = 930, so everything here stays between y = 120 and y = 900.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const CX = W / 2;

  // ---- type helpers ---------------------------------------------------------------------------------------
  // Text is centred by the browser (a wide box with centred text), so nothing depends on measuring a font that
  // may not have loaded yet when the scenes are built.
  const LS = 0.16;   // the labels' letter spacing, in em; it leaves a trailing gap, made up for on the left
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase', color: C.dim, lineHeight: 1.2 });
  const SERIF = size => ({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, letterSpacing: '-0.005em' });
  const MONO = size => ({ fontFamily: 'var(--mono)', fontSize: size + 'px', lineHeight: 1.3, color: C.code, fontVariantLigatures: 'none', fontWeight: 450 });
  // a line made of parts [text, colour], centred on cx; each part is its own element, so that it can come in
  // (or be struck) by itself. Returns { root, parts }.
  function cline(root, cx, y, parts, style) {
    const b = box(root, cx - 1200, y, Object.assign({ width: '2400px', textAlign: 'center', whiteSpace: 'pre' }, style));
    if (style.letterSpacing) b.style.paddingLeft = style.letterSpacing;
    const ps = parts.map(([t, col]) => {
      const s = document.createElement('span');
      Object.assign(s.style, { display: 'inline-block', position: 'relative', whiteSpace: 'pre' });
      if (col) s.style.color = col;
      s.textContent = t; b.appendChild(s);
      return s;
    });
    return { root: b, parts: ps };
  }
  const clabel = (root, cx, y, text, size = 32, col) => cline(root, cx, y, [[text, col]], LABEL(size)).root;
  const cserif = (root, cx, y, text, size, col) => cline(root, cx, y, [[text, col]], SERIF(size)).root;
  // a neutral strike through one part of a line (deletion is grey): the text goes faint
  function strikePart(tl, span, at) {
    const u = el(span, 'div', { left: '-0.25em', right: '0.05em', top: '52%', height: '4px', borderRadius: '2px', background: C.dim, transformOrigin: 'left center' });
    tl.set(u, { sx: 0, o: 0 }, 0); tl.set(u, { o: 1 }, at); tl.to(u, { sx: 1 }, at, 0.45, E.io);
    tl.to(span, { color: C.faint }, at, 0.45);
  }
  // a label that comes in at `at` and leaves at `out`
  function step(tl, root, cx, y, text, at, out, size = 34, col) {
    const e = clabel(root, cx, y, text, size, col);
    fadeIn(tl, e, at, 0.5, 10);
    if (out != null) fadeOut(tl, e, out, 0.3, -8);
    return e;
  }

  // ---- drawing helpers --------------------------------------------------------------------------------------
  const LINE = 3;   // the drawings' line width
  // a thin-lined rounded box with text centred in it
  function cell(parent, x, y, w, h, text, { stroke = C.ink, color = C.ink, font = MONO(44), radius = 16, width = LINE } = {}) {
    const b = box(parent, x, y, { width: w + 'px', height: h + 'px', borderRadius: radius + 'px', boxShadow: `inset 0 0 0 ${width}px ${stroke}` });
    const t = box(b, 0, 0, Object.assign({ width: w + 'px', height: h + 'px', display: 'flex', alignItems: 'center', justifyContent: 'center', whiteSpace: 'pre' }, font, { color }), text);
    b._t = t;
    return b;
  }
  // a cell's text changes: it squeezes, changes, comes back
  function flip(tl, t, text, at, dur = 0.45) {
    tl.to(t, { sy: 0.05 }, at, dur * 0.4, E.in); tl.text(t, text, at + dur * 0.4); tl.to(t, { sy: 1 }, at + dur * 0.4, dur * 0.6, E.out);
  }
  const circleD = (x, y, r) => `M ${x - r} ${y} a ${r} ${r} 0 1 0 ${2 * r} 0 a ${r} ${r} 0 1 0 ${-2 * r} 0`;
  // text placed by its centre (for edge labels)
  function ctext(parent, cx, cy, text, style, h) {
    return box(parent, cx - 300, cy - h / 2, Object.assign({ width: '600px', height: h + 'px', display: 'flex', alignItems: 'center', justifyContent: 'center', whiteSpace: 'pre' }, style), text);
  }

  // A packet's header: three fields, their names above in cyan, their values in cells.
  function header(parent, x, y, fields, { w = 150, h = 90, gap = 14, size = 44, names = 32 } = {}) {
    const g = box(parent, x, y, { width: (3 * w + 2 * gap) + 'px', height: (h + 60) + 'px' });
    const vals = fields.map(([name, v], i) => {
      ctext(g, i * (w + gap) + w / 2, 20, name, Object.assign(MONO(names), { color: C.bind }), 44);
      return cell(g, i * (w + gap), 50, w, h, v, { font: MONO(size) });
    });
    return { g, vals, width: 3 * w + 2 * gap };
  }

  // A stack drawn as a row of amber cells; index 0, the top, is on the left.
  class Row {
    constructor(tl, parent, x, y, { w = 140, h = 100, gap = 12 } = {}) {
      Object.assign(this, { tl, parent, x, y, w, h, step: w + gap }); this.cells = [];
    }
    _make(text) { return cell(this.parent, this.x, this.y, this.w, this.h, text, { stroke: C.pat, font: MONO(44) }); }
    layout(at) { this.cells.forEach((c, i) => { if (c && c._i !== i) { this.tl.to(c, { x: i * this.step }, at, 0.55, E.io); c._i = i; } }); }
    // cells that are there from the start of their appearance, at the bottom end
    append(text, at, dur = 0.5) {
      const c = this._make(text), i = this.cells.length; c._i = i; this.cells.push(c);
      this.tl.set(c, { x: i * this.step, y: 14, o: 0 }, 0); this.tl.to(c, { y: 0, o: 1 }, at, dur, E.out5);
      return c;
    }
    // a value goes on top: the others make room, it comes down into place
    push(text, at) {
      for (const c of this.cells) c._i = -1;
      this.cells.unshift(null); this.layout(at);
      const c = this._make(text); c._i = 0; this.cells[0] = c;
      this.tl.set(c, { x: 0, y: -90, o: 0 }, 0); this.tl.to(c, { y: 0, o: 1 }, at + 0.25, 0.5, E.out5);
      return c;
    }
    // the top lifts off and fades; the others close up
    pop(at) {
      const c = this.cells.shift();
      this.tl.to(c, { y: -80 }, at, 0.5, E.in); this.tl.to(c, { o: 0 }, at + 0.1, 0.4, E.in);
      this.layout(at + 0.3);
      return c;
    }
  }

  // ============================================ s_hook =========================================================
  scene('s_hook', ({ tl, root, cue }) => {
    // the network: a host, three switches A, B, C, a host, in a row (drawn at full size, in one layer)
    const g = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const svg = svgLayer(g);
    const Y = 420, HX = [280, 1640], SX = [660, 960, 1260], HR = 50, SW = 190, SH = 136;
    const hosts = HX.map((x, i) => {
      const p = path(tl, svg, circleD(x, Y, HR), { stroke: C.ink, width: LINE });
      tl.to(p, { draw: 1 }, 0.25 + i * 0.9, 0.6, E.io);
      return p;
    });
    const sws = SX.map((x, i) => {
      const b = cell(g, x - SW / 2, Y - SH / 2, SW, SH, 'ABC'[i], { font: SERIF(72), radius: 22 });
      tl.set(b, { o: 0, s: 0.96 }, 0); tl.to(b, { o: 1, s: 1 }, 0.4 + i * 0.22, 0.5, E.out5);
      return b;
    });
    const ends = [[HX[0] + HR, SX[0] - SW / 2], [SX[0] + SW / 2, SX[1] - SW / 2], [SX[1] + SW / 2, SX[2] - SW / 2], [SX[2] + SW / 2, HX[1] - HR]];
    ends.forEach(([a, b], i) => tl.to(path(tl, svg, `M ${a} ${Y} L ${b} ${Y}`, { stroke: C.ink, width: LINE }), { draw: 1 }, 0.5 + i * 0.2, 0.5, E.io));
    // "forwards packets": a packet, its header fields, at A
    const pk = header(g, 0, Y + 100, [['sw', 'A'], ['dst', '7'], ['port', '1']], { w: 150, h: 100, gap: 16, size: 52, names: 34 });
    pk.g.style.left = (SX[0] - pk.width / 2) + 'px';
    fadeIn(tl, pk.g, 1.65, 0.6, 16);
    // "match some header fields": the switch looks at dst
    const tint = (c, a, b) => { tl.to(c, { bg: alpha(C.dim, 0.14) }, a, 0.3); tl.to(c, { bg: alpha(C.dim, 0) }, b, 0.4); };
    tint(pk.vals[1], 3.4, 4.7);
    // "rewrite some": port := 2
    tint(pk.vals[2], 4.75, 5.6);
    flip(tl, pk.vals[2]._t, '2', 4.8);
    // "and send the packet on": to B, then to C, the switch field changing at each hop
    tl.to(pk.g, { x: SX[1] - SX[0] }, 5.75, 0.6, E.io); flip(tl, pk.vals[0]._t, 'B', 5.95);
    tl.to(pk.g, { x: SX[2] - SX[0] }, 6.55, 0.6, E.io); flip(tl, pk.vals[0]._t, 'C', 6.75);

    // "Net Cat reads those rules as a program.": the drawing goes up and shrinks; the program under it
    const tP = cue("prog"), K = 0.75, DY = -159;
    tl.to(pk.g, { o: 0 }, tP - 0.3, 0.35, E.in);
    tl.to(g, { s: K, y: DY }, tP - 0.2, 0.8, E.io);
    const S = 64, cw = charWidth(S);
    const px = Math.round((W - 28 * cw) / 2), py = 492;
    const code = new Code(tl, root, px, py, S, { leading: 1.62 });
    const P0 = '  if {d|dst|b} == 7 then {p|port|b} {a1|:=} 2\n  {s|sw|b} {a2|:=} B';
    const P1 = '{lp|(} if {d|dst|b} == 7 then {p|port|b} {a1|:=} 2\n  {s|sw|b} {a2|:=} B {rp|)*}';
    code.show(P0, tP + 0.5, { stagger: 0.012 });
    const ly = py + 2 * code.lh + 36;
    // "A field is a variable,"
    const tF = 10.7, tR = 12.4, tL = 14.4;
    step(tl, root, CX, ly, 'a field = a variable', tF, tR - 0.35);
    for (const id of ['d', 'p', 's']) code.mark([id], C.bind, tF + 0.05, { out: tR - 0.35, pad: 8 });
    // "a rule is an if statement,"
    step(tl, root, CX, ly, 'a rule = an if', tR, tL - 0.35);
    code.mark(t => t.line === 0, C.dim, tR + 0.05, { out: tL - 0.35, pad: 8, fill: 0.08 });
    // "and a path through the network is a loop."
    const tLoop = 16.18, tV = cue('verify');
    step(tl, root, CX, ly, 'a path = a loop', tL, tV - 0.3);
    code.swap(P1, tLoop - 0.25, { dur: 0.5 });
    code.mark(['lp'], C.dim, tLoop + 0.25, { out: tV - 0.3, pad: 6, fill: 0.08 });
    code.mark(['rp'], C.dim, tLoop + 0.25, { out: tV - 0.3, pad: 6, fill: 0.08 });

    // "whether one host can reach another": the program dims; the hosts are marked and joined
    const tE0 = cue('equiv');
    tl.to(code.root, { o: 0.35 }, tV - 0.1, 0.5);
    const hy = 540 + (Y - 540) * K + DY, hx = HX.map(x => CX + (x - CX) * K), hr = HR * K;
    const top = svgLayer(root);
    // the two hosts: a cyan dot in each
    const dr = hr * 0.5;
    hx.forEach((x, i) => {
      const d = box(root, x - dr, hy - dr, { width: 2 * dr + 'px', height: 2 * dr + 'px', borderRadius: '50%', background: C.bind });
      tl.set(d, { o: 0, s: 0.3 }, 0); tl.to(d, { o: 1, s: 1 }, 19.6 + i * 0.25, 0.4, E.out5);
      tl.to(d, { o: 0 }, tE0 - 0.4, 0.35, E.in);
    });
    const arcY = hy + hr + 6;
    const arc = path(tl, top, `M ${hx[0]} ${arcY + 4} Q ${CX} ${arcY + 126} ${hx[1]} ${arcY + 4}`, { stroke: C.ink, width: LINE, dash: '12 12' });
    tl.set(arc, { o: 0 }, 0); tl.to(arc, { o: 1 }, 20.05, 0.5);
    const reach = clabel(root, CX, arcY + 76, 'reachable?', 32, C.ink);
    fadeIn(tl, reach, 20.3, 0.5, 10);

    // "are these two programs equivalent?"
    const tE = cue('equiv'), out = tE - 0.4;
    for (const e of [g, code.root, top, reach]) tl.to(e, { o: 0 }, out, 0.35, E.in);
    const eq = cserif(root, CX, 360, 'program₁ ≡ program₂ ?', 96);
    fadeIn(tl, eq, tE - 0.1, 0.7, 16);
    // "For Net Cat this can be decided, because a packet has finitely many fields, with finitely many values."
    const dec = clabel(root, CX, 524, 'decidable', 44, C.good);
    fadeIn(tl, dec, 27.35, 0.6, 12);
    const why = cline(root, CX, 612, [['finitely many fields', null], [' × finitely many values', null]], LABEL(34));
    fadeIn(tl, why.parts[0], 29.3, 0.5, 10);
    fadeIn(tl, why.parts[1], 31.05, 0.5, 10);
  });

  // ============================================ s_limit ========================================================
  scene('s_limit', ({ tl, root, cue }) => {
    // "But real packets also carry a stack.": the header, and a stack attached to its right
    const SW = 150, GAP = 12, STEP = SW + GAP, HW = 3 * 150 + 2 * 14, J = 22;
    const x0 = Math.round((W - (HW + J + 3 * STEP - GAP)) / 2), y0 = 370;
    const hd = header(root, x0, y0, [['sw', 'A'], ['dst', '7'], ['port', '2']]);
    fadeIn(tl, hd.g, 0.25, 0.6, 16);
    const sx = x0 + HW + J;
    const stk = new Row(tl, root, sx, y0 + 50, { w: SW, h: 90, gap: GAP });
    const sl = box(root, sx, y0 + 150, { width: (3 * STEP - GAP) + 'px', height: '40px', display: 'flex', alignItems: 'center', paddingLeft: '4px' });
    Object.assign(sl.style, LABEL(32), { color: C.pat });
    sl.textContent = 'stack';
    const tS = 2.2;
    fadeIn(tl, sl, tS, 0.5, 10);
    const cs = ['', '', ''].map((t, i) => stk.append(t, tS + 0.1 + i * 0.1));
    const ly = y0 + 240;
    // "In source routing, a packet carries its whole path, and each router pops the next hop."
    const tR = cue('route'), tT = cue('tele'), tPa = cue('parse'), tU = cue('unb');
    step(tl, root, CX, ly, 'source routing: the path', tR - 0.05, tT - 0.35, 36);
    ['B', 'C', 'D'].forEach((t, i) => flip(tl, cs[i]._t, t, 5.75 + i * 0.12));
    stk.pop(7.85);
    // "Telemetry pushes a record at every hop."
    step(tl, root, CX, ly, 'telemetry: a record at every hop', tT - 0.05, tPa - 0.35, 36);
    stk.push('r1', 10.25);
    stk.push('r2', 11.35);
    // "And parsing a packet pops its bytes one by one."
    step(tl, root, CX, ly, 'parsing: the bytes, one by one', tPa - 0.05, tU - 0.35, 36);
    ['0x45', '0x00', '0x00', '0x3c'].forEach((t, i) => flip(tl, stk.cells[i]._t, t, 12.9 + i * 0.1));
    stk.pop(13.8);
    // "A stack has no bound,": it grows to the frame's edge
    // the packet makes room on the left, and cells keep coming to the frame's edge
    const shift = 160 - x0;
    for (const e of [hd.g, sl]) tl.to(e, { x: shift }, tU - 0.1, 0.7, E.io);
    tl.to(sl, { o: 0 }, tU - 0.1, 0.3);
    stk.cells.forEach((c, i) => tl.to(c, { x: i * STEP + shift }, tU - 0.1, 0.7, E.io));
    let n = stk.cells.length;
    const more = ['0x1c', '0x46', '0x40', '0x00', '0x40', '0x06', '0xb1', '0xe6'];
    let k = 0;
    while (sx + shift + n * STEP + SW < W - 40 && k < more.length) {
      const c = stk.append(more[k++], tU + 0.35 + k * 0.17, 0.35); tl.set(c, { x: n * STEP + shift }, 0); n++;
    }
    const dots = box(root, sx + shift + n * STEP - 6, y0 + 50, Object.assign({ height: '90px', display: 'flex', alignItems: 'center', whiteSpace: 'pre' }, MONO(56), { color: C.pat }), '…');
    fadeIn(tl, dots, tU + 0.45 + k * 0.17, 0.35, 0);
    // "so there are infinitely many packets, and the finite-state argument is gone."
    const tI = cue('inf');
    const all = [hd.g, sl, dots, ...stk.cells];
    for (const e of all) tl.to(e, { o: 0.3, y: -40 }, tI - 0.15, 0.6, E.io);
    const inf = clabel(root, CX, ly - 50, 'infinitely many packets', 48, C.ink);
    fadeIn(tl, inf, tI - 0.05, 0.6, 12);
    const d = cline(root, CX, ly + 40, [['decidable', C.good]], LABEL(44));
    fadeIn(tl, d.root, 20.3, 0.5, 10);
    strikePart(tl, d.parts[0], 21.85);
  });

  // ============================================ s_lang =========================================================
  scene('s_lang', ({ tl, root, cue }) => {
    // "Stack Cat adds two operations to Net Cat."
    const S = 64, cw = charWidth(S);
    const L = '{o1|f := n|d}  {o2|f == n|d}  {o3|+|d}  {o4|·|d}  {o5|*|d}  {pu|push(n)|p}  {po|pop(n)|p}';
    const ops = new Code(tl, root, Math.round((W - 40 * cw) / 2), 420, S, { palette: { d: C.dim } });
    ops.show(L.replace(/ *\{pu[^]*$/, ''), 0.2, { stagger: 0.05 });
    const opsP = new Code(tl, root, ops.x, ops.y, S);
    opsP.show(' '.repeat(25) + '{pu|push(n)|p}  {po|pop(n)|p}', 1.1, { stagger: 0.25 });
    const tag = clabel(root, CX, 556, 'stackat = netkat + a stack', 36);
    fadeIn(tl, tag, 2.55, 0.5, 10);
    const tPu = cue('push');
    for (const e of [ops.root, opsP.root, tag]) fadeOut(tl, e, tPu - 0.45, 0.35);

    // "Push puts a value on the stack.": a stack [1, 2], drawn upright, the top at the top
    const OS = 72, ocw = charWidth(OS), CW = 230, CH = 130, ST = 146, OG = 170, ox = Math.round((W - (7 * ocw + OG + CW)) / 2), bx = ox + Math.round(7 * ocw) + OG, by = 549;
    const cellAt = (text, i) => cell(root, bx, by - i * ST, CW, CH, text, { stroke: C.pat, font: MONO(64), radius: 20 });
    const c1 = cellAt('1', 0), c2 = cellAt('2', 1), c3 = cellAt('3', 2);
    fadeIn(tl, c1, tPu - 0.15, 0.5, 14); fadeIn(tl, c2, tPu - 0.05, 0.5, 14);
    const oy = by - 2 * ST + (CH - Math.round(OS * 1.62)) / 2;
    const op = new Code(tl, root, ox, oy, OS);
    op.show('{op|push|p}{l|(|p}{v|3|p}{r|)|p}', tPu, { stagger: 0.03 });
    tl.set(c3, { y: -110, o: 0 }, 0); tl.to(c3, { y: 0, o: 1 }, 4.3, 0.55, E.out5);
    // "Pop removes the top value": it lifts off; a tick
    const tPo = cue('pop');
    op.swap('{op2|pop|p}{l|(|p}{v|3|p}{r|)|p}', tPo - 0.25, { dur: 0.5 });
    tl.to(c3, { y: -110 }, 6.75, 0.5, E.in); tl.to(c3, { o: 0 }, 6.85, 0.4, E.in);
    const svg = svgLayer(root);
    const kx = bx - OG / 2, ky = oy + Math.round(OS * 1.62) / 2;
    const tk = tick(tl, svg, kx, ky, 60, C.good, 7);
    tl.to(tk, { draw: 1 }, 7.2, 0.4); tl.to(tk, { o: 0 }, 8.1, 0.3);
    // "and drops the packet if it is a different one": pop(5) on [1, 2]
    op.swap('{op2|pop|p}{l|(|p}{v|5|p}{r|)|p}', 8.25, { dur: 0.5 });
    const xs = cross(tl, svg, kx, ky, 46, C.bad, 7);
    xs.forEach((p, i) => tl.to(p, { draw: 1 }, 9.85 + i * 0.12, 0.3));
    for (const c of [c1, c2]) tl.to(c, { o: 0.3 }, 9.85, 0.5);
    const drop = clabel(root, CX, by + CH + 46, 'packet dropped', 36, C.bad);
    fadeIn(tl, drop, 9.95, 0.5, 10);
    const tSa = cue('same');
    for (const e of [c1, c2, op.root, drop, svg]) tl.to(e, { o: 0 }, tSa - 0.45, 0.35, E.in);

    // "So push and then pop of the same value does nothing,"
    const RS = 72, rcw = charWidth(RS), GW = 420, rx = Math.round((W - (20 * rcw + 80 + GW)) / 2);
    const pal = { x: C.code };
    const r1 = new Code(tl, root, rx, 305, RS, { palette: pal });
    r1.show('{a|push(v)|p} · {b|pop(v)|p} ≡ 1', tSa - 0.1, { stagger: 0.03 });
    const gl = (y, t, at) => { const e = label(root, rx + 20 * rcw + 80, y + (r1.lh - 41) / 2, t, { fontSize: '34px' }); fadeIn(tl, e, at, 0.5, 10); return e; };
    const g1 = gl(305, 'does nothing', 13.55);
    // "and push and then pop of different values drops the packet."
    const tD = cue('diff');
    const r2 = new Code(tl, root, rx, 435, RS, { palette: pal });
    r2.show('{a|push(v)|p} · {b|pop(w)|p} ≡ 0', tD - 0.1, { stagger: 0.03 });
    const g2 = gl(435, 'drops the packet', 17.05);
    // "With loops, a program can push and pop without bound. Can we still decide whether two programs are equivalent?"
    const tQ = cue('q');
    for (const e of [r1.root, r2.root, g1, g2]) tl.to(e, { o: 0.35 }, tQ - 0.2, 0.5);
    const QS = 64, qcw = charWidth(QS);
    const q = new Code(tl, root, Math.round((W - 41 * qcw) / 2), 612, QS, { palette: pal });
    q.show('{a1|push(a)|p}* · {b1|pop(a)|p}* ≡ {a2|push(a)|p}* + {b2|pop(a)|p}*', tQ - 0.1, { stagger: 0.02 });
    const qm = new Code(tl, root, q.x, q.y, QS);
    qm.show(' '.repeat(40) + '{qm|?|p}', 22.75);
  });

  // ============================================ s_result =======================================================
  scene('s_result', ({ tl, root, cue }) => {
    // "Surprisingly, yes.": large, then to the top left, smaller
    const yes = serif(root, 160, 120, 'Decidable.', 96, { color: C.good, transformOrigin: '0 0' });
    const yw = 420;   // about the word's width at 96 px, to centre it
    tl.set(yes, { x: CX - yw / 2 - 160, y: 420 - 120 + 20, o: 0 }, 0);
    tl.to(yes, { y: 420 - 120, o: 1 }, 0.3, 0.7, E.out5);
    tl.to(yes, { x: 0, y: 0, s: 56 / 96 }, 2.2, 0.8, E.io);

    // "A program becomes a finite automaton, whose transitions are labelled with pushes and pops."
    const tA = cue('auto');
    const svg = svgLayer(root), lay = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const Y = 379, X = [600, 960, 1320], R = 58;
    const states = X.map((x, i) => {
      const p = path(tl, svg, circleD(x, Y, R), { stroke: C.ink, width: LINE });
      tl.to(p, { draw: 1 }, tA - 0.1 + i * 0.2, 0.5, E.io);
      return p;
    });
    const acc = path(tl, svg, circleD(X[2], Y, R - 10), { stroke: C.ink, width: LINE });
    tl.to(acc, { draw: 1 }, tA + 0.5, 0.4, E.io);
    const start = arrow(tl, svg, X[0] - R - 90, Y, X[0] - R - 6, Y, { stroke: C.ink, width: LINE, head: 14 });
    drawArrow(tl, start, tA + 0.3, 0.4);
    const ES = 40, eh = 56;
    const eStyle = Object.assign(MONO(ES), { color: C.pat });
    const e1 = arrow(tl, svg, X[0] + R + 6, Y, X[1] - R - 6, Y, { stroke: C.ink, width: LINE, head: 14 });
    const e2 = arrow(tl, svg, X[1] + R + 6, Y, X[2] - R - 6, Y, { stroke: C.ink, width: LINE, head: 14 });
    drawArrow(tl, e1, 5.4, 0.45); drawArrow(tl, e2, 5.6, 0.45);
    const l1 = ctext(lay, (X[0] + X[1]) / 2, Y - 42, 'push(a)', eStyle, eh);
    const l2 = ctext(lay, (X[1] + X[2]) / 2, Y - 42, 'pop(a)', eStyle, eh);
    fadeIn(tl, l1, 6.95, 0.5, 10); fadeIn(tl, l2, 7.55, 0.5, 10);
    // a self-loop on the last state
    const a0 = -2.05, a1 = -1.09, lx = X[2], P = (a, r) => [lx + r * Math.cos(a), Y + r * Math.sin(a)];
    const [sx0, sy0] = P(a0, R + 4), [sx1, sy1] = P(a1, R + 4), [c0x, c0y] = P(a0 - 0.25, R + 120), [c1x, c1y] = P(a1 + 0.25, R + 120);
    const loop = path(tl, svg, `M ${sx0} ${sy0} C ${c0x} ${c0y} ${c1x} ${c1y} ${sx1} ${sy1}`, { stroke: C.ink, width: LINE });
    const lh = el(svg, 'path');
    const ang = Math.atan2(sy1 - c1y, sx1 - c1x) * 180 / Math.PI;
    lh.setAttribute('d', 'M -14 -7.7 L 0 0 L -14 7.7'); lh.setAttribute('fill', 'none'); lh.setAttribute('stroke-width', LINE);
    lh.setAttribute('stroke-linecap', 'round'); lh.setAttribute('stroke-linejoin', 'round'); lh.style.stroke = C.ink;
    lh.setAttribute('transform', `translate(${sx1} ${sy1}) rotate(${ang})`);
    tl.set(lh, { o: 0 }, 0);
    tl.to(loop, { draw: 1 }, 7.6, 0.5, E.io); tl.to(lh, { o: 1 }, 8.0, 0.15);
    const l3 = ctext(lay, lx, Y - R - 104, 'pop(a)', eStyle, eh);
    fadeIn(tl, l3, 7.85, 0.5, 10);
    const name = clabel(root, CX, Y + 290, 'a finite automaton', 36);
    fadeIn(tl, name, 3.9, 0.5, 10);

    // "Three steps bring it to a normal form:"
    const tN = cue('norm');
    fadeOut(tl, name, tN - 0.3, 0.3);
    // the steps, a left-aligned column centred as a block
    const col = box(root, 0, Y + 290, { width: W + 'px', display: 'flex', justifyContent: 'center' });
    const inner = document.createElement('div'); col.appendChild(inner);
    const steps = ['1 · cancel a push that meets its pop', '2 · keep runs that pop before they push', '3 · zip the two halves'].map(t => {
      const e = document.createElement('div');
      Object.assign(e.style, LABEL(36), { color: C.ink, whiteSpace: 'pre', height: '60px', paddingLeft: LS + 'em' });
      e.textContent = t; inner.appendChild(e);
      return e;
    });
    const at = [cue('s1') - 0.1, cue('s2') - 0.1, cue('s3') - 0.1];
    steps.forEach((e, i) => { fadeIn(tl, e, at[i], 0.5, 10); if (i < 2) tl.to(e, { color: C.dim }, at[i + 1], 0.4); });
    // step 1 in the picture: a push edge followed by a pop edge gets a shortcut
    const look = (e, a, b) => { tl.to(e, { color: C.ink }, a, 0.3); tl.to(e, { color: C.pat }, b, 0.4); };
    look(l1, 11.95, 13.6); look(l2, 13.2, 13.6);
    const cut = arrow(tl, svg, X[0] + 10, Y + R + 8, X[2] - 10, Y + R + 8, { stroke: C.ink, width: LINE, head: 14, bend: 200 });
    drawArrow(tl, cut, 13.45, 0.6);
    const l4 = ctext(lay, CX, Y + R + 8 + 100 + 30, '1', MONO(ES), eh);
    fadeIn(tl, l4, 13.9, 0.4, 8);

    // "Two programs are equivalent exactly when their normal forms accept the same language."
    const tT = cue('thm');
    for (const e of steps) fadeOut(tl, e, tT - 0.35, 0.3);
    for (const e of [svg, lay]) tl.to(e, { o: 0.3 }, tT - 0.2, 0.5);
    const th = cline(root, CX, Y + 270, [['⟦e₁⟧ = ⟦e₂⟧   ⟺   L(A₁) = L(A₂)', null]], Object.assign(SERIF(72), { fontFamily: 'var(--serif), "STIX Two Math", "STIX Two Text"', color: C.code })).root;
    fadeIn(tl, th, tT - 0.1, 0.6, 14);
    const tg = cline(root, CX, Y + 392, [['equivalent', C.good], [' exactly when the normal forms agree', null]], LABEL(34)).root;
    fadeIn(tl, tg, 20.45, 0.5, 10);
    // "When they are not, the procedure gives a counterexample."
    const cx = clabel(root, CX, Y + 452, 'otherwise: a counterexample', 34);
    fadeIn(tl, cx, cue('cex') - 0.05, 0.5, 10);
  });

  // ============================================ s_end ==========================================================
  scene('s_end', ({ tl, root, cue }) => {
    const tT = cue('title');
    const t1 = cserif(root, CX, 300, 'StacKAT', 120);
    fadeIn(tl, t1, tT - 0.15, 0.8, 24);
    const t2 = cserif(root, CX, 470, 'Infinite State Network Verification', 52);
    fadeIn(tl, t2, 1.5, 0.7, 16);
    const t3 = clabel(root, CX, 570, 'pldi 2025', 32);
    fadeIn(tl, t3, 2.9, 0.6, 10);
    // "The paper has the decision procedure, its complexity, and a complete axiomatization."
    const p0 = clabel(root, CX, 680, 'in the paper', 32);
    fadeIn(tl, p0, cue('paper') - 0.1, 0.5, 10);
    const p = cline(root, CX, 730, [['the decision procedure', null], [' · its complexity', null], [' · a complete axiomatization', null]], LABEL(32));
    const pa = [5.8, 7.1, 8.6];
    p.parts.forEach((e, i) => fadeIn(tl, e, pa[i], 0.5, 10));
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
window.CAPTIONS = [[0.5, 3.42, "A network forwards packets by rules:"], [3.46, 5.9, "match some header fields, rewrite some,"], [5.94, 7.66, "and send the packet on."], [7.7, 10.7, "NetKAT reads those rules as a program."], [10.74, 14.38, "A field is a variable, a rule is an if statement,"], [14.42, 17.1, "and a path through the network is a loop."], [17.14, 18.78, "A question about the network,"], [18.82, 21.34, "such as whether one host can reach another,"], [21.38, 23.9, "then becomes a question about programs:"], [23.94, 26.22, "are these two programs equivalent?"], [26.26, 28.5, "For NetKAT this can be decided,"], [28.54, 31.1, "because a packet has finitely many fields,"], [31.14, 33.74, "with finitely many values."], [33.78, 36.86, "But real packets also carry a stack."], [36.9, 40.3, "In source routing, a packet carries its whole path,"], [40.34, 42.94, "and each router pops the next hop."], [42.98, 45.98, "Telemetry pushes a record at every hop."], [46.02, 49.66, "And parsing a packet pops its bytes one by one."], [49.7, 52.86, "A stack has no bound, so there are infinitely many"], [52.9, 57.02, "packets, and the finite-state argument is gone."], [57.06, 60.38, "StacKAT adds two operations to NetKAT."], [60.42, 62.86, "Push puts a value on the stack."], [62.9, 64.97, "Pop removes the top value,"], [65.01, 67.74, "and drops the packet if it is a different one."], [67.78, 71.34, "So push and then pop of the same value does nothing,"], [71.38, 74.1, "and push and then pop of different values drops"], [74.14, 75.26, "the packet."], [75.3, 78.78, "With loops, a program can push and pop without"], [78.82, 79.45, "bound."], [79.49, 83.58, "Can we still decide whether two programs are equivalent?"], [83.62, 85.82, "Surprisingly, yes."], [85.86, 88.38, "A program becomes a finite automaton,"], [88.42, 90.78, "whose transitions are labelled with pushes and"], [90.82, 91.98, "pops."], [92.02, 94.7, "Three steps bring it to a normal form:"], [94.74, 97.42, "cancel each push that meets its pop,"], [97.46, 100.46, "keep only the runs that pop before they push,"], [100.5, 102.78, "and zip the two halves together."], [102.82, 105.54, "Two programs are equivalent exactly when their"], [105.58, 108.3, "normal forms accept the same language."], [108.34, 113.02, "When they are not, the procedure gives a counterexample."], [113.06, 114.22, "StacKAT:"], [114.26, 117.34, "infinite state network verification."], [117.38, 119.82, "The paper has the decision procedure,"], [119.86, 124.28, "its complexity, and a complete axiomatization."]];
