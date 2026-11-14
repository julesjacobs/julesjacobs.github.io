// A paradoxical local minimum: the film's scripts in one file, made by tools/web.py.

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
// A video (about five minutes) for social media on the note "A paradoxical local minimum" (2022): a point that is
// a strict minimum along every straight line through it and is not a local minimum. The intuition is the author's: a
// half-pipe bent into a ring, then bent gently downward. Captions are drawn in the picture.
// {name} marks a cue, as in the other films' narration.
window.NARRATION = [
  { id: 'm_hook', chapter: '', pre: 1.9, post: 0.35, text:
    `{q}Stand at a point on a hilly surface, {point}and suppose that every straight line through it goes uphill, in both directions. ` +
    `{mean}That means: take a step along any line, as small as you like, but not zero, and you end up strictly higher than where you started. {ask}Is the point a local minimum? ` +
    `{obv}Obviously, yes. Every direction is a straight line, so whichever way you step, you go up, {near}and nothing nearby can be lower. {no}And yet, that is wrong. ` },
  { id: 'm_holes', chapter: '', pre: 0.6, post: 0.35, text:
    `{bowl}Here is one way it goes wrong. Take a bowl. {min}Its bottom is as good a minimum as you could ask for. {holes}Now push single points of the surface down, below the bottom. ` +
    `{spiral}The first at distance one, turned by one radian. The next at distance a half, turned by two radians. Then at distance a third, turned by three. And so on, spiralling in. ` +
    `{line}Now take any straight line through the bottom. {one}It hits at most one of these points. For two of them to lie on the same line, a whole number of radians would have to be a multiple of pi, and pi is irrational. ` +
    `{up}So near the bottom, the line runs on the untouched bowl, and every step goes up. {close}And yet, as close to the bottom as you like, there are points below it.` },
  { id: 'm_area', chapter: '', pre: 0.35, post: 0.35, text:
    `{cheat}That feels like cheating: the holes have no width at all. {wide}And it is fragile. Give every hole some width, and it stops working. {wedge}Seen from the bottom, a hole with width blocks a whole wedge of directions. ` +
    `{sweep}The wedges keep coming, round and round. {through}However thin you make them, some line passes through infinitely many: hole after hole, all the way in. {fail}On that line, you do not go up: however short a step you allow, some step lands in a hole.` },
  { id: 'm_crev', chapter: '', pre: 0.35, post: 0.35, text:
    `{so}So low ground with any width cannot be scattered around the point. {strong}If every straight line is to go up, {curve}the only hope is to slip the low ground in along a curve, thinner and thinner, so that every straight line leaves it at once. ` +
    `{path}Then there would be a whole path that goes strictly down, from the very first step. {wild}You can picture it: a bowl, with a crevasse carved into it along a curved path. ` +
    `{smooth}But here is the second surprise. Nothing needs to be carved. The surface can be perfectly smooth.` },
  { id: 'm_pipe', chapter: '', pre: 0.35, post: 0.35, text:
    `{pipe}To see how, take a half-pipe, and bend it into a ring. {bottom}Its lowest points form a circle, all at the same height. {stand}Stand at one of them. {straight}Any straight step climbs the wall. {tangent}Even a step along the pipe climbs, because the pipe curves away under you. {level}To stay level, you have to follow the circle.` },
  { id: 'm_bend', chapter: '', pre: 0.35, post: 0.35, text:
    `{bend}Now bend the pipe downward, ever so gently, away from where you stand. {down}The circle that was level now goes downhill. {still}But a straight step still climbs, even along the tangent. {drift}The tangent drifts off the circle, and up the wall, {faster}and the wall rises faster than the bend falls. ` +
    `{gentle}This is why the bend has to be so gentle. Along the tangent, the wall rises only like the fourth power of the step. {slower}So the bend must fall more slowly than that: like the fourth power with a smaller factor, or like a higher power. {tilt2}Had we simply tilted the pipe, the tangent would have gone down with it. ` +
    `{both}So every straight line goes up, and the circle goes down. {water}Now fill the pipe with water, up to the level of where you stand. {wet}The circle goes under water on both sides. {dry}But every straight line starts out on dry ground. ` +
    `{above}Seen from above, this is the picture we began with: {lines2}straight lines that all go up, {path2}and one curved path that goes down.` },
  { id: 'm_poly', chapter: '', pre: 0.35, post: 0.35, text:
    `{poly}The surface can even be a polynomial. {trough}This part is the pipe: zero on the unit circle, and rising on both sides. {tilt}This part is the bend. {circ}On the circle, the pipe is zero, and the bend makes the height negative. {tan}On the tangent line, the pipe wins, two to one.` },
  { id: 'm_why', chapter: '', pre: 0.35, post: 0.35, text:
    `{why}So what was wrong with the obvious argument? {reach}Every point under water does lie on a straight line from where you stand. {first}But along that line you first climb, on dry ground, and only then come down to the water. ` +
    `{each}On every line, there is a distance that stays dry. {order}But a local minimum needs one distance that works for every line: the same words, in the other order. ` +
    `{inf}And here, the dry distance shrinks to nothing as the line turns toward the pipe. {pin}The pinholes were the same: each line stayed clear of them up to some distance, but no one distance worked for every line. ` +
    `{test}This is also why the second derivative test asks for positive definite, and not merely semidefinite: {hess}at this point, the second derivative along the tangent is zero.` },
  { id: 'm_end', chapter: '', pre: 0.35, post: 3.0, text:
    `{end}A minimum on every line is not a minimum.` },
];

// ==== build/timeline.js ====
window.TIMELINE = {
 "scenes": [
  {
   "id": "m_hook",
   "chapter": "",
   "start": 0.0,
   "dur": 31.65,
   "pre": 1.9,
   "post": 0.35,
   "audio": 29.4,
   "cues": {
    "q": 1.9,
    "point": 4.46,
    "mean": 9.9,
    "ask": 18.62,
    "obv": 20.7,
    "near": 27.18,
    "no": 29.58
   }
  },
  {
   "id": "m_holes",
   "chapter": "",
   "start": 31.65,
   "dur": 49.43,
   "pre": 0.6,
   "post": 0.35,
   "audio": 48.48,
   "cues": {
    "bowl": 0.6,
    "min": 4.2,
    "holes": 7.56,
    "spiral": 12.067,
    "line": 25.56,
    "one": 28.6,
    "up": 39.24,
    "close": 45.24
   }
  },
  {
   "id": "m_area",
   "chapter": "",
   "start": 81.08,
   "dur": 31.64,
   "pre": 0.35,
   "post": 0.35,
   "audio": 30.94,
   "cues": {
    "cheat": 0.35,
    "wide": 4.59,
    "wedge": 9.91,
    "sweep": 14.75,
    "through": 17.99,
    "fail": 25.31
   }
  },
  {
   "id": "m_crev",
   "chapter": "",
   "start": 112.72,
   "dur": 33.6,
   "pre": 0.35,
   "post": 0.35,
   "audio": 32.9,
   "cues": {
    "so": 0.35,
    "strong": 5.15,
    "curve": 7.47,
    "path": 16.11,
    "wild": 21.39,
    "smooth": 27.07
   }
  },
  {
   "id": "m_pipe",
   "chapter": "",
   "start": 146.32,
   "dur": 21.04,
   "pre": 0.35,
   "post": 0.35,
   "audio": 20.34,
   "cues": {
    "pipe": 0.35,
    "bottom": 4.67,
    "stand": 8.67,
    "straight": 10.27,
    "tangent": 12.99,
    "level": 18.137
   }
  },
  {
   "id": "m_bend",
   "chapter": "",
   "start": 167.36,
   "dur": 61.58,
   "pre": 0.35,
   "post": 0.35,
   "audio": 60.88,
   "cues": {
    "bend": 0.35,
    "down": 5.47,
    "still": 8.777,
    "drift": 12.75,
    "faster": 16.11,
    "gentle": 19.47,
    "slower": 27.07,
    "tilt2": 34.75,
    "both": 38.83,
    "water": 42.99,
    "wet": 46.99,
    "dry": 50.11,
    "above": 53.55,
    "lines2": 56.75,
    "path2": 58.83
   }
  },
  {
   "id": "m_poly",
   "chapter": "",
   "start": 228.94,
   "dur": 19.58,
   "pre": 0.35,
   "post": 0.35,
   "audio": 18.88,
   "cues": {
    "poly": 0.35,
    "trough": 3.67,
    "tilt": 9.47,
    "circ": 11.23,
    "tan": 15.95
   }
  },
  {
   "id": "m_why",
   "chapter": "",
   "start": 248.52,
   "dur": 50.22,
   "pre": 0.35,
   "post": 0.35,
   "audio": 49.52,
   "cues": {
    "why": 0.35,
    "reach": 3.55,
    "first": 8.323,
    "each": 14.75,
    "order": 18.43,
    "inf": 25.39,
    "pin": 31.177,
    "test": 39.55,
    "hess": 46.11
   }
  },
  {
   "id": "m_end",
   "chapter": "",
   "start": 298.74,
   "dur": 6.43,
   "pre": 0.35,
   "post": 3,
   "audio": 3.08,
   "cues": {
    "end": 0.35
   }
  }
 ],
 "total": 305.17
};

// ==== src/scenes/film.js ====
(function (addEventListener) {
// "A paradoxical local minimum": a point that is a strict minimum along every straight line through it and is not
// a local minimum. Three scenes: the question with the obvious argument and its answer (m_hook); a half-pipe bent
// into a ring, then bent gently down, seen as a solid in three dimensions, until the camera rises to look straight
// down and the hook's picture comes back on it, which then stays beside the polynomial that the surface is and
// becomes the map of what went wrong (m_pipe, m_bend, m_poly, m_why: one scene, so that the picture stays); the end
// card (m_end). Everything on the surface and on the map is computed from f, never drawn by hand.
// Every frame is a function of time: what moves is recomputed in a per-frame update from the scene's clock.
'use strict';
(function () {
  const { W, H, C, E, scene } = Film;
  const LS = 0.16;   // the labels' letter spacing, in em

  // ---- the mathematics ----------------------------------------------------------------------------------
  // the surface, with the bend k: k = 0 is the pipe, k = 1 is the film's polynomial f
  const F = (x, y, k = 1) => 2 * (x * x + y * y - 1) ** 2 - k * y ** 4;
  // the facts the storyboard states, checked (a failure is printed by shot.mjs)
  for (const t of [0.3, 1.1, 2.0, 4.0]) console.assert(Math.abs(F(Math.cos(t), Math.sin(t)) + Math.sin(t) ** 4) < 1e-12, 'f on the circle');
  for (const t of [-0.7, 0.2, 1.5]) console.assert(Math.abs(F(1, t) - t ** 4) < 1e-12, 'f on the tangent');
  // the first s > 0 at which p + s·u enters the region f < 0 (sampled, then bisected); Infinity if it does not
  function entry(ux, uy, k = 1, smax = 4) {
    const step = 0.002;
    for (let s = step; s < smax; s += step) {
      if (F(1 + s * ux, s * uy, k) < 0) {
        let a = s - step, b = s;
        for (let i = 0; i < 30; i++) { const m = (a + b) / 2; if (F(1 + m * ux, m * uy, k) < 0) b = m; else a = m; }
        return b;
      }
    }
    return Infinity;
  }
  const dir = deg => [Math.cos(deg * Math.PI / 180), Math.sin(deg * Math.PI / 180)];
  const ramp = (t, a, d, ease = E.out5) => ease(clamp((t - a) / d));
  // water's colour for text: the water's cyan, a little toward the ink, so that it reads
  const WTEXT = (() => { const a = parseColor(C.bind), b = parseColor(C.ink); return `rgb(${[0, 1, 2].map(i => Math.round(lerp(a[i], b[i], 0.3))).join(',')})`; })();

  // ---- drawing helpers ----------------------------------------------------------------------------------
  const SVGNS = 'http://www.w3.org/2000/svg';
  function sv(parent, tag, attrs = {}, style = {}) {
    const e = document.createElementNS(SVGNS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    Object.assign(e.style, style);
    parent.appendChild(e);
    return e;
  }
  // a stroked path whose geometry is set per frame
  const stroke = (parent, color, width, extra = {}) => sv(parent, 'path', Object.assign({ fill: 'none', stroke: color, 'stroke-width': width, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' }, extra));
  const poly = pts => pts.length ? 'M ' + pts.map(p => p[0].toFixed(2) + ' ' + p[1].toFixed(2)).join(' L ') : '';
  // a dot: a zero-length path with round caps, so that its size is the stroke width
  const dotD = (x, y) => `M ${x.toFixed(2)} ${y.toFixed(2)} L ${x.toFixed(2)} ${y.toFixed(2)}`;
  // the scene's clock: fn(t) runs on every frame with the scene's time
  function clock(tl, root, dur, fn) {
    const h = box(root, 0, 0, {});
    tl.custom(h, 'clk', (e, v) => fn(v), 0);
    tl.fromTo(h, { clk: 0 }, { clk: dur }, 0, dur, E.lin);
  }
  const show = (tl, e, at, dur = 0.5) => { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, at, dur, E.out); return e; };

  // ---- type helpers -------------------------------------------------------------------------------------
  function div(parent, style = {}, text) {
    const e = document.createElement('div');
    Object.assign(e.style, { position: 'relative' }, style);
    if (text !== undefined) { e.textContent = text; e._text0 = text; e._shown = text; }
    parent.appendChild(e);
    return e;
  }
  const SERIF = size => ({ fontFamily: 'var(--serif)', fontSize: size + 'px', lineHeight: 1.22, color: C.ink, whiteSpace: 'pre', letterSpacing: '-0.005em' });
  const LABEL = size => ({ fontFamily: 'var(--sans)', fontSize: size + 'px', fontWeight: 560, letterSpacing: LS + 'em', textTransform: 'uppercase', color: C.dim, whiteSpace: 'pre' });
  // parts: strings (ink), or [text, colour, extra style]
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
  const IT = { fontStyle: 'italic' };
  const it = (t, col = null) => [t, col, IT];
  // inside an upper-case label, a mathematical letter stays itself: lower case, italic serif
  const ML = (t, col = null) => [t, col, { textTransform: 'none', fontFamily: 'var(--serif)', fontStyle: 'italic', letterSpacing: '0', fontWeight: 400, fontSize: '1.2em' }];
  const rich = (parent, parts, size, style = {}) => spans(div(parent, Object.assign(SERIF(size), style)), parts);
  const flabel = (parent, parts, size = 34, style = {}) => spans(div(parent, Object.assign(LABEL(size), style)), parts);
  function crow(root, y, gap = 40, style = {}) {
    return box(root, 0, y, Object.assign({ width: W + 'px', display: 'flex', justifyContent: 'center', alignItems: 'center', columnGap: gap + 'px' }, style));
  }
  // a centred label (the padding makes up for the letter spacing after its last letter)
  function clab(root, y, parts, size = 34, style = {}) {
    return spans(box(root, 0, y, Object.assign(LABEL(size), { width: W + 'px', textAlign: 'center', paddingLeft: LS + 'em' }, style)), parts);
  }
  function cser(root, y, parts, size, style = {}) {
    return spans(box(root, 0, y, Object.assign(SERIF(size), { width: W + 'px', textAlign: 'center' }, style)), parts);
  }
  // a label that comes at `at` and goes at `out`
  function slot(tl, e, at, out) { fadeIn(tl, e, at, 0.5, 10); if (out != null) fadeOut(tl, e, out, 0.3, -8); return e; }
  // a tick or a cross, drawn in a small svg of its own that sits in a row of text
  function mark(tl, parent, size, ok, at) {
    const s = el(parent, 'svg');
    s.setAttribute('width', size * 1.3); s.setAttribute('height', size * 1.3);
    Object.assign(s.style, { position: 'relative', overflow: 'visible', flex: 'none' });
    const c = size * 0.65;
    const ps = ok ? [tick(tl, s, c, c, size, C.good, size / 8)] : cross(tl, s, c, c, size * 0.9, C.bad, size / 8);
    ps.forEach((p, i) => tl.to(p, { draw: 1 }, at + i * 0.12, 0.35, E.out));
    return s;
  }
  // a chevron pointing along angle a (radians, screen), its tip at (x, y)
  const chevron = (x, y, a, h) => {
    const c = Math.cos(a), s = Math.sin(a), bx = x - c * h, by = y - s * h, nx = -s * h * 0.6, ny = c * h * 0.6;
    return `M ${(bx + nx).toFixed(2)} ${(by + ny).toFixed(2)} L ${x.toFixed(2)} ${y.toFixed(2)} L ${(bx - nx).toFixed(2)} ${(by - ny).toFixed(2)}`;
  };

  const segD2 = (a, b) => `M ${a[0].toFixed(2)} ${a[1].toFixed(2)} L ${b[0].toFixed(2)} ${b[1].toFixed(2)}`;

  // ============================================ the surface ====================================================
  // A solid gutter: z = 2(r² − 1)² − k·y⁴ over the ring 0.64 ≤ r ≤ 1.26 (both rims about 0.70 high), with k from 0
  // to 0.3: every claim holds for 0 < k < 2 (on the circle −k·sin⁴ t, on the tangent (2 − k)·t⁴), and with a small
  // k the walls stay walls all the way round. Before that, a straight half-pipe bends into the ring: the mesh is
  // parametrized by (s, u), s the length along the bottom line from p and u the offset across it; the bottom line is
  // an arc of curvature κ through p, tangent there, so κ = 0 is a straight channel along y and κ = 1 the unit circle,
  // where (s, u) is (θ, r − 1) and the mesh is the ring's. The surface is drawn on a canvas as shaded quads, back to
  // front, seen in perspective from the +x side (p at the front); curves on it are drawn over it in the same
  // projection, faint where nearer surface hides them (tested against a coarse depth buffer of the quads).
  const R0 = 0.64, R1 = 1.26, KMAX = 0.3;
  const ZS = 0.55;   // heights drawn at 0.55 of the horizontal scale: so the bottom at p shows over the near wall
  // the camera: 4.5 units away, 50 degrees up, looking at the ring's centre from +x (so right on screen is +y); for
  // the straight pipe it stands 35 degrees round toward +y and looks at the pipe's middle, so that one sees into the
  // channel and its open end, and it swings to the ring's view as the pipe bends
  const ELEV = 50 * Math.PI / 180, DIST = 4.5, TZ = 0.1, AZ0 = 35 * Math.PI / 180;
  // At "Seen from above" the camera rises (RISE from 0 to 1, eased): up to looking straight down, toward p, and
  // away to GROW times its distance, so that at the top the view is orthographic in all but name (the ground plane
  // is square to the view, so a ground point's depth is the distance exactly)
  const GROW = 60;
  const NS = 96, NI = 12, NO = 8, NU = NI + NO;   // 96 around; across, 12 steps inside the bottom line and 8 outside
  const UU = []; for (let i = 0; i <= NU; i++) UU.push(i <= NI ? lerp(R0 - 1, 0, i / NI) : lerp(0, R1 - 1, (i - NI) / NO));
  const H0 = u => 2 * ((1 + u) ** 2 - 1) ** 2;   // the cross-section
  // a point of the mesh, with the bottom line bent to curvature kap, and the bend k (only used at kap = 1)
  function meshPoint(s, u, kap, k, out) {
    if (kap < 1e-6) { out[0] = 1 + u; out[1] = s; }
    else { const c = Math.cos(kap * s), sn = Math.sin(kap * s); out[0] = 1 + (c - 1) / kap + u * c; out[1] = sn / kap + u * sn; }
    out[2] = H0(u) - k * ((1 + u) * Math.sin(s)) ** 4;
  }
  // the light: from the upper left, in front; the paper's tones, darker low, lighter high, and the shell's outside
  const LV = (() => { const l = [0.45, -0.6, 0.75], n = Math.hypot(...l); return l.map(x => x / n); })();
  const LOW = [190, 171, 141], HIGH = [250, 245, 235], OUT = [222, 209, 187];
  const BRAD = 0.06;   // the ball
  // the ring's mesh (the half-pipe bent to curvature kap, with the bend k) as a grid for solid()
  const ringMesh = (kap, k) => (j, i, out) => meshPoint(-Math.PI + 2 * Math.PI * j / NS, UU[i], kap, k, out);

  // ---- the solid-surface renderer, shared by the scenes ----------------------------------------------------
  // A grid of nj × ni quads whose vertices come from pointAt(j, i, out) (world x, y and an unscaled height z; heights
  // are drawn at zs of the horizontal scale), seen by a perspective camera (look), drawn on its own canvas as shaded
  // quads back to front (render, with the view V: screen = V.c + V.s · (camera x, −y) / depth). Curves on it are
  // drawn in the same projection, faint where nearer surface hides them, tested against a coarse depth buffer of the
  // quads (setCurve, with curves made by lifted()).
  function solid(parent, { nj, ni, pointAt, zs = ZS, edges = true, shadow = true, height = hz => clamp((hz + 0.15) / 0.8) }) {
    // height(z, x, y): where a quad's colour lies between the low and the high tone (below 0 is darker still)
    const R = { nj, ni, pointAt, V: { s: 1, cx: 0, cy: 0 } };
    let EYE = [0, 0, 1], FWD = [0, 0, -1], UPV = [-1, 0, 0], RGT = [0, 1, 0];
    // the camera looking at tg (z scaled) from elevation el and azimuth az (radians; az = 0 is from +x), d away
    R.look = (tg, el, az, d) => {
      const ce = Math.cos(el), se = Math.sin(el), ca = Math.cos(az), sa = Math.sin(az);
      EYE = [tg[0] + d * ce * ca, tg[1] + d * ce * sa, tg[2] + d * se];
      FWD = [-ce * ca, -ce * sa, -se]; UPV = [-se * ca, -se * sa, ce]; RGT = [-sa, ca, 0];
      R.eye = EYE;
    };
    // a world point (z already scaled) in the camera's frame: [right, up, depth]
    const camOf = R.camOf = (x, y, z) => { const dx = x - EYE[0], dy = y - EYE[1], dz = z - EYE[2]; return [dx * RGT[0] + dy * RGT[1], dx * UPV[0] + dy * UPV[1] + dz * UPV[2], dx * FWD[0] + dy * FWD[1] + dz * FWD[2]]; };
    const NV = (nj + 1) * (ni + 1), NQ = nj * ni, VI = R.VI = (j, i) => j * (ni + 1) + i;
    const WX = new Float64Array(NV), WY = new Float64Array(NV), WZ = new Float64Array(NV), HZ = new Float64Array(NV);
    const QX = new Float64Array(NV), QY = new Float64Array(NV), SX = R.SX = new Float64Array(NV), SY = R.SY = new Float64Array(NV), SD = new Float64Array(NV);
    const pt = [0, 0, 0];
    // world positions and normalized screen positions (x/d, −y/d); returns their bounding box
    R.place = () => {
      const b = { x0: 1e9, x1: -1e9, y0: 1e9, y1: -1e9 };
      for (let j = 0; j <= nj; j++) for (let i = 0; i <= ni; i++) {
        const v = VI(j, i);
        R.pointAt(j, i, pt);
        WX[v] = pt[0]; WY[v] = pt[1]; HZ[v] = pt[2]; WZ[v] = pt[2] * zs;
        const c = camOf(pt[0], pt[1], WZ[v]);
        QX[v] = c[0] / c[2]; QY[v] = -c[1] / c[2]; SD[v] = c[2];
        if (QX[v] < b.x0) b.x0 = QX[v]; if (QX[v] > b.x1) b.x1 = QX[v]; if (QY[v] < b.y0) b.y0 = QY[v]; if (QY[v] > b.y1) b.y1 = QY[v];
      }
      return b;
    };
    // a point on the surface (or near it; z unscaled) on screen: [x, y, depth]
    R.scr = (x, y, z) => { const c = camOf(x, y, z * zs), V = R.V; return [V.cx + V.s * c[0] / c[2], V.cy - V.s * c[1] / c[2], c[2]]; };
    const DPR = window.devicePixelRatio || 1;
    const cv = R.cv = el(parent, 'canvas', { left: '0px', top: '0px', width: W + 'px', height: H + 'px' });
    cv.width = Math.round(W * DPR); cv.height = Math.round(H * DPR);
    const ctx = cv.getContext('2d');
    const QD = new Float64Array(NQ), QCOL = new Array(NQ), order = R.order = Array.from({ length: NQ }, (_, q) => q);
    const ink = parseColor(C.ink);
    const MESH = `rgba(${ink[0]},${ink[1]},${ink[2]},0.17)`, RIM = `rgba(${ink[0]},${ink[1]},${ink[2]},0.42)`;
    // a coarse depth buffer (4 px cells) of the quads, for the curves drawn over them
    const ZR = 4, ZW = W / ZR, ZH = H / ZR, ZB = new Float32Array(ZW * ZH);
    function zTri(a, b, c) {
      const ax = SX[a] / ZR, ay = SY[a] / ZR, bx = SX[b] / ZR, by = SY[b] / ZR, cx = SX[c] / ZR, cy = SY[c] / ZR;
      const area = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
      if (Math.abs(area) < 1e-9) return;
      const x0 = Math.max(0, Math.floor(Math.min(ax, bx, cx))), x1 = Math.min(ZW - 1, Math.ceil(Math.max(ax, bx, cx)));
      const y0 = Math.max(0, Math.floor(Math.min(ay, by, cy))), y1 = Math.min(ZH - 1, Math.ceil(Math.max(ay, by, cy)));
      const da = SD[a], db = SD[b], dc = SD[c];
      for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) {
        const px = x + 0.5, py = y + 0.5;
        const w0 = ((bx - px) * (cy - py) - (by - py) * (cx - px)) / area, w1 = ((cx - px) * (ay - py) - (cy - py) * (ax - px)) / area, w2 = 1 - w0 - w1;
        if (w0 < -0.02 || w1 < -0.02 || w2 < -0.02) continue;
        const d = w0 * da + w1 * db + w2 * dc, o = y * ZW + x;
        if (d < ZB[o]) ZB[o] = d;
      }
    }
    // the nearest surface's depth around a screen point (the farthest of the four cells around it, so that a curve
    // is hidden only where it is clearly behind)
    function depthAt(x, y) {
      const gx = x / ZR - 0.5, gy = y / ZR - 0.5, x0 = Math.floor(gx), y0 = Math.floor(gy);
      let m = -Infinity;
      for (let dy = 0; dy <= 1; dy++) for (let dx = 0; dx <= 1; dx++) {
        const xx = clamp(x0 + dx, 0, ZW - 1), yy = clamp(y0 + dy, 0, ZH - 1), z = ZB[yy * ZW + xx];
        if (z === Infinity) return Infinity;
        if (z > m) m = z;
      }
      return m;
    }
    R.eps = 0.05;
    R.seen = q => q[2] <= depthAt(q[0], q[1]) + R.eps;
    // draw what place() put, with the view R.V: clipped to clip [x0, y0, x1, y1]; open says the grid's ends (j = 0
    // and nj) are edges (a pipe not yet closed); after() runs once the depth buffer is ready
    R.render = ({ clip = [0, 0, W, H], open = false, after = null } = {}) => {
      const V = R.V;
      for (let v = 0; v < NV; v++) { SX[v] = V.cx + V.s * QX[v]; SY[v] = V.cy + V.s * QY[v]; }
      // the quads: depth, normal, which side faces the camera, colour
      for (let j = 0; j < nj; j++) for (let i = 0; i < ni; i++) {
        const q = j * ni + i, a = VI(j, i), bq = VI(j, i + 1), c = VI(j + 1, i + 1), d = VI(j + 1, i);
        QD[q] = (SD[a] + SD[bq] + SD[c] + SD[d]) / 4;
        const e1x = WX[c] - WX[a], e1y = WY[c] - WY[a], e1z = WZ[c] - WZ[a], e2x = WX[d] - WX[bq], e2y = WY[d] - WY[bq], e2z = WZ[d] - WZ[bq];
        let nx = e1y * e2z - e1z * e2y, ny = e1z * e2x - e1x * e2z, nz = e1x * e2y - e1y * e2x;
        const nl = Math.hypot(nx, ny, nz) || 1, sg = nz < 0 ? -1 : 1;
        nx *= sg / nl; ny *= sg / nl; nz *= sg / nl;
        const mx = (WX[a] + WX[c]) / 2, my = (WY[a] + WY[c]) / 2, mz = (WZ[a] + WZ[c]) / 2;
        const front = nx * (EYE[0] - mx) + ny * (EYE[1] - my) + nz * (EYE[2] - mz) > 0;
        let col;
        if (front) {
          const h = height((HZ[a] + HZ[bq] + HZ[c] + HZ[d]) / 4, mx, my);
          const sh = 0.68 + 0.36 * Math.max(0, nx * LV[0] + ny * LV[1] + nz * LV[2]);
          col = [0, 1, 2].map(z => Math.min(255, lerp(LOW[z], HIGH[z], h) * sh));
        } else {
          const sh = 0.72 + 0.34 * Math.max(0, -(nx * LV[0] + ny * LV[1] + nz * LV[2]));
          col = OUT.map(z => Math.min(255, z * sh));
        }
        QCOL[q] = `rgb(${col[0] | 0},${col[1] | 0},${col[2] | 0})`;
      }
      order.sort((p, q) => QD[q] - QD[p]);
      ctx.restore();
      ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
      ctx.clearRect(0, 0, W, H);
      ctx.save(); ctx.beginPath(); ctx.rect(clip[0], clip[1], clip[2] - clip[0], clip[3] - clip[1]); ctx.clip();
      if (shadow) {
        // the ground shadow: the footprint on the ground below, a little to the back right, its edge softened by
        // strokes of growing width (a canvas blur costs more than everything else); the grid's rows i = 0 and ni
        // are its rims
        const gz = -0.3 * zs, foot = (j, i) => { const v = VI(j, i), c = camOf(WX[v] - 0.08, WY[v] + 0.1, gz); return [V.cx + V.s * c[0] / c[2], V.cy - V.s * c[1] / c[2]]; };
        const outer = [], inner = [];
        for (let j = 0; j <= nj; j += 2) { outer.push(foot(j, ni)); inner.push(foot(j, 0)); }
        const area = new Path2D(), edge = new Path2D();
        outer.forEach((p, n) => n ? area.lineTo(p[0], p[1]) : area.moveTo(p[0], p[1]));
        for (let n = inner.length - 1; n >= 0; n--) area.lineTo(inner[n][0], inner[n][1]);
        area.closePath();
        // the edge: both rims, and across the ends while the pipe is open (closed, the seam is no edge)
        if (open) edge.addPath(area);
        else for (const ring of [outer, inner]) ring.forEach((p, n) => n ? edge.lineTo(p[0], p[1]) : edge.moveTo(p[0], p[1]));
        ctx.save(); ctx.fillStyle = ctx.strokeStyle = C.ink; ctx.lineJoin = 'round';
        ctx.globalAlpha = 0.05; ctx.fill(area);
        for (let w = 56; w > 0; w -= 8) { ctx.globalAlpha = 0.016; ctx.lineWidth = w; ctx.stroke(edge); }
        ctx.restore();
      }
      // the quads
      ctx.lineJoin = 'round';
      for (const q of order) {
        const j = (q / ni) | 0, i = q - j * ni, a = VI(j, i), bq = VI(j, i + 1), c = VI(j + 1, i + 1), d = VI(j + 1, i);
        ctx.beginPath(); ctx.moveTo(SX[a], SY[a]); ctx.lineTo(SX[bq], SY[bq]); ctx.lineTo(SX[c], SY[c]); ctx.lineTo(SX[d], SY[d]); ctx.closePath();
        ctx.fillStyle = QCOL[q]; ctx.fill();
        ctx.strokeStyle = QCOL[q]; ctx.lineWidth = 0.9; ctx.stroke();
        if (!edges) continue;
        // the mesh: every second line across, every third around
        ctx.beginPath();
        if (i % 2 === 0 && i > 0) { ctx.moveTo(SX[a], SY[a]); ctx.lineTo(SX[d], SY[d]); }
        if (j % 3 === 0 && !(open && j === 0)) { ctx.moveTo(SX[a], SY[a]); ctx.lineTo(SX[bq], SY[bq]); }
        ctx.strokeStyle = MESH; ctx.lineWidth = 1.3; ctx.stroke();
        // the rims, and the open ends
        ctx.beginPath();
        if (i === 0) { ctx.moveTo(SX[a], SY[a]); ctx.lineTo(SX[d], SY[d]); }
        if (i === ni - 1) { ctx.moveTo(SX[bq], SY[bq]); ctx.lineTo(SX[c], SY[c]); }
        if (open && j === 0) { ctx.moveTo(SX[a], SY[a]); ctx.lineTo(SX[bq], SY[bq]); }
        if (open && j === nj - 1) { ctx.moveTo(SX[d], SY[d]); ctx.lineTo(SX[c], SY[c]); }
        ctx.strokeStyle = RIM; ctx.lineWidth = 2; ctx.stroke();
      }
      // the depth buffer
      ZB.fill(Infinity);
      for (let j = 0; j < nj; j++) for (let i = 0; i < ni; i++) {
        const a = VI(j, i), bq = VI(j, i + 1), c = VI(j + 1, i + 1), d = VI(j + 1, i);
        zTri(a, bq, c); zTri(a, c, d);
      }
      if (after) after();
    };
    // set a curve made by lifted() from points [x, y, z] (z unscaled), or clear it: hidden, plain, and (wet(p)) wet
    // parts; a piece between two kinds of point goes in both
    R.setCurve = (c, pts, wet = null) => {
      const d = ['', '', ''];
      let prev = null, pv = -1;
      for (const p of pts || []) {
        const q = R.scr(p[0], p[1], p[2]), v = !R.seen(q) ? 0 : wet && wet(p) ? 2 : 1, xy = q[0].toFixed(1) + ' ' + q[1].toFixed(1);
        if (prev === null) d[v] += 'M ' + xy;
        else if (v === pv) d[v] += ' L ' + xy;
        else { d[pv] += ' L ' + xy; d[v] += ' M ' + prev + ' L ' + xy; }
        prev = xy; pv = v;
      }
      c.hid.setAttribute('d', d[0]); c.vis.setAttribute('d', d[1]); c.wet.setAttribute('d', d[2]);
    };
    return R;
  }
  // a curve over a solid: its visible parts, faintly the parts behind nearer surface, and half strength the parts
  // under water
  function lifted(parent, color, width, extra = {}) {
    const g = sv(parent, 'g');
    return { g, hid: stroke(g, color, width, Object.assign({ 'stroke-opacity': 0.14 }, extra)), wet: stroke(g, color, width, Object.assign({ 'stroke-opacity': 0.42 }, extra)), vis: stroke(g, color, width, extra) };
  }

  // ============================================ m_holes, m_area ================================================
  // The first counterexample: the bowl z = x² + y² with single points P_n (at distance 1/n from the bottom O, at
  // angle n radians) pushed down below the bottom. Every line through O meets at most one P_n (two on one line would
  // need n − m to be a multiple of π), so from O every line goes up; but the P_n come arbitrarily close. Then the
  // holes get width (a disc around P_n of radius sin(HW)/n, so that from O each blocks a double wedge of directions of
  // half-width HW): the wedges, at angles n mod π, fill the circle of directions, and the line at angle THR passes
  // through holes 1, 4, 23, 26, 45, 48, 67, 70, 92, … (22 is close to 7π). First a solid bowl in three dimensions;
  // at "The first at distance one" the camera rises to straight down, and the rest is a flat top view (the bowl a
  // shaded disc with rings of equal height), with O at (OX, OY) and S·Z px per unit (Z, the zoom, from 1).
  const HW = 0.13, THR = 0.9, NH = 1500;
  const angDist = (a, b) => { let x = (a - b) % Math.PI; if (x < 0) x += Math.PI; return Math.min(x, Math.PI - x); };
  console.assert([1, 4, 23, 26, 45, 48].every(n => angDist(n, THR) < HW) && [2, 3, 5, 22, 24].every(n => angDist(n, THR) > HW), 'the threaded line');
  function holesPart({ tl, root, cue, seg, dur }) {
    const hs = seg('m_holes'), as = seg('m_area');
    const tBowl = cue('bowl'), tMin = cue('min'), tHoles = cue('holes'), tSpiral = cue('spiral'), tLine = cue('line'), tOne = cue('one'), tUp = cue('up'), tClose = cue('close');
    const tCheat = cue('cheat'), tWide = cue('wide'), tWedge = cue('wedge'), tSweep = cue('sweep'), tThrough = cue('through'), tFail = cue('fail'), tSo = cue('so');
    const layer = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    tl.set(layer, { o: 0 }, 0); tl.to(layer, { o: 1 }, tBowl - 0.15, 0.6, E.out); tl.to(layer, { o: 0 }, tSo - 0.1, 0.5, E.in);
    const live = t => t > tBowl - 0.3 && t < tSo + 0.5;
    const OX = 960, OY = 455, S = 400, RBW = 1.1;

    // ---- the solid bowl ----
    const BZS = 0.55, NA = 120, NRB = 30;
    const b3 = box(layer, 0, 0, { width: W + 'px', height: H + 'px' });
    const BW = solid(b3, { nj: NA, ni: NRB, edges: false, zs: BZS, height: hz => clamp(hz / 1.45),
      pointAt: (j, i, out) => { const a = 2 * Math.PI * j / NA, r = RBW * i / NRB; out[0] = r * Math.cos(a); out[1] = r * Math.sin(a); out[2] = r * r; } });
    const s3 = svgLayer(b3);
    // the camera from −y (so that, from straight above, x is right and y is up), 48 degrees up; the bowl fitted into
    // x = 110..1450, y = 70..880 (the top right is the cross-section's)
    const EL3 = 48 * Math.PI / 180, AZ3 = -Math.PI / 2, D3 = 4.2;
    BW.look([0, 0, 0], EL3, AZ3, D3);
    const bb = BW.place(), fs = Math.min(1340 / (bb.x1 - bb.x0), 800 / (bb.y1 - bb.y0));
    const V0 = { s: fs, cx: 780 - fs * (bb.x0 + bb.x1) / 2, cy: 478 - fs * (bb.y0 + bb.y1) / 2 }, PPU0 = fs / D3;
    const camAt = r => {
      const d = D3 * GROW ** (r * r);
      BW.look([0, 0, 0], lerp(EL3, Math.PI / 2, r), AZ3, d);
      BW.V = { s: PPU0 ** (1 - r) * S ** r * d, cx: lerp(V0.cx, OX, r), cy: lerp(V0.cy, OY, r) };
    };
    const tRise = hs + 11.95, tTop = tRise + 1.45;
    const riseOf = t => ramp(t, tRise, tTop - tRise, E.io);
    // rings of equal height, and the rim
    const rings3 = [0.25, 0.5, 0.75, 1, RBW].map(r => ({ r, e: lifted(s3, C.ink, r === RBW ? 2.5 : 2, { 'stroke-opacity': r === RBW ? 0.5 : 0.28 }) }));
    const ringPts = r => { const pts = []; for (let n = 0; n <= 180; n++) { const a = 2 * Math.PI * n / 180; pts.push([r * Math.cos(a), r * Math.sin(a), r * r]); } return pts; };
    // "Its bottom is as good a minimum as you could ask for.": O, and green arrows climbing from it
    const arr3 = sv(s3, 'g'), o3 = sv(s3, 'circle', { r: 13, fill: C.pat });
    // the first pinhole: its stem down to below the bottom (faint where the bowl hides it), the hole it leaves
    const P1 = [Math.cos(1), Math.sin(1)], ZLOW = -0.3;
    const stemG = sv(s3, 'g'), stem = lifted(stemG, C.bad, 3.5);
    stem.hid.setAttribute('stroke-opacity', 0.5); stem.hid.setAttribute('stroke-dasharray', '2 7');
    const stemEnd = sv(stemG, 'circle', { r: 9, fill: C.bad });
    const hole3 = sv(s3, 'circle', { r: 7, fill: C.ink });
    const tDrop = hs + 8.5;
    let drawn = '';
    const draw3 = (r, t) => {
      const key = r.toFixed(5);
      if (key !== drawn) {
        drawn = key;
        camAt(r); BW.place(); BW.render();
        for (const g of rings3) BW.setCurve(g.e, ringPts(g.r));
        if (r === 0 && !arr3.firstChild) {
          // drawn once, for the still camera
          for (let k = 0; k < 6; k++) {
            const a = (k * 60 + 20) * Math.PI / 180, pts = [];
            for (let n = 0; n <= 50; n++) { const s = lerp(0.08, 0.8, n / 50); pts.push([s * Math.cos(a), s * Math.sin(a), s * s]); }
            BW.setCurve(lifted(arr3, C.good, 4.5), pts);
            const qa = BW.scr(...pts[48]), qb = BW.scr(...pts[50]), an = Math.atan2(qb[1] - qa[1], qb[0] - qa[0]);
            stroke(arr3, C.good, 4.5, { d: chevron(qb[0] + 3 * Math.cos(an), qb[1] + 3 * Math.sin(an), an, 20) });
          }
        }
        const o = BW.scr(0, 0, 0); o3.setAttribute('cx', o[0].toFixed(2)); o3.setAttribute('cy', o[1].toFixed(2));
        const h = BW.scr(P1[0], P1[1], 1); hole3.setAttribute('cx', h[0].toFixed(2)); hole3.setAttribute('cy', h[1].toFixed(2));
      }
      // the stem grows down from the surface, then goes
      const g = ramp(t, tDrop, 1.1, E.io);
      if (g > 0.001 && r === 0) {
        const z1 = lerp(1, ZLOW, g), pts = [];
        for (let n = 0; n <= 30; n++) pts.push([P1[0], P1[1], lerp(1, z1, n / 30)]);
        BW.setCurve(stem, pts);
        const q = BW.scr(P1[0], P1[1], z1); stemEnd.setAttribute('cx', q[0].toFixed(2)); stemEnd.setAttribute('cy', q[1].toFixed(2));
        stemEnd.setAttribute('fill-opacity', BW.seen(q) ? 1 : 0.55);
      } else { BW.setCurve(stem, null); stemEnd.setAttribute('cx', -99); }
    };
    tl.set(arr3, { o: 0 }, 0); tl.to(arr3, { o: 1 }, hs + 5.6, 0.6); tl.to(arr3, { o: 0 }, tHoles - 0.1, 0.5);
    tl.set(o3, { o: 0 }, 0); tl.to(o3, { o: 1 }, tMin + 0.1, 0.4);
    tl.set(hole3, { o: 0 }, 0); tl.to(hole3, { o: 1 }, tDrop + 0.1, 0.3);
    tl.set(stemG, { o: 1 }, 0); tl.to(stemG, { o: 0 }, tRise - 0.1, 0.4);
    // from above, the solid gives way to the flat top view
    tl.set(b3, { o: 1 }, 0); tl.to(b3, { o: 0 }, tTop, 0.5, E.io);

    // a cross-section beside it: a parabola, one point of it pushed down below the bottom's height
    {
      const IX = 1662, IB = 336, SX = 170, SZ = 170;   // the bottom, and px per unit across and up
      const cx = box(layer, 1450, 74, { width: '424px', height: '400px', borderRadius: '18px', background: alpha(C.panel, 0.85), boxShadow: `inset 0 0 0 1.5px ${C.line}` });
      const cs = svgLayer(layer), g = sv(cs, 'g');
      const at = x => [IX + SX * x, IB - SZ * x * x];
      const pts = []; for (let n = 0; n <= 80; n++) pts.push(at(lerp(-1.05, 1.05, n / 80)));
      stroke(g, C.dim, 2, { d: `M ${IX - 190} ${IB} L ${IX + 190} ${IB}`, 'stroke-dasharray': '8 8' });
      stroke(g, C.ink, 4, { d: poly(pts) });
      sv(g, 'circle', { cx: IX, cy: IB, r: 9, fill: C.pat });
      const xp = 0.68, q = at(xp), low = [q[0], IB + 40];
      sv(g, 'circle', { cx: q[0], cy: q[1], r: 8, fill: C.panel, stroke: C.ink, 'stroke-width': 3 });
      stroke(g, C.bad, 2.5, { d: `M ${q[0]} ${q[1] + 11} L ${low[0]} ${low[1] - 12}`, 'stroke-dasharray': '3 6' });
      stroke(g, C.bad, 2.5, { d: chevron(low[0], low[1] - 12, Math.PI / 2, 10) });
      sv(g, 'circle', { cx: low[0], cy: low[1], r: 9, fill: C.bad });
      const lb = box(layer, 1450, IB + 72, Object.assign(LABEL(26), { width: '424px', textAlign: 'center', color: C.bad, paddingLeft: LS + 'em' }), 'below the bottom');
      for (const e of [cx, cs, lb]) { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, tDrop + 0.4, 0.5); tl.to(e, { o: 0 }, tRise - 0.3, 0.4); }
    }

    // ---- the top view ----
    const tv = box(layer, 0, 0, { width: W + 'px', height: H + 'px' });
    tl.set(tv, { o: 0 }, 0); tl.to(tv, { o: 1 }, tTop - 0.05, 0.5, E.io);
    const bsvg = svgLayer(tv);
    // the bowl's shading from above (its tones by height, as the solid has them)
    const grd = sv(sv(bsvg, 'defs'), 'radialGradient', { id: 'm-bowl-top', gradientUnits: 'userSpaceOnUse', cx: OX, cy: OY, r: 100 });
    for (let k = 0; k <= 8; k++) {
      const r = RBW * k / 8, h = clamp(r * r / 1.45), c = [0, 1, 2].map(i => Math.round(lerp(LOW[i], HIGH[i], h) * 0.93));
      sv(grd, 'stop', { offset: k / 8, 'stop-color': `rgb(${c.join(',')})` });
    }
    const disc = sv(bsvg, 'circle', { cx: OX, cy: OY, fill: 'url(#m-bowl-top)' });
    const ringsT = [0.25, 0.5, 0.75, 1, RBW].map(r => ({ r, e: sv(bsvg, 'circle', { cx: OX, cy: OY, fill: 'none', stroke: C.ink, 'stroke-width': r === RBW ? 2.5 : 2, 'stroke-opacity': r === RBW ? 0.5 : 0.22 }) }));
    const DPR = window.devicePixelRatio || 1;
    const hcv = el(tv, 'canvas', { left: '0px', top: '0px', width: W + 'px', height: H + 'px' });
    hcv.width = Math.round(W * DPR); hcv.height = Math.round(H * DPR);
    const hc = hcv.getContext('2d');
    const osvg = svgLayer(tv);

    // the clock's pieces: the zoom; how many holes show; their width; how many wedges
    const lZ1 = Math.log(12), lZ3 = Math.log(24);
    const zOf = t => Math.exp(lZ1 * (ramp(t, tClose + 0.35, 3.6, E.io) - ramp(t, tCheat - 0.25, 1.5, E.io)) + lZ3 * ramp(t, as + 20.4, 4.8, E.io));
    // P1 from the top, P2 at "a half", P3 at "a third", then P4 … P40 at "And so on, spiralling in", then all
    const countOf = t => t < tTop ? 0 : t < hs + 17.0 ? 1 : t < hs + 20.9 ? 2 : t < hs + 23.15 ? 3 : t < hs + 24.9 ? 3 + 37 * ramp(t, hs + 23.15, 1.75, E.lin) : NH;
    const widthOf = t => ramp(t, as + 6.6, 1.3, E.io);
    // the wedges: hole 1 at "blocks", 2 and 3 after it, then 4 … 30 at "The wedges keep coming"
    const WT = [0, as + 10.4, as + 12.3, as + 13.0];
    for (let n = 4; n <= 30; n++) WT.push(as + 15.0 + (n - 4) * 0.1);
    const threadOf = t => ramp(t, as + 19.2, 0.6, E.io);
    const pos = (n, Z) => [OX + S * Z * Math.cos(n) / n, OY - S * Z * Math.sin(n) / n];
    const THREADED = new Uint8Array(NH + 1); for (let n = 1; n <= NH; n++) THREADED[n] = angDist(n, THR) < HW ? 1 : 0;
    const ink = parseColor(C.ink), bad = parseColor(C.bad);
    const drawHoles = t => {
      hc.setTransform(DPR, 0, 0, DPR, 0, 0); hc.clearRect(0, 0, W, H);
      const Z = zOf(t), cnt = countOf(t), wd = widthOf(t), th = threadOf(t);
      // the wedges, each a double sector out to past the rim
      const RW = RBW * S * Z, wa = 1 - 0.7 * th;
      const sector = (n, rad) => {
        for (const c of [n, n + Math.PI]) { hc.moveTo(OX, OY); hc.arc(OX, OY, rad, -(c + HW), -(c - HW)); hc.closePath(); }
      };
      hc.beginPath();
      let young = [];
      for (let n = 1; n < WT.length; n++) {
        const age = t - WT[n];
        if (age < 0) break;
        if (age < 0.7) young.push([n, age]); else sector(n, RW);
      }
      hc.fillStyle = `rgba(${bad[0]},${bad[1]},${bad[2]},${(0.16 * wa).toFixed(3)})`; hc.fill();
      for (const [n, age] of young) {
        hc.beginPath(); sector(n, RW * E.out(clamp(age / 0.35)));
        hc.fillStyle = `rgba(${bad[0]},${bad[1]},${bad[2]},${((0.16 + 0.22 * (1 - age / 0.7)) * wa).toFixed(3)})`; hc.fill();
      }
      // the faint spiral through the holes, r = 1/θ, out of P1 and in as far as the holes have come
      const sa = cnt >= 3.5 ? (t < tLine ? 0.4 : 0.2) * (1 - 0.6 * wd) : 0;
      if (sa > 0.01) {
        hc.beginPath();
        const tEnd = Math.min(cnt, S * Z / 1.5);
        for (let a = 1; a <= tEnd;) {
          const R = S * Z / a, x = OX + R * Math.cos(a), y = OY - R * Math.sin(a);
          a === 1 ? hc.moveTo(x, y) : hc.lineTo(x, y);
          a = Math.min(tEnd, a + Math.min(0.06, 5 / R)) === a ? tEnd + 1 : Math.min(tEnd, a + Math.min(0.06, 5 / R));
        }
        hc.strokeStyle = `rgba(${ink[0]},${ink[1]},${ink[2]},${sa.toFixed(3)})`; hc.lineWidth = 2; hc.stroke();
      }
      // the holes: dark points, discs once they have width; red (and the others fainter) on the threaded line
      const n1 = Math.min(NH, Math.ceil(cnt));
      const paths = [new Path2D(), new Path2D()];
      for (let n = 1; n <= n1; n++) {
        const [x, y] = pos(n, Z), R = S * Z / n;
        if (x < -80 || x > W + 80 || y < -80 || y > H + 80) continue;
        const dot = clamp(0.2 * R, 1.0, 6.5), rad = Math.max(dot, wd * R * Math.sin(HW));
        // the newest point grows in
        const gr = n === n1 && cnt < 40 ? clamp((cnt - n + 1) * 1.5) : 1;
        const pth = paths[th > 0 && THREADED[n] ? 1 : 0];
        pth.moveTo(x + rad * gr, y); pth.arc(x, y, rad * gr, 0, 2 * Math.PI);
      }
      // a hole whose wedge is coming is red
      const hot = new Path2D();
      for (const [n, age] of young) { const [x, y] = pos(n, Z), rad = Math.max(clamp(0.2 * S * Z / n, 1, 6.5), wd * S * Z / n * Math.sin(HW)); hot.moveTo(x + rad, y); hot.arc(x, y, rad, 0, 2 * Math.PI); }
      hc.fillStyle = `rgba(${ink[0]},${ink[1]},${ink[2]},${(0.85 * (1 - 0.55 * th)).toFixed(3)})`; hc.fill(paths[0]);
      hc.fillStyle = `rgba(${ink[0]},${ink[1]},${ink[2]},0.85)`; hc.fill(paths[1]);
      hc.fillStyle = `rgba(${bad[0]},${bad[1]},${bad[2]},${th.toFixed(3)})`; hc.fill(paths[1]);
      hc.fillStyle = C.bad; hc.fill(hot);
    };

    // ---- what is drawn over the top view ----
    const scrT = (x, y, Z) => [OX + S * Z * x, OY - S * Z * y];
    // the reference direction, and for P1, P2, P3 a radius from O with its length, and an arc with its angle
    const ref = stroke(osvg, C.ink, 2, { 'stroke-dasharray': '6 8', 'stroke-opacity': 0.55, d: segD2([OX, OY], [OX + S * RBW, OY]) });
    tl.set(ref, { o: 0 }, 0); tl.to(ref, { o: 1 }, hs + 13.7, 0.5); tl.to(ref, { o: 0 }, hs + 23.2, 0.6);
    const RADS = [
      { n: 1, at: hs + 13.15, arcAt: hs + 13.95, rho: 0.34, d: '1', a: '1 rad' },
      { n: 2, at: hs + 16.95, arcAt: hs + 17.9, rho: 0.25, d: '½', a: '2 rad' },
      { n: 3, at: hs + 20.85, arcAt: hs + 21.65, rho: 0.17, d: '⅓', a: '3 rad' }];
    RADS.forEach((R, k) => {
      const g = sv(osvg, 'g'), p = pos(R.n, 1), a = R.n;
      const rl = path(tl, g, segD2([OX, OY], p), { stroke: C.ink, width: 2.5 });
      tl.to(rl, { draw: 1 }, R.at, 0.45, E.io);
      const arcPts = []; for (let i = 0; i <= 60; i++) arcPts.push(scrT(R.rho * Math.cos(a * i / 60), R.rho * Math.sin(a * i / 60), 1));
      const ar = path(tl, g, poly(arcPts), { stroke: C.ink, width: 3 });
      tl.to(ar, { draw: 1 }, R.arcAt, 0.7, E.io);
      const e = arcPts[60], e0 = arcPts[57];
      const ah = stroke(g, C.ink, 3, { d: chevron(e[0], e[1], Math.atan2(e[1] - e0[1], e[0] - e0[0]), 10) });
      tl.set(ah, { o: 0 }, 0); tl.to(ah, { o: 1 }, R.arcAt + 0.6, 0.15);
      // the length beside the radius's middle, on the side away from the arc; the angle by the arc's end
      const mid = [(OX + p[0]) / 2, (OY + p[1]) / 2], nx = -Math.sin(a), ny = -Math.cos(a);
      const dl = box(layer, mid[0] + 30 * nx - 20, mid[1] + 30 * ny - 28, Object.assign(SERIF(42), { width: '40px', textAlign: 'center' }), R.d);
      const la = a / 2, lr = R.rho * S + 44;
      const al = box(layer, OX + lr * Math.cos(la) - 70, OY - lr * Math.sin(la) - 26, Object.assign(SERIF(42), { width: '140px', textAlign: 'center' }), R.a);
      fadeIn(tl, dl, R.at + 0.3, 0.4, 6); fadeIn(tl, al, R.arcAt + 0.5, 0.4, 6);
      // the earlier ones step back when the next comes, and all go as the spiral runs
      if (k < 2) { tl.to(g, { o: 0.3 }, RADS[k + 1].at - 0.1, 0.4); for (const e2 of [dl, al]) tl.to(e2, { o: 0 }, RADS[k + 1].at - 0.1, 0.4); }
      for (const e2 of [g, dl, al]) tl.to(e2, { o: 0 }, hs + 23.2, 0.5);
    });
    // "Now take any straight line through the bottom.": a line through O, turning; it settles on P2
    const LA = t => lerp(2.95, 2, ramp(t, hs + 25.8, 3.0, E.io));
    const lineG = sv(osvg, 'g'), lineE = stroke(lineG, C.ink, 3.5);
    const ringP2 = sv(lineG, 'circle', { r: 17, fill: 'none', stroke: C.bad, 'stroke-width': 3.5 });
    { const p = pos(2, 1); ringP2.setAttribute('cx', p[0]); ringP2.setAttribute('cy', p[1]); }
    tl.set(ringP2, { o: 0 }, 0); tl.to(ringP2, { o: 1 }, hs + 28.9, 0.4);
    // "So near the bottom, the line runs on the untouched bowl, and every step goes up.": green from O out to P2's
    // distance, both ways, with arrowheads leaving O
    const upG = sv(lineG, 'g'), upE = [stroke(upG, C.good, 7), stroke(upG, C.good, 7)], upH = [stroke(upG, C.good, 5), stroke(upG, C.good, 5)];
    const upL = box(layer, 0, 0, Object.assign(LABEL(34), { color: C.good, paddingLeft: LS + 'em' }), 'up');
    { const u = [Math.cos(2), -Math.sin(2)], q = [OX - 0.5 * S * u[0], OY - 0.5 * S * u[1]]; upL.style.left = (q[0] + 26) + 'px'; upL.style.top = (q[1] - 4) + 'px'; }
    fadeIn(tl, upL, hs + 43.9, 0.5, 8);
    tl.set(lineG, { o: 1 }, 0); tl.to(lineG, { o: 0 }, tClose + 0.05, 0.4); fadeOut(tl, upL, tClose + 0.05, 0.3, 0);
    // "n − m = kπ ?" and "π is irrational", in the right column
    const eq = box(layer, 1430, 300, Object.assign(SERIF(64), { width: '450px', textAlign: 'center' }));
    spans(eq, [it('n'), ' − ', it('m'), ' = ', it('k'), 'π ?']);
    const ir = box(layer, 1430, 410, Object.assign(SERIF(54), { width: '450px', textAlign: 'center' }), 'π is irrational');
    const strike = sv(svgLayer(layer), 'path', { d: 'M 1490 342 L 1820 342', stroke: C.bad, 'stroke-width': 4, 'stroke-linecap': 'round' });
    tl.custom(strike, 'draw', (e, v) => e.setAttribute('d', v > 0.001 ? `M 1490 342 L ${(1490 + 330 * v).toFixed(1)} 342` : ''), 0);
    fadeIn(tl, eq, hs + 33.6, 0.6, 10); fadeIn(tl, ir, hs + 37.3, 0.6, 10);
    tl.to(strike, { draw: 1 }, hs + 37.9, 0.5, E.io); tl.to(eq, { o: 0.45 }, hs + 37.9, 0.5);
    for (const e of [eq, ir, strike]) tl.to(e, { o: 0 }, tClose - 0.1, 0.4);
    // the threaded line of m_area: red, through O, out to past the rim
    const thrE = stroke(osvg, C.bad, 4.5);
    const oT = sv(osvg, 'circle', { cx: OX, cy: OY, r: 13, fill: C.pat });
    // the labels, under the picture
    // the labels, under the picture, on a panel (they lie over the holes when zoomed in)
    const lab = (text, color, at, out) => {
      const r = box(layer, 0, 850, { width: W + 'px', display: 'flex', justifyContent: 'center' });
      flabel(r, text, 32, { color, background: alpha(C.panel, 0.88), padding: '8px 22px 8px calc(22px + ' + LS + 'em)', borderRadius: '12px' });
      return slot(tl, r, at, out);
    };
    lab('below the bottom, arbitrarily close', C.bad, hs + 47.7, tCheat - 0.1);
    lab('holes with no width', C.dim, as + 2.2, as + 6.3);
    lab('this line does not go up', C.bad, tFail + 0.25, null);

    clock(tl, root, dur, t => {
      if (!live(t)) return;
      if (t < tTop + 0.6) draw3(riseOf(t), t);
      if (t < tTop - 0.1) return;
      const Z = zOf(t);
      grd.setAttribute('r', (RBW * S * Z).toFixed(2)); disc.setAttribute('r', (RBW * S * Z).toFixed(2));
      for (const g of ringsT) g.e.setAttribute('r', (g.r * S * Z).toFixed(2));
      drawHoles(t);
      // the turning line
      const la = LA(t), lg = ramp(t, tLine - 0.05, 0.6, E.out), Lh = 1.25 * S * lg, u = [Math.cos(la), -Math.sin(la)];
      lineE.setAttribute('d', lg > 0.001 ? segD2([OX - Lh * u[0], OY - Lh * u[1]], [OX + Lh * u[0], OY + Lh * u[1]]) : '');
      const ug = ramp(t, tUp + 0.25, 0.9, E.io), Lu = (0.5 * S - 26) * ug;
      [1, -1].forEach((sg, k) => {
        const e = [OX + sg * Lu * u[0], OY + sg * Lu * u[1]];
        upE[k].setAttribute('d', ug > 0.001 ? segD2([OX, OY], e) : '');
        upH[k].setAttribute('d', ug > 0.15 ? chevron(e[0] + sg * 3 * u[0], e[1] + sg * 3 * u[1], Math.atan2(sg * u[1], sg * u[0]), 18) : '');
      });
      // the threaded line grows out of O both ways
      const tg = ramp(t, as + 19.3, 0.8, E.io), Lt = 1400 * tg, v = [Math.cos(THR), -Math.sin(THR)];
      thrE.setAttribute('d', tg > 0.001 ? segD2([OX - Lt * v[0], OY - Lt * v[1]], [OX + Lt * v[0], OY + Lt * v[1]]) : '');
    });
  }

  // ============================================ m_hook =========================================================
  // The question: a point, every straight line through it going up; the obvious yes; the answer no; something
  // stronger, a curved path going down; what one pictures for that (a bowl with a crevasse), and what it can be (the
  // smooth valley). It opens on the landscape itself, in three dimensions, beside the claim; the camera rises to
  // straight down over p, and the flat fan that the rest of the scene uses is what remains.
  // an element seen only inside the rectangle c = [x0, y0, x1, y1] of the stage, its edges soft over fe px
  function softRect(e, c, fe) {
    const px = v => v.toFixed(1) + 'px';
    e.style.maskImage = `linear-gradient(to right, transparent ${px(c[0])}, #000 ${px(c[0] + fe)}, #000 ${px(c[2] - fe)}, transparent ${px(c[2])}), linear-gradient(to bottom, transparent ${px(c[1])}, #000 ${px(c[1] + fe)}, #000 ${px(c[3] - fe)}, transparent ${px(c[3])})`;
    e.style.maskComposite = 'intersect';
  }
  const ZSH = 0.4;   // the hook's heights (see the opening below)
  scene(['m_hook', 'm_holes', 'm_area', 'm_crev'], ({ tl, root, cue, seg, dur }) => {
    const P = { x: 960, y: 418 }, FR = 300;   // the fan: p on screen, and its lines' half-length
    const PS = 520, LF = FR / PS;   // px per unit of the plane under the fan, as in the plan at the end of m_bend
    const tQ = cue('q'), tPoint = cue('point'), tM = cue('mean');
    const ang = i => -i * Math.PI / 8;   // the fan's lines: 0°, 22.5°, ... counter-clockwise on screen; the first is
    const udir = i => [Math.sin(ang(i)), Math.cos(ang(i))];   // the tangent at p (world (0, 1); screen right is +y)

    // ---- the opening: the landscape ---------------------------------------------------------------------
    // The bent pipe (k = 0.3) near p, filled in to the centre so that its inner wall is a hill (f is a dome there,
    // 2 high at the centre), seen 42 degrees up from outside the ring and 50 degrees round toward −y, looking at p: a
    // valley curving round a hill, coming toward us on the left. Heights are drawn at ZSH = 0.4 of the horizontal
    // scale (the scenes that follow use 0.55): from straight outside, or with steeper walls, the near wall would hide
    // p. On it, the eight straight lines through p, each climbing to green arrowheads, and the bottom circle from p
    // toward us, red, going down. From 1.75 s the camera rises to straight down over p, turning to the view from +x
    // (as at "Seen from above" in m_bend), and the lifted lines become the flat fan.
    const land = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    root.insertBefore(land, root.firstChild);
    const UH = []; for (let i = 0; i <= 32; i++) UH.push(i <= 24 ? lerp(-1, 0, (i / 24) ** 0.8) : lerp(0, R1 - 1, (i - 24) / 8));
    const LAND = solid(land, { nj: NS, ni: 32, pointAt: (j, i, out) => meshPoint(-Math.PI + 2 * Math.PI * j / NS, UH[i], 1, KMAX, out), zs: ZSH });
    const lsvg = svgLayer(land);
    const EL0 = 42 * Math.PI / 180, AZH = -50 * Math.PI / 180, D0 = 3.5;
    const MR = [80, 110, 1040, 890], X0 = 660, Y0 = 600, PPU0 = 600;   // the picture (soft-edged), p in it, px per unit at p
    // the camera at rise r: up to straight down and round to azimuth 0, away to GROW times its distance; p from
    // (X0, Y0) to the fan's centre, and the scale at p from PPU0 to the fan's, geometrically
    const camAt = r => {
      const d = D0 * GROW ** (r * r);
      LAND.look([1, 0, 0], lerp(EL0, Math.PI / 2, r), lerp(AZH, 0, r), d);
      LAND.V = { s: (PPU0 ** (1 - r) * PS ** r) * d, cx: lerp(X0, P.x, r), cy: lerp(Y0, P.y, r) };
    };
    const tR0 = 1.75, tArr = tR0 + 2.35;   // the rise; it arrives just before "and suppose"
    const riseOf = t => ramp(t, tR0, tArr - tR0, E.io);
    camAt(0);
    const inPic = q => q[0] > MR[0] + 70 && q[0] < MR[2] - 70 && q[1] > MR[1] + 60 && q[1] < MR[3] - 70;
    // the lines: from p each way while the line climbs, stays on the surface and in the picture, at most LF
    const LINES = [];
    for (let i = 0; i < 8; i++) {
      const [ux, uy] = udir(i);
      const ends = [1, -1].map(sg => {
        let best = 0, bz = 0;
        for (let n = 1; n <= 600; n++) {
          const s = LF * n / 600, x = 1 + sg * s * ux, y = sg * s * uy, r = Math.hypot(x, y), z = F(x, y, KMAX);
          if (r > R1 - 0.01 || z < bz || !inPic(LAND.scr(x, y, z))) break;
          best = s; bz = z;
        }
        return best;
      });
      LINES.push({ ux, uy, ends, e: [lifted(lsvg, C.ink, 3), lifted(lsvg, C.ink, 3)], h: [stroke(lsvg, C.good, 5), stroke(lsvg, C.good, 5)] });
    }
    const lineAt = (ln, s) => { const x = 1 + s * ln.ux, y = s * ln.uy; return [x, y, F(x, y, KMAX)]; };
    const circAt = th => [Math.cos(th), Math.sin(th), F(Math.cos(th), Math.sin(th), KMAX)];
    // the bottom circle from p toward −y, as far as the picture allows
    let TD = 0; for (let n = 1; n <= 300; n++) { const th = -n * 0.005; if (!inPic(LAND.scr(...circAt(th)))) break; TD = th; }
    const red = sv(lsvg, 'g'), redL = lifted(red, C.bad, 5.5), redH = stroke(red, C.bad, 5.5);
    const pDot = sv(lsvg, 'circle', { r: 13, fill: C.pat });
    // an arrowhead 4 px past the end b of a curve that comes from a (world points), if that end is in sight
    const headAt = (e, a, b, size) => {
      const qa = LAND.scr(...a), qb = LAND.scr(...b), an = Math.atan2(qb[1] - qa[1], qb[0] - qa[0]);
      e.setAttribute('d', LAND.seen(qb) ? chevron(qb[0] + 4 * Math.cos(an), qb[1] + 4 * Math.sin(an), an, size) : '');
      return [qb[0], qb[1], an];
    };
    let drawn = '';
    const drawLand = r => {
      const key = r.toFixed(5);
      if (key === drawn) return;
      drawn = key;
      camAt(r); LAND.place(); LAND.render();
      // the mask: the picture's soft-edged rectangle, opening out past the frame as the camera rises
      const u = E.io(clamp(r / 0.7));
      softRect(land, [lerp(MR[0], -300, u), lerp(MR[1], -300, u), lerp(MR[2], W + 300, u), lerp(MR[3], H + 300, u)], 60);
      const pp = LAND.scr(1, 0, 0);
      for (const ln of LINES) {
        // each half from p, with its arrowhead as large as the flat fan's at the top; a half too short on screen (one
        // that climbs the near bank toward us) is left out, and comes as the camera rises and it lengthens
        ln.q = [0, 1].map(k => {
          const sg = k ? -1 : 1, e = ln.ends[k], h = ln.h[k];
          const pts = []; for (let n = 0; n <= 40; n++) pts.push(lineAt(ln, sg * e * n / 40));
          LAND.setCurve(ln.e[k], pts);
          const q = headAt(h, lineAt(ln, sg * (e - 0.01)), lineAt(ln, sg * e), lerp(22, 18, r));
          h.setAttribute('stroke-width', lerp(5, 4.5, r).toFixed(2));
          const o = clamp((Math.hypot(q[0] - pp[0], q[1] - pp[1]) - 45) / 30).toFixed(3);
          h.style.opacity = o; ln.e[k].g.style.opacity = o;
          return q;
        });
      }
      const cp = []; for (let n = 0; n <= 100; n++) cp.push(circAt(TD * n / 100));
      LAND.setCurve(redL, cp);
      headAt(redH, circAt(TD + 0.02), circAt(TD), 26);
      pDot.setAttribute('cx', pp[0].toFixed(2)); pDot.setAttribute('cy', pp[1].toFixed(2)); pDot.setAttribute('r', lerp(13, 14, r).toFixed(2));
      // p's name: beside the dot, and from above where the fan has it (in the gap under the tangent)
      const pa = Math.PI / 16, pr = 172;
      pl.style.left = lerp(pp[0] + 18, P.x + pr * Math.cos(pa) - 14, r).toFixed(1) + 'px';
      pl.style.top = lerp(pp[1] + 4, P.y + pr * Math.sin(pa) - 32, r).toFixed(1) + 'px';
    };
    // what goes during the rise: the red path and the labels; at the top the lines and p are the flat fan's (drawn
    // in the same place) and the surface fades to a tint, and away by "That means"
    for (const e of [red]) { tl.set(e, { o: 1 }, 0); tl.to(e, { o: 0 }, tR0, 0.7, E.in); }
    tl.set(lsvg, { o: 1 }, 0); tl.set(lsvg, { o: 0 }, tArr);
    tl.set(LAND.cv, { o: 1 }, 0); tl.to(LAND.cv, { o: 0.2 }, tArr, 0.6, E.io); tl.to(LAND.cv, { o: 0 }, tM - 1.2, 0.8, E.io);
    tl.set(land, { o: 1 }, 0); tl.set(land, { o: 0 }, tM);

    // ---- the flat fan ----
    const svg = svgLayer(root);
    // "and nothing nearby can be lower": a dashed circle around p, lightly green inside
    const near = sv(svg, 'circle', { cx: P.x, cy: P.y, r: 200, fill: alpha(C.good, 0.13), stroke: C.good, 'stroke-width': 3, 'stroke-dasharray': '10 10' });
    const nearFill = near; // the fill fades at "no"; the dashes stay faint
    // eight lines through p, each with green arrowheads riding its two tips: they take over from the lifted lines
    // when the camera arrives, as long as those were, and then grow to their full length
    const L = [], A = [];
    for (let i = 0; i < 8; i++) {
      L.push(stroke(svg, C.ink, 3));
      A.push([stroke(svg, C.good, 4.5), stroke(svg, C.good, 4.5)]);
    }
    const dot = sv(svg, 'circle', { cx: P.x, cy: P.y, r: 14, fill: C.pat });
    // p in the gap between the first two lines (placed with the landscape)
    const pl = rich(box(root, 0, 0), [it('p', C.pat)], 50);
    tl.set(svg, { o: 0 }, 0); tl.set(svg, { o: 1 }, tArr);
    tl.set(pl, { o: 0 }, 0); tl.to(pl, { o: 1 }, tQ - 0.15, 0.4, E.out);
    clock(tl, root, dur, t => {
      // (after the rise, once, so that p's name is placed whatever frame is shown first)
      drawLand(t < tM ? riseOf(t) : 1);
      const u = ramp(t, tArr, 0.7, E.io);
      for (let i = 0; i < 8; i++) {
        const a = ang(i), c = Math.cos(a), s = Math.sin(a), r0 = lerp(LINES[i].ends[0] * PS, FR, u), r1 = lerp(LINES[i].ends[1] * PS, FR, u);
        L[i].setAttribute('d', `M ${(P.x - c * r1).toFixed(2)} ${(P.y - s * r1).toFixed(2)} L ${(P.x + c * r0).toFixed(2)} ${(P.y + s * r0).toFixed(2)}`);
        A[i][0].setAttribute('d', chevron(P.x + c * (r0 + 4), P.y + s * (r0 + 4), a, 18));
        A[i][1].setAttribute('d', chevron(P.x - c * (r1 + 4), P.y - s * (r1 + 4), a + Math.PI, 18));
      }
    });

    const tAsk = cue('ask'), tObv = cue('obv'), tNear = cue('near'), tNo = cue('no');
    // "every straight line through it goes uphill, in both directions."
    const up = clab(root, 734, 'uphill along every straight line', 34, { color: C.good });
    slot(tl, up, tPoint + 2.5, tM - 0.3);   // at "uphill"

    // "That means: take a step along any line, as small as you like, but not zero, and you end up strictly higher
    // than where you started.": the fan steps left and dims but for one line; a marker steps along it, and a
    // graph of the height along that line (a schematic U, a·u² + b·u⁴) shows the step's height as a green bar
    const SHIFT = -270;
    for (const e of [svg, pl]) { tl.to(e, { x: SHIFT }, tM - 0.2, 0.8, E.io); tl.to(e, { x: 0 }, tAsk - 0.7, 0.7, E.io); }
    for (let i = 1; i < 8; i++) for (const e of [L[i], ...A[i]]) { tl.to(e, { o: 0.3 }, tM - 0.2, 0.6); tl.to(e, { o: 1 }, tAsk - 0.7, 0.6); }
    const D = [240, 170, 120];   // the three steps, in px along the line
    const stepOf = t => {
      let d = D[0] * ramp(t, tM + 1.1, 0.8, E.io);
      d = lerp(d, D[1], ramp(t, tM + 2.75, 0.6, E.io));
      return lerp(d, D[2], ramp(t, tM + 3.5, 0.6, E.io));
    };
    const mk = stroke(svg, C.pat, 4);   // a ring: hollow, so that it is not p
    const GX = 1450, GY = 520, GU = 280, GH = 230, Hu = u => GH * (0.9 * u * u + 0.1 * u ** 4);
    const gs = el(root, 'svg');
    gs.setAttribute('width', W); gs.setAttribute('height', H);
    Object.assign(gs.style, { position: 'absolute', left: 0, top: 0, overflow: 'visible' });
    const gr = sv(gs, 'g');
    stroke(gr, C.ink, 2, { d: `M ${GX - GU - 20} ${GY} L ${GX + GU + 20} ${GY}`, 'stroke-opacity': 0.55 });
    const U = []; for (let i = 0; i <= 120; i++) { const u = -1 + 2 * i / 120; U.push([GX + GU * u, GY - Hu(u)]); }
    stroke(gr, C.ink, 2.5, { d: poly(U) });
    const bar = stroke(gr, C.good, 8, { 'stroke-linecap': 'butt' });
    const lead = stroke(gr, C.good, 2);
    sv(gr, 'circle', { cx: GX, cy: GY, r: 10, fill: C.pat });
    const gmk = stroke(gr, C.pat, 4);
    const ring = (x, y, r) => `M ${(x - r).toFixed(2)} ${y.toFixed(2)} a ${r} ${r} 0 1 0 ${2 * r} 0 a ${r} ${r} 0 1 0 ${-2 * r} 0`;
    const gp = rich(box(root, GX - 12, GY + 8), [it('p', C.pat)], 44);
    const gstep = label(root, GX + GU - 70, GY + 14, 'step', { fontSize: '32px' });
    const hl = spans(label(root, 0, 216, '', { fontSize: '32px', color: C.good, width: W + 'px', textAlign: 'center', left: (GX - W / 2) + 'px', paddingLeft: LS + 'em' }), ['higher than ', ML('p', C.pat)]);
    const any = spans(label(root, 0, 600, '', { fontSize: '32px', width: W + 'px', textAlign: 'center', left: (GX - W / 2) + 'px', paddingLeft: LS + 'em' }), ['any nonzero step']);
    for (const e of [gr, mk]) { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, tM + 0.3, 0.6); tl.to(e, { o: 0 }, tAsk - 0.6, 0.4); }
    for (const e of [gp, gstep]) { fadeIn(tl, e, tM + 0.4, 0.5, 8); fadeOut(tl, e, tAsk - 0.6, 0.3, -8); }
    slot(tl, hl, tM + 1.7, tAsk - 0.6);
    slot(tl, any, tM + 4.08 - 0.1, tAsk - 0.6);   // at "but not zero"
    const tPulse = tM + 6.0;   // "strictly higher"
    clock(tl, root, dur, t => {
      const d = stepOf(t), u = d / FR, x = GX + GU * u, h = Hu(u);
      mk.setAttribute('d', d > 2 ? ring(P.x + d, P.y, 11) : '');
      gmk.setAttribute('d', d > 2 ? ring(x, GY - h, 10) : '');
      const pulse = Math.sin(Math.PI * clamp((t - tPulse) / 0.6));
      bar.setAttribute('d', d > 2 ? `M ${x.toFixed(2)} ${GY} L ${x.toFixed(2)} ${(GY - h).toFixed(2)}` : '');
      bar.setAttribute('stroke-width', (8 + 8 * pulse).toFixed(2));
      lead.setAttribute('d', d > 2 ? `M ${GX} 262 L ${x.toFixed(2)} ${(GY - h - 14).toFixed(2)}` : '');
    });
    tl.set(lead, { o: 0 }, 0); tl.to(lead, { o: 1 }, tM + 1.7, 0.4);
    // "Is the point a local minimum?"
    const QY = 772;
    const q = crow(root, QY, 26);
    rich(q, 'A local minimum?', 96);
    const qm = div(q, { width: '90px', height: '90px' });
    mark(tl, qm, 68, true, tObv + 0.1);
    fadeIn(tl, q, tAsk - 0.1, 0.7, 18);
    // "Every direction is a straight line"
    const ev = clab(root, 734, 'every direction is a straight line', 34);
    slot(tl, ev, tObv + 1.55, tNear - 0.3);
    // "and nothing nearby can be lower."
    tl.set(near, { o: 0 }, 0); tl.to(near, { o: 1 }, tNear - 0.1, 0.6, E.out);
    const nl = clab(root, 734, 'nothing lower nearby', 34, { color: C.good });
    slot(tl, nl, tNear + 0.15, tNo - 0.1);
    // "And yet, that is wrong.": at "wrong", the question and its tick give way to "Wrong." and a cross
    const wWrong = tNo + 1.2;   // "wrong." in build/audio/m_hook.json
    fadeOut(tl, q, wWrong - 0.4, 0.25, -10);
    tl.to(nearFill, { o: 0.25 }, wWrong - 0.2, 0.6, E.io);
    const no = crow(root, QY, 26);
    rich(no, 'Wrong.', 96, { color: C.bad });
    const nm = div(no, { width: '90px', height: '90px' });
    mark(tl, nm, 68, false, wWrong + 0.05);
    fadeIn(tl, no, wWrong - 0.2, 0.5, 14);

    // m_holes and m_area (a bowl with pinholes, then holes with width) are drawn by holesPart, over everything; the
    // fan, its p and "Wrong." leave as the bowl comes, and the fan comes back in m_crev at "So low ground"
    const tBowl = cue('bowl'), tSo = cue('so');
    fadeOut(tl, no, tBowl - 0.3, 0.35, -16);
    tl.to(near, { o: 0 }, tBowl - 0.3, 0.4, E.in);
    for (const e of [svg, pl]) { tl.to(e, { o: 0 }, tBowl - 0.3, 0.4, E.in); tl.to(e, { o: 1 }, tSo + 0.3, 0.7, E.out); }
    holesPart({ tl, root, cue, seg, dur });

    // m_crev. "If every straight line is to go up,": the label; "the only hope is to slip the low ground in along a
    // curve, thinner and thinner, so that every straight line leaves it at once.": the low ground, a red-shaded
    // sliver along the circle through p (the region where the bent pipe is below p: |r² − 1| < c·y², c² = KMAX/2,
    // the water of the plan at "Seen from above"), slipping in from both sides; at "thinner and thinner" bars across
    // it show its width, shrinking like the square of the distance; at "every straight line leaves it at once" a line
    // near the tangent, green from p to where it would enter the sliver
    const tStrong = cue('strong'), tCurve = cue('curve'), tPath = cue('path'), tWild = cue('wild'), tSmooth = cue('smooth');
    const cs = seg('m_crev');
    // the words (build/audio/m_crev.json)
    const wEvery = cs + 5.39, wSlip = cs + 8.75, wThinner = cs + 11.55, wLeaves = cs + 13.31, wStrictly = cs + 18.27;
    const wPicture = cs + 21.71, wBowl = cs + 22.71, wCrevasse = cs + 23.67, wAlong = cs + 25.15;
    const wNothing = cs + 29.39, wCarved = cs + 30.43, wSurface = cs + 31.39, wPerfectly = cs + 32.31, wSmooth = cs + 32.75;
    // the two labels in one centred row: the second opens up beside the first, pushing it left
    const VY = 772;
    const vrow = crow(root, VY, 0);
    const vUp = flabel(vrow, 'every straight line: up', 34, { color: C.good });
    const vWrap = div(vrow, { overflow: 'hidden', whiteSpace: 'nowrap', maxWidth: '0px' });
    const vDn = flabel(vWrap, 'a curved path: strictly down', 34, { color: C.bad, paddingLeft: '90px', display: 'inline-block' });
    tl.custom(vWrap, 'open', (e, v) => { e.style.maxWidth = (v * 1000).toFixed(1) + 'px'; }, 0);
    tl.set(vWrap, { open: 0 }, 0); tl.to(vWrap, { open: 1 }, tPath + 0.1, 0.7, E.io);
    tl.set(vDn, { o: 0 }, 0); tl.to(vDn, { o: 1 }, tPath + 0.4, 0.6, E.out);
    fadeIn(tl, vUp, wEvery - 0.25, 0.6, 10);
    // the plane under the fan: world (x, y) at P + PS·(y, x − 1), as in the plan
    const FW = (x, y) => [P.x + PS * y, P.y + PS * (x - 1)];
    const CS = Math.sqrt(KMAX / 2), YS = 0.78;   // the sliver's width factor, and how far out it is drawn
    const slv = sv(svg, 'g'), slvD = sv(sv(svg, 'defs'), 'radialGradient', { id: 'm-slv-fade', gradientUnits: 'userSpaceOnUse', cx: P.x, cy: P.y, r: 470 });
    for (const [o, a] of [[0, 1], [0.6, 1], [0.95, 0]]) sv(slvD, 'stop', { offset: o, 'stop-color': '#fff', 'stop-opacity': a });
    const slvM = sv(sv(svg, 'defs'), 'mask', { id: 'm-slv-mask', maskUnits: 'userSpaceOnUse', x: 0, y: 0, width: W, height: H });
    sv(slvM, 'rect', { x: 0, y: 0, width: W, height: H, fill: 'url(#m-slv-fade)' });
    slv.setAttribute('mask', 'url(#m-slv-mask)');
    // one arm of the sliver (sg = ±1, the side of p), from |y| = y0 out to YS: its outline, along the outer edge and
    // back along the inner
    const armD = (sg, y0) => {
      if (y0 >= YS - 1e-3) return '';
      const outE = [], inE = [];
      for (let n = 0; n <= 70; n++) {
        const y = sg * lerp(y0, YS, n / 70), w = CS * y * y;
        outE.push(FW(Math.sqrt(1 + w - y * y), y)); inE.push(FW(Math.sqrt(Math.max(0, 1 - w - y * y)), y));
      }
      return poly(outE.concat(inE.reverse())) + ' Z';
    };
    const arms = [1, -1].map(sg => ({ sg, e: sv(slv, 'path', { fill: alpha(C.bad, 0.2), stroke: alpha(C.bad, 0.55), 'stroke-width': 2, 'stroke-linejoin': 'round' }) }));
    // the width bars, at |y| = 0.62, 0.47, 0.32, 0.17 on both arms, appearing from the outside in
    const bars = [];
    [0.62, 0.47, 0.32, 0.17].forEach((y, i) => [1, -1].forEach(sg => {
      const yy = sg * y, w = CS * y * y, a = FW(Math.sqrt(1 + w - yy * yy), yy), b = FW(Math.sqrt(1 - w - yy * yy), yy);
      // drawn a little past the edges, so that the shortest still shows
      const dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L;
      const e = stroke(slv, C.bad, 3.5, { d: segD2([a[0] - 5 * ux, a[1] - 5 * uy], [b[0] + 5 * ux, b[1] + 5 * uy]) });
      tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, wThinner - 0.1 + i * 0.3, 0.3); tl.to(e, { o: 0 }, tPath - 0.3, 0.4);
      bars.push(e);
    }));
    // the line near the tangent (10 degrees off it, toward the circle): it would enter the sliver at sIn
    const AL10 = 10 * Math.PI / 180, lu = [-Math.sin(AL10), Math.cos(AL10)], sIn = 2 * Math.sin(AL10) / (1 + CS * Math.cos(AL10) ** 2);
    const lnG = sv(svg, 'g');
    stroke(lnG, C.ink, 3.5, { d: segD2(FW(1 - FR / PS * lu[0], -FR / PS * lu[1]), FW(1 + FR / PS * lu[0], FR / PS * lu[1])) });
    const lnGreen = stroke(lnG, C.good, 8, { d: segD2(FW(1, 0), FW(1 + sIn * lu[0], sIn * lu[1])) });
    { const q = FW(1 + sIn * lu[0], sIn * lu[1]); sv(lnG, 'circle', { cx: q[0], cy: q[1], r: 8, fill: C.bg, stroke: C.bad, 'stroke-width': 3 }); }
    tl.set(lnG, { o: 0 }, 0); tl.to(lnG, { o: 1 }, wLeaves - 0.2, 0.5); tl.to(lnG, { o: 0 }, tPath - 0.2, 0.4);
    // while the line is shown, the other lines step back
    for (let i = 0; i < 8; i++) for (const e of [L[i], ...A[i]]) { tl.to(e, { o: 0.35 }, wLeaves - 0.2, 0.5); tl.to(e, { o: 1 }, tPath - 0.2, 0.5); }
    // "Then there would be a whole path that goes strictly down": the circle's arc through p, red, both ways, with
    // arrowheads pointing away from p, as in the plan at "Seen from above"
    const PARC = 55 * Math.PI / 180, parc = stroke(svg, C.bad, 4.5), parcH = [];
    for (const d of [20, 38, 54.5]) for (const sg of [-1, 1]) parcH.push({ th: sg * d * Math.PI / 180, sg, e: stroke(svg, C.bad, 4.5) });
    clock(tl, root, dur, t => {
      if (t < tCurve - 0.5 || t > dur) return;
      // the sliver slips in from its far ends toward p
      const y0 = YS * (1 - ramp(t, wSlip - 0.2, 2.6, E.io));
      for (const a of arms) a.e.setAttribute('d', armD(a.sg, y0));
      const g = ramp(t, tPath + 0.1, 1.4, E.io) * PARC, pts = [];
      for (let n = 0; n <= 120; n++) { const th = lerp(-g, g, n / 120); pts.push(FW(Math.cos(th), Math.sin(th))); }
      parc.setAttribute('d', g > 0.002 ? poly(pts) : '');
      for (const h of parcH) {
        if (g < Math.abs(h.th)) { h.e.setAttribute('d', ''); continue; }
        const b = FW(Math.cos(h.th), Math.sin(h.th)), a = FW(Math.cos(h.th - h.sg * 0.01), Math.sin(h.th - h.sg * 0.01));
        h.e.setAttribute('d', chevron(b[0], b[1], Math.atan2(b[1] - a[1], b[0] - a[0]), 18));
      }
    });
    // "If you try to picture that, you probably see a bowl, with a crevasse carved into it along the curved path.":
    // the fan and its labels dim and step left; on the right, in three dimensions, a bowl around p, and then a
    // crevasse cut into it along the arc of the circle, its floor the curved path going down
    const FAN = -440;
    for (const e of [svg, pl]) { tl.to(e, { x: FAN }, tWild - 0.1, 0.8, E.io); tl.to(e, { o: 0.3 }, tWild - 0.1, 0.6); }
    fadeOut(tl, vrow, tWild - 0.1, 0.4, 0);
    // the fan's labels again, stacked under it on the left
    const vcol = box(root, P.x + FAN - 500, 772, { width: '1000px', display: 'flex', flexDirection: 'column', alignItems: 'center', rowGap: '14px' });
    flabel(vcol, 'every straight line: up', 34, { color: C.good, paddingLeft: LS + 'em' });
    flabel(vcol, 'a curved path: strictly down', 34, { color: C.bad, paddingLeft: LS + 'em' });
    tl.set(vcol, { o: 0 }, 0); tl.to(vcol, { o: 0.3 }, tWild + 0.3, 0.6);
    const PIC = { x0: 1040, x1: 1790, y0: 250, y1: 858, cx: 1415 };   // the picture's place on the right: the opening's, at 0.78
    // a solid for a static picture, in a box of its own, rendered once: p at (px, py) on screen, ppu px per unit at
    // p, the camera el up from azimuth az, d away
    const still = (parent, mesh, { el, az, d, px, py, ppu, zs, height }) => {
      const S = solid(parent, Object.assign({ shadow: false }, mesh, { zs, height }));
      S.look([1, 0, 0], el, az, d); S.V = { s: ppu * d, cx: px, cy: py };
      S.place(); S.render();
      return S;
    };
    // the crevasse's camera: 60 degrees up, looking along the crevasse toward p (from lower than this, the bowl's near
    // wall hides its floor); the smooth picture has the opening's, at 0.78 of its size, in the same place
    const CAM = { el: 60 * Math.PI / 180, az: -105 * Math.PI / 180, d: D0, px: PIC.cx, py: 580, ppu: 470, zs: 0.55 };
    const CAMS = { el: EL0, az: AZH, d: D0, px: PIC.x0 + 0.78 * (X0 - MR[0]), py: PIC.y0 + 0.78 * (Y0 - MR[1]), ppu: 0.78 * PPU0, zs: ZSH };
    // the bowl z = 1.5·|q − p|² on the disc of radius 0.65 around p; the crevasse along the unit circle from p
    // toward −y (where the opening has its red path), a V of half-width 0.1 (narrower over its first 0.3, toward p), its floor
    // going down as 0.25·θ
    const RB = 0.65, CW = 0.1, CF = 0.25, BK = 1.5;
    const bowlZ = (x, y) => BK * ((x - 1) ** 2 + y * y);
    const TCUT = 2 * Math.asin(RB / 2) - 0.12;   // where the crevasse ends: 0.12 before the rim, along the arc
    const groove = (x, y) => {
      const th = -Math.atan2(y, x);
      if (th <= 0) return 0;
      const w = CW * Math.min(1, 0.15 + th / 0.35), d = Math.abs(Math.hypot(x, y) - 1);
      // it stops short of the rim, in a steep end wall
      return d >= w ? 0 : (2 * BK * (1 - Math.cos(th)) + CF * th) * (1 - d / w) * clamp((TCUT - th) / 0.05);
    };
    // the mesh: polar about the ring's centre (so the crease, r = 1, and the groove's edges are mesh lines), out to
    // flat ground round the bowl (to radius RO around p; points beyond pulled in to that edge), so that the bowl is a
    // hollow in the ground and nothing of the crevasse shows below it
    const RO = 0.95, NTH = 430, TH0 = 1.26;
    // the radii of the mesh: 0.01 apart, and 0.004 apart across the crevasse (so that its walls shade smoothly)
    const RRS = []; for (let r = 0.05; r < 1.95; r += Math.abs(r - 1) < CW + 0.02 ? 0.004 : 0.01) RRS.push(r);
    const NR = RRS.length - 1;
    const groundZ = (x, y) => BK * Math.min(RB * RB, (x - 1) ** 2 + y * y);
    const bowlMesh = cut => ({ nj: NTH, ni: NR, edges: false, pointAt: (j, i, out) => {
      const th = lerp(-TH0, TH0, j / NTH), r = RRS[i];
      let x = r * Math.cos(th), y = r * Math.sin(th);
      const dx = x - 1, rr = Math.hypot(dx, y);
      if (rr > RO) { x = 1 + dx * RO / rr; y = y * RO / rr; }
      out[0] = x; out[1] = y; out[2] = groundZ(x, y) - (cut ? groove(x, y) : 0);
    } });
    // the bowl's tones by height; inside the crevasse darker the deeper, as a cut in shadow
    const bowlH = cut => (hz, x, y) => clamp((hz + 0.3) / 0.9) - (cut ? Math.min(2.4, 12 * groove(x, y)) : 0);
    const cre = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    softRect(cre, [PIC.x0, PIC.y0, PIC.x1, PIC.y1], 47);
    const B0 = still(cre, bowlMesh(false), Object.assign({ height: bowlH(false) }, CAM));
    const B1 = still(cre, bowlMesh(true), Object.assign({ height: bowlH(true) }, CAM));
    const csvg = svgLayer(cre);
    // the rim and rings of equal height around p (faint): on the cut bowl they dip into the crevasse; each picture has
    // its own, faded with its canvas
    const rings = (S, cut) => {
      const g = sv(csvg, 'g');
      for (const [rad, op] of [[RB, 0.5], [0.5, 0.22], [0.35, 0.22], [0.2, 0.22]]) {
        const e = lifted(g, C.ink, rad === RB ? 2.5 : 2, { 'stroke-opacity': op }), pts = [];
        for (let n = 0; n <= 480; n++) { const a = 2 * Math.PI * n / 480, x = 1 + rad * Math.cos(a), y = rad * Math.sin(a); pts.push([x, y, bowlZ(x, y) - (cut ? groove(x, y) : 0)]); }
        S.setCurve(e, pts);
      }
      return g;
    };
    const ring0 = rings(B0, false), ring1 = rings(B1, true);
    // straight lines from p climbing to the rim, with green arrowheads
    const headOn = (S, e, a, b, size) => { const qa = S.scr(...a), qb = S.scr(...b), an = Math.atan2(qb[1] - qa[1], qb[0] - qa[0]); e.setAttribute('d', chevron(qb[0] + 4 * Math.cos(an), qb[1] + 4 * Math.sin(an), an, size)); };
    for (const deg of [90, 15, 165]) {
      const u = dir(deg), e = lifted(csvg, C.ink, 3), pts = [];
      for (let n = 0; n <= 60; n++) { const s = (RB - 0.04) * n / 60, x = 1 + s * u[0], y = s * u[1]; pts.push([x, y, bowlZ(x, y)]); }
      B1.setCurve(e, pts);
      headOn(B1, stroke(csvg, C.good, 4.5), pts[57], pts[60], 20);
    }
    // the floor of the crevasse: the curved path, red, with its arrowhead, drawn from p at "along the curved path"
    const thEnd = TCUT - 0.1;
    const floorPt = th => [Math.cos(th), -Math.sin(th), -CF * th];
    const crG = sv(csvg, 'g'), crL = lifted(crG, C.bad, 5), crH = stroke(crG, C.bad, 5);
    const crDraw = t => {
      const g = ramp(t, wAlong - 0.1, 0.9, E.io);
      if (g < 0.002) { B1.setCurve(crL, null); crH.setAttribute('d', ''); return; }
      const pts = []; for (let n = 0; n <= 80; n++) pts.push(floorPt(thEnd * g * n / 80));
      B1.setCurve(crL, pts);
      if (g > 0.25) headOn(B1, crH, floorPt(thEnd * g - 0.02), floorPt(thEnd * g), 22); else crH.setAttribute('d', '');
    };
    { const q = B1.scr(1, 0, 0); sv(csvg, 'circle', { cx: q[0], cy: q[1], r: 11, fill: C.pat }); }
    const creL = clab(root, 140, 'what you picture:\na bowl with a crevasse', 34, { width: (PIC.x1 - PIC.x0) + 'px', left: PIC.x0 + 'px', lineHeight: 1.45 });
    // the bowl, then the cut (the cut picture fades in over the plain one)
    tl.set(cre, { o: 0 }, 0); tl.to(cre, { o: 1 }, wPicture - 0.2, 0.6, E.out);
    for (const e of [B1.cv, ring1]) { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, wCrevasse - 0.2, 0.7, E.io); }
    tl.set(ring0, { o: 1 }, 0); tl.to(ring0, { o: 0 }, wCrevasse - 0.2, 0.7, E.io); tl.set(B0.cv, { o: 1 }, 0); tl.set(B0.cv, { o: 0 }, wCrevasse + 0.6);
    fadeIn(tl, creL, wBowl - 0.2, 0.5, 10);
    // "But nothing needs to be carved.": the picture dims, and a red cross over it
    tl.to(cre, { o: 0.35 }, wNothing - 0.1, 0.5, E.io);
    const xs = svgLayer(root), xg = sv(xs, 'g');
    cross(tl, xg, PIC.cx, 540, 300, C.bad, 8).forEach((p, i) => tl.to(p, { draw: 1 }, wCarved - 0.2 + i * 0.12, 0.35, E.out));
    // "The surface can be perfectly smooth.": in its place, from the same kind of camera, the valley of the opening
    // with its red path along the floor and p; the label in green, with a tick
    for (const e of [cre, xg]) tl.to(e, { o: 0 }, wSurface - 0.2, 0.3, E.in);
    fadeOut(tl, creL, wSurface - 0.2, 0.3, -8);
    const smo = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    const SM = still(smo, { nj: NS, ni: 32, pointAt: LAND.pointAt, shadow: false }, CAMS);
    softRect(smo, [PIC.x0, PIC.y0, PIC.x1, PIC.y1], 47);   // soft edges, as in the opening
    const ssvg = svgLayer(smo);
    {
      // the red path as far as in the opening
      const pts = []; for (let n = 0; n <= 80; n++) pts.push(circAt(TD * n / 80));
      SM.setCurve(lifted(ssvg, C.bad, 5), pts);
      headOn(SM, stroke(ssvg, C.bad, 5), circAt(TD + 0.02), circAt(TD), 22);
      const q = SM.scr(1, 0, 0); sv(ssvg, 'circle', { cx: q[0], cy: q[1], r: 11, fill: C.pat });
    }
    tl.set(smo, { o: 0 }, 0); tl.to(smo, { o: 1 }, wSurface, 0.6, E.out);
    const sl = box(root, PIC.x0, 140, { width: (PIC.x1 - PIC.x0) + 'px', display: 'flex', justifyContent: 'center', alignItems: 'center', columnGap: '18px' });
    flabel(sl, 'perfectly smooth', 34, { color: C.good });
    const sm = div(sl, { width: '52px', height: '52px' });
    mark(tl, sm, 40, true, wSmooth - 0.1);
    fadeIn(tl, sl, wPerfectly - 0.2, 0.5, 10);
    clock(tl, root, dur, t => { if (t > wAlong - 0.2 && t < wSurface + 0.2) crDraw(t); });

    // ---- the opening frame: the claim, beside the landscape (above), complete from the first frame, until it fades
    // as the narration begins
    const OP = box(root, 0, 0, { width: W + 'px', height: H + 'px' });
    // two lines and nothing else (the author's): the claim, and the answer in red
    const cl = box(OP, 1090, 250, { width: '800px' });
    div(cl, Object.assign(SERIF(94), { lineHeight: 1.1 }), 'Every direction\ngoes uphill');
    div(cl, Object.assign(SERIF(94), { lineHeight: 1.1, color: C.bad, marginTop: '56px' }), 'But it is not\na local minimum!');
    tl.to(OP, { o: 0 }, cue('q') - 0.4, 0.4, E.in);
  });

  scene(['m_pipe', 'm_bend', 'm_poly', 'm_why'], ({ tl, root, cue, dur }) => {
    const T = {}; for (const n of ['pipe', 'bottom', 'stand', 'straight', 'tangent', 'level', 'bend', 'down', 'still', 'drift', 'faster', 'gentle', 'slower', 'tilt2', 'both', 'water', 'wet', 'dry', 'above', 'lines2', 'path2', 'poly', 'trough', 'tilt', 'circ', 'tan', 'why', 'reach', 'first', 'each', 'order', 'inf', 'pin', 'test', 'hess']) T[n] = cue(n);
    // "Seen from above": the camera's rise, and then the plan, the top-down picture that stays to the end: p at
    // (960, 440) with the unit circle 520 px, and at "polynomial" moved left, p at (520, 480) and 400 px, clipped
    const riseOf = t => ramp(t, T.above + 0.05, 2.2, E.io), tTop = T.above + 2.25;
    // "Now fill the pipe with water, up to the level of where you stand.": the level rises from the lowest point of
    // the bent surface (−k at the sides) to p's height, 0; at "This part is the bend" the water's bend grows from the
    // pipe's k to the polynomial's 1, so that from then on the water is exactly where f < 0
    const waterOf = t => t < T.water + 0.2 ? null : { h: -KMAX * (1 - ramp(t, T.water + 0.2, 2.5, E.io)), kw: lerp(KMAX, 1, ramp(t, T.tilt - 0.1, 1.0, E.io)) };
    const planU = t => ramp(t, T.poly - 0.3, 0.8, E.io);
    const planOf = t => { const u = planU(t); return { cx: lerp(960, 520, u), cy: lerp(440, 480, u), S: lerp(520, 400, u), clip: [lerp(0, 80, u), lerp(0, 120, u), lerp(W, 900, u), lerp(H, 860, u)] }; };
    let PL = planOf(0);
    // the plan's world-to-screen: x comes down the screen (p at the front is at the bottom), y goes right
    const M = (x, y) => [PL.cx + PL.S * y, PL.cy + PL.S * (x - 1)];
    // "and bend it into a ring": the straight pipe's curvature from 0 to 1
    const kapOf = t => ramp(t, T.pipe + 2.35, 1.8, E.io);
    // the bend: k from 0 to KMAX over four seconds
    const kOf = t => KMAX * ramp(t, T.bend + 0.2, 4.0, E.io);

    // ---- the mesh, projected (the shared renderer) ----
    const R = solid(root, { nj: NS, ni: NU, pointAt: ringMesh(0, 0) });
    const VI = R.VI;
    // the camera: for the straight pipe stood round toward +y, swinging to the ring's view as the pipe bends; rising
    // with RISE to straight down over p, CAMD away
    let RISE = 0, CAMD = DIST;
    function setCam(kap) {
      const w = 1 - kap;
      CAMD = DIST * GROW ** (RISE * RISE);
      R.look([lerp(0.9 * w, 1, RISE), 0, TZ * (1 - RISE)], lerp(ELEV, Math.PI / 2, RISE), AZ0 * w, CAMD);
    }
    // world positions and normalized screen positions; returns their bounding box
    function place(kap, k) { setCam(kap); R.pointAt = ringMesh(kap, k); return R.place(); }
    // the view: the ring (for every k) as large as fits y = 120..800; the straight pipe up to 1700 px wide; in
    // between, whatever the bending pipe needs, blending into the ring's box as it closes
    const union = (a, b) => ({ x0: Math.min(a.x0, b.x0), x1: Math.max(a.x1, b.x1), y0: Math.min(a.y0, b.y0), y1: Math.max(a.y1, b.y1) });
    const fit = (b, wt, ht) => { const s = Math.min(wt / (b.x1 - b.x0), ht / (b.y1 - b.y0)); return { s, cx: 960 - s * (b.x0 + b.x1) / 2, cy: 460 - s * (b.y0 + b.y1) / 2 }; };
    const BR = union(place(1, 0), place(1, KMAX));
    const V1 = fit(BR, 1100, 680);
    function viewOf(kap, b) {
      if (kap >= 1) return V1;
      const w = kap ** 4, u = union(b, BR);
      const bb = { x0: lerp(b.x0, u.x0, w), x1: lerp(b.x1, u.x1, w), y0: lerp(b.y0, u.y0, w), y1: lerp(b.y1, u.y1, w) };
      return fit(bb, lerp(1700, 1100, kap), 680);
    }
    let VX = 0, shiftOf = t => 0;   // VX: the ring's shift to the left in m_bend (set below)
    const scr = R.scr, camOf = R.camOf;
    const cv = R.cv;
    const DPR = window.devicePixelRatio || 1;

    // ---- the water: a flat sheet at the level h over the surface bent by kw (WATER, or null for none) ----
    // A pixel shows water exactly where the nearest surface there lies below the level (the ray went through the
    // sheet to reach it). So the water is drawn with the surface, quad by quad back to front, on canvases of its own:
    // each quad's part below the level filled, its part above erased (nearer walls hide water behind them). The
    // fill and the waterline are each opaque in their canvas, and made translucent by the canvas's opacity: so the
    // pieces leave no seams, and the water keeps its strength when the surface fades.
    const wcv = el(root, 'canvas', { left: '0px', top: '0px', width: W + 'px', height: H + 'px', opacity: 0.3 });
    const wlv = el(root, 'canvas', { left: '0px', top: '0px', width: W + 'px', height: H + 'px', opacity: 0.75 });
    const wctxs = [wcv, wlv].map(c => { c.width = Math.round(W * DPR); c.height = Math.round(H * DPR); return c.getContext('2d'); });
    const [wctx, lctx] = wctxs;
    let WATER = null;
    const HW = (s, u, kw) => H0(u) - kw * ((1 + u) * Math.sin(s)) ** 4;   // the height that the water sees
    // the part of a polygon of points [x, y, g] where sg·g ≤ 0
    function cut(P, sg) {
      const out = [];
      for (let n = 0; n < P.length; n++) {
        const a = P[n], b = P[(n + 1) % P.length], ga = sg * a[2], gb = sg * b[2];
        if (ga <= 0) out.push(a);
        if ((ga < 0 && gb > 0) || (ga > 0 && gb < 0)) { const r = ga / (ga - gb); out.push([lerp(a[0], b[0], r), lerp(a[1], b[1], r), 0]); }
      }
      return out;
    }
    const polyPath = (c, P) => { c.beginPath(); c.moveTo(P[0][0], P[0][1]); for (let n = 1; n < P.length; n++) c.lineTo(P[n][0], P[n][1]); c.closePath(); };
    const NSUB = 4, wpt = [0, 0, 0];
    function drawWater(kap, k) {
      const cr = PL.clip;
      for (const c of wctxs) {
        c.restore(); c.setTransform(DPR, 0, 0, DPR, 0, 0); c.clearRect(0, 0, W, H);
        c.save(); c.beginPath(); c.rect(cr[0], cr[1], cr[2] - cr[0], cr[3] - cr[1]); c.clip();
        c.lineJoin = 'round';
      }
      if (!WATER || kap < 1) return;
      const { h, kw } = WATER;
      wctx.fillStyle = wctx.strokeStyle = C.bind; wctx.lineWidth = 0.8;
      lctx.strokeStyle = C.bind; lctx.lineWidth = 2.2; lctx.lineCap = 'round';
      // in batches: the pieces of one kind that follow each other in the order are drawn as one path (each piece
      // wound the same way, so that overlaps add); a batch is drawn when a piece of the other kind comes
      let any = false, mode = 0, wetP = null, lineP = null, dryP = null, dryW = null, nb = 0;
      const BATCH = 48;   // a path of many pieces fills slowly: a batch is drawn when it has this many
      const add = (path, P) => {
        let ar = 0; for (let n = 0; n < P.length; n++) { const a = P[n], b = P[(n + 1) % P.length]; ar += a[0] * b[1] - b[0] * a[1]; }
        const Q = ar < 0 ? P.slice().reverse() : P;
        path.moveTo(Q[0][0], Q[0][1]); for (let n = 1; n < Q.length; n++) path.lineTo(Q[n][0], Q[n][1]); path.closePath();
      };
      const flush = () => {
        if (mode === 1) { wctx.fill(wetP); wctx.stroke(wetP); lctx.stroke(lineP); }
        if (mode === 2) {
          for (const c of wctxs) { c.globalCompositeOperation = 'destination-out'; c.fill(dryP); c.lineWidth = 0.6; c.stroke(dryP); }
          wctx.fill(dryW);
          for (const c of wctxs) c.globalCompositeOperation = 'source-over';
          wctx.lineWidth = 0.8; lctx.lineWidth = 2.2;
        }
        mode = 0; nb = 0;
      };
      const toWet = () => { if (mode !== 1 || ++nb > BATCH) { flush(); mode = 1; wetP = new Path2D(); lineP = new Path2D(); } any = true; };
      const toDry = () => { if (mode !== 2 || ++nb > BATCH) { flush(); mode = 2; dryP = new Path2D(); dryW = new Path2D(); } };
      const G = [];
      const { order, SX, SY } = R, V = R.V;
      for (const q of order) {
        const j = (q / NU) | 0, i = q - j * NU;
        const s0 = -Math.PI + 2 * Math.PI * j / NS, s1 = s0 + 2 * Math.PI / NS, u0 = UU[i], u1 = UU[i + 1];
        const gmin = Math.min(HW(s0, u0, kw), HW(s0, u1, kw), HW(s1, u1, kw), HW(s1, u0, kw)) - h;
        if (gmin > 0.02) {
          // seen straight down, nothing hides anything: no erasing
          if (any && RISE < 1) { const a = VI(j, i), bq = VI(j, i + 1), c = VI(j + 1, i + 1), d = VI(j + 1, i); toDry(); add(dryP, [[SX[a], SY[a]], [SX[bq], SY[bq]], [SX[c], SY[c]], [SX[d], SY[d]]]); }
          continue;
        }
        // near the water: the quad in NSUB × NSUB pieces, each cut at the level
        for (let m = 0; m <= NSUB; m++) for (let n = 0; n <= NSUB; n++) {
          const s = lerp(s0, s1, m / NSUB), u = lerp(u0, u1, n / NSUB);
          meshPoint(s, u, kap, k, wpt);
          const c = camOf(wpt[0], wpt[1], wpt[2] * ZS);
          G[m * (NSUB + 1) + n] = [V.cx + V.s * c[0] / c[2], V.cy - V.s * c[1] / c[2], HW(s, u, kw) - h];
        }
        for (let m = 0; m < NSUB; m++) for (let n = 0; n < NSUB; n++) {
          const P = [G[m * (NSUB + 1) + n], G[m * (NSUB + 1) + n + 1], G[(m + 1) * (NSUB + 1) + n + 1], G[(m + 1) * (NSUB + 1) + n]];
          const wet = cut(P, 1);
          if (wet.length >= 3) {
            toWet(); add(wetP, wet);
            // the waterline: where the edges cross the level
            const X = [];
            for (let e = 0; e < 4; e++) { const a = P[e], b = P[(e + 1) % 4]; if ((a[2] < 0) !== (b[2] < 0)) { const r = a[2] / (a[2] - b[2]); X.push([lerp(a[0], b[0], r), lerp(a[1], b[1], r)]); } }
            for (let e = 0; e + 1 < X.length; e += 2) { lineP.moveTo(X[e][0], X[e][1]); lineP.lineTo(X[e + 1][0], X[e + 1][1]); }
          }
          if (any && RISE < 1) {
            const dry = cut(P, -1);
            // a piece wholly dry hides water and waterline behind it; the dry part of a cut piece only the water
            // (so as not to halve its own waterline)
            if (dry.length >= 3) { toDry(); add(wet.length < 3 ? dryP : dryW, dry); }
          }
        }
      }
      flush();
    }

    // the last frame's inputs: when nothing changed (the plan holding still), the canvas is left as it is
    let drawn = '';
    function drawSurface(kap, k) {
      const key = [kap, k, VX, RISE, PL.cx, PL.cy, PL.S, WATER ? WATER.h : 'dry', WATER ? WATER.kw : ''].join();
      if (key === drawn) return;
      drawn = key;
      const b = place(kap, k);
      let V = viewOf(kap, b);
      if (VX) V = { s: V.s, cx: V.cx + VX, cy: V.cy };
      // rising: the ring's centre (the camera's first target) goes from where it is on screen to the plan's p (the
      // last target), and the scale at the target from the ring's view to the plan's, geometrically
      if (RISE > 0) { const ppu = (V.s / DIST) ** (1 - RISE) * PL.S ** RISE; V = { s: ppu * CAMD, cx: lerp(V.cx, PL.cx, RISE), cy: lerp(V.cy, PL.cy, RISE) }; }
      R.V = V;
      // the plan's clip (the whole frame until it moves left)
      R.render({ clip: PL.clip, open: kap < 0.9999, after: () => drawWater(kap, k) });
    }

    // ---- what is drawn over the surface ----
    const svg = svgLayer(root);
    const setCurve = (c, pts) => R.setCurve(c, pts, p => WATER && p[2] < WATER.h - 1e-9);
    // where the level circle was, left behind when the pipe bends (dashed)
    const level0 = lifted(svg, C.dim, 2.5, { 'stroke-dasharray': '7 9' });
    // "Its lowest points form a circle": the bottom circle drawn heavier, from p around both ways
    const bottomL = lifted(svg, C.ink, 4);
    // straight lines through p (in the ground plane, at 30, 60, 90 degrees to the tangent), lifted onto the surface
    const g1 = sv(svg, 'g'), g2 = sv(svg, 'g');
    const LINES = [30, 60, 90].map(a => {
      const ux = -Math.sin(a * Math.PI / 180), uy = Math.cos(a * Math.PI / 180);
      return { ux, uy, e: lifted(g1, C.good, 4.5), e2: lifted(g2, C.good, 4.5) };
    });
    // each lifted line runs from p while its ground point stays in the ring, and only as far as it climbs on the
    // bent surface (beyond that, far from p, a line can come down into the region: that is the next scene's story)
    for (const ln of LINES) {
      ln.lim = [-1, 1].map(sg => {
        let best = 0, bz = 0;
        for (let i = 1; i <= 2000; i++) {
          const ss = sg * i * 0.001, x = 1 + ss * ln.ux, y = ss * ln.uy, r = Math.hypot(x, y);
          if (r < R0 || r > R1) break;
          const z = F(x, y, KMAX);
          if (z > bz) { bz = z; best = ss; }
        }
        return best;
      });
    }
    // the tangent x = 1, lifted: it leaves the bottom circle and climbs the outer wall
    const tanE = lifted(g1, C.good, 4.5), tanLim = Math.sqrt(R1 * R1 - 1) - 0.002;
    // on the bent surface, the tangent again (heavier while it is the one talked about), and a green ball that
    // steps out along it, off the circle and up the outer wall
    const gT = sv(svg, 'g'), tan2 = lifted(gT, C.good, 4.5);
    const stepOf = t => 0.45 * ramp(t, T.drift + 0.3, 2.6, E.io) + 0.25 * ramp(t, T.faster + 0.1, 2.2, E.io);
    // the ball's trail along the bottom circle
    const trail = lifted(svg, C.pat, 6);
    // p, and the ball: a small amber sphere with its contact shadow
    const defs = sv(svg, 'defs');
    const grad = (id, stops, attrs) => { const g = sv(defs, 'radialGradient', Object.assign({ id }, attrs)); for (const [o, c] of stops) sv(g, 'stop', { offset: o, 'stop-color': c }); };
    grad('m-ball', [[0, '#fff1d2'], [0.18, '#f2b552'], [0.62, C.pat], [1, '#6e3f00']], { cx: 0.36, cy: 0.32, r: 0.78, fx: 0.32, fy: 0.27 });
    grad('m-ball-sh', [[0, alpha(C.ink, 0.5)], [0.55, alpha(C.ink, 0.22)], [1, alpha(C.ink, 0)]], {});
    const pDot = sv(svg, 'circle', { r: 7, fill: C.pat });
    const ballG = sv(svg, 'g');
    const ballSh = sv(ballG, 'ellipse', { fill: 'url(#m-ball-sh)' });
    const ball = sv(ballG, 'circle', { fill: 'url(#m-ball)' });
    grad('m-gball', [[0, '#e3f6e8'], [0.2, '#4fb37a'], [0.62, C.good], [1, '#0b4426']], { cx: 0.36, cy: 0.32, r: 0.78, fx: 0.32, fy: 0.27 });
    const gballG = sv(svg, 'g');
    const gballSh = sv(gballG, 'ellipse', { fill: 'url(#m-ball-sh)' });
    const gball = sv(gballG, 'circle', { fill: 'url(#m-gball)' });
    const pLab = rich(box(root, 0, 0), [it('p', C.pat)], 50);
    // the ball's angle on the bottom circle: at "level" out to 70 degrees, back, out the other way, back; at "down"
    // round to 80 degrees, where it stays
    const LEG = 0.85, L0 = T.level - 0.05, AL = 70 * Math.PI / 180, AD = 80 * Math.PI / 180;
    const legs = t => [0, 1, 2, 3].map(n => ramp(t, L0 + n * LEG, LEG, E.io));
    const angOf = t => { const r = legs(t); return AL * (r[0] - r[1] - r[2] + r[3]) + AD * ramp(t, T.down + 0.1, 2.4, E.io); };
    function placeBall(th, k) { return placeOn(ball, ballSh, Math.cos(th), Math.sin(th), k, BRAD); }
    // a ball of radius rad resting on the drawn surface at (x, y), and its contact shadow
    function placeOn(ball, ballSh, x, y, k, rad) {
      const z = F(x, y, k) * ZS, m = 8 * (x * x + y * y - 1);
      // the normal of the drawn surface there: (−ZS·f_x, −ZS·f_y, 1)
      const nx = -ZS * m * x, ny = -ZS * (m * y - 4 * k * y ** 3), nl = Math.hypot(nx, ny, 1);
      const cx = x + rad * nx / nl, cy = y + rad * ny / nl, cz = z + rad / nl;
      const c = scr(cx, cy, cz / ZS), r = R.V.s * rad / c[2], g = scr(x, y, z / ZS);
      ball.setAttribute('cx', c[0].toFixed(2)); ball.setAttribute('cy', c[1].toFixed(2)); ball.setAttribute('r', r.toFixed(2));
      ballSh.setAttribute('cx', (g[0] + 0.25 * r).toFixed(2)); ballSh.setAttribute('cy', (g[1] + 0.12 * r).toFixed(2));
      ballSh.setAttribute('rx', (1.3 * r).toFixed(2)); ballSh.setAttribute('ry', (0.7 * r).toFixed(2));
      return r;
    }

    const circ = (a0, a1, n, k, z0) => { const pts = []; for (let i = 0; i <= n; i++) { const th = lerp(a0, a1, i / n), x = Math.cos(th), y = Math.sin(th); pts.push([x, y, z0 === undefined ? F(x, y, k) : z0]); } return pts; };
    const live = t => t > T.pipe - 0.2;
    clock(tl, root, dur, t => {
      if (!live(t)) return;
      const kap = kapOf(t), k = kOf(t);
      VX = shiftOf(t); RISE = riseOf(t); PL = planOf(t); WATER = waterOf(t);
      drawSurface(kap, k);
      // from above, the curves of the solid picture have gone (see the plan below): only p's name follows
      if (t > tTop + 0.7) { placePLab(scr(1, 0, 0), 0); return; }
      const ring = kap >= 1;
      const Z = (x, y) => F(x, y, k);
      setCurve(level0, ring && t > T.bend ? circ(0, 2 * Math.PI, 192, k, 0) : null);
      // the bottom circle, drawn from p both ways
      const bu = ramp(t, T.bottom - 0.1, 1.4, E.io) * Math.PI;
      setCurve(bottomL, ring && bu > 0.001 ? circ(-bu, bu, 192, k) : null);
      // the lifted straight lines: drawn at "straight", drawn again on the bent surface at "still"
      LINES.forEach((ln, i) => {
        const pts = g => { if (g <= 0.001) return null; const out = []; for (let n = 0; n <= 60; n++) { const s = lerp(g * ln.lim[0], g * ln.lim[1], n / 60), x = 1 + s * ln.ux, y = s * ln.uy; out.push([x, y, Z(x, y)]); } return out; };
        setCurve(ln.e, pts(ramp(t, T.straight - 0.1 + i * 0.4, 0.8, E.out)));
        setCurve(ln.e2, pts(ramp(t, T.still - 0.1 + i * 0.3, 0.8, E.out)));
      });
      const tg = ramp(t, T.tangent - 0.1, 1.2, E.out);
      setCurve(tanE, tg > 0.001 ? (() => { const out = []; for (let n = 0; n <= 80; n++) { const y = lerp(-tg * tanLim, tg * tanLim, n / 80); out.push([1, y, Z(1, y)]); } return out; })() : null);
      // the ball and its trail
      const th = angOf(t), r = legs(t), aMax = Math.max(AL * r[0], th), aMin = -AL * r[2];
      setCurve(trail, aMax - aMin > 0.001 ? circ(aMin, aMax, Math.max(2, Math.ceil(120 * (aMax - aMin))), k) : null);
      const br = placeBall(th, k);
      // the tangent on the bent surface, and the green ball on it
      const tw = ramp(t, T.still + 2.0, 0.6, E.io) * (1 - ramp(t, T.both - 0.1, 0.6, E.io));
      tan2.vis.setAttribute('stroke-width', lerp(4.5, 7, tw).toFixed(2)); tan2.hid.setAttribute('stroke-width', lerp(4.5, 7, tw).toFixed(2));
      const t2 = ramp(t, T.still + 2.0, 1.0, E.out);
      setCurve(tan2, t2 > 0.001 ? (() => { const out = []; for (let n = 0; n <= 80; n++) { const y = lerp(-t2 * tanLim, t2 * tanLim, n / 80); out.push([1, y, Z(1, y)]); } return out; })() : null);
      placeOn(gball, gballSh, 1, stepOf(t), k, 0.05);
      drawInset(stepOf(t), t);
      const pp = scr(1, 0, 0);
      pDot.setAttribute('cx', pp[0].toFixed(2)); pDot.setAttribute('cy', pp[1].toFixed(2)); pDot.setAttribute('r', lerp(7, 14, RISE).toFixed(2));
      placePLab(pp, br);
    });
    // p's name: beside the ball, and from above where the hook has it, in the gap under the tangent's line
    function placePLab(pp, br) {
      const a = Math.PI / 16, r = 172 * PL.S / 520;
      const x = lerp(pp[0] + br + 10, pp[0] + r * Math.cos(a) - 14, RISE), y = lerp(pp[1] - 30, pp[1] + r * Math.sin(a) - 32, RISE);
      pLab.style.left = x.toFixed(1) + 'px'; pLab.style.top = y.toFixed(1) + 'px';
    }
    window.__mSurface = t => { const kap = kapOf(t); RISE = riseOf(t); PL = planOf(t); WATER = waterOf(t); drawn = ''; drawSurface(kap, kOf(t)); return R.V; };   // for timing

    // ---- m_pipe ---------------------------------------------------------------------------------------------
    const LY = 842;
    // "take a half-pipe, and bend it into a ring."
    // from above, once the camera is there, the surface fades to a tint and its curves go (the plan takes over)
    for (const e of [cv, svg]) { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, T.pipe - 0.1, 1.0, E.out); tl.to(e, { o: e === cv ? 0.25 : 0 }, tTop, 0.6, E.io); }
    slot(tl, clab(root, LY, 'a half-pipe, bent into a ring'), T.pipe + 1.3, T.bottom - 0.3);
    // "Its lowest points form a circle, all at the same height."
    slot(tl, clab(root, LY, 'the lowest points: one height'), T.bottom + 0.8, T.stand + 0.9);
    // "Stand at one of them.": the ball at p, and the cross-section through p beside the ring
    for (const e of [ballG, pDot]) { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, T.stand - 0.1, 0.4); }
    show(tl, pLab, T.stand + 0.1, 0.4);
    // the ball leaves before the water comes
    tl.to(ballG, { o: 0 }, T.water - 0.3, 0.3, E.in);
    {
      const IX = 1630, IY = 610, IS = 420;   // the bottom's place in the drawing, and px per unit
      const ins = sv(svgLayer(root), 'g');
      const at = u => [IX + IS * u, IY - IS * ZS * H0(u)];
      const prof = []; for (let n = 0; n <= 80; n++) prof.push(at(lerp(R0 - 1, R1 - 1, n / 80)));
      stroke(ins, C.ink, 5, { d: poly(prof) });
      const rb = IS * BRAD;
      sv(ins, 'ellipse', { cx: IX + 0.25 * rb, cy: IY + 0.12 * rb, rx: 1.3 * rb, ry: 0.5 * rb, fill: 'url(#m-ball-sh)' });
      sv(ins, 'circle', { cx: IX, cy: IY - rb - 2.5, r: rb, fill: 'url(#m-ball)' });
      // green arrows up both walls, a little above the line
      for (const [u0, u1] of [[-0.09, -0.27], [0.08, 0.215]]) {
        const pts = []; for (let n = 0; n <= 30; n++) { const u = lerp(u0, u1, n / 30), p = at(u), q = at(u + 1e-4), tx = q[0] - p[0], ty = q[1] - p[1], tn = Math.hypot(tx, ty); let nx = ty / tn, ny = -tx / tn; if (ny > 0) { nx = -nx; ny = -ny; } pts.push([p[0] + 16 * nx, p[1] + 16 * ny]); }
        stroke(ins, C.good, 4.5, { d: poly(pts) });
        const a = pts[pts.length - 2], b = pts[pts.length - 1];
        stroke(ins, C.good, 4.5, { d: chevron(b[0], b[1], Math.atan2(b[1] - a[1], b[0] - a[0]), 16) });
      }
      const il = box(root, IX - IS * 0.05 - 260, IY - IS * ZS * 0.7 - 150, Object.assign(LABEL(32), { width: '520px', textAlign: 'center', paddingLeft: LS + 'em', lineHeight: 1.4, whiteSpace: 'pre' }));
      spans(il, ['the cross-section\nat ', ML('p', C.pat)]);
      tl.set(ins, { o: 0 }, 0); tl.to(ins, { o: 1 }, T.stand + 0.2, 0.6); tl.to(ins, { o: 0 }, T.bend - 0.2, 0.4, E.in);
      slot(tl, il, T.stand + 0.3, T.bend - 0.2);
    }
    // "Any straight step climbs the wall." — "Even a step along the pipe climbs"
    slot(tl, clab(root, LY, 'even along the pipe', 34, { color: C.good }), T.tangent + 0.6, T.level - 0.3);
    // "To stay level, you have to follow the circle."
    tl.to(g1, { o: 0.3 }, T.level - 0.1, 0.6, E.io);
    slot(tl, clab(root, LY, ['level: only along the circle'], 34, { color: C.pat }), T.level + 0.5, T.bend - 0.3);

    // ---- m_bend ---------------------------------------------------------------------------------------------
    // "Now bend the pipe downward, ever so gently": the green curves go; where the level circle was stays, dashed
    tl.to(g1, { o: 0 }, T.bend - 0.2, 0.4, E.in);
    tl.set(level0.g, { o: 0 }, 0); tl.to(level0.g, { o: 0.9 }, T.bend + 0.2, 0.6); tl.to(level0.g, { o: 0 }, tTop, 0.4);
    slot(tl, clab(root, LY, 'bend it down, gently'), T.bend + 0.4, T.down - 0.3);
    // "The circle that was level now goes downhill."
    slot(tl, clab(root, LY, 'the circle goes down', 34, { color: C.bad }), T.down + 0.2, T.still - 0.3);
    // "But a straight step still climbs"
    slot(tl, clab(root, LY, 'straight lines still go up', 34, { color: C.good }), T.still + 0.3, T.both - 0.3);
    // "even along the tangent": the other lines dim, the tangent is drawn heavier (in the per-frame update)
    tl.to(g2, { o: 0.3 }, T.still + 2.0, 0.6, E.io); tl.to(g2, { o: 1 }, T.both - 0.1, 0.6, E.io);
    // "The tangent drifts off the circle, and up the wall": the ring steps left to make room (it comes back at
    // "both"); to its right a small top view (the circle near p, the tangent at p, a marker stepping out along it, the
    // gap between them amber), and on the ring a green ball taking the same step along the lifted tangent
    shiftOf = t => -260 * (ramp(t, T.drift - 0.5, 0.9, E.io) - ramp(t, T.both - 0.3, 0.9, E.io));
    const DX = 1500, DY = 300, DS = 230;   // p in the top view, and px per unit; x comes toward us, y goes right
    const topv = (x, y) => [DX + DS * y, DY + DS * (x - 1)];
    const isvg = svgLayer(root), inset = sv(isvg, 'g'), bars = sv(isvg, 'g'), tiltG = sv(isvg, 'g');
    const gapE = sv(inset, 'path', { fill: alpha(C.pat, 0.32), stroke: 'none' });
    { const pts = []; for (let n = 0; n <= 80; n++) { const th = lerp(-0.8, 0.8, n / 80); pts.push(topv(Math.cos(th), Math.sin(th))); } stroke(inset, C.ink, 3.5, { d: poly(pts) }); }
    stroke(inset, C.good, 4, { d: poly([topv(1, -0.72), topv(1, 0.72)]) });
    { const p = topv(1, 0); sv(inset, 'circle', { cx: p[0], cy: p[1], r: 9, fill: C.pat }); }
    const mkE = sv(inset, 'circle', { r: 10, fill: C.good });
    const offL = clab(root, DY - 140, 'off the circle', 32, { color: C.pat, width: '400px', left: (DX + 40 - 200) + 'px' });
    // "and the wall rises faster than the bend falls": under it, two bars for the marker's step t along the tangent:
    // the wall's rise 2t⁴ up, in green, and the bend's fall k·t⁴ down, in red (k = 0.3; true to scale), each with
    // its name beside it; at "gentle" their sizes are written after the names
    const BX = 1300, BY = 560, BS = 360, LX = 1420;
    stroke(bars, C.ink, 2, { d: `M ${BX - 40} ${BY} L ${BX + 110} ${BY}`, 'stroke-opacity': 0.5 });
    const wallB = stroke(bars, C.good, 28, { 'stroke-linecap': 'butt' }), bendB = stroke(bars, C.bad, 28, { 'stroke-linecap': 'butt' });
    const ROW = { display: 'flex', alignItems: 'baseline', columnGap: '20px' };
    const wallRow = box(root, LX, BY - 150, ROW), bendRow = box(root, LX, BY + 6, ROW);
    const wallL = flabel(wallRow, 'the wall', 32, { color: C.good }), wallF = rich(wallRow, ['2', it('t'), '⁴'], 44, { color: C.good });
    const bendL = flabel(bendRow, 'the bend', 32, { color: C.bad }), bendF = rich(bendRow, ['− ', it('k'), ' ', it('t'), '⁴'], 44, { color: C.bad });
    const bendK = flabel(bendRow, [ML('k', C.bad), ' < 2'], 32, { color: C.bad });
    const higher = rich(box(root, LX, BY + 80), ['or  − ', it('t'), '⁶,  − ', it('t'), '⁸, …'], 44, { color: alpha(C.bad, 0.62) });
    // "Had we simply tilted the pipe, the tangent would have gone down with it.": for contrast, a plain tilt's fall
    // c·t² in place of the bend's, longer than the wall's rise, with a cross
    const tiltB = stroke(tiltG, C.bad, 28, { 'stroke-linecap': 'butt' });
    const tiltRow = box(root, LX, BY + 200, ROW);
    flabel(tiltRow, 'a plain tilt', 32, { color: C.bad }); rich(tiltRow, ['− ', it('c'), ' ', it('t'), '²'], 44, { color: C.bad });
    mark(tl, tiltRow, 36, false, T.tilt2 + 1.0);
    function drawInset(st, t) {
      const pts = [topv(1, 0), topv(1, st)];
      for (let n = 0; n <= 40; n++) { const y = st * (1 - n / 40); pts.push(topv(Math.sqrt(1 - y * y), y)); }
      gapE.setAttribute('d', st > 0.001 ? poly(pts) + ' Z' : '');
      const m = topv(1, st); mkE.setAttribute('cx', m[0].toFixed(2)); mkE.setAttribute('cy', m[1].toFixed(2));
      const hw = BS * 2 * st ** 4, hb = BS * KMAX * st ** 4, ht = 230 * ramp(t, T.tilt2 + 0.1, 0.7, E.out);
      wallB.setAttribute('d', hw > 0.5 ? `M ${BX} ${BY} L ${BX} ${(BY - hw).toFixed(2)}` : '');
      bendB.setAttribute('d', hb > 0.5 ? `M ${BX + 70} ${BY} L ${BX + 70} ${(BY + hb).toFixed(2)}` : '');
      tiltB.setAttribute('d', ht > 0.5 ? `M ${BX + 70} ${BY} L ${BX + 70} ${(BY + ht).toFixed(2)}` : '');
    }
    const tLeave = T.both - 0.2;
    for (const e of [inset, gballG]) { tl.set(e, { o: 0 }, 0); tl.to(e, { o: 1 }, T.drift - 0.1, 0.5); tl.to(e, { o: 0 }, tLeave, 0.4, E.in); }
    slot(tl, offL, T.drift + 1.2, tLeave);
    tl.set(bars, { o: 0 }, 0); tl.to(bars, { o: 1 }, T.faster - 0.1, 0.5); tl.to(bars, { o: 0 }, tLeave, 0.4, E.in);
    for (const e of [wallL, bendL]) slot(tl, e, T.faster + 0.1, tLeave);
    // "the wall rises only like the fourth power of the step." — "So the bend must fall more slowly than that: like
    // the fourth power with a smaller factor, or like a higher power."
    slot(tl, wallF, T.gentle + 5.7, tLeave);
    slot(tl, bendF, T.slower + 3.1, tLeave); slot(tl, bendK, T.slower + 3.5, tLeave);
    slot(tl, higher, T.slower + 5.3, tLeave);
    // the tilt: the bend's bar and sizes step back while it is shown
    tl.to(bendB, { o: 0 }, T.tilt2 - 0.1, 0.3); tl.to(bendRow, { o: 0.3 }, T.tilt2 - 0.1, 0.4);
    tl.set(higher.parentNode, { o: 1 }, 0); tl.to(higher.parentNode, { o: 0.3 }, T.tilt2 - 0.1, 0.4);
    tl.set(tiltG, { o: 1 }, 0); tl.to(tiltG, { o: 0 }, tLeave, 0.4, E.in);
    slot(tl, tiltRow, T.tilt2 + 0.3, tLeave);
    // "So every straight line goes up, and the circle goes down.": the two side by side
    const both = crow(root, LY, 90);
    flabel(both, 'straight lines still go up', 34, { color: C.good });
    flabel(both, 'the circle goes down', 34, { color: C.bad });
    slot(tl, both, T.both - 0.05, T.water - 0.2);
    // "Now fill the pipe with water, up to the level of where you stand." (the level rises in the per-frame update)
    slot(tl, clab(root, LY, ['water at the level of ', ML('p', C.pat)], 34, { color: WTEXT }), T.water + 0.4, T.wet - 0.3);
    // "The circle goes under water on both sides.": the straight lines step back, the trail shows under the water
    for (const e of [g2, gT]) { tl.to(e, { o: 0.3 }, T.water - 0.1, 0.6, E.io); tl.to(e, { o: 1 }, T.dry - 0.1, 0.6, E.io); }
    slot(tl, clab(root, LY, 'the circle: under water', 34, { color: WTEXT }), T.wet + 0.3, T.dry - 0.3);
    // "But every straight line starts out on dry ground."
    slot(tl, clab(root, LY, 'straight lines: dry at first', 34, { color: C.good }), T.dry + 0.3, T.above - 0.1);

    // ---- from above: the plan -------------------------------------------------------------------------------
    // "Seen from above, this is the picture we began with": the hook's picture again, drawn flat in the plan's
    // coordinates (M) over the faint surface and clipped with it. It stays: beside the polynomial in m_poly, and as
    // the map of m_why. The eight lines are at the hook's angles on screen; the first is the tangent at p.
    const fsvg = svgLayer(root);
    const fclip = sv(sv(sv(fsvg, 'defs'), 'clipPath', { id: 'm-plan-clip' }), 'rect');
    const plan = sv(fsvg, 'g', { 'clip-path': 'url(#m-plan-clip)' });
    const circG = sv(plan, 'g'), fanG = sv(plan, 'g'), tanG = sv(plan, 'g'), arcG = sv(plan, 'g');
    const whyLines = sv(plan, 'g'), whyGreens = sv(plan, 'g'), topG = sv(plan, 'g');
    const LF = 300 / 520;   // the lines' half-length: 300 px, as in the hook, when the circle is 520 px
    const FAN = [];
    for (let i = 0; i < 8; i++) {
      const a = -i * Math.PI / 8;   // on screen; in the world (sin a, cos a), since screen right is +y and down is +x
      FAN.push({ ux: Math.sin(a), uy: Math.cos(a), at: T.lines2 - 0.15 + i * 0.13, l: stroke(fanG, C.ink, 3), h: [stroke(fanG, C.good, 4.5), stroke(fanG, C.good, 4.5)] });
    }
    // the tangent, heavier in green at "On the tangent line", and in amber for the second derivative along it
    const tanHL = stroke(tanG, C.good, 8), tanAm = stroke(tanG, C.pat, 6);
    // the circle: the arc through p, red, with arrowheads pointing away from p
    const ARC = 55 * Math.PI / 180;
    const arc = stroke(arcG, C.bad, 4.5);
    const arcH = [];
    for (const d of [20, 38, 54.5]) for (const sg of [-1, 1]) arcH.push({ th: sg * d * Math.PI / 180, sg, e: stroke(arcG, C.bad, 4.5) });
    const pDot2 = sv(topG, 'circle', { r: 14, fill: C.pat });
    tl.set(pDot2, { o: 0 }, 0); tl.set(pDot2, { o: 1 }, tTop);
    // the five lines of m_why and the turning one, and q, are set further down
    let whyFrame = () => {};
    const pulse = (t, a, d) => Math.sin(Math.PI * clamp((t - a) / d));
    const segD = (a, b) => `M ${a[0].toFixed(2)} ${a[1].toFixed(2)} L ${b[0].toFixed(2)} ${b[1].toFixed(2)}`;
    clock(tl, root, dur, t => {
      if (t < tTop - 0.05) return;
      PL = planOf(t);
      const c = PL.clip;
      fclip.setAttribute('x', c[0]); fclip.setAttribute('y', c[1]); fclip.setAttribute('width', c[2] - c[0]); fclip.setAttribute('height', c[3] - c[1]);
      // a soft edge inside the clip, for the surface and the plan both
      const fe = 60 * planU(t), px = v => v.toFixed(1) + 'px';
      const mask = fe > 0.01 ? `linear-gradient(to right, transparent ${px(c[0])}, #000 ${px(c[0] + fe)}, #000 ${px(c[2] - fe)}, transparent ${px(c[2])}), linear-gradient(to bottom, transparent ${px(c[1])}, #000 ${px(c[1] + fe)}, #000 ${px(c[3] - fe)}, transparent ${px(c[3])})` : 'none';
      for (const e of [cv, wcv, wlv, fsvg]) if (e.style.maskImage !== mask) { e.style.maskImage = mask; e.style.maskComposite = 'intersect'; }
      const p = M(1, 0);
      pDot2.setAttribute('cx', p[0].toFixed(2)); pDot2.setAttribute('cy', p[1].toFixed(2));
      // the fan
      for (const f of FAN) {
        const u = ramp(t, f.at, 0.7, E.out), r = LF * u;
        const a = M(1 - r * f.ux, -r * f.uy), b = M(1 + r * f.ux, r * f.uy), len = Math.hypot(b[0] - a[0], b[1] - a[1]) / 2;
        f.l.setAttribute('d', u > 0.001 ? segD(a, b) : '');
        const on = len > 30, ang = Math.atan2(b[1] - a[1], b[0] - a[0]), cs = Math.cos(ang), sn = Math.sin(ang);
        f.h[0].setAttribute('d', on ? chevron(p[0] + cs * (len + 4), p[1] + sn * (len + 4), ang, 18) : '');
        f.h[1].setAttribute('d', on ? chevron(p[0] - cs * (len + 4), p[1] - sn * (len + 4), ang + Math.PI, 18) : '');
      }
      const tl0 = segD(M(1, -LF), M(1, LF));
      tanHL.setAttribute('d', tl0); tanAm.setAttribute('d', tl0);
      // the arc grows out of p both ways; at "On the circle" it pulses and stays a little heavier until m_why
      const g = ramp(t, T.path2 - 0.05, 1.4, E.io) * ARC, pts = [];
      for (let n = 0; n <= 120; n++) { const th = lerp(-g, g, n / 120); pts.push(M(Math.cos(th), Math.sin(th))); }
      arc.setAttribute('d', g > 0.002 ? poly(pts) : '');
      arc.setAttribute('stroke-width', (4.5 + 2 * ramp(t, T.circ, 0.5, E.io) * (1 - ramp(t, T.why - 0.3, 0.5, E.io)) + 5 * pulse(t, T.circ - 0.05, 1.0)).toFixed(2));
      for (const h of arcH) {
        if (g < Math.abs(h.th)) { h.e.setAttribute('d', ''); continue; }
        const b = M(Math.cos(h.th), Math.sin(h.th)), a = M(Math.cos(h.th - h.sg * 0.01), Math.sin(h.th - h.sg * 0.01));
        h.e.setAttribute('d', chevron(b[0], b[1], Math.atan2(b[1] - a[1], b[0] - a[0]), 18));
      }
      whyFrame(t);
    });
    // the labels under the fan, as in the hook: the second opens up beside the first
    const vrow = crow(root, 792, 0);
    const vUp = flabel(vrow, 'every straight line: up', 34, { color: C.good });
    const vWrap = div(vrow, { overflow: 'hidden', whiteSpace: 'nowrap', maxWidth: '0px' });
    const vDn = flabel(vWrap, 'a curved path: strictly down', 34, { color: C.bad, paddingLeft: '90px', display: 'inline-block' });
    tl.custom(vWrap, 'open', (e, v) => { e.style.maxWidth = (v * 1000).toFixed(1) + 'px'; }, 0);
    tl.set(vWrap, { open: 0 }, 0); tl.to(vWrap, { open: 1 }, T.path2 - 0.1, 0.7, E.io);
    tl.set(vDn, { o: 0 }, 0); tl.to(vDn, { o: 1 }, T.path2 + 0.2, 0.6, E.out);
    fadeIn(tl, vUp, T.lines2 + 0.3, 0.6, 10);
    fadeOut(tl, vrow, T.poly - 0.45, 0.35, -10);
    // the tangent's highlights
    tl.set(tanHL, { o: 0 }, 0); tl.to(tanHL, { o: 1 }, T.tan - 0.1, 0.4); tl.to(tanHL, { o: 0 }, T.why - 0.3, 0.4);
    tl.set(tanAm, { o: 0 }, 0); tl.to(tanAm, { o: 1 }, T.hess + 2.0, 0.5);

    // ---- m_poly ---------------------------------------------------------------------------------------------
    // "The surface can even be a polynomial.": the formula on the right of the plan, with its two terms as boxes
    // that can be marked
    const RX = 980, RW = 860;   // the right column
    const fr = box(root, RX, 250, { width: RW + 'px', display: 'flex', justifyContent: 'center', alignItems: 'center' });
    const term = parts => {
      const t = div(fr, { display: 'flex', margin: '0 12px' });
      const m = div(t, { position: 'absolute', left: '-8px', right: '-8px', top: '2px', bottom: '2px', borderRadius: '10px', opacity: 0 });
      rich(t, parts, 64);
      return { t, m };
    };
    rich(fr, [it('f'), '(', it('x'), ', ', it('y'), ') = '], 64);
    const pipeT = term(['2(', it('x'), '² + ', it('y'), '² − 1)²']);
    const bendT = term(['− ', it('y'), '⁴']);
    fadeIn(tl, fr, T.poly - 0.1, 0.7, 16);
    // "This part is the pipe": an ink mark and its name under it
    const markTerm = (tm, col, at, name, nameCol) => {
      Object.assign(tm.m.style, { background: alpha(col, 0.1), boxShadow: `inset 0 0 0 1.5px ${alpha(col, 0.6)}` });
      tl.set(tm.m, { o: 0, sx: 0.3 }, 0); tl.to(tm.m, { o: 1, sx: 1 }, at, 0.4, E.out5);
      const n = div(tm.t, { position: 'absolute', left: '-200px', right: '-200px', top: '96px', display: 'flex', justifyContent: 'center' });
      flabel(n, name, 32, { color: nameCol, paddingLeft: LS + 'em' });
      fadeIn(tl, n, at + 0.5, 0.5, 10);
    };
    markTerm(pipeT, C.ink, T.trough - 0.1, 'the pipe', C.dim);
    markTerm(bendT, C.pat, T.tilt - 0.1, 'the bend', C.dim);
    // and the water grows to the polynomial's own (in waterOf), named under the plan
    const uw = clab(root, 792, ['under water: ', ML('f'), ' < 0'], 32, { color: WTEXT, width: '820px', left: '80px' });
    fadeIn(tl, uw, T.tilt + 0.6, 0.6, 10);
    // "On the circle, the pipe is zero, and the bend makes the height negative." — "On the tangent line, the pipe
    // wins, two to one.": two lines under the formula, their names in one column; the arc and the tangent in the
    // plan answer them (in the per-frame update above)
    const chk = box(root, RX, 500, { width: RW + 'px', display: 'grid', gridTemplateColumns: 'auto auto', justifyContent: 'center', alignItems: 'baseline', columnGap: '36px', rowGap: '26px' });
    const c1 = rich(chk, 'on the circle:', 50, { justifySelf: 'end', color: C.dim });
    const c2 = rich(chk, ['0 − sin⁴ ', it('t'), '  ', ['<  0', C.bad]], 50);
    const t1 = rich(chk, 'on the tangent:', 50, { justifySelf: 'end', color: C.dim });
    const t2 = rich(chk, ['2', it('t'), '⁴ − ', it('t'), '⁴  =  ', it('t'), '⁴  ', ['>  0', C.good]], 50);
    fadeIn(tl, c1, T.circ - 0.1, 0.6, 14); fadeIn(tl, c2, T.circ + 0.05, 0.6, 14);
    fadeIn(tl, t1, T.tan - 0.1, 0.6, 14); fadeIn(tl, t2, T.tan + 0.05, 0.6, 14);
    for (const e of [fr, chk]) fadeOut(tl, e, T.why - 0.45, 0.4, -12);

    // ---- m_why ----------------------------------------------------------------------------------------------
    // The plan is the map: every lower point lies on a line from p, but along it f first rises. Drawn with M, which
    // holds still from here on.
    {
      const MB = (x, y) => [520 + 400 * y, 480 + 400 * (x - 1)];   // M as it is in m_why, for what is drawn once
      // the whole unit circle, in ink, under the red arc
      { const pts = []; for (let i = 0; i <= 360; i++) { const a = 2 * Math.PI * i / 360; pts.push(MB(Math.cos(a), Math.sin(a))); } stroke(circG, C.ink, 2.5, { d: poly(pts) }); }
      // the lines from p: ink through p, green from p to where the line enters the region
      const seg = (s0, s1, u) => segD(M(1 + s0 * u[0], s0 * u[1]), M(1 + s1 * u[0], s1 * u[1]));
      const SPAN = 2.4;
      // "Every point under water does lie on a straight line from where you stand.": q on the circle, 35 degrees round
      const qa = 35 * Math.PI / 180, q = [Math.cos(qa), Math.sin(qa)];
      const qd = Math.hypot(q[0] - 1, q[1]), qu = [(q[0] - 1) / qd, q[1] / qd], qe = entry(qu[0], qu[1]);
      const qLine = stroke(whyLines, C.ink, 3);
      const qGreen = stroke(whyGreens, C.good, 7), qCyan = stroke(whyGreens, WTEXT, 7);
      const qq = MB(q[0], q[1]);
      const qDot = stroke(topG, C.ink, 18, { d: dotD(qq[0], qq[1]) });
      const qLab = rich(box(root, qq[0] - 16, qq[1] - 74), [it('q')], 50);
      // five lines into the disc, and the one that turns toward the tangent
      const FIVE = [108, 124, 160, 248, 262].map(d => { const u = dir(d); return { u, e: entry(u[0], u[1]), ink: stroke(whyLines, C.ink, 2.5), g: stroke(whyGreens, C.good, 7), end: stroke(whyGreens, C.good, 15) }; });
      const turn = { ink: stroke(whyLines, C.ink, 3), g: stroke(whyGreens, C.good, 7), end: stroke(whyGreens, C.good, 15) };
      // the angle of the turning line: from 130 degrees to 92 (2 degrees from the tangent)
      const turnDeg = t => lerp(130, 92, ramp(t, T.inf + 0.2, 3.6, E.io));
      whyFrame = t => {
        if (t < T.why - 0.5) return;
        // p to q: drawn at "reach"; green on dry ground, dark cyan in the water, at "first"
        const r = ramp(t, T.reach + 0.2, 0.8, E.out);
        qLine.setAttribute('d', r > 0.001 ? seg(0, r * qd, qu) : '');
        const gq = ramp(t, T.first + 0.1, 0.8, E.out), cq = ramp(t, T.first + 2.6, 0.7, E.out);
        qGreen.setAttribute('d', gq > 0.001 ? seg(0, gq * qe, qu) : '');
        qCyan.setAttribute('d', cq > 0.001 ? seg(qe, lerp(qe, qd, cq), qu) : '');
        FIVE.forEach((ln, i) => {
          const a = ramp(t, T.each - 0.1 + i * 0.22, 0.7, E.out), g = ramp(t, T.each + 0.4 + i * 0.22, 0.6, E.out);
          ln.ink.setAttribute('d', a > 0.001 ? seg(-0.4 * a, SPAN * a, ln.u) : '');
          ln.g.setAttribute('d', g > 0.001 ? seg(0, g * ln.e, ln.u) : '');
          const ep = M(1 + ln.e * ln.u[0], ln.e * ln.u[1]);
          ln.end.setAttribute('d', g > 0.98 ? dotD(ep[0], ep[1]) : '');
        });
        const u = dir(turnDeg(t)), e = entry(u[0], u[1]), a = ramp(t, T.inf - 0.1, 0.6, E.out);
        turn.ink.setAttribute('d', a > 0.001 ? seg(-0.4 * a, SPAN * a, u) : '');
        turn.g.setAttribute('d', a > 0.001 ? seg(0, a * e, u) : '');
        const ep = M(1 + e * u[0], e * u[1]);
        turn.end.setAttribute('d', a > 0.98 ? dotD(ep[0], ep[1]) : '');
      };

      // "So what was wrong with the obvious argument?": the fan steps back, the region f < 0 arrives, with the
      // whole circle under the arc
      tl.to(fanG, { o: 0.3 }, T.why - 0.2, 0.6, E.io);
      tl.to(arcG, { o: 0.6 }, T.why - 0.2, 0.6, E.io);
      tl.set(circG, { o: 0 }, 0); tl.to(circG, { o: 1 }, T.why - 0.2, 0.8, E.out);
      // q
      show(tl, qDot, T.reach + 0.6, 0.3); fadeIn(tl, qLab, T.reach + 0.7, 0.4, 6);
      // "But along that line you first climb, on dry ground, and only then come down to the water.": the height along
      // the line, in the right column, with the water level through p's height
      const GX = 1290, GY = 430, GW = 470;   // the graph's left end (p) at height zero (the water level), and its width
      const gsvg = svgLayer(root), gg = sv(gsvg, 'g');
      const fq = s => F(1 + s * qu[0], s * qu[1]);
      let fmin = 0; for (let i = 0; i <= 400; i++) fmin = Math.min(fmin, fq(qd * i / 400));
      const KY = 240 / -fmin;   // true to scale: the dip is 240 px deep, the hump what it is
      const gpt = s => [GX + GW * s / qd, GY - KY * fq(s)];
      stroke(gg, C.bind, 3, { d: `M ${GX - 20} ${GY} L ${GX + GW + 40} ${GY}`, 'stroke-opacity': 0.8 });
      // under the level, the water, faint
      sv(gg, 'rect', { x: GX - 20, y: GY, width: GW + 60, height: 270, fill: alpha(C.bind, 0.1) });
      const wl = label(root, GX - 300, GY - 19, 'water level', { fontSize: '32px', color: WTEXT, width: '270px', textAlign: 'right' });
      const up = [], dn = [];
      for (let i = 0; i <= 200; i++) { const s = qd * i / 200; (s <= qe ? up : dn).push(gpt(s)); }
      dn.unshift(gpt(qe));
      const gUp = path(tl, gg, poly(up), { stroke: C.good, width: 6 });
      const gDn = path(tl, gg, poly(dn), { stroke: WTEXT, width: 6 });
      sv(gg, 'circle', { cx: GX, cy: GY, r: 11, fill: C.pat });
      const gq = gpt(qd), gqc = sv(gg, 'circle', { cx: gq[0], cy: gq[1], r: 10, fill: C.ink });
      show(tl, gqc, T.first + 3.3, 0.3);
      const gl1 = rich(box(root, GX - 14, GY + 12), [it('p', C.pat)], 44);
      const gl2 = rich(box(root, gq[0] - 10, gq[1] + 8), [it('q')], 44);
      let sPk = 0; for (let i = 0; i <= 400; i++) { const s = qe * i / 400; if (fq(s) > fq(sPk)) sPk = s; }
      const pk = gpt(sPk);
      const lUp = label(root, pk[0] - 30, GY - 146, 'dry', { fontSize: '34px', color: C.good });
      const leader = stroke(gg, C.good, 2.5, { d: `M ${pk[0]} ${GY - 96} L ${pk[0]} ${pk[1] - 10}` });
      tl.set(leader, { o: 0 }, 0); tl.to(leader, { o: 1 }, T.first + 1.3, 0.4);
      const lDn = label(root, GX + 30, GY + 150, 'under water', { fontSize: '34px', color: WTEXT });
      tl.set(gg, { o: 0 }, 0); tl.to(gg, { o: 1 }, T.first - 0.1, 0.5);
      fadeIn(tl, gl1, T.first, 0.4, 6); fadeIn(tl, gl2, T.first + 2.6, 0.4, 6);
      tl.to(gUp, { draw: 1 }, T.first + 0.1, 0.8, E.out);
      tl.to(gDn, { draw: 1 }, T.first + 2.6, 0.8, E.out);
      fadeIn(tl, lUp, T.first + 1.3, 0.5, 8);
      fadeIn(tl, lDn, T.first + 3.2, 0.5, 8);
      // "On every line, there is a distance that stays dry.": the graph and q leave
      fadeIn(tl, wl, T.first, 0.4, 6);
      for (const e of [gg, gl1, gl2, lUp, lDn, qLab, wl]) fadeOut(tl, e, T.each - 0.4, 0.35, -8);
      for (const e of [qDot, qLine, qGreen, qCyan]) tl.to(e, { o: 0 }, T.each - 0.4, 0.35);
      // the statement that holds, with a tick; "But a local minimum needs one distance that works for every line:
      // the same words, in the other order.": under it the same words swapped, with a cross. The two phrases that
      // trade places are amber in both.
      const col = box(root, 1040, 270, { display: 'grid', gridTemplateColumns: 'auto auto', alignItems: 'center', columnGap: '28px', rowGap: '52px' });
      const A = t => [t, C.pat];
      const s1 = rich(col, ['for ', A('every line'), ',\nthere is ', A('a dry distance')], 52, { lineHeight: 1.3 });
      const m1 = div(col, { width: '66px', height: '66px' }); mark(tl, m1, 50, true, T.each + 3.3);
      const s2 = rich(col, ['there is ', A('a dry distance'), ',\nfor ', A('every line')], 52, { lineHeight: 1.3 });
      const m2 = div(col, { width: '66px', height: '66px' }); mark(tl, m2, 50, false, T.order + 5.8);
      slot(tl, s1, T.each + 0.2, T.test - 0.4);
      slot(tl, s2, T.order + 1.1, T.test - 0.4);
      for (const m of [m1, m2]) fadeOut(tl, m, T.test - 0.4, 0.3, -8);
      // "And here, the dry distance shrinks to nothing as the line turns toward the pipe."
      for (const ln of FIVE) for (const e of [ln.ink, ln.g, ln.end]) tl.to(e, { o: 0.32 }, T.inf - 0.1, 0.5);
      const shr = label(root, 1040, 670, '', { fontSize: '34px', color: C.good, lineHeight: 1.45 });
      shr.textContent = 'the dry distance\nshrinks to nothing'; shr._text0 = shr._shown = shr.textContent;
      slot(tl, shr, T.inf + 1.1, T.test - 0.4);

      // "The pinholes were the same: each line stayed clear of them up to some distance, but no one distance worked
      // for every line.": a small top view of the pinhole spiral, bottom right, with two lines through O, each green
      // out to the one pinhole it meets (at angle 2, distance 1/2: long; at angle 7, distance 1/7: short)
      {
        const T2 = T.pin, IX = 1716, IY = 700, IS = 240, IR = 150;
        const ps = svgLayer(root), pg = sv(ps, 'g');
        const clipId = 'm-pin-clip';
        sv(sv(sv(ps, 'defs'), 'clipPath', { id: clipId }), 'circle', { cx: IX, cy: IY, r: IR });
        sv(pg, 'circle', { cx: IX, cy: IY, r: IR, fill: alpha(C.panel, 0.9), stroke: C.line, 'stroke-width': 1.5 });
        const inner = sv(pg, 'g', { 'clip-path': `url(#${clipId})` });
        const at = (x, y) => [IX + IS * x, IY - IS * y];
        for (const r of [0.2, 0.4, 0.6]) sv(inner, 'circle', { cx: IX, cy: IY, r: r * IS, fill: 'none', stroke: C.ink, 'stroke-width': 1.5, 'stroke-opacity': 0.14 });
        for (let n = 1; n <= 160; n++) { const q = at(Math.cos(n) / n, Math.sin(n) / n); sv(inner, 'circle', { cx: q[0], cy: q[1], r: clamp(0.2 * IS / n, 0.8, 4.5), fill: C.ink, 'fill-opacity': 0.8 }); }
        const lines = [2, 7].map((n, k) => {
          const g = sv(inner, 'g'), u = [Math.cos(n), Math.sin(n)], d = 1 / n;
          stroke(g, C.ink, 2.5, { d: segD2(at(-1.3 * u[0], -1.3 * u[1]), at(1.3 * u[0], 1.3 * u[1])) });
          const dg = d - 9 / IS;
          stroke(g, C.good, 6, { d: segD2(at(-dg * u[0], -dg * u[1]), at(dg * u[0], dg * u[1])) });
          const h = at(d * u[0], d * u[1]);
          sv(g, 'circle', { cx: h[0], cy: h[1], r: 7, fill: 'none', stroke: C.bad, 'stroke-width': 2.5 });
          tl.set(g, { o: 0 }, 0); tl.to(g, { o: 1 }, T2 + 1.8 + 0.7 * k, 0.5);
          return g;
        });
        sv(inner, 'circle', { cx: IX, cy: IY, r: 6, fill: C.pat });
        const pl2 = clab(root, IY + IR + 14, 'the pinholes', 24, { width: '400px', left: (IX - 200) + 'px' });
        tl.set(pg, { o: 0 }, 0); tl.to(pg, { o: 1 }, T2 + 0.1, 0.5);
        fadeIn(tl, pl2, T2 + 0.3, 0.5, 6);
        tl.to(pg, { o: 0 }, T.test - 0.4, 0.35); fadeOut(tl, pl2, T.test - 0.4, 0.3, -6);
      }

      // "This is also why the second derivative test asks for positive definite, and not merely semidefinite:"
      const th = flabel(box(root, 1040, 150), 'second derivative test', 40, { color: C.ink });
      fadeIn(tl, th, T.test + 1.0, 0.6, 12);
      const tcol = box(root, 1040, 222, { display: 'grid', gridTemplateColumns: 'auto auto', alignItems: 'center', columnGap: '22px', rowGap: '12px' });
      const r1 = flabel(tcol, 'positive definite', 40, { color: C.good });
      const k1 = div(tcol, { width: '58px', height: '58px' }); mark(tl, k1, 42, true, T.test + 3.6);
      const r2 = flabel(tcol, 'semidefinite', 40, { color: C.bad });
      const k2 = div(tcol, { width: '58px', height: '58px' }); mark(tl, k2, 42, false, T.test + 5.8);
      fadeIn(tl, r1, T.test + 3.2, 0.5, 10);
      fadeIn(tl, r2, T.test + 5.4, 0.5, 10);
      // "at this point, the second derivative along the tangent is zero.": the second derivatives of f at p, a 2 × 2
      // matrix (f_xx = 16, f_xy = 0, f_yy = 0), its lower-right 0 marked amber, with a leader to the tangent at p in
      // the plan (drawn amber there)
      const HX = 1070, HY = 410, CW = 112, CH = 78;   // the matrix's top left, and its cells
      const hs = svgLayer(root), hg = sv(hs, 'g'), lead = sv(hs, 'g');
      const hm = box(root, HX, HY, { display: 'grid', gridTemplateColumns: `${CW}px ${CW}px`, gridAutoRows: CH + 'px' });
      for (const v of ['16', '0', '0', '0']) rich(hm, v, 56, { textAlign: 'center' });
      const zm = sv(hg, 'rect', { x: HX + CW + 20, y: HY + CH + 4, width: CW - 40, height: CH - 6, rx: 10, fill: alpha(C.pat, 0.14), stroke: alpha(C.pat, 0.8), 'stroke-width': 2 });
      for (const [x, sg] of [[HX - 6, 1], [HX + 2 * CW + 6, -1]]) stroke(hg, C.ink, 3, { d: `M ${x + sg * 10} ${HY} Q ${x - sg * 16} ${HY + CH} ${x + sg * 10} ${HY + 2 * CH}` });
      const hl = flabel(box(root, HX + 2 * CW + 50, HY + 36), 'the second\nderivatives at ', 32, { lineHeight: 1.45 });
      spans(hl, [ML('p', C.pat)]);
      fadeIn(tl, hm, T.hess + 0.1, 0.6, 12);
      tl.set(hg, { o: 0 }, 0); tl.to(hg, { o: 1 }, T.hess + 0.1, 0.6);
      tl.set(zm, { o: 0 }, 0); tl.to(zm, { o: 1 }, T.hess + 1.9, 0.4);
      fadeIn(tl, hl, T.hess + 0.5, 0.6, 10);
      // the leader: from the marked 0 down, and left to a point of the tangent near p, and up to it
      const pp = MB(1, 0), tx = pp[0] + 180, ly = 624, ex = HX + CW + CW / 2;
      stroke(lead, C.pat, 2.5, { d: `M ${ex} ${HY + 2 * CH + 4} L ${ex} ${ly} L ${tx} ${ly} L ${tx} ${pp[1] + 8}` });
      sv(lead, 'circle', { cx: tx, cy: pp[1], r: 7, fill: C.pat });
      tl.set(lead, { o: 0 }, 0); tl.to(lead, { o: 1 }, T.hess + 2.0, 0.5);
      const al = flabel(box(root, ex - 40, ly + 22), 'along the tangent: 0', 32, { color: C.pat });
      fadeIn(tl, al, T.hess + 2.6, 0.5, 8);
    }
  });

  // ============================================ m_end ==========================================================
  scene('m_end', ({ tl, root, cue }) => {
    const t0 = cue('end');
    const a = cser(root, 300, 'A minimum on every line', 84);
    const b = cser(root, 410, 'is not a minimum.', 84);
    fadeIn(tl, a, t0 - 0.15, 0.8, 22);
    fadeIn(tl, b, t0 + 1.75, 0.8, 22);
    const c = clab(root, 592, 'a paradoxical local minimum · jules jacobs', 32);
    const d = clab(root, 646, 'julesjacobs.com', 32);
    fadeIn(tl, c, t0 + 3.0, 0.6, 10);
    fadeIn(tl, d, t0 + 3.3, 0.6, 10);
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
window.CAPTIONS = [[1.9, 4.42, "Stand at a point on a hilly surface,"], [4.46, 6.9, "and suppose that every straight line through it"], [6.94, 9.86, "goes uphill, in both directions."], [9.9, 10.82, "That means:"], [10.86, 12.82, "take a step along any line,"], [12.86, 15.22, "as small as you like, but not zero,"], [15.26, 18.58, "and you end up strictly higher than where you started."], [18.62, 20.66, "Is the point a local minimum?"], [20.7, 22.26, "Obviously, yes."], [22.3, 24.5, "Every direction is a straight line,"], [24.54, 26.18, "so whichever way you step,"], [26.22, 29.54, "you go up, and nothing nearby can be lower."], [29.58, 32.21, "And yet, that is wrong."], [32.25, 34.53, "Here is one way it goes wrong."], [34.57, 35.81, "Take a bowl."], [35.85, 38.29, "Its bottom is as good a minimum as you could ask"], [38.33, 39.17, "for."], [39.21, 42.05, "Now push single points of the surface down,"], [42.09, 43.68, "below the bottom."], [43.72, 45.49, "The first at distance one,"], [45.53, 47.45, "turned by one radian."], [47.49, 49.49, "The next at distance a half,"], [49.53, 51.49, "turned by two radians."], [51.53, 54.69, "Then at distance a third, turned by three."], [54.73, 57.17, "And so on, spiralling in."], [57.21, 60.21, "Now take any straight line through the bottom."], [60.25, 63.01, "It hits at most one of these points."], [63.05, 65.25, "For two of them to lie on the same line,"], [65.29, 67.89, "a whole number of radians would have to be a multiple"], [67.93, 70.85, "of pi, and pi is irrational."], [70.89, 74.01, "So near the bottom, the line runs on the untouched"], [74.05, 76.85, "bowl, and every step goes up."], [76.89, 79.49, "And yet, as close to the bottom as you like,"], [79.53, 81.39, "there are points below it."], [81.43, 83.31, "That feels like cheating:"], [83.35, 85.63, "the holes have no width at all."], [85.67, 87.51, "And it is fragile."], [87.55, 89.12, "Give every hole some width,"], [89.16, 90.95, "and it stops working."], [90.99, 93.63, "Seen from the bottom, a hole with width blocks"], [93.67, 95.79, "a whole wedge of directions."], [95.83, 99.03, "The wedges keep coming, round and round."], [99.07, 100.51, "However thin you make them,"], [100.55, 103.55, "some line passes through infinitely many:"], [103.59, 106.35, "hole after hole, all the way in."], [106.39, 108.86, "On that line, you do not go up:"], [108.9, 110.67, "however short a step you allow,"], [110.71, 113.03, "some step lands in a hole."], [113.07, 116.07, "So low ground with any width cannot be scattered"], [116.11, 117.83, "around the point."], [117.87, 120.15, "If every straight line is to go up,"], [120.19, 123.27, "the only hope is to slip the low ground in along"], [123.31, 125.59, "a curve, thinner and thinner,"], [125.63, 128.79, "so that every straight line leaves it at once."], [128.83, 131.67, "Then there would be a whole path that goes strictly"], [131.71, 134.07, "down, from the very first step."], [134.11, 135.3, "You can picture it:"], [135.34, 138.23, "a bowl, with a crevasse carved into it along a"], [138.27, 139.75, "curved path."], [139.79, 142.07, "But here is the second surprise."], [142.11, 143.91, "Nothing needs to be carved."], [143.95, 146.63, "The surface can be perfectly smooth."], [146.67, 148.95, "To see how, take a half-pipe,"], [148.99, 150.95, "and bend it into a ring."], [150.99, 153.19, "Its lowest points form a circle,"], [153.23, 154.95, "all at the same height."], [154.99, 156.55, "Stand at one of them."], [156.59, 159.27, "Any straight step climbs the wall."], [159.31, 161.51, "Even a step along the pipe climbs,"], [161.55, 164.42, "because the pipe curves away under you."], [164.46, 167.67, "To stay level, you have to follow the circle."], [167.71, 169.51, "Now bend the pipe downward,"], [169.55, 172.79, "ever so gently, away from where you stand."], [172.83, 176.1, "The circle that was level now goes downhill."], [176.14, 178.31, "But a straight step still climbs,"], [178.35, 180.07, "even along the tangent."], [180.11, 182.26, "The tangent drifts off the circle,"], [182.3, 185.27, "and up the wall, and the wall rises faster than"], [185.31, 186.79, "the bend falls."], [186.83, 189.67, "This is why the bend has to be so gentle."], [189.71, 192.55, "Along the tangent, the wall rises only like the"], [192.59, 194.39, "fourth power of the step."], [194.43, 197.27, "So the bend must fall more slowly than that:"], [197.31, 199.83, "like the fourth power with a smaller factor,"], [199.87, 202.07, "or like a higher power."], [202.11, 203.94, "Had we simply tilted the pipe,"], [203.98, 206.15, "the tangent would have gone down with it."], [206.19, 208.26, "So every straight line goes up,"], [208.3, 210.31, "and the circle goes down."], [210.35, 212.15, "Now fill the pipe with water,"], [212.19, 214.31, "up to the level of where you stand."], [214.35, 217.43, "The circle goes under water on both sides."], [217.47, 220.87, "But every straight line starts out on dry ground."], [220.91, 224.07, "Seen from above, this is the picture we began with:"], [224.11, 226.15, "straight lines that all go up,"], [226.19, 229.25, "and one curved path that goes down."], [229.29, 232.57, "The surface can even be a polynomial."], [232.61, 234.29, "This part is the pipe:"], [234.33, 238.37, "zero on the unit circle, and rising on both sides."], [238.41, 240.13, "This part is the bend."], [240.17, 242.48, "On the circle, the pipe is zero,"], [242.52, 244.85, "and the bend makes the height negative."], [244.89, 247.33, "On the tangent line, the pipe wins,"], [247.37, 248.83, "two to one."], [248.87, 252.03, "So what was wrong with the obvious argument?"], [252.07, 254.99, "Every point under water does lie on a straight"], [255.03, 256.8, "line from where you stand."], [256.84, 259.15, "But along that line you first climb,"], [259.19, 263.23, "on dry ground, and only then come down to the water."], [263.27, 266.91, "On every line, there is a distance that stays dry."], [266.95, 269.71, "But a local minimum needs one distance that works"], [269.75, 271.15, "for every line:"], [271.19, 273.87, "the same words, in the other order."], [273.91, 277.07, "And here, the dry distance shrinks to nothing as"], [277.11, 279.66, "the line turns toward the pipe."], [279.7, 281.47, "The pinholes were the same:"], [281.51, 284.75, "each line stayed clear of them up to some distance,"], [284.79, 288.03, "but no one distance worked for every line."], [288.07, 291.15, "This is also why the second derivative test asks"], [291.19, 294.59, "for positive definite, and not merely semidefinite:"], [294.63, 297.03, "at this point, the second derivative along the"], [297.07, 299.05, "tangent is zero."], [299.09, 303.27, "A minimum on every line is not a minimum."]];
