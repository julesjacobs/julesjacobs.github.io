// A small view of the paper's algorithm for its web page: a program (editable), the stable pattern of each of its
// blocks, and the program the algorithm makes of it. The engine and the paper's notation are the paper demo's
// (CHIPDEMO/src/core/api.ts and src/paper/), unchanged; this file is only the view.

import { parse, specialize } from '@chipdemo/core/api.ts';
import { EXAMPLES } from '@chipdemo/paper/examples.ts';
import { pieces, type Role } from '@chipdemo/paper/highlight.ts';
import { show, type Clause, type Shown } from '@chipdemo/paper/show.ts';
import { lineOf, toEngine } from '@chipdemo/paper/syntax.ts';
import { PICKS } from './examples.ts';
import { CSS } from './style.ts';

export interface Options {
  /** The example shown first (an id from the list); the first by default. */
  readonly example?: string;
  /** The examples offered, by id, in order; the widget's own list by default. */
  readonly examples?: readonly string[];
}

type Result = { readonly ok: true; readonly shown: Shown } | { readonly ok: false; readonly error: string };

/** One run: the paper's text, translated, parsed and specialized with Figure 5's schedule, as the paper demo runs it. */
function run(source: string): Result {
  try {
    const tr = toEngine(source);
    const parsed = parse(tr.text);
    if (parsed.program === undefined || parsed.errors.some((e) => e.severity === 'error')) {
      const e = parsed.errors.find((x) => x.severity === 'error');
      const lines = source.replace(/\s+$/, '').split('\n').length;
      return { ok: false, error: e === undefined ? 'The program could not be read.' : `Line ${Math.min(lineOf(tr.text, e.span.from), lines)}: ${e.message}` };
    }
    const r = specialize(parsed.program, { schedule: 'finish' });
    if (r.stopped !== undefined) return { ok: false, error: `The run reached its bound on ${r.stopped.kind}.` };
    return { ok: true, shown: show(r, parsed.program, tr) };
  } catch (e) {
    return { ok: false, error: `This program could not be run: ${e instanceof Error ? e.message : String(e)}` };
  }
}

const el = <K extends keyof HTMLElementTagNameMap>(tag: K, attrs: Record<string, string> = {}, ...kids: (Node | string)[]): HTMLElementTagNameMap[K] => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  e.append(...kids);
  return e;
};

/** A program's text, coloured by role (calmly: colour only, so the layer under the editor keeps its metrics). */
function code(text: string, labels: ReadonlySet<string>): DocumentFragment {
  const f = document.createDocumentFragment();
  for (const p of pieces(text, labels)) {
    const cls = p.role === 'keyword' ? 'k' : p.role === 'comment' || p.role === 'annot' ? 'c' : p.role === 'label' ? 'l' : undefined;
    f.append(cls === undefined ? p.text : el('span', { class: `spw-${cls}` }, p.text));
  }
  return f;
}

/**
 * A pattern, the page's way: what it asserts of a value (a constant, a constructor, a closure's label, a tuple's
 * parentheses and commas) amber, a binder `?x` teal, a plain name violet; the block's own name and the punctuation
 * of calls in the text's colour.
 */
function pattern(text: string, labels: ReadonlySet<string>): DocumentFragment {
  const f = document.createDocumentFragment();
  const kind = (r: Role | undefined, first: boolean): string | undefined => {
    if (r === 'number' || r === 'ctor' || (r === 'label' && !first)) return 'a';
    if (r === 'hole') return 'b';
    if (r === 'rigid' || r === 'cont') return 'n';
    return undefined;
  };
  // a `(` is a tuple's unless a name, a constructor or a closure's `⟩` is right before it (a call, an application)
  const tuples: boolean[] = [];
  let prev = '';
  let plain = '';
  const flush = (): void => {
    if (plain !== '') f.append(plain);
    plain = '';
  };
  pieces(text, labels, true).forEach((p, i) => {
    const k = kind(p.role, i === 0);
    if (k !== undefined || p.role !== undefined) {
      flush();
      f.append(k === undefined ? p.text : el('span', { class: `spw-${k}` }, p.text));
      prev = p.text.slice(-1);
      return;
    }
    for (const c of p.text) {
      let tuple = false;
      if (c === '(') {
        tuple = !/[\p{L}\p{N}_'⟩₀-₉]/u.test(prev);
        tuples.push(tuple);
      } else if (c === ')') tuple = tuples.pop() ?? false;
      else if (c === ',') tuple = tuples[tuples.length - 1] ?? false;
      if (tuple) {
        flush();
        f.append(el('span', { class: 'spw-a' }, c));
      } else plain += c;
      if (c !== ' ') prev = c;
    }
  });
  flush();
  return f;
}

const HEAD = /^\s*(?:where\s+)?[\p{L}_][\p{L}\p{N}_'₀-₉]*\s*(?:⟨[^⟩]*⟩)?\s*\(.*\)\s*=(?!=)/u;

/** The lines (1-based, inclusive) of `name`'s definition in a text: its head line to the line before the next head. */
function linesOf(text: string, name: string): readonly [number, number] | undefined {
  const lines = text.split('\n');
  const esc = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const own = new RegExp(`^\\s*(?:where\\s+)?${esc}\\s*[⟨(]`, 'u');
  const from = lines.findIndex((l) => own.test(l) && HEAD.test(l));
  if (from < 0) return undefined;
  let to = from;
  while (to + 1 < lines.length && !HEAD.test(lines[to + 1]!) && !/^\s*@/.test(lines[to + 1]!) && lines[to + 1]!.trim() !== '') to++;
  return [from + 1, to + 1];
}

let styled = false;
let uid = 0;

export function mount(root: HTMLElement, options: Options = {}) {
  if (!styled) {
    styled = true;
    document.head.append(el('style', { 'data-stable-patterns': '' }, CSS));
  }
  const n = ++uid;
  const ids = options.examples ?? PICKS.map((p) => p.id);
  const picks = ids.flatMap((id) => {
    const ex = EXAMPLES.find((e) => e.id === id);
    if (ex === undefined) return [];
    const own = PICKS.find((p) => p.id === id);
    return [{ id, name: own?.name ?? ex.title, line: own?.line ?? '', note: ex.note, source: ex.source.replace(/\s+$/, '') }];
  });

  // --- the parts
  const chips = el('div', { class: 'spw-chips', role: 'group', 'aria-label': 'Examples' });
  const line = el('p', { class: 'spw-line' });
  const noteText = el('p', {});
  const note = el('details', { class: 'spw-note' }, el('summary', {}, 'Differs from the paper'), noteText);

  const source = el('textarea', {
    class: 'spw-code spw-edit',
    id: `spw-src-${n}`,
    spellcheck: 'false',
    autocapitalize: 'off',
    autocomplete: 'off',
    autocorrect: 'off',
    wrap: 'off',
    rows: '1',
    'aria-describedby': `spw-err-${n}`,
  });
  const under = el('pre', { class: 'spw-code spw-under', 'aria-hidden': 'true' });
  const inBand = el('div', { class: 'spw-band', hidden: '' });
  const inGrid = el('div', { class: 'spw-grid' }, inBand, under, source);
  const inBox = el('div', { class: 'spw-box spw-input' }, inGrid);
  const error = el('p', { class: 'spw-error', id: `spw-err-${n}`, role: 'status' });

  const list = el('div', { class: 'spw-patterns', 'aria-live': 'polite', 'aria-labelledby': `spw-h-pat-${n}` });

  const output = el('pre', { class: 'spw-code spw-out' });
  const outBand = el('div', { class: 'spw-band', hidden: '' });
  const outGrid = el('div', { class: 'spw-grid' }, outBand, output);
  const outBox = el('div', { class: 'spw-box spw-output', 'aria-live': 'polite', 'aria-labelledby': `spw-h-out-${n}`, tabindex: '0', role: 'region' }, outGrid);

  const part = (cls: string, id: string, title: string, ...body: Node[]): HTMLElement =>
    el('section', { class: `spw-part ${cls}` }, cls === 'spw-p-in' ? el('label', { class: 'spw-label', id, for: `spw-src-${n}` }, title) : el('div', { class: 'spw-label', id }, title), ...body);

  const view = el(
    'div',
    { class: 'spw-view' },
    part('spw-p-in', `spw-h-in-${n}`, 'Program', inBox, error),
    part('spw-p-pat', `spw-h-pat-${n}`, 'Stable patterns', list),
    part('spw-p-out', `spw-h-out-${n}`, 'Output', outBox),
  );
  root.classList.add('spw');
  root.replaceChildren(el('div', { class: 'spw-top' }, chips, line, note), view);

  // --- state
  let current = picks.find((p) => p.id === options.example) ?? picks[0];
  let labels: ReadonlySet<string> = new Set();
  let shown: Shown | undefined;
  let timer: ReturnType<typeof setTimeout> | undefined;
  let pending: Promise<void> = Promise.resolve();
  let done: () => void = () => {};

  const buttons = picks.map((p) => {
    const b = el('button', { type: 'button', class: 'spw-chip', 'aria-pressed': 'false' }, p.name);
    b.addEventListener('click', () => select(p.id));
    chips.append(b);
    return b;
  });

  const paint = (): void => {
    const text = source.value;
    const own = new Set([...labels, ...toEngine(text).blocks]);
    // (a last empty line has its height too)
    under.replaceChildren(code(text.endsWith('\n') || text === '' ? text + ' ' : text, own));
  };

  const band = (b: HTMLElement, pre: HTMLElement, range: readonly [number, number] | undefined): void => {
    if (range === undefined) {
      b.hidden = true;
      return;
    }
    const cs = getComputedStyle(pre);
    const lh = parseFloat(cs.lineHeight) || 20;
    const top = parseFloat(cs.paddingTop) || 0;
    b.hidden = false;
    b.style.top = `${top + (range[0] - 1) * lh}px`;
    b.style.height = `${(range[1] - range[0] + 1) * lh}px`;
  };
  const point = (c: Clause | undefined): void => {
    band(inBand, under, c === undefined || c.made ? undefined : linesOf(source.value, c.block));
    band(outBand, output, c === undefined ? undefined : linesOf(output.textContent ?? '', c.name));
  };

  const row = (c: Clause, many: boolean): HTMLElement => {
    const r = el('div', { class: 'spw-row' });
    if (many) r.append(el('span', { class: 'spw-ver' }, c.name, ...(c.context === undefined ? [] : [el('span', { class: 'spw-ctx' }, ` ${c.context}`)])));
    r.append(el('code', { class: 'spw-pat' }, pattern(c.head, labels)));
    r.addEventListener('mouseenter', () => point(c));
    r.addEventListener('mouseleave', () => point(undefined));
    return r;
  };

  const render = (res: Result): void => {
    if (!res.ok) {
      error.textContent = res.error;
      list.classList.add('spw-stale');
      outBox.classList.add('spw-stale');
      return;
    }
    error.textContent = '';
    list.classList.remove('spw-stale');
    outBox.classList.remove('spw-stale');
    const same = shown !== undefined && shown.output[shown.written] === res.shown.output[res.shown.written] && shown.clauses.map((c) => c.head).join('\n') === res.shown.clauses.map((c) => c.head).join('\n');
    shown = res.shown;
    labels = new Set(res.shown.labels);
    paint();
    if (same) return;
    point(undefined);
    // a row per version, in the program's order; the blocks the translation to CPS makes after them, apart
    const count = new Map<string, number>();
    for (const c of shown.clauses) count.set(c.block, (count.get(c.block) ?? 0) + 1);
    // In direct style, a block the translation to CPS makes is listed only where the output or the program names it
    // (an escaping λ₁), as an ordinary row, its continuation left out where it is a binder, as the output prints it;
    // the others name blocks the reader can't see. In CPS, all are listed, apart.
    const direct = shown.written === 'direct';
    const text = `${source.value}\n${shown.output[shown.written]}`;
    const named = (c: Clause): boolean => new RegExp(`(?<![\\p{L}\\p{N}_'₀-₉])${c.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\p{L}\\p{N}_'₀-₉])`, 'u').test(text);
    const written = shown.clauses.filter((c) => !c.made || (direct && named(c))).map((c) => (c.made ? { ...c, head: c.head.replace(/; \?[\p{L}\p{N}_'₀-₉]+\)$/u, ')') } : c));
    const made = direct ? [] : shown.clauses.filter((c) => c.made);
    const rows: Node[] = written.map((c) => row(c, (count.get(c.block) ?? 0) > 1));
    if (made.length > 0) rows.push(el('div', { class: 'spw-made' }, el('span', { class: 'spw-sub' }, 'made by the translation to CPS'), ...made.map((c) => row(c, (count.get(c.block) ?? 0) > 1))));
    list.replaceChildren(...rows);
    output.replaceChildren(code(shown.output[shown.written], labels));
    for (const x of [list, output]) {
      x.classList.remove('spw-fresh');
      void x.offsetWidth;
      x.classList.add('spw-fresh');
    }
  };

  const update = (delay: number): void => {
    if (timer !== undefined) clearTimeout(timer);
    else pending = new Promise<void>((resolve) => (done = resolve));
    timer = setTimeout(() => {
      timer = undefined;
      render(run(source.value));
      done();
    }, delay);
  };

  const select = (id: string): void => {
    const p = picks.find((x) => x.id === id);
    if (p === undefined) return;
    current = p;
    buttons.forEach((b, i) => b.setAttribute('aria-pressed', String(picks[i] === p)));
    line.textContent = p.line;
    line.hidden = p.line === '';
    line.classList.remove('spw-off');
    note.classList.remove('spw-off');
    noteText.textContent = p.note ?? '';
    note.hidden = p.note === undefined;
    note.open = false;
    source.value = p.source;
    paint();
    update(0);
  };

  source.addEventListener('input', () => {
    // the line says what the example's result shows, not the reader's own program's: dimmed (not hidden, so that
    // nothing below it moves) while the text is another
    const other = current === undefined || source.value !== current.source;
    line.classList.toggle('spw-off', other);
    note.classList.toggle('spw-off', other);
    paint();
    update(300);
  });

  if (current !== undefined) select(current.id);

  return {
    select,
    /** Resolves once no run is waiting. */
    idle: (): Promise<void> => (timer === undefined ? Promise.resolve() : pending),
  };
}
