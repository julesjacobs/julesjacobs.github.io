// Checks the widget in a headless Chromium, from file://, with nothing but file: allowed to load:
//   node check.mjs [screenshot-dir]
// 1. every example's patterns and output equal the paper demo's (examples.html, its run's last step);
// 2. an edit re-runs it, and a program that doesn't parse keeps the last result, dimmed, with one error line;
// 3. nothing wider than its container at 868, 600 and 360, every program line fits at 868, and what scrolls;
//    screenshots at 868 and 360 (with a dir);
// 4. no console messages but logs, no page errors, no request but file:.
// PLAYWRIGHT_CORE (default: the Sep viewer's) and CHROME (default: the newest headless shell under
// ~/Library/Caches/ms-playwright) say what runs it.
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import fs from 'node:fs';
import os from 'node:os';

const require = createRequire(import.meta.url);
const pw = require(process.env.PLAYWRIGHT_CORE || process.env.HOME + '/git/sep/Sep/Cli/ui/node_modules/playwright-core');
const here = dirname(fileURLToPath(import.meta.url));
const demo = join(here, '..');
const shots = process.argv[2];

function chromePath() {
  if (process.env.CHROME) return process.env.CHROME;
  const base = join(os.homedir(), 'Library/Caches/ms-playwright');
  for (const d of fs.readdirSync(base).filter((d) => d.startsWith('chromium_headless_shell-')).sort().reverse()) {
    const sub = fs.readdirSync(join(base, d)).find((x) => x.startsWith('chrome-'));
    const p = sub && join(base, d, sub, 'chrome-headless-shell');
    if (p && fs.existsSync(p)) return p;
  }
  return undefined;
}

const browser = await pw.chromium.launch({ executablePath: chromePath() });
const problems = [];
const fail = (m) => { problems.push(m); console.log('FAIL', m); };

async function open(file, width = 1100) {
  const page = await browser.newPage({ viewport: { width, height: 900 }, deviceScaleFactor: Number(process.env.SCALE || 1) });
  page.on('console', (m) => { if (m.type() !== 'log' && m.type() !== 'debug') fail(`${file}: console ${m.type()}: ${m.text()}`); });
  page.on('pageerror', (e) => fail(`${file}: page error: ${e.message}`));
  await page.route('**/*', (r) => (r.request().url().startsWith('file:') ? r.continue() : (fail(`${file}: request ${r.request().url()}`), r.abort())));
  await page.goto('file://' + join(demo, file));
  return page;
}

// --- 1. the same as the paper demo
const ids = ['intro', 'numbering', 'unbox', 'all', 'app', 'fold-once', 'stream', 'escape', 'stack'];
const paper = await open('examples.html');
const mine = await open('inline-test.html');
const read = (page) => page.evaluate(async () => {
  await window.demo.idle();
  const rows = [...document.querySelectorAll('.spw-row')].map((r) => r.textContent);
  return { rows, output: document.querySelector('.spw-out').textContent, error: document.querySelector('.spw-error').textContent };
});
for (const id of ids) {
  await mine.evaluate((id) => window.demo.select(id), id);
  const m = await read(mine);
  await paper.selectOption('#example', id);
  const p = await paper.evaluate(async () => {
    await window.PaperDemo.idle();
    // (in direct style the widget leaves out the blocks the translation to CPS makes, which the paper demo marks .made)
    const cps = document.querySelector('#output-notation [aria-checked=true]')?.dataset.value === 'cps';
    // (unless the output or the program names them: then as the widget lists them, without a binder continuation)
    const text = document.querySelector('#source').value + '\n' + document.querySelector('#output').textContent;
    const named = (n) => new RegExp(`(?<![\\p{L}\\p{N}_'₀-₉])${n}(?![\\p{L}\\p{N}_'₀-₉])`, 'u').test(text);
    const rows = [...document.querySelectorAll('#state tbody tr')]
      .filter((r) => cps || !r.querySelector('th').classList.contains('made') || named(r.querySelector('th').textContent.trim().split(' ')[0]))
      .map((r) => (cps || !r.querySelector('th').classList.contains('made') ? r.querySelector('td').textContent : r.querySelector('td').textContent.replace(/; \?[\p{L}\p{N}_'₀-₉]+\)$/u, ')')));
    return { rows, output: document.querySelector('#output').textContent };
  });
  const a = [...m.rows].sort().join('\n');
  const b = [...p.rows].sort().join('\n');
  if (a !== b) fail(`${id}: patterns differ\n  widget: ${m.rows.join(' | ')}\n  paper:  ${p.rows.join(' | ')}`);
  if (m.output.trim() !== p.output.trim()) fail(`${id}: output differs\n${m.output}\n---\n${p.output}`);
  console.log(`${id}: ${m.rows.join('  |  ')}`);
}

// --- 2. an edit, then garbage
await mine.evaluate((id) => window.demo.select(id), 'intro');
await mine.locator('textarea').fill('main(?i) = loop(i, 1)\nloop(?i, ?x) = if i == 0 then x else loop(i - 1, x + 1)\n');
await mine.waitForTimeout(350);
let r = await read(mine);
if (!r.rows.includes('loop(?i, ?x)')) fail(`edit: loop's pattern is ${r.rows.join(' | ')}`);
if (!/loop\(\?i, \?x\)/.test(r.output)) fail(`edit: the output doesn't keep x:\n${r.output}`);
console.log('edit:', r.rows.join(' | '), '\n' + r.output);
const before = r;
await mine.locator('textarea').fill('main(?i) = loop(i, 1\nloop(?i, ?x) = if then');
await mine.waitForTimeout(350);
r = await read(mine);
const stale = await mine.evaluate(() => [document.querySelector('.spw-patterns').classList.contains('spw-stale'), document.querySelector('.spw-output').classList.contains('spw-stale')]);
if (r.error === '' || r.output !== before.output || r.rows.join() !== before.rows.join() || !stale.every(Boolean)) fail(`garbage: error '${r.error}', stale ${stale}`);
console.log('garbage:', r.error);
await mine.locator('textarea').fill('main(?i) = loop(i, 1)\nloop(?i, ?x) = if i == 0 then x else loop(i - 1, 2 - x)\n');
await mine.waitForTimeout(350);
r = await read(mine);
if (r.error !== '' || !r.rows.includes('loop(?i, 1)')) fail(`back: ${r.error} ${r.rows}`);
// a hover on a pattern marks its block in both programs
await mine.locator('.spw-row', { hasText: 'loop(?i, 1)' }).hover();
const bands = await mine.evaluate(() => [...document.querySelectorAll('.spw-band')].map((b) => (b.hidden ? null : [b.style.top, b.style.height])));
if (bands.some((b) => b === null)) fail(`hover: bands ${JSON.stringify(bands)}`);
console.log('hover bands:', JSON.stringify(bands));
await paper.close();
await mine.close();

// --- 3. widths: nothing wider than its container; at 868 (the page's), every program line fits
for (const width of [868, 600, 360]) {
  for (const id of ids) {
    const page = await open(`inline-test.html?width=${width}&example=${id}`, width + 40);
    await page.evaluate(() => window.demo.idle());
    const m = await page.evaluate(() => {
      const root = document.getElementById('demo');
      const over = [...root.querySelectorAll('*')].filter((e) => e.getBoundingClientRect().right > root.getBoundingClientRect().right + 0.5 && !e.closest('.spw-box, .spw-patterns'));
      const cut = (s) => { const b = document.querySelector(s); return b.scrollWidth > b.clientWidth + 1; };
      return { page: document.documentElement.scrollWidth, over: over.map((e) => e.className || e.tagName), input: cut('.spw-input'), output: cut('.spw-output'), patterns: cut('.spw-patterns') };
    });
    if (m.page > width + 40 || m.over.length > 0) fail(`${width} ${id}: wider than its container: ${JSON.stringify(m)}`);
    if (width === 868 && m.input) fail(`868 ${id}: a program line doesn't fit`);
    if (m.output || m.patterns || m.input) console.log(`${width} ${id}: scrolls:${m.input ? ' program' : ''}${m.patterns ? ' patterns' : ''}${m.output ? ' output' : ''}`);
    if (shots && [868, 360].includes(width) && ['intro', 'numbering', 'fold-once', 'stack'].includes(id)) {
      fs.mkdirSync(shots, { recursive: true });
      await page.locator('#demo').screenshot({ path: join(shots, `${id}-${width}.png`) });
    }
    await page.close();
  }
}

await browser.close();
console.log(problems.length === 0 ? 'all good' : `${problems.length} problem(s)`);
process.exit(problems.length === 0 ? 0 : 1);
