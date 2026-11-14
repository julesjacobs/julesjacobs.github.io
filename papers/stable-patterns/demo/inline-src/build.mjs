// Bundles inline-src/index.ts and the paper demo's engine and notation (CHIPDEMO/src/core, src/paper) into
// ../inline.js: one minified IIFE that loads nothing.
//   node build.mjs                 (CHIPDEMO defaults to ~/git/sep/Apps/ChipDemo)
// It uses the esbuild installed in CHIPDEMO/node_modules; where there is none, the rolldown in
// ROLLDOWN (default: the Sep viewer's, Sep/Cli/ui/node_modules/rolldown, beside CHIPDEMO).
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { dirname, join, resolve } from 'node:path';
import { existsSync, readFileSync, statSync, writeFileSync } from 'node:fs';

const here = dirname(fileURLToPath(import.meta.url));
const chip = resolve(process.env.CHIPDEMO || process.env.HOME + '/git/sep/Apps/ChipDemo');
const src = join(chip, 'src');
const entry = join(here, 'index.ts');
const out = join(here, '..', 'inline.js');
if (!existsSync(join(src, 'core', 'api.ts'))) throw new Error(`no ChipDemo sources at ${chip} (set CHIPDEMO)`);

// api.ts re-exports the full demo's gallery and the published analyses, which the widget doesn't use: their modules
// have no effects but their exports, so the bundler may leave them out (the paper demo's build does the same).
const unused = /[\\/]core[\\/](gallery|analyses|baselines)\.ts$/;
const banner = '/* Stable patterns widget: built from Apps/ChipDemo (src/core, src/paper) by inline-src/build.mjs. */';

const req = createRequire(join(chip, 'package.json'));
let esbuild;
try { esbuild = req('esbuild'); } catch {}

if (esbuild !== undefined) {
  await esbuild.build({
    entryPoints: [entry], outfile: out, bundle: true, format: 'iife', platform: 'browser', target: 'es2022',
    minify: true, legalComments: 'none', charset: 'ascii', banner: { js: banner }, alias: { '@chipdemo': src },
    plugins: [{ name: 'unused-core', setup(b) { b.onResolve({ filter: /^\.\/(gallery|analyses|baselines)\.ts$/ }, (a) => ({ path: join(a.resolveDir, a.path), sideEffects: false })); } }],
  });
  console.log('esbuild', esbuild.version);
} else {
  const rolldownDir = resolve(process.env.ROLLDOWN || join(chip, '..', '..', 'Sep', 'Cli', 'ui', 'node_modules', 'rolldown'));
  const { rolldown } = await import(join(rolldownDir, 'dist', 'index.mjs'));
  const bundle = await rolldown({
    input: entry, platform: 'browser', resolve: { alias: { '@chipdemo': src } },
    treeshake: { moduleSideEffects: (id) => !unused.test(id) }, logLevel: 'warn',
  });
  await bundle.write({ file: out, format: 'iife', minify: true, comments: { legal: false }, sourcemap: false });
  await bundle.close();
  // (ASCII only, as esbuild's charset: 'ascii' writes it, so that the page's encoding doesn't matter)
  const ascii = readFileSync(out, 'utf8').replace(/[^\x00-\x7f]/g, (c) => '\\u' + c.charCodeAt(0).toString(16).padStart(4, '0'));
  writeFileSync(out, banner + '\n' + ascii);
  console.log('rolldown', rolldownDir);
}
console.log(out, statSync(out).size, 'bytes');
