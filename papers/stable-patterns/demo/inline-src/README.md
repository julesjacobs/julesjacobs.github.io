# The inline widget's source

`../inline.js` is built from these files and the paper demo's engine and notation (`Apps/ChipDemo/src/core/api.ts`, `src/paper/{examples,highlight,show,syntax,marks}.ts`, imported unchanged as `@chipdemo/…`). It is one minified IIFE, ASCII only, that injects its own CSS (every rule under `.spw`) and loads nothing.

    node build.mjs            # writes ../inline.js
    node check.mjs [dir]      # checks it in headless Chromium; screenshots into dir

`CHIPDEMO` is the ChipDemo folder (default `~/git/sep/Apps/ChipDemo`). The build uses the esbuild in `$CHIPDEMO/node_modules` when there is one, else the rolldown in `ROLLDOWN` (default: the Sep viewer's, `Sep/Cli/ui/node_modules/rolldown`). `check.mjs` takes `PLAYWRIGHT_CORE` and `CHROME` (default: the Sep viewer's playwright-core and the newest headless shell under `~/Library/Caches/ms-playwright`) and compares every example with `../examples.html`, the paper demo.

On the page:

    <div id="stable-patterns"></div>
    <script src="demo/inline.js"></script>
    <script>StablePatternsDemo.mount(document.getElementById('stable-patterns'))</script>

`mount(element, { example, examples })`: the first example shown, and the examples offered (ids from `examples.ts`, or any id of the paper demo's `examples.ts`). It returns `{ select(id), idle() }`.

- `widget.ts`: the view; `examples.ts`: the examples offered, their names and one line each; `style.ts`: the CSS.
