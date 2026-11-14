// The widget's styles, every rule under .spw (the element it is mounted in), injected once by the script.
// From 560 px of widget: the program at full width, under it the patterns (36 %) beside the output; else stacked.

export const CSS = `
.spw{container-type:inline-size;--spw-line:#e3e5e9;--spw-panel:#f3f4f6;--spw-quiet:#5f6672;--spw-text:#262a30;
--spw-mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;color:var(--spw-text);min-width:0}
.spw *,.spw *::before,.spw *::after{box-sizing:border-box}
.spw-top{margin:0 0 14px}
.spw-chips{display:flex;flex-wrap:wrap;gap:6px}
.spw-chip{font:inherit;font-size:13px;line-height:1.3;padding:4px 10px;border:1px solid var(--spw-line);border-radius:6px;
background:#fff;color:var(--spw-quiet);cursor:pointer}
.spw-chip:hover{border-color:#c4c9d1;color:var(--spw-text)}
.spw-chip[aria-pressed=true]{background:var(--spw-text);border-color:var(--spw-text);color:#fff}
.spw-chip:focus-visible,.spw-box:focus-visible{outline:2px solid #0d6f8a;outline-offset:1px}
.spw-line{margin:10px 0 0;font-size:14.5px;line-height:1.5;color:#3b4049}
.spw-note{margin:4px 0 0;font-size:13px;line-height:1.45;color:var(--spw-quiet)}
.spw-note summary{cursor:pointer;width:max-content;max-width:100%}
.spw-note p{margin:4px 0 0}
.spw-view{display:grid;gap:14px 16px;grid-template-columns:minmax(0,1fr);
grid-template-areas:"in" "pat" "out"}
@container (min-width:560px){.spw-view{grid-template-columns:minmax(0,36fr) minmax(0,64fr);grid-template-areas:"in in" "pat out"}}
.spw-p-in{grid-area:in}.spw-p-pat{grid-area:pat}.spw-p-out{grid-area:out}
.spw-part{min-width:0;margin:0;display:flex;flex-direction:column;align-self:stretch}
.spw-label{display:block;font-size:12.5px;line-height:1.4;color:var(--spw-quiet);margin:0 0 5px}
.spw-box{flex:1 1 auto;position:relative;border:1px solid var(--spw-line);border-radius:6px;background:var(--spw-panel);overflow:auto;max-width:100%}
.spw-input{background:#fff}
.spw-input:focus-within{border-color:#aab1bb}
.spw-grid{position:relative;display:grid;min-width:100%;min-height:100%;width:max-content;isolation:isolate}
.spw-code{grid-area:1/1;margin:0;padding:10px 12px;font-family:var(--spw-mono);font-size:13.5px;line-height:1.55;
white-space:pre;tab-size:4;letter-spacing:0;font-variant-ligatures:none;border:0;position:relative;z-index:1;background:transparent;color:var(--spw-text)}
.spw-edit{display:block;width:100%;height:100%;min-height:0;resize:none;overflow:hidden;outline:none;color:transparent;
caret-color:var(--spw-text);-webkit-text-fill-color:transparent;overflow-wrap:normal}
.spw-edit::selection{background:rgba(13,111,138,.2);-webkit-text-fill-color:transparent}
.spw-band{position:absolute;left:0;right:0;z-index:0;background:rgba(91,70,180,.08);pointer-events:none}
.spw-band[hidden]{display:none}
.spw-k{color:#6b7280}.spw-l{color:#2b4c7e}.spw-c{color:#8b919c}
.spw-error:empty{display:none}
.spw-error{margin:5px 0 0;font-size:12.5px;line-height:1.4;color:#9b3b2b}
.spw-patterns{flex:1 1 auto;border:1px solid var(--spw-line);border-radius:6px;background:#fff;padding:9px 14px;overflow-x:auto}
.spw-row{display:flex;gap:10px;align-items:baseline;white-space:pre;border-radius:4px;margin:0 -6px;padding:1px 6px;cursor:default}
.spw-row:hover{background:rgba(91,70,180,.07)}
.spw-pat{font-family:var(--spw-mono);font-size:15px;line-height:1.75;color:var(--spw-text);background:none;padding:0}
.spw-ver{flex:none;font-family:var(--spw-mono);font-size:12.5px;color:var(--spw-quiet);min-width:3.5em}
.spw-pat{flex:none}
.spw-ctx{color:#8b919c}
.spw-made{margin-top:6px;padding-top:5px;border-top:1px solid var(--spw-line)}
.spw-made .spw-pat{font-size:13.5px;color:var(--spw-quiet)}
.spw-sub{display:block;font-size:12px;color:#8b919c;margin:0 0 1px}
.spw-a{color:#a85d00}.spw-b{color:#0d6f8a}.spw-n{color:#5b46b4}
.spw-stale{opacity:.45}
.spw-off{opacity:.4}
.spw-fresh{animation:spw-in .16s ease-out}
@keyframes spw-in{from{opacity:.35}}
@media (prefers-reduced-motion:reduce){.spw-fresh{animation:none}}
`;
