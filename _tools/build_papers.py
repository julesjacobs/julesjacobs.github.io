#!/usr/bin/env python3
"""Write a page for each paper in _data/papers.json (papers/<id>/index.html), and point the home page at them.

    python3 _tools/build_papers.py

A page shows the title, authors and venue, a short summary, buttons for what there is (paper, slides, code, ...),
the first page of the paper when papers/<id>/page1.jpg exists, a video when papers/<id>/film/ exists (with its
chapters when film/chapters.json lists them as [[seconds, title], ...], and a two-minute version under it when
papers/<id>/short/ exists), the abstract, talks and the BibTeX entry. The pages share papers/paper.css. On the home page (index.html) each
publication's title then links to its page and carries its one-line summary, and so do the names in the project
cards. Running it again changes nothing. papers/stable-patterns/ and papers/stackat-completeness/ are written by
hand and are left alone."""
import html, json, os, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
E = html.escape
# Lines of the project cards that are not papers, by the address their name links to.
TOOL_ONE = {
    "vox/": "Checks specifications at compile time on top of OxCaml, with refinement types and ghost proofs that are erased before code generation.",
    "https://github.com/oxcaml/oxcaml": "Jane Street's extension of OCaml for safe, fast systems programming; its modes track whether a value can escape its stack frame or be shared between threads.",
    "https://github.com/julesjacobs/petra": "A Petri-net reachability solver.",
    "https://github.com/julesjacobs/eggstract": "Extracts shared, acyclic DAGs from e-graphs, with a Rust library, a command-line tool and an optional CP-SAT backend.",
}
EXTRA_ONE = {"stable-patterns": "One analysis that finds what constant propagation, unboxing and closure analysis find separately."}


HOME_CSS = """    /* papers:begin */
    /* A publication: its title, who wrote it, then what it does in one line. */
    .pub .one { color: var(--fg); font-size: 15px; line-height: 1.45; margin: 2px 0 4px 0; }
    /* A project card lists its papers and tools one to a line, each with what it does under its name. */
    .plist li { margin-bottom: 7px; }
    .plist .ps { display: block; flex-basis: 100%; color: var(--muted); font-size: 14px; line-height: 1.4; margin: -2px 0 0 0; }
    /* papers:end */

"""


# Counting page views, and a video's first play, without cookies. The home page and the hand-written pages carry the same lines.
COUNT = '''  <!-- Page views are counted without cookies (GoatCounter); a video's player tells this page when it is first played. -->
  <script data-goatcounter="https://julesjacobs.goatcounter.com/count" async src="https://gc.zgo.at/count.js"></script>
  <script>
    window.addEventListener("message", function (e) {
      if (e.origin === location.origin && e.data && e.data.type === "video-play" && window.goatcounter && window.goatcounter.count)
        window.goatcounter.count({ path: "video-play" + location.pathname, title: "Video played: " + document.title, event: true });
    });
  </script>
'''

def url(u):
    return u if re.match(r"^(https?:|mailto:|/)", u) else "/" + u


def authors(p):
    out = []
    for a in p["authors"]:
        name = E(a["name"]) + (a.get("mark") or "")
        out.append(f'<a href="/">{name}</a>' if a["me"] else (f'<a href="{E(a["url"])}">{name}</a>' if a.get("url") else name))
    s = ", ".join(out[:-1]) + (" and " if len(out) > 1 else "") + out[-1]
    return s + (f' <span class="note">{E(p["equal_contribution_note"])}</span>' if p.get("equal_contribution_note") else "")


# The names of a paper's links (the same words as the home page's pills) and the order they are shown in.
LINK_ORDER = {k: i for i, k in enumerate([".pdf", "DOI", "arXiv", "crossref", "talk", "slides", "demo", "code"])}


def page(p):
    pid = p["id"]
    has_film = os.path.exists(os.path.join(ROOT, "papers", pid, "film", "index.html"))
    # One order everywhere, as on the home page: the paper, the video, the talk, its slides, a demo, the code.
    buttons = []
    for l in sorted(p["links"], key=lambda l: LINK_ORDER.get(l["label"], len(LINK_ORDER))):
        if l["label"] == ".pdf":
            buttons.insert(0, f'<a class="button primary" href="{E(url(l["url"]))}">Read the paper</a>')
        else:
            buttons.append(f'<a class="button" href="{E(url(l["url"]))}">{E(l["label"])}</a>')
    if has_film:
        buttons.insert(1, '<a class="button" href="#film">Watch the video</a>')
    awards = "".join(f'<span class="award">{E(a)}</span>' for a in p["awards"])
    thumb = ""
    if p.get("thumbnail") and p.get("pdf"):
        thumb = f'''    <a class="paper" href="{E(url(p["pdf"]))}" title="Read the paper (PDF)">
      <img src="page1.jpg" alt="The first page of the paper" />
      Read the paper
    </a>
'''
    film = ""
    if has_film:
        film = '''  <div class="film" id="film">
    <iframe name="film" src="film/" title="A video about the paper" allow="fullscreen" allowfullscreen loading="lazy"></iframe>
  </div>
'''
        chapters = os.path.join(ROOT, "papers", pid, "film", "chapters.json")
        chapters = json.load(open(chapters, encoding="utf-8")) if os.path.exists(chapters) else []
        if chapters:   # the video's chapters: each link moves the player above to that time
            items = "\n".join(f'    <li><span class="t">{int(t) // 60}:{int(t) % 60:02d}</span><a href="film/?t={int(t)}" target="film">{E(name)}</a></li>'
                              for t, name in chapters)
            film += f'  <ol class="chapters">\n{items}\n  </ol>\n'
        if os.path.exists(os.path.join(ROOT, "papers", pid, "short", "index.html")):
            film += '''  <details class="short">
    <summary>The two-minute version</summary>
    <div class="film">
      <iframe src="short/" title="A two-minute video about the paper" allow="fullscreen" allowfullscreen loading="lazy"></iframe>
    </div>
  </details>
'''
        film += "\n"
    abstract = "\n".join(f"  <p>{E(par.strip())}</p>" for par in p["abstract"].split("\n\n") if par.strip())
    talks = ""
    if p["talks"]:
        def talk(t):   # a talk: its slides (or, without slides, its recording) under its title, then when and where
            rec = f' · <a href="{E(url(t["video"]))}">{E(t.get("video_label") or "recording")}</a>' if t.get("video") and t.get("url") else ""
            return f'    <li><a href="{E(url(t.get("url") or t["video"]))}">{E(t["title"])}</a> <span class="info">{E(str(t["year"]))} · {E(t["where"])}{rec}</span></li>'
        items = "\n".join(talk(t) for t in p["talks"])
        talks = f"  <h2>Talks</h2>\n  <ul class=\"files\">\n{items}\n  </ul>\n\n"
    sub = f'\n      <p class="subtitle">{E(p["subtitle"])}</p>' if p.get("subtitle") else ""
    venue = "PhD thesis, 2024" if pid == "thesis" else f'{E(p["venue"])}'
    return f'''<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <meta name="description" content="{E(p["title"])}. {E(p["one_line"])}" />
  <link rel="canonical" href="https://julesjacobs.com/papers/{pid}/" />
  <meta property="og:url" content="https://julesjacobs.com/papers/{pid}/" />
  <meta property="og:title" content="{E(p["title"])}" />
  <meta property="og:description" content="{E(p["one_line"])}" />
  <link rel="icon" type="image/png" sizes="32x32" href="/images/ico/favicon-32x32.png" />
  <link rel="stylesheet" href="../paper.css" />
  <title>{E(p["title"])}</title>
</head>
<body>
  <p class="crumb"><a href="/">Jules Jacobs</a> · <a href="/#publications-heading">Publications</a></p>
  <div class="top{"" if thumb else " plain"}">
    <div>
      <h1>{E(p["title"])}</h1>{sub}
      <p class="byline">{authors(p)}. {venue}.{" " + awards if awards else ""}</p>
      <p class="pitch">{E(p["summary"])}</p>
      <div class="buttons">
        {(chr(10) + "        ").join(buttons)}
      </div>
    </div>
{thumb}  </div>

{film}  <h2>{"Summary" if pid == "thesis" else "Abstract"}</h2>
{abstract}

{talks}  <h2>Cite</h2>
<pre>{E(p["bibtex"].strip())}</pre>
{COUNT}</body>
</html>
'''


CSS = '''/* The pages of the papers (written by _tools/build_papers.py). */
:root {
  --bg: #ffffff; --fg: #262a30; --muted: #5f6672; --line: #e3e5e9; --panel: #f3f4f6;
  --link: hsl(213, 50%, 38%); --link-hover-bg: hsl(213, 50%, 93%);
  --chip-bg: #f1f2f4; --chip-fg: #4c525c; --chip-line: #d7dae0;
  --award-bg: hsl(213, 85%, 93%); --award-fg: hsl(213, 80%, 38%);
  color-scheme: light;
}
body {
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
  font-size: 16px; line-height: 1.5; color: var(--fg); background-color: var(--bg);
  max-width: 900px; margin: 0 auto; padding: 18px 16px 48px 16px;
}
a { color: var(--link); text-decoration: none; border-radius: 4px; }
a:hover { background: var(--link-hover-bg); }
.crumb { font-size: 14px; color: var(--muted); margin: 0 0 10px 0; }
.crumb a { color: var(--muted); }
.crumb a:hover { color: var(--link); }
h1 { font-size: 30px; line-height: 1.2; margin: 0 0 4px 0; letter-spacing: -0.01em; }
h2 { font-size: 18px; margin: 34px 0 6px 0; }
.subtitle { font-size: 18px; font-style: italic; color: var(--muted); margin: 0 0 6px 0; }
.byline { color: var(--muted); margin: 0 0 14px 0; }
.byline .note { font-size: 13px; }
.award { display: inline-block; font-size: 13px; padding: 0 7px; border-radius: 5px; background: var(--award-bg); color: var(--award-fg); margin-left: 4px; white-space: nowrap; }
.top { display: grid; grid-template-columns: minmax(0, 1fr) 150px; gap: 8px 44px; align-items: start; margin: 14px 0 8px 0; }
.top.plain { grid-template-columns: minmax(0, 1fr); }
.pitch { font-size: 17.5px; line-height: 1.5; margin: 14px 0 16px 0; }
.buttons { display: flex; flex-wrap: wrap; gap: 6px; }
.button { display: inline-block; border: 1px solid var(--chip-line); border-radius: 5px; padding: 4px 12px; font-size: 15px;
  color: var(--chip-fg); background-color: var(--chip-bg); white-space: nowrap; }
.button:hover { color: var(--bg); border-color: var(--link); background-color: var(--link); }
.button.primary { color: var(--bg); background-color: var(--link); border-color: var(--link); }
.button.primary:hover { filter: brightness(1.12); }
a.paper { display: block; color: var(--muted); font-size: 13px; text-align: center; margin-top: 4px; }
a.paper:hover { background: none; color: var(--link); }
a.paper img { display: block; width: 100%; height: auto; background: #fff; border: 1px solid var(--chip-line); border-radius: 2px; margin-bottom: 14px;
  box-shadow: 0 1px 3px rgba(20, 30, 50, 0.10), 4px 4px 0 -1px #fff, 4px 4px 0 0 var(--chip-line), 8px 8px 0 -1px #fff, 8px 8px 0 0 var(--chip-line);
  transition: transform 0.15s ease; }
a.paper:hover img { transform: translateY(-3px); }
/* the picture's 16:9 plus the height of the player's control bar, so the bar sits under the picture */
.film { scroll-margin-top: 12px; position: relative; width: 100%; border: 1px solid var(--line); border-radius: 6px; overflow: hidden; background: #f4ecdf; margin: 22px 0 6px 0; }
.film::before { content: ""; display: block; padding-top: calc(56.25% + 58px); }
@media (pointer: coarse) { .film::before { padding-top: calc(56.25% + 62px); } }
.film iframe { position: absolute; inset: 0; width: 100%; height: 100%; border: 0; }
ol.chapters { columns: 2; column-gap: 28px; padding-left: 0; margin: 6px 0; list-style: none; font-size: 15px; }
ol.chapters li { break-inside: avoid; margin-bottom: 2px; }
ol.chapters .t { display: inline-block; width: 3.2em; color: var(--muted); font-variant-numeric: tabular-nums; }
details.short { margin: 10px 0 6px 0; font-size: 15px; }
details.short summary { cursor: pointer; color: var(--link); width: fit-content; border-radius: 4px; }
details.short summary:hover { background: var(--link-hover-bg); }
details.short .film { margin-top: 8px; }
ul.files { padding-left: 20px; margin: 6px 0; }
ul.files li { margin-bottom: 6px; }
.info { color: var(--muted); }
pre { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 13px; line-height: 1.5; background: var(--panel);
  border: 1px solid var(--line); border-radius: 6px; padding: 10px 14px; overflow-x: auto; margin: 8px 0; }
@media (max-width: 680px) { .top { grid-template-columns: minmax(0, 1fr); } a.paper { display: none; } ol.chapters { columns: 1; } }
'''


def home(papers):
    """Titles and names on the home page point at the pages; each publication carries its one-line summary."""
    p = os.path.join(ROOT, "index.html")
    h = open(p, encoding="utf-8").read()
    ones = {q["id"]: q["one_line"] for q in papers}
    ones.update(EXTRA_ONE)
    ids = {q["id"] for q in papers}
    for pid, one in ones.items():
        m = re.search(r'<tr id="' + re.escape(pid) + r'">.*?</tr>', h, flags=re.S)
        if not m:
            continue
        row = m.group(0)
        if pid in ids:
            row = re.sub(r'<a class="title" href="[^"]*">', f'<a class="title" href="papers/{pid}/">', row, count=1)
        row = re.sub(r'\n\s*<div class="one">.*?</div>', "", row, flags=re.S)
        # after the authors, in the text colour: the title and the authors stay together, and the line reads as content
        row = re.sub(r'(<div class="authors">.*?</div>)', lambda a: a.group(1) + f'\n            <div class="one">{E(one)}</div>', row, count=1, flags=re.S)
        h = h[:m.start()] + row + h[m.end():]
    for pid in ids:   # the project cards' lines, and links in running text, that pointed at the publication's row
        h = h.replace(f'<a class="pt" href="#{pid}">', f'<a class="pt" href="papers/{pid}/">')
    # each line of a project card carries its summary, under the name
    h = re.sub(r'<span class="ps">.*?</span>', "", h, flags=re.S)
    for pid, one in ones.items():
        h = re.sub(r'(<li><a class="pt" href="papers/' + re.escape(pid) + r'/">.*?)(</li>)', lambda m: m.group(1) + f'<span class="ps">{E(one)}</span>' + m.group(2), h, flags=re.S)
    for href, one in TOOL_ONE.items():
        h = re.sub(r'(<li><a class="pt" href="' + re.escape(href) + r'">.*?)(</li>)', lambda m: m.group(1) + f'<span class="ps">{E(one)}</span>' + m.group(2), h, flags=re.S)
    # the rules for all of this live in one marked block, rewritten on every run
    h = re.sub(r"    /\* papers:begin \*/.*?/\* papers:end \*/\n\n", "", h, flags=re.S)
    h = re.sub(r"    /\* A publication's one-line summary, under its title\. \*/\n    \.pub \.one \{[^\n]*\n\n", "", h)
    k = h.index("    /* One line for each paper of a project")
    h = h[:k] + HOME_CSS + h[k:]
    open(p, "w", encoding="utf-8").write(h)


def main():
    papers = json.load(open(os.path.join(ROOT, "_data", "papers.json"), encoding="utf-8"))
    open(os.path.join(ROOT, "papers", "paper.css"), "w", encoding="utf-8").write(CSS)
    for q in papers:
        d = os.path.join(ROOT, "papers", q["id"])
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, "index.html"), "w", encoding="utf-8").write(page(q))
    home(papers)
    print(len(papers), "pages")


if __name__ == "__main__":
    main()
