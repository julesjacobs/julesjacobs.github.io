# PL deadline calendar

The live page is at <https://julesjacobs.com/misc/deadlines/>.

`conferences.json` contains the conference descriptions, curated keywords, official links, and verified submission deadlines. An empty `deadlines` array means no date has been verified for this list. It must not be interpreted as evidence that submissions are closed. Keep previous deadlines with their original edition; never extrapolate a new deadline from last year's date.

Each deadline records its official source, the date that source was checked, its time zone, and any known abstract-registration deadline. The original annual timeline places deadlines by month and day, with the edition in each label. Past deadlines are lightly shaded. Search and the collapsed Filters section narrow the timeline; click a conference for its description, topics, and exact dates. Conferences with no verified deadline appear in a separate expandable list. Calendar exports convert the end-of-day deadline to UTC. Descriptions and keywords describe a venue's general scope, rather than reproducing the complete call for papers.

The September 9, 2026 expansion adds 18 conferences, including ICALP. Newly verified upcoming submission dates are CGO 2027 round 2 (September 10, 2026) and VMCAI 2027 (September 30, 2026, with September 23 registration). The FSCD/CADE 2027 website currently contains placeholder submission dates; these are deliberately omitted. No 2027 ICALP or STACS deadline was verified in this update.

The page is static HTML, CSS, and JavaScript, published through the existing GitHub Pages workflow. Preview this directory with a static HTTP server. Run the data, filtering, and calendar-export checks from the repository root with:

```sh
node --test misc/deadlines/app.test.mjs
```
