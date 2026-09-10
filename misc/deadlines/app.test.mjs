import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  matches,
  selectConferences,
  deadlineInstant,
  upcoming,
  calendarLinks,
  areas,
} from "./app.mjs";
const data = JSON.parse(
  readFileSync(new URL("./conferences.json", import.meta.url)),
);
const now = new Date("2026-09-09T12:00:00Z");
const get = (id) => data.find((c) => c.id === id);

test("catalogue has complete, searchable records and well-formed source dates", () => {
  assert.equal(data.length, new Set(data.map((c) => c.id)).size);
  for (const c of data) {
    assert.match(c.id, /^[a-z]+$/);
    assert(c.name && c.fullName && c.description);
    assert(c.keywords.length >= 15, c.name);
    assert.equal(c.keywords.length, new Set(c.keywords).size, c.name);
    assert(c.areas.every((a) => a in areas));
    assert.equal(new URL(c.url).protocol, "https:");
    for (const d of c.deadlines) {
      assert.match(d.date, /^20\d\d-\d\d-\d\d$/);
      assert.equal(new Date(d.date).toISOString().slice(0, 10), d.date);
      assert.equal(new URL(d.url).protocol, "https:");
      assert(!Number.isNaN(+deadlineInstant(d)));
      if (d.abstract) assert(d.abstract <= d.date);
    }
  }
});
test("search matches descriptions, full names, and topics together with area and all selected topics", () => {
  assert(
    matches(get("icalp"), { query: "track b automata", area: "logic" }, now),
  );
  assert(
    matches(get("itp"), { query: "interactive theorem proving lean" }, now),
  );
  assert(
    matches(
      get("popl"),
      { topics: ["separation logic", "logical relations"] },
      now,
    ),
  );
  assert(!matches(get("soda"), { topics: ["separation logic"] }, now));
  assert(!matches(get("itp"), { area: "algorithms" }, now));
  assert(!matches(get("cav"), { query: "compilers" }, now));
  assert.deepEqual(
    selectConferences(data, { query: "unfindable-conference" }, now),
    [],
  );
});
test("deadline filters distinguish missing dates, past dates, and multiple rounds", () => {
  assert(matches(get("icalp"), { status: "unconfirmed" }, now));
  assert(matches(get("icalp"), { status: "past" }, now));
  assert(matches({ ...get("icalp"), deadlines: [] }, { status: "unconfirmed" }, now));
  assert(!matches({ ...get("icalp"), deadlines: [] }, { status: "past" }, now));
  assert(matches(get("cgo"), { status: "past" }, now));
  assert(matches(get("cgo"), { status: "upcoming" }, now));
  assert.equal(upcoming(get("oopsla"), now).length, 2);
  const sorted = selectConferences(data, { status: "upcoming" }, now);
  assert.equal(sorted[0].id, "cgo");
  assert.equal(sorted[1].id, "cpp");
  assert.equal(
    upcoming(get("cpp"), new Date("2026-09-11T11:59:59Z")).length,
    1,
  );
  assert.equal(
    upcoming(get("cpp"), new Date("2026-09-11T12:00:00Z")).length,
    0,
  );
});
test("calendar exports use the exact AoE instant and include abstract registration and source", () => {
  const c = get("cpp"),
    d = c.deadlines[0],
    links = calendarLinks(c, d);
  assert.equal(deadlineInstant(d).toISOString(), "2026-09-11T11:59:59.000Z");
  const google = new URL(links.google);
  assert.equal(
    google.searchParams.get("dates"),
    "20260911T115959Z/20260911T125959Z",
  );
  assert(google.searchParams.get("details").includes("2026-09-03"));
  const raw = decodeURIComponent(links.ics.split(",").slice(1).join(","));
  const ics = raw.replace(/\r\n /g, "");
  assert(ics.includes("DTSTART:20260911T115959Z\r\n"));
  assert(ics.includes(`URL:${d.url}\r\n`));
  assert(ics.endsWith("END:VCALENDAR\r\n"));
  assert(raw.split("\r\n").every((line) => Buffer.byteLength(line) <= 75));
});
