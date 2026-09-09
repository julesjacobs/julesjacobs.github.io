export const areas = {
  pl: "Programming languages",
  verification: "Verification",
  logic: "Logic & foundations",
  algorithms: "Algorithms",
  systems: "Systems & compilers",
};
export const normalize = (text) =>
  text
    .normalize("NFKD")
    .replace(/\p{Diacritic}/gu, "")
    .toLowerCase();
export const deadlineInstant = (d) =>
  new Date(`${d.date}T23:59:59${d.offset || "-12:00"}`);
export const upcoming = (c, now = new Date()) =>
  c.deadlines
    .filter((d) => deadlineInstant(d) >= now)
    .sort((a, b) => deadlineInstant(a) - deadlineInstant(b));
export function matches(
  c,
  { query = "", area = "all", topics = [], status = "all" } = {},
  now = new Date(),
) {
  const haystack = normalize(
    [
      c.name,
      c.fullName,
      c.description,
      ...c.keywords,
      ...c.deadlines.map((d) => d.edition),
    ].join(" "),
  );
  return (
    normalize(query)
      .trim()
      .split(/\s+/)
      .every((word) => haystack.includes(word)) &&
    (area === "all" || c.areas.includes(area)) &&
    topics.every((t) => c.keywords.includes(t)) &&
    (status === "all" ||
      (status === "upcoming" && upcoming(c, now).length > 0) ||
      (status === "unconfirmed" && upcoming(c, now).length === 0) ||
      (status === "past" && c.deadlines.some((d) => deadlineInstant(d) < now)))
  );
}
export function selectConferences(data, state, now = new Date()) {
  return data
    .filter((c) => matches(c, state, now))
    .sort((a, b) => {
      if (state.sort === "name") return a.name.localeCompare(b.name);
      const ad = upcoming(a, now)[0],
        bd = upcoming(b, now)[0];
      return (
        (ad ? deadlineInstant(ad).getTime() : Infinity) -
          (bd ? deadlineInstant(bd).getTime() : Infinity) ||
        a.name.localeCompare(b.name)
      );
    });
}
export const escapeHTML = (value) =>
  String(value).replace(
    /[&<>"']/g,
    (c) =>
      ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[
        c
      ],
  );
const fmt = new Intl.DateTimeFormat("en-GB", {
  day: "numeric",
  month: "short",
  year: "numeric",
  timeZone: "UTC",
});
export const dateLabel = (date) => fmt.format(new Date(`${date}T12:00:00Z`));
const icsTime = (date) => date.toISOString().replace(/[-:]|\.\d{3}/g, "");
export function calendarLinks(c, d) {
  const start = deadlineInstant(d),
    end = new Date(+start + 3600000),
    title = `${c.name} ${d.edition} ${d.label} deadline`;
  const description = `Deadline: ${d.date}, end of day ${d.timezone || "AoE"}. ${d.abstract ? `Abstract registration: ${d.abstract}. ` : ""}Check the official call: ${d.url}`;
  const escapeICS = (s) =>
    s
      .replace(/\\/g, "\\\\")
      .replace(/\n/g, "\\n")
      .replace(/,/g, "\\,")
      .replace(/;/g, "\\;");
  const lines = [
    "BEGIN:VCALENDAR",
    "VERSION:2.0",
    "PRODID:-//Jules Jacobs//Conference Explorer//EN",
    "BEGIN:VEVENT",
    `UID:${c.id}-${d.edition}-${d.date}-${encodeURIComponent(d.label)}@julesjacobs.com`,
    `DTSTAMP:${icsTime(new Date())}`,
    `DTSTART:${icsTime(start)}`,
    `DTEND:${icsTime(end)}`,
    `SUMMARY:${escapeICS(title)}`,
    `DESCRIPTION:${escapeICS(description)}`,
    `URL:${d.url}`,
    "END:VEVENT",
    "END:VCALENDAR",
  ];
  const fold = (line) => {
    let result = "",
      length = 0;
    for (const ch of line) {
      const size = new TextEncoder().encode(ch).length;
      if (length + size > 74) {
        result += "\r\n ";
        length = 1;
      }
      result += ch;
      length += size;
    }
    return result;
  };
  return {
    google: `https://calendar.google.com/calendar/render?${new URLSearchParams({ action: "TEMPLATE", text: title, dates: `${icsTime(start)}/${icsTime(end)}`, details: description })}`,
    outlook: `https://outlook.live.com/calendar/0/action/compose?${new URLSearchParams({ subject: title, startdt: start.toISOString(), enddt: end.toISOString(), body: description })}`,
    ics: `data:text/calendar;charset=utf-8,${encodeURIComponent(lines.map(fold).join("\r\n") + "\r\n")}`,
  };
}

export function startApp(data, doc = document) {
  const $ = (id) => doc.getElementById(id),
    state = {
      query: "",
      area: "all",
      topics: [],
      status: "all",
      sort: "deadline",
      view: "cards",
    },
    openCards = new Set();
  let topicQuery = "",
    allTopics = false;
  const params = new URLSearchParams(location.hash.slice(1));
  state.query = params.get("q") || "";
  state.area = params.get("area") in areas ? params.get("area") : "all";
  state.topics = params
    .getAll("topic")
    .filter((t) => data.some((c) => c.keywords.includes(t)));
  if (["all", "upcoming", "unconfirmed", "past"].includes(params.get("status")))
    state.status = params.get("status");
  if (params.get("view") === "calendar") state.view = "calendar";
  if (params.get("sort") === "name") state.sort = "name";
  $("search").value = state.query;
  $("status").value = state.status;
  $("sort").value = state.sort;
  if (matchMedia("(max-width: 650px)").matches)
    doc.querySelector(".topic-panel").open = false;
  const tag = (t) =>
    `<button type="button" class="tag" data-topic="${escapeHTML(t)}" aria-pressed="${state.topics.includes(t)}">${escapeHTML(t)}</button>`;
  const links = (c, d) => {
    const l = calendarLinks(c, d);
    return `<div class="calendar-links"><a href="${escapeHTML(d.url)}" target="_blank" rel="noopener">Official deadline ↗</a><a href="${escapeHTML(l.google)}" target="_blank" rel="noopener">Google</a><a href="${escapeHTML(l.outlook)}" target="_blank" rel="noopener">Outlook</a><a href="${escapeHTML(l.ics)}" download="${c.id}-${d.edition}-${d.date}.ics">Apple / .ics</a></div>`;
  };
  function dateEntry(c, d, now) {
    const past = deadlineInstant(d) < now;
    return `<div class="deadline-entry"><div class="deadline-top"><strong>${d.edition} · ${escapeHTML(d.label)}</strong><span class="${past ? "past-label" : ""}">${dateLabel(d.date)} · ${escapeHTML(d.timezone || "AoE")}${past ? " · passed" : ""}</span></div>${d.abstract ? `<p>Abstract registration: ${dateLabel(d.abstract)}${deadlineInstant({ ...d, date: d.abstract }) < now ? " (passed)" : ""}.</p>` : ""}${links(c, d)}<p>Source checked ${dateLabel(d.checked)}.</p></div>`;
  }
  function card(c, now) {
    const next =
        state.status === "past"
          ? [...c.deadlines]
              .filter((d) => deadlineInstant(d) < now)
              .sort((a, b) => deadlineInstant(b) - deadlineInstant(a))[0]
          : upcoming(c, now)[0],
      days = next ? Math.ceil((deadlineInstant(next) - now) / 86400000) : 0;
    const isPast = next && deadlineInstant(next) < now;
    const note = isPast
      ? "Deadline passed"
      : next?.abstract &&
          deadlineInstant({ ...next, date: next.abstract }) < now
        ? "Abstract registration has passed"
        : days <= 1
          ? "Less than 24 hours"
          : `in ${days} days`;
    return `<article class="conference-card" style="--accent:var(--${c.areas[0]})"><div class="card-body"><div class="card-area"><span class="area-dot" aria-hidden="true"></span>${escapeHTML(areas[c.areas[0]])}</div><div class="card-heading"><h2><button class="conference-name" type="button" data-open="${c.id}" aria-expanded="${openCards.has(c.id)}" aria-controls="detail-${c.id}">${escapeHTML(c.name)}</button></h2><span class="edition">${next?.edition || ""}</span></div><p class="full-name">${escapeHTML(c.fullName)}</p><p class="description">${escapeHTML(c.description)}</p><div class="date-box ${next ? "" : "unconfirmed"}"><div><strong>${next ? dateLabel(next.date) : "No upcoming date verified"}</strong><small>${next ? escapeHTML(next.label) + " · " + escapeHTML(next.timezone || "AoE") : c.deadlines.length ? "Previous deadlines in details" : "Check the official website"}</small></div>${next ? `<span class="countdown">${note}</span>` : ""}</div><div class="tags">${c.keywords.slice(0, 4).map(tag).join("")}</div><details class="conference-details" id="detail-${c.id}" data-card="${c.id}" ${openCards.has(c.id) ? "open" : ""}><summary>Topics & deadlines <span class="sr-only">for ${escapeHTML(c.name)}</span><span aria-hidden="true"> · ${c.keywords.length} topics</span></summary><div class="detail-content"><h3>All topics</h3><div class="tags">${c.keywords.map(tag).join("")}</div><h3>Submission deadlines</h3>${
      c.deadlines.length
        ? [...c.deadlines]
            .sort((a, b) => a.date.localeCompare(b.date))
            .map((d) => dateEntry(c, d, now))
            .join("")
        : '<p class="detail-note">No submission deadline verified in this list. See the official call for current dates.</p>'
    }<a class="source-link" href="${escapeHTML(c.url)}" target="_blank" rel="noopener">${escapeHTML(c.name)} website ↗</a></div></details></div></article>`;
  }
  function calendar(conferences, now) {
    const events = conferences
      .flatMap((c) => c.deadlines.map((d) => ({ c, d })))
      .filter(({ d }) =>
        state.status === "past"
          ? deadlineInstant(d) < now
          : deadlineInstant(d) >= now,
      )
      .sort((a, b) => deadlineInstant(a.d) - deadlineInstant(b.d));
    if (!events.length)
      return `<div class="empty"><h2>No ${state.status === "past" ? "past" : "upcoming"} deadlines in this selection</h2><p>Conferences without a verified date are available in the conference view.</p><button type="button" class="text-button" data-action="cards">Browse conferences</button></div>`;
    let month = "",
      html = `<p class="calendar-note">${state.status === "past" ? "Past" : "Upcoming"} submission deadlines. Dates use the deadline’s stated time zone; calendar downloads convert the exact time.</p>`;
    for (const { c, d } of events) {
      const key = d.date.slice(0, 7);
      if (key !== month) {
        if (month) html += "</section>";
        month = key;
        html += `<section class="calendar-month"><h2>${new Intl.DateTimeFormat("en-GB", { month: "long", year: "numeric", timeZone: "UTC" }).format(new Date(d.date + "T12:00:00Z"))}</h2>`;
      }
      html += `<article class="calendar-event ${deadlineInstant(d) < now ? "is-past" : ""}" style="--accent:var(--${c.areas[0]})"><div class="calendar-day">${Number(d.date.slice(8))}<small>${escapeHTML(d.timezone || "AoE")}</small></div><div><h3>${escapeHTML(c.name)} ${d.edition} · ${escapeHTML(d.label)}</h3><p>${escapeHTML(c.description)}</p>${d.abstract ? `<p>Abstract registration: ${dateLabel(d.abstract)}${deadlineInstant({ ...d, date: d.abstract }) < now ? " (passed)" : ""}.</p>` : ""}${links(c, d)}</div></article>`;
    }
    return html + "</section>";
  }
  function renderTopics() {
    const counts = new Map();
    data
      .filter((c) => matches(c, state))
      .forEach((c) =>
        c.keywords.forEach((t) => counts.set(t, (counts.get(t) || 0) + 1)),
      );
    const keywords = [...new Set(data.flatMap((c) => c.keywords))]
      .filter((t) => normalize(t).includes(normalize(topicQuery)))
      .sort(
        (a, b) =>
          state.topics.includes(b) - state.topics.includes(a) ||
          (counts.get(b) || 0) - (counts.get(a) || 0) ||
          a.localeCompare(b),
      );
    const displayed =
      allTopics || topicQuery ? keywords : keywords.slice(0, 16);
    $("topics").innerHTML = displayed.length
      ? displayed
          .map(
            (t) =>
              `<button type="button" class="topic-button" data-topic="${escapeHTML(t)}" aria-pressed="${state.topics.includes(t)}">${escapeHTML(t)}<span>${counts.get(t) || 0}</span></button>`,
          )
          .join("")
      : '<p class="hint">No matching topics.</p>';
    $("more-topics").hidden = !!topicQuery || keywords.length <= 16;
    $("more-topics").textContent = allTopics
      ? "Show fewer topics"
      : `Show all ${keywords.length} topics`;
  }
  function render() {
    const now = new Date(),
      filtered = selectConferences(data, state, now);
    $("areas").innerHTML = [["all", "All areas"], ...Object.entries(areas)]
      .map(
        ([id, label]) =>
          `<button type="button" class="area-button" data-area="${id}" aria-pressed="${id === state.area}">${id === "all" ? "" : `<span class="area-dot" style="--accent:var(--${id})" aria-hidden="true"></span>`}${label}</button>`,
      )
      .join("");
    $("result-count").textContent =
      `${filtered.length} of ${data.length} conferences`;
    $("selected").innerHTML = state.topics
      .map(
        (t) =>
          `<button type="button" class="tag" data-topic="${escapeHTML(t)}" aria-label="Remove ${escapeHTML(t)} filter">${escapeHTML(t)} ×</button>`,
      )
      .join("");
    $("cards-view").setAttribute("aria-pressed", state.view === "cards");
    $("calendar-view").setAttribute("aria-pressed", state.view === "calendar");
    $("sort").disabled = state.view === "calendar";
    $("results").className =
      state.view === "cards" && filtered.length ? "cards" : "";
    $("results").innerHTML = !filtered.length
      ? '<div class="empty"><h2>No conferences match</h2><p>Try a broader search or remove a topic. Selected topics must all match.</p><button type="button" class="text-button" data-action="reset">Reset filters</button></div>'
      : state.view === "cards"
        ? filtered.map((c) => card(c, now)).join("")
        : calendar(filtered, now);
    renderTopics();
    const p = new URLSearchParams();
    if (state.query) p.set("q", state.query);
    if (state.area !== "all") p.set("area", state.area);
    state.topics.forEach((t) => p.append("topic", t));
    if (state.status !== "all") p.set("status", state.status);
    if (state.view !== "cards") p.set("view", state.view);
    if (state.sort !== "deadline") p.set("sort", state.sort);
    history.replaceState(
      null,
      "",
      location.pathname + location.search + (p.size ? "#" + p : ""),
    );
  }
  function reset() {
    Object.assign(state, {
      query: "",
      area: "all",
      topics: [],
      status: "all",
      sort: "deadline",
    });
    $("search").value = "";
    $("status").value = "all";
    $("sort").value = "deadline";
    topicQuery = "";
    $("topic-search").value = "";
    render();
  }
  doc.addEventListener("click", (event) => {
    const button = event.target.closest("button");
    if (!button) return;
    if (button.dataset.topic) {
      const t = button.dataset.topic;
      state.topics = state.topics.includes(t)
        ? state.topics.filter((x) => x !== t)
        : [...state.topics, t];
      render();
      const target = [...doc.querySelectorAll("[data-topic]")].find(
        (el) => el.dataset.topic === t,
      );
      target?.focus();
    } else if (button.dataset.area) {
      state.area = button.dataset.area;
      render();
      doc.querySelector(`[data-area="${state.area}"]`)?.focus();
    } else if (button.dataset.open) {
      const detail = $("detail-" + button.dataset.open);
      detail.open = !detail.open;
    } else if (button.dataset.action === "reset" || button.id === "reset")
      reset();
    else if (button.dataset.action === "cards" || button.id === "cards-view") {
      state.view = "cards";
      render();
    } else if (button.id === "calendar-view") {
      state.view = "calendar";
      render();
    } else if (button.id === "more-topics") {
      allTopics = !allTopics;
      renderTopics();
    }
  });
  doc.addEventListener(
    "toggle",
    (event) => {
      const id = event.target.dataset?.card;
      if (id) {
        if (event.target.open) openCards.add(id);
        else openCards.delete(id);
        doc
          .querySelector(`[data-open="${id}"]`)
          ?.setAttribute("aria-expanded", event.target.open);
      }
    },
    true,
  );
  $("search").addEventListener("input", (e) => {
    state.query = e.target.value;
    render();
  });
  $("topic-search").addEventListener("input", (e) => {
    topicQuery = e.target.value;
    renderTopics();
  });
  $("status").addEventListener("change", (e) => {
    state.status = e.target.value;
    render();
  });
  $("sort").addEventListener("change", (e) => {
    state.sort = e.target.value;
    render();
  });
  doc.addEventListener("keydown", (e) => {
    if (
      e.key === "/" &&
      !/INPUT|TEXTAREA|SELECT/.test(e.target.tagName) &&
      !e.target.isContentEditable &&
      !e.metaKey &&
      !e.ctrlKey &&
      !e.altKey
    ) {
      e.preventDefault();
      $("search").focus();
    }
  });
  render();
}
if (typeof document !== "undefined") {
  fetch("conferences.json")
    .then((response) => {
      if (!response.ok) throw new Error("Data unavailable");
      return response.json();
    })
    .then((data) => startApp(data))
    .catch(() => {
      document.getElementById("result-count").textContent =
        "Conferences could not be loaded.";
      document.getElementById("results").innerHTML =
        '<div class="empty"><h2>Could not load the conference list</h2><p>Please reload the page to try again.</p><a href="conferences.json">Open conference data</a></div>';
    });
}
