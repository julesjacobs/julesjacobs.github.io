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

export function yearPosition(date) {
  const normalized = new Date(`2022-${date.slice(5)}T12:00:00Z`);
  return (+normalized - Date.UTC(2022, 0, 1)) / (365 * 86400000);
}

export function startApp(data, doc = document) {
  const $ = (id) => doc.getElementById(id);
  const state = { query: "", area: "all", topics: [], status: "all" };
  const categories = {
    pl: "programming-languages",
    logic: "formal-methods",
    verification: "formal-methods",
    systems: "systems",
    algorithms: "algorithms",
  };
  const major = new Set(["popl", "pldi", "oopsla", "icfp"]);
  const tag = (t) =>
    `<button type="button" class="topic" data-topic="${escapeHTML(t)}">${escapeHTML(t)}</button>`;
  $("area").insertAdjacentHTML(
    "beforeend",
    Object.entries(areas)
      .map(([id, name]) => `<option value="${id}">${name}</option>`)
      .join(""),
  );
  $("topic-options").innerHTML = [...new Set(data.flatMap((c) => c.keywords))]
    .sort()
    .map((t) => `<option value="${escapeHTML(t)}"></option>`)
    .join("");
  function links(c, d) {
    if (d.timeUnverified) return `<a href="${escapeHTML(d.url)}" target="_blank" rel="noopener">Official website ↗</a>`;
    const urls = calendarLinks(c, d);
    return `<div class="calendar-links">${[
      ["Google Calendar", urls.google, "fab fa-google"],
      ["Apple Calendar", urls.ics, "fab fa-apple"],
      ["Outlook Calendar", urls.outlook, "fab fa-microsoft"],
      ["Download .ics", urls.ics, "fas fa-file-download"],
      ["Official website", d.url, "fas fa-external-link-alt"],
    ]
      .map(
        ([name, url, icon]) =>
          `<a href="${escapeHTML(url)}" title="${name}" aria-label="${name}" ${url.startsWith("data:") ? `download="${c.id}-${d.date}.ics"` : 'target="_blank" rel="noopener"'}><i class="${icon}" aria-hidden="true"></i></a>`,
      )
      .join("")}</div>`;
  }
  function showConference(id) {
    const c = data.find((c) => c.id === id),
      now = new Date();
    $("conference-title").textContent = c.name;
    $("conference-content").innerHTML =
      `<p class="small">${escapeHTML(c.fullName)}</p><p>${escapeHTML(c.description)}</p><h3>Topics</h3><div class="topics">${c.keywords.map(tag).join("")}</div><h3>Submission deadlines</h3>${
        c.deadlines.length
          ? [...c.deadlines]
              .sort((a, b) => a.date.localeCompare(b.date))
              .map(
                (d) =>
                  `<div class="deadline"><strong>${d.edition} · ${escapeHTML(d.label)}</strong><p>${dateLabel(d.date)} · ${escapeHTML(d.timezone)}${deadlineInstant(d) < now ? " · passed" : ""} ${links(c, d)}</p>${d.abstract ? `<p class="small">Abstract registration: ${dateLabel(d.abstract)}${deadlineInstant({ ...d, date: d.abstract }) < now ? " (passed)" : ""}.</p>` : ""}${d.note ? `<p class="small">${escapeHTML(d.note)}</p>` : ""}<p class="small">Source checked ${dateLabel(d.checked)}.</p></div>`,
              )
              .join("")
          : "<p>No submission date verified in this list.</p>"
      }<p><a href="${escapeHTML(c.url)}" target="_blank" rel="noopener">Official website ↗</a></p><p class="small">Topics are a guide to the venue’s scope. Check the official call for current dates and requirements.</p>`;
    $("conference-info").showModal();
  }
  function closeDeadline() {
    const active = $("timeline").querySelector(".active");
    if (!active) return;
    active.classList.remove("active");
    active.querySelector("[data-deadline]").setAttribute("aria-expanded", "false");
    active.querySelector(".timehover").hidden = true;
    $("timeline").classList.remove("has-active");
  }
  function render() {
    const now = new Date(),
      filtered = data.filter((c) => matches(c, state, now));
    $("selected-topics").innerHTML = state.topics
      .map(
        (t) =>
          `<button class="topic" type="button" data-topic="${escapeHTML(t)}" aria-label="Remove ${escapeHTML(t)} filter">${escapeHTML(t)} ×</button>`,
      )
      .join("");
    $("reset").hidden =
      !state.query &&
      state.area === "all" &&
      state.status === "all" &&
      !state.topics.length;
    const events = filtered
      .flatMap((c) =>
        c.deadlines.map((d) => ({ c, d, position: yearPosition(d.date) })),
      )
      .filter(({ d }) =>
        state.status === "past"
          ? deadlineInstant(d) < now
          : state.status === "upcoming"
            ? deadlineInstant(d) >= now
            : true,
      )
      .sort(
        (a, b) => b.position - a.position || a.c.name.localeCompare(b.c.name),
      );
    const timeline = $("timeline");
    timeline.innerHTML = '<div id="mid"></div>';
    timeline.classList.remove("has-active");
    let move = 0,
      width = 350;
    events.forEach(({ c, d, position }, i) => {
      const title = `${c.name}'${String(d.edition).slice(-2)}${/^R\d/.test(d.label) ? " " + d.label : ""}`;
      move =
        i > 0 && Math.abs(events[i - 1].position - position) < 7 / 365
          ? move + title.length
          : 0;
      const lineWidth = 110 + 9 * move;
      width = Math.max(width, 70 + lineWidth + 12);
      const days = (deadlineInstant(d) - now) / 86400000;
      const row = doc.createElement("div");
      row.className = `conf ${categories[c.id === "tacas" ? "systems" : c.areas[0]]}${major.has(c.id) ? " main" : ""}${days < 0 ? " past" : ""}`;
      row.style.cssText = `position:absolute;top:${100 * position}%;width:${lineWidth}px;z-index:${events.length - i}`;
      row.innerHTML = `<button type="button" data-deadline aria-expanded="false" aria-controls="deadline-${i}">${escapeHTML(title)}</button><div id="deadline-${i}" class="timehover" hidden><span>${dateLabel(d.date)} · ${escapeHTML(d.timezone)} · ${Math.abs(days).toFixed(1)} days ${days < 0 ? "ago" : "to go"} ${links(c, d)} <button type="button" class="conference-button" data-conference="${c.id}" aria-haspopup="dialog">Conference details</button></span></div>`;
      timeline.appendChild(row);
    });
    timeline.style.width = width + "px";
    for (let month = 0; month < 12; month++) {
      const line = doc.createElement("div");
      line.className = "month";
      line.style.cssText = `position:absolute;top:${(100 * (Date.UTC(2022, month, 1) - Date.UTC(2022, 0, 1))) / (365 * 86400000)}%`;
      line.textContent = new Intl.DateTimeFormat("default", {
        month: "long",
        timeZone: "UTC",
      }).format(new Date(Date.UTC(2022, month, 1)));
      timeline.appendChild(line);
    }
    const marker = doc.createElement("div");
    marker.className = "now";
    marker.style.cssText = `position:absolute;top:${yearPosition(now.toISOString().slice(0, 10)) * 100}%`;
    marker.title = "Today";
    timeline.appendChild(marker);
    $("empty").hidden = events.length > 0;
    $("timeline-scroll").hidden = events.length === 0;
    const undated = filtered.filter((c) => !c.deadlines.length);
    $("undated").hidden = !undated.length;
    $("undated").querySelector("summary").textContent =
      `Conferences without a verified deadline (${undated.length})`;
    $("undated-list").innerHTML = undated
      .sort((a, b) => a.name.localeCompare(b.name))
      .map(
        (c) =>
          `<button type="button" class="conference-button" data-conference="${c.id}" aria-haspopup="dialog">${escapeHTML(c.name)}</button>`,
      )
      .join(" · ");
    if (state.query || state.topics.length || state.area !== "all")
      $("undated").open = true;
  }
  function toggleTopic(topic) {
    state.topics = state.topics.includes(topic)
      ? state.topics.filter((t) => t !== topic)
      : [...state.topics, topic];
    if ($("conference-info").open) $("conference-info").close();
    render();
    $("search").focus();
  }
  $("search").addEventListener("input", (e) => {
    state.query = e.target.value;
    render();
  });
  ["area", "status"].forEach((id) =>
    $(id).addEventListener("change", (e) => {
      state[id] = e.target.value;
      render();
    }),
  );
  $("reset").addEventListener("click", () => {
    Object.assign(state, { query: "", area: "all", status: "all", topics: [] });
    $("search").value = "";
    $("area").value = "all";
    $("status").value = "all";
    $("topic-filter").value = "";
    $("undated").open = false;
    render();
  });
  $("add-topic").addEventListener("click", () => {
    const topic = $("topic-filter").value;
    if (data.some((c) => c.keywords.includes(topic))) {
      toggleTopic(topic);
      $("topic-filter").value = "";
      $("topic-filter").setCustomValidity("");
    } else {
      $("topic-filter").setCustomValidity("Choose a topic from the list.");
      $("topic-filter").reportValidity();
    }
  });
  $("topic-filter").addEventListener("input", () =>
    $("topic-filter").setCustomValidity(""),
  );
  $("close-info").addEventListener("click", () => $("conference-info").close());
  doc.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !$("conference-info").open) {
      const trigger = $("timeline").querySelector(".active [data-deadline]");
      closeDeadline();
      trigger?.focus();
    }
  });
  doc.addEventListener("click", (e) => {
    const trigger = e.target.closest("[data-deadline]");
    if (trigger) {
      const row = trigger.closest(".conf"), wasOpen = row.classList.contains("active");
      closeDeadline();
      if (!wasOpen) {
        row.classList.add("active");
        trigger.setAttribute("aria-expanded", "true");
        row.querySelector(".timehover").hidden = false;
        $("timeline").classList.add("has-active");
      }
      return;
    }
    if (!e.target.closest(".timehover")) closeDeadline();
    const button = e.target.closest("button");
    if (button?.dataset.conference) showConference(button.dataset.conference);
    if (button?.dataset.topic) toggleTopic(button.dataset.topic);
  });
  render();
}
if (typeof document !== "undefined") {
  fetch("conferences.json?v=20260910b")
    .then((r) => {
      if (!r.ok) throw new Error();
      return r.json();
    })
    .then((data) => startApp(data))
    .catch(() => {
      document.getElementById("load-error").hidden = false;
      document.getElementById("load-error").textContent =
        "Could not load conferences. Please reload to try again.";
    });
}
