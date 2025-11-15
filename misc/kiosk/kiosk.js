(() => {
  if (!window.luxon) {
    console.error("Luxon failed to load – kiosk clock disabled.");
    return;
  }

  const { DateTime } = luxon;
  const TIMEZONE = "America/New_York";
  const ROW_COUNT = 5;

  // Static timetable pulled from https://www.nywaterway.com/PaulusHook-WTCRoute.aspx
  const TIMETABLES = {
    phToBpt: {
      weekday: [
        "06:00", "06:07", "06:15", "06:22", "06:30", "06:37", "06:45", "06:52",
        "07:00", "07:07", "07:15", "07:22", "07:30", "07:37", "07:45", "07:52",
        "08:00", "08:07", "08:15", "08:22", "08:30", "08:37", "08:45", "08:52",
        "09:00", "09:15", "09:30", "09:45", "10:00", "10:15", "10:30", "10:45",
        "11:00", "11:15", "11:30", "11:45", "12:00", "12:15", "12:30", "12:45",
        "13:00", "13:15", "13:30", "13:45", "14:00", "14:15", "14:30", "14:45",
        "15:00", "15:15", "15:30", "15:45", "16:00", "16:15", "16:30", "16:45",
        "17:00", "17:15", "17:30", "17:45", "18:00", "18:15", "18:30", "18:45",
        "19:00", "19:15", "19:30", "19:45", "20:00", "20:15", "20:30", "20:45",
        "21:00", "21:15", "21:30", "21:45", "22:00", "22:15", "22:30", "22:45"
      ],
      weekend: [
        "10:10", "10:40", "11:10", "11:40", "12:10",
        "12:40", "13:10", "13:40", "14:10", "14:40",
        "15:10", "15:40", "16:10", "16:40", "17:10",
        "17:40", "18:10", "18:40", "19:10", "19:40"
      ]
    },
    bptToPh: {
      weekday: [
        "06:07", "06:15", "06:22", "06:30", "06:37", "06:45", "06:52", "07:00",
        "07:07", "07:15", "07:22", "07:30", "07:37", "07:45", "07:52", "08:00",
        "08:07", "08:15", "08:22", "08:30", "08:37", "08:45", "08:52", "09:07",
        "09:22", "09:37", "09:52", "10:07", "10:22", "10:37", "10:52", "11:07",
        "11:22", "11:37", "11:52", "12:07", "12:22", "12:37", "12:52", "13:07",
        "13:22", "13:37", "13:52", "14:07", "14:22", "14:37", "14:52", "15:07",
        "15:22", "15:37", "15:52", "16:07", "16:22", "16:37", "16:52", "17:07",
        "17:22", "17:37", "17:52", "18:07", "18:22", "18:37", "18:52", "19:07",
        "19:22", "19:37", "19:52", "20:07", "20:22", "20:37", "20:52", "21:07",
        "21:22", "21:37", "21:52", "22:07", "22:22", "22:37", "22:52"
      ],
      weekend: [
        "10:20", "10:50", "11:20", "11:50", "12:20", "12:50",
        "13:20", "13:50", "14:20", "14:50", "15:30", "16:00",
        "16:30", "17:00", "17:30", "18:00", "18:30", "19:00",
        "19:30", "20:00"
      ]
    }
  };

  const TIMETABLE_MINUTES = Object.fromEntries(
    Object.entries(TIMETABLES).map(([routeKey, schedule]) => [
      routeKey,
      Object.fromEntries(
        Object.entries(schedule).map(([period, times]) => [period, times.map(toMinutes)])
      )
    ])
  );

  const ROUTES = [
    {
      containerId: "departures-ph-bpt",
      timetableKey: "phToBpt",
      badges: [
        { label: "PH", className: "badge badge--origin" },
        { label: "BPT", className: "badge badge--dest" }
      ]
    },
    {
      containerId: "departures-bpt-ph",
      timetableKey: "bptToPh",
      badges: [
        { label: "BPT", className: "badge badge--dest" },
        { label: "PH", className: "badge badge--origin" }
      ]
    }
  ];

  function toMinutes(time) {
    const [hour, minute] = time.split(":").map(Number);
    return hour * 60 + minute;
  }

  function scheduleKey(dateTime) {
    return dateTime.weekday === 6 || dateTime.weekday === 7 ? "weekend" : "weekday";
  }

  function formatDayLabel(departure, now) {
    const diff = departure.startOf("day").diff(now.startOf("day"), "days").days;
    if (diff === 0) return "Today";
    if (diff === 1) return "Tomorrow";
    return departure.toFormat("ccc");
  }

  function describeCountdown(diffMinutes) {
    if (diffMinutes <= 0) {
      return { primary: "Now", unit: "", secondary: "" };
    }
    if (diffMinutes >= 60) {
      const hours = Math.floor(diffMinutes / 60);
      const mins = diffMinutes % 60;
      return {
        primary: hours,
        unit: hours === 1 ? "hr" : "hrs",
        secondary: mins ? `${mins} min` : ""
      };
    }
    return { primary: diffMinutes, unit: "min", secondary: "" };
  }

  function collectDepartures(timetableKey, count = ROW_COUNT) {
    const now = DateTime.now().setZone(TIMEZONE);
    const nowMinutes = now.hour * 60 + now.minute;
    const results = [];
    let cursor = now.startOf("day");

    const timetable = TIMETABLE_MINUTES[timetableKey];
    if (!timetable) {
      return results;
    }

    for (let dayOffset = 0; dayOffset < 4 && results.length < count; dayOffset += 1) {
      const key = scheduleKey(cursor);
      const minutes = timetable[key];
      if (!minutes) {
        continue;
      }

      minutes.forEach((minute) => {
        if (dayOffset === 0 && minute < nowMinutes) return;
        const departure = cursor.plus({ minutes: minute });
        const diff = Math.round(departure.diff(now, "minutes").minutes);
        results.push({
          diff,
          departure,
          dayLabel: formatDayLabel(departure, now),
          timeText: departure.toFormat("HH:mm"),
          ampm: "", // not used in 24h format
          scheduleKey: key
        });
      });

      cursor = cursor.plus({ days: 1 });
    }

    return results.slice(0, count);
  }

  function buildRow(data, badgeSet) {
    const row = document.createElement("article");
    row.className = "departure-row";
    if (data.diff <= 5) {
      row.classList.add("departing-soon");
    }

    const routeInfo = document.createElement("div");
    routeInfo.className = "route-info";

    const badgePair = document.createElement("div");
    badgePair.className = "badge-pair";

    badgeSet.forEach((badge, index) => {
      const badgeEl = document.createElement("span");
      badgeEl.className = badge.className;
      badgeEl.textContent = badge.label;
      badgePair.append(badgeEl);
      if (index === 0) {
        const arrow = document.createElement("span");
        arrow.className = "badge-arrow";
        arrow.textContent = "→";
        badgePair.append(arrow);
      }
    });

    const destinations = document.createElement("div");
    destinations.className = "destinations";

    const label = document.createElement("span");
    label.className = "label";
    label.textContent = `${data.timeText} ${data.ampm}`;

    const countdown = describeCountdown(data.diff);

    const sub = document.createElement("span");
    sub.className = "sub";
    const secondaryText = countdown.secondary ? ` ${countdown.secondary}` : "";
    sub.textContent = countdown.unit ? `${countdown.primary} ${countdown.unit}${secondaryText}` : countdown.primary;

    destinations.append(label, sub);
    routeInfo.append(badgePair, destinations);

    row.append(routeInfo);
    return row;
  }

  function updateBoard() {
    ROUTES.forEach((route) => {
      const container = document.getElementById(route.containerId);
      if (!container) return;

      container.innerHTML = "";
      const departures = collectDepartures(route.timetableKey);

      if (!departures.length) {
        const empty = document.createElement("p");
        empty.className = "departures__empty";
        empty.textContent = "No departures scheduled";
        container.append(empty);
        return;
      }

      departures.forEach((departure) => {
        container.append(buildRow(departure, route.badges));
      });
    });
  }

  function updateClock() {
    const clock = document.getElementById("clock");
    if (!clock) return;
    const now = DateTime.now().setZone(TIMEZONE);
    clock.textContent = now.toFormat("ccc, LLL d • HH:mm:ss");
  }

  function init() {
    updateBoard();
    updateClock();
    setInterval(updateBoard, 30 * 1000);
    setInterval(updateClock, 1000);
    document.addEventListener("visibilitychange", () => {
      if (!document.hidden) {
        updateBoard();
        updateClock();
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
