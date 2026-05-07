(function () {
  const existing = document.querySelector(".course-side-toc, .course-compact-toc");
  if (existing) return;

  const script = document.currentScript;
  const rootUrl = script ? new URL("../", script.src) : new URL("./", window.location.href);

  const pages = [
    {
      key: "index",
      number: "",
      title: "Course Index",
      path: "index.html",
      aliases: ["index.html", ""],
    },
    {
      key: "why",
      number: "00",
      title: "Why OxCaml Exists",
      navTitle: "Why",
      path: "sections/01-why-oxcaml-exists.html",
    },
    {
      key: "parallelism",
      number: "01",
      title: "Parallelism",
      navTitle: "Parallelism",
      path: "sections/02-parallelism-contention-portability.html",
    },
    {
      key: "allocation",
      number: "02",
      title: "Allocation",
      navTitle: "Allocation",
      path: "sections/03-locality-stack-zeroalloc.html",
    },
    {
      key: "representation",
      number: "03",
      title: "Value Layouts And Unboxing",
      navTitle: "Representation",
      path: "sections/04-representation.processed.html",
      aliases: ["sections/04-representation.html"],
    },
  ];
  const navPages = pages.filter((page) => page.key !== "index");

  const normalizePath = (url) => {
    const parsed = new URL(url, window.location.href);
    let path = decodeURI(parsed.pathname);
    if (path.endsWith("/")) path += "index.html";
    return path;
  };

  const currentPath = normalizePath(window.location.href);
  const pageHref = (path) => new URL(path, rootUrl).href;
  const pagePaths = (page) => [page.path].concat(page.aliases || []).map((path) => normalizePath(pageHref(path)));
  const currentPage = pages.find((page) => pagePaths(page).includes(currentPath)) || pages[0];

  const themes = [
    {
      key: "teal",
    },
    {
      key: "logo",
    },
  ];
  const themesByKey = new Map(themes.map((theme) => [theme.key, theme]));
  let currentThemeKey = "teal";

  const applyTheme = (themeKey) => {
    const theme = themesByKey.get(themeKey) || themes[0];
    currentThemeKey = theme.key;
    document.documentElement.dataset.courseTheme = theme.key;
  };

  applyTheme("teal");

  const slugBase = (text) =>
    text
      .trim()
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, "-")
      .replace(/^-+|-+$/g, "") || "section";

  const usedIds = new Set(Array.from(document.querySelectorAll("[id]")).map((el) => el.id));
  const uniqueId = (base) => {
    let id = base;
    let i = 2;
    while (usedIds.has(id)) {
      id = `${base}-${i}`;
      i += 1;
    }
    usedIds.add(id);
    return id;
  };

  const headings =
    currentPage.key === "index"
      ? []
      : Array.from(document.querySelectorAll("main h1, main h2, main h3"))
          .filter((heading) => heading.textContent.trim().length > 0)
          .map((heading) => {
            if (!heading.id) heading.id = uniqueId(slugBase(heading.textContent));
            const exerciseContainer = heading.closest(".exercise");
            const checkpointContainer = heading.closest(".checkpoint");
            return {
              id: heading.id,
              level: Number(heading.tagName.slice(1)),
              title: heading.textContent.trim().replace(/\s+/g, " "),
              element: heading,
              kind: exerciseContainer ? "exercise" : checkpointContainer ? "checkpoint" : "section",
            };
          });
  const exerciseHeadings = headings.filter((heading) => heading.kind === "exercise");

  const el = (tag, className, text) => {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  };

  const homeIcon = () => {
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("viewBox", "0 0 24 24");
    svg.setAttribute("aria-hidden", "true");
    svg.setAttribute("focusable", "false");
    const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
    path.setAttribute(
      "d",
      "M4.5 10.75 12 4.5l7.5 6.25v8.75a1 1 0 0 1-1 1h-4.75v-5.25h-3.5v5.25H5.5a1 1 0 0 1-1-1v-8.75Z"
    );
    svg.append(path);
    return svg;
  };

  const buildPageList = () => {
    const list = el("ol", "course-toc-list course-toc-pages");
    const homeItem = el("li");
    const homeLink = el("a", "course-toc-link course-toc-home-link");
    homeLink.href = pageHref("index.html");
    homeLink.dataset.coursePage = "index";
    homeLink.setAttribute("aria-label", "Course home");
    const homeIconWrap = el("span", "course-toc-home-icon");
    homeIconWrap.append(homeIcon());
    homeLink.append(homeIconWrap);
    if (currentPage.key === "index") {
      homeLink.classList.add("is-active");
      homeLink.setAttribute("aria-current", "page");
    }
    homeItem.append(homeLink);
    list.append(homeItem);

    for (const page of navPages) {
      const item = el("li");
      const link = el("a", "course-toc-link");
      link.href = pageHref(page.path);
      link.dataset.coursePage = page.key;
      if (page.key === currentPage.key) {
        link.classList.add("is-active");
        link.setAttribute("aria-current", "page");
      }
      link.append(el("span", "course-toc-text", page.navTitle || page.title));
      item.append(link);
      list.append(item);
    }
    return list;
  };

  const buildSectionList = () => {
    const list = el("ol", "course-toc-list course-toc-local-list");
    for (const heading of headings) {
      const item = el("li");
      item.className = `course-toc-item-level-${heading.level}`;
      const link = el("a", "course-toc-link");
      link.classList.add(`course-toc-link-level-${heading.level}`);
      link.classList.add(`course-toc-link-kind-${heading.kind}`);
      link.href = `#${heading.id}`;
      link.dataset.tocTarget = heading.id;
      link.append(el("span", "course-toc-text", heading.title));
      link.addEventListener("click", () => {
        holdActiveSection(heading.id);
        const compact = document.querySelector(".course-compact-toc");
        if (compact) compact.removeAttribute("open");
      });
      item.append(link);
      list.append(item);
    }
    return list;
  };

  const buildContent = () => {
    const fragment = document.createDocumentFragment();

    const pageSection = el("div", "course-toc-section course-toc-page-nav");
    pageSection.append(buildPageList());
    fragment.append(pageSection);

    if (headings.length > 0) {
      const localSection = el("div", "course-toc-section course-toc-local");
      localSection.append(buildSectionList());
      fragment.append(localSection);
    }

    return fragment;
  };

  const sideNav = el("nav", "course-side-toc");
  sideNav.setAttribute("aria-label", "Course table of contents");
  sideNav.append(buildContent());
  document.body.append(sideNav);
  document.body.classList.add("course-toc-ready");

  const compactNav = el("details", "course-compact-toc");
  const summary = el("summary", "course-compact-summary");
  summary.append(el("span", "course-compact-label", "Contents"));
  summary.append(el("span", "course-compact-current", currentPage.title));
  compactNav.append(summary);
  const compactPanel = el("div", "course-compact-panel");
  compactPanel.append(buildContent());
  compactNav.append(compactPanel);
  document.body.append(compactNav);

  let nextExerciseLink = null;
  if (exerciseHeadings.length > 0) {
    nextExerciseLink = el("a", "course-next-exercise", "Next exercise");
    nextExerciseLink.setAttribute("aria-label", "Jump to next exercise");
    document.body.append(nextExerciseLink);
  }

  const activeLinks = () => Array.from(document.querySelectorAll("[data-toc-target]"));
  const currentSummary = compactNav.querySelector(".course-compact-current");

  let activeId = "";
  let scheduled = false;
  let heldActiveId = "";
  let holdTimer = 0;

  const setActiveSection = (id) => {
    if (id === activeId) return;
    activeId = id;
    for (const link of activeLinks()) {
      const isActive = link.dataset.tocTarget === id;
      link.classList.toggle("is-active", isActive);
      if (isActive) link.setAttribute("aria-current", "location");
      else link.removeAttribute("aria-current");
    }
    const activeHeading = headings.find((heading) => heading.id === id);
    currentSummary.textContent = activeHeading
      ? `${currentPage.title} / ${activeHeading.title}`
      : currentPage.title;
  };

  const nextExerciseAfterViewport = () => {
    if (exerciseHeadings.length === 0) return null;
    const y = window.scrollY + 170;
    return exerciseHeadings.find((heading) => heading.element.offsetTop > y) || exerciseHeadings[0];
  };

  const updateNextExerciseLink = () => {
    if (!nextExerciseLink) return;
    const nextExercise = nextExerciseAfterViewport();
    if (!nextExercise) return;
    nextExerciseLink.href = `#${nextExercise.id}`;
    nextExerciseLink.title = nextExercise.title;
  };

  if (nextExerciseLink) {
    nextExerciseLink.addEventListener("click", (event) => {
      const nextExercise = nextExerciseAfterViewport();
      if (!nextExercise) return;
      event.preventDefault();
      holdActiveSection(nextExercise.id);
      nextExercise.element.scrollIntoView({ behavior: "smooth", block: "start" });
      window.history.replaceState(null, "", `#${nextExercise.id}`);
      updateNextExerciseLink();
    });
  }

  const holdActiveSection = (id) => {
    heldActiveId = id;
    window.clearTimeout(holdTimer);
    setActiveSection(id);
    holdTimer = window.setTimeout(() => {
      if (heldActiveId === id) heldActiveId = "";
    }, 700);
  };

  const updateActiveSection = () => {
    scheduled = false;
    if (headings.length === 0) return;
    if (heldActiveId) {
      setActiveSection(heldActiveId);
      return;
    }
    let current = headings[0];
    for (const heading of headings) {
      if (heading.element.getBoundingClientRect().top <= 150) current = heading;
      else break;
    }
    setActiveSection(current.id);
    updateNextExerciseLink();
  };

  const scheduleUpdate = () => {
    if (scheduled) return;
    scheduled = true;
    window.requestAnimationFrame(updateActiveSection);
  };

  updateActiveSection();
  updateNextExerciseLink();
  window.addEventListener("scroll", scheduleUpdate, { passive: true });
  window.addEventListener("resize", scheduleUpdate);
})();
