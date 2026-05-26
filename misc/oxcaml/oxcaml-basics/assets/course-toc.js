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
      path: "sections/00-why-oxcaml-exists.html",
    },
    {
      key: "allocation",
      number: "01",
      title: "Locality And Stack Allocation",
      navTitle: "Locality",
      path: "sections/01-locality-stack-allocation.html",
    },
    {
      key: "representation",
      number: "02",
      title: "Value Layouts And Unboxing",
      navTitle: "Representation",
      path: "sections/02-value-layouts-unboxing.processed.html",
      aliases: ["sections/02-value-layouts-unboxing.html"],
    },
    {
      key: "parallelism",
      number: "03",
      title: "Parallelism",
      navTitle: "Parallelism",
      path: "sections/03-parallelism-contention-portability.html",
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
          .filter((heading) => {
            if (heading.closest(".exercise, .checkpoint")) return true;
            return !heading.closest(".card, .diagram-card, .axis-strip, .value-model-panel");
          })
          .map((heading) => {
            if (!heading.id) heading.id = uniqueId(slugBase(heading.textContent));
            const exerciseContainer = heading.closest(".exercise");
            const checkpointContainer = heading.closest(".checkpoint");
            return {
              id: heading.id,
              level: Number(heading.tagName.slice(1)),
              title: heading.textContent.trim().replace(/\s+/g, " "),
              element: heading,
              exerciseContainer,
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

  const initializeExerciseFreeformAnswers = () => {
    const storageAvailable = (() => {
      try {
        const key = "oxcaml-basics:storage-test";
        window.localStorage.setItem(key, "1");
        window.localStorage.removeItem(key);
        return true;
      } catch {
        return false;
      }
    })();
    const storagePrefix = "oxcaml-basics:exercise-freeform:v1:";
    const pageKey = window.location.pathname.replace(/\/+/g, "/");
    const answerSummaryPattern = /^answer(?:\s+key)?$/i;

    document.querySelectorAll(".exercise").forEach((exercise, index) => {
      if (exercise.dataset.freeformInitialized) return;
      exercise.dataset.freeformInitialized = "true";
      const answerDetails = Array.from(exercise.querySelectorAll("details")).find((details) => {
        const summary = details.querySelector("summary");
        return summary && answerSummaryPattern.test(summary.textContent.trim());
      });
      if (!answerDetails) return;
      if (
        exercise.querySelector(
          ".exercise-choice, .exercise-freeform-textarea, input, select, textarea, [contenteditable='true'], oxcaml, .oxcaml-embed"
        )
      ) {
        return;
      }

      const heading = exercise.querySelector("h2, h3, h4, h5, h6");
      const exerciseId = heading?.id || uniqueId(`exercise-${index + 1}`);
      if (heading && !heading.id) heading.id = exerciseId;
      const textareaId = `${exerciseId}-freeform-answer`;
      const storageKey = `${storagePrefix}${pageKey}#${exerciseId}`;

      const wrapper = el("div", "exercise-freeform");
      const label = el("label", "exercise-freeform-label", "Your answer");
      label.setAttribute("for", textareaId);
      const textarea = document.createElement("textarea");
      textarea.className = "exercise-freeform-textarea";
      textarea.id = textareaId;
      textarea.rows = 5;
      textarea.spellcheck = true;
      textarea.placeholder = "Write your answer here before opening the answer key.";

      if (storageAvailable) {
        textarea.value = window.localStorage.getItem(storageKey) || "";
        textarea.addEventListener("input", () => {
          if (textarea.value) window.localStorage.setItem(storageKey, textarea.value);
          else window.localStorage.removeItem(storageKey);
        });
      }

      wrapper.append(label, textarea);
      exercise.insertBefore(wrapper, answerDetails);
    });
  };

  initializeExerciseFreeformAnswers();

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
  let lastExerciseJumpId = "";
  let lastExerciseJumpTime = 0;
  const exerciseScrollGap = 86;
  const targetAnimationTimers = new WeakMap();

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

  const headingDocumentTop = (heading) =>
    heading.element.getBoundingClientRect().top + window.scrollY;

  const exerciseAfter = (heading) => {
    const index = exerciseHeadings.indexOf(heading);
    if (index < 0) return exerciseHeadings[0] || null;
    return exerciseHeadings[index + 1] || exerciseHeadings[0] || null;
  };

  const nextExerciseAfterViewport = () => {
    if (exerciseHeadings.length === 0) return null;
    const y = window.scrollY + exerciseScrollGap + 24;
    let nextExercise = exerciseHeadings.find((heading) => headingDocumentTop(heading) > y) || exerciseHeadings[0];

    const lastJumpTarget = exerciseHeadings.find((heading) => heading.id === lastExerciseJumpId);
    if (lastJumpTarget && nextExercise === lastJumpTarget) {
      const expectedTop = window.scrollY + exerciseScrollGap;
      const recentJump = window.performance.now() - lastExerciseJumpTime < 5000;
      const nearLastJumpTarget = Math.abs(headingDocumentTop(lastJumpTarget) - expectedTop) < 260;
      if (recentJump || nearLastJumpTarget) nextExercise = exerciseAfter(lastJumpTarget);
    }

    return nextExercise;
  };

  const updateNextExerciseLink = () => {
    if (!nextExerciseLink) return;
    const nextExercise = nextExerciseAfterViewport();
    if (!nextExercise) return;
    nextExerciseLink.href = `#${nextExercise.id}`;
    nextExerciseLink.title = nextExercise.title;
  };

  const animateTargetExercise = (heading) => {
    const target = heading.exerciseContainer || heading.element;
    const priorTimer = targetAnimationTimers.get(target);
    if (priorTimer) window.clearTimeout(priorTimer);
    target.classList.remove("course-exercise-targeted");
    void target.offsetWidth;
    target.classList.add("course-exercise-targeted");
    targetAnimationTimers.set(
      target,
      window.setTimeout(() => target.classList.remove("course-exercise-targeted"), 1500)
    );
  };

  const animateTargetExerciseWhenVisible = (heading) => {
    const target = heading.exerciseContainer || heading.element;
    const started = window.performance.now();
    let lastScrollY = window.scrollY;
    let settledFrames = 0;
    const tick = () => {
      const rect = target.getBoundingClientRect();
      const visible = rect.top < window.innerHeight * 0.85 && rect.bottom > 80;
      const scrollDelta = Math.abs(window.scrollY - lastScrollY);
      settledFrames = scrollDelta < 0.5 ? settledFrames + 1 : 0;
      lastScrollY = window.scrollY;
      if ((visible && settledFrames >= 5) || (visible && window.performance.now() - started > 1600)) {
        animateTargetExercise(heading);
      } else {
        window.requestAnimationFrame(tick);
      }
    };
    window.requestAnimationFrame(tick);
  };

  const scrollToExercise = (heading) => {
    const targetY = headingDocumentTop(heading) - exerciseScrollGap;
    window.scrollTo({ top: Math.max(0, targetY), behavior: "smooth" });
  };

  if (nextExerciseLink) {
    nextExerciseLink.addEventListener("click", (event) => {
      const nextExercise = nextExerciseAfterViewport();
      if (!nextExercise) return;
      event.preventDefault();
      lastExerciseJumpId = nextExercise.id;
      lastExerciseJumpTime = window.performance.now();
      holdActiveSection(nextExercise.id);
      scrollToExercise(nextExercise);
      window.history.replaceState(null, "", `#${nextExercise.id}`);
      animateTargetExerciseWhenVisible(nextExercise);
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
