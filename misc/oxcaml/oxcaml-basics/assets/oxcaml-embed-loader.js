(function () {
  const version = "20260428-single-mount";
  const script = document.currentScript;
  const localHostnames = new Set(["localhost", "127.0.0.1", "::1"]);
  const baseUrl = localHostnames.has(window.location.hostname)
    ? new URL("../../playground/", script?.src || document.baseURI).href
    : "https://julesjacobs.com/misc/oxcaml/playground/";
  const scrollKey = `oxcaml-course-scroll:${window.location.pathname}${window.location.search}`;
  let savedScroll = readSavedScroll();
  let userInterruptedScrollRestore = false;

  if ("scrollRestoration" in window.history) {
    window.history.scrollRestoration = "manual";
  }

  function readSavedScroll() {
    try {
      const raw = window.sessionStorage.getItem(scrollKey);
      return raw ? JSON.parse(raw) : null;
    } catch {
      return null;
    }
  }

  function prepareScrollAnchors() {
    document.querySelectorAll("oxcaml").forEach((element) => {
      if (element.closest(".code-with-figure")) {
        return;
      }
      if (element.parentElement?.classList.contains("course-scroll-anchor")) {
        return;
      }

      const wrapper = document.createElement("div");
      wrapper.className = "course-scroll-anchor";
      element.before(wrapper);
      wrapper.append(element);
    });

    const candidates = document.querySelectorAll(
      [
        "main > h1",
        "main > p",
        "main > section",
        "main > section > h2",
        "main > section > h3",
        "main > section > p",
        "main > section > ul",
        "main > section > aside",
        "main > section > figure",
        "main > section > .course-scroll-anchor",
        "main > section > .code-with-figure",
        "main > section > .diagram-grid",
        "main > section > .comparison",
        "main > section > .axis-grid",
        "main > section > .capture-rule-list",
        "main > section > .capture-matrix",
        "main > nav"
      ].join(", ")
    );

    candidates.forEach((element, index) => {
      element.setAttribute("data-course-scroll-anchor", String(index));
    });
  }

  function anchorForScrollPosition() {
    prepareScrollAnchors();

    const probeY = Math.min(window.innerHeight - 1, 96);
    let element = document.elementFromPoint(window.innerWidth / 2, probeY);
    while (element && element !== document.documentElement) {
      if (element.hasAttribute("data-course-scroll-anchor")) {
        return element;
      }
      element = element.parentElement;
    }

    const anchors = Array.from(document.querySelectorAll("[data-course-scroll-anchor]"));
    let chosen = anchors[0] || null;
    for (const anchor of anchors) {
      if (anchor.offsetTop <= window.scrollY + probeY) {
        chosen = anchor;
      }
    }
    return chosen;
  }

  function saveScrollPosition() {
    const anchor = anchorForScrollPosition();
    window.sessionStorage.setItem(
      scrollKey,
      JSON.stringify(
        anchor
          ? {
              anchorId: anchor.getAttribute("data-course-scroll-anchor"),
              anchorOffset: window.scrollY - anchor.offsetTop,
              scrollY: window.scrollY,
            }
          : { scrollY: window.scrollY }
      )
    );
  }

  window.addEventListener("beforeunload", saveScrollPosition);
  window.addEventListener("pagehide", saveScrollPosition);

  for (const eventName of ["wheel", "touchstart", "keydown", "mousedown"]) {
    window.addEventListener(
      eventName,
      () => {
        userInterruptedScrollRestore = true;
      },
      { passive: true }
    );
  }

  function restoreScrollWhileLayoutSettles() {
    prepareScrollAnchors();

    if (!savedScroll || (savedScroll.scrollY ?? 0) <= 0) {
      return;
    }

    let attempts = 0;
    let stableFrames = 0;
    let lastHeight = 0;

    function tick() {
      if (userInterruptedScrollRestore) {
        return;
      }

      const pageHeight = document.documentElement.scrollHeight;
      const maxScrollY = Math.max(0, pageHeight - window.innerHeight);
      prepareScrollAnchors();
      const anchor = savedScroll.anchorId != null
        ? document.querySelector(`[data-course-scroll-anchor="${CSS.escape(String(savedScroll.anchorId))}"]`)
        : null;
      const targetY = anchor
        ? anchor.offsetTop + (savedScroll.anchorOffset || 0)
        : savedScroll.scrollY || 0;
      window.scrollTo(0, Math.min(targetY, maxScrollY));

      stableFrames = pageHeight === lastHeight ? stableFrames + 1 : 0;
      lastHeight = pageHeight;
      attempts += 1;

      const playgroundBusy = document.querySelector(
        '.oxcaml-embed[data-state="loading"], .oxcaml-embed[data-state="running"]'
      );
      if (attempts < 900 && (playgroundBusy || stableFrames < 30)) {
        window.requestAnimationFrame(tick);
      }
    }

    window.requestAnimationFrame(tick);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", restoreScrollWhileLayoutSettles, { once: true });
  } else {
    restoreScrollWhileLayoutSettles();
  }

  const embedScript = document.createElement("script");
  embedScript.src = new URL(`oxcaml-embed.js?v=${version}`, baseUrl).href;
  embedScript.addEventListener("load", restoreScrollWhileLayoutSettles, { once: true });
  document.head.appendChild(embedScript);
}());
