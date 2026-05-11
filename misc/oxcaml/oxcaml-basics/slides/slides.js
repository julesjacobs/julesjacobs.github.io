(function () {
  function dedentSource(source) {
    const lines = source.replace(/\r\n?/g, "\n").split("\n");
    while (lines.length && lines[0].trim() === "") lines.shift();
    while (lines.length && lines[lines.length - 1].trim() === "") lines.pop();

    const indent = lines.reduce((minimum, line) => {
      if (line.trim() === "") return minimum;
      const width = line.match(/^[\t ]*/)[0].length;
      return Math.min(minimum, width);
    }, Infinity);

    const dedented = lines.map((line) => line.slice(Number.isFinite(indent) ? indent : 0));
    if (dedented.length) dedented[0] = dedented[0].trimStart();
    return dedented.join("\n");
  }

  function normalizeCodeIndentation() {
    document.querySelectorAll("pre code, oxcaml").forEach((block) => {
      block.textContent = dedentSource(block.textContent);
    });
  }

  function escapeHtml(text) {
    return text
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;");
  }

  function span(cls, text) {
    return `<span class="${cls}">${escapeHtml(text)}</span>`;
  }

  function highlightOcaml(source) {
    const keywords = new Set([
      "and", "as", "begin", "class", "constraint", "do", "done", "downto", "else", "end",
      "exception", "external", "false", "for", "fun", "function", "functor", "if", "in",
      "include", "inherit", "initializer", "lazy", "let", "match", "method", "module", "mutable",
      "new", "nonrec", "object", "of", "open", "private", "rec", "sig", "struct", "then", "to",
      "true", "try", "type", "val", "virtual", "when", "while", "with"
    ]);
    const typeWords = new Set([
      "bool", "contended", "float", "float64", "float64s", "global", "immediate", "int", "local",
      "nonportable", "portable", "shareable", "shared", "stateless", "string", "uncontended", "unit", "value"
    ]);
    const constructors = new Set(["None", "Null", "Some", "This"]);

    let html = "";
    let i = 0;
    while (i < source.length) {
      const rest = source.slice(i);
      const whitespace = /^[\s]+/.exec(rest);
      if (whitespace) {
        html += escapeHtml(whitespace[0]);
        i += whitespace[0].length;
        continue;
      }

      if (rest.startsWith("(*")) {
        const end = source.indexOf("*)", i + 2);
        const text = end === -1 ? source.slice(i) : source.slice(i, end + 2);
        html += span("tok-comment", text);
        i += text.length;
        continue;
      }

      const string = /^"([^"\\]|\\.)*"/.exec(rest);
      if (string) {
        html += span("tok-string", string[0]);
        i += string[0].length;
        continue;
      }

      const charLiteral = /^'([^'\\]|\\.)'/.exec(rest);
      if (charLiteral) {
        html += span("tok-string", charLiteral[0]);
        i += charLiteral[0].length;
        continue;
      }

      const typeVariable = /^'[A-Za-z_][A-Za-z0-9_']*/.exec(rest);
      if (typeVariable) {
        html += span("tok-type", typeVariable[0]);
        i += typeVariable[0].length;
        continue;
      }

      const number = /^\d+(?:\.\d+)?[lLn]?/.exec(rest);
      if (number) {
        html += span("tok-number", number[0]);
        i += number[0].length;
        continue;
      }

      const identifier = /^[A-Za-z_][A-Za-z0-9_']*/.exec(rest);
      if (identifier) {
        const word = identifier[0];
        const cls = keywords.has(word)
          ? "tok-keyword"
          : typeWords.has(word)
            ? "tok-type"
            : constructors.has(word) || /^[A-Z]/.test(word)
              ? "tok-constructor"
              : "";
        html += cls ? span(cls, word) : escapeHtml(word);
        i += word.length;
        continue;
      }

      const operator = /^[()[\]{};,:.=#@|&+\-*\/<>_!%]+/.exec(rest);
      if (operator) {
        html += span("tok-operator", operator[0]);
        i += operator[0].length;
        continue;
      }

      html += escapeHtml(source[i]);
      i += 1;
    }
    return html;
  }

  function highlightStaticCode() {
    document.querySelectorAll("pre code").forEach((block) => {
      if (block.closest(".oxcaml-embed")) return;
      block.innerHTML = highlightOcaml(block.textContent);
      block.dataset.highlighted = "true";
    });
  }

  function setupPredictionTables() {
    document.querySelectorAll("[data-prediction-table]").forEach((table) => {
      const buttons = Array.from(table.querySelectorAll("button[data-answer]"));

      function setButton(button, value) {
        button.dataset.value = value;
        button.textContent = value || "?";
        button.classList.remove("is-correct", "is-incorrect");
      }

      buttons.forEach((button) => {
        setButton(button, "");
      });
    });
  }

  function cyclePredictionButton(button, feedback) {
    const current = button.dataset.value || "";
    const next = current === "" ? "yes" : current === "yes" ? "no" : "";
    button.dataset.value = next;
    button.textContent = next || "?";
    button.classList.remove("is-correct", "is-incorrect");
    if (feedback) feedback.textContent = "";
  }

  function checkPredictionTable(table, feedback) {
    const buttons = Array.from(table.querySelectorAll("button[data-answer]"));
    let filled = 0;
    let correct = 0;
    buttons.forEach((button) => {
      button.classList.remove("is-correct", "is-incorrect");
      if (!button.dataset.value) return;
      filled += 1;
      if (button.dataset.value === button.dataset.answer) {
        correct += 1;
        button.classList.add("is-correct");
      } else {
        button.classList.add("is-incorrect");
      }
    });
    if (feedback) {
      feedback.textContent = `${correct}/${buttons.length} correct; ${buttons.length - filled} blank.`;
    }
  }

  function resetPredictionTable(table, feedback) {
    table.querySelectorAll("button[data-answer]").forEach((button) => {
      button.dataset.value = "";
      button.textContent = "?";
      button.classList.remove("is-correct", "is-incorrect");
    });
    if (feedback) feedback.textContent = "";
  }

  function showStateWidgetState(widget, state) {
    const triad = widget.querySelector(".storage-triad, .memory-map");
    const tabs = Array.from(widget.querySelectorAll("[data-state]"));
    const panels = Array.from(widget.querySelectorAll("[data-show]"));
    const visibleByState = Array.from(widget.querySelectorAll("[data-visible-states]"));

    if (triad) triad.dataset.currentState = state;
    if (widget.dataset.allocationState !== undefined) widget.dataset.allocationState = state;
    tabs.forEach((tab) => {
      tab.setAttribute("aria-selected", String(tab.dataset.state === state));
    });
    panels.forEach((panel) => {
      panel.classList.toggle("is-visible", panel.dataset.show === state);
    });
    visibleByState.forEach((node) => {
      const isVisible = node.dataset.visibleStates.split(/\s+/).includes(state);
      node.hidden = !isVisible;
      node.classList.toggle("is-visible", isVisible);
    });
  }

  function setupStateWidgets() {
    document.querySelectorAll("[data-state-widget]").forEach((widget) => {
      const tabs = Array.from(widget.querySelectorAll("[data-state]"));

      tabs.forEach((tab) => {
        const activate = (event) => {
          event.preventDefault();
          showStateWidgetState(widget, tab.dataset.state);
        };
        tab.onclick = activate;
        tab.addEventListener("click", activate);
        tab.addEventListener("pointerdown", activate);
      });
      widget.addEventListener("click", (event) => {
        const tab = event.target.closest("[data-state]");
        if (!tab || !widget.contains(tab)) return;
        showStateWidgetState(widget, tab.dataset.state);
      });
      showStateWidgetState(widget, tabs[0]?.dataset.state || "heap");
    });
  }

  function setupDelegatedInteractions() {
    document.addEventListener("click", (event) => {
      const stateButton = event.target.closest("[data-allocation-state-button]");
      if (stateButton) {
        const widget = stateButton.closest("[data-state-widget]");
        if (widget) showStateWidgetState(widget, stateButton.dataset.state);
        return;
      }

      const answer = event.target.closest("button[data-answer]");
      if (answer) {
        const slide = answer.closest(".slide");
        const feedback = slide?.querySelector("[data-table-feedback]");
        cyclePredictionButton(answer, feedback);
        return;
      }

      const check = event.target.closest("[data-check-table]");
      if (check) {
        const slide = check.closest(".slide");
        const table = slide?.querySelector("[data-prediction-table]");
        const feedback = slide?.querySelector("[data-table-feedback]");
        if (table) checkPredictionTable(table, feedback);
        return;
      }

      const reset = event.target.closest("[data-reset-table]");
      if (reset) {
        const slide = reset.closest(".slide");
        const table = slide?.querySelector("[data-prediction-table]");
        const feedback = slide?.querySelector("[data-table-feedback]");
        if (table) resetPredictionTable(table, feedback);
        return;
      }

      const stateTab = event.target.closest("[data-state]");
      if (stateTab) {
        const widget = stateTab.closest("[data-state-widget]");
        if (widget) showStateWidgetState(widget, stateTab.dataset.state);
      }
    });
  }

  function keepRevealOutOfInteractiveControls() {
    const selector = [
      "button",
      "input",
      "textarea",
      "select",
      "[contenteditable]",
      "oxcaml",
      ".oxcaml-embed",
      ".live-editor-frame"
    ].join(",");

    document.addEventListener(
      "keydown",
      (event) => {
        if (!event.target.closest(selector)) return;
        if (["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", " ", "Enter"].includes(event.key)) {
          event.stopPropagation();
        }
      },
      true
    );
  }

  function setupExerciseJump() {
    const exerciseSlides = Reveal.getSlides().filter((slide) => slide.classList.contains("exercise-slide"));
    if (!exerciseSlides.length) return;

    const button = document.createElement("button");
    button.type = "button";
    button.className = "exercise-jump";
    button.textContent = "Next exercise";
    button.setAttribute("aria-label", "Jump to next exercise slide");
    document.querySelector(".reveal")?.append(button);

    const indicesFor = (slide) => Reveal.getIndices(slide);
    const pastCountFor = (slide) => Reveal.getSlidePastCount(slide);

    function nextExerciseSlide() {
      const current = Reveal.getCurrentSlide();
      const currentPast = current ? pastCountFor(current) : -1;
      return (
        exerciseSlides.find((slide) => pastCountFor(slide) > currentPast) ||
        exerciseSlides[0]
      );
    }

    function animateExerciseSlide(slide) {
      slide.classList.remove("exercise-targeted");
      window.setTimeout(() => {
        slide.classList.add("exercise-targeted");
        window.setTimeout(() => slide.classList.remove("exercise-targeted"), 1500);
      }, 120);
    }

    function updateVisibility() {
      const current = Reveal.getCurrentSlide();
      button.classList.toggle("is-hidden", current?.classList.contains("exercise-slide"));
    }

    button.addEventListener("click", (event) => {
      event.preventDefault();
      event.stopPropagation();
      const target = nextExerciseSlide();
      if (!target) return;
      const indices = indicesFor(target);
      Reveal.slide(indices.h, indices.v, indices.f);
      animateExerciseSlide(target);
    });
    Reveal.on("slidechanged", updateVisibility);
    updateVisibility();
  }

  normalizeCodeIndentation();
  highlightStaticCode();
  setupDelegatedInteractions();
  keepRevealOutOfInteractiveControls();

  Reveal.initialize({
    width: 1366,
    height: 768,
    margin: 0,
    minScale: 0.05,
    maxScale: 2,
    hash: true,
    controls: false,
    progress: true,
    slideNumber: "c/t",
    center: false,
    transition: "none",
    backgroundTransition: "none",
    plugins: [RevealNotes]
  }).then(() => {
    setupStateWidgets();
    setupExerciseJump();
  });
}());
