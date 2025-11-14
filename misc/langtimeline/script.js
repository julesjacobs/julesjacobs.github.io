document.addEventListener('DOMContentLoaded', () => {
  const railButtons = Array.from(document.querySelectorAll('.timeline-rail__list button[data-target]'));
  const events = Array.from(document.querySelectorAll('.timeline-event'));

  if (!railButtons.length || !events.length) {
    return;
  }

  const targetToButton = new Map();
  railButtons.forEach((button) => {
    const id = button.dataset.target;
    if (id) {
      targetToButton.set(id, button);
      button.addEventListener('click', () => {
        const el = document.getElementById(id);
        if (el) {
          el.scrollIntoView({ behavior: 'smooth', block: 'center' });
        }
      });
    }
  });

  let activeId = events[0].id;
  setActive(activeId);

  const observer = new IntersectionObserver(
    (entries) => {
      const visible = entries
        .filter((entry) => entry.isIntersecting)
        .sort((a, b) => b.intersectionRatio - a.intersectionRatio);

      if (!visible.length) {
        return;
      }

      const top = visible[0].target;
      if (top.id && top.id !== activeId) {
        setActive(top.id);
      }
    },
    {
      root: null,
      rootMargin: '-40% 0px -50% 0px',
      threshold: [0.1, 0.25, 0.5, 0.75],
    }
  );

  events.forEach((event) => observer.observe(event));

  function setActive(id) {
    activeId = id;
    events.forEach((event) => {
      event.classList.toggle('is-active', event.id === id);
    });

    railButtons.forEach((button) => {
      const isActive = button.dataset.target === id;
      button.setAttribute('aria-current', isActive ? 'true' : 'false');
      const li = button.closest('li');
      if (li) {
        li.classList.toggle('is-active', isActive);
      }
    });
  }
});
