// The player around the film (tools/web.py copies it into build/web/). The film is a page whose every frame is a
// function of time, window.seek(t); here an <audio> element is the clock, and each animation frame shows
// seek(audio.currentTime). Settings come from window.PLAYER: { title, film, audio, poster: [segment, cue, dt], captions }.
'use strict';
(function () {
  const P = window.PLAYER || {}, W = 1920, H = 1080;
  const $ = (tag, cls, parent, html) => { const e = document.createElement(tag); if (cls) e.className = cls; if (html !== undefined) e.innerHTML = html; if (parent) parent.appendChild(e); return e; };
  const svg = d => `<svg viewBox="0 0 24 24" aria-hidden="true">${d}</svg>`;
  const ICON = {
    play: svg('<path d="M7 4.5v15l12.5-7.5z" fill="currentColor"/>'),
    pause: svg('<rect x="6" y="4.5" width="4" height="15" rx="1" fill="currentColor"/><rect x="14" y="4.5" width="4" height="15" rx="1" fill="currentColor"/>'),
    chapters: svg('<g fill="currentColor"><circle cx="5" cy="6.5" r="1.4"/><circle cx="5" cy="12" r="1.4"/><circle cx="5" cy="17.5" r="1.4"/></g><g stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M9.5 6.5h10M9.5 12h10M9.5 17.5h10"/></g>'),
    cc: svg('<rect x="2.5" y="5" width="19" height="14" rx="3" fill="none" stroke="currentColor" stroke-width="1.8"/><path d="M10.6 10.2a2.3 2.3 0 1 0 0 3.6M17.4 10.2a2.3 2.3 0 1 0 0 3.6" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/>'),
    full: svg('<path d="M4 9V4h5M15 4h5v5M20 15v5h-5M9 20H4v-5" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>'),
    unfull: svg('<path d="M9 4v5H4M20 9h-5V4M15 20v-5h5M4 15h5v5" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>'),
  };

  // ---- the page -----------------------------------------------------------------------------------------------
  const player = document.getElementById('player'), frame = document.getElementById('frame'), box = document.getElementById('box'), scaler = document.getElementById('scaler');
  const stage = document.getElementById('stage');
  const audio = $('audio', null, player); audio.preload = 'none'; audio.src = P.audio;
  const capRow = $('div', 'caption', box), capSpan = $('span', null, capRow); capRow.style.display = 'none';
  const big = $('button', 'big', box, ICON.play); big.setAttribute('aria-label', 'Play');
  $('div', 'spin', box);
  const msg = $('div', 'msg', box); msg.setAttribute('role', 'alert');
  const bar = $('div', 'bar', frame);
  const scrub = $('div', 'scrub', bar); scrub.tabIndex = 0; scrub.setAttribute('role', 'slider'); scrub.setAttribute('aria-label', 'Position');
  const track = $('div', 'track', scrub), played = $('div', 'played', track), knob = $('div', 'knob', scrub), tip = $('div', 'tip', scrub);
  const row = $('div', 'row', bar);
  const btn = (cls, label, html) => { const b = $('button', cls, row, html); b.type = 'button'; b.setAttribute('aria-label', label); b.title = label; b.addEventListener('mousedown', e => e.preventDefault()); return b; };
  const bPlay = btn('play', 'Play (k)', ICON.play);
  const time = $('span', 'time', row), chapName = $('span', 'chap', row); $('span', 'gap', row);
  const bChap = btn('chapters', 'Chapters', ICON.chapters);
  const bSpeed = btn('speed', 'Speed', '1×');
  const bCC = btn('cc', 'Captions (c)', ICON.cc);
  const bFull = btn('full', 'Full screen (f)', ICON.full);
  const menu = $('div', 'menu', frame); menu.setAttribute('role', 'menu');
  const NO_SOUND = 'The sound (audio.m4a) could not be loaded, and the video plays to it. Check the connection and press play again.';
  const say = text => { msg.textContent = text; msg.classList.toggle('on', !!text); };

  // the stage keeps its 1920 x 1080 coordinates and is scaled to the box
  let k = 0.5;
  const fit = () => {
    const vw = player.clientWidth, vh = player.clientHeight, barh = bar.offsetHeight || 56, w = Math.min(vw, vh * 16 / 9);
    frame.classList.toggle('under', !isFull() && vh - w * 9 / 16 >= barh);
    k = box.clientWidth / W; scaler.style.transform = `scale(${k})`; frame.style.setProperty('--k', k.toFixed(4));
    frame.style.setProperty('--menuh', Math.max(120, frame.getBoundingClientRect().bottom - barh - 14) + 'px');
  };
  const isFull = () => !!(document.fullscreenElement || document.webkitFullscreenElement);
  new ResizeObserver(fit).observe(player); new ResizeObserver(fit).observe(box); fit();

  // ---- the film's script, once its fonts are there (the code's character grid and labels are measured when the
  // scenes are built, and a face loaded later would show a frame in another one) ----------------------------------
  const faces = ['450 50px "Fira Code"', '400 64px "Source Serif 4 Film"', 'italic 400 64px "Source Serif 4 Film"'];
  const fontsIn = Promise.race([Promise.all(faces.map(f => document.fonts.load(f))), new Promise(r => setTimeout(r, 8000))]).catch(() => {});
  fontsIn.then(() => {
    const s = document.createElement('script'); s.src = P.film;
    s.onload = () => document.fonts.ready.then(start);
    s.onerror = () => say('The film could not be loaded (film.js).');
    document.body.appendChild(s);
  });

  // ---- state ------------------------------------------------------------------------------------------------------
  let total = 1, chapters = [], caps = [], pos = 0, shown = -1, started = false, told = false, dragging = false, pendingSeek = false;
  let capsOn = !!P.captions, speeds = [1, 1.25, 1.5], speedI = 0, ready = false;
  const fmt = t => { t = Math.max(0, Math.floor(t)); const h = Math.floor(t / 3600), m = Math.floor(t % 3600 / 60), s = String(t % 60).padStart(2, '0'); return h ? `${h}:${String(m).padStart(2, '0')}:${s}` : `${m}:${s}`; };
  const clampT = t => Math.max(0, Math.min(total, t));
  const chapterAt = t => { let c = null; for (const x of chapters) { if (x.start <= t + 1e-6) c = x; else break; } return c; };
  const capAt = t => { let lo = 0, hi = caps.length - 1, r = -1; while (lo <= hi) { const m = (lo + hi) >> 1; if (caps[m][0] <= t) { r = m; lo = m + 1; } else hi = m - 1; } return r >= 0 && t < caps[r][1] ? caps[r][2] : null; };
  const playing = () => started && !audio.paused && !audio.ended;

  // the start time from the address: ?t=754, #t=754, t=12:34 or t=12m34s
  function urlTime() {
    const q = new URLSearchParams(location.search).get('t') ?? new URLSearchParams(location.hash.slice(1)).get('t');
    if (!q) return null;
    let m;
    if ((m = q.match(/^(?:(\d+):)?(\d+):(\d+(?:\.\d+)?)$/))) return (+(m[1] || 0)) * 3600 + (+m[2]) * 60 + (+m[3]);
    if ((m = q.match(/^(?:(\d+)h)?(?:(\d+)m)?(?:(\d+(?:\.\d+)?)s?)?$/)) && q) return (+(m[1] || 0)) * 3600 + (+(m[2] || 0)) * 60 + (+(m[3] || 0));
    return null;
  }

  function start() {
    if (typeof window.seek !== 'function') { say('The video could not be started.'); return; }
    stage.style.transform = ''; stage.style.transformOrigin = '';   // film.js fits the stage to its window; the player scales it
    // the film's own hairline of progress at the bottom of the stage: the scrub bar says the same
    for (const e of stage.querySelectorAll(':scope > div')) if (e.style.top === (H - 4) + 'px' && e.style.height === '4px') e.style.display = 'none';
    const T = window.TIMING || { scenes: [], total: window.DURATION || 0 };
    total = window.DURATION || T.total || 1;
    caps = (window.CAPTIONS || []).slice().sort((a, b) => a[0] - b[0]);
    // chapters: a segment's chapter; consecutive segments share one. The unnamed opening is "Opening".
    let prev;
    for (const s of T.scenes) if (s.chapter !== prev) { prev = s.chapter; chapters.push({ start: s.start, name: s.chapter || (chapters.length ? '' : 'Opening') }); }
    chapters = chapters.filter(c => c.name);
    if (chapters.length < 2) { chapters = []; bChap.style.display = 'none'; chapName.style.display = 'none'; }
    for (const c of chapters.slice(1)) { const t = $('div', 'tick', track); t.style.left = (100 * c.start / total) + '%'; }
    for (const c of chapters) {
      const b = $('button', null, menu); b.type = 'button'; b.setAttribute('role', 'menuitem');
      $('span', 'nm', b).textContent = c.name; $('span', 'at', b).textContent = fmt(c.start);
      b.addEventListener('click', () => { seekTo(c.start); closeMenu(); if (started && audio.paused) play(); });
      c.el = b;
    }
    if (!caps.length) bCC.style.display = 'none';
    if (!(document.fullscreenEnabled || document.webkitFullscreenEnabled)) bFull.style.display = 'none';
    scrub.setAttribute('aria-valuemin', 0); scrub.setAttribute('aria-valuemax', Math.round(total));
    setCaps(capsOn);
    const ut = urlTime();
    pos = clampT(ut ?? 0);
    // the still before the first play: the poster frame, unless the address asks for a time
    let still = pos;
    if (ut === null && P.poster && P.poster[0]) {
      const s = T.scenes.find(x => x.id === P.poster[0]);
      if (s) still = s.start + (P.poster[1] && s.cues && s.cues[P.poster[1]] !== undefined ? s.cues[P.poster[1]] : 0) + (P.poster[2] || 0);
    }
    ready = true;
    render(still, true);
    frame.classList.add('ui', 'ready');
    window.player = { audio, get pos() { return pos; }, seekTo, play, pause, total, chapters, render };
  }

  // ---- drawing ------------------------------------------------------------------------------------------------
  let lastSec = -1, lastChap;
  function render(t, frameAt) {   // frameAt: show the film at t (otherwise the bar only)
    if (!ready) return;
    if (t !== shown) { window.seek(t); shown = t; }
    const c = capsOn && started ? capAt(t) : null;   // the still has no caption
    if (c) { if (capSpan.textContent !== c) capSpan.textContent = c; capRow.style.display = ''; } else capRow.style.display = 'none';
    bar_(pos);
  }
  function bar_(t) {
    const f = total ? t / total : 0;
    played.style.width = (100 * f) + '%'; knob.style.left = (100 * f) + '%';
    const sec = Math.floor(t);
    if (sec !== lastSec) {
      lastSec = sec; time.innerHTML = `${fmt(t)}<span class="tot"> / ${fmt(total)}</span>`;
      scrub.setAttribute('aria-valuenow', sec); scrub.setAttribute('aria-valuetext', `${fmt(t)} of ${fmt(total)}`);
    }
    const ch = chapterAt(t);
    if (ch !== lastChap) { lastChap = ch; chapName.textContent = ch ? ch.name : ''; for (const c of chapters) c.el.classList.toggle('cur', c === ch); }
  }
  function step() {
    if (playing() && !dragging) { pos = clampT(audio.currentTime); render(pos); }
    if (playing()) requestAnimationFrame(step);
  }

  // ---- play, pause, seek ----------------------------------------------------------------------------------------
  function play() {
    if (!ready) return;
    if (!started) { started = true; frame.classList.add('started'); }
    // tell the page that embeds the player, once, that the video was started (the page may count it; the player itself sends nothing anywhere)
    if (!told) { told = true; try { if (window.parent !== window) window.parent.postMessage({ type: 'video-play', title: document.title }, location.origin); } catch (e) {} }
    if (pos >= total - 0.05) seekTo(0);
    if (audio.error) { say(''); audio.load(); }   // a second try after a failed load
    if (audio.readyState === 0) { pendingSeek = true; frame.classList.add('waiting'); }
    audio.playbackRate = speeds[speedI];
    const p = audio.play();
    if (p && p.catch) p.catch(e => {
      frame.classList.remove('waiting');
      if (e.name === 'NotAllowedError' || e.name === 'AbortError') return;
      say(e.name === 'NotSupportedError' ? NO_SOUND : 'The sound could not be played: ' + e.message);
    });
    render(pos);
  }
  function pause() { audio.pause(); }
  function toggle() { if (playing() || (started && !audio.paused)) pause(); else play(); }
  function seekTo(t) {
    pos = clampT(t);
    if (audio.readyState > 0) { try { audio.currentTime = pos; } catch (e) { pendingSeek = true; } } else pendingSeek = true;
    if (!started) { started = true; frame.classList.add('started'); }   // a chosen time replaces the still
    render(pos);
  }
  audio.addEventListener('loadedmetadata', () => { if (pendingSeek || Math.abs(audio.currentTime - pos) > 0.25) { audio.currentTime = Math.min(pos, audio.duration || pos); pendingSeek = false; } });
  audio.addEventListener('play', () => { frame.classList.add('playing'); bPlay.innerHTML = ICON.pause; bPlay.setAttribute('aria-label', 'Pause (k)'); bPlay.title = 'Pause (k)'; nudge(); requestAnimationFrame(step); });
  audio.addEventListener('pause', () => { frame.classList.remove('playing'); bPlay.innerHTML = ICON.play; bPlay.setAttribute('aria-label', 'Play (k)'); bPlay.title = 'Play (k)'; frame.classList.add('ui'); });
  audio.addEventListener('waiting', () => frame.classList.add('waiting'));
  audio.addEventListener('playing', () => { frame.classList.remove('waiting'); say(''); });
  audio.addEventListener('canplay', () => frame.classList.remove('waiting'));
  audio.addEventListener('seeked', () => { if (!playing() && !dragging) render(pos); });
  audio.addEventListener('ended', () => { pos = Math.min(total, audio.currentTime); render(pos); frame.classList.add('ui'); });
  audio.addEventListener('error', () => {
    frame.classList.remove('waiting');
    const e = audio.error, why = e ? ({ 1: 'stopped', 2: 'a network error', 3: 'it could not be decoded', 4: 'the file is missing or not supported' })[e.code] || 'an error' : 'an error';
    say(NO_SOUND + ` (${why})`);
  });

  // ---- the controls ---------------------------------------------------------------------------------------------
  let hideTimer = 0, overBar = false;
  function nudge() {   // show the controls; hide them again after a while of no movement, while playing
    frame.classList.add('ui'); clearTimeout(hideTimer);
    hideTimer = setTimeout(() => { if (playing() && !overBar && !menu.classList.contains('on') && !dragging) frame.classList.remove('ui'); }, 2600);
  }
  bar.addEventListener('pointerenter', () => { overBar = true; }); bar.addEventListener('pointerleave', () => { overBar = false; nudge(); });
  frame.addEventListener('pointermove', e => { if (e.pointerType === 'mouse') nudge(); });
  let lastPointer = 'mouse', wasUI = true;
  box.addEventListener('pointerdown', e => { lastPointer = e.pointerType; wasUI = frame.classList.contains('ui'); });
  // a click on the picture plays or pauses; on a touch screen, the first tap only brings the controls back
  box.addEventListener('click', e => {
    if (bar.contains(e.target) || menu.contains(e.target) || e.target.closest('.big')) return;
    if (menu.classList.contains('on')) { closeMenu(); return; }
    if (lastPointer === 'touch' && !wasUI) { nudge(); return; }
    toggle(); nudge();
  });
  big.addEventListener('click', () => { play(); nudge(); });
  bPlay.addEventListener('click', () => { toggle(); nudge(); });
  bSpeed.addEventListener('click', () => { speedI = (speedI + 1) % speeds.length; audio.playbackRate = speeds[speedI]; bSpeed.textContent = speeds[speedI] + '×'; nudge(); });
  function setCaps(on) { capsOn = on; bCC.setAttribute('aria-pressed', String(on)); render(pos); }
  bCC.addEventListener('click', () => { setCaps(!capsOn); nudge(); });
  function openMenu() { menu.classList.add('on'); bChap.setAttribute('aria-expanded', 'true'); const c = menu.querySelector('.cur'); if (c) c.scrollIntoView({ block: 'nearest' }); frame.classList.add('ui'); }
  function closeMenu() { menu.classList.remove('on'); bChap.setAttribute('aria-expanded', 'false'); nudge(); }
  bChap.addEventListener('click', () => menu.classList.contains('on') ? closeMenu() : openMenu());

  function toggleFull() {
    if (isFull()) (document.exitFullscreen || document.webkitExitFullscreen).call(document);
    else { const r = player.requestFullscreen || player.webkitRequestFullscreen; if (r) { const p = r.call(player); if (p && p.catch) p.catch(() => {}); } }
  }
  bFull.addEventListener('click', toggleFull);
  const onFull = () => { fit(); const f = isFull(); bFull.innerHTML = f ? ICON.unfull : ICON.full; bFull.setAttribute('aria-label', f ? 'Leave full screen (f)' : 'Full screen (f)'); bFull.title = bFull.getAttribute('aria-label'); };
  document.addEventListener('fullscreenchange', onFull); document.addEventListener('webkitfullscreenchange', onFull);

  // the scrub line: drag to move, hover for the time and chapter there
  const frac = e => { const r = scrub.getBoundingClientRect(); return Math.max(0, Math.min(1, (e.clientX - r.left) / r.width)); };
  function showTip(e) {
    const f = frac(e), t = f * total, c = chapterAt(t);
    tip.textContent = fmt(t) + (c ? '  ·  ' + c.name : ''); tip.classList.add('on');
    const w = tip.offsetWidth, sw = scrub.clientWidth, x = Math.max(-8, Math.min(sw - w + 8, f * sw - w / 2)); tip.style.left = x + 'px';
  }
  scrub.addEventListener('pointerdown', e => {
    if (!ready) return;
    dragging = true; scrub.classList.add('drag'); scrub.setPointerCapture(e.pointerId);
    pos = frac(e) * total; if (!started) { started = true; frame.classList.add('started'); } render(pos); showTip(e); e.preventDefault();
  });
  scrub.addEventListener('pointermove', e => { if (!ready) return; showTip(e); if (dragging) { pos = frac(e) * total; render(pos); } });
  const endDrag = e => { if (!dragging) return; dragging = false; scrub.classList.remove('drag'); seekTo(pos); if (e.pointerType !== 'mouse') tip.classList.remove('on'); nudge(); if (playing()) requestAnimationFrame(step); };
  scrub.addEventListener('pointerup', endDrag); scrub.addEventListener('pointercancel', endDrag);
  scrub.addEventListener('pointerleave', () => { if (!dragging) tip.classList.remove('on'); });

  // keys: space or k plays and pauses, the arrows move 5 s, f is full screen, c captions, Escape closes the menu
  document.addEventListener('keydown', e => {
    if (e.metaKey || e.ctrlKey || e.altKey || !ready) return;
    // space on a focused button presses that button (the play button included), as buttons do
    if (e.key === ' ' && e.target.closest && e.target.closest('button')) return;
    if (e.key === ' ' || e.key === 'k' || e.key === 'K') { e.preventDefault(); toggle(); }
    else if (e.key === 'ArrowLeft' || e.key === 'ArrowRight') { e.preventDefault(); seekTo(pos + (e.key === 'ArrowLeft' ? -5 : 5)); }
    else if (e.key === 'f' || e.key === 'F') toggleFull();
    else if (e.key === 'c' || e.key === 'C') { if (caps.length) setCaps(!capsOn); }
    else if (e.key === 'Escape' && menu.classList.contains('on')) closeMenu();
    else return;
    nudge();
  });
})();
