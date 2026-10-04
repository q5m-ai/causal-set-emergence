// Display-only controls: no change to the mathematical model or WebGL dependency.
// Native fullscreen when allowed; an accessible full-window dialog otherwise.
export function initDisplay(lab) {
  const fullscreen = document.getElementById("fullscreen-view");
  const message = document.getElementById("fullscreen-status");
  const toggle = document.getElementById("controls-toggle");
  const panel = document.getElementById("scene-controls");
  const close = document.getElementById("close-controls");
  let expanded = false, native = false, pending = false, returnFocus, scroll;
  const background = new Map();

  function showControls(show, moveFocus = true) {
    panel.hidden = !show;
    toggle.setAttribute("aria-expanded", String(show));
    if (moveFocus) (show ? close : toggle).focus();
  }
  toggle.hidden = false;
  toggle.addEventListener("click", () => showControls(panel.hidden));
  close.addEventListener("click", () => showControls(false));

  function activate() {
    returnFocus = document.activeElement;
    scroll = { left: window.scrollX, top: window.scrollY, behavior: "instant" };
    // Inert every sibling along the ancestor chain, not the dialog's ancestors.
    // Preserve pre-existing inert state rather than enabling unrelated content.
    for (let node = lab; node !== document.body; node = node.parentElement) {
      for (const sibling of node.parentElement.children) if (sibling !== node) {
        background.set(sibling, sibling.inert);
        sibling.inert = true;
      }
    }
    expanded = true;
    lab.classList.add("is-expanded");
    lab.setAttribute("role", "dialog");
    lab.setAttribute("aria-modal", "true");
    lab.dataset.displayMode = "window";
    document.documentElement.classList.add("spine-immersive");
    fullscreen.setAttribute("aria-expanded", "true");
    fullscreen.querySelector("span").textContent = "Exit full screen";
    fullscreen.title = "Exit full screen (Escape)";
    fullscreen.focus({ preventScroll: true });
    message.textContent = "Expanded window view. Use Exit full screen or Escape to return.";
  }
  function restore() {
    if (!expanded) return;
    expanded = false; native = false;
    lab.classList.remove("is-expanded");
    lab.removeAttribute("role"); lab.removeAttribute("aria-modal");
    delete lab.dataset.displayMode;
    document.documentElement.classList.remove("spine-immersive");
    for (const [element, inert] of background) element.inert = inert;
    background.clear();
    fullscreen.setAttribute("aria-expanded", "false");
    fullscreen.querySelector("span").textContent = "Full screen";
    fullscreen.removeAttribute("title");
    message.textContent = "Returned to the proof page. Your scene settings are unchanged.";
    if (returnFocus?.isConnected) returnFocus.focus({ preventScroll: true });
    window.scrollTo(scroll);
  }
  async function enter() {
    if (pending) return;
    activate();
    if (!lab.requestFullscreen || !document.fullscreenEnabled) return;
    pending = true;
    try {
      await lab.requestFullscreen();
    } catch {
      // Permissions, browser support and secure-context restrictions can all
      // deny fullscreen. The already active full-window view remains usable.
      if (expanded) message.textContent = "Browser fullscreen unavailable. Expanded window view is active; use Exit full screen or Escape to return.";
    } finally { pending = false; }
  }
  async function exit() {
    if (document.fullscreenElement === lab) {
      try { await document.exitFullscreen(); }
      catch { message.textContent = "Use Escape or the browser fullscreen control to leave fullscreen."; }
    } else { restore(); }
  }
  fullscreen.hidden = false;
  fullscreen.addEventListener("click", () => { if (!pending) { if (expanded) void exit(); else void enter(); } });
  document.addEventListener("fullscreenchange", () => {
    if (document.fullscreenElement === lab) {
      // A browser may finish entering after Escape was pressed during startup.
      if (!expanded) { void exit(); return; }
      native = true;
      lab.dataset.displayMode = "native";
      message.textContent = "Fullscreen view. Use Exit full screen or Escape to return.";
    } else if (native) { restore(); }
  });
  document.addEventListener("keydown", event => {
    if (!expanded) {
      if (event.key === "Escape" && !panel.hidden) showControls(false);
      return;
    }
    if (event.key === "Escape") {
      event.preventDefault(); void exit();
    } else if (event.key === "Tab") {
      const focusable = [...lab.querySelectorAll('button:not(:disabled), input:not(:disabled), select:not(:disabled), a[href], [tabindex="0"]')]
        .filter(element => element.getClientRects().length && !element.closest("[hidden]"));
      const first = focusable[0], last = focusable.at(-1);
      if (event.shiftKey && (document.activeElement === first || !lab.contains(document.activeElement))) {
        event.preventDefault(); last?.focus();
      } else if (!event.shiftKey && (document.activeElement === last || !lab.contains(document.activeElement))) {
        event.preventDefault(); first?.focus();
      }
    }
  });
}
