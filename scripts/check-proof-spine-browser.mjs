// Run against an already hosted site. Playwright is validation-only tooling.
// Screenshots/receipts go outside served content; see notes/proof-spine-page.md.
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import path from "node:path";
const { chromium } = await import(process.env.PLAYWRIGHT_MODULE || "playwright");
const [base, out = "/tmp/proof-spine-browser"] = process.argv.slice(2);
if (!base) throw new Error("Usage: node scripts/check-proof-spine-browser.mjs SITE_URL OUT_DIR");
await fs.mkdir(out, { recursive: true });
const browser = await chromium.launch({ headless: true, args: ["--use-gl=angle", "--use-angle=swiftshader", "--enable-unsafe-swiftshader"] });
const results = [];
const activate = (page, selector, touch) => touch ? page.locator(selector).tap() : page.locator(selector).click();
async function controls(page, show = true) {
  if (await page.locator("#scene-controls").isVisible() !== show) await page.locator("#controls-toggle").click();
  assert.equal(await page.locator("#scene-controls").isVisible(), show);
}
async function accessibility(page) {
  if (!process.env.AXE_SCRIPT) return "not run (set AXE_SCRIPT)";
  if (!await page.evaluate(() => Boolean(window.axe))) await page.addScriptTag({ path: process.env.AXE_SCRIPT });
  const audit = await page.evaluate(async () => axe.run(document, { runOnly: { type: "tag", values: ["wcag2a", "wcag2aa", "wcag21aa"] } }));
  const violations = audit.violations.map(v => ({ id: v.id, impact: v.impact, targets: v.nodes.map(n => n.target) }));
  assert.deepEqual(violations, []);
  return "axe WCAG 2 A/AA + 2.1 AA: zero violations";
}
async function checkExpanded(page, expectedMode) {
  await page.waitForFunction(mode => document.getElementById("example-lab").dataset.displayMode === mode, expectedMode);
  await page.waitForTimeout(150); // ResizeObserver + on-demand WebGL frame.
  assert.equal(await page.locator("#example-lab").getAttribute("role"), "dialog");
  assert.equal(await page.locator("#example-lab").getAttribute("aria-modal"), "true");
  assert.equal(await page.locator("#fullscreen-view").getAttribute("aria-expanded"), "true");
  const size = await page.evaluate(() => {
    const lab = document.getElementById("example-lab"), rect = lab.getBoundingClientRect();
    const stage = document.getElementById("spineStage");
    return { width: rect.width, height: rect.height, top: rect.top, left: rect.left,
      viewport: [innerWidth, innerHeight], stage: stage.clientHeight,
      inert: document.querySelector("main").inert, overflow: document.documentElement.scrollWidth - innerWidth };
  });
  assert.ok(Math.abs(size.width - size.viewport[0]) <= 1 && Math.abs(size.height - size.viewport[1]) <= 1, JSON.stringify(size));
  assert.equal(size.top, 0); assert.equal(size.left, 0);
  assert.ok(size.stage >= 180); assert.ok(size.inert); assert.ok(size.overflow <= 1);
  // Reverse and forward tab wrap stay in the dialog, not the underlying guide.
  await page.locator("#fullscreen-view").focus(); await page.keyboard.press("Shift+Tab");
  assert.equal(await page.evaluate(() => document.activeElement.id), "controls-toggle");
  await page.keyboard.press("Tab");
  assert.equal(await page.evaluate(() => document.activeElement.id), "fullscreen-view");
  return size;
}
async function checkRestored(page, previousScroll) {
  await page.waitForFunction(() => !document.getElementById("example-lab").classList.contains("is-expanded"));
  assert.equal(await page.locator("#fullscreen-view").getAttribute("aria-expanded"), "false");
  assert.equal(await page.locator("#example-lab").getAttribute("aria-modal"), null);
  assert.equal(await page.evaluate(() => document.activeElement.id), "fullscreen-view");
  assert.equal(await page.evaluate(() => document.querySelector("main").inert), false);
  assert.ok(Math.abs(await page.evaluate(() => scrollY) - previousScroll) <= 2);
}
async function checkDeepZoom(page, context, config) {
  // Observe the actual rendered camera without exposing a production debug API.
  await page.evaluate(async () => {
    const { Scene } = await import("three"), beforeRender = Scene.prototype.onBeforeRender;
    Scene.prototype.onBeforeRender = function(renderer, scene, camera, ...rest) {
      if (renderer.domElement.parentElement?.id === "spineStage") window.spineTestCamera = { distance: camera.position.length(), near: camera.near };
      return beforeRender.call(this, renderer, scene, camera, ...rest);
    };
  });
  const waitForDistance = distance => page.waitForFunction(expected => Math.abs(window.spineTestCamera.distance / expected - 1) < 1e-6, distance);
  await page.locator("#orbit-view").click();
  await page.waitForFunction(() => window.spineTestCamera);
  const fitted = await page.evaluate(() => spineTestCamera.distance);
  for (let i = 0; i < 16; i++) await activate(page, "#zoom-in", config.hasTouch);
  await waitForDistance(fitted * 0.05); // Old 0.55 clamp stopped after three clicks.
  assert.ok(await page.evaluate(() => spineTestCamera.distance > 2 * spineTestCamera.near));
  await page.locator("#spineStage").screenshot({ path: path.join(out, `${config.name}-deep-zoom.png`) });
  await activate(page, "#zoom-out", config.hasTouch);
  await waitForDistance(fitted * 0.0625);
  const stage = await page.locator("#spineStage").boundingBox(), x = stage.x + stage.width / 2, y = stage.y + stage.height / 2;
  if (config.hasTouch) {
    const session = await context.newCDPSession(page);
    const touches = radius => [{ x: x - radius, y, id: 1 }, { x: x + radius, y, id: 2 }];
    await session.send("Input.dispatchTouchEvent", { type: "touchStart", touchPoints: touches(25) });
    for (const radius of [35, 45, 55, 65]) await session.send("Input.dispatchTouchEvent", { type: "touchMove", touchPoints: touches(radius) });
    await session.send("Input.dispatchTouchEvent", { type: "touchEnd", touchPoints: [] });
    await session.detach();
  } else {
    await page.mouse.move(x, y); await page.mouse.wheel(0, -300);
  }
  await page.waitForFunction(distance => spineTestCamera.distance < distance, fitted * 0.0625 - 1e-6);
  // Reach the shared close limit again, then preserve it through every resize.
  await activate(page, "#zoom-in", config.hasTouch);
  await waitForDistance(fitted * 0.05);
  await page.evaluate(() => scrollTo({ top: 0, behavior: "instant" }));
  await activate(page, "#fullscreen-view", config.hasTouch);
  await checkExpanded(page, await page.evaluate(() => document.fullscreenEnabled ? "native" : "window"));
  await controls(page); await controls(page, false);
  await activate(page, "#fullscreen-view", config.hasTouch);
  await checkRestored(page, 0);
  await waitForDistance(fitted * 0.05);
  await page.locator("#orbit-view").click();
  await waitForDistance(fitted);
  return { minimumDistanceRatio: 0.05, gesture: config.hasTouch ? "emulated two-finger pinch" : "mouse wheel", resizeAndReset: true };
}
try {
  for (const config of [
    { name: "desktop", viewport: { width: 1440, height: 1000 } },
    { name: "mobile", viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true },
    { name: "narrow-mobile", viewport: { width: 320, height: 740 }, isMobile: true, hasTouch: true },
    { name: "reduced-dark", viewport: { width: 360, height: 800 }, reducedMotion: "reduce", colorScheme: "dark", isMobile: true, hasTouch: true }
  ]) {
    const context = await browser.newContext(config), page = await context.newPage(), errors = [], failed = [];
    page.on("pageerror", e => errors.push(e.message));
    page.on("requestfailed", r => failed.push(`${r.url()} ${r.failure()?.errorText}`));
    const response = await page.goto(new URL("proof-spine.html", base).href);
    const source = await response.text();
    const mainSource = source.split("<main")[1].split("</main>")[0];
    const expectedMath = (mainSource.match(/\\\(/g) || []).length + (mainSource.match(/\\\[/g) || []).length;
    await page.waitForFunction(() => window.MathJax?.startup?.document && document.querySelector("#spineStage canvas"));
    await page.evaluate(() => MathJax.startup.promise);
    await page.waitForTimeout(200);
    const hero = await page.locator("#spineStage").boundingBox();
    assert.ok(hero.y < config.viewport.height / 2, "The scene must lead the first screen");
    assert.ok(hero.width > config.viewport.width * 0.9 && hero.height > config.viewport.height * 0.35, JSON.stringify(hero));
    assert.equal(await page.locator("#scene-controls").isVisible(), false);
    await page.screenshot({ path: path.join(out, `${config.name}-hero.png`) });
    for (const button of await page.locator(".camera-controls button").all()) {
      const bounds = await button.boundingBox();
      assert.ok(bounds.x >= hero.x && bounds.x + bounds.width <= hero.x + hero.width, "Camera buttons must not be clipped");
    }
    const stillFrame = await page.locator("#spineStage").screenshot();
    await page.waitForTimeout(250);
    assert.ok(stillFrame.equals(await page.locator("#spineStage").screenshot()), "The scene must not auto-animate");
    if (!config.hasTouch) {
      await page.mouse.move(hero.x + hero.width / 2, hero.y + hero.height / 2);
      await page.mouse.down();
      await page.mouse.move(hero.x + hero.width / 2 + 75, hero.y + hero.height / 2 + 25, { steps: 8 });
      await page.mouse.up();
      assert.ok(!stillFrame.equals(await page.locator("#spineStage").screenshot()), "Dragging must rotate the scene");
      await page.locator("#orbit-view").click();
    }
    await page.evaluate(async () => {
      document.querySelectorAll("details").forEach(d => { d.open = true; });
      await MathJax.typesetPromise();
    });
    const math = await page.evaluate(() => ({
      count: MathJax.startup.document.math.toArray ? MathJax.startup.document.math.toArray().length : Array.from(MathJax.startup.document.math).length,
      containers: document.querySelectorAll("mjx-container").length,
      errors: document.querySelectorAll("mjx-merror, [data-mjx-error]").length,
      rawDelimiters: /\\\[|\\\]|\\\(|\\\)/.test(document.querySelector("main").innerText)
    }));
    assert.equal(math.count, expectedMath, JSON.stringify(math));
    assert.equal(math.containers, expectedMath);
    assert.equal(math.errors, 0); assert.equal(math.rawDelimiters, false);
    await page.screenshot({ path: path.join(out, `${config.name}-expanded.png`), fullPage: true });
    await page.evaluate(() => document.querySelectorAll("details").forEach(d => { d.open = false; }));
    for (const guide of ["interval", "points", "split", "faces"]) {
      await activate(page, `[data-guide="${guide}"]`, config.hasTouch);
      assert.equal(await page.locator(`[data-guide="${guide}"]`).getAttribute("aria-pressed"), "true");
      await page.waitForTimeout(100);
    }
    await page.locator('[data-guide="split"]').click();
    assert.match(await page.locator("#layer-key").textContent(), /Blue solid: short.*Coral dashed: long/);
    assert.doesNotMatch(await page.locator("#layer-key").textContent(), /future boundary/);
    await controls(page);
    await page.locator("#spine-cutoff").evaluate(el => { el.value = "0.595"; el.dispatchEvent(new Event("input", { bubbles: true })); });
    assert.match(await page.locator("#pair-readout").textContent(), /this pair is long/);
    await page.locator("#spine-cutoff").evaluate(el => { el.value = "0.600"; el.dispatchEvent(new Event("input", { bubbles: true })); });
    assert.match(await page.locator("#pair-readout").textContent(), /this pair is short/);
    await controls(page, false); // The small-screen drawer overlays camera controls.
    await page.locator("#front-view").click();
    await page.locator("#example-lab").screenshot({ path: path.join(out, `${config.name}-split.png`) });
    await controls(page);
    await page.locator("#reset-view").click();
    assert.equal(await page.locator("#spine-cutoff").inputValue(), "0.4");
    assert.equal(await page.locator("#pair-choice").inputValue(), "axial");
    const beforeSample = await page.locator("#pair-readout").textContent();
    await page.locator("#resprinkle").click();
    assert.notEqual(await page.locator("#pair-readout").textContent(), beforeSample);
    await page.locator("#reset-view").click();
    assert.equal(await page.locator("#pair-readout").textContent(), beforeSample);
    await page.locator("#show-cones").focus(); await page.keyboard.press("Space");
    assert.ok(await page.locator("#show-cones").isChecked());
    const start = performance.now();
    for (let i = 0; i < 20; i++) await page.locator("#spine-cutoff").evaluate((el, i) => { el.value = String(0.2 + i * 0.02); el.dispatchEvent(new Event("input")); }, i);
    const interactionMs = (performance.now() - start) / 20;
    await controls(page, false);
    await page.locator('[data-guide="split"]').click();
    const splitStart = performance.now();
    for (let i = 0; i < 20; i++) await page.locator("#spine-cutoff").evaluate((el, i) => { el.value = String(0.2 + i * 0.02); el.dispatchEvent(new Event("input")); }, i);
    const splitInteractionMs = (performance.now() - splitStart) / 20;
    await page.locator("#zoom-in").click(); await page.locator("#zoom-out").click(); await page.locator("#orbit-view").click();
    const pageAccessibility = await accessibility(page);
    const beforeFullscreen = await page.locator("#pair-readout").textContent();
    await page.evaluate(() => scrollTo({ top: 0, behavior: "instant" }));
    const previousScroll = await page.evaluate(() => scrollY);
    const mode = await page.evaluate(() => document.fullscreenEnabled ? "native" : "window");
    await activate(page, "#fullscreen-view", config.hasTouch);
    const expanded = await checkExpanded(page, mode);
    assert.equal(await page.locator("#pair-readout").textContent(), beforeFullscreen);
    await page.screenshot({ path: path.join(out, `${config.name}-fullscreen.png`) });
    await controls(page);
    assert.equal(await page.evaluate(() => document.activeElement.id), "close-controls");
    const fullscreenAccessibility = await accessibility(page);
    await page.screenshot({ path: path.join(out, `${config.name}-fullscreen-controls.png`) });
    await page.locator("#close-controls").click();
    assert.equal(await page.evaluate(() => document.activeElement.id), "controls-toggle");
    // Also exercise the browser's own exit path, not just our button handler.
    if (mode === "native") await page.evaluate(() => document.exitFullscreen()); else await page.keyboard.press("Escape");
    await checkRestored(page, previousScroll);
    assert.equal(await page.locator("#pair-readout").textContent(), beforeFullscreen);
    await activate(page, "#fullscreen-view", config.hasTouch);
    await checkExpanded(page, mode);
    await activate(page, "#fullscreen-view", config.hasTouch);
    await checkRestored(page, previousScroll);
    // Canvas pixels retain the stage's aspect ratio, including after fullscreen.
    const distortion = await page.locator("#spineStage canvas").evaluate(c => Math.abs(c.width / c.clientWidth - c.height / c.clientHeight));
    assert.ok(distortion < 0.01, `Canvas aspect distortion: ${distortion}`);
    const deepZoom = await checkDeepZoom(page, context, config);
    if (config.reducedMotion) assert.equal(await page.evaluate(() => getComputedStyle(document.documentElement).scrollBehavior), "auto");
    const overflow = await page.evaluate(() => document.documentElement.scrollWidth - innerWidth);
    assert.ok(overflow <= 1, `Page overflow: ${overflow}`);
    assert.deepEqual(errors, []); assert.deepEqual(failed, []);
    // Links from the proof still select the existing hero; no duplicate canvas.
    await page.locator('[data-visit="interval"]').click();
    assert.equal(await page.locator('[data-guide="interval"]').getAttribute("aria-pressed"), "true");
    assert.equal(await page.locator("#spineStage canvas").count(), 1);
    await page.goto(new URL("index.html", base).href);
    await page.getByRole("link", { name: "Proof spine", exact: true }).click();
    assert.ok(page.url().endsWith("proof-spine.html"));
    results.push({ name: config.name, hero, math, expanded: { mode, ...expanded }, deepZoom, distortion, overflow, interactionMs, splitInteractionMs, pageAccessibility, fullscreenAccessibility, errors, failed });
    await context.close();
  }
  for (const mode of ["fullscreen-unsupported", "fullscreen-denied", "webgl-failure", "context-loss", "cdn-failure", "no-js"]) {
    const context = await browser.newContext({ viewport: { width: 390, height: 844 }, javaScriptEnabled: mode !== "no-js" });
    if (mode === "fullscreen-unsupported") await context.addInitScript(() => Object.defineProperty(document, "fullscreenEnabled", { value: false }));
    if (mode === "fullscreen-denied") await context.addInitScript(() => {
      HTMLElement.prototype.requestFullscreen = () => Promise.reject(new Error("Fullscreen intentionally denied"));
    });
    if (mode === "webgl-failure") await context.addInitScript(() => {
      const get = HTMLCanvasElement.prototype.getContext;
      HTMLCanvasElement.prototype.getContext = function(type, ...args) { return type.includes("webgl") ? null : get.call(this, type, ...args); };
    });
    if (mode === "cdn-failure") await context.route("**/cdn.jsdelivr.net/**", route => route.abort());
    const page = await context.newPage(), errors = [];
    page.on("pageerror", e => errors.push(e.message));
    await page.goto(new URL("proof-spine.html", base).href);
    if (mode === "no-js") {
      assert.ok(await page.locator(".scene-fallback").isVisible());
      assert.equal(await page.locator("#fullscreen-view").isVisible(), false);
    } else {
      if (["webgl-failure", "cdn-failure"].includes(mode)) {
        await page.waitForFunction(() => document.getElementById("viewer-status").textContent.includes("unavailable"));
        assert.ok(await page.locator(".scene-fallback").isVisible());
        assert.ok(await page.locator("#front-view").isDisabled());
      }
      await controls(page);
      await page.locator("#pair-choice").selectOption("null");
      assert.match(await page.locator("#pair-readout").textContent(), /σ = 0.002975/);
      await controls(page, false);
      await page.evaluate(() => scrollTo({ top: 0, behavior: "instant" }));
      await page.locator("footer").evaluate(el => { el.inert = true; });
      await page.locator("#fullscreen-view").click();
      if (mode === "fullscreen-denied") await page.waitForFunction(() => document.getElementById("fullscreen-status").textContent.includes("unavailable"));
      await checkExpanded(page, mode.startsWith("fullscreen-") ? "window" : "native");
      if (mode === "context-loss") {
        await page.waitForSelector("#spineStage canvas");
        await page.locator("#spineStage canvas").evaluate(canvas => {
          const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
          gl.getExtension("WEBGL_lose_context").loseContext();
        });
        await page.waitForFunction(() => document.getElementById("viewer-status").textContent.includes("context lost"));
        assert.ok(await page.locator(".scene-fallback").isVisible());
        assert.ok(await page.locator("#front-view").isDisabled());
      }
      await page.screenshot({ path: path.join(out, `${mode}-expanded.png`) });
      // Chromium cannot resize its native fullscreen window through CDP.
      // Test live rotation in the full-window fallback; for native fullscreen,
      // leave, resize, then enter again in the new landscape viewport.
      const native = await page.evaluate(() => Boolean(document.fullscreenElement));
      if (native) { await page.keyboard.press("Escape"); await checkRestored(page, 0); }
      await page.setViewportSize({ width: 844, height: 390 });
      if (native) { await page.locator("#fullscreen-view").click(); await checkExpanded(page, "native"); }
      await page.waitForTimeout(150);
      await page.screenshot({ path: path.join(out, `${mode}-landscape.png`) });
      assert.ok(await page.locator("#fullscreen-view").isVisible());
      await controls(page);
      await page.locator("#spine-cutoff").focus(); await page.keyboard.press("ArrowRight");
      await controls(page, false);
      await page.keyboard.press("Escape");
      await checkRestored(page, 0);
      assert.ok(await page.locator("footer").evaluate(el => el.inert), "Preserve previously inert background content");
    }
    assert.deepEqual(errors, []);
    await page.screenshot({ path: path.join(out, `${mode}.png`) });
    results.push({ name: mode, readout: mode !== "no-js", errors });
    await context.close();
  }
  await fs.writeFile(path.join(out, "results.json"), JSON.stringify(results, null, 2));
  console.log(JSON.stringify(results, null, 2));
} finally { await browser.close(); }
