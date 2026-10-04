// Run against an already hosted site. Playwright is a validation-only tool,
// not a website dependency. Screenshots/receipts go outside served content.
// PLAYWRIGHT_MODULE=/absolute/path/to/playwright/index.mjs node scripts/check-proof-spine-browser.mjs URL OUT_DIR
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import path from "node:path";
const { chromium } = await import(process.env.PLAYWRIGHT_MODULE || "playwright");
const [base, out = "/tmp/proof-spine-browser"] = process.argv.slice(2);
if (!base) throw new Error("Usage: node scripts/check-proof-spine-browser.mjs SITE_URL OUT_DIR");
await fs.mkdir(out, { recursive: true });
const browser = await chromium.launch({ headless: true, args: ["--use-gl=angle", "--use-angle=swiftshader", "--enable-unsafe-swiftshader"] });
const results = [];
try {
  for (const config of [
    { name: "desktop", viewport: { width: 1440, height: 1000 } },
    { name: "mobile", viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true },
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
    await page.evaluate(async () => {
      document.querySelectorAll("details").forEach(d => { d.open = true; });
      await MathJax.startup.promise;
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
    assert.ok(await page.locator("#spineStage canvas").isVisible());
    await page.screenshot({ path: path.join(out, `${config.name}-expanded.png`), fullPage: true });
    await page.evaluate(() => document.querySelectorAll("details").forEach(d => { d.open = false; }));
    for (const guide of ["interval", "points", "split", "faces"]) {
      const button = page.locator(`[data-guide="${guide}"]`);
      if (config.hasTouch) await button.tap(); else await button.click();
      assert.equal(await page.locator(`[data-guide="${guide}"]`).getAttribute("aria-pressed"), "true");
      await page.waitForTimeout(100);
    }
    await page.locator('[data-guide="split"]').click();
    await page.locator("#spine-cutoff").evaluate(el => { el.value = "0.595"; el.dispatchEvent(new Event("input", { bubbles: true })); });
    assert.match(await page.locator("#pair-readout").textContent(), /this pair is long/);
    await page.locator("#spine-cutoff").evaluate(el => { el.value = "0.600"; el.dispatchEvent(new Event("input", { bubbles: true })); });
    assert.match(await page.locator("#pair-readout").textContent(), /this pair is short/);
    await page.locator("#front-view").click();
    await page.locator("#example-lab").screenshot({ path: path.join(out, `${config.name}-split.png`) });
    await page.locator("#reset-view").click();
    assert.equal(await page.locator("#spine-cutoff").inputValue(), "0.4");
    assert.equal(await page.locator("#pair-choice").inputValue(), "axial");
    const beforeSample = await page.locator("#pair-readout").textContent();
    await page.locator("#resprinkle").click();
    assert.notEqual(await page.locator("#pair-readout").textContent(), beforeSample);
    await page.locator("#reset-view").click();
    assert.equal(await page.locator("#pair-readout").textContent(), beforeSample);
    // Keyboard operation and accessible native names, not canvas-only interaction.
    await page.locator("#show-cones").focus(); await page.keyboard.press("Space");
    assert.ok(await page.locator("#show-cones").isChecked());
    const start = performance.now();
    for (let i = 0; i < 20; i++) await page.locator("#spine-cutoff").evaluate((el, i) => { el.value = String(0.2 + i * 0.02); el.dispatchEvent(new Event("input")); }, i);
    const interactionMs = (performance.now() - start) / 20;
    await page.locator("#zoom-in").click(); await page.locator("#zoom-out").click(); await page.locator("#orbit-view").click();
    let accessibility = "not run (set AXE_SCRIPT)";
    if (process.env.AXE_SCRIPT) {
      await page.addScriptTag({ path: process.env.AXE_SCRIPT });
      const audit = await page.evaluate(async () => axe.run(document, { runOnly: { type: "tag", values: ["wcag2a", "wcag2aa", "wcag21aa"] } }));
      const violations = audit.violations.map(v => ({ id: v.id, impact: v.impact, targets: v.nodes.map(n => n.target) }));
      assert.deepEqual(violations, []); accessibility = "axe WCAG 2 A/AA + 2.1 AA: zero violations";
    }
    const overflow = await page.evaluate(() => document.documentElement.scrollWidth - innerWidth);
    assert.ok(overflow <= 1, `Page overflow: ${overflow}`);
    assert.deepEqual(errors, []); assert.deepEqual(failed, []);
    await page.goto(new URL("index.html", base).href);
    await page.getByRole("link", { name: "Proof spine", exact: true }).click();
    assert.ok(page.url().endsWith("proof-spine.html"));
    results.push({ name: config.name, math, overflow, interactionMs, accessibility, errors, failed });
    await context.close();
  }
  // WebGL constructor failure: dynamic-import catch leaves useful fallback.
  for (const mode of ["webgl-failure", "cdn-failure", "no-js"]) {
    const context = await browser.newContext({ viewport: { width: 390, height: 844 }, javaScriptEnabled: mode !== "no-js" });
    if (mode === "webgl-failure") await context.addInitScript(() => {
      const get = HTMLCanvasElement.prototype.getContext;
      HTMLCanvasElement.prototype.getContext = function(type, ...args) { return type.includes("webgl") ? null : get.call(this, type, ...args); };
    });
    if (mode === "cdn-failure") await context.route("**/cdn.jsdelivr.net/**", route => route.abort());
    const page = await context.newPage(); await page.goto(new URL("proof-spine.html", base).href);
    if (mode !== "no-js") {
      await page.waitForFunction(() => document.getElementById("viewer-status").textContent.includes("unavailable"));
      await page.locator("#pair-choice").selectOption("null");
      assert.match(await page.locator("#pair-readout").textContent(), /σ = 0.002975/);
    }
    assert.ok(await page.locator(".scene-fallback").isVisible());
    await page.locator("#example-lab").screenshot({ path: path.join(out, `${mode}.png`) });
    results.push({ name: mode, staticFallback: true, readout: mode !== "no-js" });
    await context.close();
  }
  await fs.writeFile(path.join(out, "results.json"), JSON.stringify(results, null, 2));
  console.log(JSON.stringify(results, null, 2));
} finally { await browser.close(); }
