// Static review-page checks. External Playwright is test tooling, not a site dependency.
import fs from 'node:fs/promises';
const { chromium } = await import(process.env.PLAYWRIGHT_MODULE || 'playwright');
const [base, out = '/tmp/cse-research-browser'] = process.argv.slice(2);
if (!base) throw new Error('Usage: node scripts/check-research-browser.mjs LOCAL_URL [OUT_DIR]');
if (!['localhost', '127.0.0.1', '::1', '[::1]'].includes(new URL(base).hostname)) {
  throw new Error('Local preview only; this script does not deploy or inspect production');
}
await fs.mkdir(out, { recursive: true });
const browser = await chromium.launch({ headless: true });
const receipts = [], failures = [];
try {
  for (const [name, width, colorScheme] of [
    ['desktop', 1280, 'light'], ['mobile', 390, 'light'], ['dark-mobile', 390, 'dark'],
  ]) {
    const context = await browser.newContext({
      viewport: { width, height: 900 }, javaScriptEnabled: false,
      colorScheme, reducedMotion: 'reduce',
    });
    const page = await context.newPage();
    const responses = [], requests = [];
    page.on('response', r => { if (r.status() >= 400) responses.push([r.url(), r.status()]); });
    page.on('request', r => requests.push(r.url()));
    await page.goto(`${base}/research.html`, { waitUntil: 'networkidle' });
    const info = await page.evaluate(() => ({
      viewport: innerWidth, width: document.documentElement.scrollWidth,
      h1: document.querySelectorAll('h1').length,
      main: document.querySelectorAll('main').length,
      scripts: document.scripts.length,
      accountWords: document.querySelector('#account').innerText.split(/\s+/).length,
    }));
    await page.keyboard.press('Tab');
    const focus = await page.locator(':focus').getAttribute('href');
    await page.keyboard.press('Enter');
    const skipTarget = await page.locator(':focus').getAttribute('id');
    if (info.width > info.viewport || info.h1 !== 1 || info.main !== 1 || info.scripts ||
        focus !== '#main' || skipTarget !== 'main' || responses.length ||
        requests.some(url => new URL(url).origin !== new URL(base).origin)) {
      failures.push({ name, info, focus, skipTarget, responses, requests });
    }
    await page.locator('#account').screenshot({ path: `${out}/${name}-account.png` });
    await page.locator('#claims').screenshot({ path: `${out}/${name}-claims.png` });
    await page.locator('#mechanism').screenshot({ path: `${out}/${name}-mechanism.png` });
    receipts.push({ name, info, focus, skipTarget, requests });
    await context.close();
  }
  // Old teaching pages must still expose the new navigation without overflow.
  const navContext = await browser.newContext({ viewport: { width: 390, height: 844 }, javaScriptEnabled: false });
  for (const file of ['index.html', 'dimensions.html', 'proof-spine.html']) {
    const page = await navContext.newPage();
    await page.goto(`${base}/${file}`, { waitUntil: 'domcontentloaded' });
    const nav = page.locator('nav').first();
    const link = nav.locator('a[href="research.html"]');
    const box = await nav.boundingBox();
    if (!await link.isVisible() || box.x < 0 || box.x + box.width > 391) failures.push({ file, box });
    await nav.screenshot({ path: `${out}/${file}-nav.png` });
    await page.close();
  }
  await navContext.close();
  const printContext = await browser.newContext({ viewport: { width: 672, height: 1001 }, javaScriptEnabled: false });
  const printPage = await printContext.newPage();
  await printPage.goto(`${base}/research.html`);
  await printPage.emulateMedia({ media: 'print' });
  const account = await printPage.locator('#account').boundingBox();
  // A4 minus two 16mm margins is approximately 1001 CSS pixels tall.
  if (account.height > 1001) failures.push({ printAccountTooTall: account.height });
  await printPage.locator('#account').screenshot({ path: `${out}/print-account.png` });
  await printPage.pdf({ path: `${out}/research-review.pdf`, preferCSSPageSize: true, printBackground: true });
  receipts.push({ printAccountHeight: account.height, availableA4Height: 1001 });
  await printContext.close();
} finally { await browser.close(); }
await fs.writeFile(`${out}/receipt.json`, JSON.stringify({ receipts, failures }, null, 2));
console.log(JSON.stringify({ receipts, failures }, null, 2));
if (failures.length) process.exitCode = 1;
