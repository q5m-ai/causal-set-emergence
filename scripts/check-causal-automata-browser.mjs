// Usage: PLAYWRIGHT_MODULE=/absolute/path/to/playwright/index.mjs node scripts/check-causal-automata-browser.mjs
// Uses file:// deliberately: the artifact must work offline without a server.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
const {chromium}=await import(process.env.PLAYWRIGHT_MODULE || 'playwright');
const browser=await chromium.launch({headless:true});
const url=new URL('../site/causal-automata.html',import.meta.url).href;
const out=process.env.SCREENSHOT_DIR || '/tmp/causal-automata-browser';
await fs.mkdir(out,{recursive:true});
try {
  for(const viewport of [{width:1440,height:1100},{width:390,height:844},{width:320,height:740}]) {
    const page=await browser.newPage({viewport}),errors=[],network=[];
    page.on('pageerror',e=>errors.push(e.message));
    page.on('request',r=>{if(/^https?:/.test(r.url()))network.push(r.url());});
    await page.goto(url);
    await page.waitForFunction(()=>document.querySelector('#possible-count').textContent!=='—');
    assert.equal(await page.locator('#truth tr').count(),8);
    const screenshot=async name=>page.screenshot({path:`${out}/${viewport.width}-${name}.png`,fullPage:true});
    await screenshot('states');
    await page.locator('[data-tour="order"]').click();
    assert.equal(await page.locator('[data-mode="order"]').getAttribute('aria-pressed'),'true');
    const order=await page.evaluate(()=>[document.querySelector('#world30').toDataURL(),document.querySelector('#world150').toDataURL()]);
    assert.equal(order[0],order[1],'Causal-order panels must be pixel-identical');
    await screenshot('order');
    await page.locator('[data-tour="difference"]').click();
    assert.equal(await page.locator('#initial').inputValue(),'random');
    const differences=await page.evaluate(()=>[document.querySelector('#world30').toDataURL(),document.querySelector('#world150').toDataURL()]);
    assert.notEqual(differences[0],differences[1]);
    await screenshot('difference');
    // Pointer selection is shared between the worlds.
    const canvas=page.locator('#world30'),box=await canvas.boundingBox();
    await canvas.click({position:{x:box.width/2,y:box.height*10.5/49}});
    assert.equal(await page.locator('#event-x').inputValue(),'0');
    assert.equal(await page.locator('#event-t').inputValue(),'10');
    await canvas.press('ArrowRight');assert.equal(await page.locator('#event-x').inputValue(),'1');
    await canvas.press('ArrowDown');assert.equal(await page.locator('#event-t').inputValue(),'11');
    await page.locator('#event-x').fill('-40');await page.locator('#event-x').press('Tab');
    assert.equal(await page.locator('#event-x').inputValue(),'-40');
    await page.locator('#event-t').fill('48');await page.locator('#event-t').press('Tab');
    assert.equal(await page.locator('#effect-count').textContent(),'0 / 0');
    await page.locator('#time').evaluate(el=>{el.value=0;el.dispatchEvent(new Event('input'));});
    assert.match(await page.locator('#selection').textContent(),/not yet revealed/);
    assert.equal(await page.locator('#event-count').textContent(),'81');
    await page.locator('#play').click();
    await page.waitForFunction(()=>Number(document.querySelector('#time').value)>=2);
    await page.locator('#play').click();
    assert.equal(await page.locator('#play').getAttribute('aria-pressed'),'false');
    await page.locator('#new-seed').click();assert.equal(await page.locator('#seed').inputValue(),'31');
    for(const kind of ['zero','periodic','single']) await page.locator('#initial').selectOption(kind);
    await page.locator('[data-tour="patterns"]').click();
    assert.equal(await page.locator('#time').inputValue(),'48');
    assert.equal(await page.locator('#initial').inputValue(),'single');
    await page.locator('summary').click();
    assert.equal(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),true,'No horizontal overflow');
    if(process.env.AXE_SCRIPT) {
      await page.addScriptTag({path:process.env.AXE_SCRIPT});
      const violations=await page.evaluate(async()=> (await axe.run(document,{runOnly:{type:'tag',values:['wcag2a','wcag2aa','wcag21aa']}})).violations.map(v=>({id:v.id,nodes:v.nodes.map(n=>n.target)})));
      assert.deepEqual(violations,[]);
    }
    assert.deepEqual(errors,[]);assert.deepEqual(network,[]);
    console.log(`PASS ${viewport.width}px: offline load, identical order, different perturbations, controls, keyboard, playback, no overflow${process.env.AXE_SCRIPT?', axe WCAG AA':''}.`);
    await page.close();
  }
} finally {await browser.close();}
