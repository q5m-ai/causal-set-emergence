// The page is intentionally standalone. Exercise its actual embedded model.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
const html = fs.readFileSync(new URL('../site/causal-automata.html', import.meta.url), 'utf8');
const source = html.match(/<script id="causal-model">([\s\S]*?)<\/script>/)[1];
const M = vm.runInNewContext(`${source}\nCausalModel`);
for (const match of html.matchAll(/<script(?: [^>]*)?>([\s\S]*?)<\/script>/g)) new vm.Script(match[1]);
assert.ok(!/<(?:script|link|img)[^>]*(?:src|href)=/i.test(html), 'No external assets');
for (let n=0;n<8;n++) {
  const l=n>>2,c=(n>>1)&1,r=n&1;
  assert.equal(M.bit(30,l,c,r),l^(c|r));
  assert.equal(M.bit(150,l,c,r),l^c^r);
}
// Compare with an independent, wider implementation of the local formulas.
for (const kind of ['single','zero','random','periodic']) {
  for (const rule of [30,150]) {
    const actual=M.history(rule,kind,30), extent=140;
    let previous=Array.from({length:2*extent+1},(_,i)=>M.initialBit(kind,30,i-extent));
    for(let t=0;t<=48;t++) {
      for(let x=-40;x<=40;x++) assert.equal(M.get(actual,x,t),previous[x+extent],`${rule}/${kind}/${x}/${t}`);
      previous=previous.map((c,i)=>rule===30?(previous[i-1]||0)^(c|(previous[i+1]||0)):(previous[i-1]||0)^c^(previous[i+1]||0));
    }
  }
}
let interventions=0;
for (const kind of ['single','zero','random','periodic']) for(const rule of [30,150]) {
  const base=M.history(rule,kind,30);
  for(const event of [{x:0,t:0},{x:0,t:8},{x:-40,t:1},{x:40,t:47},{x:0,t:48}]) {
    const altered=M.history(rule,kind,30,event);
    let expectedPossible=0, expectedChanged=0;
    for(let t=0;t<=48;t++) for(let x=-40;x<=40;x++) {
      const changed=M.get(base,x,t)!==M.get(altered,x,t);
      if(changed) assert.ok((t===event.t&&x===event.x)||M.precedes(event,{x,t}), 'Nothing escapes the causal future');
      if(M.precedes(event,{x,t})){expectedPossible++;expectedChanged+=+changed;}
    }
    assert.equal(M.get(base,event.x,event.t)^M.get(altered,event.x,event.t),1);
    const metrics=M.metrics(base,altered,event,48);
    assert.equal(metrics.possible,expectedPossible);assert.equal(metrics.changed,expectedChanged);
    interventions++;
  }
}
const zero=M.history(150,'zero',0), e={x:0,t:0}, flip=M.history(150,'zero',0,e);
assert.equal(M.get(flip,0,2),1);assert.equal(M.get(flip,1,2),0,'Recombining XOR paths can cancel');
assert.equal(M.metrics(zero,flip,e,0).changed,0,'Source excluded from descendant counts');
assert.equal(M.metrics(zero,flip,e,1).changed,3);
// Reachability agrees with the closed-form cone, using explicit graph traversal.
let reachable=new Set([0]);
for(let t=1;t<12;t++) {
  reachable=new Set([...reachable].flatMap(x=>[x-1,x,x+1]));
  for(let x=-15;x<=15;x++) assert.equal(M.precedes({x:0,t:0},{x,t}),reachable.has(x));
}
assert.equal(M.bit(30,0,0,0),M.bit(30,1,1,1),'Distinct uniform rows have the same Rule 30 future');
console.log(`PASS: embedded script syntax, offline assets, truth tables, padded boundaries, ${interventions} interventions, counts, cancellation, reachability.`);
