import test from "node:test";
import assert from "node:assert/strict";
import { SLOPE, PAIRS, faceHeight, inRegion, precedes, sector, pairMetrics, markedPair, sampleSlice, intervalPoint, kernel, capsuleTarget } from "../site/proof-spine-model.js";

test("exact steep-capsule slice and independent 4D target", () => {
  assert.equal(SLOPE, 0.75);
  assert.equal(faceHeight(0, 0), 3 / 8);
  assert.equal(faceHeight(1, 0), 0);
  assert.ok(inRegion({ t: 0, x: 0, y: 0 }));
  assert.ok(!inRegion({ t: 0, x: 1, y: 0 }));
  assert.ok(!inRegion({ t: 3 / 8, x: 0, y: 0 }));
  assert.ok(Math.abs(capsuleTarget() - 25 * Math.PI / 6) < 1e-14);
});
test("conditional uniform-location rejection sample is deterministic and contained", () => {
  const points = sampleSlice(193);
  assert.equal(points.length, 56);
  assert.deepEqual(points, sampleSlice(193));
  assert.notDeepEqual(points, sampleSlice(194));
  assert.ok(points.every(inRegion));
  // Distribution regression only, not certification of the probability law.
  const large = sampleSlice(1, 20000);
  const r2 = large.reduce((sum, p) => sum + p.x ** 2 + p.y ** 2, 0) / large.length;
  // Slice radial density ∝ r(1-r²), hence E[r²]=1/3.
  assert.ok(Math.abs(r2 - 1 / 3) < 0.012);
});
test("causality is oriented, Euclidean-spatial, and includes null relations", () => {
  const zero = { t: 0, x: 0, y: 0 };
  assert.ok(precedes(zero, { t: 1, x: 0.6, y: 0.8 }));
  assert.ok(!precedes(zero, { t: -1, x: 0, y: 0 }));
  assert.ok(!precedes(zero, zero));
  assert.ok(!precedes(zero, { t: 1, x: 0.8, y: 0.8 }));
});
test("short is strictly v<delta; equality is long, not a proper-time cutoff", () => {
  const [a, b] = markedPair("null"), m = pairMetrics(a, b);
  assert.equal(m.v, 0.595);
  assert.ok(Math.abs(m.sigma - 0.002975) < 1e-16);
  assert.equal(sector(a, b, 0.4), "long");
  assert.equal(sector(a, b, m.v), "long");
  assert.equal(sector(a, b, m.v + 0.00001), "short");
  assert.equal(sector(...markedPair("short"), 0.4), "short");
});
test("boosted causal-interval surface has correct endpoints and null boundary", () => {
  for (const name of Object.keys(PAIRS)) {
    const [a, b] = markedPair(name);
    assert.ok(inRegion(a) && inRegion(b) && precedes(a, b));
    for (let lambda = -1; lambda <= 1; lambda += 0.125) for (let angle = 0; angle < 6.3; angle += 0.3) {
      const p = intervalPoint(name, lambda, angle);
      assert.ok(inRegion(p)); // Causal convexity of this concrete slice.
      const am = pairMetrics(a, p), bm = pairMetrics(p, b);
      assert.ok(am.sigma > -1e-14 && bm.sigma > -1e-14);
      assert.ok(Math.abs(lambda < 0 ? am.sigma : bm.sigma) < 1e-14);
    }
    for (const [lambda, expected] of [[-1, a], [1, b]]) {
      const p = intervalPoint(name, lambda, 0);
      for (const coord of ["t", "x", "y"]) assert.ok(Math.abs(p[coord] - expected[coord]) < 1e-14);
    }
  }
});
test("chart uses the signed original kernel, not absolute weights", () => {
  assert.equal(kernel(0), 1);
  assert.ok(kernel(0.5) < 0);
  assert.ok(kernel(2) > 0);
  assert.ok(kernel(6) < 0);
});
