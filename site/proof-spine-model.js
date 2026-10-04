// Pure explanatory geometry. This is a 2+1 slice, NOT a 4D BDG simulation.
export const SLOPE = 3 / 4;
export const SAMPLE_COUNT = 56;
export const PAIRS = {
  axial: { dt: 0.56, r: 0 },
  short: { dt: 0.11, r: 0.06 },
  null: { dt: 0.30, r: 0.295 }
};
export const faceHeight = (x, y) => SLOPE / 2 * (1 - x * x - y * y);
export const inRegion = p => p.x * p.x + p.y * p.y < 1 && Math.abs(p.t) < faceHeight(p.x, p.y);
export function precedes(a, b) {
  const dt = b.t - a.t;
  return dt > 0 && dt * dt >= (b.x - a.x) ** 2 + (b.y - a.y) ** 2;
}
export function pairMetrics(a, b) {
  const dt = b.t - a.t;
  const r = Math.hypot(b.x - a.x, b.y - a.y);
  return { dt, r, v: dt + r, sigma: dt * dt - r * r };
}
// Strict short / closed long matches ShortDisplacement.lean. No tolerance
// changes the mathematical convention; tests exercise exact equality.
export const sector = (a, b, delta) => pairMetrics(a, b).v < delta ? "short" : "long";
export function markedPair(name) {
  const { dt, r } = PAIRS[name];
  return [{ t: -dt / 2, x: -r / 2, y: 0 }, { t: dt / 2, x: r / 2, y: 0 }];
}
export function seededRandom(seed) {
  let state = seed >>> 0;
  return () => {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    return state / 4294967296;
  };
}
export function sampleSlice(seed, n = SAMPLE_COUNT) {
  // Rejection from a constant-density coordinate-volume box. Drawing a
  // uniform radius on each time slice would not give uniform spacetime volume.
  const random = seededRandom(seed), points = [];
  while (points.length < n) {
    const p = { x: 2 * random() - 1, y: 2 * random() - 1, t: SLOPE * (random() - 0.5) };
    if (inRegion(p)) points.push(p);
  }
  return points;
}
export function intervalPoint(name, lambda, angle) {
  // Boost the REST interval, including its endpoints; display axes have equal
  // units. This keeps a tilted interval's null boundary faithful to the metric.
  const { dt, r } = PAIRS[name];
  const tau = Math.sqrt(dt * dt - r * r), beta = r / dt, gamma = dt / tau;
  const t = lambda * tau / 2, radius = (1 - Math.abs(lambda)) * tau / 2;
  const x = radius * Math.cos(angle), y = radius * Math.sin(angle);
  return { t: gamma * (t + beta * x), x: gamma * (x + beta * t), y };
}
export const kernel = u => (1 - 9 * u + 8 * u * u - 4 / 3 * u ** 3) * Math.exp(-u);
export const capsuleTarget = () => 4 * Math.PI * (1 + SLOPE ** 2) / (2 * SLOPE);
