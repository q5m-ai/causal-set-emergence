import { SAMPLE_COUNT, sampleSlice, markedPair, pairMetrics, precedes, sector, kernel } from "./proof-spine-model.js";

const ids = ["faces", "joint", "cones", "interval", "points", "relations", "split"];
const inputs = Object.fromEntries(ids.map(id => [id, document.getElementById(`show-${id}`)]));
const cutoff = document.getElementById("spine-cutoff");
const pairChoice = document.getElementById("pair-choice");
const guides = {
  faces: { layers: ["faces", "joint"], pair: "axial", copy: "The two spacelike faces meet along a circle in this slice. The actual 4D joint is a two-sphere, not this circle." },
  interval: { layers: ["faces", "joint", "cones", "interval"], pair: "axial", copy: "A ≺ B. The gold interval is the future of A intersected with the past of B. Its boundary rays are null; its interior contains possible intermediate events." },
  points: { layers: ["faces", "joint", "interval", "points", "relations"], pair: "axial", copy: "Uniform slice locations, conditional on 56 events. Lines show all causal pairs, not just links. Gold points lie strictly between the marked endpoints A and B." },
  split: { layers: ["joint", "interval", "points", "relations", "split"], pair: "null", copy: "A long, nearly-null pair can have small proper time. Blue solid pairs have v < δ; coral dashed pairs have v ≥ δ. Equality is long. The split uses coordinates, not camera distance." }
};
let seed = 193, points = sampleSlice(seed), viewer;
function state() {
  return { layers: Object.fromEntries(ids.map(id => [id, inputs[id].checked])), pair: pairChoice.value, delta: Number(cutoff.value), points };
}
function update() {
  const current = state(), [a, b] = markedPair(current.pair), metrics = pairMetrics(a, b);
  let short = 0, long = 0;
  for (let i = 0; i < points.length; i++) for (let j = 0; j < points.length; j++) {
    if (!precedes(points[i], points[j])) continue;
    if (sector(points[i], points[j], current.delta) === "short") short++; else long++;
  }
  const between = points.filter(p => precedes(a, p) && precedes(p, b)).length;
  document.getElementById("cutoff-out").textContent = current.delta.toFixed(3);
  document.getElementById("pair-readout").textContent = `A–B: v = ${metrics.v.toFixed(3)}, σ = ${metrics.sigma.toFixed(6)}. At δ = ${current.delta.toFixed(3)} this pair is ${sector(a, b, current.delta)}. ${between} sampled events between A and B. Sample pairs: ${short} short, ${long} long (${SAMPLE_COUNT} points; marked endpoints excluded).`;
  viewer?.update(current);
}
function guide(name) {
  const g = guides[name];
  ids.forEach(id => { inputs[id].checked = g.layers.includes(id); });
  pairChoice.value = g.pair;
  document.getElementById("guide-copy").textContent = g.copy;
  document.querySelectorAll("[data-guide]").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.guide === name)));
  update();
}
function custom() {
  document.querySelectorAll("[data-guide]").forEach(b => b.setAttribute("aria-pressed", "false"));
  document.getElementById("guide-copy").textContent = "Custom view. The layer checkboxes, marked pair and cutoff are independent explanatory controls; none evaluates the 4D action.";
  update();
}
ids.forEach(id => inputs[id].addEventListener("change", custom));
pairChoice.addEventListener("change", custom);
cutoff.addEventListener("input", update);
document.querySelectorAll("[data-guide]").forEach(button => button.addEventListener("click", () => guide(button.dataset.guide)));
document.getElementById("front-view").addEventListener("click", () => viewer?.front());
document.getElementById("orbit-view").addEventListener("click", () => viewer?.reset());
document.getElementById("zoom-in").addEventListener("click", () => viewer?.zoom(0.8));
document.getElementById("zoom-out").addEventListener("click", () => viewer?.zoom(1.25));
document.querySelectorAll("[data-visit]").forEach(link => link.addEventListener("click", () => {
  guide(link.dataset.visit);
  document.getElementById("example-lab").focus({ preventScroll: true });
}));
document.getElementById("reset-view").addEventListener("click", () => {
  seed = 193; points = sampleSlice(seed); cutoff.value = "0.40";
  guide("faces"); viewer?.reset();
});
document.getElementById("resprinkle").addEventListener("click", () => {
  points = sampleSlice(++seed); inputs.points.checked = true; custom();
});
update();

// An illustrative finite plot, never a numeric certification of zero moments.
const svg = document.getElementById("kernel-chart"), NS = "http://www.w3.org/2000/svg";
function el(tag, attrs, text) {
  const node = document.createElementNS(NS, tag);
  Object.entries(attrs).forEach(([k, v]) => node.setAttribute(k, v));
  if (text) node.textContent = text;
  return node;
}
svg.querySelector("[data-static-kernel]")?.remove();
const X = w => 52 + w / 3.5 * 600, Y = k => 120 - 70 * k;
svg.append(el("line", { x1: 52, x2: 652, y1: 120, y2: 120, stroke: "currentColor", opacity: 0.35 }));
for (let w = 0; w <= 3.5; w += 0.5) {
  svg.append(el("text", { x: X(w), y: 203, fill: "currentColor", "text-anchor": "middle", "font-size": 12 }, w.toFixed(1)));
}
for (const k of [-1, 0, 1]) svg.append(el("text", { x: 40, y: Y(k) + 4, fill: "currentColor", "text-anchor": "end", "font-size": 12 }, String(k)));
let curve = "";
for (let i = 0; i <= 500; i++) {
  const w = 3.5 * i / 500, k = kernel(w * w);
  curve += `${i ? "L" : "M"}${X(w)},${Y(k)} `;
  if (i < 500) {
    const next = 3.5 * (i + 1) / 500;
    svg.append(el("path", { d: `M${X(w)},120 L${X(w)},${Y(k)} L${X(next)},${Y(kernel(next * next))} L${X(next)},120 Z`, fill: k >= 0 ? "#2a78d6" : "#bf4935", opacity: 0.25 }));
  }
}
svg.append(el("path", { d: curve, fill: "none", stroke: "currentColor", "stroke-width": 1.8 }));
svg.append(el("text", { x: 54, y: 24, fill: "currentColor", "font-size": 13 }, "K(w²) · signed transverse kernel"));
svg.append(el("text", { x: 650, y: 225, fill: "currentColor", "text-anchor": "end", "font-size": 12 }, "w = √(cρ) σ · not coordinate distance"));

// Dynamic imports keep the readout, chart and fallback functional on CDN or
// WebGL failure. Same Three.js version and OrbitControls as the existing site.
try {
  const { createViewer } = await import("./proof-spine-viewer.js");
  viewer = createViewer(document.getElementById("spineStage"));
  update();
} catch (error) {
  document.getElementById("viewer-status").textContent = "3D unavailable: static section retained. Pair/cutoff controls still work.";
  console.warn("Proof-spine 3D fallback:", error.message);
}
