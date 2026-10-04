import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { faceHeight, markedPair, intervalPoint, precedes, sector } from "./proof-spine-model.js";

const colors = { future: 0x56b4e9, past: 0x38c99a, joint: 0xffd37c, short: 0x56b4e9, long: 0xed8068, point: 0x93a4bf };
const position = p => new THREE.Vector3(p.x, p.t, p.y);
function clear(group) {
  for (const child of [...group.children]) {
    child.traverse(obj => {
      obj.geometry?.dispose();
      const materials = Array.isArray(obj.material) ? obj.material : [obj.material];
      materials.filter(Boolean).forEach(m => { m.map?.dispose(); m.dispose(); });
    });
    group.remove(child);
  }
}
function label(text, at, color = "#b9c6dc") {
  const canvas = document.createElement("canvas"); canvas.width = 128; canvas.height = 64;
  const ctx = canvas.getContext("2d"); ctx.font = "30px system-ui"; ctx.fillStyle = color; ctx.textAlign = "center"; ctx.fillText(text, 64, 43);
  const texture = new THREE.CanvasTexture(canvas);
  const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: texture, depthTest: false }));
  sprite.position.copy(at); sprite.scale.set(0.20, 0.10, 1);
  return sprite;
}
function line(points, color, opacity = 1, dashed = false) {
  const material = dashed ? new THREE.LineDashedMaterial({ color, transparent: true, opacity, dashSize: 0.018, gapSize: 0.012 }) : new THREE.LineBasicMaterial({ color, transparent: true, opacity });
  const obj = new THREE.Line(new THREE.BufferGeometry().setFromPoints(points), material);
  if (dashed) obj.computeLineDistances();
  return obj;
}
function radialSurface(point, color, opacity, rings = 24, steps = 64) {
  const vertices = [], indices = [];
  for (let ring = 0; ring <= rings; ring++) for (let i = 0; i <= steps; i++) {
    vertices.push(...position(point(ring / rings, i / steps * 2 * Math.PI)).toArray());
  }
  for (let ring = 0; ring < rings; ring++) for (let i = 0; i < steps; i++) {
    const a = ring * (steps + 1) + i, b = a + steps + 1;
    indices.push(a, b, a + 1, a + 1, b, b + 1);
  }
  const geometry = new THREE.BufferGeometry(); geometry.setAttribute("position", new THREE.Float32BufferAttribute(vertices, 3)); geometry.setIndex(indices);
  return new THREE.Mesh(geometry, new THREE.MeshBasicMaterial({ color, transparent: true, opacity, side: THREE.DoubleSide, depthWrite: false }));
}
export function createViewer(stage) {
  const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: false });
  renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5));
  renderer.setClearColor(0x04060d); renderer.outputColorSpace = THREE.SRGBColorSpace;
  const scene = new THREE.Scene(), camera = new THREE.PerspectiveCamera(42, 1, 0.01, 30);
  const initial = new THREE.Vector3(2.9, 1.95, 3.15); camera.position.copy(initial);
  const controls = new OrbitControls(camera, renderer.domElement);
  // On-demand rendering and no auto-motion, even before reduced-motion is set.
  controls.enableDamping = false; controls.minDistance = 1.8; controls.maxDistance = 7;
  controls.enablePan = false; controls.update();
  const groups = Object.fromEntries(["faces", "joint", "cones", "interval", "points", "relations", "marked"].map(id => [id, new THREE.Group()]));
  Object.values(groups).forEach(g => scene.add(g));
  const axes = new THREE.Group(); scene.add(axes);
  axes.add(line([new THREE.Vector3(-1.18, 0, 0), new THREE.Vector3(1.18, 0, 0)], 0x526580, 0.4));
  axes.add(line([new THREE.Vector3(0, -0.58, 0), new THREE.Vector3(0, 0.58, 0)], 0x526580, 0.5, true));
  axes.add(line([new THREE.Vector3(0, 0, -1.18), new THREE.Vector3(0, 0, 1.18)], 0x526580, 0.4));
  axes.add(label("x₁", new THREE.Vector3(1.25, 0, 0)), label("t", new THREE.Vector3(0, 0.63, 0)), label("x₂", new THREE.Vector3(0, 0, 1.25)));
  for (const sign of [1, -1]) {
    const color = sign === 1 ? colors.future : colors.past;
    const point = (r, a) => ({ x: r * Math.cos(a), y: r * Math.sin(a), t: sign * faceHeight(r * Math.cos(a), r * Math.sin(a)) });
    groups.faces.add(radialSurface(point, color, 0.15));
    for (const r of [0.25, 0.5, 0.75]) groups.faces.add(line(Array.from({ length: 65 }, (_, i) => position(point(r, i / 64 * 2 * Math.PI))), color, 0.36));
    for (let a = 0; a < 2 * Math.PI; a += Math.PI / 4) groups.faces.add(line(Array.from({ length: 25 }, (_, i) => position(point(i / 24, a))), color, 0.36));
  }
  groups.joint.add(line(Array.from({ length: 129 }, (_, i) => new THREE.Vector3(Math.cos(i / 128 * 2 * Math.PI), 0, Math.sin(i / 128 * 2 * Math.PI))), colors.joint));
  const status = document.getElementById("viewer-status"), fallback = stage.querySelector(".scene-fallback");
  renderer.domElement.setAttribute("aria-hidden", "true");
  stage.prepend(renderer.domElement); fallback.hidden = true;
  const defaultStatus = "3D slice · drag / pinch · labeled view, zoom and reset controls available";
  status.textContent = defaultStatus;
  let visible = true, pending = false, alive = true;
  function draw() {
    if (!visible || pending || !alive) return;
    pending = true;
    requestAnimationFrame(() => { pending = false; if (alive && visible) renderer.render(scene, camera); });
  }
  controls.addEventListener("change", draw);
  const resize = new ResizeObserver(() => {
    renderer.setSize(stage.clientWidth, stage.clientHeight, false);
    camera.aspect = stage.clientWidth / stage.clientHeight; camera.updateProjectionMatrix(); draw();
  }); resize.observe(stage);
  const observer = new IntersectionObserver(entries => { visible = entries[0].isIntersecting; if (visible) draw(); }); observer.observe(stage);
  renderer.domElement.addEventListener("webglcontextlost", e => {
    e.preventDefault(); alive = false; renderer.domElement.hidden = true; fallback.hidden = false;
    status.textContent = "Graphics context lost: static section retained. Pair/cutoff controls still work.";
    controls.dispose(); resize.disconnect(); observer.disconnect();
  });
  function update(state) {
    if (!alive) return;
    for (const id of ["cones", "interval", "points", "relations", "marked"]) clear(groups[id]);
    Object.entries(state.layers).forEach(([id, show]) => { if (groups[id]) groups[id].visible = show; });
    const [a, b] = markedPair(state.pair);
    for (const [p, text] of [[a, "A"], [b, "B"]]) {
      const dot = new THREE.Mesh(new THREE.SphereGeometry(0.019, 12, 8), new THREE.MeshBasicMaterial({ color: colors.joint }));
      dot.position.copy(position(p)); groups.marked.add(dot, label(text, position(p).add(new THREE.Vector3(0.065, 0.015, 0)), "#ffd37c"));
    }
    groups.marked.visible = state.layers.interval || state.layers.cones || state.layers.points || state.layers.split;
    groups.marked.add(line([position(a), position(b)], colors.joint, 0.9, sector(a, b, state.delta) === "long" && state.layers.split));
    // Both sheets of the marked interval are boosted rest-frame null surfaces.
    for (const sign of [-1, 1]) groups.interval.add(radialSurface((r, angle) => intervalPoint(state.pair, sign * r, angle), colors.joint, 0.10, 20, 48));
    groups.interval.add(line(Array.from({ length: 65 }, (_, i) => position(intervalPoint(state.pair, 0, i / 64 * 2 * Math.PI))), colors.joint, 0.8));
    for (const angle of [0, Math.PI / 2, Math.PI, 3 * Math.PI / 2]) {
      groups.interval.add(line(Array.from({ length: 41 }, (_, i) => position(intervalPoint(state.pair, i / 20 - 1, angle))), colors.joint, 0.6));
    }
    // Cone scaffolding extends outside M; the interval inside is separately gold.
    for (const [p, direction] of [[a, 1], [b, -1]]) {
      groups.cones.add(radialSurface((r, angle) => ({ t: p.t + direction * r * 0.48, x: p.x + r * 0.48 * Math.cos(angle), y: p.y + r * 0.48 * Math.sin(angle) }), colors.future, 0.045, 8, 40));
      for (let angle = 0; angle < Math.PI * 2; angle += Math.PI / 4) groups.cones.add(line([position(p), position({ t: p.t + direction * 0.48, x: p.x + 0.48 * Math.cos(angle), y: p.y + 0.48 * Math.sin(angle) })], colors.future, 0.27, true));
    }
    state.points.forEach(p => {
      const inside = precedes(a, p) && precedes(p, b);
      const dot = new THREE.Mesh(new THREE.SphereGeometry(inside ? 0.014 : 0.010, 8, 6), new THREE.MeshBasicMaterial({ color: inside ? colors.joint : colors.point }));
      dot.position.copy(position(p)); groups.points.add(dot);
    });
    for (let i = 0; i < state.points.length; i++) for (let j = 0; j < state.points.length; j++) {
      const first = state.points[i], second = state.points[j];
      if (!precedes(first, second)) continue;
      const long = sector(first, second, state.delta) === "long";
      groups.relations.add(line([position(first), position(second)], state.layers.split && long ? colors.long : colors.short, 0.27, state.layers.split && long));
    }
    draw();
  }
  return {
    update,
    front() { camera.position.set(0, 0, 3.5); controls.target.set(0, 0, 0); controls.update(); status.textContent = "Front projection along x₂ · joint circle projects to a line"; draw(); },
    reset() { camera.position.copy(initial); controls.target.set(0, 0, 0); controls.update(); status.textContent = defaultStatus; draw(); },
    zoom(factor) { camera.position.multiplyScalar(Math.min(7, Math.max(1.8, camera.position.length() * factor)) / camera.position.length()); controls.update(); draw(); }
  };
}
