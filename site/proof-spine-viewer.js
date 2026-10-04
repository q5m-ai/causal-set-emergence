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
  const defaultStatus = "Drag to rotate · Pinch / scroll to zoom · No auto-motion";
  status.textContent = defaultStatus;
  let visible = true, pending = false, alive = true;
  function draw() {
    if (!visible || pending || !alive) return;
    pending = true;
    requestAnimationFrame(() => { pending = false; if (alive && visible) renderer.render(scene, camera); });
  }
  controls.addEventListener("change", draw);
  // Fit the actual slice and axes, not a sphere or a stretched time coordinate.
  // Framing adapts to portrait, wide hero, drawer and fullscreen sizes while
  // keeping the current orientation and relative user zoom on resize.
  const framingPoints = [new THREE.Vector3(0, 0.74, 0), new THREE.Vector3(0, -0.65, 0)];
  for (const axis of ["x", "z"]) for (const sign of [-1, 1]) {
    const p = new THREE.Vector3(); p[axis] = sign * 1.36; framingPoints.push(p);
  }
  for (let r = 0; r <= 1; r += 0.125) for (let a = 0; a < Math.PI * 2; a += Math.PI / 32) {
    const x = r * Math.cos(a), y = r * Math.sin(a);
    for (const sign of [-1, 1]) framingPoints.push(position({ x, y, t: sign * faceHeight(x, y) }));
  }
  function framingDistance() {
    const right = new THREE.Vector3(1, 0, 0).applyQuaternion(camera.quaternion);
    const up = new THREE.Vector3(0, 1, 0).applyQuaternion(camera.quaternion);
    const back = camera.position.clone().normalize();
    const tangent = Math.tan(THREE.MathUtils.degToRad(camera.fov / 2));
    let distance = 0;
    for (const p of framingPoints) distance = Math.max(distance,
      p.dot(back) + Math.abs(p.dot(right)) / (tangent * camera.aspect),
      p.dot(back) + Math.abs(p.dot(up)) / tangent);
    return distance * 1.1;
  }
  function fitCamera(zoom = 1) {
    const distance = framingDistance();
    controls.minDistance = distance * 0.55; controls.maxDistance = distance * 2.6;
    camera.position.setLength(distance * Math.max(0.55, Math.min(2.6, zoom)));
    controls.update(); draw();
  }
  let sized = false;
  const resize = new ResizeObserver(() => {
    if (!stage.clientWidth || !stage.clientHeight) return;
    const zoom = sized ? camera.position.length() / framingDistance() : 1;
    renderer.setSize(stage.clientWidth, stage.clientHeight, false);
    camera.aspect = stage.clientWidth / stage.clientHeight; camera.updateProjectionMatrix();
    fitCamera(zoom); sized = true;
  }); resize.observe(stage);
  const observer = new IntersectionObserver(entries => { visible = entries[0].isIntersecting; if (visible) draw(); }); observer.observe(stage);
  renderer.domElement.addEventListener("webglcontextlost", e => {
    e.preventDefault(); alive = false; renderer.domElement.hidden = true; fallback.hidden = false;
    status.textContent = "Graphics context lost: static section retained. Pair/cutoff controls still work.";
    document.querySelectorAll(".camera-controls button").forEach(button => { button.disabled = true; });
    controls.dispose(); resize.disconnect(); observer.disconnect();
  });
  let previous = {}, relationLines = [], markedLine;
  function update(state) {
    if (!alive) return;
    const pairChanged = previous.pair !== state.pair, sampleChanged = previous.points !== state.points;
    let changed = pairChanged || sampleChanged;
    Object.entries({ ...state.layers, marked: state.layers.interval || state.layers.cones || state.layers.points || state.layers.split }).forEach(([id, show]) => {
      if (groups[id]) { changed ||= groups[id].visible !== show; groups[id].visible = show; }
    });
    const [a, b] = markedPair(state.pair);
    if (pairChanged) {
      for (const id of ["cones", "interval", "marked"]) clear(groups[id]);
      for (const [p, text] of [[a, "A"], [b, "B"]]) {
        const dot = new THREE.Mesh(new THREE.SphereGeometry(0.019, 12, 8), new THREE.MeshBasicMaterial({ color: colors.joint }));
        dot.position.copy(position(p)); groups.marked.add(dot, label(text, position(p).add(new THREE.Vector3(0.065, 0.015, 0)), "#ffd37c"));
      }
      markedLine = line([position(a), position(b)], colors.joint, 0.9, true);
      groups.marked.add(markedLine);
      // Both sheets are the same boosted rest-frame null surfaces as the model.
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
    }
    if (pairChanged || sampleChanged) {
      clear(groups.points);
      state.points.forEach(p => {
        const inside = precedes(a, p) && precedes(p, b);
        const dot = new THREE.Mesh(new THREE.SphereGeometry(inside ? 0.014 : 0.010, 8, 6), new THREE.MeshBasicMaterial({ color: inside ? colors.joint : colors.point }));
        dot.position.copy(position(p)); groups.points.add(dot);
      });
    }
    if (sampleChanged) {
      clear(groups.relations); relationLines = [];
      for (const first of state.points) for (const second of state.points) {
        if (!precedes(first, second)) continue;
        const object = line([position(first), position(second)], colors.short, 0.27, true);
        groups.relations.add(object); relationLines.push({ first, second, object });
      }
    }
    // Reuse geometry on cutoff changes. A zero dash gap is a solid line;
    // classification still calls the exact shared strict-short/closed-long rule.
    if (pairChanged || sampleChanged || previous.split !== state.layers.split || (state.layers.split && previous.delta !== state.delta)) {
      markedLine.material.gapSize = state.layers.split && sector(a, b, state.delta) === "long" ? 0.012 : 0;
      for (const { first, second, object } of relationLines) {
        const long = state.layers.split && sector(first, second, state.delta) === "long";
        object.material.color.set(long ? colors.long : colors.short);
        object.material.gapSize = long ? 0.012 : 0;
      }
      changed = true;
    }
    previous = { pair: state.pair, points: state.points, split: state.layers.split, delta: state.delta };
    if (changed) draw();
  }
  return {
    update,
    front() { camera.position.set(0, 0, 3.5); controls.target.set(0, 0, 0); controls.update(); fitCamera(); status.textContent = "Front projection along x₂ · joint circle projects to a line"; },
    reset() { camera.position.copy(initial); controls.target.set(0, 0, 0); controls.update(); fitCamera(); status.textContent = defaultStatus; },
    zoom(factor) { camera.position.setLength(Math.min(controls.maxDistance, Math.max(controls.minDistance, camera.position.length() * factor))); controls.update(); draw(); }
  };
}
