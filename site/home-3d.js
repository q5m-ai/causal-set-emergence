import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";

function makeViewer(stage, cameraPosition, target = new THREE.Vector3()) {
  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x04060d);
  const camera = new THREE.PerspectiveCamera(42, 1, 0.1, 100);
  camera.position.copy(cameraPosition);
  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  renderer.domElement.setAttribute("aria-hidden", "true");
  stage.insertBefore(renderer.domElement, stage.firstChild);
  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.07;
  controls.minDistance = 2.4;
  controls.maxDistance = 11;
  controls.target.copy(target);
  controls.update();
  const resize = () => {
    const width = stage.clientWidth;
    const height = stage.clientHeight;
    renderer.setSize(width, height, false);
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
  };
  new ResizeObserver(resize).observe(stage);
  resize();
  return { scene, camera, renderer, controls, resize };
}

function disposeGroup(group) {
  while (group.children.length) {
    const child = group.children.pop();
    child.traverse(object => {
      object.geometry?.dispose();
      if (object.material) {
        const materials = Array.isArray(object.material) ? object.material : [object.material];
        materials.forEach(material => material.dispose());
      }
    });
  }
}

// Hero: a causal diamond whose intrinsic content is only events and order.
const heroStage = document.getElementById("heroStage");
try {
  const viewer = makeViewer(heroStage, new THREE.Vector3(3.5, 1.9, 4.3), new THREE.Vector3(0, 0, 0));
  const { scene, controls } = viewer;
  scene.fog = new THREE.Fog(0x04060d, 6.5, 11);
  scene.add(new THREE.HemisphereLight(0xbfe5ff, 0x101726, 2.4));
  const keyLight = new THREE.DirectionalLight(0xffffff, 2.8);
  keyLight.position.set(3, 4, 4);
  scene.add(keyLight);

  const root = new THREE.Group();
  root.rotation.y = -0.38;
  root.rotation.z = -0.04;
  scene.add(root);

  const coneMaterial = new THREE.MeshBasicMaterial({
    color: 0x56b4e9,
    wireframe: true,
    transparent: true,
    opacity: 0.105,
    depthWrite: false
  });
  const upperCone = new THREE.Mesh(new THREE.ConeGeometry(1.2, 1.5, 40, 5, true), coneMaterial);
  upperCone.position.y = 0.75;
  const lowerCone = new THREE.Mesh(new THREE.ConeGeometry(1.2, 1.5, 40, 5, true), coneMaterial.clone());
  lowerCone.rotation.z = Math.PI;
  lowerCone.position.y = -0.75;
  root.add(upperCone, lowerCone);

  for (const [height, radius] of [[-0.75, 0.6], [0, 1.2], [0.75, 0.6]]) {
    const points = [];
    for (let step = 0; step <= 64; step++) {
      const angle = step / 64 * Math.PI * 2;
      points.push(new THREE.Vector3(Math.cos(angle) * radius, height, Math.sin(angle) * radius));
    }
    const ring = new THREE.LineLoop(
      new THREE.BufferGeometry().setFromPoints(points),
      new THREE.LineBasicMaterial({ color: 0x91a3bb, transparent: true, opacity: height ? 0.12 : 0.22 })
    );
    root.add(ring);
  }

  const random = (() => {
    let seed = 0x5ca15e7;
    return () => {
      seed |= 0;
      seed = seed + 0x6D2B79F5 | 0;
      let value = Math.imul(seed ^ seed >>> 15, 1 | seed);
      value = value + Math.imul(value ^ value >>> 7, 61 | value) ^ value;
      return ((value ^ value >>> 14) >>> 0) / 4294967296;
    };
  })();
  const events = [{ t: -1, x: 0, z: 0 }, { t: 1, x: 0, z: 0 }];
  while (events.length < 36) {
    const t = random() * 2 - 1;
    const radius = (1 - Math.abs(t)) * 1.14 * Math.sqrt(random());
    const angle = random() * Math.PI * 2;
    events.push({ t, x: radius * Math.cos(angle), z: radius * Math.sin(angle) });
  }
  events.sort((a, b) => a.t - b.t);
  const selected = events.reduce((best, event, index) => {
    const score = Math.abs(event.t) + Math.hypot(event.x, event.z) * 0.35;
    return score < best.score ? { index, score } : best;
  }, { index: 0, score: Infinity }).index;
  const position = event => new THREE.Vector3(event.x, event.t * 1.5, event.z);
  const precedes = (a, b) => {
    const dt = (b.t - a.t) * 1.15;
    return dt > 0 && (b.x - a.x) ** 2 + (b.z - a.z) ** 2 <= dt ** 2;
  };
  const isLink = (first, second) => {
    if (!precedes(events[first], events[second])) return false;
    return !events.some((event, index) => index !== first && index !== second && precedes(events[first], event) && precedes(event, events[second]));
  };

  for (let first = 0; first < events.length; first++) {
    for (let second = first + 1; second < events.length; second++) {
      if (!isLink(first, second)) continue;
      const highlighted = first === selected || second === selected;
      const line = new THREE.Line(
        new THREE.BufferGeometry().setFromPoints([position(events[first]), position(events[second])]),
        new THREE.LineBasicMaterial({
          color: highlighted ? 0xed8068 : 0x56b4e9,
          transparent: true,
          opacity: highlighted ? 0.82 : 0.26
        })
      );
      root.add(line);
    }
  }

  const sphere = new THREE.SphereGeometry(0.042, 18, 12);
  let selectedMesh;
  events.forEach((event, index) => {
    const endpoint = index === 0 || index === events.length - 1;
    const related = index !== selected && (precedes(event, events[selected]) || precedes(events[selected], event));
    const color = index === selected ? 0xf2bf63 : endpoint ? 0xffffff : related ? 0x8bd7ff : 0x76859b;
    const point = new THREE.Mesh(sphere, new THREE.MeshStandardMaterial({
      color,
      emissive: color,
      emissiveIntensity: index === selected ? 0.85 : related ? 0.28 : 0.08,
      roughness: 0.32
    }));
    point.position.copy(position(event));
    point.scale.setScalar(index === selected ? 1.8 : endpoint ? 1.25 : 1);
    root.add(point);
    if (index === selected) selectedMesh = point;
  });

  const axis = new THREE.Line(
    new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(0, -1.72, 0), new THREE.Vector3(0, 1.72, 0)]),
    new THREE.LineDashedMaterial({ color: 0xf2bf63, transparent: true, opacity: 0.34, dashSize: 0.07, gapSize: 0.065 })
  );
  axis.computeLineDistances();
  root.add(axis);

  let engaged = false;
  controls.addEventListener("start", () => { engaged = true; });
  heroStage.querySelector(".three-loading")?.remove();
  const reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  const clock = new THREE.Clock();
  const animate = () => {
    const elapsed = clock.getElapsedTime();
    if (!engaged && !reduceMotion) root.rotation.y += 0.0014;
    if (selectedMesh && !reduceMotion) selectedMesh.scale.setScalar(1.72 + Math.sin(elapsed * 2.4) * 0.12);
    controls.update();
    viewer.renderer.render(scene, viewer.camera);
    requestAnimationFrame(animate);
  };
  animate();
} catch (error) {
  const loading = heroStage?.querySelector(".three-loading");
  if (loading) loading.textContent = "The causal-set view could not load.";
  console.error(error);
}

// Continuum concepts: the same rotatable renderer, three different structures.
const conceptStage = document.getElementById("conceptStage");
const conceptText = document.getElementById("conceptText");
const conceptCopy = {
  manifold: ["Manifold", "The continuous stage of GR: a collection of points that locally resembles ordinary coordinate space. It lets us draw smooth paths and define fields.", "the fabric—not yet its measurements."],
  topology: ["Topology", "The rules of neighborhood and connection: which regions join, what can be continuously deformed, and whether the space contains holes.", "connectedness without a ruler."],
  metric: ["Metric", "The field gμν that supplies spacetime geometry. It determines proper time, spatial distance, light cones, volume, angles, and curvature.", "the ruler, clock, and light-cone structure."]
};

try {
  const viewer = makeViewer(conceptStage, new THREE.Vector3(4, 2.8, 4.8));
  const { scene } = viewer;
  scene.add(new THREE.HemisphereLight(0xc9e6ff, 0x17263a, 2.1));
  const light = new THREE.DirectionalLight(0xffffff, 2.2);
  light.position.set(3, 5, 4);
  scene.add(light);
  const root = new THREE.Group();
  scene.add(root);

  const surface = geometry => {
    const mesh = new THREE.Mesh(geometry, new THREE.MeshStandardMaterial({ color: 0x1769c2, roughness: 0.55, metalness: 0.05, transparent: true, opacity: 0.72, side: THREE.DoubleSide }));
    const grid = new THREE.Mesh(geometry.clone(), new THREE.MeshBasicMaterial({ color: 0x8bd7ff, wireframe: true, transparent: true, opacity: 0.34 }));
    root.add(mesh, grid);
  };

  function drawConcept(name) {
    disposeGroup(root);
    root.rotation.set(0, 0, 0);
    const [title, body, think] = conceptCopy[name];
    conceptText.innerHTML = `<h3>${title}</h3><p>${body}</p><p><strong>Think:</strong> ${think}</p>`;
    conceptStage.setAttribute("aria-label", `Rotatable three-dimensional visualization of ${title.toLowerCase()}`);

    if (name === "manifold") {
      const geometry = new THREE.PlaneGeometry(4.2, 3.1, 28, 22);
      const positions = geometry.attributes.position;
      for (let i = 0; i < positions.count; i++) {
        const x = positions.getX(i), y = positions.getY(i);
        positions.setZ(i, 0.34 * Math.sin(x * 1.25) * Math.cos(y * 1.5) + 0.08 * x);
      }
      geometry.computeVertexNormals();
      root.rotation.x = -0.35;
      surface(geometry);
      const point = new THREE.Mesh(new THREE.SphereGeometry(0.075, 20, 14), new THREE.MeshBasicMaterial({ color: 0xf2bf63 }));
      point.position.set(0.6, 0.25, 0.32 * Math.sin(0.75) * Math.cos(0.375) + 0.048);
      root.add(point);
    } else if (name === "topology") {
      root.rotation.set(0.45, 0.15, 0);
      surface(new THREE.TorusGeometry(1.25, 0.48, 22, 64));
    } else {
      const geometry = new THREE.PlaneGeometry(4.1, 3.1, 30, 24);
      const positions = geometry.attributes.position;
      for (let i = 0; i < positions.count; i++) {
        const x = positions.getX(i), y = positions.getY(i);
        const radius2 = x * x + y * y;
        positions.setZ(i, -0.72 * Math.exp(-radius2 * 0.85));
      }
      geometry.computeVertexNormals();
      root.rotation.x = -0.25;
      surface(geometry);
      const cone = new THREE.Mesh(new THREE.ConeGeometry(0.72, 1.35, 32, 1, true), new THREE.MeshBasicMaterial({ color: 0xed8068, wireframe: true, transparent: true, opacity: 0.75 }));
      cone.rotation.x = Math.PI / 2;
      cone.position.set(0, 0, 0.15);
      root.add(cone);
    }
  }

  document.querySelectorAll(".tab[data-concept]").forEach(tab => tab.addEventListener("click", () => drawConcept(tab.dataset.concept)));
  drawConcept("manifold");
  conceptStage.querySelector(".three-loading")?.remove();

  const animate = () => {
    viewer.controls.update();
    viewer.renderer.render(scene, viewer.camera);
    requestAnimationFrame(animate);
  };
  animate();
} catch (error) {
  const loading = conceptStage.querySelector(".three-loading");
  if (loading) loading.textContent = "The 3D concept view could not load.";
  console.error(error);
}

// Locality: one rotatable 2+1-dimensional sprinkling replaces two disconnected SVG demos.
const localityStage = document.getElementById("localityStage");
try {
  const viewer = makeViewer(localityStage, new THREE.Vector3(3.4, 2.5, 4.2));
  const { scene, camera, renderer, controls } = viewer;
  scene.add(new THREE.HemisphereLight(0xc9e6ff, 0x17263a, 2));
  const diamond = new THREE.Group();
  scene.add(diamond);

  const coneMaterial = new THREE.MeshBasicMaterial({ color: 0x56b4e9, wireframe: true, transparent: true, opacity: 0.16, depthWrite: false });
  const lower = new THREE.Mesh(new THREE.ConeGeometry(1, 1, 40, 4, true), coneMaterial);
  lower.rotation.z = Math.PI;
  lower.position.y = -0.5;
  const upper = new THREE.Mesh(new THREE.ConeGeometry(1, 1, 40, 4, true), coneMaterial.clone());
  upper.position.y = 0.5;
  diamond.add(lower, upper);
  const endpointGeometry = new THREE.SphereGeometry(0.055, 18, 12);
  const endpointMaterial = new THREE.MeshBasicMaterial({ color: 0xf2bf63 });
  for (const y of [-1, 1]) {
    const endpoint = new THREE.Mesh(endpointGeometry, endpointMaterial);
    endpoint.position.y = y;
    diamond.add(endpoint);
  }

  const eventGroup = new THREE.Group();
  const linkGroup = new THREE.Group();
  scene.add(eventGroup, linkGroup);
  let events = [];
  let selected = 0;
  const raycaster = new THREE.Raycaster();
  const pointer = new THREE.Vector2();

  function generator(seed) {
    return () => {
      seed |= 0;
      seed = seed + 0x6D2B79F5 | 0;
      let value = Math.imul(seed ^ seed >>> 15, 1 | seed);
      value = value + Math.imul(value ^ value >>> 7, 61 | value) ^ value;
      return ((value ^ value >>> 14) >>> 0) / 4294967296;
    };
  }

  function sprinkle(count) {
    const random = generator(193 + count * 17);
    const points = [];
    while (points.length < count) {
      const t = random() * 2 - 1;
      const radius = 1 - Math.abs(t);
      if (random() > radius * radius) continue;
      const radial = Math.sqrt(random()) * radius;
      const angle = random() * Math.PI * 2;
      points.push({ t, x: radial * Math.cos(angle), y: radial * Math.sin(angle) });
    }
    return points.sort((a, b) => a.t - b.t);
  }

  function related(a, b) {
    const dt = b.t - a.t;
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    return dt > 0 && dx * dx + dy * dy <= dt * dt;
  }

  function isLink(aIndex, bIndex) {
    let first = aIndex, second = bIndex;
    if (events[first].t > events[second].t) [first, second] = [second, first];
    const a = events[first], b = events[second];
    if (!related(a, b)) return false;
    return !events.some((z, index) => index !== first && index !== second && related(a, z) && related(z, b));
  }

  function position(event) {
    return new THREE.Vector3(event.x, event.t, event.y);
  }

  function drawSelection() {
    disposeGroup(eventGroup);
    disposeGroup(linkGroup);
    const chosen = events[selected];
    let relatedCount = 0;
    let linkCount = 0;
    const sphereGeometry = new THREE.SphereGeometry(0.035, 16, 10);

    events.forEach((event, index) => {
      const isSelected = index === selected;
      const isRelated = !isSelected && (related(event, chosen) || related(chosen, event));
      const linked = isRelated && isLink(index, selected);
      if (isRelated) relatedCount++;
      if (linked) linkCount++;
      const color = isSelected ? 0xf2bf63 : linked ? 0xed8068 : isRelated ? 0x56b4e9 : 0x7f90aa;
      const mesh = new THREE.Mesh(sphereGeometry.clone(), new THREE.MeshStandardMaterial({ color, emissive: color, emissiveIntensity: isSelected ? 0.45 : 0.16, roughness: 0.45 }));
      mesh.position.copy(position(event));
      mesh.scale.setScalar(isSelected ? 1.65 : linked ? 1.25 : 1);
      mesh.userData.eventIndex = index;
      eventGroup.add(mesh);
      if (linked) {
        const geometry = new THREE.BufferGeometry().setFromPoints([position(chosen), position(event)]);
        linkGroup.add(new THREE.Line(geometry, new THREE.LineBasicMaterial({ color: 0xed8068, transparent: true, opacity: 0.74 })));
      }
    });

    document.getElementById("localitySelection").textContent = `Event ${selected + 1}`;
    document.getElementById("localityRelated").textContent = relatedCount;
    document.getElementById("localityLinks").textContent = linkCount;
  }

  function regenerate() {
    const count = Number(document.getElementById("localityDensity").value);
    events = sprinkle(count);
    selected = Math.floor(count / 2);
    document.getElementById("localityDensityOut").textContent = count;
    drawSelection();
  }

  renderer.domElement.addEventListener("pointerdown", event => {
    const box = renderer.domElement.getBoundingClientRect();
    pointer.x = (event.clientX - box.left) / box.width * 2 - 1;
    pointer.y = -(event.clientY - box.top) / box.height * 2 + 1;
    raycaster.setFromCamera(pointer, camera);
    const hit = raycaster.intersectObjects(eventGroup.children, false)[0];
    if (hit) {
      selected = hit.object.userData.eventIndex;
      drawSelection();
    }
  });

  document.getElementById("localityDensity").addEventListener("input", regenerate);
  document.getElementById("localityReset").addEventListener("click", () => {
    camera.position.set(3.4, 2.5, 4.2);
    controls.target.set(0, 0, 0);
    controls.update();
  });
  regenerate();
  localityStage.querySelector(".three-loading")?.remove();

  const animate = () => {
    controls.update();
    renderer.render(scene, camera);
    requestAnimationFrame(animate);
  };
  animate();
} catch (error) {
  const loading = localityStage.querySelector(".three-loading");
  if (loading) loading.textContent = "The 3D locality explorer could not load.";
  console.error(error);
}
