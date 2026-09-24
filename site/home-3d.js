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
