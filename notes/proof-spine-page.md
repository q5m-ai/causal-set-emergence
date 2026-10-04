# Proof Spine — Work in Progress: page and validation

## Assessment boundary

The page at [`site/proof-spine.html`](../site/proof-spine.html) assesses main
revision [`8b05befffd4a24fea3724f2d5ed41d33684b9fc5`](https://github.com/q5m-ai/causal-set-emergence/tree/8b05befffd4a24fea3724f2d5ed41d33684b9fc5),
using sources inspected on **2026-10-03**. It is a dated reading guide, not a
live issue-status feed. Research links are pinned to that revision. No existing
research claims, Lean sources, checker inputs, dependencies, or build configuration
are changed. This website pass did **not** rerun the full Lean audit; the
Lean-checked labels refer to the encoded source declarations and existing
validation receipts, not a new verification of the whole proof library.
Independent human mathematical/physical review remains separate and outstanding.

The central route is the current independent-envelope class E, not merely the
older combined-budget class. The source spine is:

1. `formal/BoundaryDraft/DiscreteBDG.lean`: independently defined finite action.
2. `formal/BoundaryDraft/ExpectationBridge.lean`: independently constructed
   Poisson law and exact finite-density equality.
3. `formal/BoundaryDraft/Specification.lean`, `TranslatedOverlap.lean`: original
   signed deterministic action and actual causal-pair overlap.
4. `formal/BoundaryDraft/ShortDisplacement.lean`, `NullCoordinates.lean`: strict
   short / closed long partition, retaining the point term once.
5. `IndependentShortLimit.lean`, `IndependentFaceSurface.lean`,
   `TwoFaceCoefficient.lean`: actual short producer and independent target.
6. `IndependentFaceLongNull.lean`, `NullTransverseMoments.lean`: actual long
   producer and exact signed cancellation.
7. `IndependentFaceLimit.lean`: compatible fixed-cutoff assembly, then expectation.

Those abbreviated names in items 5–7 are under `formal/BoundaryDraft/`.
`IndependentFaceContract.lean` supplies the precise geometric hypotheses;
`IndependentFaceExamples.lean` and `IndependentFaceLimitRegression.lean` supply
the concrete steep-capsule calibration. The page also links the written
proof maps, separate dimensional sources, current supported curved-bulk argument,
and the explicitly open boundary collar. It does not use closed issues or PR
summaries as mathematical evidence.

## Architecture and design reference

This is another page of the existing **build-free static site**, with navigation
links from Home and Dimensions. The current image's `q5m/Dockerfile` already
copies `site/`; no new website, framework, release adapter, or deployment is
introduced. `site/site.css` supplies Outfit, color tokens, navigation, and
bordered surfaces. Page-local additions live in `proof-spine.css`.
MathJax 3 and Three.js 0.160.0 / OrbitControls follow the existing Dimensions
and Home conventions. The imports are pinned to the same versions; no runtime
package installation is needed. CDN failure leaves the narrative and static
geometry intact. The controller and pure model remain independent of the
WebGL import, preserving the pair/cutoff readout when only 3D fails.

The actual Erdős 193 reference was located at
`/home/q5m/code/q5m-ai/erdos-193`, revision
`e5ceac4bf1be27fff297c18be379ae9da4efff83`.
The implementation inspected `viz/proof.html`, `viz/site.css`, and the
corresponding `site/pages/` convention, then viewed the live
[proof](https://erdos-193.q5m.ai/proof.html) and
[learning](https://erdos-193.q5m.ai/learn.html) pages in Chromium.
Useful adaptations are the numbered proof chain, compact evidence boundaries,
reading route, restrained surfaces, and expandable technical explanations.
No Erdős-specific theorem, authorship, logos, publication claims, or branding
is imported.

## Visual accuracy boundary

- The 3D scene is the exact **two-space + one-time slice with the third spatial
  coordinate zero** of the stated 4D capsule. All displayed axes have equal
  physical coordinate units. The joint circle is not the actual two-sphere.
- The front view is explicitly a projection along the second spatial axis;
  the joint circle then projects to a line. Causality uses both slice spatial
  coordinates, not apparent screen distance.
- Interval surfaces are a Lorentz boost of the rest-frame interval. Their
  endpoints, null boundary, containment, and spacelike/causal classification
  have pure-model tests. Ambient cone scaffolding may extend outside the region.
- A seeded, fixed-count pseudorandom rejection sample illustrates uniform slice
  volume. This is the conditional Poisson location law, not Poisson-distributed
  counts, a 4D simulation, or a computed discrete action. Marked endpoints are
  excluded from sample counts. The sampler's radial-moment test is a regression,
  not probability-law certification.
- The exact strict-short / equality-long cutoff convention is shared between
  the renderer, readout, and tests. The slider does not certify a Taylor radius
  or represent a cutoff depending on density.
- The signed-kernel chart is a finite plot, not certified quadrature. Exact
  zero moments and the asymptotic theorem are attributed to actual proof sources,
  never inferred from the plotted lobes.

## Validation receipt (2026-10-04)

After the last implementation change:

- Pure model: **6 Node tests** covering the capsule, target, seeded rejection
  sampler, causal inequality, exact cutoff equality, boosted intervals, and
  signed kernel. These are explanatory-model tests, not research proofs.
- Website contract: **5 Python tests** covering every local HTML link/fragment,
  duplicate IDs, navigation, status boundaries, all pinned research source
  paths at the assessed Git revision, all **121** page math expressions, and
  the Node model suite.
- Full repository Python suite: **240 tests passed**; symbolic checks passed.
- All site and new validation JavaScript syntax checks and `git diff --check`
  passed. Repository Markdown lint and its **20 tests** passed.
- Chromium inspected desktop **1440×1000**, touch-emulated mobile **390×844**,
  and dark/reduced-motion touch-emulated **360×800**. Each rendered **121/121**
  MathJax expressions, with no error nodes or literal delimiters, no page-wide
  horizontal overflow, and no unhandled page errors or failed requests.
  Complete desktop displays were compared with source, including both closing
  inequalities of the capsule. Longer mobile displays remain horizontally
  scrollable; their complete ends were inspected, not merely counted.
- All four guided views, native keyboard toggles, camera/zoom/reset controls,
  sampling, and the exact cutoff endpoint were exercised. There is no autonomous
  motion; rendering is on demand and suspended offscreen. Twenty cutoff updates
  averaged roughly **18–34 ms** in this software-rendered headless test, not a
  hardware/mobile performance guarantee.
- Axe WCAG 2 A/AA and 2.1 AA scan: **zero reported violations** in all three
  normal browser configurations. This is an automated accessibility check,
  not a claim of complete accessibility certification or human assistive-tech
  review. Visible focus, native controls, non-color-only dashed/solid distinction,
  and accessible text alternatives were also inspected.
- Forced WebGL-constructor failure, blocked CDN, and disabled JavaScript retained
  useful static geometry; the first two retained the pair/cutoff readout. A static
  signed-kernel plot and prose also survive without JavaScript.

Browser screenshots and JSON receipts were retained outside the served site
under `/tmp/proof-spine-browser-final/` on the validation host. The browser test
is reproducible; these temporary paths are not permanent public evidence links.
Touch emulation does not establish real phone, Safari, screen-reader, or remote
LAN-client reachability. The managed LAN server returned a healthy listener;
local short-name DNS and HTTP were observed. No merge or public/production
deployment was performed.

### Reproduce the lightweight and browser checks

Use Python 3.12 with the pinned `requirements.txt` for the research regression
suite. Python 3.14 lacks binary wheels for these pinned NumPy/SciPy versions;
no dependency change or compiler installation is needed for this page.

```sh
python3 check_markdown.py
python3 -m unittest -v test_check_markdown test_proof_spine
node --test scripts/test-proof-spine.mjs
for file in site/*.js scripts/*proof-spine.mjs; do node --check "$file"; done
# In an environment with the repository's requirements installed:
python -m unittest -v
python check_symbolic.py
```

For a LAN preview, serve only the dedicated site directory:

```sh
q5m-lab serve --directory ./site --json
```

Keep that foreground process in its own managed terminal and use the exact
cleanup command from its receipt. Browser tests take the returned site URL:

```sh
# Validation-only tooling, installed outside the checkout if necessary:
# npm install --prefix /tmp/proof-spine-tools playwright axe-core
PLAYWRIGHT_MODULE=/path/to/playwright/index.mjs \
AXE_SCRIPT=/path/to/axe-core/axe.min.js \
node scripts/check-proof-spine-browser.mjs SITE_URL /tmp/proof-spine-browser
```

The host used its already available Playwright/Chromium and unprivileged browser
libraries; no fleet update, privileged package installation, or network-policy
change was made. `AXE_SCRIPT` is optional, and the receipt explicitly says when
that scan is not run. Formal reproduction remains the separate workflow in
[`formal/README.md`](../formal/README.md#reproduce).
