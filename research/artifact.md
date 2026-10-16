# Reproducible artifact and evidence boundaries

## Two source identities

- **Mathematics:** integration branch `issue-81-general-coverage` at
  **`9e0068f91c219fe61984d20fdb3f6939eab907c4`** (S), fetched 16 October 2026.
  All principal source links and hashes refer to this immutable commit, not
  whatever a branch later contains.
- **Presentation:** record `git rev-parse HEAD` in this package's checkout.
  New manuscript/site files summarize S; they do not modify its proofs or
  certificates. A subsequent source update needs a new coverage snapshot.

[Evidence manifest](evidence.json) records source-file SHA-256 hashes, the
inspected issue/PR states and public literature/data retrievals. Its hashes
identify bytes, **not correctness**. External pages may later change even at
versioned URLs. Paper bodies and datasets are not redistributed here.

## Small, offline-first reproduction

From an existing clone containing the package and S:

```sh
git status --short
git rev-parse HEAD
git show -s --format='%H %cI %s' 9e0068f91c219fe61984d20fdb3f6939eab907c4
python3 -m unittest -v test_research_release
python3 research/estimate_signals.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

The release tests verify the pinned source hashes through `git show`, internal
packet links, required static-page invariants, and the small feasibility
arithmetic. They do not test mathematical truth. No network or dataset fetch
occurs in them. If S is missing, fetch the integration branch explicitly;
do not silently switch the review to its moving head.

To reproduce original diagnostics separately from presentation changes:

```sh
git worktree add --detach ../cse-source-review 9e0068f91c219fe61984d20fdb3f6939eab907c4
cd ../cse-source-review
python3.12 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -m unittest -v \
  test_curved4_focal_globalization test_curved4_focal_certificate \
  test_flat_klein_bottle_obstruction test_flat_proof_stabilization \
  test_curved4_corrected_convergence test_sphere_weighted_lenses
.venv/bin/python check_symbolic.py
.venv/bin/python reproduce.py
```

Python dependencies are pinned in `requirements.txt`: mpmath 1.3.0, SymPy
1.14.0, NumPy 2.2.6, SciPy 1.15.3, python-flint 0.8.0. The broader suite is
`.venv/bin/python -m unittest -v`; it is optional for a focused human reading,
not a substitute for the proofs. No finite-density fitted curve certifies CO's
complete asymptotic or the universal positive estimates.

### Model sign: replay is not regeneration

```sh
.venv/bin/python curved4_focal_certificate.py --head-checks
.venv/bin/python curved4_focal_certificate.py --replay certificates/curved4-focal-model.json
# Optional full independent regeneration, one local worker by default:
.venv/bin/python curved4_focal_certificate.py --generate /tmp/curved4-focal-model.json --workers 1
```

Replay trusts saved nodal evidence. Full regeneration recomputes the 2,527
Arb enclosures; the source uses 192-bit arithmetic and 25 rational head checks.
Both still rely on the analytic inequalities in CC. The resulting sign bound
is for **I only**, not an independent interval implementation, physical source
coefficient, complete-action numerical certificate or Lean proof. This task
runs replay/selected-node tests, not full regeneration; earlier full-run
receipts remain historical evidence at their stated heads.

### Formal layer: a separate, scoped audit

Read [the pinned Lean setup](https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/formal/README.md#reproduce)
before installing anything. Use the committed toolchain/manifest and targeted
mathlib cache list there; avoid fetching the entire cache. Then:

```sh
cd formal
./check.sh
```

The full local gate builds, rechecks **every local Lean source**, treats warnings
as errors, enforces the transitive-axiom rule, then runs the aggregate audit.
Default two workers; check memory/swap headroom before changing it. Incremental
changed-source checks and GitHub CI do not replace it. This package changes no
Lean/checker/dependency/build inputs and claims **no fresh full Lean audit**.
Running that gate still would not certify CO/FLAT/SW/C2's unencoded arguments.
The earlier integrated thin-torus receipt reports 343 sources and 3,485 public
theorems/all public definitions; those historical counts are not a claim about
new manuscript verification.

### Optional tiny public-data check, not a scientific fit

```sh
curl --fail --max-time 30 \
  https://lambda.gsfc.nasa.gov/data/cobe/firas/monopole_spec/firas_monopole_spec_v1.txt \
  -o /tmp/firas-monopole.txt
python3 research/estimate_signals.py --firas /tmp/firas-monopole.txt
```

The manifest identifies the checked 2,388-byte table. Output should report
43 bins and peak-bin error about 46.9 ppm. This checks units and availability,
not inter-bin covariance, foreground treatment or a new diffusion constraint.
No bulk event/strain/light-curve download is required.

## Presentation validation and safe preview

The static review page uses the existing `site/site.css` design tokens, has a
skip link, labeled reading path, text status labels, native HTML equations
and a clearly labeled **illustration, not proof**. No JavaScript, WebGL, CDN
math renderer or font download is required to read it. Its print layout starts
with the one-page account. The older proof-spine page retains its source-pinned
teaching scope and links to this current package rather than silently updating
historical theorem claims.

A local-only preview can be run with
`python3 -m http.server 8765 --bind 127.0.0.1 --directory site`.
It is not deployment. Check desktop/mobile, light/dark, keyboard navigation,
no-JavaScript, reduced motion and print. New Markdown equations must be inspected
with GitHub's **live browser-side renderer**, not just its Markdown API.

If Playwright and its Chromium runtime are already available, the reproducible
local browser check is:

```sh
# In another terminal while the loopback server above is running:
node scripts/check-research-browser.mjs http://127.0.0.1:8765 /tmp/cse-review
```

`PLAYWRIGHT_MODULE` can name an absolute `playwright/index.mjs` path instead of
a project install. The script refuses non-loopback URLs, disables page scripts,
checks mobile/light/dark/keyboard navigation and print fit, and writes screenshots,
a PDF and a JSON receipt locally. These are presentation checks, not a formal
accessibility certification. Minimal hosts need Chromium's shared libraries and
math-capable fonts for the separate GitHub preview; a missing glyph is not a
successful visual check. [Validation receipt](validation.md) records actual results.

No workflow, production branch, image publication, release tag or live site is
changed by preparing this artifact. No manuscript submission or outreach is
authorized or recorded.
