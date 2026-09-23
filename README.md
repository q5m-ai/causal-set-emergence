# Causal Set Emergence

Research into how continuum spacetime geometry, gravitational action, and
possibly dynamical laws can emerge from discrete causal order.

This repository now has two deliberately separated layers:

1. **A rigorous continuum-limit proof program** for boundary and joint terms in
   the four-dimensional Benincasa–Dowker–Glaser (BDG) causal-set action.
2. **An exploratory emergence program** collecting conceptual notes,
   visualizations, and research questions about causal growth, quantum
   histories, and automaton-like dynamics.

The first layer contains mathematical claims with explicit verification status.
The second is a research agenda, not an assertion that an automaton model or a
complete causal-set dynamics has been found.

> **Research status:** private, unpublished, and not peer reviewed. Formal
> verification checks the encoded statements; it does not establish novelty,
> physical applicability, or assumptions that have not yet been formalized.

## Why “emergence”?

A causal set begins with very little: discrete elements, causal order, and local
finiteness. A successful theory must explain how familiar continuum structures
appear at larger scales—including manifold structure, topology, Lorentzian
metric, dimension, locality, and the geometric field described as gravity in
general relativity.

The current proofs study one controlled part of that bridge. Given causal sets
obtained from increasingly dense Poisson sprinklings into specified continuum
regions, does the discrete BDG action recover the expected continuum geometric
term? This is a necessary consistency test, but it runs from a known continuum
target toward its discrete approximation. It does **not** yet derive spacetime
or gravity from unconstrained microscopic dynamics.

The longer-term question is complementary: can covariant causal growth or
rewriting rules make manifold-like causal sets and their effective physics
emerge without assuming a background lattice, global clock, or preferred
frame?

## Program 1 — BDG continuum limits

[The analytic proof draft](notes/first-attempt.md) studies the flat-space
specialization of Conjecture 1′ in Dowker–Liu–Lloyd-Jones:

```math
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_J\coth\theta\,dA,
 \qquad
 \mathcal A_\rho=\frac{l_p^2}{\hbar}\,\mathbb E S^{(4)}_\rho.
```

In **3+1-dimensional Minkowski space**, the draft gives arguments for these
restricted classes, pending independent mathematical review:

1. **One-null-tip regions**, including a causal diamond with `T>0` cut by
   the null plane `t-z=-a`, retaining `t-z>-a`, with `0<a<T`. The limiting
   normalized mean action is `π a (2T-a)`, equal to the joint area.
2. **Spacelike graph caps with a planar future boundary**, under the stated
   regularity, strict-spacelikeness, and transversality assumptions. The limit
   is `∫∂Ω 1/|∇h| dA = ∫J coth(θ) dA`.
3. **A connected variable-angle family:** unequal-axis ellipsoidal graph caps,
   with explicit limit `2π b₁b₂b₃/a`.

The argument performs the complete future-point integral before taking the
limit. This avoids an unjustified coordinate-local approximation for nearly
null pairs, which can have small interval volume despite large coordinate
separation. The graph-cap argument then uses a signed approximate identity and
the coarea formula.

### Machine-checked boundary

[The Lean layer](formal/README.md) uses pinned Lean 4.19.0 and mathlib. It now
proves the concrete kernel normalization and tails, exact four-dimensional
admissible graph-cap and concrete null-cap action reductions, explicit ellipsoid
height-integration formulae, and both
**deterministic continuum limits**:

```text
ellipsoidLimitGoal : EllipsoidLimitGoal
nullCapLimitGoal   : NullCapLimitGoal
```

All public theorems and definitions pass a transitive axiom audit permitting
only Lean’s standard foundations. The ellipsoid proof retains the whole signed kernel,
including its negative tail; the null proof derives the exact causal-interval
cancellation and normalized Gaussian concentration.

The **concrete ellipsoid geometric interpretation** is also checked separately:
its joint is a smooth regular level with nonzero Euclidean gradient, its angle
lies on the strict positive branch with `coth θ = 1 / ‖∇h‖`, and its variable-angle
surface integral equals `2π (∏ bᵢ) / a`. The surface measure uses a global
sphere-to-ellipsoid parameterization with a checked tangential Jacobian. Unequal
axes give distinct weights on one connected joint; `(a,b) = (1/4, ![1,2,3])`
has weights `2` and `6` at two axis endpoints and integral `48π`.

The **general graph-cap exact reduction** is now checked at every positive
density: `AdmissibleGraphCap.graphReduction` proves the unchanged
`GraphReductionGoal h` from `continuumMean`. Bounded positivity and strict
Euclidean Lipschitz control of `max 0 ∘ h` suffice for complete future slices,
causal convexity, compact domination, and vertical Fubini. The API separately
records C³ regularity near the closed positive region and a nonzero differential
only on its zero-level boundary; positive-height critical points remain allowed.
The original ellipsoids instantiate it without stronger hypotheses. A quartic
height profile also instantiates it and has a checked interior critical point.
`GraphCollar.lean` additionally proves that the Euclidean joint is compact and
measurable, and that some uniform positive-height band has no critical points.
Each point of this band has an ambient C³ regular neighborhood and a local
height-flattening chart. `GraphAngle.lean` derives the normals, strict slope
bound, and positive-branch angle identity for every admissible cap.
`GraphSurface.lean` defines a Euclidean Hausdorff surface target, proves its
finiteness and both boundary weights' absolute integrability, and equates their
integrals. `HausdorffGraph.lean` proves the local two-sided Euclidean
Hausdorff comparison of a C¹ graph with its tangent image.
`HausdorffPlane.lean` proves the covering half of planar normalization and
that Lebesgue-null planar sets are Hausdorff-null. The reverse planar inequality
and the identification with parametric area are still unproved.
`GraphTail.lean` proves that every fixed positive-height remainder vanishes
without coarea. The quartic regression retains its interior critical point.

Still open in the formal program:

- the surface-area normalization/coarea theorem and general graph-cap limit
  identifying the boundary integral with `continuumMean`;
- arbitrary null boundaries and the induced null-joint area interpretation;
- the Poisson-sprinkling expectation bridge.

The null result starts from the unchanged four-dimensional `continuumMean` and
proves the exact logarithmic weight, support, endpoint, absolute integrability,
and density limit under exactly `0 < a < T`. It does not formalize the
Poisson-expectation bridge or identify the algebraic `nullJointArea` with a
general induced-joint theorem.

Accordingly, this is not yet a checked proof of the unrestricted conjecture or
of convergence for individual random sprinklings. See
[tracking issue #1](https://github.com/q5m-ai/causal-set-emergence/issues/1).

## Program 2 — dynamics and automaton-like growth

The exploratory question is whether causal-set dynamics can be represented as
an asynchronous, label-independent growth or graph-rewriting system:

```text
discrete event + causal dependencies + covariant update law
                         ↓
       histories with emergent geometry and physics
```

The Game of Life is a useful intuition for emergence from simple rules, but not
a direct model. Ordinary cellular automata assume a spatial lattice, global
clock, simultaneous updates, and fixed local neighborhood. Those assumptions
would build in structures that causal set theory is meant to explain.

A viable causal analogue would need to preserve partial order and local
finiteness, avoid physical dependence on birth labels, support Lorentzian
rather than lattice locality, and ultimately admit quantum amplitudes or a
quantum measure over histories. One possible bridge to Program 1 is to ask
whether the BDG action can weight legal histories through an amplitude such as
`exp(iS)`.

This direction currently consists of questions and comparisons—not a proposed
fundamental rule. See:

- [Emergence and dynamics: current learnings and roadmap](notes/emergence-roadmap.md)
- [Viewing notes from the Fay Dowker / Curt Jaimungal conversation](notes/fay-dowker-interview-notes.md)
- [Discussion #12: order-invariant automata](https://github.com/q5m-ai/causal-set-emergence/discussions/12)

## Interactive explainer

[`site/index.html`](site/index.html) is a build-free visual introduction
to:

- discrete events and causal partial order;
- manifold, topology, and metric as emergent continuum concepts;
- causal diamonds, links, light cones, and Lorentzian nonlocality;
- a toy observer represented as a causal process across alternative histories;
- canonical, path-integral, and stochastic quantization;
- the continuum-limit calculation studied in this repository.

Open it directly, or serve only the site directory:

```sh
python3 -m http.server 8000 --directory site
```

Then visit <http://localhost:8000/>.

## Evidence and claim discipline

| Label | Meaning here |
|---|---|
| **Exploratory** | A question, analogy, or proposed direction; not a result |
| **Drafted** | A written analytic argument awaiting independent review |
| **Numerically checked** | Reproducible finite-density or symbolic evidence |
| **Machine checked** | The stated Lean declaration compiles and passes the axiom audit |
| **Established** | Reserved for independently reviewed or published work |

Distinct proof programs should remain independently auditable. A deeper result
may supersede an earlier argument without erasing its provenance. Numerical
agreement and visualization never substitute for proof, and machine checking
never substitutes for validating that the formal statement matches the intended
physics.

## Repository map

- `notes/first-attempt.md` — analytic boundary-limit proof draft and scope.
- `notes/references.md` — sources, attribution, and novelty boundaries.
- `notes/emergence-roadmap.md` — synthesis of conceptual learnings and next questions.
- `notes/fay-dowker-interview-notes.md` — provisional viewing notes and study prompts.
- `formal/` — Lean proofs, admissible graph-cap API, explicit targets, audit,
  and reproduction guide.
- `calculations.py`, `check_symbolic.py` — deterministic numerical and symbolic checks.
- `RESULTS.md` — reproducible finite-density tables.
- `site/` — standalone interactive explainer.

## Writing mathematics on GitHub

Follow [the math authoring guide](notes/github-math.md) for Markdown files,
issues, PRs, and comments. Use fenced `math` displays and dollar/backtick inline
math; GitHub does not render all LaTeX delimiters or macros. Run
`python3 check_markdown.py` before publishing and check the browser preview,
not just the Markdown API. Repository agent instructions are in
[`AGENTS.md`](AGENTS.md).

## Reproduce the computational checks

Requires Python 3.11+ and the pinned packages in `requirements.txt`:

```sh
uv venv .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python check_symbolic.py
.venv/bin/python check_markdown.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
```

Without `uv`, create a standard virtual environment and install from
`requirements.txt`. Lean reproduction instructions and the exact checked
boundary live in [`formal/README.md`](formal/README.md).

Downloaded source articles, local environments, and build products are ignored.
No third-party article text is committed.
