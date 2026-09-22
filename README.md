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

\[
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_J\coth\theta\,dA,
 \qquad
 \mathcal A_\rho=\frac{l_p^2}{\hbar}\,\mathbb E S^{(4)}_\rho.
\]

In **3+1-dimensional Minkowski space**, the draft gives arguments for these
restricted classes, pending independent mathematical review:

1. **One-null-tip regions**, including a causal diamond of duration `T` cut by
   the null plane `t-z=-a`. The limiting normalized mean action is
   `π a (2T-a)`, equal to the joint area.
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
ellipsoid action reduction, explicit ellipsoid integration, and the
**deterministic ellipsoid continuum limit**:

```text
ellipsoidLimitGoal : EllipsoidLimitGoal
```

All **97 public theorems** pass a transitive axiom audit permitting only Lean’s
standard foundations. The whole signed kernel is retained, including its
negative tail.

Still open in the formal program:

- `NullCapLimitGoal`;
- the general admissible graph-cap theorem;
- the Lorentzian angle and joint-area interpretation;
- the Poisson-sprinkling expectation bridge.

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

[`site/index.html`](site/index.html) is a dependency-free visual introduction
to:

- discrete events and causal partial order;
- manifold, topology, and metric as emergent continuum concepts;
- causal diamonds, links, light cones, and Lorentzian nonlocality;
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
- `formal/` — Lean proofs, explicit targets, audit, and reproduction guide.
- `calculations.py`, `check_symbolic.py` — deterministic numerical and symbolic checks.
- `RESULTS.md` — reproducible finite-density tables.
- `site/` — standalone interactive explainer.

## Reproduce the computational checks

Requires Python 3.11+ and the pinned packages in `requirements.txt`:

```sh
uv venv .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
```

Without `uv`, create a standard virtual environment and install from
`requirements.txt`. Lean reproduction instructions and the exact checked
boundary live in [`formal/README.md`](formal/README.md).

Downloaded source articles, local environments, and build products are ignored.
No third-party article text is committed.
