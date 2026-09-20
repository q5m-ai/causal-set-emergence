# Causal Set Gravity

Research on continuum limits, boundary terms, and formal verification in
causal-set gravity. The repository is intentionally broader than one theorem:
each proof program gets its own stated hypotheses, evidence, and verification
status.

This is a **private research repository**. Nothing here is a peer-reviewed or
publicly released result.

## Proof program 1: modified BDG boundary conjecture

[Read the proof draft](notes/first-attempt.md).

In **3+1-dimensional Minkowski space**, the draft gives complete arguments for
these restricted classes, pending independent mathematical review:

1. **One-null-tip regions**, including a causal diamond of duration `T` cut by
   the null plane `t-z=-a`, retaining `t-z>-a`, with `0<a<T`. The limiting
   normalized mean action is `π a (2T-a)`, exactly the joint area.
2. **Spacelike graph caps with a planar future boundary**,
   `M_h = { (t,x): -h(x)<t<0 }`, with the regularity, strict spacelikeness, and
   transversality conditions in the proof. The limit is
   `∫∂Ω 1/|∇h| dA = ∫J coth(θ) dA`.
3. **Genuinely variable angle:** unequal-axis ellipsoidal graph caps have a
   single connected joint with nonconstant `θ`. The explicit limit is
   `2π b₁b₂b₃/a`, where `h=a(1-Σxᵢ²/bᵢ²)`.

Normalization: every action above is `l_p² E[S⁽⁴⁾_ρ]/ℏ`. These are results
about the expectation, not convergence of individual random sprinklings.

The key is to do the entire future-point integral **exactly** before taking a
limit. This avoids an unjustified short-distance approximation for nearly
null, widely separated pairs. The graph-cap proof then uses a signed
approximate identity of mass one and the coarea formula.

**Not established:** arbitrary pairs of curved boundary faces, other spacetime
dimensions, degenerate joints, variance control, or novelty relative to all
existing literature. The symbolic/numerical tests are consistency checks,
not a formal verification of the proofs.

## Proof-program organization

As the project grows, distinct arguments should remain independently auditable:

- `notes/`: proof drafts, assumptions, failed approaches, and references;
- `formal/`: Lean-checked components and explicitly unproved targets;
- numerical code and result tables: reproducible diagnostics, never substitutes
  for analytic proofs.

A deeper proof may supersede an earlier argument without erasing its provenance.
Claims must identify whether they are conjectural, drafted, independently
reviewed, or machine-checked.

## Lean status

[The Lean layer](formal/README.md) compiles with Lean 4.19.0 and pinned
mathlib. In addition to the original algebra and generic signed-kernel limits,
it proves the concrete plane kernel's density scaling, differentiation of its
auxiliary integral through order three, boundary constants, and exact
finite-interval mass and signed first-moment identities. All **26 supporting
theorems** pass an axiom audit permitting only Lean's standard foundations.

The full four-dimensional limit theorems, the kernel's half-line normalization
and tail estimates, the geometric reductions, and the Poisson-expectation bridge
are **not yet formalized as proofs**. In particular, finite-interval identities
do not prove absolute integrability or mass one on the half-line. This is
partial verification, not a machine-checked proof of either paper theorem;
[tracking issue #1](https://github.com/q5m-ai/causal-set-gravity/issues/1) remains open.

## Reproduce

Requires Python 3.11+ and the two pinned packages in `requirements.txt`.

```sh
uv venv .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
```

Without `uv`, use `python3 -m venv .venv` and
`.venv/bin/pip install -r requirements.txt` for the first two steps.

- [Proof and explicit remaining scope](notes/first-attempt.md)
- [Sources and attribution](notes/references.md)
- [Reproducible numerical tables](RESULTS.md)
- [Lean proofs, unproved targets, and verification plan](formal/README.md)
- `check_symbolic.py`: seven groups of exact algebra checks, including
  all-orders kernel coefficient identities.
- `test_calculations.py`: 13 tests, including independent integral
  representations, signs, normalization, scaling, and convergence examples.
- `calculations.py`: high-precision deterministic integral evaluators.
- `test_formal_check.py`: five checker-orchestration regression tests; these
  use a fake Lake and do **not** replace running `formal/check.sh`.

Downloaded source articles and local environments are ignored by Git. No
third-party article text is included in the committed draft.
