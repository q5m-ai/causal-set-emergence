# Untitled research draft

A first attempt at the modified Benincasa–Dowker boundary conjecture.

**Naming deferred.** This is a local Git repository only. No GitHub repository
has been created, and nothing has been pushed or published. After a name is
chosen, the intended destination is a **private** repository in `q5m-ai`.

## First result

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

## Lean status

[The initial Lean layer](formal/README.md) compiles with Lean 4.19.0 and pinned
mathlib. It proves eight supporting theorems: six algebraic identities and two
signed-kernel convergence statements. An axiom audit permits only Lean's
standard foundations. The full four-dimensional limit theorems, the concrete
kernel estimates, the geometric reductions, and the Poisson-expectation bridge
are **not yet formalized as proofs**; their targets and remaining obligations
are explicit. This is partial verification, not a machine-checked proof of the
conjecture or of the two paper theorems.

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

Downloaded source articles and local environments are ignored by Git. No
third-party article text is included in the committed draft.
