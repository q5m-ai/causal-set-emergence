# Lean verification: first checked layer and explicit targets

**Status: partial formal verification, not a Lean proof of either main theorem.**

Lean **4.19.0** and mathlib **v4.19.0** are pinned. `lake-manifest.json` pins the
resolved dependency commits; mathlib is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The internal Lake package identifier `formal_checks` is only a build identifier;
the research project and GitHub repository remain unnamed.

## What actually compiles and is proved

`./check.sh` builds the library, checks local files with warnings treated as
errors, and audits the transitive axioms of **eight theorems**:

| File | Checked result | What it does **not** establish |
|---|---|---|
| `BoundaryDraft/Algebra.lean` | BDG coefficient factorization | The exponential-series interchange with an integral |
| same | Interval coefficient cancellation for every natural `n` | The Lorentzian interval moment formula itself |
| same | Plane-cap coefficient recurrence | The beta integral or differentiated series |
| same | Null joint area decomposition | That the two geometric patches have those areas |
| same | Uncut area specialization | The causal-diamond action limit |
| same | Squared angle-weight algebra | The geometric angle relation or positive square-root step |
| `BoundaryDraft/AnalyticCore.lean` | Signed rescaling limit | Integrability of the particular BDG kernel |
| same | Unit-mass specialization | Normalization of the particular BDG kernel |

The analytic theorem genuinely permits a **signed** kernel. In ordinary
notation it proves

\[
 \int G(u)B(\varepsilon u)\,d\mu(u)
 \longrightarrow B(0)\int G\,d\mu
 \quad(\varepsilon\to0),
\]

assuming `G` is integrable and `B` is globally bounded and continuous. There is
no assumption that `G ≥ 0`. The measure `μ` may be Lebesgue measure restricted
to the positive half-line. A bounded continuous extension of the collar
profile fits this theorem; the interior remainder of a general graph cap
still needs its separate tail estimate. We have **not** instantiated this
lemma with the concrete BDG kernel yet.

`Audit.lean` rejects any axiom dependency beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. The checked results contain no
`sorry`, `admit`, or custom axioms. This does not mean that the full research
argument has been checked: the missing theorems are not silently assumed.

## The actual main targets, not weakened substitutes

`BoundaryDraft/Specification.lean` defines:

- Four spacetime coordinates with **product Lebesgue measure**.
- The causal relation using the Minkowski quadratic form, explicitly, rather
  than confusing the coordinate function space's norm with a Lorentzian norm.
- The actual bilocal deterministic continuum mean action, `continuumMean`.
- The null-plane-truncated region and ellipsoidal graph-cap family.
- The concrete auxiliary integral and its second derivative defining the
  signed kernel.

For example, the first full target is expressed as:

```lean
def NullCapLimitGoal : Prop :=
  ∀ T a : ℝ, 0 < a → a < T →
    Tendsto (fun ρ => continuumMean ρ (nullCapRegion T a))
      atTop (𝓝 (nullJointArea T a))
```

The variable-angle family's full target is:

```lean
def EllipsoidLimitGoal : Prop :=
  ∀ (a : ℝ) (b : Fin 3 → ℝ), 0 < a → (∀ i, 2 * a < b i) →
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b)))
      atTop (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a))
```

These are **definitions of propositions, not proofs**. In particular, a build
succeeding only means Lean accepts their precise statements. It does not mean
that either proposition is true. `GraphReductionGoal`, `KernelMassGoal`, and
`KernelTailGoal` likewise record unsolved obligations without asserting them.

The continuum action is not defined to be its conjectured answer. Completing
these targets would therefore require the actual integral calculations.

## Remaining proof graph

1. **Probability bridge, separate milestone.** Define Poisson sprinkling,
   interval counts, and the discrete BDG action; derive the deterministic
   continuum formula. Until then, even a completed continuum target would
   rely on the paper's Poisson-counting identification.
2. **Causal geometry and measures.** Prove causal convexity, exact complete
   future slices, coordinate changes/Jacobians, and joint area formulae.
3. **Exact integral reductions.** Formalize the interval moments and the
   exponential series exchange; for graph caps, justify differentiation of
   the auxiliary integral and the vertical-fibre integral.
4. **Concrete kernel estimates.** Prove `KernelMassGoal`, `KernelTailGoal`,
   the density-scaling identity, and the differentiable asymptotic estimates.
   Algebra already checked is only one component of this work.
5. **Limit argument.** Instantiate the checked signed-kernel lemma on a collar
   and prove that the interior contribution tends to zero. For null-tip
   regions, prove the corresponding one-sided Gaussian concentration result.
6. **Geometry of the variable-angle answer.** Establish coarea on the regular
   boundary collar and identify its density with `coth θ`; alternatively
   close the explicit ellipsoid case first using its direct volume profile.
7. **Main theorem and audit.** Construct proof terms of the main goal
   propositions, audit their dependencies, and compare their assumptions
   line by line with the paper statements.

The fastest substantive next milestone is the **concrete one-dimensional
kernel normalization and tail bound**, then the explicit ellipsoid target.
The general graph-cap coarea and Lorentzian geometry are likely larger
formalization tasks. We do not assume all needed geometric infrastructure
already exists in mathlib.

## Reproduce

With Lean/elan installed and the pinned toolchain selected by `lean-toolchain`:

```sh
cd formal
# The committed manifest pins dependencies. Avoid fetching all of mathlib's
# cache; the modules below are sufficient for this first layer.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get \
  Mathlib.MeasureTheory.Integral.DominatedConvergence \
  Mathlib.MeasureTheory.Measure.Lebesgue.Basic \
  Mathlib.Analysis.Calculus.Deriv.Basic \
  Mathlib.Analysis.SpecialFunctions.Exp \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic \
  Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
./check.sh
```

The current workspace also has an ignored, task-local Lean distribution under
`.tools/`; `check.sh` detects it. No global toolchain configuration was changed.
Dependencies and build products under `.lake/`, and the local distribution,
are excluded from Git. Only the formal sources, configuration, and lockfile
are committed. No GitHub repository has been created or published.
