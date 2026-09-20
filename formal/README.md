# Lean verification: checked components and explicit targets

**Status: partial formal verification, not a Lean proof of either main theorem.**

Lean **4.19.0** and mathlib **v4.19.0** are pinned. `lake-manifest.json` pins the
resolved dependency commits; mathlib is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The Lake package identifier is `causal_set_gravity`; this directory contains
the checked layer and open formal targets for the current proof program.

## What actually compiles and is proved

`./check.sh` builds the library, discovers **every local Lean source** (excluding
`.lake/` and `.tools/`), and checks each with warnings treated as errors. Each
source is also rechecked in an isolated current module so all of its public
declarations receive a transitive axiom audit even when that source is not
imported by the library root. Finally, the aggregate audit inventories the
library's **26 public theorems** and public definitions. The library root imports
both new kernel modules.

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
| `BoundaryDraft/KernelScaling.lean` | Auxiliary-integral scaling; fourth-power and positive-density kernel scaling | Mass one or tail estimates |
| `BoundaryDraft/KernelDerivatives.lean` | Differentiation under the auxiliary integral through order three | The BDG future-cone/action-density identity |
| same | Kernel differentiability and continuity; boundary values | Estimates at infinity |
| same | Exact finite-interval mass and signed first moment | Half-line mass or absolute first-moment integrability |

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

`Audit.lean` discovers the public declarations in the imported `BoundaryDraft`
namespace rather than maintaining a theorem allowlist. In addition, the
per-source audit in `check.sh` covers public declarations in unimported files
and other namespaces. Both reject any transitive axiom dependency beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`. Compiler-generated
implementation artifacts are not audit roots; private helper dependencies are
still audited transitively. The checked results contain no `sorry`, `admit`, or
custom axioms. This does not mean that the full research argument has been
checked: the missing theorems are not silently assumed.

## Concrete kernel: what the new proofs establish

`planeKernel_density_scaling` proves equation (14) directly from the defining
integral, for **every** positive density and every real height:

\[
 G_\rho(H)=sG_1(sH),\qquad s=\sqrt{\sqrt\rho}=\varepsilon^{-1}.
\]

The radial change of variables is proved first, including oriented integrals
for negative heights. The nonzero linear-chain-rule step is valid even for
Lean's total derivative; it does not hide a differentiability assumption.
The separate `KernelDerivatives` module then proves actual `HasDerivAt`
statements, not just equalities involving a possibly undefined derivative.

For \(z=(\pi/24)\rho H^4(1-v^2)^2\), the fixed-interval representation is

\[
 F_\rho^{(j)}(H)=4\pi H^{3-j}\int_0^1 v^2 R_j(z)e^{-z}\,dv,
 \quad j=0,1,2,3,
\]

where

\[
 R_0=1,\quad R_1=3-4z,\quad R_2=6-36z+16z^2,\quad
 R_3=6-204z+288z^2-64z^3.
\]

Joint continuity on a compact parameter rectangle supplies an integrable
uniform bound for each differentiation. This proves
\(F_\rho'(0)=F_\rho''(0)=G_\rho(0)=0\) and
\(F_\rho'''(0)=8\pi\), with no positivity assumption on the kernel.
Writing \(c_\rho=\sqrt\rho/(2\pi\sqrt6)\), the fundamental theorem of
calculus then proves

\[
 \int_0^H G_\rho(u)\,du=c_\rho F_\rho'(H),\qquad
 \int_0^H uG_\rho(u)\,du=c_\rho\bigl(HF_\rho'(H)-F_\rho(H)\bigr).
\]

These identities hold for finite \(H\). They do **not** justify passing to
infinity or prove `KernelMassGoal` or `KernelTailGoal`. The exact reduction
from `continuumMean` remains unproved too. This is partial progress on
[issue #1](https://github.com/q5m-ai/causal-set-gravity/issues/1), not its completion.

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
3. **Exact integral reductions.** Formalize the interval moments, exponential
   series exchange, and graph-cap action-density and vertical-fibre reductions.
   Differentiation of the auxiliary integral itself is now checked; its
   identification with the four-dimensional action density is not.
4. **Concrete kernel estimates.** Prove `KernelMassGoal`, `KernelTailGoal`,
   and the differentiable asymptotic estimates. Scaling and finite-interval
   calculus are now checked, but no half-line estimate is silently assumed.
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
# cache; the modules below are sufficient for the checked layer.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get \
  Mathlib.MeasureTheory.Integral.DominatedConvergence \
  Mathlib.MeasureTheory.Measure.Lebesgue.Basic \
  Mathlib.Analysis.Calculus.Deriv.Basic \
  Mathlib.Analysis.Calculus.Deriv.Comp \
  Mathlib.Analysis.Calculus.Deriv.Mul \
  Mathlib.Analysis.Calculus.Deriv.Pow \
  Mathlib.Analysis.Calculus.ParametricIntervalIntegral \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus \
  Mathlib.Analysis.SpecialFunctions.Exp \
  Mathlib.Analysis.SpecialFunctions.ExpDeriv \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic \
  Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
./check.sh
```

The current workspace also has an ignored, task-local Lean distribution under
`.tools/`; `check.sh` detects it. No global toolchain configuration was changed.
Dependencies and build products under `.lake/`, and the local distribution,
are excluded from Git. Only the formal sources, configuration, and lockfile
are committed. The enclosing repository is private; no paper or result has
been publicly released.
