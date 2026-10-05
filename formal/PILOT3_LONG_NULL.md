# Actual smooth 3D long density and signed cancellation (#125)

## Scope

This package formalizes the three-dimensional long producer of
[the conventional #78 argument](../notes/dimension-long-null.md), using exactly
merged #115's `SmoothPilot3`, physical dimension three as `DimensionSpacetime 2`,
the existing `pilot3Overlap`, and the unchanged `pilot3Action` /
`dimensionWeightedAction 2` constants. No geometric admissibility field,
region, intrinsic target, action, kernel or Poisson law is changed.

`SmoothPilot3.tendsto_longAction` proves the **unconditional normalized signed
long limit for every fixed positive cutoff**. The actual density, its signed
transport and analytic premises are derived, not postulated. This is not the
short producer (#126), final deterministic/expected assembly (#80), a new
expectation bridge, shrinking-cutoff uniformity, a full-action rate, an
all-dimensional extension, or sample-wise convergence. Independent human
mathematical review remains separate and outstanding. The subsequent
[#80 assembly](PILOT3_LIMIT.md) combines this producer with #126's actual
short theorem and then transfers the full limit through the separate bridge.

## Exact shared split and producer signatures

All names below are in namespace `BoundaryDraft`. Implicit `h f` have type
`Pilot3Space → ℝ`; `hf` has type `SmoothPilot3 h f`. These are signatures of
compiled declarations; their implementations live in the producer modules.
The integrated validation receipt is recorded below.

```lean
def pilot3LongFuture (δ : ℝ) : Set Pilot3Spacetime :=
  {z | z ∈ dimensionCausalFuture 0 ∧ δ ≤ z.1 + ‖z.2‖}

def pilot3ShortFuture (δ : ℝ) : Set Pilot3Spacetime :=
  dimensionCausalFuture 0 \ pilot3LongFuture δ

def pilot3ShortAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ
def pilot3LongAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ
def pilot3LongDensity (h f : Pilot3Space → ℝ) (δ σ : ℝ) : ℝ

theorem SmoothPilot3.action_eq_short_add_long
    (hf : SmoothPilot3 h f) (ρ δ : ℝ) :
  pilot3Action ρ h f = pilot3ShortAction ρ δ h f + pilot3LongAction ρ δ h f

theorem SmoothPilot3.longAction_eq_density
    (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
  pilot3LongAction ρ δ h f =
    -(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ *
      ∫ σ : ℝ, dimensionKernel 3
        (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
          pilot3LongDensity h f δ σ

theorem SmoothPilot3.longDensity_linear_quadratic_bound
    (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
  ∃ b0 b1 C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ σ ∈ Ioc 0 ε,
    |pilot3LongDensity h f δ σ - (b0 + b1 * σ)| ≤ C * σ ^ 2

theorem SmoothPilot3.longDensity_right_linear_jet
    (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
  ∃ b0 b1 : ℝ,
    (fun σ => pilot3LongDensity h f δ σ - (b0 + b1 * σ))
      =o[𝓝[>] 0] (fun σ => σ ^ (3 / 2 : ℝ))

theorem SmoothPilot3.tendsto_longAction
    (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
  Tendsto (fun ρ : ℝ => pilot3LongAction ρ δ h f) atTop (𝓝 0)
```

Short is exactly `v < δ`; cutoff equality belongs to long. The point volume
occurs **once, in short**. The long coefficient is negative and retains both
powers of density. Every source component and every causal partner stays in
the original region indicator; no componentwise bilocal additivity is used.

#125 owns these shared split/coordinate definitions. Early compiled split and
density signatures were published in both [#125](https://github.com/q5m-ai/causal-set-emergence/issues/125#issuecomment-5980371162)
and [#126](https://github.com/q5m-ai/causal-set-emergence/issues/126#issuecomment-5980371315).
The short producer may select any sufficiently small **fixed** positive cutoff;
the long theorem accepts it with no additional smallness assumption. After
integration of the sibling producer, #80 must validate the exact combined Lean
tree before assembling either full-action goal and then applying the separately
proved expectation identity.

## Construction and proof architecture

| Module | Derived result |
| --- | --- |
| `Pilot3Displacement` | Canonical overlap measurability, bounded compact support and continuous-weight integrability; actual endpoint/displacement shear; complete signed causal-pair identity and exact short/long action split |
| `Pilot3LongCoordinates` | Ordinary circle measure with mass `2 * Real.pi`; spatial polar exponent one; actual nonnegative null-coordinate transport with `pilot3NullJacobian σ v = (1 - σ / v ^ 2) / 4` |
| `Pilot3LongDensity` | Actual density from the canonical overlap; negative-side zero extension, pointwise finiteness including zero, global bound, compact support and integrability; measure pushforward and signed transport |
| `Pilot3LongGeometry` | Common primitive monotone-hinge hypotheses from the checked old-active tube, endpoint margins and finite length support; actual product derivatives and uniform compact bounds |
| `Pilot3LongFibre` | Pointwise gap-fibre identity including sigma zero; nonnegative Tonelli before real transport; measurable and absolutely integrable fibres on the full circle/source product |
| `Pilot3LongNull` | Coefficient measurability by fixed probes, coefficient integrability, dominated averaging, uniform quadratic error for the linear jet, real-order remainder, and unconditional signed cancellation |

The density is the real value of `pilot3LongDensityENN`, the nonnegative
circle/length integral of `pilot3ProperTimeOverlap`. Its exact domain is
`0 ≤ σ ≤ v^2` and `δ ≤ v`, equivalently `v ≥ max δ (Real.sqrt σ)` for
nonnegative sigma. The source overlap is defined by the original region
indicator before its positive-part gap formula is inserted. Only the scalar
time/radius change of variables is reused from `OverlapCoordinates`; its
four-dimensional angular or radial factors are **not** reused.

`lintegral_pilot3LongFuture_properTime` applies to arbitrary measurable
nonnegative spacetime observables, without radial symmetry. Pointwise finite
bounds then permit conversion to real integrals. `integrable_overlap_weight`
and `integrable_longDensity_weight` establish absolute integrability before
signed transport or polynomial subtraction. Only proved Lebesgue-null endpoints
are removed when passing to `Ioi 0`; null displacements and exact cutoff
contacts remain in the underlying definitions and pointwise identities.

### Contact layer and averaging

`Pilot3LongGeometry.exists_hypotheses` puts all constants before both source
and direction quantifiers. Nonnegative old gaps force both endpoints into the
checked compact positive-height tubes. Perturbed endpoints remain there even
when their new gaps have turned negative. Actual smooth future germs and
compactness bound the first and second derivatives of the **full product**
with the three-dimensional Jacobian. No derivative of a clipped height at the
joint or nonzero interior height gradient is required.

The geometry-independent `MonotoneHinge` proof handles inactive fibres, exact
cutoff contacts and strictly active roots separately. Its lost-layer integral
bound covers the **whole** old interval when the perturbed fibre closes
completely. The moving-contact quadratic coefficient is retained. Only its
pointwise Peano proof shrinks the neighbourhood with root-to-cutoff distance;
the normalized remainder bound uses one common positive width.

The averaging proof restricts the parameter measure to the full circle times
a derived compact positive-height source tube. All small right fibres vanish
off it. Fixed positive difference quotients establish coefficient measurability;
three finite probes and the common remainder bound establish integrability.
Dominated convergence yields `longDensity_right_quadratic_jet`. Subtracting its
quadratic coefficient gives the displayed **uniform quadratic error for the
averaged linear jet**, then the real-order `3 / 2` little-o needed by
`dimensionKernel_transverse_cancellation 3`. There is no inference of uniform
quadratic fibre little-o from pointwise expansions, contact-nullity assumption,
or measurable selection of roots.

## Acceptance and regression map

| #125 requirement | Checked implementation |
| --- | --- |
| Actual canonical density and complete signed disintegration | `Pilot3Displacement`, `Pilot3LongCoordinates`, `Pilot3LongDensity`; expanded finite-density regression |
| Measurability, finiteness, compact bounds and Fubini/change of variables | Nonnegative transport, pointwise finiteness, measure pushforward, absolute-integrability and fibre theorems |
| Actual averaged jet including the entire lost layer | Geometric `MonotoneHinge.Hypotheses`, common normalized bound, finite-probe integrability and dominated average; `longDensity_linear_quadratic_bound` |
| Unconditional normalized signed limit, compatible with short | `tendsto_longAction`, quantified over every positive fixed cutoff; original physical constants and unchanged cancellation theorem |
| Exact interfaces and standalone edge cases | Signatures above and `Pilot3LongNullRegression.lean` |
| Full local integrated verification | Receipt below; independent review and future sibling integration are separate |

`Pilot3LongNullRegression.lean` imports the producer directly and independently
expands its physical normalization, signed finite-density equality and limit.
It checks the circle mass, null and zero-radius Jacobians, equality-long cutoff,
point allocation, actual density bounds and real-order remainder. Geometric
instances retain the genuinely curved ball/sine future and its nonzero second
derivative, the nonempty region, positive-height critical center, both
components of the disconnected member, the annular critical set and the empty
member. The planar ball supplies exact all-direction critical-center contacts,
roots approaching the **same fixed cutoff**, and a whole old fibre that becomes
zero after perturbation. These regressions test the actual geometry, not a
postulated contact model or Taylor polynomial.

Existing `test_dimension_long_null.py` and symbolic/numerical controls remain
useful diagnostics; their conventional 5D/6D claims are not promoted to Lean
results by this 3D port. The historical #78 note remains a written delivery.

## Validation receipt and reproduction

Lean-source commit: `eaa3785dee08cfdbbd3ea7802d2182c2536c7983`, based on
`c74801692a65f58be3f8e3caf7e0ccf1824946a1` (merged #120 plus unrelated #127).
Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are unchanged. No dependency or checker input is modified.

The incremental developer check **passed**, as did the required full local
integrated `LEAN_NUM_THREADS=2 ./check.sh`, using the default two workers.
It built and checked all 259 local Lean sources: 258 warning-as-error
source/transitive-axiom rechecks, followed by the aggregate `Audit.lean`.
The aggregate audited **2,710 public theorems and all public definitions**,
allowing only `propext`, `Quot.sound` and `Classical.choice`. The full gate
exited zero in **2:05:50**, with peak single-process RSS **2,921,844 KiB**
(not total concurrent memory). CI does not replace this local gate.

After that audit, merge `3c665e7bb5be28496d9c161dc6551d83f0e5b209`
integrated `86428214e63d1e7ff8830c4300770a8be9940882` (unrelated website
PR #124). Its entire committed `formal/` tree is byte-identical to the
audited commit (`93e0b4cce44bdbd4dd8a4f9a992066e58d9fcaf5`). Subsequent
task changes are Markdown-only; no Lean/checker/dependency/build input changed.
The repeated lightweight checks passed on the combined tree: **268 Python
tests**, symbolic checks, numerical reproduction, Markdown lint and its
**20 tests**, site syntax checks and **6 proof-explorer model tests**.
The exact final documentation-only head is recorded in the PR receipt.

```sh
cd formal
./check.sh --incremental --base origin/main # developer feedback only
./check.sh                                # required full local gate
cd ..
.venv/bin/python -m unittest -v
.venv/bin/python check_symbolic.py
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
node --check site/home-3d.js
node --check site/order-fraction-worker.js
```

Numerical dependencies use the unchanged `requirements.txt` under Python 3.12.
No runtime handoff, service restart, deployment, merge or release is needed or
authorized for this proof package. No new rendered math expressions are added
to the Markdown; theorem signatures and normalization examples remain code.
