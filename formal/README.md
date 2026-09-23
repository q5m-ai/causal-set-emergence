# Lean verification: checked components and explicit targets

**Status: the deterministic ellipsoid continuum limit is proved in Lean.
The general boundary conjecture, angle interpretation, null-cap limit, and
Poisson-expectation bridge remain open.**

Lean **4.19.0** and mathlib **v4.19.0** are pinned. `lake-manifest.json` pins the
resolved dependency commits; mathlib is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

This is the checked layer for Program 1 of **Causal Set Emergence**. The Lake
package identifier remains `causal_set_gravity` because this program studies the
BDG gravitational action; renaming the research umbrella does not change its
mathematical scope. This directory contains the proved components and explicit
open targets.

## What actually compiles and is proved

`./check.sh` builds the library, discovers **every local Lean source** (excluding
`.lake/` and `.tools/`), and checks each with warnings treated as errors. Each
source is also rechecked in an isolated current module so all of its public
declarations receive a transitive axiom audit even when that source is not
imported by the library root. Finally, the aggregate audit inventories the
library's **97 public theorems** and public definitions. The library root imports
all kernel, ellipsoid geometry, four-dimensional reduction, and ellipsoid-limit
modules. `EllipsoidRegression.lean` additionally checks the original target,
volume endpoints, the critical height, a negative integrand, and the unequal-axis
example with limit `48π`.

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
| same | Exact finite-interval mass and signed first moment | Half-line mass or absolute first-moment integrability by itself |
| `BoundaryDraft/GaussianCancellation.lean` | Exact substitution and absolute Gaussian cancellation estimate | The sharper asymptotic expansion |
| `BoundaryDraft/KernelEstimates.lean` | Explicit absolute `O(u⁻³)` kernel bound; `KernelTailGoal`; vanishing-moment boundary estimate | Graph-cap geometry or its non-collar reduction |
| `BoundaryDraft/KernelHalfLine.lean` | Large-argument limits; absolute integrability and first moment; mass one; `KernelMassGoal`; signed first moment zero | The four-dimensional action reduction |
| same | Concrete positive-half-line signed-rescaling limit | Coarea or either main boundary-limit theorem |
| `BoundaryDraft/EllipsoidGeometry.lean` | Positive ellipsoid, measurability, boundedness, compact positive-part support, strict Euclidean Lipschitz estimate | Sublevel volumes or coarea |
| same | Complete future-cone slices and causal convexity under the original axis hypotheses | Arbitrary graph profiles |
| `BoundaryDraft/ConeIntegral.lean` | Exact radial action-density identity by a zero-endpoint primitive; finite-fibre FTC | A boundary limit |
| `BoundaryDraft/SpacetimeIntegration.lean` | Product-measure coordinate decomposition, Fubini, spatial polar integration, and translation of actual BDG integrals | The Poisson-expectation bridge |
| same | `ellipsoid_graphReduction` proves the unchanged `GraphReductionGoal (ellipsoidProfile a b)` | A boundary limit by itself |
| `BoundaryDraft/EllipsoidIntegration.lean` | Axis determinant, Euclidean superlevel volumes, and exact signed height-integration formula with absolute integrability | General coarea or Lorentzian joint geometry |
| `BoundaryDraft/EllipsoidLimit.lean` | Bounded continuous global weight, exact fixed-half-line rescaling, and `ellipsoidLimitGoal : EllipsoidLimitGoal` | A convergence rate, arbitrary graph caps, `NullCapLimitGoal`, or the Poisson bridge |

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
still needs its geometric reduction and use of the tail estimate. The theorem
`planeKernel_rescaling_limit` now instantiates this lemma with the concrete
BDG kernel and Lebesgue measure restricted to `Ioi 0`, using the proved
absolute integrability and mass one, not additional kernel hypotheses.
`EllipsoidLimit` now applies it to the actual globally extended ellipsoid
weight; no collar/remainder split or global C¹ hypothesis is needed.

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

These identities hold for finite \(H\); they alone do not justify passing to
infinity. That passage is now proved separately as follows, completing the
one-dimensional analytic milestone in
[issue #4](https://github.com/q5m-ai/causal-set-emergence/issues/4).
The exact reduction from `continuumMean` is also now proved for ellipsoids in
[issue #6](https://github.com/q5m-ai/causal-set-emergence/issues/6), as described below.
Neither result completes the boundary-limit program in
[issue #1](https://github.com/q5m-ai/causal-set-emergence/issues/1).

## Half-line estimates and normalization

The proof avoids differentiating the remainder of an asymptotic expansion.
Set \(a=(\pi/24)u^4\) and substitute \(t=1-v^2\) in the already-checked
fixed-interval formulas. The substitution is differentiated in the smooth
polynomial direction, so no derivative of a square root at zero is needed.
The two relevant polynomials are instances of

\[
 P_{b,d}(a,t)=b-(2b+3d)at^2+2da^2t^4.
\]

For \(a>0\) and \(b,d\ge0\), `gaussianCancellation_bound` proves

\[
 \left|\int_0^1\sqrt{1-t}\,P_{b,d}(a,t)e^{-at^2}\,dt\right|
 \le \frac{5b+11d}{2a}.
\]

Its proof uses an exact primitive for the constant-weight integral,
\((bt-dat^3)e^{-at^2}\), the bound \(|\sqrt{1-t}-1|\le t\), and an
explicit primitive for the resulting nonnegative absolute envelope. Thus the
estimate controls absolute values rather than merely signed cancellation.
Taking \((b,d)=(6,8)\) and \((2,0)\), respectively, gives for every \(u>0\)

\[
 |F''(u)|\le\frac{2832}{u^3},\qquad
 |uF'(u)-F(u)|\le\frac{240}{u},\qquad
 |G(u)|\le\frac{1416}{\pi\sqrt6\,u^3}.
\]

These loose constants suffice: continuity handles \([0,1]\), and comparison
with \(u^{-3}\) and \(u^{-2}\) proves integrability of \(G\) and \(u|G|\).
The theorem `kernelTailGoal` uses \(C=1416/(\pi\sqrt6)\) and \(R=1\).

For normalization, `planeAuxiliary_div_eq_integral` proves

\[
 \frac{F(u)}u=2\pi\int_0^\infty
   \sqrt{1-s/u^2}\,e^{-(\pi/24)s^2}\,ds.
\]

Here Lean's real square root is zero for negative inputs; the integrand
vanishes above \(u^2\). It is dominated by an integrable Gaussian. Dominated
convergence and the half-Gaussian integral yield \(F(u)/u\to2\pi\sqrt6\).
The second bound above then proves \(F'(u)\to2\pi\sqrt6\) and
\(uF'(u)-F(u)\to0\). Only after proving absolute integrability do we pass the
finite-interval identities to infinity, obtaining mass one and signed first
moment zero. `kernelMassGoal` proves the **unchanged** target, including its
absolute first-moment clause.

No additional hypotheses on the concrete kernel are introduced. The sharper
coefficient \(G(u)\sim-2\sqrt6/(\pi u^3)\), and the derivative remainders
through order three in the draft, are **not** claimed as Lean results.

## Exact ellipsoid action reduction

The checked theorem is:

```lean
theorem ellipsoid_graphReduction (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    GraphReductionGoal (ellipsoidProfile a b)
```

It proves equality at **every positive density**, not just asymptotically.
`continuumMean`, `graphCapRegion`, `ellipsoidProfile`, `bdgKernel`, `planeKernel`,
and the target proposition are unchanged. No future-slice, density-identity,
or reduction premise is introduced.

1. **Geometry.** Positivity is equivalent to `∑ (x i / b i)^2 < 1`.
   Continuity gives measurability; the positive set is contained in `Icc (-b) b`,
   and the positive part has compact support. For a smallest axis `m`, its
   global Euclidean Lipschitz constant is `κ = 2*a/m < 1`, including pairs
   outside the ellipsoid. The raw quadratic is not asserted to be Lipschitz.
   `spatialDistance_sq` identifies this Euclidean metric with the spatial
   quadratic form in `causalFuture`, rather than the coordinate supremum norm.
   The positive-part epigraph is a future set; `ellipsoid_complete_future`
   proves the exact cap/causal intersection, with null points and vertex
   retained, and `ellipsoid_causallyConvex` proves causal convexity.
2. **Analytic cancellation.** `coneRadialSlice_eq_radial` justifies `r = H*v`.
   With `k = (π/24)*ρ*H⁴`, `w = 1-v²`, `z = k*w²`, and
   `R₃ = 6-204z+288z²-64z³`, the primitive

   ```text
   M(v) = 2*v³*w*(-8*z²*(w+1) + 2*z*(15*w+14) - 15*w - 12)*exp(-z)
   ```

   vanishes at both endpoints and has derivative
   `v²*(w²*(R₃'-R₃)(z) + 48*P(z))*exp(-z)`.
   Compact-rectangle dominated differentiation and the FTC therefore give
   `Fρ''''(H) = -8πρ * coneRadialSlice ρ H`. Integrating from zero, retaining
   the checked `Fρ'''(0) = 8π`, proves the exact radial density identity.
   This replaces the previously unformalized exponential-series/beta exchange
   with a finite exact argument; algebraic recurrences alone are not used as
   an analytic justification.
3. **Measures and Fubini.** A measure-preserving equivalence splits `Fin 4 → ℝ`
   into time and three spatial coordinates. Another identifies spatial product
   Lebesgue measure with Euclidean volume. Polar integration uses the checked
   three-ball volume `4π/3`, giving the angular factor `4π`. Continuous
   integrands on explicit compact boxes supply absolute integrability before
   either Fubini interchange. Endpoint replacements use the atomlessness of
   Lebesgue measure. Thus `coneIntegral_eq_radial` identifies the actual
   four-dimensional cone integral, and `planeAuxiliaryThird_eq_coneIntegral`
   proves `Fρ'''(H)/(8π) = 1 - ρ*Qρ(H)` for every finite `H ≥ 0`.
4. **Original action.** Translation invariance and the complete-future theorem
   identify the inner integral in `continuumMean`. The exact spatial/vertical
   decomposition is `integral_ellipsoid_depth`. Finally the FTC and
   `Fρ''(0) = 0` give the existing `planeKernel ρ (h x)` along each fibre.

No strengthened geometric hypotheses were needed. This exact reduction is
reused, rather than assumed or redefined, in the ellipsoid-limit proof below.
The general admissible graph-cap theorem and null-cap reduction are not claimed.

## Explicit ellipsoid integration and continuum limit

`EllipsoidIntegration.lean` proves, for positive axes and `a > 0`,

\[
 |\{x:s<h(x)\}|=\frac{4\pi}{3}\Bigl(\prod_i b_i\Bigr)
   \sqrt{1-s/a}^{\,3},\qquad 0\le s\le a.
\]

At and above `s = a` the strict superlevel set is empty. The coordinate map
`x_i ↦ x_i/b_i` has diagonal determinant `∏ b_i⁻¹`; mathlib's Lebesgue
transformation law supplies the axis factor, and a measure-preserving
identification with Euclidean space supplies the three-ball volume. Neither
volume identity is an assumption. Spheres have zero spatial measure, so open
and closed radial domains give the same integrals, including radius zero.

For **every globally continuous real integrand** `f`, including `planeKernel ρ`,
`integral_ellipsoid_profile` proves the exact signed formula

\[
 \int_{h>0}f(h(x))\,dx
 =C\int_0^a\sqrt{1-s/a}\,f(s)\,ds,
 \qquad C=\frac{2\pi\prod_i b_i}{a}.
\]

Continuous integrands on the explicit compact spatial box are absolutely
integrable. The weighted finite-interval integrand is continuous, including
both endpoints. After diagonal and radial integration, the substitution is
proved in the **polynomial direction** `t = 1-r²`, followed by `s = a*t`.
There is no differentiation of the square root at the interior critical
height `s = a`, nor an assumption that this weight is globally C¹.

`EllipsoidLimit.lean` uses the global extension

\[
 B(s)=C\sqrt{\bigl(1-\max(0,s)/a\bigr)_+}.
\]

It is continuous, satisfies `|B(s)| ≤ |C|`, is constant for `s ≤ 0`, and
vanishes for `s ≥ a`. The exact height formula and checked
`ellipsoid_graphReduction` therefore give, at every positive density,

\[
 \operatorname{continuumMean}_\rho(M_h)
 =\int_0^\infty G(u)B(\varepsilon u)\,du,
 \qquad \varepsilon=\bigl(\sqrt{\sqrt\rho}\bigr)^{-1}.
\]

The half-line extension adds only zeros. The original weighted half-line
integral is absolutely integrable by compactness and its zero tail; the
rescaled integral is dominated by the checked integrable function `|C| |G|`.
`planeKernel_density_scaling` and positive linear substitution justify the
fixed-domain identity. Continuity of square root at zero and the reciprocal
limit prove `ε → 0` as `ρ → ∞`; positive density holds eventually. Finally
`planeKernel_rescaling_limit` gives `B(0) = C`, proving
`ellipsoidLimitGoal : EllipsoidLimitGoal` under the original hypotheses.
This retains the **entire signed kernel**, including its negative tail, and
controls the whole ellipsoid, not just a collar. No rate is asserted.

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

These `Goal` declarations are **definitions of propositions, not themselves
proofs**. The unchanged `EllipsoidLimitGoal` now has the proof term
`ellipsoidLimitGoal`; `NullCapLimitGoal` still does not. `GraphReductionGoal`
has a proof for the concrete ellipsoid family, `ellipsoid_graphReduction`, but
not for arbitrary profiles. The original `KernelMassGoal` and `KernelTailGoal`
also have proof terms, `kernelMassGoal` and `kernelTailGoal`. All are audited
transitively along with the rest of the library.

The continuum action is not defined to be its conjectured answer. The
ellipsoid proof starts from the actual four-dimensional integral, not a
reformulated target or an assumed geometric reduction.

## Remaining proof graph

1. **Probability bridge, separate milestone.** Define Poisson sprinkling,
   interval counts, and the discrete BDG action; derive the deterministic
   continuum formula. The proved deterministic ellipsoid limit does not by
   itself establish the paper's Poisson-counting identification.
2. **Causal geometry and measures.** Completed for the ellipsoid reduction:
   causal convexity, complete future slices, coordinate measures, and spatial
   polar integration. Joint area formulae and other region families remain open.
3. **Exact integral reductions.** Completed for ellipsoids: the concrete BDG
   cone/action-density identity and vertical-fibre reduction. The null-tip
   interval moments and their analytic kernel interchange remain open.
4. **Concrete kernel estimates: completed for the half-line milestone.**
   `KernelMassGoal`, `KernelTailGoal`, the required limits, and the concrete
   signed-rescaling theorem are proved. The sharper differentiable asymptotic
   expansion remains draft-level and is not needed for these proofs.
5. **Explicit ellipsoid limit: completed.** The exact superlevel volume and
   signed integration formula establish `EllipsoidLimitGoal` using the checked
   graph reduction and kernel limit. No extra geometric or analytic hypotheses
   are introduced. General collar geometry and its interior remainder, and
   null-tip Gaussian concentration, remain separate tasks.
6. **Geometry of the variable-angle answer: open.** Formalize the Lorentzian
   relation `coth θ = 1 / ‖∇h‖` and the joint-area interpretation. The direct
   ellipsoid volume proof does not establish these identities or general coarea.
7. **Remaining theorem and audits.** Construct a proof of `NullCapLimitGoal`
   and the general graph-cap theorem, with their hypotheses compared line by
   line against the draft. The deterministic ellipsoid target is already proved
   and audited; neither paper theorem in its full stated generality is checked.

The explicit ellipsoid deterministic milestone is complete. General graph-cap
coarea, Lorentzian joint geometry, null caps, and the probability bridge remain
separate tasks; we do not assume their infrastructure already exists in mathlib.

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
  Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts \
  Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral \
  Mathlib.Analysis.SpecialFunctions.ImproperIntegrals \
  Mathlib.Analysis.SpecialFunctions.Exp \
  Mathlib.Analysis.SpecialFunctions.ExpDeriv \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic \
  Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.Data.Fintype.Lattice \
  Mathlib.MeasureTheory.Integral.Prod \
  Mathlib.MeasureTheory.Constructions.HaarToSphere \
  Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls \
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
