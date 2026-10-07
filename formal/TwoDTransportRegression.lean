import BoundaryDraft.TwoDExamples
import BoundaryDraft.TwoDLine
import BoundaryDraft.TwoDShortDensity
import BoundaryDraft.TwoDLongJet
import BoundaryDraft.TwoDShortAngular

/-! Regression of actual 2D transport, overlap jets and endpoint coefficients.
These are not terms of `TwoDDeterministicGoal` or `TwoDExpectedGoal`. -/

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft.TwoDTransportRegression

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    frontier (twoDRegion h f) = twoDPast h f ∪ twoDFuture h f := hf.frontier_region

example (h f : TwoDSpace → ℝ) : twoDPast h f ∩ twoDFuture h f = twoDJoint h f :=
  SmoothTwoD.past_inter_future

/-- The canonical intersection volume, not an arbitrary overlap function. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (z : TwoDSpacetime)
    (hc : ‖z.2‖ ≤ z.1) :
    twoDOverlap h f z.1 z.2 = ∫ x, max 0 (twoDOverlapGap h f z x) := by
  rw [← hf.displacementOverlap_eq_actual z, hf.overlap_eq_gap z hc]

example : twoDDirectionMeasure = Measure.dirac twoDRight + Measure.dirac twoDLeft :=
  twoDDirectionMeasure_eq_dirac

example (σ v : ℝ) : twoDNullJacobian σ v = 1 / (2 * v) := rfl

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (ρ δ : ℝ) :
    twoDAction ρ h f = twoDShortAction ρ δ h f + twoDLongAction ρ δ h f :=
  hf.action_eq_short_add_long ρ δ

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (w : TwoDSpacetime → ℝ)
    (hw : Continuous w) :
    (∫ x in twoDRegion h f, ∫ y in twoDRegion h f ∩ dimensionCausalFuture x, w (y - x)) =
      ∫ z in dimensionCausalFuture 0, w z * twoDDisplacementOverlap h f z :=
  hf.integral_causalPair_eq_overlap w hw

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (δ : ℝ) (w : ℝ → ℝ)
    (hw : Continuous w) :
    (∫ z in twoDShortFuture δ, w (dimensionIntervalSq 0 z) * twoDDisplacementOverlap h f z) =
      ∫ σ : ℝ, w σ * twoDShortOverlapDensity h f δ σ :=
  integral_twoDShortOverlap hf δ w hw

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) {δ : ℝ} (hδ : 0 < δ)
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ z in twoDLongFuture δ, w (dimensionIntervalSq 0 z) * twoDDisplacementOverlap h f z) =
      ∫ σ : ℝ, w σ * twoDLongDensity h f δ σ :=
  hf.integral_longOverlap hδ w hw

/-- Absolute signed integrability does not assert pointwise finiteness at sigma zero. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (δ : ℝ) (w : ℝ → ℝ)
    (hw : Continuous w) : Integrable (fun σ => w σ * twoDShortOverlapDensity h f δ σ) :=
  integrable_twoDShortOverlapDensity_weight hf δ w hw

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 : ℝ, (fun σ => twoDLongDensity h f δ σ - (b0 + b1 * σ))
      =o[𝓝[>] 0] (fun σ => σ) := by
  simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using
    hf.longDensity_right_linear_jet hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ σ ∈ Ioc 0 ε,
      |twoDLongDensity twoDIntervalHeight twoDSineFuture δ σ - (b0 + b1 * σ)| ≤ C * σ ^ 2 :=
  twoDIntervalSine_admissible.longDensity_linear_quadratic_bound hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ σ ∈ Ioc 0 ε,
      |twoDLongDensity twoDIntervalHeight (fun _ => 0) δ σ - (b0 + b1 * σ)| ≤ C * σ ^ 2 :=
  twoDIntervalPlanar_admissible.longDensity_linear_quadratic_bound hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ σ ∈ Ioc 0 ε,
      |twoDLongDensity (fun _ => 0) (fun _ => 0) δ σ - (b0 + b1 * σ)| ≤ C * σ ^ 2 :=
  twoDEmpty_admissible.longDensity_linear_quadratic_bound hδ

example : 0 < twoDIntervalHeight 0 ∧ fderiv ℝ twoDIntervalHeight 0 = 0 :=
  twoDIntervalHeight_critical

/-- Derived complete interval geometry, with no connectedness premise. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) : Nonempty (TwoDIntervalFamily h) :=
  hf.exists_intervalFamily

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    twoDShortTimeCoefficient h - twoDShortSpaceCoefficient h f = twoDBoundaryIntegral h f :=
  hf.short_coefficients_eq_boundaryIntegral

/-- These are actual-overlap expansions, not assumed jets. -/
example : ∃ δ : ℝ, 0 < δ ∧ ∃ (R : TwoDSpacetime → ℝ) (T : ℝ),
    Measurable R ∧ TwoDShortRemainder.CubicBounds R δ T ∧
    ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
      twoDOverlap twoDIntervalHeight twoDSineFuture z.1 z.2 =
        twoDAbsoluteShortPolynomial twoDIntervalHeight twoDSineFuture z + R z :=
  twoDIntervalSine_admissible.exists_absoluteOverlap_remainder

example : ∃ δ : ℝ, 0 < δ ∧ ∃ (R : TwoDSpacetime → ℝ) (T : ℝ),
    Measurable R ∧ TwoDShortRemainder.CubicBounds R δ T ∧
    ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
      twoDOverlap twoDIntervalHeight (fun _ => 0) z.1 z.2 =
        twoDAbsoluteShortPolynomial twoDIntervalHeight (fun _ => 0) z + R z :=
  twoDIntervalPlanar_admissible.exists_absoluteOverlap_remainder

/-- The finite-collar construction also works when the whole joint is empty. -/
example : ∃ δ : ℝ, 0 < δ ∧ ∃ (R : TwoDSpacetime → ℝ) (T : ℝ),
    Measurable R ∧ TwoDShortRemainder.CubicBounds R δ T ∧
    ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
      twoDOverlap (fun _ => 0) (fun _ => 0) z.1 z.2 =
        twoDAbsoluteShortPolynomial (fun _ => 0) (fun _ => 0) z + R z :=
  twoDEmpty_admissible.exists_absoluteOverlap_remainder

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (A : TwoDIntervalFamily h) (G : TwoDSpace → ℝ) :
    (∑ x ∈ hf.joint_finite.toFinset, G x) =
      ∑ p ∈ A.intervals, (G (twoDLine.symm p.1) + G (twoDLine.symm p.2)) :=
  hf.endpoint_sum_eq_intervals A G

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (s r : ℝ) :
    (∫ ω : TwoDDirection, twoDAbsoluteShortPolynomial h f (s, r • ω.val) ∂twoDDirectionMeasure) =
      2 * volume.real (twoDRegion h f) - 2 * s * volume.real {x | 0 < h x} +
        twoDShortTimeCoefficient h * s ^ 2 + twoDShortSpaceCoefficient h f * r ^ 2 :=
  hf.integral_directions_absoluteShortPolynomial s r

end BoundaryDraft.TwoDTransportRegression
