import BoundaryDraft.TwoDDisconnected
import BoundaryDraft.TwoDExponentialTail

/-! # Unconditional genuine 2D limits, signed logs and all-endpoint regressions

These examples instantiate the unchanged contracts. They are Lean regressions,
not independent human mathematical review or sample-wise convergence results.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft.TwoDLimitRegression

example : TwoDDeterministicGoal := twoDDeterministicGoal
example : TwoDExpectedGoal := twoDExpectedGoal

/-- The full causal-pair action and the independent normal/Hausdorff target,
with the physical point, pair and interval constants expanded. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    Tendsto (fun ρ => ρ * (2 * (∫ _p in twoDRegion h f, (1 : ℝ)) -
      4 * ρ * ∫ p in twoDRegion h f, ∫ q in twoDRegion h f ∩ dimensionCausalFuture p,
        dimensionKernel 2 ((1 / 2) * ρ * ((q.1 - p.1) ^ 2 - ‖q.2 - p.2‖ ^ 2)))) atTop
      (𝓝 (∫ x, twoDCosh h f x / Real.sqrt (twoDCosh h f x ^ 2 - 1)
        ∂(μH[0] : Measure TwoDSpace).restrict (closure {x | 0 < h x} ∩ {x | h x = 0}))) := by
  simpa only [twoDAction, dimensionWeightedAction, dimensionBilocalKernel,
    dimensionIntervalSq, one_mul, Nat.reduceAdd, Nat.cast_ofNat,
    dimensionPointCoefficient_two, dimensionPairCoefficient_two, dimensionIntervalCoefficient_two,
    div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one, twoDBoundaryIntegral,
    twoDWeight, dimensionTwoJointMeasure, dimensionTwoSpatialJoint] using hf.tendsto_action

/-- The independently constructed Poisson law and actual discrete layer counts.
No density power, fitted layer weight or bounded-cardinality assumption remains. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    Tendsto (fun ρ => ∫ c : Multiset TwoDSpacetime,
      2 * c.card - 4 * ((dimensionMeasuredOrder 1).layer 0 c : ℝ) +
        8 * ((dimensionMeasuredOrder 1).layer 1 c : ℝ) -
        4 * ((dimensionMeasuredOrder 1).layer 2 c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoDRegion h f))) atTop
      (𝓝 (∫ x, twoDCosh h f x / Real.sqrt (twoDCosh h f x ^ 2 - 1)
        ∂(μH[0] : Measure TwoDSpace).restrict (closure {x | 0 < h x} ∩ {x | h x = 0}))) := by
  simpa only [dimensionExpectedAction, Nat.reduceAdd, discreteDimensionAction_two,
    twoDBoundaryIntegral, twoDWeight, dimensionTwoJointMeasure, dimensionTwoSpatialJoint]
    using hf.tendsto_expectedAction

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (FinitePoisson.law
      (ENNReal.ofReal ρ • volume.restrict (twoDRegion h f))) ∧
    Integrable (discreteDimensionAction (dimensionMeasuredOrder 1) 2 ρ)
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoDRegion h f))) :=
  ⟨inferInstanceAs (IsProbabilityMeasure (hf.boundedCausalRegion.sprinkling ρ hρ).probability),
    (hf.boundedCausalRegion.sprinkling ρ hρ).integrable_action⟩

/-- One produced fixed cutoff, point allocated once, both actual responses. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ ρ, twoDAction ρ h f = twoDShortAction ρ δ h f + twoDLongAction ρ δ h f) ∧
      Tendsto (fun ρ => twoDShortAction ρ δ h f) atTop (𝓝 (twoDBoundaryIntegral h f)) ∧
      Tendsto (fun ρ => twoDLongAction ρ δ h f) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hs⟩ := hf.exists_shortAction_limit
  exact ⟨δ, hδ, fun ρ => hf.action_eq_short_add_long ρ δ, hs, hf.tendsto_longAction hδ⟩

example (δ : ℝ) (z : TwoDSpacetime) (hz : z ∈ dimensionCausalFuture 0)
    (he : z.1 + ‖z.2‖ = δ) : z ∈ twoDLongFuture δ ∧ z ∉ twoDShortFuture δ :=
  ⟨⟨hz, he.ge⟩, fun hs => hs.2 ⟨hz, he.ge⟩⟩

example (n : ℕ) {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    (∫ σ : ℝ in Ioi q, (k * σ) ^ n * |dimensionKernel 2 (k * σ)|) ≤
      (TwoDExponentialTail.constant n / k) * Real.exp (-(k * q) / 2) :=
  TwoDExponentialTail.scaled_moment_tail n hk hq

example : (∫ u : ℝ in Ioi 0, Real.log u * dimensionKernel 2 u) = -(1 / 2 : ℝ) :=
  TwoDLogMoments.integral_log_zero

example : (∫ u : ℝ in Ioi 0, u * Real.log u * dimensionKernel 2 u) = (1 / 2 : ℝ) :=
  TwoDLogMoments.integral_log_one

example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ a₀ a₁ : ℝ,
      (fun σ => twoDShortOverlapDensity h f δ σ -
        (a₀ + a₁ * σ - (volume.real (twoDRegion h f) / 2) * Real.log σ -
          (twoDBoundaryIntegral h f / 8) * σ * Real.log σ)) =o[𝓝[>] 0] (fun σ => σ) :=
  hf.shortDensity_logarithmic_jet

/-- The complete normalized long response works at any fixed positive cutoff. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => twoDLongAction ρ δ h f) atTop (𝓝 0) := hf.tendsto_longAction hδ

example : Tendsto (fun ρ => twoDAction ρ twoDIntervalHeight twoDSineFuture)
    atTop (𝓝 (twoDBoundaryIntegral twoDIntervalHeight twoDSineFuture)) :=
  twoDIntervalSine_admissible.tendsto_action

example : Tendsto (fun ρ => twoDAction ρ twoDIntervalHeight (fun _ => 0))
    atTop (𝓝 (twoDBoundaryIntegral twoDIntervalHeight (fun _ => 0))) :=
  twoDIntervalPlanar_admissible.tendsto_action

example : Tendsto (fun ρ => twoDAction ρ (fun _ => 0) (fun _ => 0))
    atTop (𝓝 (twoDBoundaryIntegral (fun _ => 0) (fun _ => 0))) :=
  twoDEmpty_admissible.tendsto_action

example : Tendsto (fun ρ => twoDAction ρ twoDDisconnectedHeight twoDSineFuture)
    atTop (𝓝 (twoDBoundaryIntegral twoDDisconnectedHeight twoDSineFuture)) :=
  twoDDisconnectedSine_admissible.tendsto_action

example : Tendsto (fun ρ => dimensionExpectedAction 1 ρ (twoDRegion twoDDisconnectedHeight twoDSineFuture))
    atTop (𝓝 (twoDBoundaryIntegral twoDDisconnectedHeight twoDSineFuture)) :=
  twoDDisconnectedSine_admissible.tendsto_expectedAction

example : dimensionTwoSpatialJoint twoDDisconnectedHeight =
    {twoDLine.symm (-1), twoDLine.symm 1, twoDLine.symm 3, twoDLine.symm 5} :=
  twoDDisconnected_four_endpoints

example : (∫ _x, (1 : ℝ) ∂dimensionTwoJointMeasure twoDDisconnectedHeight) = 4 := by
  rw [twoDDisconnected_endpoint_integral]
  norm_num

example : (0 < twoDDisconnectedHeight 0 ∧ fderiv ℝ twoDDisconnectedHeight 0 = 0) ∧
    (0 < twoDDisconnectedHeight twoDOtherCenter ∧ fderiv ℝ twoDDisconnectedHeight twoDOtherCenter = 0) :=
  twoDDisconnected_both_critical

/-- The actual-overlap expansion also applies to null displacements. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (R : TwoDSpacetime → ℝ) (T : ℝ),
      Measurable R ∧ TwoDShortRemainder.CubicBounds R δ T ∧
      ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ = z.1 →
        twoDOverlap h f z.1 z.2 = twoDAbsoluteShortPolynomial h f z + R z := by
  obtain ⟨δ, hδ, R, T, hR, hB, he⟩ := hf.exists_absoluteOverlap_remainder
  exact ⟨δ, hδ, R, T, hR, hB, fun z hz hc => he z hz hc.le⟩

end BoundaryDraft.TwoDLimitRegression
