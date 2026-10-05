import BoundaryDraft.TwoDDisconnected

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
