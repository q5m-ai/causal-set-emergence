import BoundaryDraft.Pilot3ShortExpansion
import BoundaryDraft.Pilot3ShortAssembly

/-!
# Unconditional short-action limit for the smooth three-dimensional pilot

For every member of the unchanged combined-budget class, one positive geometric
radius works for every smaller fixed positive cutoff. The actual overlap jet,
sharp signed responses, derivative-controlled nearly-null remainder and
intrinsic coefficient identification are proved producers, not hypotheses.
This file does not assert the long, global-action or expected-action limit.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace SmoothPilot3

/-- The actual fully normalized short action converges to the independently
fixed intrinsic target. The cutoff is fixed before taking the density limit;
no analytic admissibility assumptions or planar-base theorem are required. -/
theorem exists_shortAction_limit {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop
        (𝓝 (pilot3BoundaryIntegral h f)) := by
  obtain ⟨δ₀, hδ₀, R, T, hR, hb, he⟩ := hf.exists_absoluteOverlap_remainder
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  have hbδ := hb.mono hδ₀'
  have heδ (z : Pilot3Spacetime) (hz : z ∈ Metric.ball (0 : Pilot3Spacetime) δ)
      (hc : ‖z.2‖ ≤ z.1) :
      pilot3Overlap h f z = pilot3AbsoluteShortPolynomial h f z + R z :=
    he z (Metric.ball_subset_ball hδ₀' hz) hc
  have hm := Pilot3ShortResponse.modelAction_limit hδ (volume.real (pilot3Region h f))
    (pilot3ShortLinearCoefficient h) (pilot3ShortTimeCoefficient h)
      (pilot3ShortSpaceCoefficient h f)
  rw [hf.shortCoefficient_identification] at hm
  have hr := hbδ.normalized_action_remainder_limit hR
  have hl := hm.add hr
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hf.shortAction_eq_model_add_remainder hδ hρ hR hbδ heδ).symm

end SmoothPilot3
end BoundaryDraft
