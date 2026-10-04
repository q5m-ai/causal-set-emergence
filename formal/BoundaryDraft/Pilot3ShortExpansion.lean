import BoundaryDraft.Pilot3ShortAngular
import BoundaryDraft.Pilot3ShortJet
import BoundaryDraft.Pilot3CubicBounds

/-!
# The actual absolute short overlap expansion

The geometric two-jet identifies the independently specified absolute
polynomial, retaining point volume, moving slice, future Hessian and the
canonical surface square. The generic C³ Taylor theorem then supplies a
measurable primitive remainder with value and first/second derivative bounds
on one fixed causal ball. No analytic premise is added to `SmoothPilot3`.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

/-- The time, mixed and spatial surface terms of the absolute polynomial are
exactly half the canonical surface square. All signed splits are justified by
absolute integrability before the integral identities are used. -/
theorem absoluteShortPolynomial_eq_expanded (z : Pilot3Spacetime) :
    pilot3AbsoluteShortPolynomial h f z =
      volume.real (pilot3Region h f) - z.1 * volume.real {x | 0 < h x} +
      (∫ x in {x | 0 < h x}, inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) +
      (1 / 2 : ℝ) * (∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x z.2 z.2) +
      (1 / 2 : ℝ) * (∫ x, (z.1 - inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) ^ 2 /
        ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) := by
  have hi₀ := (hf.integrable_graphSurface_weight_div (fun _ => 1)
    continuousOn_const).const_mul (z.1 ^ 2)
  have hi₁ := hf.integrable_graphSurface_inner_mul_div z.2 z.2
  have hi₂ := (hf.integrable_graphSurface_inner_div z.2).const_mul (2 * z.1)
  have he : (∫ x, (z.1 - inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) ^ 2 /
      ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) =
      z.1 ^ 2 * (∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) +
      ∫ x, (inner (𝕜 := ℝ) (pilot3Gradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) / ‖pilot3Gradient h x‖
          ∂pilot3SurfaceMeasure h := by
    have hic : Integrable (fun x => (inner (𝕜 := ℝ) (pilot3Gradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) / ‖pilot3Gradient h x‖)
          (pilot3SurfaceMeasure h) := (hi₁.sub hi₂).congr (Eventually.of_forall fun x => by
            dsimp only [Pi.sub_apply]; ring)
    rw [← integral_const_mul, ← integral_add hi₀ hic]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he, pilot3AbsoluteShortPolynomial, pilot3SpatialShortPolynomial]
  ring

/-- The actual causal-overlap extension has precisely the absolute polynomial
as its Taylor polynomial, not a fitted or assumed model. -/
theorem exists_absoluteOverlap_taylorPolynomial :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Pilot3Spacetime → ℝ,
      ContDiffAt ℝ 3 F 0 ∧
      (∀ z, pilot3AbsoluteShortPolynomial h f z =
        F 0 + fderiv ℝ F 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ F) 0 z z) ∧
      ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ, ‖z.2‖ ≤ z.1 → F z = pilot3Overlap h f z := by
  obtain ⟨δ, hδ, F, hF, hF₀, hF₁, hF₂, heF⟩ := hf.exists_absoluteOverlap_twoJet
  refine ⟨δ, hδ, F, hF, ?_, heF⟩
  intro z
  rw [hf.absoluteShortPolynomial_eq_expanded, hF₀, hF₁, hF₂]
  simp only [pow_two]
  ring

/-- Unconditional primitive remainder for the actual overlap, with a positive
geometry-dependent fixed radius and all three derivative-controlled cubic
bounds. No partner restriction, shrinking-cutoff claim or action limit is
introduced by this producer. -/
theorem exists_absoluteOverlap_remainder :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ (R : Pilot3Spacetime → ℝ) (T : ℝ),
      Measurable R ∧ Pilot3ShortRemainder.CubicBounds R δ₀ T ∧
      ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ₀, ‖z.2‖ ≤ z.1 →
        pilot3Overlap h f z = pilot3AbsoluteShortPolynomial h f z + R z := by
  obtain ⟨ε, hε, F, hF, hP, heF⟩ := hf.exists_absoluteOverlap_taylorPolynomial
  obtain ⟨R, δ, T, hR, hδ, hB, he⟩ := Pilot3ShortRemainder.exists_absolute_taylor_remainder hF
  refine ⟨min ε δ, lt_min hε hδ, R, T, hR, hB.mono (min_le_right _ _), ?_⟩
  intro z hz hc
  rw [← heF z (Metric.ball_subset_ball (min_le_left _ _) hz) hc,
    he z (Metric.ball_subset_ball (min_le_right _ _) hz), ← hP z]

end SmoothPilot3
end BoundaryDraft
