import BoundaryDraft.TwoDShortJet
import BoundaryDraft.TwoDCubicBounds

/-! # Actual 2D overlap polynomial and derivative-controlled cubic remainder -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- All bulk and endpoint terms of the actual absolute two-jet. This is not
an angular average, a planar subtraction or a redefinition of the target. -/
def twoDAbsoluteShortPolynomial (h f : TwoDSpace → ℝ) (z : TwoDSpacetime) : ℝ :=
  volume.real (twoDRegion h f) - z.1 * volume.real {x | 0 < h x} +
    (∫ x in {x | 0 < h x}, inner (𝕜 := ℝ) (twoDGradient f x) z.2) +
    (1 / 2 : ℝ) * ((∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x z.2 z.2) +
      ∫ x, (z.1 - inner (𝕜 := ℝ) (twoDGradient f x) z.2) ^ 2 / ‖twoDGradient h x‖
        ∂dimensionTwoJointMeasure h)

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem exists_absoluteOverlap_taylorPolynomial :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : TwoDSpacetime → ℝ,
      ContDiffAt ℝ 3 F 0 ∧
      (∀ z, twoDAbsoluteShortPolynomial h f z =
        F 0 + fderiv ℝ F 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ F) 0 z z) ∧
      ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
        F z = twoDOverlap h f z.1 z.2 := by
  obtain ⟨δ, hδ, F, hF, hF₀, hF₁, hF₂, heF⟩ := hf.exists_absoluteOverlap_twoJet
  refine ⟨δ, hδ, F, hF, ?_, ?_⟩
  · intro z
    rw [twoDAbsoluteShortPolynomial, hF₀, hF₁, hF₂]
    simp only [pow_two]
    ring
  · intro z hz hc
    exact (heF z hz hc).trans (hf.displacementOverlap_eq_actual z)

/-- One measurable remainder and one positive FIXED radius, derived from the
actual overlap germ. Includes value, first- and second-derivative bounds;
a cubic value bound alone is not a signed-density cancellation theorem. -/
theorem exists_absoluteOverlap_remainder :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ (R : TwoDSpacetime → ℝ) (T : ℝ),
      Measurable R ∧ TwoDShortRemainder.CubicBounds R δ₀ T ∧
      ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ₀, ‖z.2‖ ≤ z.1 →
        twoDOverlap h f z.1 z.2 = twoDAbsoluteShortPolynomial h f z + R z := by
  obtain ⟨ε, hε, F, hF, hP, heF⟩ := hf.exists_absoluteOverlap_taylorPolynomial
  obtain ⟨R, δ, T, hR, hδ, hB, he⟩ := TwoDShortRemainder.exists_absolute_taylor_remainder hF
  refine ⟨min ε δ, lt_min hε hδ, R, T, hR, hB.mono (min_le_right _ _), ?_⟩
  intro z hz hc
  rw [← heF z (Metric.ball_subset_ball (min_le_left _ _) hz) hc,
    he z (Metric.ball_subset_ball (min_le_right _ _) hz), ← hP z]

end SmoothTwoD
end BoundaryDraft
