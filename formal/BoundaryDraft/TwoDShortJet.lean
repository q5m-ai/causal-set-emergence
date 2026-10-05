import BoundaryDraft.TwoDShortCollar

/-! # Complete actual 2D overlap C³ extension and absolute two-jet -/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

set_option maxHeartbeats 800000 in
/-- The complete absolute overlap C³ extension and two-jet, derived solely
from the unchanged `SmoothTwoD`. The surface term uses the independently
fixed canonical unit endpoint measure, and equality holds for the actual covariogram
on the entire causal ball, including the vertex and null displacements. -/
theorem exists_absoluteOverlap_twoJet :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : TwoDSpacetime → ℝ,
      ContDiffAt ℝ 3 F 0 ∧ F 0 = volume.real (twoDRegion h f) ∧
      (∀ v : TwoDSpacetime, fderiv ℝ F 0 v =
        -v.1 * volume.real {x | 0 < h x} +
          ∫ x in {x | 0 < h x}, inner (𝕜 := ℝ) (twoDGradient f x) v.2) ∧
      (∀ v w : TwoDSpacetime, fderiv ℝ (fderiv ℝ F) 0 v w =
        (∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x v.2 w.2) +
        ∫ x, ((v.1 - inner (𝕜 := ℝ) (twoDGradient f x) v.2) *
          (w.1 - inner (𝕜 := ℝ) (twoDGradient f x) w.2)) / ‖twoDGradient h x‖
          ∂dimensionTwoJointMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 → F z = twoDDisplacementOverlap h f z := by
  obtain ⟨δ, hδ, V, hV, hV₀, hV₁, hV₂, heV⟩ := hf.exists_shortCollar_twoJet
  obtain ⟨hB, hB₀, hB₁, hB₂⟩ := hf.shortBulk_twoJet
  let L : TwoDSpacetime →L[ℝ] ℝ :=
    (-volume.real {x | 0 < h x}) • ContinuousLinearMap.fst ℝ ℝ TwoDSpace
  let U : TwoDSpacetime → ℝ := fun z => volume.real (twoDRegion h f) + L z
  have hU : ContDiff ℝ 3 U := contDiff_const.add L.contDiff
  have hUD (z : TwoDSpacetime) : fderiv ℝ U z = L := by
    simpa only [zero_add] using
      ((hasFDerivAt_const (volume.real (twoDRegion h f)) z).add L.hasFDerivAt).fderiv
  let F : TwoDSpacetime → ℝ := fun z => U z + twoDShortBulk h f z + V z
  have hF : ContDiffAt ℝ 3 F 0 := (hU.contDiffAt.add hB).add hV
  refine ⟨δ, hδ, F, hF, by simp [F, U, hB₀, hV₀], ?_, ?_, ?_⟩
  · intro v
    dsimp only [F]
    rw [fderiv_add ((hU.differentiable (by norm_num) 0).add (hB.differentiableAt (by norm_num)))
      (hV.differentiableAt (by norm_num)), fderiv_add (hU.differentiable (by norm_num) 0)
        (hB.differentiableAt (by norm_num)), hV₁, hUD]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, add_zero, hB₁]
    simp only [twoD_differential_eq_inner]
    dsimp [L]
    ring
  · intro v w
    have heD : fderiv ℝ F =ᶠ[𝓝 (0 : TwoDSpacetime)]
        (fun z => L + fderiv ℝ (twoDShortBulk h f) z + fderiv ℝ V z) := by
      filter_upwards [hB.eventually (by simp), hV.eventually (by simp)] with z hzB hzV
      dsimp only [F]
      rw [fderiv_add ((hU.differentiable (by norm_num) z).add (hzB.differentiableAt (by norm_num)))
        (hzV.differentiableAt (by norm_num)), fderiv_add (hU.differentiable (by norm_num) z)
          (hzB.differentiableAt (by norm_num)), hUD]
    have hDB := (hB.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hDV := (hV.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    rw [heD.fderiv_eq, fderiv_add (differentiableAt_const L |>.add hDB) hDV,
      fderiv_const_add L]
    simp only [ContinuousLinearMap.add_apply, hB₂, hV₂,
      twoDShortGapLinear_apply, twoD_differential_eq_inner]
  · intro z hz hc
    rw [hf.overlap_eq_absolute_bulk z hc]
    dsimp only [F, U]
    rw [heV z hz hc]
    dsimp [L]
    ring

end SmoothTwoD
end BoundaryDraft
