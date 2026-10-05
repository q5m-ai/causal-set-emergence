import BoundaryDraft.TwoDLine

/-! # Normal-to-scalar endpoint identity for the independently fixed 2D target -/

open MeasureTheory Set
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

theorem twoD_differential_eq_inner (g : TwoDSpace → ℝ) (x v : TwoDSpace) :
    fderiv ℝ g x v = inner (𝕜 := ℝ) (twoDGradient g x) v := by
  change _ = (InnerProductSpace.toDual ℝ TwoDSpace)
    ((InnerProductSpace.toDual ℝ TwoDSpace).symm _) v
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem twoD_real_hasDerivAt {g : TwoDSpace → ℝ} {s : ℝ}
    (hg : DifferentiableAt ℝ g (twoDLine.symm s)) :
    HasDerivAt (fun t => g (twoDLine.symm t)) (twoDGradient g (twoDLine.symm s) 0) s := by
  have he : HasDerivAt (fun t : ℝ => twoDLine.symm t) (twoDLine.symm 1) s :=
    twoDLine.symm.toContinuousLinearEquiv.hasFDerivAt.hasDerivAt
  simpa only [twoD_differential_eq_inner, twoD_inner_eq, twoDLine_symm_apply, mul_one] using
    hg.hasFDerivAt.comp_hasDerivAt s he

/-- In one spatial dimension the Gram defect is exactly the squared slope difference. -/
theorem twoDUnitNormal_weight {v w : TwoDSpace} (hv : ‖v‖ < 1) (hw : ‖w‖ < 1)
    (hne : v ≠ w) :
    dimensionMinkowski 1 (twoDUnitNormal v) (twoDUnitNormal w) /
      Real.sqrt (dimensionMinkowski 1 (twoDUnitNormal v) (twoDUnitNormal w) ^ 2 - 1) =
        (1 - v 0 * w 0) / |v 0 - w 0| := by
  have hdiff : v 0 - w 0 ≠ 0 := by
    intro he
    apply hne
    apply twoDLine.injective
    exact sub_eq_zero.mp he
  have hv' : 0 < 1 - v 0 ^ 2 := by
    rw [twoD_norm_eq] at hv
    nlinarith [sq_abs (v 0), abs_nonneg (v 0)]
  have hw' : 0 < 1 - w 0 ^ 2 := by
    rw [twoD_norm_eq] at hw
    nlinarith [sq_abs (w 0), abs_nonneg (w 0)]
  let D := Real.sqrt (1 - v 0 ^ 2) * Real.sqrt (1 - w 0 ^ 2)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr hv') (Real.sqrt_pos.mpr hw')
  have hDs : D ^ 2 = (1 - v 0 ^ 2) * (1 - w 0 ^ 2) := by
    dsimp only [D]
    rw [mul_pow, Real.sq_sqrt hv'.le, Real.sq_sqrt hw'.le]
  have he : ((1 - v 0 * w 0) / D) ^ 2 - 1 = ((v 0 - w 0) / D) ^ 2 := by
    field_simp
    nlinarith [hDs]
  simp only [twoDUnitNormal_inner, twoD_inner_eq, twoD_norm_eq, sq_abs]
  change ((1 - v 0 * w 0) / D) / Real.sqrt (((1 - v 0 * w 0) / D) ^ 2 - 1) = _
  rw [he, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hD]
  field_simp [hD.ne', abs_ne_zero.mpr hdiff]

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- The scalar endpoint coefficient is derived from the actual unit normals.
The target is NOT redefined as an asymptotic coefficient. -/
theorem weight_eq_scalar (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    twoDWeight h f x =
      (1 - twoDGradient f x 0 ^ 2 + twoDGradient h x 0 * twoDGradient f x 0) /
        |twoDGradient h x 0| := by
  have hneq : twoDGradient (fun y => f y - h y) x ≠ twoDGradient f x := by
    rw [hf.gradient_past x hx.1]
    intro he
    have hg : twoDGradient h x = 0 := sub_eq_self.mp he
    have hn : 0 < ‖twoDGradient h x‖ := by
      rw [twoDGradient_norm]
      exact norm_pos_iff.mpr (hf.regular_zero x hx.1 hx.2)
    simp [hg] at hn
  unfold twoDWeight twoDCosh twoDNormal
  rw [twoDUnitNormal_weight (hf.face_slopes_lt_one x hx.1).2
    (hf.face_slopes_lt_one x hx.1).1 hneq, hf.gradient_past x hx.1]
  simp only [PiLp.sub_apply, sub_sub_cancel_left, abs_neg]
  congr 1
  ring

theorem boundaryIntegral_eq_scalar_sum :
    twoDBoundaryIntegral h f = ∑ x ∈ hf.joint_finite.toFinset,
      (1 - twoDGradient f x 0 ^ 2 + twoDGradient h x 0 * twoDGradient f x 0) /
        |twoDGradient h x 0| := by
  rw [hf.boundaryIntegral_eq_sum]
  exact Finset.sum_congr rfl (fun x hx => hf.weight_eq_scalar x (hf.joint_finite.mem_toFinset.mp hx))

end SmoothTwoD
end BoundaryDraft
