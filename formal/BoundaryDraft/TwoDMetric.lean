import BoundaryDraft.TwoDGeometry
import BoundaryDraft.JointMetric

/-!
# Actual 2D normals and the independent all-endpoint angle target

Only the scalar positive-rapidity identity is reused from the 4D package.
No higher-dimensional angular measure, moment, jet, or limit is imported as
a two-dimensional analytic theorem.
-/

open MeasureTheory Set
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

theorem twoDGradient_norm (h : TwoDSpace → ℝ) (x : TwoDSpace) :
    ‖twoDGradient h x‖ = ‖fderiv ℝ h x‖ :=
  (InnerProductSpace.toDual ℝ TwoDSpace).symm.norm_map _

theorem twoDUnitNormal_inner (v w : TwoDSpace) :
    dimensionMinkowski 1 (twoDUnitNormal v) (twoDUnitNormal w) =
      (1 - inner (𝕜 := ℝ) v w) /
        (Real.sqrt (1 - ‖v‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) := by
  simp only [twoDUnitNormal, dimensionMinkowski_apply, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

theorem twoDUnitNormal_future_unit {v : TwoDSpace} (hv : ‖v‖ < 1) :
    0 < (twoDUnitNormal v).1 ∧
      dimensionMinkowski 1 (twoDUnitNormal v) (twoDUnitNormal v) = 1 := by
  have hd : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hs := Real.sqrt_pos.mpr hd
  constructor
  · simpa [twoDUnitNormal] using inv_pos.mpr hs
  · rw [twoDUnitNormal_inner, real_inner_self_eq_norm_sq, ← pow_two, Real.sq_sqrt hd.le]
    exact div_self hd.ne'

theorem twoDUnitNormal_inner_gt_one {v w : TwoDSpace}
    (hv : ‖v‖ < 1) (hw : ‖w‖ < 1) (hne : v ≠ w) :
    1 < dimensionMinkowski 1 (twoDUnitNormal v) (twoDUnitNormal w) := by
  have hv0 := norm_nonneg v
  have hw0 := norm_nonneg w
  have hdv : 0 < 1 - ‖v‖ ^ 2 := by nlinarith
  have hdw : 0 < 1 - ‖w‖ ^ 2 := by nlinarith
  have hsv := Real.sqrt_pos.mpr hdv
  have hsw := Real.sqrt_pos.mpr hdw
  have hprod := mul_pos hsv hsw
  have hn : 0 < 1 - inner (𝕜 := ℝ) v w := by
    have hi := real_inner_le_norm v w
    have hm : ‖v‖ * ‖w‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hv.le hw0 hw
    linarith
  have hdiff := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hid : (1 - inner (𝕜 := ℝ) v w) ^ 2 -
      (1 - ‖v‖ ^ 2) * (1 - ‖w‖ ^ 2) =
      ‖v - w‖ ^ 2 * (1 - ‖w‖ ^ 2) + inner (𝕜 := ℝ) (v - w) w ^ 2 := by
    rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
    ring
  have hsq : (Real.sqrt (1 - ‖v‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) ^ 2 =
      (1 - ‖v‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hdv.le, Real.sq_sqrt hdw.le]
  rw [twoDUnitNormal_inner, one_lt_div hprod]
  nlinarith [mul_pos hdiff hdw, sq_nonneg (inner (𝕜 := ℝ) (v - w) w)]

theorem twoDNormal_orthogonal {f : TwoDSpace → ℝ} (x v : TwoDSpace) :
    dimensionMinkowski 1 (twoDNormal f x) (fderiv ℝ f x v, v) = 0 := by
  have he : fderiv ℝ f x v = inner (𝕜 := ℝ) (twoDGradient f x) v := by
    change _ = (InnerProductSpace.toDual ℝ TwoDSpace)
      ((InnerProductSpace.toDual ℝ TwoDSpace).symm _) v
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  simp [twoDNormal, twoDUnitNormal, dimensionMinkowski_apply, inner_smul_left]

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem gradient_past (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    twoDGradient (fun y => f y - h y) x = twoDGradient f x - twoDGradient h x := by
  simp only [twoDGradient, gradient,
    fderiv_sub ((hf.future_smoothAt x hx).differentiableAt (by simp))
      ((hf.height_smoothAt x hx).differentiableAt (by simp)), map_sub]

theorem exists_slope_bounds : ∃ κ η : ℝ, 0 ≤ κ ∧ 0 ≤ η ∧ κ + η < 1 ∧
    ∀ x ∈ twoDClosedPositive h, ‖twoDGradient h x‖ ≤ κ ∧ ‖twoDGradient f x‖ ≤ η := by
  obtain ⟨κ, η, hκ, hη, hb, hl, hu⟩ := hf.slope_budget
  have hL : LipschitzOnWith ⟨κ, hκ⟩ h {x | 0 < h x} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have he := hl x y
    rw [max_eq_right hx.le, max_eq_right hy.le] at he
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using he
  have hfL : LipschitzWith ⟨η, hη⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using hu x y
  have hc : ContinuousOn (fderiv ℝ h) (twoDClosedPositive h) :=
    fun x hx => ((hf.height_smoothAt x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  refine ⟨κ, η, hκ, hη, hb, fun x hx => ?_⟩
  rw [twoDGradient_norm, twoDGradient_norm]
  exact ⟨le_on_closure (fun y hy => norm_fderiv_le_of_lipschitzOn ℝ
    (hf.isOpen_positive.mem_nhds hy) hL) hc.norm continuousOn_const hx,
    norm_fderiv_le_of_lipschitz ℝ hfL⟩

theorem face_slopes_lt_one (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    ‖twoDGradient f x‖ < 1 ∧ ‖twoDGradient (fun y => f y - h y) x‖ < 1 := by
  obtain ⟨κ, η, hκ, _, hb, hs⟩ := hf.exists_slope_bounds
  obtain ⟨hhx, hfx⟩ := hs x hx
  refine ⟨by linarith, ?_⟩
  rw [hf.gradient_past x hx]
  exact (norm_sub_le _ _).trans_lt (by linarith)

theorem normals_future_unit (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    (0 < (twoDNormal f x).1 ∧
      dimensionMinkowski 1 (twoDNormal f x) (twoDNormal f x) = 1) ∧
    (0 < (twoDNormal (fun y => f y - h y) x).1 ∧
      dimensionMinkowski 1 (twoDNormal (fun y => f y - h y) x)
        (twoDNormal (fun y => f y - h y) x) = 1) :=
  ⟨twoDUnitNormal_future_unit (hf.face_slopes_lt_one x hx).1,
    twoDUnitNormal_future_unit (hf.face_slopes_lt_one x hx).2⟩

theorem cosh_gt_one (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    1 < twoDCosh h f x := by
  apply twoDUnitNormal_inner_gt_one (hf.face_slopes_lt_one x hx.1).2
    (hf.face_slopes_lt_one x hx.1).1
  rw [hf.gradient_past x hx.1]
  intro he
  have hg : twoDGradient h x = 0 := sub_eq_self.mp he
  have hp : 0 < ‖twoDGradient h x‖ := by
    rw [twoDGradient_norm]
    exact norm_pos_iff.mpr (hf.regular_zero x hx.1 hx.2)
  simp [hg] at hp

theorem angle_identities (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    0 < twoDAngle h f x ∧ Real.cosh (twoDAngle h f x) = twoDCosh h f x ∧
    Real.sinh (twoDAngle h f x) = Real.sqrt (twoDCosh h f x ^ 2 - 1) ∧
    Real.cosh (twoDAngle h f x) / Real.sinh (twoDAngle h f x) = twoDWeight h f x :=
  jointAngle_identities (hf.cosh_gt_one x hx)

/-- The independent target is the positive-angle weight at EVERY endpoint. -/
theorem boundaryIntegral_eq_coth_sum :
    twoDBoundaryIntegral h f = ∑ x ∈ hf.joint_finite.toFinset,
      Real.cosh (twoDAngle h f x) / Real.sinh (twoDAngle h f x) := by
  rw [hf.boundaryIntegral_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact (hf.angle_identities x (hf.joint_finite.mem_toFinset.mp hx)).2.2.2.symm

end SmoothTwoD
end BoundaryDraft
