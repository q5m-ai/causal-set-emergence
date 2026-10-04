import BoundaryDraft.Pilot3Geometry
import BoundaryDraft.JointMetric

/-!
# Future normals, positive angle and the one-dimensional induced Gram density

The scalar positive-rapidity identity is reused from `JointMetric`; none of
its spatial cross-product or four-dimensional analytic results is used.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

@[simp] theorem pilot3Gradient_zero (x : Pilot3Space) :
    pilot3Gradient (fun _ => 0) x = 0 := by simp [pilot3Gradient, gradient]

theorem pilot3Gradient_sub {h f : Pilot3Space → ℝ} {x : Pilot3Space}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    pilot3Gradient (fun y => f y - h y) x = pilot3Gradient f x - pilot3Gradient h x := by
  simp only [pilot3Gradient, gradient, fderiv_sub hf hh, map_sub]

theorem continuousOn_pilot3Gradient {f : Pilot3Space → ℝ} {s : Set Pilot3Space}
    (hf : ∀ x ∈ s, ContDiffAt ℝ ∞ f x) : ContinuousOn (pilot3Gradient f) s := by
  apply (InnerProductSpace.toDual ℝ Pilot3Space).symm.continuous.comp_continuousOn
  intro x hx
  exact ((hf x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt

/-- A future normal defined directly from a Euclidean slope vector. -/
def pilot3UnitNormal (v : Pilot3Space) : Pilot3Spacetime :=
  (Real.sqrt (1 - ‖v‖ ^ 2))⁻¹ • (1, v)

@[simp] theorem pilot3UnitNormal_inner (v w : Pilot3Space) :
    dimensionMinkowski 2 (pilot3UnitNormal v) (pilot3UnitNormal w) =
      (1 - inner (𝕜 := ℝ) v w) /
        (Real.sqrt (1 - ‖v‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) := by
  simp only [pilot3UnitNormal, dimensionMinkowski_apply, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

theorem pilot3UnitNormal_future_unit {v : Pilot3Space} (hv : ‖v‖ < 1) :
    0 < (pilot3UnitNormal v).1 ∧
      dimensionMinkowski 2 (pilot3UnitNormal v) (pilot3UnitNormal v) = 1 := by
  have hd : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hs := Real.sqrt_pos.mpr hd
  constructor
  · simpa [pilot3UnitNormal] using inv_pos.mpr hs
  · rw [pilot3UnitNormal_inner, real_inner_self_eq_norm_sq, ← pow_two, Real.sq_sqrt hd.le]
    exact div_self hd.ne'

theorem pilot3UnitNormal_inner_gt_one {v w : Pilot3Space}
    (hv : ‖v‖ < 1) (hw : ‖w‖ < 1) (hne : v ≠ w) :
    1 < dimensionMinkowski 2 (pilot3UnitNormal v) (pilot3UnitNormal w) := by
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
  rw [pilot3UnitNormal_inner, one_lt_div hprod]
  nlinarith [mul_pos hdiff hdw, sq_nonneg (inner (𝕜 := ℝ) (v - w) w)]

def pilot3GraphTangent (q v : Pilot3Space) : Pilot3Spacetime := (inner (𝕜 := ℝ) q v, v)

theorem pilot3UnitNormal_orthogonal (q v : Pilot3Space) :
    dimensionMinkowski 2 (pilot3UnitNormal q) (pilot3GraphTangent q v) = 0 := by
  simp [pilot3UnitNormal, pilot3GraphTangent, dimensionMinkowski_apply, inner_smul_left]

theorem pilot3_tangential_norm_sq (q n : Pilot3Space) (hn : ‖n‖ = 1) :
    ‖q - inner (𝕜 := ℝ) q n • n‖ ^ 2 = ‖q‖ ^ 2 - inner (𝕜 := ℝ) q n ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hn]
  ring

theorem pilot3_tangential_norm_le (q n : Pilot3Space) (hn : ‖n‖ = 1) :
    ‖q - inner (𝕜 := ℝ) q n • n‖ ≤ ‖q‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pilot3_tangential_norm_sq q n hn]
  linarith [sq_nonneg (inner (𝕜 := ℝ) q n)]

/-- One-dimensional Lorentzian Gram density, not a two-frame determinant. -/
def pilot3GramDensity (v : Pilot3Spacetime) : ℝ :=
  Real.sqrt (-dimensionMinkowski 2 v v)

/-- Orientation reversal has the same absolute Jacobian as any nonzero
change of one-dimensional tangent coordinates. This is pointwise algebra,
not yet a change-of-variables theorem for measures. -/
theorem pilot3GramDensity_smul (a : ℝ) (v : Pilot3Spacetime) :
    pilot3GramDensity (a • v) = |a| * pilot3GramDensity v := by
  simp only [pilot3GramDensity, dimensionMinkowski_apply, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [show -(a * v.1 * (a * v.1) - a * (a * inner (𝕜 := ℝ) v.2 v.2)) =
    a ^ 2 * -(v.1 * v.1 - inner (𝕜 := ℝ) v.2 v.2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem gradient_past (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    pilot3Gradient (fun y => f y - h y) x = pilot3Gradient f x - pilot3Gradient h x :=
  pilot3Gradient_sub ((hf.future_smoothAt x hx).differentiableAt (by simp))
    ((hf.toPilot3RegularHeight.smoothAt x hx).differentiableAt (by simp))

/-- Differentiate the clipped height only INSIDE the positive set, then
extend the actual smooth differential bound to its closure. -/
theorem exists_slope_bounds : ∃ κ η : ℝ, 0 ≤ κ ∧ 0 ≤ η ∧ κ + η < 1 ∧
    ∀ x ∈ pilot3ClosedPositive h,
      ‖pilot3Gradient h x‖ ≤ κ ∧ ‖pilot3Gradient f x‖ ≤ η := by
  obtain ⟨κ, η, hκ, hη, hb, hl, hu⟩ := hf.slope_budget
  have hopen := hf.toPilot3RegularHeight.isOpen_positive
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
  refine ⟨κ, η, hκ, hη, hb, fun x hx => ?_⟩
  rw [pilot3Gradient_norm, pilot3Gradient_norm]
  exact ⟨le_on_closure (fun y hy => norm_fderiv_le_of_lipschitzOn ℝ
    (hopen.mem_nhds hy) hL) hf.toPilot3RegularHeight.continuousOn_fderiv.norm continuousOn_const hx,
    norm_fderiv_le_of_lipschitz ℝ hfL⟩

theorem face_slopes_lt_one (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    ‖pilot3Gradient f x‖ < 1 ∧ ‖pilot3Gradient (fun y => f y - h y) x‖ < 1 := by
  obtain ⟨κ, η, hκ, _, hb, hs⟩ := hf.exists_slope_bounds
  obtain ⟨hhx, hfx⟩ := hs x hx
  refine ⟨by linarith, ?_⟩
  rw [hf.gradient_past x hx]
  exact (norm_sub_le _ _).trans_lt (by linarith)

theorem normals_future_unit (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    (0 < (pilot3Normal f x).1 ∧
      dimensionMinkowski 2 (pilot3Normal f x) (pilot3Normal f x) = 1) ∧
    (0 < (pilot3Normal (fun y => f y - h y) x).1 ∧
      dimensionMinkowski 2 (pilot3Normal (fun y => f y - h y) x)
        (pilot3Normal (fun y => f y - h y) x) = 1) :=
  ⟨pilot3UnitNormal_future_unit (hf.face_slopes_lt_one x hx).1,
    pilot3UnitNormal_future_unit (hf.face_slopes_lt_one x hx).2⟩

theorem cosh_gt_one (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) : 1 < pilot3Cosh h f x := by
  apply pilot3UnitNormal_inner_gt_one (hf.face_slopes_lt_one x hx.1).2
    (hf.face_slopes_lt_one x hx.1).1
  rw [hf.gradient_past x hx.1]
  intro he
  have hg : pilot3Gradient h x = 0 := sub_eq_self.mp he
  have hp := hf.toPilot3RegularHeight.gradient_pos x hx
  simp [hg] at hp

theorem angle_identities (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    0 < pilot3Angle h f x ∧ Real.cosh (pilot3Angle h f x) = pilot3Cosh h f x ∧
    Real.sinh (pilot3Angle h f x) = Real.sqrt (pilot3Cosh h f x ^ 2 - 1) ∧
    Real.cosh (pilot3Angle h f x) / Real.sinh (pilot3Angle h f x) = pilot3Weight h f x :=
  jointAngle_identities (hf.cosh_gt_one x hx)

theorem areaDensity_pos (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    0 < pilot3AreaDensity h f x := by
  have hb := pilot3_tangential_norm_le (pilot3Gradient f x) (pilot3Inward h x)
    (hf.toPilot3RegularHeight.inward_norm x hx)
  have hq := (hf.face_slopes_lt_one x hx.1).1
  apply Real.sqrt_pos.mpr
  change 0 < 1 - ‖pilot3TangentialGradient h f x‖ ^ 2
  change ‖pilot3TangentialGradient h f x‖ ≤ ‖pilot3Gradient f x‖ at hb
  nlinarith [norm_nonneg (pilot3TangentialGradient h f x)]

theorem continuousOn_cosh : ContinuousOn (pilot3Cosh h f) (pilot3SpatialJoint h) := by
  have hq := continuousOn_pilot3Gradient hf.future_smoothAt
  have hp := continuousOn_pilot3Gradient
    (fun x hx => (hf.future_smoothAt x hx).sub (hf.toPilot3RegularHeight.smoothAt x hx))
  have hc : ContinuousOn (fun x =>
      (1 - inner (𝕜 := ℝ) (pilot3Gradient (fun y => f y - h y) x) (pilot3Gradient f x)) /
        (Real.sqrt (1 - ‖pilot3Gradient (fun y => f y - h y) x‖ ^ 2) *
          Real.sqrt (1 - ‖pilot3Gradient f x‖ ^ 2))) (pilot3ClosedPositive h) := by
    apply (continuousOn_const.sub (hp.inner hq)).div
      (((continuousOn_const.sub (hp.norm.pow 2)).sqrt).mul
        ((continuousOn_const.sub (hq.norm.pow 2)).sqrt))
    intro x hx
    obtain ⟨hq1, hp1⟩ := hf.face_slopes_lt_one x hx
    apply mul_ne_zero <;> apply (Real.sqrt_pos.mpr ?_).ne'
    · nlinarith [norm_nonneg (pilot3Gradient (fun y => f y - h y) x)]
    · nlinarith [norm_nonneg (pilot3Gradient f x)]
  have he (x : Pilot3Space) : pilot3Cosh h f x =
      (1 - inner (𝕜 := ℝ) (pilot3Gradient (fun y => f y - h y) x) (pilot3Gradient f x)) /
        (Real.sqrt (1 - ‖pilot3Gradient (fun y => f y - h y) x‖ ^ 2) *
          Real.sqrt (1 - ‖pilot3Gradient f x‖ ^ 2)) := pilot3UnitNormal_inner _ _
  change ContinuousOn (fun x => pilot3Cosh h f x) (pilot3SpatialJoint h)
  simp_rw [he]
  exact hc.mono inter_subset_left

theorem continuousOn_weight : ContinuousOn (pilot3Weight h f) (pilot3SpatialJoint h) := by
  apply hf.continuousOn_cosh.div ((hf.continuousOn_cosh.pow 2).sub continuousOn_const).sqrt
  intro x hx
  apply (Real.sqrt_pos.mpr ?_).ne'
  nlinarith [hf.cosh_gt_one x hx]

theorem continuousOn_areaDensity : ContinuousOn (pilot3AreaDensity h f) (pilot3SpatialJoint h) := by
  have hq : ContinuousOn (pilot3Gradient f) (pilot3SpatialJoint h) :=
    (continuousOn_pilot3Gradient hf.future_smoothAt).mono inter_subset_left
  have hg : ContinuousOn (pilot3Gradient h) (pilot3SpatialJoint h) :=
    (continuousOn_pilot3Gradient hf.toPilot3RegularHeight.smoothAt).mono inter_subset_left
  have hn : ContinuousOn (pilot3Inward h) (pilot3SpatialJoint h) :=
    (hg.norm.inv₀ (fun x hx => (hf.toPilot3RegularHeight.gradient_pos x hx).ne')).smul hg
  exact (continuousOn_const.sub ((hq.sub ((hq.inner hn).smul hn)).norm.pow 2)).sqrt

/-- The actual induced metric is strictly positive on every nonzero tangent;
no positivity is inferred merely from a total square root. -/
theorem tangentMetric_pos (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h)
    (v : Pilot3Space) (hv : v ≠ 0) : 0 < pilot3TangentMetric f x v v := by
  have hvp := norm_pos_iff.mpr hv
  have hq := (hf.face_slopes_lt_one x hx).1
  have hcs := abs_real_inner_le_norm (pilot3Gradient f x) v
  have hb : ‖pilot3Gradient f x‖ * ‖v‖ < ‖v‖ := by nlinarith
  have hs := (sq_lt_sq₀ (abs_nonneg (inner (𝕜 := ℝ) (pilot3Gradient f x) v))
    (norm_nonneg v)).mpr (hcs.trans_lt hb)
  rw [sq_abs] at hs
  simp only [pilot3TangentMetric, pilot3_differential_eq_inner, real_inner_self_eq_norm_sq]
  nlinarith

/-- Both future normals are orthogonal to the actual joint tangent. -/
theorem normals_orthogonal (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h)
    (v : Pilot3Space) (hv : fderiv ℝ h x v = 0) :
    dimensionMinkowski 2 (pilot3Normal f x) (fderiv ℝ f x v, v) = 0 ∧
    dimensionMinkowski 2 (pilot3Normal (fun y => f y - h y) x) (fderiv ℝ f x v, v) = 0 := by
  rw [pilot3_differential_eq_inner] at hv ⊢
  refine ⟨pilot3UnitNormal_orthogonal _ _, ?_⟩
  have he : pilot3GraphTangent (pilot3Gradient (fun y => f y - h y) x) v =
      pilot3GraphTangent (pilot3Gradient f x) v := by
    rw [pilot3GraphTangent, hf.gradient_past x hx.1, inner_sub_left, hv, sub_zero]
    rfl
  change dimensionMinkowski 2 (pilot3UnitNormal _) (pilot3GraphTangent _ _) = 0
  rw [← he]
  exact pilot3UnitNormal_orthogonal _ _

end SmoothPilot3
end BoundaryDraft
