import BoundaryDraft.IndependentFaceGeometry
import BoundaryDraft.TwoFaceAngle

/-!
# Independent spacelike face bounds and positive joint angle

Differentiate the envelope estimate only on the open positive region, then
extend the raw-germ differential bound to its closure. The clipped envelopes
are never differentiated at the joint. The height itself need not be spacelike.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A raw smooth germ inherits the bound of an agreeing Lipschitz envelope.
Agreement is required only on the closed positive region. -/
theorem RegularHeight.gradient_bound_of_envelope {h f g : Spatial → ℝ}
    (hh : RegularHeight h)
    (hs : ∀ x ∈ graphClosedPositive h, ContDiffAt ℝ 3 (fun y : JointSpace => f y) x)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hl : ∀ x y, |g x - g y| ≤ κ * spatialDistance x y)
    (he : ∀ x : JointSpace, x ∈ graphClosedPositive h → g x = f x) :
    ∀ x ∈ graphClosedPositive h, ‖graphGradient f x‖ ≤ κ := by
  have hopen : IsOpen {x : JointSpace | 0 < h x} :=
    hh.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)
  have hLip : LipschitzOnWith ⟨κ, hκ⟩ (fun x : JointSpace => f x) {x | 0 < h x} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hb := hl x y
    rw [he x (subset_closure hx), he y (subset_closure hy)] at hb
    change |f x - f y| ≤ κ * ‖y - x‖ at hb
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using hb
  intro x hx
  rw [← graphSlope, graphSlope_eq_norm_fderiv]
  have hc : ContinuousOn (fderiv ℝ (fun y : JointSpace => f y)) (graphClosedPositive h) :=
    fun y hy => ((hs y hy).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  exact le_on_closure (fun y hy => norm_fderiv_le_of_lipschitzOn ℝ
    (hopen.mem_nhds hy) hLip) hc.norm continuousOn_const hx

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

theorem gradient_past (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    graphGradient (fun y => f y - h y) x = graphGradient f x - graphGradient h x :=
  graphGradient_sub ((hf.smooth_future x hx).differentiableAt (by norm_num))
    ((hf.smooth_near x hx).differentiableAt (by norm_num))

/-- The maximum of two independent strict bounds, NOT their sum, controls the faces. -/
theorem exists_face_slope_bound : ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
    ∀ x ∈ graphClosedPositive h,
      ‖graphGradient f x‖ ≤ k ∧ ‖graphGradient (fun y => f y - h y) x‖ ≤ k := by
  obtain ⟨a, ha, ha1, hl⟩ := hf.strictGraphLipschitz_lower
  obtain ⟨b, hb, hb1, hu⟩ := hf.strictGraphLipschitz_upper
  have hupper := hf.toRegularHeight.gradient_bound_of_envelope hf.smooth_future hb hu hf.upper_eq
  have hlower := hf.toRegularHeight.gradient_bound_of_envelope
    (fun x hx => (hf.smooth_future x hx).sub (hf.smooth_near x hx)) ha hl hf.lower_eq
  exact ⟨max a b, ha.trans (le_max_left _ _), max_lt ha1 hb1,
    fun x hx => ⟨(hupper x hx).trans (le_max_right _ _),
      (hlower x hx).trans (le_max_left _ _)⟩⟩

theorem face_slopes_lt_one (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    ‖graphGradient f x‖ < 1 ∧ ‖graphGradient (fun y => f y - h y) x‖ < 1 := by
  obtain ⟨k, _, hk, hb⟩ := hf.exists_face_slope_bound
  exact ⟨((hb x hx).1).trans_lt hk, ((hb x hx).2).trans_lt hk⟩

theorem normals_future_unit (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    (0 < twoFaceNormal f x 0 ∧ minkowskiInner (twoFaceNormal f x) (twoFaceNormal f x) = 1) ∧
    (0 < twoFaceNormal (fun y => f y - h y) x 0 ∧
      minkowskiInner (twoFaceNormal (fun y => f y - h y) x)
        (twoFaceNormal (fun y => f y - h y) x) = 1) :=
  ⟨jointUnitNormal_future_unit (hf.face_slopes_lt_one x hx).1,
    jointUnitNormal_future_unit (hf.face_slopes_lt_one x hx).2⟩

theorem cosh_gt_one (x : JointSpace) (hx : x ∈ graphJoint h) : 1 < twoFaceCosh h f x := by
  apply jointUnitNormal_inner_gt_one (hf.face_slopes_lt_one x hx.1).2
    (hf.face_slopes_lt_one x hx.1).1
  rw [hf.gradient_past x hx.1]
  intro he
  have hg : graphGradient h x = 0 := sub_eq_self.mp he
  have hp := hf.toRegularHeight.graphSlope_pos x hx
  simp [graphSlope, hg] at hp

/-- Independence of the two future unit normals, expressed without choosing
coordinates on their span. -/
theorem normals_independent (x : JointSpace) (hx : x ∈ graphJoint h) (a b : ℝ)
    (he : a • twoFaceNormal (fun y => f y - h y) x + b • twoFaceNormal f x = 0) :
    a = 0 ∧ b = 0 := by
  have hn := hf.normals_future_unit x hx.1
  have hp := congrArg (fun v => minkowskiInner v (twoFaceNormal f x)) he
  have hm := congrArg (fun v => minkowskiInner v (twoFaceNormal (fun y => f y - h y) x)) he
  dsimp only at hp hm
  have hz (v : Spacetime) : minkowskiInner 0 v = 0 := by simp [minkowskiInner]
  rw [minkowskiInner_add_left, minkowskiInner_smul_left, minkowskiInner_smul_left,
    hn.1.2, mul_one, hz] at hp
  rw [minkowskiInner_add_left, minkowskiInner_smul_left, minkowskiInner_smul_left,
    hn.2.2, mul_one, minkowskiInner_symm (twoFaceNormal f x), hz] at hm
  change a * twoFaceCosh h f x + b = 0 at hp
  change a + b * twoFaceCosh h f x = 0 at hm
  have hc : twoFaceCosh h f x ^ 2 - 1 ≠ 0 := by nlinarith [hf.cosh_gt_one x hx]
  have ha : a * (twoFaceCosh h f x ^ 2 - 1) = 0 := by
    nlinarith [congrArg (fun t => t * twoFaceCosh h f x) hp]
  have ha0 := (mul_eq_zero.mp ha).resolve_right hc
  exact ⟨ha0, by simpa [ha0] using hp⟩

theorem angle_identities (x : JointSpace) (hx : x ∈ graphJoint h) :
    0 < jointAngle (twoFaceCosh h f x) ∧
    Real.cosh (jointAngle (twoFaceCosh h f x)) = twoFaceCosh h f x ∧
    Real.sinh (jointAngle (twoFaceCosh h f x)) = Real.sqrt (twoFaceCosh h f x ^ 2 - 1) ∧
    Real.cosh (jointAngle (twoFaceCosh h f x)) /
      Real.sinh (jointAngle (twoFaceCosh h f x)) = twoFaceWeight h f x :=
  jointAngle_identities (hf.cosh_gt_one x hx)

theorem areaDensity_pos (x : JointSpace) (hx : x ∈ graphJoint h) :
    0 < twoFaceAreaDensity h f x := by
  have hb := joint_tangential_norm_le (graphGradient f x) (graphInward h x)
    (hf.toRegularHeight.graphInward_norm x hx)
  have hq := (hf.face_slopes_lt_one x hx.1).1
  apply Real.sqrt_pos.mpr
  change 0 < 1 - ‖twoFaceTangentialGradient h f x‖ ^ 2
  change ‖twoFaceTangentialGradient h f x‖ ≤ ‖graphGradient f x‖ at hb
  nlinarith [norm_nonneg (twoFaceTangentialGradient h f x)]

theorem continuousOn_cosh : ContinuousOn (twoFaceCosh h f) (graphJoint h) := by
  have hq := continuousOn_graphGradient_of_smooth hf.smooth_future
  have hp := continuousOn_graphGradient_of_smooth
    (fun x hx => (hf.smooth_future x hx).sub (hf.smooth_near x hx))
  have hc : ContinuousOn (fun x =>
      (1 - inner (𝕜 := ℝ) (graphGradient (fun y => f y - h y) x) (graphGradient f x)) /
        (Real.sqrt (1 - ‖graphGradient (fun y => f y - h y) x‖ ^ 2) *
          Real.sqrt (1 - ‖graphGradient f x‖ ^ 2))) (graphClosedPositive h) := by
    apply (continuousOn_const.sub (hp.inner hq)).div
      (((continuousOn_const.sub (hp.norm.pow 2)).sqrt).mul
        ((continuousOn_const.sub (hq.norm.pow 2)).sqrt))
    intro x hx
    obtain ⟨hq1, hp1⟩ := hf.face_slopes_lt_one x hx
    apply mul_ne_zero <;> apply (Real.sqrt_pos.mpr ?_).ne'
    · exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr
        (by simpa only [abs_of_nonneg (norm_nonneg _)] using hp1))
    · exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr
        (by simpa only [abs_of_nonneg (norm_nonneg _)] using hq1))
  have he (x : JointSpace) : twoFaceCosh h f x =
      (1 - inner (𝕜 := ℝ) (graphGradient (fun y => f y - h y) x) (graphGradient f x)) /
        (Real.sqrt (1 - ‖graphGradient (fun y => f y - h y) x‖ ^ 2) *
          Real.sqrt (1 - ‖graphGradient f x‖ ^ 2)) := jointUnitNormal_inner _ _
  change ContinuousOn (fun x => twoFaceCosh h f x) (graphJoint h)
  simp_rw [he]
  exact hc.mono inter_subset_left

theorem continuousOn_weight : ContinuousOn (twoFaceWeight h f) (graphJoint h) := by
  apply hf.continuousOn_cosh.div ((hf.continuousOn_cosh.pow 2).sub continuousOn_const).sqrt
  intro x hx
  apply (Real.sqrt_pos.mpr ?_).ne'
  nlinarith [hf.cosh_gt_one x hx]

theorem continuousOn_areaDensity : ContinuousOn (twoFaceAreaDensity h f) (graphJoint h) := by
  have hq : ContinuousOn (graphGradient f) (graphJoint h) :=
    (continuousOn_graphGradient_of_smooth hf.smooth_future).mono inter_subset_left
  have hg : ContinuousOn (graphGradient h) (graphJoint h) :=
    (continuousOn_graphGradient_of_smooth hf.smooth_near).mono inter_subset_left
  have hn : ContinuousOn (graphInward h) (graphJoint h) :=
    (hg.norm.inv₀ (fun x hx => (hf.toRegularHeight.graphSlope_pos x hx).ne')).smul hg
  exact (continuousOn_const.sub ((hq.sub ((hq.inner hn).smul hn)).norm.pow 2)).sqrt

/-- The induced tangent metric is positive definite; both actual face normals
are orthogonal to it. -/
theorem joint_tangent_geometry (x : JointSpace) (hx : x ∈ graphJoint h)
    (v : JointSpace) (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0) (hne : v ≠ 0) :
    0 < -minkowskiInner (jointGraphTangent (graphGradient f x) v)
      (jointGraphTangent (graphGradient f x) v) ∧
    minkowskiInner (twoFaceNormal f x) (jointGraphTangent (graphGradient f x) v) = 0 ∧
    minkowskiInner (twoFaceNormal (fun y => f y - h y) x)
      (jointGraphTangent (graphGradient f x) v) = 0 := by
  refine ⟨jointGraphTangent_spacelike (hf.face_slopes_lt_one x hx.1).1 hne,
    jointUnitNormal_orthogonal _ _, ?_⟩
  have he : jointGraphTangent (graphGradient (fun y => f y - h y) x) v =
      jointGraphTangent (graphGradient f x) v := by
    rw [jointGraphTangent, hf.gradient_past x hx.1, inner_sub_left,
      ← graph_differential_eq_inner h x v, hv, sub_zero]
    rfl
  rw [← he]
  exact jointUnitNormal_orthogonal _ _

end AdmissibleIndependentTwoFace
end BoundaryDraft
