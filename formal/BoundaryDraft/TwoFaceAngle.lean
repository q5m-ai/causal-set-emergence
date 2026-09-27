import BoundaryDraft.JointMetric

/-!
# Derived two-face nondegeneracy and angle geometry

All differential bounds follow from the original slope budget. In particular,
the positive part is differentiated only in the open positive region.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

@[simp] theorem graphGradient_zero (x : JointSpace) :
    graphGradient (fun _ => 0) x = 0 := by simp [graphGradient, gradient]

theorem graphGradient_sub {h f : Spatial → ℝ} {x : JointSpace}
    (hf : DifferentiableAt ℝ (fun y : JointSpace => f y) x)
    (hh : DifferentiableAt ℝ (fun y : JointSpace => h y) x) :
    graphGradient (fun y => f y - h y) x = graphGradient f x - graphGradient h x := by
  simp only [graphGradient, gradient, fderiv_sub hf hh, map_sub]

theorem continuousOn_graphGradient_of_smooth {f : Spatial → ℝ} {s : Set JointSpace}
    (hf : ∀ x ∈ s, ContDiffAt ℝ 3 (fun y : JointSpace => f y) x) :
    ContinuousOn (graphGradient f) s := by
  apply (InnerProductSpace.toDual ℝ JointSpace).symm.continuous.comp_continuousOn
  intro x hx
  exact ((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt

/-- Orthogonal projection onto the plane with unit normal `n`. -/
theorem joint_tangential_norm_sq (q n : JointSpace) (hn : ‖n‖ = 1) :
    ‖q - inner (𝕜 := ℝ) q n • n‖ ^ 2 = ‖q‖ ^ 2 - inner (𝕜 := ℝ) q n ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hn]
  ring

theorem joint_tangential_norm_le (q n : JointSpace) (hn : ‖n‖ = 1) :
    ‖q - inner (𝕜 := ℝ) q n • n‖ ≤ ‖q‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [joint_tangential_norm_sq q n hn]
  linarith [sq_nonneg (inner (𝕜 := ℝ) q n)]

namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem gradient_past (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    graphGradient (fun y => f y - h y) x = graphGradient f x - graphGradient h x :=
  graphGradient_sub ((hf.smooth_future x hx).differentiableAt (by norm_num))
    ((hf.smooth_near x hx).differentiableAt (by norm_num))

/-- A common strict bound for both face slopes, valid up to the joint. -/
theorem exists_face_slope_bound : ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
    ∀ x ∈ graphClosedPositive h,
      ‖graphGradient f x‖ ≤ k ∧ ‖graphGradient (fun y => f y - h y) x‖ ≤ k := by
  obtain ⟨κ, η, hκ, hη, hbudget, hLip, hfLip⟩ := hf.slope_budget
  have hopen : IsOpen {x : JointSpace | 0 < h x} :=
    hf.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)
  have hhL : LipschitzOnWith ⟨κ, hκ⟩ (fun x : JointSpace => h x) {x | 0 < h x} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have he := hLip x y
    rw [max_eq_right hx.le, max_eq_right hy.le] at he
    change |h x - h y| ≤ κ * ‖y - x‖ at he
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using he
  have hfL : LipschitzWith ⟨η, hη⟩ (fun x : JointSpace => f x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := hfLip x y
    change |f x - f y| ≤ η * ‖y - x‖ at he
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using he
  have hhbound : ∀ x ∈ graphClosedPositive h, ‖graphGradient h x‖ ≤ κ := by
    intro x hx
    rw [← graphSlope, graphSlope_eq_norm_fderiv]
    apply le_on_closure (fun y hy => norm_fderiv_le_of_lipschitzOn ℝ
      (hopen.mem_nhds hy) hhL) hf.toAdmissibleGraphCap.continuousOn_fderiv_closedPositive.norm
      continuousOn_const hx
  have hfbound (x : JointSpace) : ‖graphGradient f x‖ ≤ η := by
    rw [← graphSlope, graphSlope_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hfL
  refine ⟨κ + η, add_nonneg hκ hη, hbudget, ?_⟩
  intro x hx
  refine ⟨by linarith [hfbound x], ?_⟩
  rw [hf.gradient_past x hx]
  exact (norm_sub_le _ _).trans (by linarith [hfbound x, hhbound x hx])

theorem face_slopes_lt_one (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    ‖graphGradient f x‖ < 1 ∧ ‖graphGradient (fun y => f y - h y) x‖ < 1 := by
  obtain ⟨k, _, hk, hb⟩ := hf.exists_face_slope_bound
  exact ⟨((hb x hx).1).trans_lt hk, ((hb x hx).2).trans_lt hk⟩

/-- Both normals are future-directed and unit timelike; this fixes the sign. -/
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
  have hp := hf.toAdmissibleGraphCap.graphSlope_pos x hx
  simp [graphSlope, hg] at hp

/-- The invariant quotient is the actual hyperbolic cotangent on a strictly
positive angle branch. -/
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
    (hf.toAdmissibleGraphCap.graphInward_norm x hx)
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
    (hg.norm.inv₀ (fun x hx => (hf.toAdmissibleGraphCap.graphSlope_pos x hx).ne')).smul hg
  exact (continuousOn_const.sub ((hq.sub ((hq.inner hn).smul hn)).norm.pow 2)).sqrt

/-- Each fixed compact geometry has strict uniform margins; no uniformity over
families approaching tangency or null faces is claimed. Empty joints are allowed. -/
theorem exists_joint_margins : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ graphJoint h,
    1 + ε ≤ twoFaceCosh h f x ∧ ε ≤ twoFaceAreaDensity h f x := by
  by_cases hne : (graphJoint h).Nonempty
  · obtain ⟨a, ha, hamin⟩ := hf.toAdmissibleGraphCap.isCompact_joint.exists_isMinOn hne
      (hf.continuousOn_cosh.sub (continuousOn_const (c := (1 : ℝ))))
    obtain ⟨b, hb, hbmin⟩ := hf.toAdmissibleGraphCap.isCompact_joint.exists_isMinOn hne
      hf.continuousOn_areaDensity
    refine ⟨min (twoFaceCosh h f a - 1) (twoFaceAreaDensity h f b),
      lt_min (by linarith [hf.cosh_gt_one a ha]) (hf.areaDensity_pos b hb), ?_⟩
    intro x hx
    constructor
    · have hmin := hamin hx
      have hm := min_le_left (twoFaceCosh h f a - 1) (twoFaceAreaDensity h f b)
      dsimp at hmin
      linarith
    · exact (min_le_right _ _).trans (hbmin hx)
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- The joint tangent metric is positive definite and both actual face normals
are orthogonal to it. No abstract assigned normal is used here. -/
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

end AdmissibleTwoFace
end BoundaryDraft
