import BoundaryDraft.IndependentFaceAngle
import BoundaryDraft.GraphExamples
import BoundaryDraft.EllipsoidHausdorff

/-!
# Steep symmetric capsules and old-class compatibility

The symmetric family uses two clipped envelopes with independent strict
bounds. Its raw thickness can have slope greater than one. The origin stays
a positive-height critical point; no cap reduction is applied to that height.
-/

open Set MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace BoundaryDraft

/-- Regular compact ellipsoid heights require positive axes, not cap spacelikeness. -/
theorem ellipsoid_regularHeight (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 0 < b i) : RegularHeight (ellipsoidProfile a b) where
  bounded_positive := isBounded_ellipsoid_positive a b ha hb
  smooth_near := fun x _ => ((contDiff_ellipsoidProfile a b).of_le (by norm_num)).contDiffAt
  boundary_zero := fun _ hx =>
    (frontier_lt_subset_eq continuous_const (continuous_ellipsoidProfile a b) hx).symm
  regular_zero := by
    intro x _ hx
    apply ellipsoid_joint_regular a b ha hb x
    rw [ellipsoidJoint_eq_zero a b ha]
    exact hx

/-- The actual joint identification only needs regular compact height geometry. -/
theorem graphJoint_ellipsoid_regular (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) : graphJoint (ellipsoidProfile a b) = ellipsoidJoint b := by
  let e := euclideanAxisEquiv b hb
  have hiff (x : JointSpace) : 0 < ellipsoidProfile a b x ↔ ‖e.symm x‖ < 1 := by
    rw [ellipsoidProfile_pos_iff a b ha, ← ellipsoidRadius_sq]
    change ‖e.symm x‖ ^ 2 < 1 ↔ ‖e.symm x‖ < 1
    constructor <;> intro hx <;> nlinarith [norm_nonneg (e.symm x)]
  have hpos : {x : JointSpace | 0 < ellipsoidProfile a b x} = e '' Metric.ball 0 1 := by
    ext x
    rw [mem_setOf_eq, hiff]
    constructor
    · intro hx
      exact ⟨e.symm x, mem_ball_zero_iff.mpr hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [e.symm_apply_apply] using mem_ball_zero_iff.mp hy
  rw [(ellipsoid_regularHeight a b ha hb).graphJoint_eq_frontier, hpos]
  change frontier (e.toHomeomorph '' Metric.ball 0 1) = _
  rw [← e.toHomeomorph.image_frontier,
    frontier_ball (0 : JointSpace) (by norm_num : (1 : ℝ) ≠ 0)]
  exact ellipsoidAxisLinear_image_sphere b hb

private theorem ellipsoid_half (a : ℝ) (b : Fin 3 → ℝ) (x : Spatial) :
    ellipsoidProfile a b x = 2 * ellipsoidProfile (a / 2) b x := by
  unfold ellipsoidProfile
  ring

/-- Independent envelopes admit axes strictly larger than `a`, rather than
larger than `2*a`. Both raw faces are the symmetric half-height graphs. -/
theorem symmetricEllipsoid_independent (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, a < b i) :
    AdmissibleIndependentTwoFace (ellipsoidProfile a b) (ellipsoidProfile (a / 2) b) := by
  have hhalf := ellipsoid_admissible (a / 2) b (half_pos ha) (fun i => by linarith [hb i])
  have hr := ellipsoid_regularHeight a b ha (fun i => ha.trans (hb i))
  refine { hr with
    smooth_future := fun x _ => ((contDiff_ellipsoidProfile (a / 2) b).of_le (by norm_num)).contDiffAt
    envelopes := ?_ }
  obtain ⟨κ, hκ, hk, hl⟩ := hhalf.lipschitz_positivePart
  refine ⟨fun x => -max 0 (ellipsoidProfile (a / 2) b x),
    fun x => max 0 (ellipsoidProfile (a / 2) b x), ?_, ⟨κ, hκ, hk, hl⟩, ?_, ?_⟩
  · refine ⟨κ, hκ, hk, fun x y => ?_⟩
    simpa only [neg_sub_neg, abs_sub_comm] using hl x y
  · intro x
    dsimp only
    rw [ellipsoid_half a b x]
    rcases le_total 0 (ellipsoidProfile (a / 2) b x) with hp | hp
    · rw [max_eq_right hp, max_eq_right (mul_nonneg (by norm_num) hp)]
      ring
    · rw [max_eq_left hp, max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hp)]
      ring
  · intro x hx
    have hp := hr.nonneg_on_closedPositive x hx
    rw [ellipsoid_half a b x] at hp
    exact max_eq_right (by linarith)

/-- Opposite half-height face gradients give the actual symmetric normal angle. -/
theorem symmetricEllipsoid_cosh (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, a < b i) (x : JointSpace)
    (hx : x ∈ graphClosedPositive (ellipsoidProfile a b)) :
    twoFaceCosh (ellipsoidProfile a b) (ellipsoidProfile (a / 2) b) x =
      (1 + ‖graphGradient (ellipsoidProfile (a / 2) b) x‖ ^ 2) /
        (1 - ‖graphGradient (ellipsoidProfile (a / 2) b) x‖ ^ 2) := by
  have hf := symmetricEllipsoid_independent a b ha hb
  have hp : graphGradient (fun y => ellipsoidProfile (a / 2) b y - ellipsoidProfile a b y) x =
      -graphGradient (ellipsoidProfile (a / 2) b) x := by
    rw [hf.gradient_past x hx, graphGradient_ellipsoid, graphGradient_ellipsoid]
    ext i
    change (-2 * (a / 2) * x i / b i ^ 2) - (-2 * a * x i / b i ^ 2) =
      -(-2 * (a / 2) * x i / b i ^ 2)
    ring
  have hk := (hf.face_slopes_lt_one x hx).1
  have hd : 0 ≤ 1 - ‖graphGradient (ellipsoidProfile (a / 2) b) x‖ ^ 2 := by
    nlinarith [norm_nonneg (graphGradient (ellipsoidProfile (a / 2) b) x)]
  change minkowskiInner (jointUnitNormal _) (jointUnitNormal _) = _
  rw [jointUnitNormal_inner, hp, norm_neg, inner_neg_left, real_inner_self_eq_norm_sq,
    sub_neg_eq_add, ← pow_two, Real.sq_sqrt hd]

/-- The fixed witness from E9, in the original spatial coordinate convention. -/
def steepCapsuleHeight : Spatial → ℝ := ellipsoidProfile (3 / 4) (fun _ => 1)

def steepCapsuleFuture : Spatial → ℝ := ellipsoidProfile (3 / 8) (fun _ => 1)

theorem steepCapsule_height (x : JointSpace) :
    steepCapsuleHeight x = (3 / 4 : ℝ) * (1 - ‖x‖ ^ 2) := by
  simp [steepCapsuleHeight, ellipsoidProfile, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]

theorem steepCapsule_future (x : Spatial) :
    steepCapsuleFuture x = steepCapsuleHeight x / 2 := by
  unfold steepCapsuleFuture steepCapsuleHeight ellipsoidProfile
  ring

/-- The displayed causal envelopes are precisely plus/minus half the positive height. -/
theorem steepCapsule_upper_envelope (x : Spatial) :
    max 0 (steepCapsuleFuture x) = max 0 (steepCapsuleHeight x) / 2 := by
  rw [steepCapsule_future]
  rcases le_total 0 (steepCapsuleHeight x) with hp | hp
  · rw [max_eq_right hp, max_eq_right (div_nonneg hp (by norm_num))]
  · rw [max_eq_left hp, max_eq_left (div_nonpos_of_nonpos_of_nonneg hp (by norm_num)), zero_div]

theorem steepCapsule_admissible :
    AdmissibleIndependentTwoFace steepCapsuleHeight steepCapsuleFuture := by
  simpa only [steepCapsuleHeight, steepCapsuleFuture,
    show (3 / 4 : ℝ) / 2 = 3 / 8 by norm_num] using
    symmetricEllipsoid_independent (3 / 4) (fun _ => 1) (by norm_num) (fun _ => by norm_num)

/-- The Euclidean gradient, not a coordinate supremum-norm substitute. -/
theorem steepCapsule_gradient (x : JointSpace) :
    graphGradient steepCapsuleHeight x = (- (3 / 2 : ℝ)) • x := by
  rw [steepCapsuleHeight, graphGradient_ellipsoid]
  ext i
  change -2 * (3 / 4 : ℝ) * x i / 1 ^ 2 = -(3 / 2 : ℝ) * x i
  ring

/-- The whole unit sphere has thickness slope three-halves. -/
theorem steepCapsule_slope (x : JointSpace) (hx : ‖x‖ = 1) :
    graphSlope steepCapsuleHeight x = 3 / 2 := by
  rw [graphSlope, steepCapsule_gradient, norm_smul, hx]
  norm_num

/-- Positive-height critical points have not been removed from the new class. -/
theorem steepCapsule_positive_critical : steepCapsuleHeight 0 = 3 / 4 ∧
    fderiv ℝ (fun x : JointSpace => steepCapsuleHeight x) 0 = 0 := by
  constructor
  · norm_num [steepCapsuleHeight, ellipsoidProfile]
  · ext v
    rw [graph_differential_eq_inner, steepCapsule_gradient]
    simp

/-- A direct positive-height point already violates the old strict cap slope.
Thus this is a genuinely new instance, not an old member under a new name. -/
theorem steepCapsule_not_old_cap : ¬AdmissibleGraphCap steepCapsuleHeight := by
  intro hh
  let x : JointSpace := EuclideanSpace.single 0 (3 / 4)
  have hn : ‖x‖ = 3 / 4 := by norm_num [x, EuclideanSpace.norm_single]
  have hx : x ∈ graphClosedPositive steepCapsuleHeight := by
    apply subset_closure
    change 0 < steepCapsuleHeight x
    rw [steepCapsule_height, hn]
    norm_num
  have hb := hh.graphSlope_lt_one x hx
  rw [graphSlope, steepCapsule_gradient, norm_smul, hn] at hb
  norm_num at hb

theorem steepCapsule_not_old_twoFace : ¬AdmissibleTwoFace steepCapsuleHeight steepCapsuleFuture :=
  fun hh => steepCapsule_not_old_cap hh.toAdmissibleGraphCap

/-- Every original unequal-axis planar instance keeps its original assumptions. -/
theorem planarEllipsoid_independent (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    AdmissibleIndependentTwoFace (ellipsoidProfile a b) (fun _ => 0) :=
  (ellipsoid_admissible a b ha hb).twoFace_planar.toIndependentTwoFace

end BoundaryDraft
