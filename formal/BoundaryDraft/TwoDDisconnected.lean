import BoundaryDraft.TwoDExamples
import BoundaryDraft.TwoDLimit

/-!
# A genuine disconnected, curved, four-endpoint 2D regression family

The raw maximum is smooth near the entire closed positive region. Its
irrelevant exterior bisector need not be smooth. Both positive-height critical
points and the same globally curved future are retained.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

def twoDShiftedIntervalHeight (a x : TwoDSpace) : ℝ := twoDIntervalHeight (x - a)

theorem twoDShiftedInterval_smooth (a : TwoDSpace) : ContDiff ℝ ∞ (twoDShiftedIntervalHeight a) :=
  twoDIntervalHeight_smooth.comp (contDiff_id.sub contDiff_const)

theorem twoDShiftedInterval_positive (a : TwoDSpace) :
    {x | 0 < twoDShiftedIntervalHeight a x} = Metric.ball a 1 := by
  ext x
  change (x - a ∈ {y | 0 < twoDIntervalHeight y}) ↔ _
  rw [twoDIntervalHeight_positive]
  simp only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero]

theorem twoDShiftedInterval_closedPositive (a : TwoDSpace) :
    twoDClosedPositive (twoDShiftedIntervalHeight a) = Metric.closedBall a 1 := by
  rw [twoDClosedPositive, twoDShiftedInterval_positive, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem twoDShiftedInterval_nonneg_iff (a x : TwoDSpace) :
    0 ≤ twoDShiftedIntervalHeight a x ↔ x ∈ Metric.closedBall a 1 := by
  simp only [twoDShiftedIntervalHeight, twoDIntervalHeight, Metric.mem_closedBall, dist_eq_norm]
  constructor <;> intro hx <;> nlinarith [norm_nonneg (x - a)]

theorem twoDShiftedInterval_fderiv (a x v : TwoDSpace) :
    fderiv ℝ (twoDShiftedIntervalHeight a) x v = -(1 / 2 : ℝ) * inner (𝕜 := ℝ) (x - a) v := by
  change fderiv ℝ (fun y => twoDIntervalHeight (y - a)) x v = _
  rw [fderiv_comp_sub]
  exact twoDIntervalHeight_fderiv _ _

theorem twoDShiftedInterval_lipschitz (a x y : TwoDSpace) :
    |max 0 (twoDShiftedIntervalHeight a x) - max 0 (twoDShiftedIntervalHeight a y)| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  simpa only [twoDShiftedIntervalHeight, sub_sub_sub_cancel_right] using twoDIntervalHeight_lipschitz (x - a) (y - a)

theorem twoDShiftedIntervalSine_admissible (a : TwoDSpace) : SmoothTwoD (twoDShiftedIntervalHeight a) twoDSineFuture where
  bounded_positive := by rw [twoDShiftedInterval_positive]; exact Metric.isBounded_ball
  smooth_height := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, (twoDShiftedInterval_smooth a).contDiffOn⟩
  zero_frontier := fun x hx => (frontier_lt_subset_eq continuous_const (twoDShiftedInterval_smooth a).continuous hx).symm
  regular_zero := by
    intro x _ hz hd
    have he := twoDShiftedInterval_fderiv a x (x - a)
    rw [hd, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at he
    dsimp [twoDShiftedIntervalHeight, twoDIntervalHeight] at hz
    linarith
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, twoDSineFuture_smooth.contDiffOn⟩
  slope_budget := ⟨1 / 2, 1 / 8, by norm_num, by norm_num, by norm_num,
    twoDShiftedInterval_lipschitz a, twoDSineFuture_lipschitz⟩

def twoDOtherCenter : TwoDSpace := twoDLine.symm 4

theorem twoDOtherCenter_norm : ‖twoDOtherCenter‖ = 4 := by simp [twoDOtherCenter]

def twoDDisconnectedHeight (x : TwoDSpace) : ℝ :=
  max (twoDShiftedIntervalHeight 0 x) (twoDShiftedIntervalHeight twoDOtherCenter x)

theorem twoDDisconnected_separated :
    Disjoint (Metric.closedBall (0 : TwoDSpace) 1) (Metric.closedBall twoDOtherCenter 1) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [dist_zero_left, twoDOtherCenter_norm]
  norm_num

theorem twoDDisconnected_positive : {x | 0 < twoDDisconnectedHeight x} =
    Metric.ball (0 : TwoDSpace) 1 ∪ Metric.ball twoDOtherCenter 1 := by
  ext x
  change 0 < max (twoDShiftedIntervalHeight 0 x) (twoDShiftedIntervalHeight twoDOtherCenter x) ↔ _
  rw [lt_max_iff]
  change x ∈ {x | 0 < twoDShiftedIntervalHeight 0 x} ∨ x ∈ {x | 0 < twoDShiftedIntervalHeight twoDOtherCenter x} ↔ _
  rw [twoDShiftedInterval_positive, twoDShiftedInterval_positive]
  rfl

theorem twoDDisconnected_closedPositive : twoDClosedPositive twoDDisconnectedHeight =
    Metric.closedBall (0 : TwoDSpace) 1 ∪ Metric.closedBall twoDOtherCenter 1 := by
  rw [twoDClosedPositive, twoDDisconnected_positive, closure_union,
    closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

private theorem disconnected_right_neg (x : TwoDSpace) (hx : x ∈ Metric.closedBall (0 : TwoDSpace) 1) :
    twoDShiftedIntervalHeight twoDOtherCenter x < 0 := by
  apply lt_of_not_ge
  intro hn
  exact Set.disjoint_left.mp twoDDisconnected_separated hx ((twoDShiftedInterval_nonneg_iff _ _).mp hn)

private theorem disconnected_left_neg (x : TwoDSpace) (hx : x ∈ Metric.closedBall twoDOtherCenter 1) :
    twoDShiftedIntervalHeight 0 x < 0 := by
  apply lt_of_not_ge
  intro hn
  exact Set.disjoint_left.mp twoDDisconnected_separated ((twoDShiftedInterval_nonneg_iff _ _).mp hn) hx

private theorem disconnected_left_lt (x : TwoDSpace) (hx : x ∈ Metric.closedBall (0 : TwoDSpace) 1) :
    twoDShiftedIntervalHeight twoDOtherCenter x < twoDShiftedIntervalHeight 0 x :=
  (disconnected_right_neg x hx).trans_le ((twoDShiftedInterval_nonneg_iff _ _).mpr hx)

private theorem disconnected_right_lt (x : TwoDSpace) (hx : x ∈ Metric.closedBall twoDOtherCenter 1) :
    twoDShiftedIntervalHeight 0 x < twoDShiftedIntervalHeight twoDOtherCenter x :=
  (disconnected_left_neg x hx).trans_le ((twoDShiftedInterval_nonneg_iff _ _).mpr hx)

theorem twoDDisconnected_eq_left_near (x : TwoDSpace) (hx : x ∈ Metric.closedBall (0 : TwoDSpace) 1) :
    twoDDisconnectedHeight =ᶠ[𝓝 x] twoDShiftedIntervalHeight 0 := by
  filter_upwards [(isOpen_lt (twoDShiftedInterval_smooth twoDOtherCenter).continuous
    (twoDShiftedInterval_smooth 0).continuous).mem_nhds (disconnected_left_lt x hx)] with y hy
  exact max_eq_left_of_lt hy

theorem twoDDisconnected_eq_right_near (x : TwoDSpace) (hx : x ∈ Metric.closedBall twoDOtherCenter 1) :
    twoDDisconnectedHeight =ᶠ[𝓝 x] twoDShiftedIntervalHeight twoDOtherCenter := by
  filter_upwards [(isOpen_lt (twoDShiftedInterval_smooth 0).continuous
    (twoDShiftedInterval_smooth twoDOtherCenter).continuous).mem_nhds (disconnected_right_lt x hx)] with y hy
  exact max_eq_right_of_lt hy

theorem twoDDisconnected_lipschitz (x y : TwoDSpace) :
    |max 0 (twoDDisconnectedHeight x) - max 0 (twoDDisconnectedHeight y)| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  have he (a b : ℝ) : max 0 (max a b) = max (max 0 a) (max 0 b) := by simp [max_assoc, max_left_comm]
  simp only [twoDDisconnectedHeight, he]
  exact (abs_max_sub_max_le_max _ _ _ _).trans
    (max_le (twoDShiftedInterval_lipschitz 0 x y) (twoDShiftedInterval_lipschitz twoDOtherCenter x y))

theorem twoDDisconnectedSine_admissible : SmoothTwoD twoDDisconnectedHeight twoDSineFuture where
  bounded_positive := by rw [twoDDisconnected_positive]; exact Metric.isBounded_ball.union Metric.isBounded_ball
  smooth_height := by
    intro x hx
    rw [twoDDisconnected_closedPositive] at hx
    rcases hx with hx | hx
    · exact ⟨{y | twoDShiftedIntervalHeight twoDOtherCenter y < twoDShiftedIntervalHeight 0 y},
        isOpen_lt (twoDShiftedInterval_smooth twoDOtherCenter).continuous (twoDShiftedInterval_smooth 0).continuous,
        disconnected_left_lt x hx, (twoDShiftedInterval_smooth 0).contDiffOn.congr
          (fun y hy => max_eq_left_of_lt hy)⟩
    · exact ⟨{y | twoDShiftedIntervalHeight 0 y < twoDShiftedIntervalHeight twoDOtherCenter y},
        isOpen_lt (twoDShiftedInterval_smooth 0).continuous (twoDShiftedInterval_smooth twoDOtherCenter).continuous,
        disconnected_right_lt x hx, (twoDShiftedInterval_smooth twoDOtherCenter).contDiffOn.congr
          (fun y hy => max_eq_right_of_lt hy)⟩
  zero_frontier := fun x hx => (frontier_lt_subset_eq continuous_const
    ((twoDShiftedInterval_smooth 0).continuous.max (twoDShiftedInterval_smooth twoDOtherCenter).continuous) hx).symm
  regular_zero := by
    intro x hx hz hd
    rw [twoDDisconnected_closedPositive] at hx
    rcases hx with hx | hx
    · have he := twoDDisconnected_eq_left_near x hx
      rw [he.fderiv_eq] at hd
      exact (twoDShiftedIntervalSine_admissible 0).regular_zero x
        (by rwa [twoDShiftedInterval_closedPositive]) (he.eq_of_nhds ▸ hz) hd
    · have he := twoDDisconnected_eq_right_near x hx
      rw [he.fderiv_eq] at hd
      exact (twoDShiftedIntervalSine_admissible twoDOtherCenter).regular_zero x
        (by rwa [twoDShiftedInterval_closedPositive]) (he.eq_of_nhds ▸ hz) hd
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, twoDSineFuture_smooth.contDiffOn⟩
  slope_budget := ⟨1 / 2, 1 / 8, by norm_num, by norm_num, by norm_num,
    twoDDisconnected_lipschitz, twoDSineFuture_lipschitz⟩

/-- Both unit intervals, including BOTH positive-height critical points. -/
theorem twoDDisconnected_both_critical :
    (0 < twoDDisconnectedHeight 0 ∧ fderiv ℝ twoDDisconnectedHeight 0 = 0) ∧
    (0 < twoDDisconnectedHeight twoDOtherCenter ∧ fderiv ℝ twoDDisconnectedHeight twoDOtherCenter = 0) := by
  have hleft := twoDDisconnected_eq_left_near 0 (Metric.mem_closedBall_self (by norm_num))
  have hright := twoDDisconnected_eq_right_near twoDOtherCenter (Metric.mem_closedBall_self (by norm_num))
  have hl : 0 < twoDShiftedIntervalHeight 0 0 := by norm_num [twoDShiftedIntervalHeight, twoDIntervalHeight]
  have hr : 0 < twoDShiftedIntervalHeight twoDOtherCenter twoDOtherCenter := by
    norm_num [twoDShiftedIntervalHeight, twoDIntervalHeight]
  refine ⟨⟨hl.trans_le (le_max_left _ _), ?_⟩, hr.trans_le (le_max_right _ _), ?_⟩
  · rw [hleft.fderiv_eq]
    ext v
    simp [twoDShiftedInterval_fderiv]
  · rw [hright.fderiv_eq]
    ext v
    simp [twoDShiftedInterval_fderiv]

/-- The complete joint is the union of both components' complete joints.
This is a set identity, not a bilocal additivity statement. -/
theorem twoDDisconnected_joint_parts : dimensionTwoSpatialJoint twoDDisconnectedHeight =
    dimensionTwoSpatialJoint (twoDShiftedIntervalHeight 0) ∪
      dimensionTwoSpatialJoint (twoDShiftedIntervalHeight twoDOtherCenter) := by
  ext x
  change (x ∈ twoDClosedPositive twoDDisconnectedHeight ∧ twoDDisconnectedHeight x = 0) ↔ _
  rw [twoDDisconnected_closedPositive]
  constructor
  · rintro ⟨hx | hx, hz⟩
    · exact Or.inl ⟨by rwa [show closure {x | 0 < twoDShiftedIntervalHeight 0 x} =
          Metric.closedBall 0 1 from twoDShiftedInterval_closedPositive 0],
        (twoDDisconnected_eq_left_near x hx).eq_of_nhds.symm.trans hz⟩
    · exact Or.inr ⟨by rwa [show closure {x | 0 < twoDShiftedIntervalHeight twoDOtherCenter x} =
          Metric.closedBall twoDOtherCenter 1 from twoDShiftedInterval_closedPositive twoDOtherCenter],
        (twoDDisconnected_eq_right_near x hx).eq_of_nhds.symm.trans hz⟩
  · rintro (hx | hx)
    · have hb : x ∈ Metric.closedBall (0 : TwoDSpace) 1 := by
        rw [← twoDShiftedInterval_closedPositive 0]
        exact hx.1
      exact ⟨Or.inl hb, (twoDDisconnected_eq_left_near x hb).eq_of_nhds.trans hx.2⟩
    · have hb : x ∈ Metric.closedBall twoDOtherCenter 1 := by
        rw [← twoDShiftedInterval_closedPositive twoDOtherCenter]
        exact hx.1
      exact ⟨Or.inr hb, (twoDDisconnected_eq_right_near x hb).eq_of_nhds.trans hx.2⟩

private theorem twoD_sphere_pair (a : ℝ) : Metric.sphere (twoDLine.symm a) 1 =
    {twoDLine.symm (a - 1), twoDLine.symm (a + 1)} := by
  ext x
  simp only [Metric.mem_sphere, dist_eq_norm, twoD_norm_eq, PiLp.sub_apply,
    twoDLine_symm_apply, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hx
    have he : |x 0 - a| = |(1 : ℝ)| := by simpa using hx
    rcases abs_eq_abs.mp he with he | he
    · right
      apply twoDLine.injective
      change x 0 = a + 1
      linarith
    · left
      apply twoDLine.injective
      change x 0 = a - 1
      linarith
  · rintro (rfl | rfl) <;> simp [twoDLine_symm_apply]

/-- All FOUR endpoints are explicit and distinct: minus one, one, three, five. -/
theorem twoDDisconnected_four_endpoints : dimensionTwoSpatialJoint twoDDisconnectedHeight =
    {twoDLine.symm (-1), twoDLine.symm 1, twoDLine.symm 3, twoDLine.symm 5} := by
  rw [twoDDisconnected_joint_parts, (twoDShiftedIntervalSine_admissible 0).joint_eq_frontier,
    (twoDShiftedIntervalSine_admissible twoDOtherCenter).joint_eq_frontier,
    twoDShiftedInterval_positive, twoDShiftedInterval_positive,
    frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0), frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  rw [show (0 : TwoDSpace) = twoDLine.symm 0 from (map_zero _).symm,
    twoDOtherCenter, twoD_sphere_pair, twoD_sphere_pair]
  ext x
  norm_num
  tauto

/-- Unit counting gives one term for each endpoint, for ANY observable. -/
theorem twoDDisconnected_endpoint_integral (G : TwoDSpace → ℝ) :
    (∫ x, G x ∂dimensionTwoJointMeasure twoDDisconnectedHeight) =
      G (twoDLine.symm (-1)) + G (twoDLine.symm 1) + G (twoDLine.symm 3) + G (twoDLine.symm 5) := by
  classical
  have he : twoDDisconnectedSine_admissible.joint_finite.toFinset =
      {twoDLine.symm (-1), twoDLine.symm 1, twoDLine.symm 3, twoDLine.symm 5} := by
    ext x
    simp [twoDDisconnected_four_endpoints]
  rw [(twoDDisconnectedSine_admissible.endpoint_integral G).2, he]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, twoDLine.symm.injective.eq_iff]
    norm_num

end BoundaryDraft
