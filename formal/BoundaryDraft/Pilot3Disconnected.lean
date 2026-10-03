import BoundaryDraft.Pilot3Divergence
import BoundaryDraft.Pilot3JointAtlas
import BoundaryDraft.Pilot3Examples
import BoundaryDraft.Pilot3Components

/-!
# An admissible disconnected smooth pilot, not just a set identity

Two disjoint unit disks share the original curved sine future. The raw max
height need not be smooth on the irrelevant exterior bisector; it is smooth
on genuine neighborhoods of the entire closed positive region. Both disks,
both circles, and both positive-height critical points are retained.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

theorem Pilot3RegularHeight.max_of_separated {h k : Pilot3Space → ℝ}
    (hh : Pilot3RegularHeight h) (hk : Pilot3RegularHeight k)
    (hhs : ContDiff ℝ ∞ h) (hks : ContDiff ℝ ∞ k)
    (hsep : ∀ x ∈ pilot3ClosedPositive h, k x < 0)
    (ksep : ∀ x ∈ pilot3ClosedPositive k, h x < 0) :
    Pilot3RegularHeight (fun x => max (h x) (k x)) := by
  have hpos : {x | 0 < max (h x) (k x)} = {x | 0 < h x} ∪ {x | 0 < k x} := by
    ext x
    simp only [mem_setOf_eq, mem_union, lt_max_iff]
  have hlt : ∀ x ∈ pilot3ClosedPositive h, k x < h x :=
    fun x hx => (hsep x hx).trans_le (hh.nonneg_on_closedPositive x hx)
  have klt : ∀ x ∈ pilot3ClosedPositive k, h x < k x :=
    fun x hx => (ksep x hx).trans_le (hk.nonneg_on_closedPositive x hx)
  have heh : ∀ x ∈ pilot3ClosedPositive h, (fun y => max (h y) (k y)) =ᶠ[𝓝 x] h := by
    intro x hx
    filter_upwards [(isOpen_lt hks.continuous hhs.continuous).mem_nhds (hlt x hx)] with y hy
    exact max_eq_left_of_lt hy
  have hek : ∀ x ∈ pilot3ClosedPositive k, (fun y => max (h y) (k y)) =ᶠ[𝓝 x] k := by
    intro x hx
    filter_upwards [(isOpen_lt hhs.continuous hks.continuous).mem_nhds (klt x hx)] with y hy
    exact max_eq_right_of_lt hy
  refine {
    bounded_positive := by rw [hpos]; exact hh.bounded_positive.union hk.bounded_positive
    smooth_near := ?_
    zero_frontier := fun x hx => (frontier_lt_subset_eq continuous_const (hhs.continuous.max hks.continuous) hx).symm
    regular_zero := ?_ }
  · intro x hx
    rw [pilot3ClosedPositive_max] at hx
    rcases hx with hx | hx
    · exact ⟨{y | k y < h y}, isOpen_lt hks.continuous hhs.continuous, hlt x hx,
        hhs.contDiffOn.congr (fun y hy => max_eq_left_of_lt hy)⟩
    · exact ⟨{y | h y < k y}, isOpen_lt hhs.continuous hks.continuous, klt x hx,
        hks.contDiffOn.congr (fun y hy => max_eq_right_of_lt hy)⟩
  · intro x hx hz hd
    rw [pilot3ClosedPositive_max] at hx
    rcases hx with hx | hx
    · rw [(heh x hx).fderiv_eq] at hd
      exact hh.regular_zero x hx (by simpa only [max_eq_left (hlt x hx).le] using hz) hd
    · rw [(hek x hx).fderiv_eq] at hd
      exact hk.regular_zero x hx (by simpa only [max_eq_right (klt x hx).le] using hz) hd

def pilot3ShiftedBallHeight (a x : Pilot3Space) : ℝ := pilot3BallHeight (x - a)

theorem pilot3ShiftedBall_smooth (a : Pilot3Space) : ContDiff ℝ ∞ (pilot3ShiftedBallHeight a) :=
  pilot3BallHeight_smooth.comp (contDiff_id.sub contDiff_const)

theorem pilot3ShiftedBall_positive (a : Pilot3Space) :
    {x | 0 < pilot3ShiftedBallHeight a x} = Metric.ball a 1 := by
  ext x
  change (x - a ∈ {y | 0 < pilot3BallHeight y}) ↔ _
  rw [pilot3BallHeight_positive]
  simp only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero]

theorem pilot3ShiftedBall_closedPositive (a : Pilot3Space) :
    pilot3ClosedPositive (pilot3ShiftedBallHeight a) = Metric.closedBall a 1 := by
  rw [pilot3ClosedPositive, pilot3ShiftedBall_positive, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem pilot3ShiftedBall_nonneg_iff (a x : Pilot3Space) :
    0 ≤ pilot3ShiftedBallHeight a x ↔ x ∈ Metric.closedBall a 1 := by
  simp only [pilot3ShiftedBallHeight, pilot3BallHeight, Metric.mem_closedBall, dist_eq_norm]
  constructor <;> intro hx <;> nlinarith [norm_nonneg (x - a)]

theorem pilot3ShiftedBall_fderiv (a x v : Pilot3Space) :
    fderiv ℝ (pilot3ShiftedBallHeight a) x v = -(1 / 2 : ℝ) * inner (𝕜 := ℝ) (x - a) v := by
  change fderiv ℝ (fun y => pilot3BallHeight (y - a)) x v = _
  rw [fderiv_comp_sub]
  exact pilot3BallHeight_fderiv _ _

theorem pilot3ShiftedBall_regular (a : Pilot3Space) : Pilot3RegularHeight (pilot3ShiftedBallHeight a) where
  bounded_positive := by rw [pilot3ShiftedBall_positive]; exact Metric.isBounded_ball
  smooth_near := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, (pilot3ShiftedBall_smooth a).contDiffOn⟩
  zero_frontier := fun x hx => (frontier_lt_subset_eq continuous_const (pilot3ShiftedBall_smooth a).continuous hx).symm
  regular_zero := by
    intro x _ hz hd
    have he := pilot3ShiftedBall_fderiv a x (x - a)
    rw [hd, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at he
    dsimp [pilot3ShiftedBallHeight, pilot3BallHeight] at hz
    linarith

theorem pilot3ShiftedBall_lipschitz (a x y : Pilot3Space) :
    |max 0 (pilot3ShiftedBallHeight a x) - max 0 (pilot3ShiftedBallHeight a y)| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  simpa only [pilot3ShiftedBallHeight, sub_sub_sub_cancel_right] using pilot3BallHeight_lipschitz (x - a) (y - a)

def pilot3OtherCenter : Pilot3Space := pilot3Coordinates.symm (4, 0)

theorem pilot3OtherCenter_norm : ‖pilot3OtherCenter‖ = 4 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  norm_num [pilot3OtherCenter, pilot3Coordinates_norm_sq]

def pilot3DisconnectedHeight (x : Pilot3Space) : ℝ := max (pilot3BallHeight x) (pilot3ShiftedBallHeight pilot3OtherCenter x)

theorem pilot3Disconnected_separated : Disjoint (Metric.closedBall (0 : Pilot3Space) 1) (Metric.closedBall pilot3OtherCenter 1) := by
  apply Metric.closedBall_disjoint_closedBall
  rw [dist_zero_left, pilot3OtherCenter_norm]
  norm_num

private theorem pilot3Disconnected_right_neg (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive pilot3BallHeight) :
    pilot3ShiftedBallHeight pilot3OtherCenter x < 0 := by
  apply lt_of_not_ge
  intro hn
  rw [pilot3BallHeight_closedPositive] at hx
  exact Set.disjoint_left.mp pilot3Disconnected_separated hx ((pilot3ShiftedBall_nonneg_iff _ _).mp hn)

private theorem pilot3Disconnected_left_neg (x : Pilot3Space)
    (hx : x ∈ pilot3ClosedPositive (pilot3ShiftedBallHeight pilot3OtherCenter)) : pilot3BallHeight x < 0 := by
  apply lt_of_not_ge
  intro hn
  rw [pilot3ShiftedBall_closedPositive] at hx
  have hl : x ∈ Metric.closedBall (0 : Pilot3Space) 1 :=
    (pilot3ShiftedBall_nonneg_iff 0 x).mp (by simpa only [pilot3ShiftedBallHeight, sub_zero] using hn)
  exact Set.disjoint_left.mp pilot3Disconnected_separated hl hx

theorem pilot3Disconnected_regular : Pilot3RegularHeight pilot3DisconnectedHeight :=
  pilot3BallHeight_regular.max_of_separated (pilot3ShiftedBall_regular pilot3OtherCenter)
    pilot3BallHeight_smooth (pilot3ShiftedBall_smooth pilot3OtherCenter)
    pilot3Disconnected_right_neg pilot3Disconnected_left_neg

theorem pilot3Disconnected_positive : {x | 0 < pilot3DisconnectedHeight x} =
    Metric.ball (0 : Pilot3Space) 1 ∪ Metric.ball pilot3OtherCenter 1 := by
  ext x
  change 0 < max (pilot3BallHeight x) (pilot3ShiftedBallHeight pilot3OtherCenter x) ↔ _
  rw [lt_max_iff]
  change x ∈ {y | 0 < pilot3BallHeight y} ∨ x ∈ {y | 0 < pilot3ShiftedBallHeight pilot3OtherCenter y} ↔ _
  rw [pilot3BallHeight_positive, pilot3ShiftedBall_positive]
  rfl

theorem pilot3Disconnected_closedPositive : pilot3ClosedPositive pilot3DisconnectedHeight =
    Metric.closedBall (0 : Pilot3Space) 1 ∪ Metric.closedBall pilot3OtherCenter 1 := by
  unfold pilot3DisconnectedHeight
  rw [pilot3ClosedPositive_max, pilot3BallHeight_closedPositive, pilot3ShiftedBall_closedPositive]

theorem pilot3Disconnected_lipschitz (x y : Pilot3Space) :
    |max 0 (pilot3DisconnectedHeight x) - max 0 (pilot3DisconnectedHeight y)| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  have he (a b : ℝ) : max 0 (max a b) = max (max 0 a) (max 0 b) := by simp [max_assoc, max_left_comm]
  simp only [pilot3DisconnectedHeight, he]
  exact (abs_max_sub_max_le_max _ _ _ _).trans
    (max_le (pilot3BallHeight_lipschitz x y) (pilot3ShiftedBall_lipschitz pilot3OtherCenter x y))

theorem pilot3DisconnectedSine_admissible : SmoothPilot3 pilot3DisconnectedHeight pilot3SineFuture where
  toPilot3RegularHeight := pilot3Disconnected_regular
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, pilot3SineFuture_smooth.contDiffOn⟩
  slope_budget := ⟨1 / 2, 1 / 8, by norm_num, by norm_num, by norm_num,
    pilot3Disconnected_lipschitz, pilot3SineFuture_lipschitz⟩

/-- Both whole circles, with neither selected as a distinguished component. -/
theorem pilot3Disconnected_joint : pilot3SpatialJoint pilot3DisconnectedHeight =
    Metric.sphere (0 : Pilot3Space) 1 ∪ Metric.sphere pilot3OtherCenter 1 := by
  unfold pilot3DisconnectedHeight
  rw [pilot3SpatialJoint_max]
  · rw [pilot3BallHeight_joint, (pilot3ShiftedBall_regular pilot3OtherCenter).joint_eq_frontier,
      pilot3ShiftedBall_positive, frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  · exact pilot3BallHeight_regular
  · exact pilot3ShiftedBall_regular pilot3OtherCenter
  · rw [pilot3BallHeight_closedPositive, pilot3ShiftedBall_closedPositive]
    exact pilot3Disconnected_separated

theorem pilot3Disconnected_both_nonempty :
    (-1 / 8, (0 : Pilot3Space)) ∈ pilot3Region pilot3DisconnectedHeight pilot3SineFuture ∧
    (pilot3SineFuture pilot3OtherCenter - 1 / 8, pilot3OtherCenter) ∈
      pilot3Region pilot3DisconnectedHeight pilot3SineFuture := by
  constructor
  · apply (pilot3Region_max _ _ _).symm.subset
    exact Or.inl pilot3BallSine_nonempty
  · apply (pilot3Region_max _ _ _).symm.subset
    right
    have he : pilot3ShiftedBallHeight pilot3OtherCenter pilot3OtherCenter = 1 / 4 := by
      norm_num [pilot3ShiftedBallHeight, pilot3BallHeight]
    change pilot3SineFuture pilot3OtherCenter - pilot3ShiftedBallHeight pilot3OtherCenter pilot3OtherCenter <
      pilot3SineFuture pilot3OtherCenter - 1 / 8 ∧ pilot3SineFuture pilot3OtherCenter - 1 / 8 < _
    rw [he]
    constructor <;> linarith

/-- Genuine local equality, including contact points on the left circle. -/
theorem pilot3Disconnected_eq_left_near (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive pilot3BallHeight) :
    pilot3DisconnectedHeight =ᶠ[𝓝 x] pilot3BallHeight := by
  have ht := (pilot3Disconnected_right_neg x hx).trans_le (pilot3BallHeight_regular.nonneg_on_closedPositive x hx)
  filter_upwards [(isOpen_lt (pilot3ShiftedBall_smooth pilot3OtherCenter).continuous
    pilot3BallHeight_smooth.continuous).mem_nhds ht] with y hy
  exact max_eq_left_of_lt hy

theorem pilot3Disconnected_eq_right_near (x : Pilot3Space)
    (hx : x ∈ pilot3ClosedPositive (pilot3ShiftedBallHeight pilot3OtherCenter)) :
    pilot3DisconnectedHeight =ᶠ[𝓝 x] pilot3ShiftedBallHeight pilot3OtherCenter := by
  have ht := (pilot3Disconnected_left_neg x hx).trans_le
    ((pilot3ShiftedBall_regular pilot3OtherCenter).nonneg_on_closedPositive x hx)
  filter_upwards [(isOpen_lt pilot3BallHeight_smooth.continuous
    (pilot3ShiftedBall_smooth pilot3OtherCenter).continuous).mem_nhds ht] with y hy
  exact max_eq_right_of_lt hy

theorem pilot3Disconnected_both_critical :
    (0 < pilot3DisconnectedHeight 0 ∧ fderiv ℝ pilot3DisconnectedHeight 0 = 0) ∧
    (0 < pilot3DisconnectedHeight pilot3OtherCenter ∧ fderiv ℝ pilot3DisconnectedHeight pilot3OtherCenter = 0) := by
  have hleft := pilot3Disconnected_eq_left_near 0 (subset_closure pilot3BallHeight_critical.1)
  have hrightpos : 0 < pilot3ShiftedBallHeight pilot3OtherCenter pilot3OtherCenter := by
    norm_num [pilot3ShiftedBallHeight, pilot3BallHeight]
  have hright := pilot3Disconnected_eq_right_near pilot3OtherCenter (subset_closure hrightpos)
  refine ⟨⟨pilot3BallHeight_critical.1.trans_le (le_max_left _ _), ?_⟩,
    hrightpos.trans_le (le_max_right _ _), ?_⟩
  · rw [hleft.fderiv_eq]
    exact pilot3BallHeight_critical.2
  · rw [hright.fderiv_eq]
    ext v
    simp only [pilot3ShiftedBall_fderiv, sub_self, inner_zero_left, mul_zero, ContinuousLinearMap.zero_apply]

/-- The curved interior portion of the original future survives unchanged. -/
theorem pilot3Disconnected_curved :
    deriv (deriv (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0]))) (1 / 2) ≠ 0 ∧
    0 < pilot3DisconnectedHeight ((WithLp.equiv 2 _).symm ![(1 / 2 : ℝ), 0]) :=
  ⟨pilot3SineFuture_curved.1, pilot3SineFuture_curved.2.trans_le (le_max_left _ _)⟩

/-- Actual integration on the union, using the proved shared collar interface. -/
theorem pilot3Disconnected_collar_coarea : ∃ δ : ℝ, 0 < δ ∧
    ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 δ) →
      IntegrableOn (fun x => g (pilot3DisconnectedHeight x)) (pilot3ClosedCollar pilot3DisconnectedHeight δ) ∧
      (∫ x in pilot3ClosedCollar pilot3DisconnectedHeight δ, g (pilot3DisconnectedHeight x)) =
        ∫ t in Icc 0 δ, g t * pilot3HeightDensity pilot3DisconnectedHeight t := by
  obtain ⟨δ, hδ, _, hco⟩ := pilot3Disconnected_regular.exists_collar_coarea
  refine ⟨δ, hδ, fun g hg => ?_⟩
  obtain ⟨hi, _, he⟩ := hco (fun _ => 1) continuousOn_const g hg
  simpa only [mul_one, pilot3WeightedHeightDensity_one] using And.intro hi he

end BoundaryDraft
