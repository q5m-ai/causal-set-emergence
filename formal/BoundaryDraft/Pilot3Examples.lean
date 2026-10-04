import BoundaryDraft.Pilot3Surface
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Pi.Bounds

/-!
# Nonempty curved-future pilot and retained critical point

The concrete example is exactly §6's a=1/4, epsilon=1/8 unit ball/sine
member. These checks do not evaluate its target or prove an action limit.
-/

open Set
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

def pilot3BallHeight (x : Pilot3Space) : ℝ := (1 - ‖x‖ ^ 2) / 4

def pilot3SineFuture (x : Pilot3Space) : ℝ := Real.sin (x 0) / 8

private theorem clipped_square_bound {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |max 0 (1 - r ^ 2) - max 0 (1 - s ^ 2)| ≤ 2 * |r - s| := by
  wlog hrs : r ≤ s generalizing r s
  · simpa only [abs_sub_comm] using this hs hr (le_of_not_ge hrs)
  rw [abs_sub_comm r s, abs_of_nonneg (sub_nonneg.mpr hrs)]
  by_cases hs1 : s ≤ 1
  · have hr1 := hrs.trans hs1
    rw [max_eq_right (by nlinarith : 0 ≤ 1 - r ^ 2),
      max_eq_right (by nlinarith : 0 ≤ 1 - s ^ 2),
      abs_of_nonneg (by nlinarith : 0 ≤ (1 - r ^ 2) - (1 - s ^ 2))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (show 0 ≤ 2 - r - s by linarith)]
  · rw [max_eq_left (by nlinarith : 1 - s ^ 2 ≤ 0), sub_zero, abs_of_nonneg (le_max_left _ _)]
    by_cases hr1 : r ≤ 1
    · rw [max_eq_right (by nlinarith : 0 ≤ 1 - r ^ 2)]
      nlinarith [sq_nonneg (1 - r)]
    · rw [max_eq_left (by nlinarith : 1 - r ^ 2 ≤ 0)]
      linarith

theorem pilot3BallHeight_lipschitz : ∀ x y : Pilot3Space,
    |max 0 (pilot3BallHeight x) - max 0 (pilot3BallHeight y)| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  intro x y
  have hdiv (r : ℝ) : max 0 (r / 4) = max 0 r / 4 := by
    by_cases hr : 0 ≤ r
    · rw [max_eq_right hr, max_eq_right (div_nonneg hr (by norm_num))]
    · rw [max_eq_left (le_of_not_ge hr), max_eq_left (div_nonpos_of_nonpos_of_nonneg
        (le_of_not_ge hr) (by norm_num)), zero_div]
  simp only [pilot3BallHeight, hdiv, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hb := clipped_square_bound (norm_nonneg x) (norm_nonneg y)
  have hn : |‖x‖ - ‖y‖| ≤ ‖y - x‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le x y
  linarith

theorem pilot3BallHeight_smooth : ContDiff ℝ ∞ pilot3BallHeight :=
  (contDiff_const.sub (contDiff_norm_sq ℝ)).div_const 4

theorem pilot3BallHeight_positive : {x | 0 < pilot3BallHeight x} = Metric.ball 0 1 := by
  ext x
  simp only [pilot3BallHeight, Metric.mem_ball, dist_zero_right, mem_setOf_eq]
  constructor <;> intro hx <;> nlinarith [norm_nonneg x]

theorem pilot3BallHeight_closedPositive : pilot3ClosedPositive pilot3BallHeight = Metric.closedBall 0 1 := by
  rw [pilot3ClosedPositive, pilot3BallHeight_positive, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem pilot3BallHeight_fderiv (x v : Pilot3Space) :
    fderiv ℝ pilot3BallHeight x v = -(1 / 2 : ℝ) * inner (𝕜 := ℝ) x v := by
  have hd : HasFDerivAt pilot3BallHeight ((1 / 4 : ℝ) • (-((2 : ℝ) • (innerSL ℝ x)))) x := by
    convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1).const_smul (1 / 4 : ℝ) using 1
    · ext y
      simp only [pilot3BallHeight, smul_eq_mul]
      ring
    · ext y
      simp
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, innerSL_apply, smul_eq_mul]
  ring

theorem pilot3BallHeight_regular : Pilot3RegularHeight pilot3BallHeight where
  bounded_positive := by rw [pilot3BallHeight_positive]; exact Metric.isBounded_ball
  smooth_near := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, pilot3BallHeight_smooth.contDiffOn⟩
  zero_frontier := by
    intro x hx
    rw [pilot3BallHeight_positive, frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hx
    have hn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    simp [pilot3BallHeight, hn]
  regular_zero := by
    intro x _ hz hd
    have hdx := pilot3BallHeight_fderiv x x
    rw [hd, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hdx
    dsimp [pilot3BallHeight] at hz
    linarith

theorem pilot3SineFuture_smooth : ContDiff ℝ ∞ pilot3SineFuture := by
  exact (Real.contDiff_sin.comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff)).div_const 8

theorem pilot3SineFuture_lipschitz : ∀ x y : Pilot3Space,
    |pilot3SineFuture x - pilot3SineFuture y| ≤ (1 / 8 : ℝ) * ‖y - x‖ := by
  have hl : LipschitzWith 1 Real.sin :=
    lipschitzWith_of_nnnorm_deriv_le Real.differentiable_sin (by
      intro x
      change ‖deriv Real.sin x‖ ≤ (1 : ℝ)
      rw [Real.deriv_sin, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
  intro x y
  have hs : |Real.sin (x 0) - Real.sin (y 0)| ≤ |x 0 - y 0| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul (x 0) (y 0)
  have hc : |x 0 - y 0| ≤ ‖y - x‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs, norm_sub_rev] using PiLp.norm_apply_le (x - y) 0
  simp only [pilot3SineFuture, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith

/-- The specified genuinely curved-future three-dimensional pilot. -/
theorem pilot3BallSine_admissible : SmoothPilot3 pilot3BallHeight pilot3SineFuture where
  toPilot3RegularHeight := pilot3BallHeight_regular
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, pilot3SineFuture_smooth.contDiffOn⟩
  slope_budget := ⟨1 / 2, 1 / 8, by norm_num, by norm_num, by norm_num,
    pilot3BallHeight_lipschitz, pilot3SineFuture_lipschitz⟩

theorem pilot3BallPlanar_admissible : SmoothPilot3 pilot3BallHeight (fun _ => 0) where
  toPilot3RegularHeight := pilot3BallHeight_regular
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, contDiff_const.contDiffOn⟩
  slope_budget := ⟨1 / 2, 0, by norm_num, by norm_num, by norm_num,
    pilot3BallHeight_lipschitz, by simp⟩

theorem pilot3BallSine_nonempty : (-1 / 8, (0 : Pilot3Space)) ∈
    pilot3Region pilot3BallHeight pilot3SineFuture := by
  norm_num [pilot3Region, pilot3BallHeight, pilot3SineFuture]

/-- Positive-height critical point, explicitly retained by the class. -/
theorem pilot3BallHeight_critical : 0 < pilot3BallHeight 0 ∧ fderiv ℝ pilot3BallHeight 0 = 0 := by
  constructor
  · norm_num [pilot3BallHeight]
  · ext v
    simp [pilot3BallHeight_fderiv]

/-- Every controlled band must stop below the retained critical height. -/
theorem pilot3BallHeight_band_below_critical {δ : ℝ}
    (hδ : ∀ x ∈ pilot3ClosedPositive pilot3BallHeight,
      pilot3BallHeight x ≤ δ → fderiv ℝ pilot3BallHeight x ≠ 0) : δ < 1 / 4 := by
  by_contra hn
  have hz : (0 : Pilot3Space) ∈ pilot3ClosedPositive pilot3BallHeight :=
    subset_closure pilot3BallHeight_critical.1
  exact hδ 0 hz (by simpa [pilot3BallHeight] using le_of_not_gt hn) pilot3BallHeight_critical.2

/-- Entire circular joint, not just one chosen coordinate patch. -/
theorem pilot3BallHeight_joint : pilot3SpatialJoint pilot3BallHeight = Metric.sphere 0 1 := by
  rw [pilot3BallHeight_regular.joint_eq_frontier, pilot3BallHeight_positive,
    frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

/-- Along an interior straight line the future height has nonzero second
derivative. This is a genuine curved future face, not a tilted plane. -/
theorem pilot3SineFuture_curved :
    deriv (deriv (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0]))) (1 / 2) ≠ 0 ∧
    0 < pilot3BallHeight ((WithLp.equiv 2 _).symm ![(1 / 2 : ℝ), 0]) := by
  have he : (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0])) =
      fun s : ℝ => Real.sin s / 8 := by rfl
  have hderiv : deriv (fun s : ℝ => Real.sin s / 8) = fun s => Real.cos s / 8 := by
    ext s
    exact ((Real.hasDerivAt_sin s).div_const 8).deriv
  rw [he, hderiv, ((Real.hasDerivAt_cos (1 / 2)).div_const 8).deriv]
  constructor
  · have hp := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith [Real.pi_gt_three] : (1 / 2 : ℝ) < Real.pi)
    exact div_ne_zero (neg_ne_zero.mpr hp.ne') (by norm_num)
  · norm_num [pilot3BallHeight, ← real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-- Empty raw height has no joint, despite being zero everywhere. -/
theorem pilot3Empty_admissible : SmoothPilot3 (fun _ => 0) (fun _ => 0) where
  bounded_positive := by simp
  smooth_near := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, contDiff_const.contDiffOn⟩
  zero_frontier := by simp
  regular_zero := by simp [pilot3ClosedPositive]
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, contDiff_const.contDiffOn⟩
  slope_budget := ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp, by simp⟩

end BoundaryDraft
