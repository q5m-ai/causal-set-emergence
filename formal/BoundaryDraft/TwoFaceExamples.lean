import BoundaryDraft.TwoFaceContract
import BoundaryDraft.GraphExamples
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Pi.Bounds

/-!
# Nonvacuity of the two-face interface

Every old admissible height has room for a small independently chosen sine
future face. The concrete large spherical cap below contains three collinear
interior points where that future graph violates the affine midpoint identity.
This is not a boost of a planar future face. No action limit is proved here.
-/

open Set

noncomputable section
namespace BoundaryDraft

/-- A smooth, globally controlled bend, unrelated to the thickness profile. -/
def twoFaceSine (c : ℝ) (x : Spatial) : ℝ := c * Real.sin (x 0)

private theorem sin_sub_bound (s t : ℝ) : |Real.sin s - Real.sin t| ≤ |s - t| := by
  have hl : LipschitzWith 1 Real.sin :=
    lipschitzWith_of_nnnorm_deriv_le Real.differentiable_sin (by
      intro x
      change ‖deriv Real.sin x‖ ≤ (1 : ℝ)
      rw [Real.deriv_sin, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul s t

/-- Nonzero future curvature is available without strengthening the original
height assumptions, even if the original positive-part margin is very small. -/
theorem AdmissibleGraphCap.exists_twoFace_sine {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) : ∃ c : ℝ, 0 < c ∧ AdmissibleTwoFace h (twoFaceSine c) := by
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hh.lipschitz_positivePart
  let c := (1 - κ) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨c, hc, { hh with smooth_future := ?_, slope_budget := ?_ }⟩
  · intro x _
    apply ContDiffAt.mul contDiffAt_const
    exact Real.contDiff_sin.contDiffAt.comp x
      ((contDiff_apply ℝ ℝ (0 : Fin 3)).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff).contDiffAt
  · refine ⟨κ, c, hκ, hc.le, ?_, hLip, ?_⟩
    · dsimp [c]; linarith
    · intro x y
      have hd : |x 0 - y 0| ≤ spatialDistance x y := by
        have he := PiLp.norm_apply_le ((WithLp.equiv 2 _).symm (y - x)) (0 : Fin 3)
        change ‖y 0 - x 0‖ ≤ spatialDistance x y at he
        simpa only [Real.norm_eq_abs, abs_sub_comm] using he
      calc
        |twoFaceSine c x - twoFaceSine c y| = c * |Real.sin (x 0) - Real.sin (y 0)| := by
          rw [twoFaceSine, twoFaceSine, ← mul_sub, abs_mul, abs_of_pos hc]
        _ ≤ c * |x 0 - y 0| := mul_le_mul_of_nonneg_left (sin_sub_bound _ _) hc.le
        _ ≤ c * spatialDistance x y := mul_le_mul_of_nonneg_left hd hc.le

/-- A nonempty concrete member with a genuinely nonplanar FUTURE face.
The three spatial points are 0, (π/2,0,0), (π,0,0), all strictly inside Ω.
Their unequal midpoint heights rule out every affine future graph on Ω. -/
theorem twoFace_curved_nonvacuity : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    (∀ s ∈ ({0, Real.pi / 2, Real.pi} : Set ℝ),
      0 < ellipsoidProfile (1 / 4) (fun _ => 4) ![s, 0, 0]) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 := by
  obtain ⟨c, hc, hf⟩ := (ellipsoid_admissible (1 / 4) (fun _ => 4)
    (by norm_num) (fun _ => by norm_num)).exists_twoFace_sine
  refine ⟨c, hc, hf, ?_, ?_⟩
  · intro s hs
    have hp := Real.pi_pos
    have hp4 := Real.pi_lt_four
    have hs0 : 0 ≤ s ∧ s < 4 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl <;> constructor <;> linarith
    norm_num [ellipsoidProfile, Fin.sum_univ_succ]
    rw [abs_of_nonneg (div_nonneg hs0.1 (by norm_num))]
    linarith
  · simpa [twoFaceSine, Real.sin_pi_div_two, Real.sin_pi] using ne_of_gt hc

end BoundaryDraft
