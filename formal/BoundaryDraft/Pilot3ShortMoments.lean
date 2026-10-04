import BoundaryDraft.DimensionActionConstants
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Signed and absolute transverse moments for the three-dimensional short model

These are moments of the actual dimension-three kernel. The absolute scaling
also supplies fixed-cutoff domination, without an exponential-tail hypothesis.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace Pilot3ShortMoments

/-- The actual signed transverse moment, not its algebraic Mellin multiplier. -/
def moment (j : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel 3 (u ^ (3 / 2 : ℝ))

/-- The finite absolute moment used only after signed cancellation. -/
def absMoment (j : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, u ^ j * |dimensionKernel 3 (u ^ (3 / 2 : ℝ))|

theorem moment_eq {j : ℝ} (hj : -1 < j) :
    moment j = (2 / 3 : ℝ) * Real.Gamma (2 * (j + 1) / 3) *
      (1 - (j + 1)) * (1 - (j + 1) / 2) := by
  have he := integral_dimensionKernel_transverse 3 (by norm_num) hj
  norm_num only [Nat.cast_ofNat] at he
  rw [moment, he]
  norm_num [dimensionFactorCount, Finset.prod_range_succ]
  ring

@[simp] theorem moment_zero : moment 0 = 0 := by
  rw [moment_eq (by norm_num)]
  ring

@[simp] theorem moment_one : moment 1 = 0 := by
  rw [moment_eq (by norm_num)]
  ring

@[simp] theorem moment_half : moment (1 / 2) = -1 / 12 := by
  rw [moment_eq (by norm_num)]
  norm_num

@[simp] theorem moment_three_halves : moment (3 / 2) = Real.Gamma (5 / 3) / 4 := by
  rw [moment_eq (by norm_num)]
  norm_num
  ring

theorem integrable {j c ρ : ℝ} (hj : -1 < j) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => σ ^ j * dimensionKernel 3
      (c * ρ * σ ^ (3 / 2 : ℝ))) (Ioi 0) :=
  integrableOn_dimensionKernel_density_rpow 3 (by norm_num) hj (mul_pos hc hρ)

theorem integrable_abs {j c ρ : ℝ} (hj : -1 < j) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => σ ^ j * |dimensionKernel 3
      (c * ρ * σ ^ (3 / 2 : ℝ))|) (Ioi 0) := by
  apply (integrable hj hc hρ).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ.le _)]

/-- Positive scaling of an absolute moment; no signed formula is used here. -/
theorem scaled_abs (j : ℝ) {k : ℝ} (hk : 0 < k) :
    (∫ u : ℝ in Ioi 0, u ^ j * |dimensionKernel 3 ((k * u) ^ (3 / 2 : ℝ))|) =
      k ^ (-(j + 1)) * absMoment j := by
  have hs := integral_comp_mul_left_Ioi
    (fun u : ℝ => u ^ j * |dimensionKernel 3 (u ^ (3 / 2 : ℝ))|) 0 hk
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (∫ u : ℝ in Ioi 0,
      (k * u) ^ j * |dimensionKernel 3 ((k * u) ^ (3 / 2 : ℝ))|) =
      k ^ j * ∫ u : ℝ in Ioi 0,
        u ^ j * |dimensionKernel 3 ((k * u) ^ (3 / 2 : ℝ))| := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.mul_rpow hk.le hu.le]
    ring
  rw [he] at hs
  have hp : k ^ (-j) * k ^ j = 1 := by
    rw [← Real.rpow_add hk, neg_add_cancel, Real.rpow_zero]
  calc
    _ = k ^ (-j) * (k ^ j * ∫ u : ℝ in Ioi 0,
        u ^ j * |dimensionKernel 3 ((k * u) ^ (3 / 2 : ℝ))|) := by
      rw [← mul_assoc, hp, one_mul]
    _ = k ^ (-j) * (k⁻¹ * absMoment j) := by rw [hs]; rfl
    _ = _ := by
      rw [← Real.rpow_neg_one k, ← mul_assoc, ← Real.rpow_add hk]
      congr 2
      ring

theorem density_moment (j : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ σ : ℝ in Ioi 0, σ ^ j * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) =
      (c * ρ) ^ (-(2 * (j + 1) / 3)) * moment j := by
  calc
    _ = ∫ σ : ℝ in Ioi 0, σ ^ j *
        dimensionKernel 3 (((c * ρ) ^ (2 / 3 : ℝ) * σ) ^ (3 / 2 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      have he := dimensionKernel_density_scaling 3 (by norm_num) c ρ σ hc hρ hσ.le
      norm_num only [Nat.cast_ofNat] at he
      dsimp only
      rw [he]
    _ = _ := by
      rw [integral_dimensionKernel_scaled_rpow 3 _ _ _
        (Real.rpow_pos_of_pos (mul_pos hc hρ) _), ← Real.rpow_mul (mul_pos hc hρ).le]
      congr 2
      ring

theorem density_abs_moment (j : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ σ : ℝ in Ioi 0, σ ^ j * |dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))|) =
      (c * ρ) ^ (-(2 * (j + 1) / 3)) * absMoment j := by
  calc
    _ = ∫ σ : ℝ in Ioi 0, σ ^ j *
        |dimensionKernel 3 (((c * ρ) ^ (2 / 3 : ℝ) * σ) ^ (3 / 2 : ℝ))| := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      have he := dimensionKernel_density_scaling 3 (by norm_num) c ρ σ hc hρ hσ.le
      norm_num only [Nat.cast_ofNat] at he
      dsimp only
      rw [he]
    _ = _ := by
      rw [scaled_abs j (Real.rpow_pos_of_pos (mul_pos hc hρ) _),
        ← Real.rpow_mul (mul_pos hc hρ).le]
      congr 2
      ring

private theorem normalization (j M : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (5 / 3 : ℝ) * ((c * ρ) ^ (-(2 * (j + 1) / 3)) * M) =
      c ^ (-(2 * (j + 1) / 3)) * ρ ^ ((3 - 2 * j) / 3) * M := by
  rw [Real.mul_rpow hc.le hρ.le]
  calc
    _ = c ^ (-(2 * (j + 1) / 3)) *
        (ρ ^ (5 / 3 : ℝ) * ρ ^ (-(2 * (j + 1) / 3))) * M := by ring
    _ = _ := by
      rw [← Real.rpow_add hρ]
      congr 2
      congr 1
      ring

/-- Full physical normalization of every signed transverse order. -/
theorem normalized_moment (j : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (5 / 3 : ℝ) *
      (∫ σ : ℝ in Ioi 0, σ ^ j * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) =
      c ^ (-(2 * (j + 1) / 3)) * ρ ^ ((3 - 2 * j) / 3) * moment j := by
  rw [density_moment j hc hρ]
  exact normalization j _ hc hρ

/-- In particular the second absolute moment has normalized order minus one-third. -/
theorem normalized_abs_moment (j : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (5 / 3 : ℝ) *
      (∫ σ : ℝ in Ioi 0, σ ^ j * |dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))|) =
      c ^ (-(2 * (j + 1) / 3)) * ρ ^ ((3 - 2 * j) / 3) * absMoment j := by
  rw [density_abs_moment j hc hρ]
  exact normalization j _ hc hρ

theorem integrable_of_bound (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    {j : ℝ} (hj : -1 < j) (hbound : ∀ σ, 0 < σ → ‖B σ‖ ≤ C * σ ^ j)
    {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ => B σ * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ)))
      (Ioi 0) := by
  apply ((integrable_abs hj hc hρ).const_mul C).mono'
    (hB.mul ((continuous_dimensionKernel 3).measurable.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  dsimp only [Function.comp_apply]
  rw [norm_mul, Real.norm_eq_abs (dimensionKernel _ _)]
  exact (mul_le_mul_of_nonneg_right (hbound σ hσ) (abs_nonneg _)).trans_eq (by ring)

/-- A global power strictly above three-halves suffices for normalized decay.
The constant may depend on the fixed positive cutoff. -/
theorem limit_of_bound (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    {j : ℝ} (hj : 3 / 2 < j) (hbound : ∀ σ, 0 < σ → ‖B σ‖ ≤ C * σ ^ j)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, B σ * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hj' : -1 < j := by linarith
  apply squeeze_zero_norm' (a := fun ρ : ℝ =>
    (C * c ^ (-(2 * (j + 1) / 3)) * absMoment j) * ρ ^ ((3 - 2 * j) / 3))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    have hi := integrable_of_bound B hB C hj' hbound hc hρ
    have hnorm : ‖∫ σ : ℝ in Ioi 0,
        B σ * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))‖ ≤
        C * ∫ σ : ℝ in Ioi 0, σ ^ j * |dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))| := by
      calc
        _ ≤ ∫ σ : ℝ in Ioi 0,
            ‖B σ * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ σ : ℝ in Ioi 0,
            C * (σ ^ j * |dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))|) := by
          apply integral_mono_ae hi.norm ((integrable_abs hj' hc hρ).const_mul C)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
          rw [norm_mul, Real.norm_eq_abs (dimensionKernel _ _)]
          exact (mul_le_mul_of_nonneg_right (hbound σ hσ) (abs_nonneg _)).trans_eq (by ring)
        _ = _ := integral_const_mul _ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hρ _)]
    apply (mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hρ.le _)).trans_eq
    calc
      _ = C * (ρ ^ (5 / 3 : ℝ) * ∫ σ : ℝ in Ioi 0,
          σ ^ j * |dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))|) := by ring
      _ = _ := by rw [normalized_abs_moment j hc hρ]; ring
  · have he : (3 - 2 * j) / 3 = -((2 * j - 3) / 3) := by ring
    rw [he]
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < (2 * j - 3) / 3)).const_mul
        (C * c ^ (-(2 * (j + 1) / 3)) * absMoment j)

end Pilot3ShortMoments
end BoundaryDraft
