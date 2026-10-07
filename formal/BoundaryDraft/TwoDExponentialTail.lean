import BoundaryDraft.TwoDLogScaling

/-!
# Fixed-threshold exponential tails for the actual signed 2D kernel

Absolute values are used only for the discarded tail, after the signed moments
have been computed. The final action proof can instead use its simpler global
quadratic comparison; no shrinking cutoff or full-action rate is asserted.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft.TwoDExponentialTail

private def majorant (n : ℕ) (u : ℝ) : ℝ :=
  u ^ n * (1 + 2 * u + u ^ 2 / 2) * Real.exp (-u / 2)

private theorem majorant_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ majorant n u := by
  unfold majorant
  positivity

private theorem integrable_half_exp (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-u / 2)) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-u)) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using
      Real.GammaIntegral_convergent (show 0 < (n : ℝ) + 1 by positivity)
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => u ^ n * Real.exp (-u)) 0 (by norm_num : 0 < (1 / 2 : ℝ))).mpr
    (by simpa using hi)
  apply (hs.const_mul ((2 : ℝ) ^ n)).congr
  filter_upwards [] with u
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring, div_pow,
    show -(u / 2) = -u / 2 by ring]
  field_simp

private theorem integrable_majorant (n : ℕ) :
    IntegrableOn (majorant n) (Ioi 0) := by
  apply ((integrable_half_exp n).add
    (((integrable_half_exp (n + 1)).const_mul 2).add
      ((integrable_half_exp (n + 2)).const_mul (1 / 2)))).congr
  filter_upwards [] with u
  simp only [Pi.add_apply, majorant, pow_add, pow_one]
  ring

/-- A finite positive-envelope moment; it is not a signed-response coefficient. -/
def constant (n : ℕ) : ℝ := ∫ u : ℝ in Ioi 0, majorant n u

theorem constant_nonneg (n : ℕ) : 0 ≤ constant n := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact majorant_nonneg n hu.le

private theorem kernel_bound {u : ℝ} (hu : 0 ≤ u) :
    |dimensionKernel 2 u| ≤ (1 + 2 * u + u ^ 2 / 2) * Real.exp (-u) := by
  rw [TwoDLogMoments.kernel_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply (abs_add _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ u ^ 2 / 2)]
  have hh : |1 - 2 * u| ≤ 1 + 2 * u := by
    simpa only [abs_one, abs_of_nonneg (by positivity : 0 ≤ 2 * u)] using abs_sub 1 (2 * u)
  linarith

/-- Every absolute polynomial moment has an exponentially small fixed tail. -/
theorem moment_tail (n : ℕ) {L : ℝ} (hL : 0 < L) :
    (∫ u : ℝ in Ioi L, u ^ n * |dimensionKernel 2 u|) ≤
      constant n * Real.exp (-L / 2) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ n * |dimensionKernel 2 u|) (Ioi 0) := by
    apply ((TwoDLogMoments.integrable_rpow (j := (n : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    simp only [Real.norm_eq_abs, abs_mul, Real.rpow_natCast, abs_pow, abs_of_pos hu]
  have hs : Ioi L ⊆ Ioi (0 : ℝ) := fun _ hu => hL.trans hu
  calc
    _ ≤ ∫ u : ℝ in Ioi L, Real.exp (-L / 2) * majorant n u := by
      apply setIntegral_mono_on (hi.mono_set hs)
        (((integrable_majorant n).mono_set hs).const_mul _) measurableSet_Ioi
      intro u hu
      change L < u at hu
      have hu0 : 0 ≤ u := (hL.trans hu).le
      calc
        _ ≤ u ^ n * ((1 + 2 * u + u ^ 2 / 2) * Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left (kernel_bound hu0) (pow_nonneg hu0 n)
        _ = (u ^ n * (1 + 2 * u + u ^ 2 / 2) * Real.exp (-u / 2)) *
            Real.exp (-u / 2) := by
          rw [show Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) by
            rw [← Real.exp_add]; congr 1; ring]
          ring
        _ ≤ majorant n u * Real.exp (-L / 2) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (majorant_nonneg n hu0)
        _ = _ := mul_comm _ _
    _ = Real.exp (-L / 2) * (∫ u : ℝ in Ioi L, majorant n u) := integral_const_mul _ _
    _ ≤ Real.exp (-L / 2) * constant n := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply setIntegral_mono_set (integrable_majorant n)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact majorant_nonneg n hu.le
      · exact Filter.Eventually.of_forall hs
    _ = _ := mul_comm _ _

/-- Direct fixed-threshold density scaling, with no assumption on kernel sign. -/
theorem scaled_moment_tail (n : ℕ) {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    (∫ σ : ℝ in Ioi q, (k * σ) ^ n * |dimensionKernel 2 (k * σ)|) ≤
      (constant n / k) * Real.exp (-(k * q) / 2) := by
  rw [integral_comp_mul_left_Ioi (fun u : ℝ => u ^ n * |dimensionKernel 2 u|) q hk,
    smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left (moment_tail n (mul_pos hk hq))
    (inv_pos.mpr hk).le).trans_eq (by ring)

/-- Logarithmic sectors obey the same fixed-tail estimate one moment higher. -/
theorem logarithmic_tail (n : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    (∫ u : ℝ in Ioi L, u ^ n * |Real.log u * dimensionKernel 2 u|) ≤
      constant (n + 1) * Real.exp (-L / 2) := by
  have hL0 : 0 < L := by linarith
  have hs : Ioi L ⊆ Ioi (0 : ℝ) := fun _ hu => hL0.trans hu
  have hi : IntegrableOn (fun u : ℝ => u ^ n * |Real.log u * dimensionKernel 2 u|) (Ioi 0) := by
    apply (TwoDLogMoments.integrable_log n).norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hu, mul_assoc]
  have hj : IntegrableOn (fun u : ℝ => u ^ (n + 1) * |dimensionKernel 2 u|) (Ioi 0) := by
    apply ((TwoDLogMoments.integrable_rpow (j := ((n + 1 : ℕ) : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) (n + 1); linarith)).norm).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    simp only [Real.norm_eq_abs, abs_mul, Real.rpow_natCast, abs_pow, abs_of_pos hu]
  apply le_trans _ (moment_tail (n + 1) hL0)
  apply setIntegral_mono_on (hi.mono_set hs) (hj.mono_set hs) measurableSet_Ioi
  intro u hu
  have hu1 : 1 ≤ u := hL.trans hu.le
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  rw [abs_mul, abs_of_nonneg (Real.log_nonneg hu1), pow_succ, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.log_le_self hu0) (abs_nonneg _)) (pow_nonneg hu0 n)

theorem scaled_logarithmic_tail (n : ℕ) {k q : ℝ} (hk : 0 < k) (hq : 1 ≤ k * q) :
    (∫ σ : ℝ in Ioi q, (k * σ) ^ n * |Real.log (k * σ) * dimensionKernel 2 (k * σ)|) ≤
      (constant (n + 1) / k) * Real.exp (-(k * q) / 2) := by
  rw [integral_comp_mul_left_Ioi
    (fun u : ℝ => u ^ n * |Real.log u * dimensionKernel 2 u|) q hk, smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left (logarithmic_tail n hq)
    (inv_pos.mpr hk).le).trans_eq (by ring)

end BoundaryDraft.TwoDExponentialTail
