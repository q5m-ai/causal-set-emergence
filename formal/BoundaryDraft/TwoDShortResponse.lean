import BoundaryDraft.TwoDQuadraticResponse

/-!
# Signed response of the genuine 2D sharp polynomial model

The logarithmic sectors have exact signed responses. A globally quadratic
error controls the sharp fixed cutoff; its constant may depend on that cutoff.
The point term is allocated once, and the independent endpoint coefficient
survives with unit normalization.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDShortResponse

def lowDensity (a b V J σ : ℝ) : ℝ :=
  a + b * σ - (V / 2) * Real.log σ - (J / 8) * σ * Real.log σ

def modelDensity (q a b V J c σ : ℝ) : ℝ :=
  if 0 < σ ∧ σ ≤ q then lowDensity a b V J σ - c * σ ^ 2 else 0

def modelAction (q a b V J c ρ : ℝ) : ℝ :=
  ρ * (dimensionPointCoefficient 2 * V - dimensionPairCoefficient 2 * ρ *
    ∫ σ : ℝ in Ioi 0, modelDensity q a b V J c σ *
      dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ))

theorem measurable_lowDensity (a b V J : ℝ) : Measurable (lowDensity a b V J) := by
  unfold lowDensity
  fun_prop

theorem measurable_modelDensity (q a b V J c : ℝ) : Measurable (modelDensity q a b V J c) := by
  unfold modelDensity
  exact ((measurable_lowDensity a b V J).sub (by fun_prop)).ite measurableSet_Ioc measurable_const

theorem integrable_lowDensity (a b V J : ℝ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun σ : ℝ => lowDensity a b V J σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
  have h0 : IntegrableOn (fun σ : ℝ => dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_power 0 hk
  have h1 : IntegrableOn (fun σ : ℝ => σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_power 1 hk
  have hL0 : IntegrableOn (fun σ : ℝ => Real.log σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_log 0 hk
  have hL1 : IntegrableOn (fun σ : ℝ => σ * Real.log σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_log 1 hk
  apply (((h0.const_mul a).add (h1.const_mul b)).sub (hL0.const_mul (V / 2))).sub
    (hL1.const_mul (J / 8)) |>.congr
  exact Eventually.of_forall fun σ => by dsimp [lowDensity]; ring

/-- No absolute value is put inside the signed kernel calculation. -/
theorem integral_lowDensity (a b V J : ℝ) {k : ℝ} (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, lowDensity a b V J σ * dimensionKernel 2 (k * σ)) =
      V / (4 * k) - J / (16 * k ^ 2) := by
  have h0 : IntegrableOn (fun σ : ℝ => dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_power 0 hk
  have h1 : IntegrableOn (fun σ : ℝ => σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_power 1 hk
  have hL0 : IntegrableOn (fun σ : ℝ => Real.log σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_log 0 hk
  have hL1 : IntegrableOn (fun σ : ℝ => σ * Real.log σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
    simpa using TwoDLogMoments.integrable_scaled_log 1 hk
  have he : (fun σ : ℝ => lowDensity a b V J σ * dimensionKernel 2 (k * σ)) =
      fun σ => (a * dimensionKernel 2 (k * σ) + b * (σ * dimensionKernel 2 (k * σ))) -
        (V / 2) * (Real.log σ * dimensionKernel 2 (k * σ)) -
        (J / 8) * (σ * Real.log σ * dimensionKernel 2 (k * σ)) := by
    funext σ
    unfold lowDensity
    ring
  have hs₂ := integral_sub (((h0.const_mul a).add (h1.const_mul b)).sub (hL0.const_mul (V / 2)))
    (hL1.const_mul (J / 8))
  have hs₁ := integral_sub ((h0.const_mul a).add (h1.const_mul b)) (hL0.const_mul (V / 2))
  have hs₀ := integral_add (h0.const_mul a) (h1.const_mul b)
  simp only [Pi.add_apply, Pi.sub_apply] at hs₂ hs₁ hs₀
  rw [he, hs₂, hs₁, hs₀]
  simp only [integral_const_mul]
  have hz0 : (∫ σ : ℝ in Ioi 0, dimensionKernel 2 (k * σ)) = 0 := by
    simpa using TwoDLogMoments.scaled_power_zero 0 (by norm_num) hk
  have hz1 : (∫ σ : ℝ in Ioi 0, σ * dimensionKernel 2 (k * σ)) = 0 := by
    simpa using TwoDLogMoments.scaled_power_zero 1 (by norm_num) hk
  rw [hz0, hz1, TwoDLogMoments.scaled_log_zero hk, TwoDLogMoments.scaled_log_one hk]
  field_simp
  ring

/-- Exact point-term cancellation and unit endpoint response at every positive
physical density. This is NOT yet the response of the sharp/actual density. -/
theorem low_action_eq (a b V J : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ * (dimensionPointCoefficient 2 * V - dimensionPairCoefficient 2 * ρ *
      ∫ σ : ℝ in Ioi 0, lowDensity a b V J σ *
        dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ)) = J := by
  rw [integral_lowDensity a b V J (mul_pos (dimensionIntervalCoefficient_pos 2 (by norm_num)) hρ),
    dimensionPointCoefficient_two, dimensionPairCoefficient_two, dimensionIntervalCoefficient_two]
  field_simp [hρ.ne']
  ring

private theorem low_bound_above (a b V J : ℝ) {q σ : ℝ} (hq : 0 < q) (hqs : q ≤ σ) :
    |lowDensity a b V J σ| ≤
      (|a| / q ^ 2 + |b| / q + |V / 2| * (1 / q + 1 / q ^ 3) +
        |J / 8| * (1 + 1 / q ^ 2)) * σ ^ 2 := by
  have hσ := hq.trans_le hqs
  have h1 : (1 : ℝ) ≤ σ ^ 2 / q ^ 2 := (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by nlinarith)
  have hlin : σ ≤ σ ^ 2 / q := (le_div_iff₀ hq).mpr (by nlinarith)
  have hinv : σ⁻¹ ≤ σ ^ 2 / q ^ 3 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hσ (pow_pos hq 3)]
    simpa only [one_mul, pow_succ] using pow_le_pow_left₀ hq.le hqs 3
  have hlog : |Real.log σ| ≤ σ + σ⁻¹ := by
    exact abs_le.mpr ⟨by linarith [Real.neg_inv_le_log hσ.le],
      by linarith [Real.log_le_self hσ.le, inv_nonneg.mpr hσ.le]⟩
  have hmul : |σ * Real.log σ| ≤ 1 + σ ^ 2 := by
    rw [abs_mul, abs_of_pos hσ]
    apply (mul_le_mul_of_nonneg_left hlog hσ.le).trans_eq
    field_simp
    ring
  have ht : |lowDensity a b V J σ| ≤
      |a| + |b| * σ + |V / 2| * |Real.log σ| + |J / 8| * |σ * Real.log σ| := by
    calc
      _ ≤ |a + b * σ - (V / 2) * Real.log σ| + |(J / 8) * σ * Real.log σ| := abs_sub _ _
      _ ≤ |a + b * σ| + |(V / 2) * Real.log σ| + |(J / 8) * σ * Real.log σ| := by
        gcongr
        exact abs_sub _ _
      _ ≤ |a| + |b * σ| + |(V / 2) * Real.log σ| + |(J / 8) * σ * Real.log σ| := by
        gcongr
        exact abs_add _ _
      _ = _ := by simp only [abs_mul, abs_of_pos hσ]; ring
  calc
    _ ≤ |a| + |b| * σ + |V / 2| * |Real.log σ| + |J / 8| * |σ * Real.log σ| := ht
    _ ≤ |a| * (σ ^ 2 / q ^ 2) + |b| * (σ ^ 2 / q) +
        |V / 2| * (σ ^ 2 / q + σ ^ 2 / q ^ 3) + |J / 8| * (σ ^ 2 / q ^ 2 + σ ^ 2) := by
      gcongr
      · exact le_mul_of_one_le_right (abs_nonneg a) h1
      · exact hlog.trans (add_le_add hlin hinv)
      · exact hmul.trans (by linarith)
    _ = _ := by ring

/-- One fixed cutoff suffices; the error has a global quadratic bound. -/
theorem model_error_bound {q : ℝ} (hq : 0 < q) (a b V J c : ℝ) :
    ∃ C : ℝ, ∀ σ, 0 < σ → ‖modelDensity q a b V J c σ - lowDensity a b V J σ‖ ≤ C * σ ^ 2 := by
  let D := |a| / q ^ 2 + |b| / q + |V / 2| * (1 / q + 1 / q ^ 3) + |J / 8| * (1 + 1 / q ^ 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨|c| + D, ?_⟩
  intro σ hσ
  by_cases hs : σ ≤ q
  · simp only [modelDensity, if_pos (show 0 < σ ∧ σ ≤ q from ⟨hσ, hs⟩), sub_sub_cancel_left, norm_neg, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg σ)]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg σ)
  · simp only [modelDensity, if_neg (not_and.mpr (fun _ => hs)), zero_sub, norm_neg, Real.norm_eq_abs]
    exact (low_bound_above a b V J hq (not_le.mp hs).le).trans
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg c]) (sq_nonneg σ))

theorem integrable_modelDensity {q : ℝ} (hq : 0 < q) (a b V J c : ℝ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun σ : ℝ => modelDensity q a b V J c σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := model_error_bound hq a b V J c
  have hE := TwoDQuadraticResponse.integrable_of_bound _
    ((measurable_modelDensity q a b V J c).sub (measurable_lowDensity a b V J)) C hC hk
  apply (hE.add (integrable_lowDensity a b V J hk)).congr
  exact Eventually.of_forall fun _ => by dsimp; ring

/-- The sharp model converges only after the signed logarithmic responses and
quadratic comparison estimate have both been established. -/
theorem tendsto_modelAction {q : ℝ} (hq : 0 < q) (a b V J c : ℝ) :
    Tendsto (modelAction q a b V J c) atTop (𝓝 J) := by
  obtain ⟨C, hC⟩ := model_error_bound hq a b V J c
  have hE := TwoDQuadraticResponse.limit_of_bound _
    ((measurable_modelDensity q a b V J c).sub (measurable_lowDensity a b V J)) C hC
    (dimensionIntervalCoefficient_pos 2 (by norm_num))
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => J) atTop (𝓝 J)).sub
    (hE.const_mul (dimensionPairCoefficient 2))
  simp only [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hk := mul_pos (dimensionIntervalCoefficient_pos 2 (by norm_num)) hρ
  have he : (∫ σ : ℝ in Ioi 0, (modelDensity q a b V J c σ - lowDensity a b V J σ) *
      dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ)) =
      (∫ σ : ℝ in Ioi 0, modelDensity q a b V J c σ * dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ)) -
      (∫ σ : ℝ in Ioi 0, lowDensity a b V J σ * dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ)) := by
    simp_rw [sub_mul]
    exact integral_sub (integrable_modelDensity hq a b V J c hk) (integrable_lowDensity a b V J hk)
  rw [he]
  nth_rw 1 [← low_action_eq a b V J hρ]
  unfold modelAction
  ring

end TwoDShortResponse
end BoundaryDraft
