import BoundaryDraft.ThinTorusPhase

/-!
# Deterministic and Poisson-expected thin-torus zero limits

The actual phase primitive identifies the logarithm. Its signed response
cancels the physical point volume exactly. The remaining signed integral is
controlled by a second, exact finite-primitive identity with `planeKernel`,
whose absolute tail was independently checked. No desired Taylor jet is an
input, and no phase or geometric cutoff depends on density.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace BoundaryDraft
namespace CompactTorus

/-- The logarithmic contribution derived in `phaseAmplitude_eq_log`. -/
def phaseLog (T w : ℝ) : ℝ := (Real.pi * T / 2) * (w * Real.log w)

/-- The ACTUAL remainder after subtracting precisely the derived logarithm.
This is not a prescribed quadratic jet. It includes the uncut logarithmic tail. -/
def phaseRemainder (T w : ℝ) : ℝ := phaseAmplitude T w - phaseLog T w

theorem phaseRemainder_eq_smooth {T w : ℝ} (hT : 0 < T) (hw : 0 < w) (hwT : w ≤ T ^ 2) :
    phaseRemainder T w = phaseSmooth T w := by
  rw [phaseRemainder, phaseAmplitude_eq_log hT hw hwT]
  simp [phaseLog]

theorem integrable_phaseLog {ρ : ℝ} (hρ : 0 < ρ) (T : ℝ) :
    IntegrableOn (fun w => phaseLog T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) (Ioi 0) := by
  have hk : 0 < Real.sqrt ((Real.pi / 24) * ρ) := by positivity
  have he (w : ℝ) : (Real.pi / 24) * ρ * w ^ 2 = (Real.sqrt ((Real.pi / 24) * ρ) * w) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  simp_rw [he]
  apply ((integrableOn_bdgKernel_transverse_scaled_log_one _ hk).const_mul
    (Real.pi * T / 2)).congr
  exact Eventually.of_forall fun w => by unfold phaseLog; ring

/-- Original signed logarithmic moment, with its full geometric normalization. -/
theorem phaseLog_response {ρ : ℝ} (hρ : 0 < ρ) (T : ℝ) :
    (∫ w : ℝ in Ioi 0, phaseLog T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) = T / ρ := by
  have hk : 0 < Real.sqrt ((Real.pi / 24) * ρ) := by positivity
  have he (w : ℝ) : (Real.pi / 24) * ρ * w ^ 2 = (Real.sqrt ((Real.pi / 24) * ρ) * w) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  simp_rw [he, phaseLog, mul_assoc]
  rw [integral_const_mul]
  have h := integral_bdgKernel_transverse_scaled_log_one _ hk
  simp only [mul_assoc] at h
  rw [h, inv_pow, Real.sq_sqrt (by positivity)]
  field_simp [Real.pi_ne_zero, hρ.ne']
  ring

/-- One physical point volume, not one allocation per chart or endpoint. -/
theorem phaseLog_point_cancellation (L T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ * (L ^ 3 * T - ρ * L ^ 3 *
      ∫ w : ℝ in Ioi 0, phaseLog T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) = 0 := by
  rw [phaseLog_response hρ]
  field_simp [hρ.ne']
  ring

theorem integrable_phaseRemainder {ρ : ℝ} (hρ : 0 < ρ) (T : ℝ) :
    IntegrableOn (fun w => phaseRemainder T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) (Ioi 0) := by
  have hi := (integrable_phaseAmplitude_mul T
    (fun w => bdgKernel ((Real.pi / 24) * ρ * w ^ 2))
    (by unfold bdgKernel bdgPolynomial; fun_prop)).integrableOn (s := Ioi 0)
  simpa only [phaseRemainder, sub_mul] using hi.sub (integrable_phaseLog hρ T)

variable (L : ℝ) [Fact (0 < L)]

/-- Exact signed remainder evaluation from the complete pair integral and finite
auxiliary primitives. This precedes, rather than assumes, the zero limit. -/
theorem phaseRemainder_exact {T : ℝ} (hT0 : 0 < T) (hT : 2 * T < L) {ρ : ℝ} (hρ : 0 < ρ) :
    -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      (∫ w : ℝ in Ioi 0, phaseRemainder T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) =
      planeKernel ρ T := by
  have h := action_eq_planeKernel L hT0.le hT ρ
  rw [MeasuredOrderBDG4.action_eq, slabVolume_univ,
    ENNReal.toReal_ofReal (mul_nonneg hT0.le (pow_nonneg (le_of_lt (Fact.out : 0 < L)) 3)),
    pair_integral_phase L hT0.le hT,
    ← phase_halfline] at h
  have hi := (integrable_phaseAmplitude_mul T
    (fun w => bdgKernel ((Real.pi / 24) * ρ * w ^ 2))
    (by unfold bdgKernel bdgPolynomial; fun_prop)).integrableOn (s := Ioi 0)
  simp_rw [phaseRemainder, sub_mul]
  rw [integral_sub hi (integrable_phaseLog hρ T), phaseLog_response hρ]
  apply (mul_left_cancel₀ (pow_ne_zero 3 (ne_of_gt (Fact.out : 0 < L))))
  convert h using 1
  field_simp [hρ.ne']
  ring

/-- Absolute control of the whole signed remainder, including its fixed-phase
complement and the subtracted logarithmic tail. It is derived from the exact
finite primitive, not a value-only bound on a postulated density jet. -/
theorem phaseRemainder_bound {T : ℝ} (hT0 : 0 < T) (hT : 2 * T < L) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖-(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      (∫ w : ℝ in Ioi 0, phaseRemainder T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2))‖ ≤
      (1416 / (Real.pi * Real.sqrt 6)) * ((Real.sqrt (Real.sqrt ρ))⁻¹) ^ 2 / T ^ 3 := by
  rw [phaseRemainder_exact L hT0 hT hρ, Real.norm_eq_abs]
  exact abs_planeKernel_density_le ρ T hρ hT0

/-- The fixed positive-phase complement can also be discarded separately, by an
absolute bound. The threshold is arbitrary but fixed before density varies. -/
theorem fixed_phase_complement (T : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ w : ℝ in Ioi 0,
      (Ici δ).indicator (phaseAmplitude T) w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := phaseAmplitude_bound T
  apply bdgKernel_cubic_cancellation _
    ((measurable_phaseAmplitude T).indicator measurableSet_Ici) (C / δ ^ 3) _ _ (by positivity)
  intro w hw
  by_cases hwd : δ ≤ w
  · rw [indicator_of_mem (show w ∈ Ici δ from hwd)]
    apply (hb w).trans
    have hp : δ ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ hδ.le hwd 3
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (pow_pos hδ 3)).mpr (mul_le_mul_of_nonneg_left hp hC)
  · rw [indicator_of_not_mem (show w ∉ Ici δ from hwd), norm_zero]
    positivity

/-- The full actual deterministic action of a fixed thin slab tends to zero. -/
theorem action_limit {T : ℝ} (hT0 : 0 < T) (hT : 2 * T < L) :
    Tendsto (fun ρ => MeasuredOrderBDG4.action (measuredOrder L) (slabVolume L T) ρ)
      atTop (𝓝 0) := by
  have hp : Tendsto (fun ρ => planeKernel ρ T) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
      simpa only [Real.norm_eq_abs] using abs_planeKernel_density_le ρ T hρ hT0
    · simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] using
        ((tendsto_density_width.pow 2).const_mul (1416 / (Real.pi * Real.sqrt 6))).div_const (T ^ 3)
  simpa only [action_eq_planeKernel L hT0.le hT, mul_zero] using hp.const_mul (L ^ 3)

/-- Separate expectation transfer under the existing ACTUAL finite Poisson law.
This is a limit of expectations, not a sample-wise convergence theorem. -/
theorem expectedAction_limit {T : ℝ} (hT0 : 0 < T) (hT : 2 * T < L) :
    Tendsto (fun ρ => ∫ c, MeasuredOrderBDG4.discreteAction (measuredOrder L) ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • slabVolume L T)) atTop (𝓝 0) := by
  apply (action_limit L hT0 hT).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (expectation_eq L T hρ).symm

end CompactTorus

/-- Unconditional checked thin-torus port with the original geometric inputs.
The two conclusions retain distinct deterministic and probability observables. -/
theorem thinFlatTorusLimit4 (L T : ℝ) (hL : 0 < L) (hT : 0 < T) (hthin : T < L / 2) :
    letI : Fact (0 < L) := ⟨hL⟩
    Tendsto (fun ρ => MeasuredOrderBDG4.action (CompactTorus.measuredOrder L)
      (CompactTorus.slabVolume L T) ρ) atTop (𝓝 0) ∧
    Tendsto (fun ρ => ∫ c, MeasuredOrderBDG4.discreteAction (CompactTorus.measuredOrder L) ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • CompactTorus.slabVolume L T)) atTop (𝓝 0) := by
  letI : Fact (0 < L) := ⟨hL⟩
  exact ⟨CompactTorus.action_limit L hT (by linarith),
    CompactTorus.expectedAction_limit L hT (by linarith)⟩

end BoundaryDraft
