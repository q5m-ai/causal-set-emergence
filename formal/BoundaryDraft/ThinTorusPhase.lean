import BoundaryDraft.ThinTorusIntegration
import BoundaryDraft.ShortRadialAbsolute
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The full thin-slab phase density

The phase density is derived from the complete time/radius integral. Square
root vanishing outside the causal triangle permits continuous rectangular
Fubini, including both time faces and every radial displacement.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace BoundaryDraft
namespace CompactTorus

/-- Actual full time-fibre density per spatial quotient volume. -/
def phaseAmplitude (T w : ℝ) : ℝ :=
  if w ∈ Icc 0 (T ^ 2) then
    2 * Real.pi * ∫ τ in (Real.sqrt w)..T, (T - τ) * Real.sqrt (τ ^ 2 - w)
  else 0

theorem continuous_phaseIntegral (T : ℝ) :
    Continuous (fun w : ℝ => 2 * Real.pi * ∫ τ in (Real.sqrt w)..T, (T - τ) * Real.sqrt (τ ^ 2 - w)) := by
  have hc : Continuous (fun w : ℝ => ∫ τ in T..(Real.sqrt w), (T - τ) * Real.sqrt (τ ^ 2 - w)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (by fun_prop) Real.continuous_sqrt
  simp_rw [intervalIntegral.integral_symm (a := T) (b := Real.sqrt _)]
  exact continuous_const.mul hc.neg

theorem measurable_phaseAmplitude (T : ℝ) : Measurable (phaseAmplitude T) :=
  Measurable.ite measurableSet_Icc (continuous_phaseIntegral T).measurable measurable_const

/-- Compact absolute domination of the actual amplitude, before signed transport. -/
theorem phaseAmplitude_bound (T : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖phaseAmplitude T w‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (T ^ 2)) (continuous_phaseIntegral T).continuousOn
  refine ⟨max 0 C, le_max_left _ _, fun w => ?_⟩
  by_cases hw : w ∈ Icc 0 (T ^ 2)
  · exact (show ‖phaseAmplitude T w‖ ≤ C by
      simpa only [phaseAmplitude, if_pos hw] using hC w hw).trans (le_max_right 0 C)
  · simp only [phaseAmplitude, if_neg hw, norm_zero]
    exact le_max_left _ _

theorem integrable_phaseAmplitude_mul (T : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun w => phaseAmplitude T w * f w) := by
  have hi := (((continuous_phaseIntegral T).mul hf).continuousOn.integrableOn_compact (μ := volume)
    (isCompact_Icc : IsCompact (Icc 0 (T ^ 2)))).integrable_indicator measurableSet_Icc
  apply hi.congr
  exact Eventually.of_forall fun w => by
    by_cases hw : w ∈ Icc 0 (T ^ 2) <;> simp [phaseAmplitude, hw]

/-- Extending the full phase density by zero loses neither endpoint nor tail. -/
theorem phase_halfline (T : ℝ) (f : ℝ → ℝ) :
    (∫ w : ℝ in Ioi 0, phaseAmplitude T w * f w) =
      ∫ w in (0 : ℝ)..T ^ 2, phaseAmplitude T w * f w := by
  have he : (fun w => phaseAmplitude T w * f w) =
      (Icc 0 (T ^ 2)).indicator (fun w => phaseAmplitude T w * f w) := by
    funext w
    by_cases hw : w ∈ Icc 0 (T ^ 2)
    · simp only [indicator_of_mem hw]
    · simp [phaseAmplitude, hw]
  conv_lhs => rw [he, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc 0 (T ^ 2) ∩ Ioi (0 : ℝ) = Ioc 0 (T ^ 2) := by
    ext w
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
  rw [hset, intervalIntegral.integral_of_le (sq_nonneg T)]

private theorem radial_phase {τ : ℝ} (hτ : 0 ≤ τ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ r in (0 : ℝ)..τ, r ^ 2 * f (τ ^ 2 - r ^ 2)) =
      (1 / 2) * ∫ w in (0 : ℝ)..τ ^ 2, Real.sqrt (τ ^ 2 - w) * f w := by
  have hg : Continuous (fun w => Real.sqrt (τ ^ 2 - w) * f w) := by fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv
    (f := fun r : ℝ => τ ^ 2 - r ^ 2) (f' := fun r => -2 * r)
    (g := fun w => Real.sqrt (τ ^ 2 - w) * f w) (a := 0) (b := τ)
    (fun r _ => by convert ((hasDerivAt_id r).pow 2).const_sub (τ ^ 2) using 1; simp)
    (by fun_prop) hg
  have he : (∫ r in (0 : ℝ)..τ,
      (Real.sqrt (τ ^ 2 - (τ ^ 2 - r ^ 2)) * f (τ ^ 2 - r ^ 2)) * (-2 * r)) =
      -2 * ∫ r in (0 : ℝ)..τ, r ^ 2 * f (τ ^ 2 - r ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hτ] at hr
    dsimp only
    rw [show τ ^ 2 - (τ ^ 2 - r ^ 2) = r ^ 2 by ring, Real.sqrt_sq hr.1]
    ring
  simp only [Function.comp_apply, zero_pow (by decide : 2 ≠ 0), sub_zero, sub_self] at h
  rw [he, intervalIntegral.integral_symm (a := 0) (b := τ ^ 2)] at h
  linarith

private theorem phase_fubini {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ) (hf : Continuous f) :
    (4 * Real.pi * ∫ τ in (0 : ℝ)..T, (T - τ) *
      ∫ r in (0 : ℝ)..τ, r ^ 2 * f (τ ^ 2 - r ^ 2)) =
      ∫ w in (0 : ℝ)..T ^ 2, phaseAmplitude T w * f w := by
  let F : ℝ → ℝ → ℝ := fun τ w => (T - τ) * Real.sqrt (τ ^ 2 - w) * f w
  have hc : Continuous (Function.uncurry F) := by dsimp [F, Function.uncurry]; fun_prop
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 (T ^ 2)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs := integral_integral_swap hi
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_of_le (sq_nonneg T)] at hs
  have hrad (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      (T - τ) * (∫ r in (0 : ℝ)..τ, r ^ 2 * f (τ ^ 2 - r ^ 2)) =
        (1 / 2) * ∫ w in (0 : ℝ)..T ^ 2, F τ w := by
    have hg : Continuous (fun w => Real.sqrt (τ ^ 2 - w) * f w) := by fun_prop
    have hz : (∫ w in (τ ^ 2)..T ^ 2, Real.sqrt (τ ^ 2 - w) * f w) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_).trans
        intervalIntegral.integral_zero
      intro w hw
      dsimp only
      rw [uIcc_of_le (sq_le_sq₀ hτ.1 hT |>.mpr hτ.2)] at hw
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith [hw.1]), zero_mul]
    rw [radial_phase hτ.1 f hf]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hg.intervalIntegrable 0 (τ ^ 2)) (hg.intervalIntegrable (τ ^ 2) (T ^ 2))
    rw [hz, add_zero] at hadd
    rw [hadd]
    simp only [F, mul_assoc, intervalIntegral.integral_const_mul]
    ring
  have hcol (w : ℝ) (hw : w ∈ Icc 0 (T ^ 2)) :
      2 * Real.pi * (∫ τ in (0 : ℝ)..T, F τ w) = phaseAmplitude T w * f w := by
    have hfτ : Continuous (fun τ : ℝ => F τ w) := hc.comp (continuous_id.prodMk continuous_const)
    have hz : (∫ τ in (0 : ℝ)..Real.sqrt w, F τ w) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_).trans
        intervalIntegral.integral_zero
      intro τ hτ
      rw [uIcc_of_le (Real.sqrt_nonneg w)] at hτ
      have hsq : τ ^ 2 ≤ w := by
        calc
          τ ^ 2 ≤ (Real.sqrt w) ^ 2 := pow_le_pow_left₀ hτ.1 hτ.2 2
          _ = w := Real.sq_sqrt hw.1
      simp [F, Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hsq)]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hfτ.intervalIntegrable 0 (Real.sqrt w)) (hfτ.intervalIntegrable (Real.sqrt w) T)
    rw [hz, zero_add] at hadd
    rw [← hadd, phaseAmplitude, if_pos hw]
    simp only [F, intervalIntegral.integral_mul_const]
    ring
  rw [intervalIntegral.integral_congr (fun τ hτ => hrad τ (by rwa [uIcc_of_le hT] at hτ)),
    intervalIntegral.integral_const_mul]
  have hfactor (z : ℝ) : 4 * Real.pi * ((1 / 2) * z) = 2 * Real.pi * z := by ring
  rw [hfactor, hs, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun w hw => hcol w (by rwa [uIcc_of_le (sq_nonneg T)] at hw)

/-- The regular part of the evaluated phase primitive. The singular logarithm
is kept separate and has a geometrically derived coefficient. -/
def phaseSmooth (T w : ℝ) : ℝ :=
  Real.pi * T * (T * Real.sqrt (T ^ 2 - w) - w * Real.log (T + Real.sqrt (T ^ 2 - w))) -
    (2 * Real.pi / 3) * Real.sqrt (T ^ 2 - w) ^ 3

private def phasePrimitive (T w τ : ℝ) : ℝ :=
  Real.pi * T * (τ * Real.sqrt (τ ^ 2 - w) - w * Real.log (τ + Real.sqrt (τ ^ 2 - w))) -
    (2 * Real.pi / 3) * Real.sqrt (τ ^ 2 - w) ^ 3

private theorem phasePrimitive_deriv (T : ℝ) {w τ : ℝ} (hw : 0 < w) (hτ : Real.sqrt w < τ) :
    HasDerivAt (phasePrimitive T w) (2 * Real.pi * (T - τ) * Real.sqrt (τ ^ 2 - w)) τ := by
  have hτ0 : 0 < τ := (Real.sqrt_pos.mpr hw).trans hτ
  have hsq : 0 < τ ^ 2 - w := by nlinarith [Real.sq_sqrt hw.le, Real.sqrt_nonneg w]
  have hr : 0 < Real.sqrt (τ ^ 2 - w) := Real.sqrt_pos.mpr hsq
  have hrsq := Real.sq_sqrt hsq.le
  have hp : τ + Real.sqrt (τ ^ 2 - w) ≠ 0 := ne_of_gt (add_pos hτ0 hr)
  have hd : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - w))
      (τ / Real.sqrt (τ ^ 2 - w)) τ := by
    convert (((hasDerivAt_id τ).pow 2).sub_const w).sqrt hsq.ne' using 1
    dsimp
    field_simp
    ring
  have hl : HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t ^ 2 - w)))
      (1 / Real.sqrt (τ ^ 2 - w)) τ := by
    convert ((hasDerivAt_id τ).add hd).log hp using 1
    dsimp
    field_simp
    ring
  have hfirst : HasDerivAt
      (fun t : ℝ => t * Real.sqrt (t ^ 2 - w) - w * Real.log (t + Real.sqrt (t ^ 2 - w)))
      (2 * Real.sqrt (τ ^ 2 - w)) τ := by
    convert ((hasDerivAt_id τ).mul hd).sub (hl.const_mul w) using 1
    dsimp
    field_simp
    nlinarith
  have hcubic : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - w) ^ 3)
      (3 * τ * Real.sqrt (τ ^ 2 - w)) τ := by
    convert hd.pow 3 using 1
    dsimp
    field_simp
    nlinarith only [congrArg (fun z : ℝ => 3 * τ * z) hrsq]
  convert (hfirst.const_mul (Real.pi * T)).sub (hcubic.const_mul (2 * Real.pi / 3)) using 1
  ring

/-- The actual full phase amplitude, including its retained logarithmic term.
No expansion coefficient or interval-volume identity is assumed. -/
theorem phaseAmplitude_eq_log {T w : ℝ} (hT : 0 < T) (hw : 0 < w) (hwT : w ≤ T ^ 2) :
    phaseAmplitude T w = phaseSmooth T w + (Real.pi * T / 2) * (w * Real.log w) := by
  have hs : Real.sqrt w ≤ T := Real.sqrt_le_iff.mpr ⟨hT.le, hwT⟩
  have hp (t : ℝ) (ht : t ∈ Icc (Real.sqrt w) T) : t + Real.sqrt (t ^ 2 - w) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ((Real.sqrt_pos.mpr hw).trans_le ht.1) (Real.sqrt_nonneg _))
  have hc : ContinuousOn (phasePrimitive T w) (Icc (Real.sqrt w) T) := by
    unfold phasePrimitive
    exact (continuousOn_const.mul ((continuousOn_id.mul (by fun_prop)).sub
      (continuousOn_const.mul ((continuousOn_id.add (by fun_prop)).log hp)))).sub (by fun_prop)
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hc
    (fun t ht => phasePrimitive_deriv T hw ht.1)
    ((show Continuous (fun t : ℝ => 2 * Real.pi * (T - t) * Real.sqrt (t ^ 2 - w)) by
      fun_prop).intervalIntegrable _ _)
  rw [phaseAmplitude, if_pos ⟨hw.le, hwT⟩, ← intervalIntegral.integral_const_mul]
  have he : (∫ t in (Real.sqrt w)..T, 2 * Real.pi * ((T - t) * Real.sqrt (t ^ 2 - w))) =
      ∫ t in (Real.sqrt w)..T, 2 * Real.pi * (T - t) * Real.sqrt (t ^ 2 - w) := by
    congr 1
    funext t
    ring
  rw [he, hd]
  simp only [phasePrimitive, phaseSmooth, Real.sq_sqrt hw.le, sub_self, Real.sqrt_zero,
    mul_zero, add_zero, zero_pow (by decide : 3 ≠ 0), sub_zero, zero_sub, Real.log_sqrt hw.le]
  ring

variable (L : ℝ) [Fact (0 < L)]

/-- Exact full quotient pair-to-phase reduction at every finite density. -/
theorem pair_integral_phase {T : ℝ} (hT0 : 0 ≤ T) (hT : 2 * T < L) (ρ : ℝ) :
    (∫ x, ∫ y in {y | (measuredOrder L).Rel x y},
      bdgKernel (ρ * (slabVolume L T ((measuredOrder L).interval x y)).toReal)
        ∂slabVolume L T ∂slabVolume L T) =
      L ^ 3 * ∫ w in (0 : ℝ)..T ^ 2,
        phaseAmplitude T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2) := by
  rw [pair_integral_radial L hT0 hT]
  exact congrArg (fun z => L ^ 3 * z) (phase_fubini hT0
    (fun w => bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) (by unfold bdgKernel bdgPolynomial; fun_prop))

end CompactTorus
end BoundaryDraft
