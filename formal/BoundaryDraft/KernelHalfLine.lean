import BoundaryDraft.KernelEstimates
import BoundaryDraft.AnalyticCore
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Half-line normalization of the concrete signed plane kernel

Absolute estimates precede every improper-integral passage. Normalization is
obtained from the Gaussian integral and dominated convergence, not numerical
quadrature or an assumption about the derivative of an asymptotic expansion.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

namespace BoundaryDraft

private def auxiliaryProfile (u s : ℝ) : ℝ :=
  Real.sqrt (1 - s / u ^ 2) * Real.exp (-(Real.pi / 24) * s ^ 2)

private theorem auxiliaryProfile_bound (u : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ‖auxiliaryProfile u s‖ ≤ Real.exp (-(Real.pi / 24) * s ^ 2) := by
  have hsq : Real.sqrt (1 - s / u ^ 2) ≤ 1 := by
    apply Real.sqrt_le_one.2
    exact sub_le_self _ (div_nonneg hs (sq_nonneg u))
  rw [auxiliaryProfile, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) hsq

/-- A half-line representation with a bounded square-root weight. The weight
vanishes beyond `u²`, so it introduces no unproved extension of the integral. -/
theorem planeAuxiliary_div_eq_integral {u : ℝ} (hu : 0 < u) :
    planeAuxiliary 1 u / u = 2 * Real.pi *
      ∫ s in Ioi (0 : ℝ), Real.sqrt (1 - s / u ^ 2) * Real.exp (-(Real.pi / 24) * s ^ 2) := by
  have hu0 := ne_of_gt hu
  have hscale := intervalIntegral.smul_integral_comp_mul_left (auxiliaryProfile u)
    (a := 0) (b := 1) (u ^ 2)
  simp only [smul_eq_mul, mul_zero, mul_one] at hscale
  have hp (t : ℝ) : auxiliaryProfile u (u ^ 2 * t) =
      Real.sqrt (1 - t) * Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2) := by
    unfold auxiliaryProfile
    congr 2
    · field_simp
    · ring
  simp_rw [hp] at hscale
  have hsupport : (∫ s in Ioi (0 : ℝ), auxiliaryProfile u s) =
      ∫ s in (0 : ℝ)..u ^ 2, auxiliaryProfile u s := by
    rw [intervalIntegral.integral_of_le (sq_nonneg u)]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro s hs
    have hs' : u ^ 2 < s := by
      by_contra h
      exact hs.2 ⟨hs.1, le_of_not_gt h⟩
    unfold auxiliaryProfile
    rw [Real.sqrt_eq_zero_of_nonpos, zero_mul]
    exact sub_nonpos.mpr ((le_div_iff₀ (sq_pos_of_pos hu)).2 (by simpa using hs'.le))
  change _ = 2 * Real.pi * ∫ s in Ioi (0 : ℝ), auxiliaryProfile u s
  rw [hsupport, ← hscale, planeAuxiliary_eq_sqrt_integral]
  field_simp
  ring

/-- The large-argument slope of the auxiliary integral itself, justified by
an integrable Gaussian majorant on the positive half-line. -/
theorem tendsto_planeAuxiliary_div :
    Tendsto (fun u : ℝ => planeAuxiliary 1 u / u) atTop (𝓝 (2 * Real.pi * Real.sqrt 6)) := by
  have hinv : Tendsto (fun u : ℝ => (u ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).pow 2
  have hg : IntegrableOn (fun s : ℝ => Real.exp (-(Real.pi / 24) * s ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 24)).integrableOn
  have hlim : Tendsto (fun u : ℝ => ∫ s in Ioi (0 : ℝ), auxiliaryProfile u s)
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * s ^ 2))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun s : ℝ => Real.exp (-(Real.pi / 24) * s ^ 2))
    · exact Eventually.of_forall fun u =>
        (by unfold auxiliaryProfile; fun_prop : Continuous (auxiliaryProfile u)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro u
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact auxiliaryProfile_bound u hs.le
    · exact hg
    · apply Eventually.of_forall
      intro s
      have hs : Tendsto (fun u : ℝ => 1 - s / u ^ 2) atTop (𝓝 1) := by
        simpa [div_eq_mul_inv] using tendsto_const_nhds.sub (hinv.const_mul s)
      have hsqrt : Tendsto (fun u : ℝ => Real.sqrt (1 - s / u ^ 2)) atTop (𝓝 1) := by
        simpa only [Real.sqrt_one] using (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hs
      change Tendsto (fun u : ℝ => Real.sqrt (1 - s / u ^ 2) *
        Real.exp (-(Real.pi / 24) * s ^ 2)) atTop (𝓝 (Real.exp (-(Real.pi / 24) * s ^ 2)))
      simpa only [one_mul] using hsqrt.mul_const (Real.exp (-(Real.pi / 24) * s ^ 2))
  have hgauss : (∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * s ^ 2)) = Real.sqrt 6 := by
    rw [integral_gaussian_Ioi,
      show Real.pi / (Real.pi / 24) = 4 * 6 by field_simp; ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hs4]
    ring
  rw [hgauss] at hlim
  apply (hlim.const_mul (2 * Real.pi)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (planeAuxiliary_div_eq_integral hu).symm

/-- The boundary term for the signed first moment tends to zero. -/
theorem tendsto_mul_planeAuxiliaryFirst_sub :
    Tendsto (fun u : ℝ => u * planeAuxiliaryFirst 1 u - planeAuxiliary 1 u) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _
    (by simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).const_mul 240)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  simpa only [Real.norm_eq_abs] using abs_mul_planeAuxiliaryFirst_sub_le hu

/-- The limiting first derivative needed for the half-line mass identity. -/
theorem tendsto_planeAuxiliaryFirst :
    Tendsto (planeAuxiliaryFirst 1) atTop (𝓝 (2 * Real.pi * Real.sqrt 6)) := by
  have h := (tendsto_mul_planeAuxiliaryFirst_sub.mul
    (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0))).add
      tendsto_planeAuxiliary_div
  simp only [zero_mul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  field_simp

private theorem integrableOn_Ioi_of_abs_le_inv_pow (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (n : ℕ) (hn : 1 < n)
    (hbound : ∀ u : ℝ, 1 ≤ u → |f u| ≤ C / u ^ n) : IntegrableOn f (Ioi (0 : ℝ)) := by
  have hpow : IntegrableOn (fun u : ℝ => C / u ^ n) (Ioi (1 : ℝ)) := by
    have hn' : -(n : ℝ) < -1 := neg_lt_neg (by exact_mod_cast hn)
    have h : IntegrableOn (fun u : ℝ => C * u ^ (-(n : ℝ))) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hn' zero_lt_one).const_mul C
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    change C * u ^ (-(n : ℝ)) = C / u ^ n
    rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one hu)), Real.rpow_natCast, div_eq_mul_inv]
  have htail : IntegrableOn f (Ioi (1 : ℝ)) := by
    apply hpow.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [Real.norm_eq_abs] using hbound u hu.le
  have hcompact : IntegrableOn f (Ioc (0 : ℝ) 1) :=
    (hf.intervalIntegrable 0 1).1
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using hcompact.union htail

/-- Absolute (Bochner) integrability of the concrete signed kernel. -/
theorem integrableOn_planeKernel : IntegrableOn (planeKernel 1) (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_of_abs_le_inv_pow _ (continuous_planeKernel 1)
    (1416 / (Real.pi * Real.sqrt 6)) 3 (by norm_num)
  intro u hu
  exact abs_planeKernel_le (lt_of_lt_of_le zero_lt_one hu)

/-- The first *absolute* moment is integrable; a signed cancellation alone
would not suffice for this theorem. -/
theorem integrableOn_mul_abs_planeKernel :
    IntegrableOn (fun u => u * |planeKernel 1 u|) (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_of_abs_le_inv_pow _
    (continuous_id.mul (continuous_planeKernel 1).abs)
    (1416 / (Real.pi * Real.sqrt 6)) 2 (by norm_num)
  intro u hu
  have hu' : 0 < u := lt_of_lt_of_le zero_lt_one hu
  change |u * (|planeKernel 1 u|)| ≤ _
  rw [abs_mul, abs_of_pos hu', abs_abs]
  apply (mul_le_mul_of_nonneg_left (abs_planeKernel_le hu') hu'.le).trans_eq
  field_simp
  ring

/-- Half-line mass obtained by passing the checked finite-interval identity
to infinity, now with absolute integrability and a proved derivative limit. -/
theorem integral_planeKernel_Ioi : (∫ u in Ioi (0 : ℝ), planeKernel 1 u) = 1 := by
  have h := tendsto_planeAuxiliaryFirst.const_mul (1 / (2 * Real.pi * Real.sqrt 6))
  have hconst : 1 / (2 * Real.pi * Real.sqrt 6) * (2 * Real.pi * Real.sqrt 6) = 1 := by
    field_simp
  rw [hconst] at h
  have hfinite : Tendsto (fun H : ℝ => ∫ u in (0 : ℝ)..H, planeKernel 1 u) atTop (𝓝 1) := by
    simpa only [integral_planeKernel, Real.sqrt_one] using h
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 integrableOn_planeKernel tendsto_id) hfinite

/-- The unchanged concrete mass target, including its absolute first moment. -/
theorem kernelMassGoal : KernelMassGoal :=
  ⟨integrableOn_planeKernel, integral_planeKernel_Ioi, integrableOn_mul_abs_planeKernel⟩

/-- The signed first moment vanishes, separately from its absolute integrability. -/
theorem integral_mul_planeKernel_Ioi : (∫ u in Ioi (0 : ℝ), u * planeKernel 1 u) = 0 := by
  have hi : IntegrableOn (fun u => u * planeKernel 1 u) (Ioi (0 : ℝ)) := by
    apply integrableOn_mul_abs_planeKernel.mono'
      (continuous_id.mul (continuous_planeKernel 1)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [Real.norm_eq_abs, id_eq, abs_mul, abs_of_pos (show 0 < u from hu), le_refl]
  have h := tendsto_mul_planeAuxiliaryFirst_sub.const_mul (1 / (2 * Real.pi * Real.sqrt 6))
  simp only [mul_zero] at h
  have hfinite : Tendsto (fun H : ℝ => ∫ u in (0 : ℝ)..H, u * planeKernel 1 u) atTop (𝓝 0) := by
    simpa only [integral_mul_planeKernel, Real.sqrt_one] using h
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id) hfinite

/-- Concrete positive-half-line specialization of the signed approximate
identity. No geometric reduction or four-dimensional limit is asserted. -/
theorem planeKernel_rescaling_limit (B : ℝ → ℝ) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ x, ‖B x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), planeKernel 1 u * B (ε * u))
      (𝓝 0) (𝓝 (B 0)) := by
  exact signed_rescaling_limit_unit_mass (volume.restrict (Ioi 0)) (planeKernel 1) B
    integrableOn_planeKernel hB C hbound integral_planeKernel_Ioi

end BoundaryDraft
