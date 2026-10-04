import BoundaryDraft.Pilot3Endpoints
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Scalar cutoff calculus for spatial divergence

The elementary unit-mass height ramp is derived by FTC. This is an
approximation-to-boundary-flux lemma, not an action kernel or an action limit.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
noncomputable section
namespace BoundaryDraft

def pilot3HeightRamp (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

theorem contDiff_pilot3HeightRamp : ContDiff ℝ ∞ pilot3HeightRamp :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem pilot3HeightRamp_zero {t : ℝ} (ht : t ≤ 1 / 2) : pilot3HeightRamp t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem pilot3HeightRamp_one {t : ℝ} (ht : 1 ≤ t) : pilot3HeightRamp t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem norm_pilot3HeightRamp_le (t : ℝ) : ‖pilot3HeightRamp t‖ ≤ 1 := by
  unfold pilot3HeightRamp
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem deriv_pilot3HeightRamp_zero {t : ℝ} (ht : t < 1 / 2) : deriv pilot3HeightRamp t = 0 := by
  have he : pilot3HeightRamp =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [gt_mem_nhds ht] with u hu
    exact pilot3HeightRamp_zero hu.le
  rw [he.deriv_eq, deriv_const]

theorem deriv_pilot3HeightRamp_zero_of_gt {t : ℝ} (ht : 1 < t) : deriv pilot3HeightRamp t = 0 := by
  have he : pilot3HeightRamp =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [lt_mem_nhds ht] with u hu
    exact pilot3HeightRamp_one hu.le
  rw [he.deriv_eq, deriv_const]

theorem continuous_deriv_pilot3HeightRamp : Continuous (deriv pilot3HeightRamp) :=
  contDiff_pilot3HeightRamp.continuous_deriv (by simp)

theorem integral_deriv_pilot3HeightRamp : (∫ t in Icc (0 : ℝ) 1, deriv pilot3HeightRamp t) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (contDiff_pilot3HeightRamp.differentiable (by simp) t).hasDerivAt)
    (continuous_deriv_pilot3HeightRamp.intervalIntegrable 0 1)]
  rw [pilot3HeightRamp_one le_rfl, pilot3HeightRamp_zero (by norm_num)]
  norm_num

theorem pilot3_integral_ramp_density_rescale {δ ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (B : ℝ → ℝ) :
    (∫ t in Icc 0 δ, (deriv pilot3HeightRamp (t / ε) / ε) * B t) =
      ∫ u in Icc (0 : ℝ) 1, deriv pilot3HeightRamp u * B (ε * u) := by
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Icc
    (Icc_subset_Icc_right hεδ.le) (fun t ht => ?_)]
  swap
  · have htε : ε < t := lt_of_not_ge (fun ht' => ht.2 ⟨ht.1.1, ht'⟩)
    rw [deriv_pilot3HeightRamp_zero_of_gt ((one_lt_div hε).mpr htε), zero_div, zero_mul]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hε.le,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he := intervalIntegral.smul_integral_comp_mul_left
    (fun t => (deriv pilot3HeightRamp (t / ε) / ε) * B t) ε (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at he
  rw [← he, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [mul_div_cancel_left₀ _ hε.ne', smul_eq_mul]
  field_simp

theorem pilot3_tendsto_ramp_density {δ : ℝ} (hδ : 0 < δ) (B : ℝ → ℝ) (hB : ContinuousOn B (Icc 0 δ)) :
    Tendsto (fun ε : ℝ => ∫ t in Icc 0 δ, (deriv pilot3HeightRamp (t / ε) / ε) * B t)
      (𝓝[>] 0) (𝓝 (B 0)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hδ)] with ε hε hεδ
    exact ⟨hε, hεδ⟩
  have harg (ε : ℝ) (hε : 0 < ε ∧ ε < δ) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ε * u ∈ Icc 0 δ :=
    ⟨mul_nonneg hε.1.le hu.1, (mul_le_mul_of_nonneg_left hu.2 hε.1.le).trans (by simpa using hε.2.le)⟩
  have hB0 : ContinuousWithinAt B (Ici 0) 0 :=
    (continuousWithinAt_Icc_iff_Ici hδ).mp (hB 0 ⟨le_rfl, hδ.le⟩)
  have hlim : Tendsto (fun ε : ℝ => ∫ u in Icc (0 : ℝ) 1, deriv pilot3HeightRamp u * B (ε * u))
      (𝓝[>] 0) (𝓝 (∫ u in Icc (0 : ℝ) 1, deriv pilot3HeightRamp u * B 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => ‖deriv pilot3HeightRamp u‖ * C)
    · filter_upwards [hsmall] with ε hε
      exact (continuous_deriv_pilot3HeightRamp.continuousOn.mul
        (hB.comp (continuous_const.mul continuous_id).continuousOn (harg ε hε))).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [hsmall] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ (harg ε hε u hu)) (norm_nonneg _)
    · exact (continuous_deriv_pilot3HeightRamp.norm.mul continuous_const).integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have ha : Tendsto (fun ε : ℝ => ε * u) (𝓝[>] 0) (𝓝[≥] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · simpa only [id_eq, zero_mul] using
            (((continuous_id : Continuous (fun ε : ℝ => ε)).mul
              (continuous_const : Continuous (fun _ : ℝ => u))).tendsto (0 : ℝ)).mono_left
              (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact mul_nonneg hε.le hu.1
      exact tendsto_const_nhds.mul (hB0.tendsto.comp ha)
  have hlim' : Tendsto (fun ε : ℝ => ∫ u in Icc (0 : ℝ) 1, deriv pilot3HeightRamp u * B (ε * u))
      (𝓝[>] 0) (𝓝 (B 0)) := by
    simpa only [integral_mul_const, integral_deriv_pilot3HeightRamp, one_mul] using hlim
  apply hlim'.congr'
  filter_upwards [hsmall] with ε hε
  exact (pilot3_integral_ramp_density_rescale hε.1 hε.2 B).symm

end BoundaryDraft
