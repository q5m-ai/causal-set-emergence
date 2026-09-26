import BoundaryDraft.EllipsoidLimit

/-!
# One-sided signed kernel limits on a collar

A bounded measurable height weight need only be continuous from nonnegative
heights at zero. Cutting it off at a positive collar endpoint is harmless;
no continuity at the cutoff and no positivity of the kernel are required.
These are analytic theorems about the existing kernel, not a coarea formula
or a proof of `GraphCapLimitGoal`.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Positive-density kernel scaling preserves absolute half-line integrability. -/
theorem integrableOn_planeKernel_density (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (planeKernel ρ) (Ioi (0 : ℝ)) := by
  let k := Real.sqrt (Real.sqrt ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hρ)
  have hi : IntegrableOn (fun u => planeKernel 1 (k * u)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ 0 hk).2
    simpa only [mul_zero] using integrableOn_planeKernel
  apply (hi.const_mul k).congr
  exact Eventually.of_forall fun u => (planeKernel_density_scaling ρ u hρ).symm

/-- Absolute integrability of a bounded measurable weighted kernel; the bound
is only needed on the positive half-line. -/
theorem integrableOn_planeKernel_mul_bounded (ρ : ℝ) (hρ : 0 < ρ)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) :
    IntegrableOn (fun s => planeKernel ρ s * B s) (Ioi (0 : ℝ)) := by
  apply ((integrableOn_planeKernel_density ρ hρ).norm.mul_const C).mono'
    ((continuous_planeKernel ρ).measurable.mul hB).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)

/-- The concrete signed mass theorem with only right continuity of the weight. -/
theorem planeKernel_rescaling_limit_right (B : ℝ → ℝ) (hB : Measurable B)
    (hB0 : ContinuousWithinAt B (Ici 0) 0)
    (C : ℝ) (hbound : ∀ s, 0 ≤ s → ‖B s‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), planeKernel 1 u * B (ε * u))
      (𝓝[>] 0) (𝓝 (B 0)) := by
  have hμ : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hu.le
  simpa only [integral_planeKernel_Ioi, one_mul] using
    signed_rescaling_limit_right _ (planeKernel 1) B hμ integrableOn_planeKernel hB hB0 C hbound

/-- Exact change of scale on a fixed half-line for the unchanged kernel. -/
theorem integral_planeKernel_mul_eq_rescaled (B : ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ s in Ioi (0 : ℝ), planeKernel ρ s * B s) =
      ∫ u in Ioi (0 : ℝ), planeKernel 1 u * B ((Real.sqrt (Real.sqrt ρ))⁻¹ * u) := by
  let k := Real.sqrt (Real.sqrt ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hρ)
  have hscale := integral_comp_mul_left_Ioi (fun u => planeKernel 1 u * B (k⁻¹ * u)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hscale
  calc
    _ = k * ∫ s in Ioi (0 : ℝ), planeKernel 1 (k * s) * B s := by
      simp_rw [planeKernel_density_scaling ρ _ hρ, mul_assoc]
      exact integral_const_mul _ _
    _ = _ := by rw [hscale, mul_inv_cancel_left₀ hk.ne']

/-- The physical density parameter approaches zero width from the positive side. -/
theorem tendsto_density_width_right :
    Tendsto (fun ρ : ℝ => (Real.sqrt (Real.sqrt ρ))⁻¹) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨tendsto_density_width, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hρ))

/-- A bounded measurable weight continuous from the right at zero gives the
positive-density half-line limit. No assertion about any geometric height density is a premise
of the admissible graph-cap structure or a conclusion here. -/
theorem planeKernel_halfLine_limit_right (B : ℝ → ℝ) (hB : Measurable B)
    (hB0 : ContinuousWithinAt B (Ici 0) 0)
    (C : ℝ) (hbound : ∀ s, 0 ≤ s → ‖B s‖ ≤ C) :
    Tendsto (fun ρ : ℝ => ∫ s in Ioi (0 : ℝ), planeKernel ρ s * B s)
      atTop (𝓝 (B 0)) := by
  apply ((planeKernel_rescaling_limit_right B hB hB0 C hbound).comp
    tendsto_density_width_right).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (integral_planeKernel_mul_eq_rescaled B ρ hρ).symm

/-- Extending a strict collar weight by zero gives exactly its interval
integral. Only a one-dimensional Lebesgue-null endpoint is replaced. -/
theorem integral_planeKernel_collar_eq_halfLine (B : ℝ → ℝ) (ρ δ : ℝ) (hδ : 0 < δ) :
    (∫ s in (0 : ℝ)..δ, planeKernel ρ s * B s) =
      ∫ s in Ioi (0 : ℝ), planeKernel ρ s * (Iio δ).indicator B s := by
  have he : (fun s => planeKernel ρ s * (Iio δ).indicator B s) =
      (Iio δ).indicator (fun s => planeKernel ρ s * B s) := by
    ext s
    by_cases hs : s ∈ Iio δ <;> simp [hs]
  rw [he, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    intervalIntegral.integral_of_le hδ.le, integral_Ioc_eq_integral_Ioo]
  have hs : Ioo (0 : ℝ) δ = Iio δ ∩ Ioi 0 := by ext s; exact and_comm
  rw [hs]

/-- Absolute integrability on a finite collar follows from the local bound,
including both endpoints. It holds at every density, not only positive ones. -/
theorem intervalIntegrable_planeKernel_mul_bounded (B : ℝ → ℝ) (ρ δ : ℝ) (hδ : 0 ≤ δ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s ∈ Icc (0 : ℝ) δ, ‖B s‖ ≤ C) :
    IntervalIntegrable (fun s => planeKernel ρ s * B s) volume 0 δ := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hδ).2
  apply ((continuous_planeKernel ρ).integrableOn_Icc.norm.mul_const C).mono'
    ((continuous_planeKernel ρ).measurable.mul hB).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)

/-- The analytic collar limit needs a bound only on the collar and continuity
only from the right at zero. In particular it does not require a globally
continuous extension, or differentiability at any positive critical height. -/
theorem planeKernel_collar_limit (B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hB : Measurable B) (hB0 : ContinuousWithinAt B (Ici 0) 0)
    (C : ℝ) (hbound : ∀ s ∈ Icc (0 : ℝ) δ, ‖B s‖ ≤ C) :
    Tendsto (fun ρ : ℝ => ∫ s in (0 : ℝ)..δ, planeKernel ρ s * B s)
      atTop (𝓝 (B 0)) := by
  have hC : 0 ≤ C := (norm_nonneg (B 0)).trans (hbound 0 ⟨le_rfl, hδ.le⟩)
  have hcut0 : ContinuousWithinAt ((Iio δ).indicator B) (Ici 0) 0 := by
    apply hB0.congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with s hs
      exact indicator_of_mem hs B
    · exact indicator_of_mem (show 0 ∈ Iio δ from hδ) B
  have hcutbound : ∀ s, 0 ≤ s → ‖(Iio δ).indicator B s‖ ≤ C := by
    intro s hs
    by_cases hsd : s < δ
    · rw [indicator_of_mem (show s ∈ Iio δ from hsd)]
      exact hbound s ⟨hs, hsd.le⟩
    · rw [indicator_of_not_mem (show s ∉ Iio δ from hsd), norm_zero]
      exact hC
  have hl := planeKernel_halfLine_limit_right _ (hB.indicator measurableSet_Iio) hcut0 C hcutbound
  simpa only [← integral_planeKernel_collar_eq_halfLine B _ δ hδ,
    indicator_of_mem (show 0 ∈ Iio δ from hδ) B] using hl

end BoundaryDraft
