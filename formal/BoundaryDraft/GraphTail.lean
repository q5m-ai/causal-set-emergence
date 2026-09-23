import BoundaryDraft.SpacetimeIntegration
import BoundaryDraft.KernelEstimates
import BoundaryDraft.EllipsoidLimit

/-!
# Non-collar graph-cap remainder

The signed kernel's checked absolute tail and bounded spatial support control
the entire region `h ≥ δ`, with no use of coarea or any differential condition
at positive height. The finite-density action is split exactly before taking
the limit; critical levels and the endpoint `h = δ` remain in the remainder.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- Density-scaled absolute tail, valid at every positive height. -/
theorem abs_planeKernel_density_le (ρ H : ℝ) (hρ : 0 < ρ) (hH : 0 < H) :
    |planeKernel ρ H| ≤ (1416 / (Real.pi * Real.sqrt 6)) *
      ((Real.sqrt (Real.sqrt ρ))⁻¹) ^ 2 / H ^ 3 := by
  let k := Real.sqrt (Real.sqrt ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hρ)
  rw [planeKernel_density_scaling ρ H hρ, abs_mul, abs_of_pos hk]
  apply (mul_le_mul_of_nonneg_left (abs_planeKernel_le (mul_pos hk hH)) hk.le).trans_eq
  change k * ((1416 / (Real.pi * Real.sqrt 6)) / (k * H) ^ 3) =
    (1416 / (Real.pi * Real.sqrt 6)) * (k⁻¹) ^ 2 / H ^ 3
  field_simp
  ring

namespace GraphCapData

variable {h : Spatial → ℝ} (hh : GraphCapData h)
include hh

/-- Positive superlevels are closed even though the raw profile need not be
continuous away from its positive set. -/
theorem isClosed_superlevel (δ : ℝ) (hδ : 0 < δ) : IsClosed {x | δ ≤ h x} := by
  have he : {x | δ ≤ h x} = {x | δ ≤ max 0 (h x)} := by
    ext x
    simp only [mem_setOf_eq, le_max_iff]
    exact (or_iff_right (not_le_of_gt hδ)).symm
  rw [he]
  exact isClosed_le continuous_const hh.continuous_positivePart

theorem integrableOn_kernel_superlevel (ρ δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun x => planeKernel ρ (h x)) {x | δ ≤ h x} :=
  (integrableOn_graphCap_profile h hh _ (continuous_planeKernel ρ)).mono_set
    (fun _ hx => hδ.trans_le hx)

/-- A uniform absolute estimate on the actual spatial remainder. No level
set, coarea, or critical-point assumption occurs. -/
theorem norm_integral_kernel_superlevel_le (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ‖∫ x in {x | δ ≤ h x}, planeKernel ρ (h x)‖ ≤
      ((1416 / (Real.pi * Real.sqrt 6)) *
        ((Real.sqrt (Real.sqrt ρ))⁻¹) ^ 2 / δ ^ 3) *
      volume.real {x : Spatial | 0 < h x} := by
  have hsub : {x | δ ≤ h x} ⊆ {x | 0 < h x} := fun _ hx => hδ.trans_le hx
  have hfinite := hh.bounded_positive.measure_lt_top (μ := volume)
  calc
    _ ≤ ((1416 / (Real.pi * Real.sqrt 6)) *
        ((Real.sqrt (Real.sqrt ρ))⁻¹) ^ 2 / δ ^ 3) *
        volume.real {x | δ ≤ h x} := by
      apply norm_setIntegral_le_of_norm_le_const ((measure_mono hsub).trans_lt hfinite)
      intro x hx
      rw [Real.norm_eq_abs]
      apply (abs_planeKernel_density_le ρ (h x) hρ (hsub hx)).trans
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hδ 3)
        (pow_le_pow_left₀ hδ.le hx 3)
    _ ≤ _ := mul_le_mul_of_nonneg_left (measureReal_mono hsub hfinite.ne) (by positivity)

/-- Every fixed positive-height remainder vanishes, even across interior
critical levels. This proves the tail half of the general limit argument. -/
theorem tendsto_integral_kernel_superlevel (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ρ => ∫ x in {x | δ ≤ h x}, planeKernel ρ (h x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
        exact hh.norm_integral_kernel_superlevel_le ρ δ hρ hδ)
  simpa using (((tendsto_density_width.pow 2).const_mul
    (1416 / (Real.pi * Real.sqrt 6))).div_const (δ ^ 3)).mul_const
      (volume.real {x : Spatial | 0 < h x})

/-- Exact collar/remainder decomposition of the unchanged four-dimensional
action. The height endpoint belongs to the remainder, so no unproved
level-set-nullity assertion is used. -/
theorem continuumMean_eq_collar_add_remainder (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    continuumMean ρ (graphCapRegion h) =
      (∫ x in {x | 0 < h x ∧ h x < δ}, planeKernel ρ (h x)) +
      ∫ x in {x | δ ≤ h x}, planeKernel ρ (h x) := by
  rw [graphCap_graphReduction h hh ρ hρ]
  have he : {x | 0 < h x} = {x | 0 < h x ∧ h x < δ} ∪ {x | δ ≤ h x} := by
    ext x
    constructor
    · intro hx
      by_cases hs : h x < δ
      · exact Or.inl ⟨hx, hs⟩
      · exact Or.inr (le_of_not_gt hs)
    · rintro (hx | hx)
      · exact hx.1
      · exact hδ.trans_le hx
  rw [he]
  apply setIntegral_union
  · exact disjoint_left.mpr fun _ hx hy => not_lt_of_ge hy hx.2
  · exact (hh.isClosed_superlevel δ hδ).measurableSet
  · exact (integrableOn_graphCap_profile h hh _ (continuous_planeKernel ρ)).mono_set
      (fun _ hx => hx.1)
  · exact hh.integrableOn_kernel_superlevel ρ δ hδ

end GraphCapData
end BoundaryDraft
