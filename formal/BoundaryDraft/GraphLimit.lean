import BoundaryDraft.GraphCoarea
import BoundaryDraft.GraphDensityRegularity
import BoundaryDraft.KernelCollar

/-!
# The deterministic boundary limit for every admissible graph cap

Use one constructed noncritical collar for both coarea and density regularity.
The measurable cutoff of the canonical density has only right continuity at
zero; the entire signed kernel concentrates there. Outside that collar the
spatial tail theorem bypasses all positive-height critical points. The exact
action split starts from the unchanged four-dimensional `continuumMean`.
No probability or Poisson-expectation statement is made here.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ControlledCollarAtlas

variable {h : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- The canonical density needs regularity only on this collar. Its measurable
zero extension is an analytic device, not a replacement geometric density or
an assumption about positive critical levels outside the collar. -/
theorem tendsto_integral_planeKernel_mul_graphHeightDensity (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ : ℝ => ∫ t in (0 : ℝ)..A.width, planeKernel ρ t * graphHeightDensity h t)
      atTop (𝓝 (graphBoundaryIntegral h)) := by
  let B := (Icc 0 A.width).indicator (graphHeightDensity h)
  have hB0 : ContinuousWithinAt B (Ici 0) 0 := by
    apply (A.continuousWithinAt_graphHeightDensity_zero hh).congr_of_eventuallyEq
    · filter_upwards [Icc_mem_nhdsGE A.width_pos] with t ht
      exact indicator_of_mem ht _
    · exact indicator_of_mem (show (0 : ℝ) ∈ Icc 0 A.width from ⟨le_rfl, A.width_pos.le⟩) _
  obtain ⟨C, _, hC⟩ := A.exists_bound_graphHeightDensity hh
  have hbound : ∀ t ∈ Icc 0 A.width, ‖B t‖ ≤ C := by
    intro t ht
    simpa only [B, indicator_of_mem ht] using hC t ht
  have hl := planeKernel_collar_limit B A.width A.width_pos
    (A.measurable_indicator_graphHeightDensity hh) hB0 C hbound
  have hzero : B 0 = graphBoundaryIntegral h := by
    simp only [B, indicator_of_mem (show (0 : ℝ) ∈ Icc 0 A.width from ⟨le_rfl, A.width_pos.le⟩),
      graphHeightDensity_zero]
  rw [hzero] at hl
  apply hl.congr'
  exact Eventually.of_forall fun ρ => intervalIntegral.integral_congr fun t ht => by
    rw [uIcc_of_le A.width_pos.le] at ht
    rw [show B t = graphHeightDensity h t from indicator_of_mem ht _]

end ControlledCollarAtlas
namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- The unchanged general deterministic target, with no extra reduction,
coarea, density, normalization, or limit premise. Coarea is used only on the
constructed noncritical collar; the remainder needs only `GraphCapData`. -/
theorem graphCapLimit : GraphCapLimitGoal h := by
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  have hl := (A.tendsto_integral_planeKernel_mul_graphHeightDensity hh).add
    (hh.toGraphCapData.tendsto_integral_kernel_superlevel A.width A.width_pos)
  rw [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (A.continuumMean_eq_height_collar_add_remainder hh ρ hρ).symm

/-- The checked boundary value is also the canonical variable-angle integral. -/
theorem tendsto_continuumMean_graphCap_eq_angle :
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion h)) atTop
      (𝓝 (∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h)) := by
  rw [← hh.graphBoundaryIntegral_eq_angle]
  exact hh.graphCapLimit

end AdmissibleGraphCap
end BoundaryDraft
