import BoundaryDraft.GraphAtlasRepresentation
import BoundaryDraft.GraphEndpoints
import BoundaryDraft.GraphTail
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Global coarea on a controlled graph-cap collar

Compact-rectangle integrability justifies Fubini in each chart. The finite
partition sum then identifies the height integral with the existing canonical
Hausdorff density. Null regular levels remove the endpoints before returning
to the original spatial product measure. Only the selected noncritical collar
is used; neither density continuity nor a boundary limit is asserted.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- Splitting the Euclidean height coordinates preserves Lebesgue measure,
though it does not preserve the product supremum norm. -/
theorem jointHeightCoordinates_symm_measurePreserving :
    MeasurePreserving jointHeightCoordinates.symm := by
  have hm := (PiLp.volume_preserving_equiv_symm (Fin 3)).comp
    (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _).comp
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_equiv (Fin 2))))
  convert hm using 1
  · ext p i
    simp only [Function.comp_apply, Prod.map_apply, id_eq,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
    rfl

namespace ControlledCollarAtlas

variable {h : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- Continuity is needed only on the selected interval, not beyond the collar.
Compact domination establishes absolute integrability before any chart sum. -/
theorem integrableOn_closedCollar_profile (hh : AdmissibleGraphCap h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    IntegrableOn (fun x : JointSpace => f (h x)) (graphClosedCollar h A.width) := by
  have hc := hf.comp (hh.continuousOn_closedPositive.mono inter_subset_left)
    (fun x hx => ⟨hh.nonneg_on_closedPositive x hx.1, hx.2⟩)
  exact hc.integrableOn_compact (hh.isCompact_closedCollar A.width)

/-- Joint absolute integrability on each fixed rectangle, including
measurability, is proved before Fubini. The weight may have either sign. -/
theorem integrableOn_localTerm_mul (i : Fin A.count) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 A.width)) :
    IntegrableOn (fun p : ℝ × SurfacePlane => A.localTerm i p.1 p.2 * f p.1)
      (Icc 0 A.width ×ˢ (A.charts i).disk) := by
  have hc := (A.continuousOn_localTerm i).mul
    (hf.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  exact (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
    (prod_mono Subset.rfl Metric.ball_subset_closedBall)

/-- Integrable height functions for every summand; this supplies the
hypothesis for interchanging the finite sum and the height integral. -/
theorem integrableOn_localTerm_integral_mul (i : Fin A.count) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 A.width)) :
    IntegrableOn (fun t => f t * ∫ u in (A.charts i).disk, A.localTerm i t u)
      (Icc 0 A.width) := by
  have hi := A.integrableOn_localTerm_mul i f hf
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  have hj := hi.integral_prod_left
  simp only [integral_mul_const] at hj
  simpa only [mul_comm] using hj

/-- The weighted ambient change of variables followed by justified Fubini
uses precisely the local term already identified with canonical slice area. -/
theorem integral_chart_profile (i : Fin A.count) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 A.width)) :
    (∫ p in (A.charts i).parameterRegion A.width,
      (A.charts i).weightedJacobian (A.weights i) p * f (h ((A.charts i).chart.symm p))) =
      ∫ t in Icc 0 A.width, f t * ∫ u in (A.charts i).disk, A.localTerm i t u := by
  let c := A.charts i
  have he : jointHeightCoordinates.symm ⁻¹' c.parameterRegion A.width =
      Icc 0 A.width ×ˢ c.disk := by
    ext p
    change jointHeightCoordinates (jointHeightCoordinates.symm p) ∈
      Icc 0 A.width ×ˢ c.disk ↔ p ∈ Icc 0 A.width ×ˢ c.disk
    rw [jointHeightCoordinates.apply_symm_apply]
  rw [← (jointHeightCoordinates_symm_measurePreserving.restrict_preimage_emb
    jointHeightCoordinates.symm.toHomeomorph.measurableEmbedding
    (c.parameterRegion A.width)).integral_comp
      jointHeightCoordinates.symm.toHomeomorph.measurableEmbedding, he]
  have heq : (∫ p : ℝ × SurfacePlane in Icc 0 A.width ×ˢ c.disk,
      c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm p) *
        f (h (c.chart.symm (jointHeightCoordinates.symm p)))) =
      ∫ p : ℝ × SurfacePlane in Icc 0 A.width ×ˢ c.disk,
        A.localTerm i p.1 p.2 * f p.1 := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_ball)
    intro p hp
    have hpT := c.parameterRegion_subset_target A.width (A.width_lt i).le
      (show jointHeightCoordinates.symm p ∈ c.parameterRegion A.width by
        change p ∈ jointHeightCoordinates.symm ⁻¹' c.parameterRegion A.width
        rw [he]
        exact hp)
    dsimp only
    rw [c.height_symm _ hpT]
    rfl
  rw [heq, Measure.volume_eq_prod, setIntegral_prod _
    (by simpa only [Measure.volume_eq_prod] using A.integrableOn_localTerm_mul i f hf)]
  simp only [integral_mul_const]
  simp only [mul_comm]
  rfl

/-- Absolute integrability of the canonical weighted height density is
obtained from the finite chart representation, not assumed as coarea data. -/
theorem integrableOn_mul_graphHeightDensity (hh : AdmissibleGraphCap h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    IntegrableOn (fun t => f t * graphHeightDensity h t) (Icc 0 A.width) := by
  have hi := integrable_finset_sum (μ := volume.restrict (Icc 0 A.width)) Finset.univ
    (fun i _ => A.integrableOn_localTerm_integral_mul i f hf)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [A.graphHeightDensity_eq_sum hh t ht, Finset.mul_sum]

/-- Closed-collar coarea derived from ambient transport, overlap summation,
and canonical slice transport. All interchanges have integrability proofs. -/
theorem integral_closedCollar_profile (hh : AdmissibleGraphCap h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    (∫ x in graphClosedCollar h A.width, f (h x)) =
      ∫ t in Icc 0 A.width, f t * graphHeightDensity h t := by
  rw [A.integral_closedCollar_eq_sum hh _ (A.integrableOn_closedCollar_profile hh f hf)]
  simp_rw [A.integral_chart_profile _ f hf]
  rw [← integral_finset_sum _ (fun i _ => A.integrableOn_localTerm_integral_mul i f hf)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [A.graphHeightDensity_eq_sum hh t ht, Finset.mul_sum]

/-- Absolute integrability in the original spatial measure, including both
null-endpoint replacements. -/
theorem integrableOn_openCollar_profile (hh : AdmissibleGraphCap h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    IntegrableOn (fun x : Spatial => f (h x)) {x | 0 < h x ∧ h x < A.width} :=
  (hh.integrableOn_spatial_openCollar_iff A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩) _).mpr
      (A.integrableOn_closedCollar_profile hh f hf)

/-- The height integrand is absolutely interval-integrable, so the displayed
coarea integral is not using Lean's nonintegrable fallback value. -/
theorem intervalIntegrable_mul_graphHeightDensity (hh : AdmissibleGraphCap h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    IntervalIntegrable (fun t => f t * graphHeightDensity h t) volume 0 A.width :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le A.width_pos.le).mpr
    (A.integrableOn_mul_graphHeightDensity hh f hf)

/-- The strict spatial collar in the original product Lebesgue measure,
with the existing canonical density and the usual oriented interval integral. -/
theorem integral_openCollar_profile (hh : AdmissibleGraphCap h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    (∫ x : Spatial in {x | 0 < h x ∧ h x < A.width}, f (h x)) =
      ∫ t in (0 : ℝ)..A.width, f t * graphHeightDensity h t := by
  rw [hh.integral_spatial_openCollar_eq_closedCollar A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩),
    A.integral_closedCollar_profile hh f hf, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le A.width_pos.le]

/-- The signed kernel specialization holds at every density (in particular,
every positive density used by the finite-density action reduction). -/
theorem integral_openCollar_planeKernel (hh : AdmissibleGraphCap h) (ρ : ℝ) :
    (∫ x : Spatial in {x | 0 < h x ∧ h x < A.width}, planeKernel ρ (h x)) =
      ∫ t in (0 : ℝ)..A.width, planeKernel ρ t * graphHeightDensity h t :=
  A.integral_openCollar_profile hh _ (continuous_planeKernel ρ).continuousOn

/-- Exact finite-density action split with coarea used only below the
controlled width. The remainder can contain positive-height critical points. -/
theorem continuumMean_eq_height_collar_add_remainder (hh : AdmissibleGraphCap h)
    (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (graphCapRegion h) =
      (∫ t in (0 : ℝ)..A.width, planeKernel ρ t * graphHeightDensity h t) +
        ∫ x in {x | A.width ≤ h x}, planeKernel ρ (h x) := by
  rw [hh.toGraphCapData.continuumMean_eq_collar_add_remainder ρ A.width hρ A.width_pos,
    A.integral_openCollar_planeKernel hh ρ]

end ControlledCollarAtlas

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- A positive regular collar is constructed from the unchanged admissibility
hypotheses. The same width works for every continuous-on-the-collar signed
weight, with spatial and height absolute integrability both explicit. -/
theorem exists_collar_coarea : ∃ δ : ℝ, 0 < δ ∧
    (∀ x ∈ graphClosedCollar h δ, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) ∧
    ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 δ) →
      IntegrableOn (fun x : Spatial => f (h x)) {x | 0 < h x ∧ h x < δ} ∧
      IntervalIntegrable (fun t => f t * graphHeightDensity h t) volume 0 δ ∧
      (∫ x : Spatial in {x | 0 < h x ∧ h x < δ}, f (h x)) =
        ∫ t in (0 : ℝ)..δ, f t * graphHeightDensity h t := by
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  exact ⟨A.width, A.width_pos, A.noncritical, fun f hf =>
    ⟨A.integrableOn_openCollar_profile hh f hf,
      A.intervalIntegrable_mul_graphHeightDensity hh f hf,
      A.integral_openCollar_profile hh f hf⟩⟩

/-- One collar works simultaneously at every positive action density; no
positivity assumption is imposed on the signed kernel itself. -/
theorem exists_planeKernel_collar_coarea : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ →
    IntegrableOn (fun x : Spatial => planeKernel ρ (h x)) {x | 0 < h x ∧ h x < δ} ∧
    IntervalIntegrable (fun t => planeKernel ρ t * graphHeightDensity h t) volume 0 δ ∧
    (∫ x : Spatial in {x | 0 < h x ∧ h x < δ}, planeKernel ρ (h x)) =
      ∫ t in (0 : ℝ)..δ, planeKernel ρ t * graphHeightDensity h t := by
  obtain ⟨δ, hδ, _, hc⟩ := hh.exists_collar_coarea
  exact ⟨δ, hδ, fun ρ _ => hc _ (continuous_planeKernel ρ).continuousOn⟩

end AdmissibleGraphCap
end BoundaryDraft
