import BoundaryDraft.Pilot3AtlasRepresentation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Normalized spatially weighted coarea in the pilot plane

Lebesgue measure is split without changing its normalization. Signed Fubini
is preceded by absolute-integrability proofs. The density is the fixed
Hausdorff-one level integral, and its boundary limit is right-sided only.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

theorem pilot3Coordinates_symm_measurePreserving : MeasurePreserving pilot3Coordinates.symm := by
  have hm := (PiLp.volume_preserving_equiv_symm (Fin 2)).comp ((volume_preserving_finTwoArrow ℝ).symm _)
  convert hm using 1

def pilot3WeightedHeightDensity (h w : Pilot3Space → ℝ) (t : ℝ) : ℝ :=
  ∫ x, w x / ‖pilot3Gradient h x‖ ∂pilot3LevelMeasure h t

@[simp] theorem pilot3WeightedHeightDensity_zero (h w : Pilot3Space → ℝ) :
    pilot3WeightedHeightDensity h w 0 = ∫ x, w x / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h := rfl

@[simp] theorem pilot3WeightedHeightDensity_one (h : Pilot3Space → ℝ) :
    pilot3WeightedHeightDensity h (fun _ => 1) = pilot3HeightDensity h := rfl

namespace Pilot3CollarAtlas
variable {h : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

def weightedLocalTerm (w : Pilot3Space → ℝ) (i : Fin A.count) (t u : ℝ) : ℝ :=
  A.localTerm i t u * w ((A.charts i).chart.symm (pilot3Curve (fun _ => t) u))

theorem continuousOn_weightedLocalTerm (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (i : Fin A.count) : ContinuousOn (fun p : ℝ × ℝ => A.weightedLocalTerm w i p.1 p.2)
      (Icc 0 A.width ×ˢ (A.charts i).closedDisk) := by
  let c := A.charts i
  have hT : ∀ p ∈ Icc 0 A.width ×ˢ c.closedDisk, pilot3Coordinates.symm p ∈ c.chart.target := by
    intro p hp
    exact c.ball_subset (c.rectangle_subset p.1
      ⟨(neg_nonpos.mpr c.width_pos.le).trans hp.1.1, hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)
  apply (A.continuousOn_localTerm i).mul
  apply hw.comp (c.chart.continuousOn_symm.comp pilot3Coordinates.symm.continuous.continuousOn hT)
  intro p hp
  exact c.symm_mem_closedPositive _ (hT p hp) hp.1.1

theorem integrableOn_weightedLocalTerm (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (i : Fin A.count) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    IntegrableOn (A.weightedLocalTerm w i t) (A.charts i).disk := by
  have hc : ContinuousOn (A.weightedLocalTerm w i t) (A.charts i).closedDisk :=
    (A.continuousOn_weightedLocalTerm w hw i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨ht, hu⟩)
  exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall

theorem integrable_level_weight_div (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    Integrable (fun x => w x / ‖pilot3Gradient h x‖) (pilot3LevelMeasure h t) := by
  have hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0 :=
    fun x hx => A.noncritical x ⟨hx.1, hx.2.le.trans ht.2⟩
  letI := hh.finite_levelMeasure t hreg
  have hc : ContinuousOn (fun x => w x / ‖pilot3Gradient h x‖) (pilot3Level h t) := by
    apply (hw.mono inter_subset_left).div (hh.continuousOn_gradient.norm.mono inter_subset_left)
    intro x hx
    rw [pilot3Gradient_norm]
    exact norm_ne_zero_iff.mpr (hreg x hx)
  have hi := hc.integrableOn_compact (μ := pilot3LevelMeasure h t) (hh.isCompact_level t)
  simpa only [IntegrableOn, pilot3LevelMeasure,
    Measure.restrict_restrict_of_subset (Subset.refl (pilot3Level h t))] using hi

theorem weightedHeightDensity_eq_sum (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    pilot3WeightedHeightDensity h w t = ∑ i, ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u := by
  rw [pilot3WeightedHeightDensity, A.integral_level_eq_sum hh t ht _ (A.integrable_level_weight_div hh w hw t ht)]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun measurableSet_ball
  intro u hu
  let c := A.charts i
  have huD := c.disk_subset_sliceDomain t
    ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩ hu
  dsimp only
  rw [c.slice_eq_symm t u huD]
  dsimp only [weightedLocalTerm, localTerm, Pilot3HeightChart.weightedJacobian]
  rw [c.abs_det_fderiv_symm _ (c.ball_subset huD)]
  ring

/-- Compact domination includes the two height endpoints and signed weights. -/
theorem continuousOn_integral_weightedLocalTerm (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (i : Fin A.count) :
    ContinuousOn (fun t => ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u) (Icc 0 A.width) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
    (A.continuousOn_weightedLocalTerm w hw i)
  haveI : IsFiniteMeasure (volume.restrict (A.charts i).disk) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact Metric.isBounded_ball.measure_lt_top
  intro t ht
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (A.integrableOn_weightedLocalTerm w hw i s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    exact hM (s, u) ⟨hs, Metric.ball_subset_closedBall hu⟩
  · exact integrable_const M
  · filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    exact ((A.continuousOn_weightedLocalTerm w hw i).comp
      (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hs => ⟨hs, Metric.ball_subset_closedBall hu⟩)) t ht

theorem continuousOn_weightedHeightDensity (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) :
    ContinuousOn (pilot3WeightedHeightDensity h w) (Icc 0 A.width) := by
  apply (continuousOn_finset_sum _ (fun i _ => A.continuousOn_integral_weightedLocalTerm w hw i)).congr
  exact fun t ht => A.weightedHeightDensity_eq_sum hh w hw t ht

theorem integrableOn_closedCollar_weighted (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun x => g (h x) * w x) (pilot3ClosedCollar h A.width) := by
  have hc := hg.comp (hh.continuousOn_closedPositive.mono inter_subset_left)
    (fun x hx => ⟨hh.nonneg_on_closedPositive x hx.1, hx.2⟩)
  exact (hc.mul (hw.mono inter_subset_left)).integrableOn_compact (hh.isCompact_closedCollar A.width)

theorem integrableOn_weightedLocalTerm_mul (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (i : Fin A.count) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun p : ℝ × ℝ => A.weightedLocalTerm w i p.1 p.2 * g p.1)
      (Icc 0 A.width ×ˢ (A.charts i).disk) := by
  have hc := (A.continuousOn_weightedLocalTerm w hw i).mul
    (hg.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  exact (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
    (prod_mono Subset.rfl Metric.ball_subset_closedBall)

theorem integral_chart_weighted (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (i : Fin A.count) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    (∫ p in (A.charts i).parameterRegion A.width, (A.charts i).weightedJacobian (A.weights i) p *
      (g (h ((A.charts i).chart.symm p)) * w ((A.charts i).chart.symm p))) =
      ∫ t in Icc 0 A.width, g t * ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u := by
  let c := A.charts i
  have he : pilot3Coordinates.symm ⁻¹' c.parameterRegion A.width = Icc 0 A.width ×ˢ c.disk := by
    ext p
    change pilot3Coordinates (pilot3Coordinates.symm p) ∈ Icc 0 A.width ×ˢ c.disk ↔ p ∈ Icc 0 A.width ×ˢ c.disk
    rw [pilot3Coordinates.apply_symm_apply]
  rw [← (pilot3Coordinates_symm_measurePreserving.restrict_preimage_emb
    pilot3Coordinates.symm.toHomeomorph.measurableEmbedding (c.parameterRegion A.width)).integral_comp
      pilot3Coordinates.symm.toHomeomorph.measurableEmbedding, he]
  have heq : (∫ p : ℝ × ℝ in Icc 0 A.width ×ˢ c.disk,
      c.weightedJacobian (A.weights i) (pilot3Coordinates.symm p) *
        (g (h (c.chart.symm (pilot3Coordinates.symm p))) * w (c.chart.symm (pilot3Coordinates.symm p)))) =
      ∫ p : ℝ × ℝ in Icc 0 A.width ×ˢ c.disk, A.weightedLocalTerm w i p.1 p.2 * g p.1 := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_ball)
    intro p hp
    have hpT := c.parameterRegion_subset_target A.width (A.width_lt i).le
      (show pilot3Coordinates.symm p ∈ c.parameterRegion A.width by
        change p ∈ pilot3Coordinates.symm ⁻¹' c.parameterRegion A.width
        rw [he]
        exact hp)
    dsimp only
    rw [c.height_symm _ hpT]
    dsimp only [weightedLocalTerm, localTerm]
    change (A.charts i).weightedJacobian (A.weights i) (pilot3Curve (fun _ => p.1) p.2) *
      (g p.1 * w ((A.charts i).chart.symm (pilot3Curve (fun _ => p.1) p.2))) = _
    ring
  rw [heq, Measure.volume_eq_prod, setIntegral_prod _
    (by simpa only [Measure.volume_eq_prod] using A.integrableOn_weightedLocalTerm_mul w hw i g hg)]
  simp only [integral_mul_const]
  simp only [mul_comm]
  rfl

/-- Normalization one: there is NO sphere-area, angular-average, action or
four-dimensional coefficient in this spatial coarea identity. -/
theorem integral_closedCollar_weighted (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    (∫ x in pilot3ClosedCollar h A.width, g (h x) * w x) =
      ∫ t in Icc 0 A.width, g t * pilot3WeightedHeightDensity h w t := by
  rw [A.integral_closedCollar_eq_sum hh _ (A.integrableOn_closedCollar_weighted hh w hw g hg)]
  simp_rw [A.integral_chart_weighted w hw _ g hg]
  rw [← integral_finset_sum _ (fun i _ =>
    (hg.mul (A.continuousOn_integral_weightedLocalTerm w hw i)).integrableOn_compact isCompact_Icc)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [A.weightedHeightDensity_eq_sum hh w hw t ht, Finset.mul_sum]

theorem integrableOn_weightedHeightDensity_mul (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun t => g t * pilot3WeightedHeightDensity h w t) (Icc 0 A.width) :=
  (hg.mul (A.continuousOn_weightedHeightDensity hh w hw)).integrableOn_compact isCompact_Icc

theorem continuousOn_heightDensity (hh : Pilot3RegularHeight h) :
    ContinuousOn (pilot3HeightDensity h) (Icc 0 A.width) :=
  A.continuousOn_weightedHeightDensity hh (fun _ => 1) continuousOn_const

theorem measurable_indicator_heightDensity (hh : Pilot3RegularHeight h) :
    Measurable ((Icc 0 A.width).indicator (pilot3HeightDensity h)) := by
  classical
  rw [← piecewise_eq_indicator]
  exact (A.continuousOn_heightDensity hh).measurable_piecewise continuousOn_const measurableSet_Icc

theorem exists_bound_heightDensity (hh : Pilot3RegularHeight h) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 A.width, ‖pilot3HeightDensity h t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (A.continuousOn_heightDensity hh)
  exact ⟨max C 0 + 1, by positivity, fun t ht =>
    (hC t ht).trans ((le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one))⟩

end Pilot3CollarAtlas
namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
include hh

theorem tendsto_weightedHeightDensity_zero (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h)) :
    Tendsto (pilot3WeightedHeightDensity h w) (𝓝[≥] 0)
      (𝓝 (∫ x, w x / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)) := by
  obtain ⟨A⟩ := hh.exists_collarAtlas
  have hc := (continuousWithinAt_Icc_iff_Ici A.width_pos).mp
    (A.continuousOn_weightedHeightDensity hh w hw 0 ⟨le_rfl, A.width_pos.le⟩)
  exact hc.tendsto

theorem tendsto_heightDensity_zero : Tendsto (pilot3HeightDensity h) (𝓝[≥] 0)
    (𝓝 (∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)) :=
  hh.tendsto_weightedHeightDensity_zero (fun _ => 1) continuousOn_const

/-- A single geometry-dependent collar works for all continuous signed
spatial and height observables, with both integrability claims explicit. -/
theorem exists_collar_coarea : ∃ δ : ℝ, 0 < δ ∧
    (∀ x ∈ pilot3ClosedCollar h δ, fderiv ℝ h x ≠ 0) ∧
    ∀ w : Pilot3Space → ℝ, ContinuousOn w (pilot3ClosedPositive h) →
    ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 δ) →
      IntegrableOn (fun x => g (h x) * w x) (pilot3ClosedCollar h δ) ∧
      IntegrableOn (fun t => g t * pilot3WeightedHeightDensity h w t) (Icc 0 δ) ∧
      (∫ x in pilot3ClosedCollar h δ, g (h x) * w x) =
        ∫ t in Icc 0 δ, g t * pilot3WeightedHeightDensity h w t := by
  obtain ⟨A⟩ := hh.exists_collarAtlas
  exact ⟨A.width, A.width_pos, A.noncritical, fun w hw g hg =>
    ⟨A.integrableOn_closedCollar_weighted hh w hw g hg,
      A.integrableOn_weightedHeightDensity_mul hh w hw g hg,
      A.integral_closedCollar_weighted hh w hw g hg⟩⟩

end Pilot3RegularHeight
end BoundaryDraft
