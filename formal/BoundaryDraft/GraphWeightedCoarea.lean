import BoundaryDraft.GraphCoarea
import BoundaryDraft.GraphDensityRegularity

/-!
# Spatially weighted collar coarea

Continuous spatial observables are transported through the existing finite
atlas. The level measures are the canonical normalized Hausdorff measures.
Only the constructed noncritical collar is used; interior critical points
are not excluded.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

set_option maxHeartbeats 800000

/-- The canonical coarea density with a spatial observable. -/
def graphWeightedHeightDensity (h : Spatial → ℝ) (w : JointSpace → ℝ) (t : ℝ) : ℝ :=
  ∫ x, w x / ‖graphGradient h x‖ ∂graphLevelMeasure h t

@[simp] theorem graphWeightedHeightDensity_zero (h : Spatial → ℝ) (w : JointSpace → ℝ) :
    graphWeightedHeightDensity h w 0 =
      ∫ x, w x / ‖graphGradient h x‖ ∂graphSurfaceMeasure h := by
  simp only [graphWeightedHeightDensity, graphLevelMeasure_zero]

namespace ControlledCollarAtlas

variable {h : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- The same chart Jacobian, multiplied by the pulled-back observable. -/
def weightedLocalTerm (w : JointSpace → ℝ) (i : Fin A.count)
    (t : ℝ) (u : SurfacePlane) : ℝ :=
  A.localTerm i t u * w ((A.charts i).chart.symm (surfaceGraph (fun _ => t) u))

theorem continuousOn_weightedLocalTerm (w : JointSpace → ℝ)
    (hw : ContinuousOn w (graphClosedPositive h)) (i : Fin A.count) :
    ContinuousOn (fun p : ℝ × SurfacePlane => A.weightedLocalTerm w i p.1 p.2)
      (Icc 0 A.width ×ˢ (A.charts i).closedDisk) := by
  let c := A.charts i
  have hT : ∀ p ∈ Icc 0 A.width ×ˢ c.closedDisk,
      jointHeightCoordinates.symm p ∈ c.chart.target := by
    intro p hp
    exact c.ball_subset (c.rectangle_subset p.1
      ⟨(neg_nonpos.mpr c.width_pos.le).trans hp.1.1,
        hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)
  apply (A.continuousOn_localTerm i).mul
  apply hw.comp (c.chart.continuousOn_symm.comp
    jointHeightCoordinates.symm.continuous.continuousOn hT)
  intro p hp
  exact c.symm_mem_closedPositive _ (hT p hp) hp.1.1

theorem integrableOn_weightedLocalTerm (w : JointSpace → ℝ)
    (hw : ContinuousOn w (graphClosedPositive h)) (i : Fin A.count)
    (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    IntegrableOn (A.weightedLocalTerm w i t) (A.charts i).disk := by
  have hc : ContinuousOn (A.weightedLocalTerm w i t) (A.charts i).closedDisk :=
    (A.continuousOn_weightedLocalTerm w hw i).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨ht, hu⟩)
  exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set
    Metric.ball_subset_closedBall

/-- Absolute integrability on each canonical level, including height zero. -/
theorem integrable_graphLevel_weight_div (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h))
    (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    Integrable (fun x => w x / ‖graphGradient h x‖) (graphLevelMeasure h t) := by
  have hreg : ∀ x ∈ graphLevel h t, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0 :=
    fun x hx => A.noncritical x ⟨hx.1, hx.2.le.trans ht.2⟩
  letI := hh.finite_graphLevelMeasure t hreg
  have hc : ContinuousOn (fun x => w x / ‖graphGradient h x‖) (graphLevel h t) := by
    apply (hw.mono inter_subset_left).div
      (hh.continuousOn_graphSlope.mono inter_subset_left)
    intro x hx
    change graphSlope h x ≠ 0
    rw [graphSlope_eq_norm_fderiv]
    exact norm_ne_zero_iff.mpr (hreg x hx)
  have hi := hc.integrableOn_compact (μ := graphLevelMeasure h t) (hh.isCompact_level t)
  simpa only [IntegrableOn, graphLevelMeasure,
    Measure.restrict_restrict_of_subset (Subset.refl (graphLevel h t))] using hi

theorem weighted_level_integral_spatial (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (i : Fin A.count) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    (∫ x, A.weights i x * (w x / ‖graphGradient h x‖) ∂graphLevelMeasure h t) =
      ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u := by
  let c := A.charts i
  have htC : t ∈ Icc (-c.width) c.width :=
    ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩
  have he : (∫ x in c.slice t '' c.disk,
      A.weights i x * (w x / ‖graphGradient h x‖) ∂graphLevelMeasure h t) =
      ∫ x, A.weights i x * (w x / ‖graphGradient h x‖) ∂graphLevelMeasure h t := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_restrict_mem (μ := normalizedHausdorffTwo)
      (hh.measurableSet_level t)] with x hx
    intro hxS
    have hxP : x ∉ c.patch := fun hp => hxS (c.mem_slice_image_of_mem_patch x hp t hx.2)
    rw [A.weight_eq_zero_of_not_mem_patch i x hxP, zero_mul]
  rw [← he, c.integral_graphLevelMeasure_slice_image t ht.1 c.disk measurableSet_ball
    (c.disk_subset_sliceDomain t htC)]
  apply setIntegral_congr_fun measurableSet_ball
  intro u hu
  have huD := c.disk_subset_sliceDomain t htC hu
  change c.sliceJacobian (surfaceGraph (fun _ => t) u) *
    (A.weights i (c.slice t u) * (w (c.slice t u) / ‖graphGradient h (c.slice t u)‖)) = _
  rw [c.slice_eq_symm t u huD]
  dsimp only [weightedLocalTerm, localTerm, RegularHeightChart.weightedJacobian]
  rw [c.abs_det_fderiv_symm _ (c.ball_subset huD)]
  ring

theorem graphWeightedHeightDensity_eq_sum (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h))
    (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    graphWeightedHeightDensity h w t =
      ∑ i, ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u := by
  have hi := A.integrable_graphLevel_weight_div hh w hw t ht
  unfold graphWeightedHeightDensity
  calc
    _ = ∫ x, ∑ i, A.weights i x * (w x / ‖graphGradient h x‖)
        ∂graphLevelMeasure h t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := normalizedHausdorffTwo)
        (hh.measurableSet_level t)] with x hx
      rw [← Finset.sum_mul, A.sum_weights x ⟨hx.1, hx.2.le.trans ht.2⟩, one_mul]
    _ = ∑ i, ∫ x, A.weights i x * (w x / ‖graphGradient h x‖) ∂graphLevelMeasure h t :=
      integral_finset_sum _ (fun i _ => A.integrable_weight_mul _ hi i)
    _ = _ := Finset.sum_congr rfl (fun i _ => A.weighted_level_integral_spatial hh w i t ht)

/-- Compact fixed chart rectangles supply domination for signed observables. -/
theorem continuousOn_integral_weightedLocalTerm (w : JointSpace → ℝ)
    (hw : ContinuousOn w (graphClosedPositive h)) (i : Fin A.count) :
    ContinuousOn (fun t => ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u)
      (Icc 0 A.width) := by
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

theorem continuousOn_graphWeightedHeightDensity (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h)) :
    ContinuousOn (graphWeightedHeightDensity h w) (Icc 0 A.width) := by
  apply (continuousOn_finset_sum _
    (fun i _ => A.continuousOn_integral_weightedLocalTerm w hw i)).congr
  exact fun t ht => A.graphWeightedHeightDensity_eq_sum hh w hw t ht

theorem integrableOn_closedCollar_weighted (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun x : JointSpace => g (h x) * w x) (graphClosedCollar h A.width) := by
  have hc := hg.comp (hh.continuousOn_closedPositive.mono inter_subset_left)
    (fun x hx => ⟨hh.nonneg_on_closedPositive x hx.1, hx.2⟩)
  exact (hc.mul (hw.mono inter_subset_left)).integrableOn_compact (hh.isCompact_closedCollar A.width)

theorem integrableOn_weightedLocalTerm_mul (w : JointSpace → ℝ)
    (hw : ContinuousOn w (graphClosedPositive h)) (i : Fin A.count)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun p : ℝ × SurfacePlane => A.weightedLocalTerm w i p.1 p.2 * g p.1)
      (Icc 0 A.width ×ˢ (A.charts i).disk) := by
  have hc := (A.continuousOn_weightedLocalTerm w hw i).mul
    (hg.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  exact (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
    (prod_mono Subset.rfl Metric.ball_subset_closedBall)

theorem integral_chart_weighted (w : JointSpace → ℝ)
    (hw : ContinuousOn w (graphClosedPositive h)) (i : Fin A.count)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    (∫ p in (A.charts i).parameterRegion A.width,
      (A.charts i).weightedJacobian (A.weights i) p *
        (g (h ((A.charts i).chart.symm p)) * w ((A.charts i).chart.symm p))) =
      ∫ t in Icc 0 A.width, g t * ∫ u in (A.charts i).disk, A.weightedLocalTerm w i t u := by
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
        (g (h (c.chart.symm (jointHeightCoordinates.symm p))) *
          w (c.chart.symm (jointHeightCoordinates.symm p)))) =
      ∫ p : ℝ × SurfacePlane in Icc 0 A.width ×ˢ c.disk,
        A.weightedLocalTerm w i p.1 p.2 * g p.1 := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_ball)
    intro p hp
    have hpT := c.parameterRegion_subset_target A.width (A.width_lt i).le
      (show jointHeightCoordinates.symm p ∈ c.parameterRegion A.width by
        change p ∈ jointHeightCoordinates.symm ⁻¹' c.parameterRegion A.width
        rw [he]
        exact hp)
    dsimp only
    rw [c.height_symm _ hpT]
    dsimp only [weightedLocalTerm, localTerm]
    change (A.charts i).weightedJacobian (A.weights i) (surfaceGraph (fun _ => p.1) p.2) *
      (g p.1 * w ((A.charts i).chart.symm (surfaceGraph (fun _ => p.1) p.2))) = _
    ring
  rw [heq, Measure.volume_eq_prod, setIntegral_prod _
    (by simpa only [Measure.volume_eq_prod] using A.integrableOn_weightedLocalTerm_mul w hw i g hg)]
  simp only [integral_mul_const]
  simp only [mul_comm]
  rfl

/-- Coarea with a spatial observable and a continuous height profile. -/
theorem integral_closedCollar_weighted (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    (∫ x in graphClosedCollar h A.width, g (h x) * w x) =
      ∫ t in Icc 0 A.width, g t * graphWeightedHeightDensity h w t := by
  rw [A.integral_closedCollar_eq_sum hh _ (A.integrableOn_closedCollar_weighted hh w hw g hg)]
  simp_rw [A.integral_chart_weighted w hw _ g hg]
  rw [← integral_finset_sum _ (fun i _ =>
    (hg.mul (A.continuousOn_integral_weightedLocalTerm w hw i)).integrableOn_compact isCompact_Icc)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [A.graphWeightedHeightDensity_eq_sum hh w hw t ht, Finset.mul_sum]

end ControlledCollarAtlas

namespace AdmissibleGraphCap

/-- A continuous spatial observable has the actual canonical boundary flux
as its one-sided density limit. No global noncriticality is needed. -/
theorem tendsto_graphWeightedHeightDensity_zero {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h)) :
    Tendsto (graphWeightedHeightDensity h w) (𝓝[≥] 0)
      (𝓝 (∫ x, w x / ‖graphGradient h x‖ ∂graphSurfaceMeasure h)) := by
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  have hc := (continuousWithinAt_Icc_iff_Ici A.width_pos).mp
    (A.continuousOn_graphWeightedHeightDensity hh w hw 0 ⟨le_rfl, A.width_pos.le⟩)
  simpa only [graphWeightedHeightDensity_zero] using hc.tendsto

end AdmissibleGraphCap
end BoundaryDraft
