import BoundaryDraft.Pilot3Atlas

/-!
# Common finite-sum collar representation

Actual canonical level integrals and ambient integrals use the same local
weighted Jacobian. Compact fixed rectangles supply a uniform integrable bound.
The partition handles all overlaps before integrating in height.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Manifold
noncomputable section
namespace BoundaryDraft
namespace Pilot3CollarAtlas
set_option maxHeartbeats 800000
variable {h : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

theorem sum_weights (x : Pilot3Space) (hx : x ∈ pilot3ClosedCollar h A.width) :
    ∑ i, A.weights i x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using A.weights.sum_eq_one hx

theorem weight_eq_zero_of_not_mem_patch (i : Fin A.count) (x : Pilot3Space)
    (hx : x ∉ (A.charts i).patch) : A.weights i x = 0 := by
  by_contra hn
  exact hx (A.subordinate i (subset_tsupport _ hn))

theorem integrable_weight_mul {μ : Measure Pilot3Space} (f : Pilot3Space → ℝ)
    (hf : Integrable f μ) (i : Fin A.count) : Integrable (fun x => A.weights i x * f x) μ :=
  hf.bdd_mul (A.weights i).contMDiff.continuous.aestronglyMeasurable ⟨1, fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (A.weights.nonneg i x)]
    exact A.weights.le_one i x⟩

def localTerm (i : Fin A.count) (t u : ℝ) : ℝ :=
  (A.charts i).weightedJacobian (A.weights i) (pilot3Curve (fun _ => t) u)

theorem continuousOn_localTerm (i : Fin A.count) :
    ContinuousOn (fun p : ℝ × ℝ => A.localTerm i p.1 p.2)
      (Icc 0 A.width ×ˢ (A.charts i).closedDisk) := by
  apply ((A.charts i).continuousOn_weightedJacobian (A.weights i)
    (A.weights i).contMDiff.continuous).comp pilot3Coordinates.symm.continuous.continuousOn
  intro p hp
  exact (A.charts i).ball_subset ((A.charts i).rectangle_subset p.1
    ⟨(neg_nonpos.mpr (A.charts i).width_pos.le).trans hp.1.1,
      hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)

theorem integrableOn_localTerm (i : Fin A.count) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    IntegrableOn (A.localTerm i t) (A.charts i).disk := by
  have hc : ContinuousOn (A.localTerm i t) (A.charts i).closedDisk :=
    (A.continuousOn_localTerm i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨ht, hu⟩)
  exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall

theorem exists_uniform_integrable_dominator : ∃ M : ℝ, 0 < M ∧
    ∀ i, IntegrableOn (fun _ : ℝ => M) (A.charts i).disk ∧
      ∀ t ∈ Icc 0 A.width, ∀ u ∈ (A.charts i).disk, ‖A.localTerm i t u‖ ≤ M := by
  classical
  have hb : ∀ i, ∃ M : ℝ, ∀ p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk,
      ‖A.localTerm i p.1 p.2‖ ≤ M := fun i =>
    (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn (A.continuousOn_localTerm i)
  choose M hM using hb
  let B : ℝ := 1 + ∑ i, max (M i) 0
  have hnonneg : 0 ≤ ∑ i, max (M i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨B, by dsimp [B]; linarith, fun i => ⟨?_, ?_⟩⟩
  · haveI : IsFiniteMeasure (volume.restrict (A.charts i).disk) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact Metric.isBounded_ball.measure_lt_top
    exact integrable_const B
  · intro t ht u hu
    have hle : max (M i) 0 ≤ ∑ j, max (M j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    exact (hM i (t, u) ⟨ht, Metric.ball_subset_closedBall hu⟩).trans
      ((le_max_left (M i) 0).trans (hle.trans (le_add_of_nonneg_left zero_le_one)))

/-- Arbitrary integrable canonical level observables glue without any
connectedness or overlap multiplicity assumption. -/
theorem integral_level_eq_sum (hh : Pilot3RegularHeight h) (t : ℝ) (ht : t ∈ Icc 0 A.width)
    (F : Pilot3Space → ℝ) (hF : Integrable F (pilot3LevelMeasure h t)) :
    (∫ x, F x ∂pilot3LevelMeasure h t) = ∑ i, ∫ u in (A.charts i).disk,
      (A.charts i).sliceJacobian (pilot3Curve (fun _ => t) u) *
        (A.weights i ((A.charts i).slice t u) * F ((A.charts i).slice t u)) := by
  have he : (∫ x, F x ∂pilot3LevelMeasure h t) =
      ∑ i, ∫ x, A.weights i x * F x ∂pilot3LevelMeasure h t := by
    rw [← integral_finset_sum _ (fun i _ => A.integrable_weight_mul F hF i)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := (μH[1] : Measure Pilot3Space)) (hh.measurableSet_level t)] with x hx
    rw [← Finset.sum_mul, A.sum_weights x ⟨hx.1, hx.2.le.trans ht.2⟩, one_mul]
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  let c := A.charts i
  have htC : t ∈ Icc (-c.width) c.width :=
    ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩
  have hi : (∫ x in c.slice t '' c.disk, A.weights i x * F x ∂pilot3LevelMeasure h t) =
      ∫ x, A.weights i x * F x ∂pilot3LevelMeasure h t := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_restrict_mem (μ := (μH[1] : Measure Pilot3Space)) (hh.measurableSet_level t)] with x hx
    intro hxS
    rw [A.weight_eq_zero_of_not_mem_patch i x (fun hp => hxS (c.mem_slice_image_of_mem_patch x hp t hx.2)), zero_mul]
  rw [← hi, c.integral_levelMeasure_slice_image t ht.1 c.disk measurableSet_ball (c.disk_subset_sliceDomain t htC)]

/-- The reciprocal-gradient density is an application of the canonical level
sum, not a newly selected density. -/
theorem heightDensity_eq_sum (hh : Pilot3RegularHeight h) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    pilot3HeightDensity h t = ∑ i, ∫ u in (A.charts i).disk, A.localTerm i t u := by
  have hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0 :=
    fun x hx => A.noncritical x ⟨hx.1, hx.2.le.trans ht.2⟩
  rw [pilot3HeightDensity, A.integral_level_eq_sum hh t ht _ (hh.integrable_level_reciprocal_gradient t hreg)]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun measurableSet_ball
  intro u hu
  let c := A.charts i
  have huD := c.disk_subset_sliceDomain t
    ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩ hu
  dsimp only
  rw [c.slice_eq_symm t u huD]
  change c.sliceJacobian (pilot3Curve (fun _ => t) u) * _ = c.weightedJacobian (A.weights i) (pilot3Curve (fun _ => t) u)
  rw [Pilot3HeightChart.weightedJacobian, c.abs_det_fderiv_symm _ (c.ball_subset huD)]
  ring

theorem weighted_collar_integral (hh : Pilot3RegularHeight h) (i : Fin A.count) (f : Pilot3Space → ℝ) :
    (∫ x in pilot3ClosedCollar h A.width, A.weights i x * f x) =
      ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p * f ((A.charts i).chart.symm p) := by
  let c := A.charts i
  have he : (∫ x in c.chart.symm '' c.parameterRegion A.width, A.weights i x * f x) =
      ∫ x in pilot3ClosedCollar h A.width, A.weights i x * f x := by
    symm
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero (f := fun x => A.weights i x * f x)
      (hh.isCompact_closedCollar A.width).isClosed.measurableSet
      (c.parameterImage_subset_closedCollar A.width (A.width_lt i).le)
    intro x hx
    have hxP : x ∉ c.patch := fun hp => hx.2 (c.mem_parameterImage_of_mem_patch A.width x hp
      ⟨hh.nonneg_on_closedPositive x hx.1.1, hx.1.2⟩)
    rw [A.weight_eq_zero_of_not_mem_patch i x hxP, zero_mul]
  rw [← he, c.integral_symm_image _ (c.measurableSet_parameterRegion A.width)
    (c.parameterRegion_subset_target A.width (A.width_lt i).le)]
  apply setIntegral_congr_fun (c.measurableSet_parameterRegion A.width)
  intro p hp
  dsimp only
  rw [Pilot3HeightChart.weightedJacobian,
    c.abs_det_fderiv_symm p (c.parameterRegion_subset_target A.width (A.width_lt i).le hp)]
  ring

theorem integral_closedCollar_eq_sum (hh : Pilot3RegularHeight h) (f : Pilot3Space → ℝ)
    (hf : IntegrableOn f (pilot3ClosedCollar h A.width)) :
    (∫ x in pilot3ClosedCollar h A.width, f x) =
      ∑ i, ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p * f ((A.charts i).chart.symm p) := by
  calc
    _ = ∫ x in pilot3ClosedCollar h A.width, ∑ i, A.weights i x * f x := by
      apply setIntegral_congr_fun (hh.isCompact_closedCollar A.width).isClosed.measurableSet
      intro x hx
      change f x = ∑ i, A.weights i x * f x
      rw [← Finset.sum_mul, A.sum_weights x hx, one_mul]
    _ = ∑ i, ∫ x in pilot3ClosedCollar h A.width, A.weights i x * f x :=
      integral_finset_sum _ (fun i _ => A.integrable_weight_mul f hf i)
    _ = _ := Finset.sum_congr rfl (fun i _ => A.weighted_collar_integral hh i f)

end Pilot3CollarAtlas
end BoundaryDraft
