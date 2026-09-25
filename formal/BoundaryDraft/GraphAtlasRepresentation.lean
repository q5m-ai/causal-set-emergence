import BoundaryDraft.GraphAtlas

/-!
# Common finite-sum collar representation

The same weighted Jacobian occurs in ambient chart integrals and canonical
level-density integrals. All planar domains are fixed. The local data are
jointly continuous on compact parameter rectangles and admit one uniform
integrable constant dominator on these finite-measure domains. This file does
not integrate in height or take a height limit.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Manifold
noncomputable section
namespace BoundaryDraft
namespace ControlledCollarAtlas

variable {h : Spatial → ℝ} (A : ControlledCollarAtlas h)

theorem sum_weights (x : JointSpace) (hx : x ∈ graphClosedCollar h A.width) :
    ∑ i, A.weights i x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using A.weights.sum_eq_one hx

theorem weight_eq_zero_of_not_mem_patch (i : Fin A.count) (x : JointSpace)
    (hx : x ∉ (A.charts i).patch) : A.weights i x = 0 := by
  by_contra hn
  exact hx (A.subordinate i (subset_tsupport _ hn))

theorem integrable_weight_mul {μ : Measure JointSpace} (f : JointSpace → ℝ)
    (hf : Integrable f μ) (i : Fin A.count) :
    Integrable (fun x => A.weights i x * f x) μ :=
  hf.bdd_mul (A.weights i).contMDiff.continuous.aestronglyMeasurable ⟨1, fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (A.weights.nonneg i x)]
    exact A.weights.le_one i x⟩

/-- The shared local term on a fixed planar domain. -/
def localTerm (i : Fin A.count) (t : ℝ) (u : SurfacePlane) : ℝ :=
  (A.charts i).weightedJacobian (A.weights i) (surfaceGraph (fun _ => t) u)

/-- The local scalar data are continuous jointly in height and planar
coordinates, up to the boundary of one compact fixed rectangle. -/
theorem continuousOn_localTerm (i : Fin A.count) :
    ContinuousOn (fun p : ℝ × SurfacePlane => A.localTerm i p.1 p.2)
      (Icc 0 A.width ×ˢ (A.charts i).closedDisk) := by
  apply ((A.charts i).continuousOn_weightedJacobian (A.weights i)
    (A.weights i).contMDiff.continuous).comp jointHeightCoordinates.symm.continuous.continuousOn
  intro p hp
  exact (A.charts i).ball_subset ((A.charts i).rectangle_subset p.1
    ⟨(neg_nonpos.mpr (A.charts i).width_pos.le).trans hp.1.1,
      hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)

/-- All local integrands are absolutely integrable on their fixed disks. -/
theorem integrableOn_localTerm (i : Fin A.count) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    IntegrableOn (A.localTerm i t) (A.charts i).disk := by
  have hc : ContinuousOn (A.localTerm i t) (A.charts i).closedDisk :=
    (A.continuousOn_localTerm i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨ht, hu⟩)
  exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall

/-- One height-independent constant dominates every local term on every
fixed disk, and is integrable on each such disk. This is not an assumed
boundedness or continuity statement about the global height density. -/
theorem exists_uniform_integrable_dominator : ∃ M : ℝ, 0 < M ∧
    ∀ i, IntegrableOn (fun _ : SurfacePlane => M) (A.charts i).disk ∧
      ∀ t ∈ Icc 0 A.width, ∀ u ∈ (A.charts i).disk, ‖A.localTerm i t u‖ ≤ M := by
  classical
  have hb : ∀ i, ∃ M : ℝ, ∀ p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk,
      ‖A.localTerm i p.1 p.2‖ ≤ M := fun i =>
    (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      (A.continuousOn_localTerm i)
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
    have hbound := hM i (t, u) ⟨ht, Metric.ball_subset_closedBall hu⟩
    exact hbound.trans ((le_max_left (M i) 0).trans (hle.trans (le_add_of_nonneg_left zero_le_one)))

/-- The weighted contribution of one canonical level is exactly its chart
term. Subordination, not a multiplicity assumption, localizes the integral. -/
theorem weighted_level_integral (hh : AdmissibleGraphCap h) (i : Fin A.count)
    (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    (∫ x, A.weights i x * (1 / ‖graphGradient h x‖) ∂graphLevelMeasure h t) =
      ∫ u in (A.charts i).disk, A.localTerm i t u := by
  let c := A.charts i
  have htC : t ∈ Icc (-c.width) c.width :=
    ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩
  have he : (∫ x in c.slice t '' c.disk, A.weights i x * (1 / ‖graphGradient h x‖)
      ∂graphLevelMeasure h t) =
      ∫ x, A.weights i x * (1 / ‖graphGradient h x‖) ∂graphLevelMeasure h t := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_restrict_mem (μ := normalizedHausdorffTwo) (hh.measurableSet_level t)] with x hx
    intro hxS
    have hxP : x ∉ c.patch := fun hp => hxS (c.mem_slice_image_of_mem_patch x hp t hx.2)
    rw [A.weight_eq_zero_of_not_mem_patch i x hxP, zero_mul]
  rw [← he, c.integral_graphLevelMeasure_slice_image t ht.1 c.disk measurableSet_ball
    (c.disk_subset_sliceDomain t htC)]
  apply setIntegral_congr_fun measurableSet_ball
  intro u hu
  have huD := c.disk_subset_sliceDomain t htC hu
  change c.sliceJacobian (surfaceGraph (fun _ => t) u) *
    (A.weights i (c.slice t u) * (1 / ‖graphGradient h (c.slice t u)‖)) = _
  rw [c.slice_eq_symm t u huD]
  change c.sliceJacobian (surfaceGraph (fun _ => t) u) * _ =
    c.weightedJacobian (A.weights i) (surfaceGraph (fun _ => t) u)
  rw [RegularHeightChart.weightedJacobian, c.abs_det_fderiv_symm _ (c.ball_subset huD)]
  ring

/-- Finite-sum representation of the canonical height density. This equality
alone does not assert continuity or perform any height integration. -/
theorem graphHeightDensity_eq_sum (hh : AdmissibleGraphCap h) (t : ℝ)
    (ht : t ∈ Icc 0 A.width) :
    graphHeightDensity h t = ∑ i, ∫ u in (A.charts i).disk, A.localTerm i t u := by
  have hreg : ∀ x ∈ graphLevel h t, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0 :=
    fun x hx => A.noncritical x ⟨hx.1, hx.2.le.trans ht.2⟩
  have hi := hh.integrable_graphLevel_reciprocal_slope t hreg
  unfold graphHeightDensity
  calc
    _ = ∫ x, ∑ i, A.weights i x * (1 / ‖graphGradient h x‖) ∂graphLevelMeasure h t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := normalizedHausdorffTwo) (hh.measurableSet_level t)] with x hx
      rw [← Finset.sum_mul, A.sum_weights x ⟨hx.1, hx.2.le.trans ht.2⟩, one_mul]
    _ = ∑ i, ∫ x, A.weights i x * (1 / ‖graphGradient h x‖) ∂graphLevelMeasure h t :=
      integral_finset_sum _ (fun i _ => A.integrable_weight_mul _ hi i)
    _ = _ := Finset.sum_congr rfl (fun i _ => A.weighted_level_integral hh i t ht)

/-- One weighted ambient collar contribution in fixed Euclidean coordinates.
No height Fubini or global coarea theorem is used here. -/
theorem weighted_collar_integral (hh : AdmissibleGraphCap h) (i : Fin A.count)
    (f : JointSpace → ℝ) :
    (∫ x in graphClosedCollar h A.width, A.weights i x * f x) =
      ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p * f ((A.charts i).chart.symm p) := by
  let c := A.charts i
  have he : (∫ x in c.chart.symm '' c.parameterRegion A.width, A.weights i x * f x) =
      ∫ x in graphClosedCollar h A.width, A.weights i x * f x := by
    symm
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (f := fun x => A.weights i x * f x)
      (hh.isCompact_closedCollar A.width).isClosed.measurableSet
      (c.parameterImage_subset_closedCollar A.width (A.width_lt i).le)
    intro x hx
    have hxP : x ∉ c.patch := by
      intro hp
      exact hx.2 (c.mem_parameterImage_of_mem_patch A.width x hp
        ⟨hh.nonneg_on_closedPositive x hx.1.1, hx.1.2⟩)
    rw [A.weight_eq_zero_of_not_mem_patch i x hxP, zero_mul]
  rw [← he, c.integral_symm_image _ (c.measurableSet_parameterRegion A.width)
    (c.parameterRegion_subset_target A.width (A.width_lt i).le)]
  apply setIntegral_congr_fun (c.measurableSet_parameterRegion A.width)
  intro p hp
  dsimp only
  rw [RegularHeightChart.weightedJacobian,
    c.abs_det_fderiv_symm p (c.parameterRegion_subset_target A.width (A.width_lt i).le hp)]
  ring

/-- Common finite-sum ambient representation for every absolutely integrable
collar test function, including the signed kernel. -/
theorem integral_closedCollar_eq_sum (hh : AdmissibleGraphCap h) (f : JointSpace → ℝ)
    (hf : IntegrableOn f (graphClosedCollar h A.width)) :
    (∫ x in graphClosedCollar h A.width, f x) =
      ∑ i, ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p * f ((A.charts i).chart.symm p) := by
  calc
    _ = ∫ x in graphClosedCollar h A.width, ∑ i, A.weights i x * f x := by
      apply setIntegral_congr_fun (hh.isCompact_closedCollar A.width).isClosed.measurableSet
      intro x hx
      change f x = ∑ i, A.weights i x * f x
      rw [← Finset.sum_mul, A.sum_weights x hx, one_mul]
    _ = ∑ i, ∫ x in graphClosedCollar h A.width, A.weights i x * f x :=
      integral_finset_sum _ (fun i _ => A.integrable_weight_mul f hf i)
    _ = _ := Finset.sum_congr rfl (fun i _ => A.weighted_collar_integral hh i f)

end ControlledCollarAtlas
end BoundaryDraft
