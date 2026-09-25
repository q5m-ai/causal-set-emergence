import BoundaryDraft.GraphAtlasRepresentation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# One-sided regularity of the canonical height density

Dominated convergence on each fixed planar disk, followed by the proved
partition-of-unity sum, gives continuity on a closed nonnegative collar.
Measurability and a uniform finite bound follow for the existing canonical
density. Its right-hand limit is the already checked boundary integral, not
the zero value on negative levels. No height coarea or action limit is used.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
namespace ControlledCollarAtlas

variable {h : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- Dominated convergence on a fixed disk includes both height endpoints.
The dominator is supplied by the controlled atlas, not a density hypothesis. -/
theorem continuousOn_integral_localTerm (i : Fin A.count) :
    ContinuousOn (fun t => ∫ u in (A.charts i).disk, A.localTerm i t u) (Icc 0 A.width) := by
  obtain ⟨M, _, hM⟩ := A.exists_uniform_integrable_dominator
  intro t ht
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (A.integrableOn_localTerm i s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    exact (hM i).2 s hs u hu
  · exact (hM i).1
  · filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    have hc : ContinuousOn (fun s => A.localTerm i s u) (Icc 0 A.width) :=
      (A.continuousOn_localTerm i).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hs => ⟨hs, Metric.ball_subset_closedBall hu⟩)
    exact hc t ht

/-- Smooth partition weights handle every chart overlap before taking the
limit. This is continuity of the canonical density, not a new definition. -/
theorem continuousOn_graphHeightDensity (hh : AdmissibleGraphCap h) :
    ContinuousOn (graphHeightDensity h) (Icc 0 A.width) := by
  apply (continuousOn_finset_sum _ (fun i _ => A.continuousOn_integral_localTerm i)).congr
  exact fun t ht => A.graphHeightDensity_eq_sum hh t ht

/-- Borel measurability of the canonical density on the actual collar. -/
theorem measurable_graphHeightDensity (hh : AdmissibleGraphCap h) :
    Measurable (fun t : Icc (0 : ℝ) A.width => graphHeightDensity h t) :=
  (A.continuousOn_graphHeightDensity hh).restrict.measurable

/-- The restricted-measure form is convenient for signed height integrals. -/
theorem aestronglyMeasurable_graphHeightDensity (hh : AdmissibleGraphCap h) :
    AEStronglyMeasurable (graphHeightDensity h) (volume.restrict (Icc 0 A.width)) :=
  (A.continuousOn_graphHeightDensity hh).aestronglyMeasurable measurableSet_Icc

/-- A measurable zero cutoff is available to half-line kernel theorems without
asserting measurability or regularity of any positive critical level outside
the collar. The uncut canonical density remains the object of the proof. -/
theorem measurable_indicator_graphHeightDensity (hh : AdmissibleGraphCap h) :
    Measurable ((Icc 0 A.width).indicator (graphHeightDensity h)) := by
  classical
  rw [← piecewise_eq_indicator]
  exact (A.continuousOn_graphHeightDensity hh).measurable_piecewise
    continuousOn_const measurableSet_Icc

/-- Compactness upgrades the derived continuity to one positive finite bound
valid uniformly over the whole closed collar. -/
theorem exists_bound_graphHeightDensity (hh : AdmissibleGraphCap h) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 A.width, ‖graphHeightDensity h t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (A.continuousOn_graphHeightDensity hh)
  refine ⟨max C 0 + 1, by positivity, fun t ht => ?_⟩
  exact (hC t ht).trans ((le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one))

include A in
/-- Only nonnegative heights approach the joint. There is no two-sided
continuity claim for the canonical zero-on-negative-heights density. -/
theorem continuousWithinAt_graphHeightDensity_zero (hh : AdmissibleGraphCap h) :
    ContinuousWithinAt (graphHeightDensity h) (Ici 0) 0 :=
  (continuousWithinAt_Icc_iff_Ici A.width_pos).mp
    (A.continuousOn_graphHeightDensity hh 0 ⟨le_rfl, A.width_pos.le⟩)

end ControlledCollarAtlas
namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- All regularity needed on one nonnegative collar follows from admissibility
and the constructed atlas. No global noncriticality assumption is introduced. -/
theorem exists_regular_heightDensity_band : ∃ δ : ℝ, 0 < δ ∧
    ContinuousOn (graphHeightDensity h) (Icc 0 δ) ∧
    Measurable (fun t : Icc (0 : ℝ) δ => graphHeightDensity h t) ∧
    AEStronglyMeasurable (graphHeightDensity h) (volume.restrict (Icc 0 δ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 δ, ‖graphHeightDensity h t‖ ≤ C := by
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  exact ⟨A.width, A.width_pos, A.continuousOn_graphHeightDensity hh,
    A.measurable_graphHeightDensity hh, A.aestronglyMeasurable_graphHeightDensity hh,
    A.exists_bound_graphHeightDensity hh⟩

theorem continuousWithinAt_graphHeightDensity_zero :
    ContinuousWithinAt (graphHeightDensity h) (Ici 0) 0 := by
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  exact A.continuousWithinAt_graphHeightDensity_zero hh

/-- The right-hand limit is the previously checked reciprocal-gradient joint
integral, by the existing exact zero-height identity. -/
theorem tendsto_graphHeightDensity_zero :
    Tendsto (graphHeightDensity h) (𝓝[≥] 0) (𝓝 (graphBoundaryIntegral h)) := by
  simpa only [graphHeightDensity_zero] using hh.continuousWithinAt_graphHeightDensity_zero.tendsto

end AdmissibleGraphCap
end BoundaryDraft
