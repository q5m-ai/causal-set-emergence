import BoundaryDraft.GraphGeometry
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Compact joint and a uniformly noncritical boundary band

This is a prerequisite for, not a proof of, a regular integration collar.
The critical set is separated from height zero by compactness. No condition
is imposed on positive-height critical points away from the resulting band.
Neither a coarea formula nor a surface measure is assumed here.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- The closed positive region in the Euclidean, rather than coordinate sup,
metric. The distinction matters for future surface-measure constructions. -/
def graphClosedPositive (h : Spatial → ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  closure {x | 0 < h x}

/-- Only zeros approached from the positive region belong to the joint. -/
def graphJoint (h : Spatial → ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  graphClosedPositive h ∩ {x | h x = 0}

namespace GraphCapData

variable {h : Spatial → ℝ} (hh : GraphCapData h)
include hh

/-- Compactness transfers through the coordinate homeomorphism, not an
incorrect identification of the Euclidean and coordinate norms. -/
theorem isCompact_closedPositive : IsCompact (graphClosedPositive h) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph
  have he : graphClosedPositive h = e ⁻¹' closure {x : Spatial | 0 < h x} := by
    rw [e.preimage_closure]
    rfl
  rw [he]
  exact e.isCompact_preimage.mpr hh.bounded_positive.isCompact_closure

end GraphCapData

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem continuousOn_closedPositive :
    ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => h x) (graphClosedPositive h) :=
  fun x hx => (hh.smooth_near x hx).continuousAt.continuousWithinAt

theorem continuousOn_fderiv_closedPositive :
    ContinuousOn (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => h x))
      (graphClosedPositive h) := by
  intro x hx
  exact ((hh.smooth_near x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt

/-- The Euclidean joint agrees with the already established spatial frontier. -/
theorem graphJoint_eq_frontier :
    graphJoint h = frontier {x : EuclideanSpace ℝ (Fin 3) | 0 < h x} := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph
  have he := e.preimage_frontier {x : Spatial | 0 < h x}
  rw [hh.frontier_eq h, preimage_inter, e.preimage_closure] at he
  exact he

theorem isCompact_joint : IsCompact (graphJoint h) := by
  rw [hh.graphJoint_eq_frontier]
  exact hh.toGraphCapData.isCompact_closedPositive.of_isClosed_subset
    isClosed_frontier frontier_subset_closure

theorem measurableSet_joint : MeasurableSet (graphJoint h) :=
  hh.isCompact_joint.isClosed.measurableSet

theorem nonneg_on_closedPositive (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ graphClosedPositive h) : 0 ≤ h x := by
  by_cases hp : 0 < h x
  · exact hp.le
  · have hf : x ∈ frontier {x : EuclideanSpace ℝ (Fin 3) | 0 < h x} :=
      ⟨hx, fun hi => hp (show x ∈ {x : EuclideanSpace ℝ (Fin 3) | 0 < h x} from interior_subset hi)⟩
    rw [← hh.graphJoint_eq_frontier] at hf
    exact hf.2.ge

/-- There is a uniform positive height below which the actual differential
never vanishes in the closed positive region. This includes height zero,
allows an empty cap, and does not exclude interior critical points. -/
theorem exists_noncritical_band : ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ graphClosedPositive h, h x ≤ δ →
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => h y) x ≠ 0 := by
  let K := graphClosedPositive h
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hh.toGraphCapData.isCompact_closedPositive
  let C : Set K := {x | fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => h y) x.val = 0}
  have hC : IsCompact C :=
    (isClosed_eq hh.continuousOn_fderiv_closedPositive.restrict continuous_const).isCompact
  have hpos : ∀ x ∈ C, 0 < h x.val := by
    intro x hx
    refine lt_of_le_of_ne (hh.nonneg_on_closedPositive x.val x.property) ?_
    intro hz
    exact hh.regular_zero x.val x.property hz.symm hx
  obtain ⟨m, hm, hmin⟩ := hC.exists_forall_le'
    hh.continuousOn_closedPositive.restrict.continuousOn hpos
  refine ⟨m / 2, half_pos hm, ?_⟩
  intro x hx hδ hc
  have hle := hmin ⟨x, hx⟩ hc
  dsimp at hle
  linarith

/-- At each noncritical point of the closed cap, the ambient C³ extension
is regular on an open neighborhood. This is local analytic data for a later
implicit-function construction, not an assumed level-set chart. -/
theorem exists_regular_neighborhood (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => h y) x ≠ 0) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U ∧ x ∈ U ∧
      ContDiffOn ℝ 3 (fun y : EuclideanSpace ℝ (Fin 3) => h y) U ∧
      ∀ y ∈ U, fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => h z) y ≠ 0 := by
  have hc := ((hh.smooth_near x hx).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hn : {y | fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => h z) y ≠ 0} ∈ 𝓝 x :=
    hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hr)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hn
  obtain ⟨W, hW, hxW, hsmooth⟩ := (hh.smooth_near x hx).contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ x), univ_inter] at hsmooth
  refine ⟨W ∩ V, hW.inter hVopen, ⟨hxW, hxV⟩, hsmooth.mono inter_subset_left, ?_⟩
  intro y hy
  exact hVsub hy.2

end AdmissibleGraphCap
end BoundaryDraft
