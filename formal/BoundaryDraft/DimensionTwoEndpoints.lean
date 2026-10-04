import BoundaryDraft.Pilot3Contract
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Physical-dimension-two endpoint normalization

The compact regular zero set of a one-dimensional height is finite by the
inverse function theorem. Its canonical zero-dimensional Hausdorff restriction
is exactly counting measure and its integral sums ALL endpoints. No new
2D causal-region/admissibility contract or dimensional action limit is claimed.
-/

open MeasureTheory Set
open scoped Topology ENNReal ContDiff
noncomputable section
namespace BoundaryDraft

def dimensionTwoEndpointMeasure (J : Finset (DimensionSpatial 1)) : Measure (DimensionSpatial 1) :=
  (μH[0] : Measure (DimensionSpatial 1)).restrict (J : Set (DimensionSpatial 1))

/-- Equality on every Borel subset, with unit mass at each endpoint. -/
theorem dimensionTwoEndpointMeasure_eq_count (J : Finset (DimensionSpatial 1)) :
    dimensionTwoEndpointMeasure J = Measure.count.restrict (J : Set (DimensionSpatial 1)) := by
  classical
  unfold dimensionTwoEndpointMeasure
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
    have hd : Disjoint ({a} : Set (DimensionSpatial 1)) (J : Set (DimensionSpatial 1)) := disjoint_singleton_left.mpr ha
    rw [Finset.coe_insert, insert_eq, Measure.restrict_union hd J.measurableSet,
      Measure.restrict_union hd J.measurableSet, Measure.restrict_singleton,
      Measure.restrict_singleton, Measure.hausdorffMeasure_zero_singleton, Measure.count_singleton, ih]

theorem dimensionTwoEndpoint_integrable (J : Finset (DimensionSpatial 1)) (w : DimensionSpatial 1 → ℝ) :
    Integrable w (dimensionTwoEndpointMeasure J) := by
  change IntegrableOn w (J : Set (DimensionSpatial 1)) (μH[0] : Measure (DimensionSpatial 1))
  rw [← J.toSet.biUnion_of_singleton]
  apply (integrableOn_finite_biUnion J.finite_toSet).mpr
  intro x _
  exact integrableOn_singleton_iff.mpr (Or.inr (by simp))

theorem dimensionTwoEndpoint_integral (J : Finset (DimensionSpatial 1)) (w : DimensionSpatial 1 → ℝ) :
    (∫ x, w x ∂dimensionTwoEndpointMeasure J) = ∑ x ∈ J, w x := by
  rw [dimensionTwoEndpointMeasure, integral_finset J w (dimensionTwoEndpoint_integrable J w)]
  simp only [measureReal_def, Measure.hausdorffMeasure_zero_singleton, ENNReal.toReal_one, one_smul]

theorem dimensionTwoEndpoint_finite (J : Finset (DimensionSpatial 1)) : IsFiniteMeasure (dimensionTwoEndpointMeasure J) := by
  have hi := dimensionTwoEndpoint_integrable J (fun _ => 1)
  exact (integrable_const_iff.mp hi).resolve_left one_ne_zero

/-- Compact regular zero sets are finite in spatial dimension ONE. -/
theorem dimensionTwo_regular_zero_set_finite {h : DimensionSpatial 1 → ℝ} {J : Set (DimensionSpatial 1)}
    (hJ : IsCompact J) (hz : ∀ x ∈ J, h x = 0)
    (hs : ∀ x ∈ J, ContDiffAt ℝ ∞ h x) (hr : ∀ x ∈ J, fderiv ℝ h x ≠ 0) : J.Finite := by
  classical
  have hlocal : ∀ x : J, ∃ U : Set (DimensionSpatial 1), IsOpen U ∧ x.val ∈ U ∧
      ∀ y ∈ J, y ∈ U → y = x.val := by
    intro x
    let L := fderiv ℝ h x.val
    have hn : L.toLinearMap ≠ 0 := by
      intro he
      apply hr x.val x.property
      ext v
      exact LinearMap.congr_fun he v
    have hsur : Function.Surjective L := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hn)
    have hinj : Function.Injective L :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp [DimensionSpatial] : Module.finrank ℝ (DimensionSpatial 1) = Module.finrank ℝ ℝ)).mpr hsur
    let eL : DimensionSpatial 1 ≃L[ℝ] ℝ :=
      (LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsur⟩).toContinuousLinearEquiv
    have hd : HasStrictFDerivAt h (eL : DimensionSpatial 1 →L[ℝ] ℝ) x.val :=
      (hs x.val x.property).hasStrictFDerivAt (by simp)
    let e := hd.toPartialHomeomorph h
    have hx := hd.mem_toPartialHomeomorph_source
    refine ⟨e.source, e.open_source, hx, fun y hy hyU => ?_⟩
    exact e.injOn hyU hx ((hz y hy).trans (hz x.val x.property).symm)
  choose U hU hxU huniq using hlocal
  obtain ⟨T, hT⟩ := hJ.elim_finite_subcover U hU (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  apply (T.finite_toSet.image Subtype.val).subset
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hT hx)
  exact ⟨j, hj, (huniq j x hx hxj).symm⟩

def dimensionTwoSpatialJoint (h : DimensionSpatial 1 → ℝ) : Set (DimensionSpatial 1) :=
  closure {x | 0 < h x} ∩ {x | h x = 0}

def dimensionTwoJointMeasure (h : DimensionSpatial 1 → ℝ) : Measure (DimensionSpatial 1) :=
  (μH[0] : Measure (DimensionSpatial 1)).restrict (dimensionTwoSpatialJoint h)

/-- Every component is retained; exterior raw zeros are excluded by closure. -/
theorem dimensionTwo_joint_finite {h : DimensionSpatial 1 → ℝ}
    (hb : Bornology.IsBounded {x | 0 < h x})
    (hs : ∀ x ∈ closure {x | 0 < h x}, ContDiffAt ℝ ∞ h x)
    (hr : ∀ x ∈ dimensionTwoSpatialJoint h, fderiv ℝ h x ≠ 0) : (dimensionTwoSpatialJoint h).Finite := by
  have hc : ContinuousOn h (closure {x | 0 < h x}) := fun x hx => (hs x hx).continuousAt.continuousWithinAt
  have hcompact : IsCompact (dimensionTwoSpatialJoint h) :=
    hb.isCompact_closure.of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed isClosed_closure (isClosed_singleton (x := 0))) inter_subset_left
  exact dimensionTwo_regular_zero_set_finite hcompact (fun _ hx => hx.2) (fun x hx => hs x hx.1) hr

/-- Intrinsic all-endpoint target at unit normalization, for ANY observable. -/
theorem dimensionTwo_joint_integral {h : DimensionSpatial 1 → ℝ}
    (hb : Bornology.IsBounded {x | 0 < h x})
    (hs : ∀ x ∈ closure {x | 0 < h x}, ContDiffAt ℝ ∞ h x)
    (hr : ∀ x ∈ dimensionTwoSpatialJoint h, fderiv ℝ h x ≠ 0) (w : DimensionSpatial 1 → ℝ) :
    Integrable w (dimensionTwoJointMeasure h) ∧
      (∫ x, w x ∂dimensionTwoJointMeasure h) = ∑ x ∈ (dimensionTwo_joint_finite hb hs hr).toFinset, w x := by
  have he : dimensionTwoJointMeasure h = dimensionTwoEndpointMeasure (dimensionTwo_joint_finite hb hs hr).toFinset := by
    simp only [dimensionTwoJointMeasure, dimensionTwoEndpointMeasure, Set.Finite.coe_toFinset]
  rw [he]
  exact ⟨dimensionTwoEndpoint_integrable _ w, dimensionTwoEndpoint_integral _ w⟩

end BoundaryDraft
