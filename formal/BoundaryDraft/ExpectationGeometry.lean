import BoundaryDraft.SpacetimeSprinkling
import BoundaryDraft.TimelikeInterval
import BoundaryDraft.NullBoundary

/-!
# Geometry needed by the finite-density expectation identity

Causal convexity is interval containment, not an assumed integral identity.
The interval rate is computed from restricted volume. Endpoints have zero
volume; null-related endpoint pairs form a null set and are removed only in
integration, not from the finite order or its interval counts.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace BoundaryDraft

/-- Every closed causal interval between points of the region stays inside it. -/
def CausallyConvex (M : Set Spacetime) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, causalInterval x y ⊆ M

theorem GraphCapData.causallyConvex {h : Spatial → ℝ} (hh : GraphCapData h) :
    CausallyConvex (graphCapRegion h) := by
  intro x hx y hy z hz
  exact graphCap_causallyConvex h hh x z y hx hy hz.1 hz.2

theorem causallyConvex_nullCap (T a : ℝ) : CausallyConvex (nullCapRegion T a) := by
  intro x hx y hy z hz
  exact nullCap_causallyConvex T a hx hy hz.1 hz.2

/-- Removing the two marked endpoints does not change interval volume. -/
theorem volume_causalIntervalInterior (x y : Spacetime) :
    volume (causalIntervalInterior x y) = volume (causalInterval x y) := by
  exact measure_diff_null (((Set.finite_singleton y).insert x).measure_zero volume)

/-- The restricted Poisson rate is the geometric Minkowski rate when the
endpoints lie in a causally convex region and are timelike related. -/
theorem FiniteSprinkling.interval_rate (S : FiniteSprinkling)
    (hconv : CausallyConvex S.region) {x y : Spacetime}
    (hx : x ∈ S.region) (hy : y ∈ S.region) (hxy : y ∈ chronologicalFuture x) :
    (S.intensity (causalIntervalInterior x y)).toReal =
      (Real.pi / 24) * S.density * intervalSq x y ^ 2 := by
  rw [S.intensity_apply_of_subset (measurableSet_causalIntervalInterior x y)
    (fun _ hz => hconv x hx y hy hz.1), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal S.density_pos.le, volume_causalIntervalInterior,
    volume_causalInterval_timelike x y hxy]
  ring

/-- A translated null cone has zero four-dimensional product volume. -/
theorem volume_nullCone_at (x : Spacetime) :
    volume {y : Spacetime | intervalSq x y = 0} = 0 := by
  have hm : MeasurableSet {y : Spacetime | intervalSq y 0 = 0} :=
    (isClosed_eq (continuous_intervalSq.comp (continuous_id.prodMk continuous_const))
      continuous_const).measurableSet
  have hpre : (fun y : Spacetime => y - x) ⁻¹' {y | intervalSq y 0 = 0} =
      {y | intervalSq x y = 0} := by
    ext y
    simp only [mem_preimage, mem_setOf_eq]
    unfold intervalSq spatialSeparationSq
    simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, neg_sq]
  rw [← hpre, (measurePreserving_sub_right volume x).measure_preimage hm.nullMeasurableSet,
    volume_nullCone_zero]

/-- For almost every future endpoint, the causal inequality is strict.
This justifies use of the timelike volume formula without changing the order. -/
theorem ae_causalFuture_chronological (x : Spacetime) :
    ∀ᵐ y ∂volume, y ∈ causalFuture x → y ∈ chronologicalFuture x ∧ x ≠ y := by
  have hn : ∀ᵐ y ∂volume, intervalSq x y ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using volume_nullCone_at x
  filter_upwards [hn] with y hn hy
  have hs : spatialSeparationSq x y < (y 0 - x 0) ^ 2 := by
    have : intervalSq x y ≠ 0 := hn
    unfold intervalSq at this
    exact lt_of_le_of_ne hy.2 (fun h => this (sub_eq_zero.mpr h.symm))
  have ht : x 0 < y 0 := by
    have hnon : 0 ≤ spatialSeparationSq x y :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hne : x 0 ≠ y 0 := by intro h; rw [h, sub_self, sq] at hs; linarith
    exact lt_of_le_of_ne hy.1 hne
  exact ⟨⟨ht, hs⟩, fun h => (ne_of_lt ht) (congrFun h 0)⟩

end BoundaryDraft
