import BoundaryDraft.TimelikeInterval
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Null-boundary removal

The action uses a strict chronological future tip, whereas the exact interval
calculation is most naturally stated for the closed causal interval.  This
module proves directly in product Lebesgue measure that the intervening null
cone has measure zero, and therefore removes it from every set integral.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

private theorem spatial_sq_boundary_null (R : ℝ) (hR : 0 ≤ R) :
    volume {x : Spatial | ∑ i : Fin 3, x i ^ 2 = R ^ 2} = 0 := by
  have hm : MeasurableSet {x : Spatial | ∑ i : Fin 3, x i ^ 2 = R ^ 2} := by
    apply isClosed_eq ?_ continuous_const |>.measurableSet
    fun_prop
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).measure_preimage
    hm.nullMeasurableSet]
  have he (x : EuclideanSpace ℝ (Fin 3)) :
      ∑ i : Fin 3, ((WithLp.equiv 2 (Fin 3 → ℝ)) x i) ^ 2 = ‖x‖ ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  have hpre : (WithLp.equiv 2 (Fin 3 → ℝ)) ⁻¹'
      {x : Spatial | ∑ i : Fin 3, x i ^ 2 = R ^ 2} = Metric.sphere 0 R := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, Metric.mem_sphere, dist_zero_right]
    rw [he]
    exact sq_eq_sq₀ (norm_nonneg _) hR
  rw [hpre, Measure.addHaar_sphere]

private def spacetimeCoordEquiv : ℝ × Spatial ≃ᵐ Spacetime :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm

private theorem spacetimeCoordEquiv_apply (t : ℝ) (x : Spatial) :
    spacetimeCoordEquiv (t, x) = Fin.cons t x := by
  simp [spacetimeCoordEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

private theorem spacetimeCoordEquiv_measurePreserving :
    MeasurePreserving spacetimeCoordEquiv :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm _

/-- The null cone at the origin has zero four-dimensional product Lebesgue
measure.  The proof is Fubini plus the zero volume of every spatial sphere. -/
theorem volume_nullCone_zero :
    volume {x : Spacetime | intervalSq x 0 = 0} = 0 := by
  let s := {x : Spacetime | intervalSq x 0 = 0}
  have hm : MeasurableSet s := by
    dsimp [s]
    apply isClosed_eq ?_ continuous_const |>.measurableSet
    exact continuous_intervalSq.comp (continuous_id.prodMk continuous_const)
  rw [← spacetimeCoordEquiv_measurePreserving.measure_preimage hm.nullMeasurableSet]
  have hpre : spacetimeCoordEquiv ⁻¹' s =
      {(p : ℝ × Spatial) | ∑ i : Fin 3, p.2 i ^ 2 = p.1 ^ 2} := by
    ext p
    rcases p with ⟨t, x⟩
    simp only [mem_preimage, mem_setOf_eq, s, spacetimeCoordEquiv_apply]
    simp [intervalSq, spatialSeparationSq, Fin.sum_univ_succ]
    constructor <;> intro h <;> linarith
  rw [hpre, Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null
  · apply isClosed_eq ?_ ?_ |>.measurableSet
    · fun_prop
    · fun_prop
  · filter_upwards [] with t
    change volume {x : Spatial | ∑ i : Fin 3, x i ^ 2 = t ^ 2} = 0
    convert spatial_sq_boundary_null |t| (abs_nonneg t) using 1
    rw [sq_abs]

/-- The closed and strict-past versions of a future slice agree almost
Everywhere; their only possible discrepancy lies on the null cone. -/
theorem future_chronologicalPast_ae_causalInterval (x : Spacetime) :
    ((causalFuture x ∩ chronologicalPast 0 : Set Spacetime) =ᶠ[ae volume]
      causalInterval x 0) := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : causalFuture x ∩ chronologicalPast 0 ⊆ causalInterval x 0 := by
      intro y hy
      exact ⟨hy.1, le_of_lt hy.2.1, le_of_lt hy.2.2⟩
    rw [diff_eq_empty.mpr hsub, measure_empty]
  · apply measure_mono_null (t := {y : Spacetime | intervalSq y 0 = 0})
      (fun y hy => ?_) volume_nullCone_zero
    rcases hy with ⟨⟨hyfuture, hypast⟩, hynot⟩
    have hnchron : y ∉ chronologicalPast 0 := fun h => hynot ⟨hyfuture, h⟩
    unfold causalPast causalFuture at hypast
    unfold chronologicalPast chronologicalFuture at hnchron
    have htime : y 0 ≤ 0 := hypast.1
    have hsq : spatialSeparationSq y 0 ≤ (0 - y 0) ^ 2 := hypast.2
    have heq : spatialSeparationSq y 0 = (0 - y 0) ^ 2 := by
      by_cases ht : y 0 < 0
      · have hnlt : ¬spatialSeparationSq y 0 < (0 - y 0) ^ 2 :=
          fun hs => hnchron ⟨ht, hs⟩
        exact le_antisymm hsq (not_lt.mp hnlt)
      · have hy0 : y 0 = 0 := le_antisymm htime (not_lt.mp ht)
        rw [hy0] at hsq ⊢
        exact le_antisymm hsq (by
          have hnonneg : 0 ≤ spatialSeparationSq y 0 := by
            unfold spatialSeparationSq
            exact Finset.sum_nonneg fun i _ => sq_nonneg _
          simpa using hnonneg)
    change intervalSq y 0 = 0
    unfold intervalSq
    rw [heq]
    simp

/-- Removing the future null boundary does not change a set integral. -/
theorem integral_future_chronologicalPast_eq_causalInterval
    (f : Spacetime → ℝ) (x : Spacetime) :
    (∫ y in causalFuture x ∩ chronologicalPast 0, f y) =
      ∫ y in causalInterval x 0, f y :=
  setIntegral_congr_set (future_chronologicalPast_ae_causalInterval x)

end BoundaryDraft
