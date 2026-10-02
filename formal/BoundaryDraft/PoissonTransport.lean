import BoundaryDraft.FinitePoisson

/-!
# Coordinate transport of the constructed finite Poisson law

This is a stratum-by-stratum consequence of the existing Janossy construction,
not a second probability law or a coupling premise. It is independent of any
order, dimension, action, or volume formula.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical
noncomputable section
namespace BoundaryDraft
namespace FiniteConfiguration
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

omit [MeasurableSpace α] [MeasurableSpace β] in
theorem map_ofTuple (f : α → β) {n : ℕ} (v : Fin n → α) :
    (ofTuple v).map f = ofTuple (f ∘ v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ofTuple_remove v 0, Multiset.map_cons, ofTuple_remove (f ∘ v) 0, ih]
    rfl

theorem measurable_map {f : α → β} (hf : Measurable f) :
    Measurable (Multiset.map f) := by
  apply (measurable_iff _).2
  intro n
  simp only [map_ofTuple]
  exact (measurable_ofTuple n).comp (measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i))

/-- The actual map of locations as a measurable configuration equivalence. -/
def mapEquiv (e : α ≃ᵐ β) : Multiset α ≃ᵐ Multiset β where
  toFun := Multiset.map e
  invFun := Multiset.map e.symm
  left_inv c := by simp [Multiset.map_map]
  right_inv c := by simp [Multiset.map_map]
  measurable_toFun := measurable_map e.measurable
  measurable_invFun := measurable_map e.symm.measurable

end FiniteConfiguration
namespace FinitePoisson
open FiniteConfiguration
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Pushforward of the law along a measure-preserving location equivalence. -/
theorem measurePreserving_mapEquiv (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (he : MeasurePreserving e μ ν) :
    MeasurePreserving (mapEquiv e) (law μ) (law ν) := by
  refine ⟨(mapEquiv e).measurable, ?_⟩
  have hw (n : ℕ) : weight μ n = weight ν n := by
    have hm : μ univ = ν univ := by
      simpa only [preimage_univ] using he.measure_preimage MeasurableSet.univ.nullMeasurableSet
    rw [weight, weight, hm]
  rw [law, Measure.map_sum (mapEquiv e).measurable.aemeasurable, law]
  congr 1
  funext n
  rw [Measure.map_smul, hw, Measure.map_map (mapEquiv e).measurable (measurable_ofTuple n)]
  have hp := measurePreserving_pi (fun _ : Fin n => μ) (fun _ : Fin n => ν) (fun _ => he)
  have hcomp : (mapEquiv e) ∘ (ofTuple : (Fin n → α) → Multiset α) =
      (ofTuple : (Fin n → β) → Multiset β) ∘ (fun v i => e (v i)) := by
    funext v
    exact map_ofTuple e v
  rw [hcomp, ← Measure.map_map (measurable_ofTuple n) hp.measurable, hp.map_eq]

end FinitePoisson
end BoundaryDraft
