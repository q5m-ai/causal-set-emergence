import BoundaryDraft.PoissonCounts

/-!
# Support and absence of duplicate points

The generic finite-intensity construction permits atoms and multiplicities.
Under atomlessness and a measurable diagonal, configurations are almost
surely simple. In particular these hypotheses hold for restricted spacetime
Lebesgue measure.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators ENNReal Classical

noncomputable section

namespace BoundaryDraft
namespace FinitePoisson

open FiniteConfiguration

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- No points occur outside any measurable support of the intensity. -/
theorem ae_supported {s : Set α} (hs : MeasurableSet s) (hμ : μ sᶜ = 0) :
    ∀ᵐ c ∂law μ, ∀ x ∈ c, x ∈ s := by
  have h : ∀ᵐ c ∂law μ, count sᶜ c = 0 := by
    apply (mem_ae_iff_prob_eq_one
      ((measurable_count hs.compl) (measurableSet_singleton 0))).2
    change law μ {c | count sᶜ c = 0} = 1
    rw [count_zero_probability μ hs.compl, hμ]
    simp
  simpa [FiniteConfiguration.count, Multiset.countP_eq_zero] using h

/-- Null intensity gives the empty configuration almost surely. -/
theorem ae_empty (hμ : μ = 0) : ∀ᵐ c ∂law μ, c = 0 := by
  have h := ae_supported μ MeasurableSet.empty (by simp [hμ])
  filter_upwards [h] with c hc
  exact Multiset.eq_zero_of_forall_not_mem (by simpa using hc)

/-- Atomlessness removes repeated locations at every finite stratum. -/
theorem ae_nodup_tuple [NoAtoms μ]
    (hdiag : MeasurableSet {p : α × α | p.1 = p.2}) (n : ℕ) :
    ∀ᵐ v : Fin n → α ∂Measure.pi (fun _ => μ), (ofTuple v).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : MeasurePreserving (fun p : α × (Fin n → α) => Fin.cons p.1 p.2)
        (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) := by
      simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero] using
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hm := (measurableSet_nodup hdiag).preimage (measurable_ofTuple (n + 1))
    rw [← hc.map_eq]
    apply (ae_map_iff hc.measurable.aemeasurable
      (show MeasurableSet {v : Fin (n + 1) → α | (ofTuple v).Nodup} from hm)).2
    apply (ae_prod_iff_ae_ae (hm.preimage hc.measurable)).2
    apply Filter.Eventually.of_forall
    intro x
    have ha : ∀ᵐ v : Fin n → α ∂Measure.pi (fun _ => μ), ∀ i, v i ≠ x :=
      ae_all_iff.2 fun i => Measure.ae_eval_ne (fun _ => μ) i x
    filter_upwards [ih, ha] with v hv ha
    change (ofTuple (Fin.cons x v)).Nodup
    rw [ofTuple_cons, Multiset.nodup_cons]
    exact ⟨by simpa using ha, hv⟩

/-- The actual configuration probability measure is almost surely simple.
No quotient of coincident points is used to hide multiplicities. -/
theorem ae_nodup [NoAtoms μ]
    (hdiag : MeasurableSet {p : α × α | p.1 = p.2}) :
    ∀ᵐ c ∂law μ, c.Nodup := by
  rw [law, Measure.ae_sum_iff]
  intro n
  apply ae_smul_measure
  exact (ae_map_iff (measurable_ofTuple n).aemeasurable (measurableSet_nodup hdiag)).2
    (ae_nodup_tuple μ hdiag n)

end FinitePoisson
end BoundaryDraft
