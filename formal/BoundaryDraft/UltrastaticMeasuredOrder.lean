import BoundaryDraft.SpatialDistance
import BoundaryDraft.MeasuredOrderBDG4
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Ultrastatic measured orders and ambient slab containment

The order is time separation at least the actual spatial distance. Only the
metric laws enter transitivity and antisymmetry. Closedness, interval
measurability, finite atomless product volume and ambient interval containment
are proved, not consequences assumed from intrinsic global hyperbolicity.
-/

open MeasureTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft
namespace Ultrastatic

variable {X : Type*} [TopologicalSpace X] (D : SpatialDistance X)

/-- Closed ultrastatic causal relation, including equality and null separation. -/
def Rel (x y : ℝ × X) : Prop := D.distance x.2 y.2 ≤ y.1 - x.1

theorem time_le {x y : ℝ × X} (h : Rel D x y) : x.1 ≤ y.1 := by
  have hn := D.nonneg x.2 y.2
  dsimp [Rel] at h
  linarith

def causalOrder : PartialOrder (ℝ × X) where
  le := Rel D
  le_refl x := by simp [Rel, D.self]
  le_trans x y z hxy hyz := by
    have ht := D.triangle x.2 y.2 z.2
    dsimp [Rel] at *
    linarith
  le_antisymm x y hxy hyx := by
    have ht : x.1 = y.1 := le_antisymm (time_le D hxy) (time_le D hyx)
    refine Prod.ext ht (D.eq_of_zero _ _ ?_)
    have hn := D.nonneg x.2 y.2
    dsimp [Rel] at hxy
    rw [ht, sub_self] at hxy
    exact le_antisymm hxy hn

theorem isClosed_relation : IsClosed {p : (ℝ × X) × (ℝ × X) | Rel D p.1 p.2} :=
  isClosed_le (D.continuous.comp (continuous_fst.snd.prodMk continuous_snd.snd))
    (continuous_snd.fst.sub continuous_fst.fst)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- The single shared measured-order API instantiated by the actual distance. -/
def measuredOrder : MeasuredOrder (ℝ × X) where
  order := causalOrder D
  measurable_rel := (isClosed_relation D).measurableSet

@[simp] theorem measuredOrder_rel (x y : ℝ × X) :
    (measuredOrder D).Rel x y ↔ Rel D x y := Iff.rfl

/-- Ambient closed interval, prior to endpoint removal or region restriction. -/
def closedInterval (x y : ℝ × X) : Set (ℝ × X) := {z | Rel D x z ∧ Rel D z y}

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem isClosed_interval (x y : ℝ × X) : IsClosed (closedInterval D x y) :=
  ((isClosed_relation D).preimage (continuous_const.prodMk continuous_id)).inter
    ((isClosed_relation D).preimage (continuous_id.prodMk continuous_const))

@[simp] theorem exclusiveInterval_eq (x y : ℝ × X) :
    (measuredOrder D).interval x y = closedInterval D x y \ {x, y} := rfl

/-- Open time slab with its entire spatial factor, not a chartwise substitute. -/
def slab (T : ℝ) : Set (ℝ × X) := Ioo (-T / 2) (T / 2) ×ˢ univ

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem measurable_slab (T : ℝ) : MeasurableSet (slab (X := X) T) :=
  measurableSet_Ioo.prod MeasurableSet.univ

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- Every AMBIENT closed interval stays in the slab for slab endpoints. -/
theorem interval_subset_slab {T : ℝ} {x y : ℝ × X}
    (hx : x ∈ slab T) (hy : y ∈ slab T) : closedInterval D x y ⊆ slab T := by
  intro z hz
  exact ⟨⟨hx.1.1.trans_le (time_le D hz.1), (time_le D hz.2).trans_lt hy.1.2⟩, mem_univ _⟩

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem isCompact_interval [CompactSpace X] (x y : ℝ × X) :
    IsCompact (closedInterval D x y) := by
  apply (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set X))).of_isClosed_subset
    (isClosed_interval D x y)
  intro z hz
  exact ⟨⟨time_le D hz.1, time_le D hz.2⟩, mem_univ _⟩

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem isCompact_closure_slab [CompactSpace X] (T : ℝ) :
    IsCompact (closure (slab (X := X) T)) := by
  apply ((isCompact_Icc : IsCompact (Icc (-T / 2) (T / 2))).prod
    (isCompact_univ : IsCompact (univ : Set X))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ (isClosed_Icc.prod isClosed_univ)
  exact fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, h.2⟩

/-- Restricted product metric volume: Lebesgue time times geometric spatial volume. -/
def slabVolume (ν : Measure X) (T : ℝ) : Measure (ℝ × X) :=
  (volume.prod ν).restrict (slab T)

variable (ν : Measure X) [IsFiniteMeasure ν]

omit [BorelSpace X] in
theorem slabVolume_univ (T : ℝ) :
    slabVolume ν T univ = ENNReal.ofReal T * ν univ := by
  rw [slabVolume, Measure.restrict_apply_univ, slab, Measure.prod_prod, Real.volume_Ioo]
  congr 2
  ring

instance (T : ℝ) : IsFiniteMeasure (slabVolume ν T) := ⟨by
  rw [slabVolume_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν _)⟩

instance (T : ℝ) : NoAtoms (slabVolume ν T) := by
  unfold slabVolume
  infer_instance

omit [IsFiniteMeasure ν] in
/-- Containment, not global hyperbolicity, identifies restricted and ambient
volume. Endpoint removal changes no volume but remains essential for counts. -/
theorem intervalVolume_ambient {T : ℝ} {x y : ℝ × X}
    (hx : x ∈ slab T) (hy : y ∈ slab T) :
    slabVolume ν T ((measuredOrder D).interval x y) = (volume.prod ν) (closedInterval D x y) := by
  rw [slabVolume, Measure.restrict_apply ((measuredOrder D).measurable_interval x y),
    exclusiveInterval_eq,
    inter_eq_left.mpr (diff_subset.trans (interval_subset_slab D hx hy))]
  exact measure_diff_null (((Set.finite_singleton y).insert x).measure_zero _)

/-- The original generic law; no probability distribution is a geometry field. -/
abbrev probability (T ρ : ℝ) : Measure (Multiset (ℝ × X)) :=
  FinitePoisson.law (ENNReal.ofReal ρ • slabVolume ν T)

instance finite_intensity (T ρ : ℝ) : IsFiniteMeasure (ENNReal.ofReal ρ • slabVolume ν T) := ⟨by
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

instance atomless_intensity (T ρ : ℝ) : NoAtoms (ENNReal.ofReal ρ • slabVolume ν T) :=
  ⟨fun x => by simp⟩

instance probability_isProbability (T ρ : ℝ) : IsProbabilityMeasure (probability ν T ρ) :=
  FinitePoisson.isProbabilityMeasure_law _

theorem ae_supported_layers (T ρ : ℝ) :
    ∀ᵐ c ∂probability ν T ρ, (∀ x ∈ c, x ∈ slab T) ∧ c.Nodup ∧
      ∀ k, (measuredOrder D).layer k c = ((measuredOrder D).layerPairs k c).card := by
  apply (measuredOrder D).ae_supported_layers _ (measurable_slab T)
  simp [slabVolume, Measure.restrict_apply (measurable_slab T).compl]

omit [BorelSpace X] in
theorem count_probability (T ρ : ℝ) {A : Set (ℝ × X)} (hA : MeasurableSet A) (k : ℕ) :
    probability ν T ρ {c | FiniteConfiguration.count A c = k} =
      ProbabilityTheory.poissonPMF ((ENNReal.ofReal ρ • slabVolume ν T) A).toNNReal k :=
  FinitePoisson.count_probability _ hA k

/-- Finite-density bridge for every slab width and every positive density. -/
theorem expectation_eq (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, MeasuredOrderBDG4.discreteAction (measuredOrder D) ρ c ∂probability ν T ρ) =
      MeasuredOrderBDG4.action (measuredOrder D) (slabVolume ν T) ρ :=
  MeasuredOrderBDG4.expectation_eq _ _ hρ

end Ultrastatic
end BoundaryDraft
