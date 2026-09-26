import BoundaryDraft.PoissonSimplicity
import BoundaryDraft.PoissonDisjoint
import BoundaryDraft.PoissonIntegration
import BoundaryDraft.NullGeometry

/-!
# Finite-volume spacetime sprinklings and causal interval counts

A sprinkling specifies only a measurable region of finite Lebesgue volume and
a positive density. Its probability measure is constructed, not supplied as a
field. The interior below is the order-theoretic interval with its two
endpoints removed; null-related intermediate points are not silently dropped.
No discrete BDG action or continuum expectation bridge is defined here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Classical

noncomputable section

namespace BoundaryDraft

open FiniteConfiguration

/-- Geometric and density input, with no probabilistic conclusions as fields. -/
structure FiniteSprinkling where
  region : Set Spacetime
  measurable_region : MeasurableSet region
  finite_volume : volume region < ∞
  density : ℝ
  density_pos : 0 < density

namespace FiniteSprinkling

/-- Intensity: density times restricted product Lebesgue measure. -/
def intensity (S : FiniteSprinkling) : Measure Spacetime :=
  ENNReal.ofReal S.density • volume.restrict S.region

instance (S : FiniteSprinkling) : IsFiniteMeasure S.intensity := by
  constructor
  simp only [intensity, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top S.finite_volume

instance (S : FiniteSprinkling) : NoAtoms S.intensity := by
  constructor
  intro x
  simp [intensity]

/-- Probability on unordered finite point configurations. -/
def probability (S : FiniteSprinkling) : Measure (Multiset Spacetime) :=
  FinitePoisson.law S.intensity

instance (S : FiniteSprinkling) : IsProbabilityMeasure S.probability :=
  FinitePoisson.isProbabilityMeasure_law S.intensity

theorem intensity_apply (S : FiniteSprinkling) {A : Set Spacetime} (hA : MeasurableSet A) :
    S.intensity A = ENNReal.ofReal S.density * volume (A ∩ S.region) := by
  simp [intensity, Measure.restrict_apply hA]

theorem intensity_apply_of_subset (S : FiniteSprinkling) {A : Set Spacetime}
    (hA : MeasurableSet A) (hAM : A ⊆ S.region) :
    S.intensity A = ENNReal.ofReal S.density * volume A := by
  rw [S.intensity_apply hA, inter_eq_left.2 hAM]

/-- In real units the rate is exactly density times the volume within the
sprinkled region. Finiteness justifies both conversions from extended reals. -/
theorem intensity_toReal (S : FiniteSprinkling) {A : Set Spacetime} (hA : MeasurableSet A) :
    (S.intensity A).toReal = S.density * (volume (A ∩ S.region)).toReal := by
  rw [S.intensity_apply hA, ENNReal.toReal_mul, ENNReal.toReal_ofReal S.density_pos.le]

theorem count_probability (S : FiniteSprinkling) {A : Set Spacetime}
    (hA : MeasurableSet A) (k : ℕ) :
    S.probability {c | count A c = k} =
      ENNReal.ofReal (Real.exp (-(S.density * (volume (A ∩ S.region)).toReal)) *
        (S.density * (volume (A ∩ S.region)).toReal) ^ k / k.factorial) := by
  rw [probability, FinitePoisson.count_probability S.intensity hA]
  change ENNReal.ofReal (poissonPMFReal (S.intensity A).toNNReal k) = _
  simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal, S.intensity_toReal hA]

theorem ae_supported (S : FiniteSprinkling) :
    ∀ᵐ c ∂S.probability, ∀ x ∈ c, x ∈ S.region := by
  apply FinitePoisson.ae_supported S.intensity S.measurable_region
  rw [S.intensity_apply S.measurable_region.compl]
  simp

theorem ae_nodup (S : FiniteSprinkling) : ∀ᵐ c ∂S.probability, c.Nodup :=
  FinitePoisson.ae_nodup S.intensity (isClosed_eq continuous_fst continuous_snd).measurableSet

/-- Zero-volume regions, not only the empty set, have no points almost surely. -/
theorem ae_empty_of_volume_zero (S : FiniteSprinkling) (hS : volume S.region = 0) :
    ∀ᵐ c ∂S.probability, c = 0 := by
  apply FinitePoisson.ae_empty S.intensity
  simp [intensity, Measure.restrict_eq_zero.mpr hS]

end FiniteSprinkling

/-- Strict order interval: the existing closed causal interval, with both
endpoints excluded. This is not a replacement by the chronological interval. -/
def causalIntervalInterior (x y : Spacetime) : Set Spacetime :=
  causalInterval x y \ {x, y}

@[simp] theorem left_not_mem_causalIntervalInterior (x y : Spacetime) :
    x ∉ causalIntervalInterior x y := by simp [causalIntervalInterior]

@[simp] theorem right_not_mem_causalIntervalInterior (x y : Spacetime) :
    y ∉ causalIntervalInterior x y := by simp [causalIntervalInterior]

theorem measurableSet_causalRelation :
    MeasurableSet {p : Spacetime × Spacetime | p.2 ∈ causalFuture p.1} := by
  apply IsClosed.measurableSet
  apply IsClosed.inter
  · exact isClosed_le ((continuous_apply 0).comp continuous_fst)
      ((continuous_apply 0).comp continuous_snd)
  · apply isClosed_le continuous_spatialSeparationSq
    fun_prop

theorem measurableSet_causalIntervalInterior_joint :
    MeasurableSet {p : (Spacetime × Spacetime) × Spacetime |
      p.2 ∈ causalIntervalInterior p.1.1 p.1.2} := by
  have h₁ := measurableSet_causalRelation.preimage
    (measurable_fst.fst.prodMk measurable_snd :
      Measurable (fun p : (Spacetime × Spacetime) × Spacetime => (p.1.1, p.2)))
  have h₂ := measurableSet_causalRelation.preimage
    (measurable_snd.prodMk measurable_fst.snd :
      Measurable (fun p : (Spacetime × Spacetime) × Spacetime => (p.2, p.1.2)))
  have he : MeasurableSet {p : (Spacetime × Spacetime) × Spacetime |
      p.2 = p.1.1 ∨ p.2 = p.1.2} :=
    (isClosed_eq continuous_snd continuous_fst.fst).measurableSet.union
      (isClosed_eq continuous_snd continuous_fst.snd).measurableSet
  exact (h₁.inter h₂).diff he

theorem measurableSet_causalIntervalInterior (x y : Spacetime) :
    MeasurableSet (causalIntervalInterior x y) :=
  measurableSet_causalIntervalInterior_joint.preimage
    (show Measurable (fun z : Spacetime => ((x, y), z)) from
      measurable_const.prodMk measurable_id)

/-- Measurable, finite order-interval count. -/
def intervalCount (x y : Spacetime) : Multiset Spacetime → ℕ :=
  count (causalIntervalInterior x y)

theorem jointMeasurable_intervalCount :
    JointMeasurable (fun p : Spacetime × Spacetime => intervalCount p.1 p.2) :=
  jointMeasurable_count measurableSet_causalIntervalInterior_joint

@[measurability] theorem measurable_intervalCount (x y : Spacetime) :
    Measurable (intervalCount x y) :=
  measurable_count (measurableSet_causalIntervalInterior x y)

/-- Reinserting the two selected endpoints does not alter their interior
count, even on a configuration with multiplicities. -/
@[simp] theorem intervalCount_insert_endpoints (x y : Spacetime) (c : Multiset Spacetime) :
    intervalCount x y (x ::ₘ y ::ₘ c) = intervalCount x y c := by
  simp [intervalCount]

theorem intervalCount_probability (S : FiniteSprinkling) (x y : Spacetime) (k : ℕ) :
    S.probability {c | intervalCount x y c = k} =
      poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k :=
  FinitePoisson.count_probability S.intensity (measurableSet_causalIntervalInterior x y) k

/-- Sum an interval-count observable over ordered strictly causal pairs.
The residual configuration has both selected occurrences removed. -/
def intervalPairSum {E : Type*} [AddCommMonoid E] (f : ℕ → E) : Multiset Spacetime → E :=
  pairSum fun x y c => if y ∈ causalFuture x ∧ x ≠ y then f (intervalCount x y c) else 0

theorem jointMeasurable_intervalPairTerm {E : Type*} [MeasurableSpace E] [Zero E] (f : ℕ → E) :
    JointMeasurable (fun p : Spacetime × Spacetime =>
      fun c => if p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2 then f (intervalCount p.1 p.2 c) else 0) := by
  intro n
  have hp : MeasurableSet {p : Spacetime × Spacetime | p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2} :=
    measurableSet_causalRelation.inter (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  exact Measurable.ite (hp.preimage measurable_fst)
    ((measurable_of_countable f).comp (jointMeasurable_intervalCount n)) measurable_const

@[measurability] theorem measurable_intervalPairSum {E : Type*} [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E] (f : ℕ → E) : Measurable (intervalPairSum f) :=
  measurable_pairSum (jointMeasurable_intervalPairTerm f)

/-- Exact interval-layer averaging, derived from two-point Mecke and the
subset count law. The rate is the volume *inside the sprinkled region*;
causal convexity and a Minkowski volume formula are separate downstream work. -/
theorem lintegral_intervalLayer (S : FiniteSprinkling) (k : ℕ) :
    (∫⁻ c, intervalPairSum (fun n => if n = k then (1 : ℝ≥0∞) else 0) c ∂S.probability) =
      ∫⁻ x, ∫⁻ y, if y ∈ causalFuture x ∧ x ≠ y then
        poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k else 0
        ∂S.intensity ∂S.intensity := by
  rw [intervalPairSum, FiniteSprinkling.probability,
    FinitePoisson.lintegral_pairSum S.intensity
      (jointMeasurable_intervalPairTerm (fun n => if n = k then (1 : ℝ≥0∞) else 0))]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  by_cases hxy : y ∈ causalFuture x ∧ x ≠ y
  · simp only [hxy.1, hxy.2, ne_eq, not_false_eq_true, and_self, if_true]
    rw [← intervalCount_probability S x y k]
    have hm := (measurable_intervalCount x y) (measurableSet_singleton k)
    have h := lintegral_indicator (μ := S.probability) hm (fun _ => (1 : ℝ≥0∞))
    simpa only [Set.indicator, mem_preimage, mem_singleton_iff, lintegral_const,
      Measure.restrict_apply_univ, one_mul, FiniteSprinkling.probability] using h
  · simp [hxy]

/-- Bounded signed interval weights are absolutely integrable. This applies
to any finite set of layer coefficients, without defining the BDG action. -/
theorem integrable_intervalPairSum (S : FiniteSprinkling) (f : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    Integrable (intervalPairSum f) S.probability := by
  apply FinitePoisson.integrable_pairSum S.intensity (jointMeasurable_intervalPairTerm f) C
  intro x y c
  split_ifs
  · exact hf _
  · simpa using hC

end BoundaryDraft
