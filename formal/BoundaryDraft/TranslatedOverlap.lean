import BoundaryDraft.SpacetimeIntegration
import BoundaryDraft.NullGeometry
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exact translated overlap

The weighted-volume/volume-of-realisation representation is prior work of
Dowker–Liu–Lloyd-Jones, §2.6. Here it is derived for the original signed action
on bounded measurable sets. No causal convexity or overlap regularity is used.
The probabilistic interpretation, unlike this deterministic identity, requires
the separate causal-convexity hypotheses of `ExpectationBridge`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Classical

noncomputable section
namespace BoundaryDraft

/-- Four-dimensional translated overlap, independently of the action. -/
def translatedOverlap (M : Set Spacetime) (z : Spacetime) : ℝ :=
  ∫ x in M, M.indicator (fun _ => (1 : ℝ)) (x + z)

theorem translatedOverlap_eq_indicator (M : Set Spacetime) (hM : MeasurableSet M)
    (z : Spacetime) :
    translatedOverlap M z = ∫ x, M.indicator (fun _ => (1 : ℝ)) x *
      M.indicator (fun _ => (1 : ℝ)) (x + z) := by
  rw [translatedOverlap, ← integral_indicator hM]
  congr 1
  ext x
  by_cases hx : x ∈ M <;> simp [hx]

theorem measurable_translatedOverlap {M : Set Spacetime} (hM : MeasurableSet M) :
    Measurable (translatedOverlap M) := by
  have h : StronglyMeasurable (fun p : Spacetime × Spacetime =>
      M.indicator (fun _ => (1 : ℝ)) (p.2 + p.1)) :=
    ((measurable_const.indicator hM).comp (measurable_snd.add measurable_fst)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume.restrict M)).measurable

theorem translatedOverlap_nonneg (M : Set Spacetime) (z : Spacetime) :
    0 ≤ translatedOverlap M z :=
  integral_nonneg fun _ => indicator_nonneg (fun _ _ => zero_le_one) _

theorem integrable_overlap_fibre {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (z : Spacetime) :
    IntegrableOn (fun x => M.indicator (fun _ => (1 : ℝ)) (x + z)) M := by
  haveI : IsFiniteMeasure (volume.restrict M) := ⟨by
    simpa using hb.measure_lt_top⟩
  apply (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((measurable_const.indicator hm).comp (measurable_id.add_const z)).aestronglyMeasurable
  · by_cases hx : x + z ∈ M <;> simp [hx]

theorem translatedOverlap_le_volume {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (z : Spacetime) :
    translatedOverlap M z ≤ volume.real M := by
  haveI : IsFiniteMeasure (volume.restrict M) := ⟨by simpa using hb.measure_lt_top⟩
  calc
    _ ≤ ∫ _x in M, (1 : ℝ) := integral_mono (integrable_overlap_fibre hm hb z)
      (integrable_const _) (fun x => by by_cases hx : x + z ∈ M <;> simp [hx])
    _ = _ := by simp

/-- A support bound valid also for empty and nonempty null-volume regions. -/
theorem translatedOverlap_eq_zero_of_diam_lt {M : Set Spacetime}
    (hb : Bornology.IsBounded M) {z : Spacetime} (hz : Metric.diam M < ‖z‖) :
    translatedOverlap M z = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  apply indicator_of_not_mem
  intro hxz
  have hd := Metric.dist_le_diam_of_mem hb hxz hx
  rw [dist_eq_norm, add_sub_cancel_left] at hd
  exact (not_le_of_gt hz) hd

theorem hasCompactSupport_translatedOverlap {M : Set Spacetime}
    (hb : Bornology.IsBounded M) : HasCompactSupport (translatedOverlap M) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Spacetime) (Metric.diam M))
  intro z hz
  apply translatedOverlap_eq_zero_of_diam_lt hb
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz

theorem translatedOverlap_zero_of_volume_zero {M : Set Spacetime}
    (hM : volume M = 0) (z : Spacetime) : translatedOverlap M z = 0 := by
  simp [translatedOverlap, Measure.restrict_eq_zero.mpr hM]

@[simp] theorem translatedOverlap_empty (z : Spacetime) : translatedOverlap ∅ z = 0 := by
  simp [translatedOverlap]

/-- Translation preserves the full causal relation, including its null boundary. -/
theorem add_mem_causalFuture_iff (x z : Spacetime) :
    x + z ∈ causalFuture x ↔ z ∈ causalFuture 0 := by
  simp [causalFuture, spatialSeparationSq]

theorem intervalSq_add_right (x z : Spacetime) : intervalSq x (x + z) = intervalSq 0 z := by
  simp [intervalSq, spatialSeparationSq]

/-- The endpoint/displacement shear preserves product Lebesgue measure. -/
theorem displacement_measurePreserving :
    MeasurePreserving (fun p : Spacetime × Spacetime => (p.1, p.2 - p.1)) := by
  simpa only [Measure.volume_eq_prod] using
    (measurePreserving_prod_sub (volume : Measure Spacetime) volume)

/-- The block matrix of `(x,y) ↦ (x,y-x)`; spacetime uses `n = Fin 4`. -/
def displacementMatrix (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix (n ⊕ n) (n ⊕ n) ℝ := Matrix.fromBlocks 1 0 (-1) 1

theorem displacementMatrix_apply (x y : Spacetime) :
    (displacementMatrix (Fin 4)).mulVec (Sum.elim x y) = Sum.elim x (y - x) := by
  ext i
  cases i <;> simp [displacementMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, sub_eq_add_neg, add_comm]

theorem det_displacementMatrix (n : Type*) [Fintype n] [DecidableEq n] :
    (displacementMatrix n).det = 1 := by
  rw [displacementMatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

private def pairSet (M : Set Spacetime) : Set (Spacetime × Spacetime) :=
  {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ causalFuture p.1}

private theorem measurableSet_pairSet {M : Set Spacetime} (hM : MeasurableSet M) :
    MeasurableSet (pairSet M) := by
  have hc : MeasurableSet {p : Spacetime × Spacetime | p.2 ∈ causalFuture p.1} := by
    apply MeasurableSet.inter
    · exact (isClosed_le
        (show Continuous (fun p : Spacetime × Spacetime => p.1 0) by fun_prop)
        (show Continuous (fun p : Spacetime × Spacetime => p.2 0) by fun_prop)).measurableSet
    · exact (isClosed_le continuous_spatialSeparationSq (by fun_prop)).measurableSet
  exact (hM.preimage measurable_fst).inter ((hM.preimage measurable_snd).inter hc)

/-- Compact domination of the signed integrand precedes the shear and Fubini. -/
private theorem integrable_pair {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {f : Spacetime → ℝ} (hf : Continuous f) :
    Integrable ((pairSet M).indicator (fun p => f (p.2 - p.1))) := by
  apply (integrable_indicator_iff (measurableSet_pairSet hm)).mpr
  exact ((hf.comp (continuous_snd.sub continuous_fst)).continuousOn.integrableOn_compact
    (hb.isCompact_closure.prod hb.isCompact_closure)).mono_set
    (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩)

private theorem pair_shear (M : Set Spacetime) (f : Spacetime → ℝ)
    (x z : Spacetime) :
    (pairSet M).indicator (fun p => f (p.2 - p.1)) (x, x + z) =
      (causalFuture 0).indicator f z *
        M.indicator (fun x => M.indicator (fun _ => (1 : ℝ)) (x + z)) x := by
  classical
  by_cases hx : x ∈ M <;> by_cases hy : x + z ∈ M <;>
    by_cases hz : z ∈ causalFuture 0 <;>
    simp [pairSet, hx, hy, hz, add_mem_causalFuture_iff]

private theorem integral_pair_fibre (M : Set Spacetime) (hm : MeasurableSet M)
    (f : Spacetime → ℝ) (x : Spacetime) :
    (∫ y, (pairSet M).indicator (fun p => f (p.2 - p.1)) (x, y)) =
      M.indicator (fun x => ∫ y in M ∩ causalFuture x, f (y - x)) x := by
  classical
  by_cases hx : x ∈ M
  · rw [indicator_of_mem hx, ← integral_indicator (hm.inter (isClosed_causalFuture x).measurableSet)]
    congr 1
    ext y
    simp only [Set.indicator, pairSet]
    simp only [mem_setOf_eq, mem_inter_iff, hx, true_and]
  · simp [pairSet, hx, Set.indicator]

/-- Signed Fubini after the measure-preserving shear. This is an exact identity
for arbitrary continuous displacement weights, not a radial approximation. -/
theorem integral_causalPair_eq_overlap {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (f : Spacetime → ℝ) (hf : Continuous f) :
    (∫ x in M, ∫ y in M ∩ causalFuture x, f (y - x)) =
      ∫ z in causalFuture 0, f z * translatedOverlap M z := by
  let F := (pairSet M).indicator (fun p => f (p.2 - p.1))
  have hi := integrable_pair hm hb hf
  have hmp := measurePreserving_prod_add (volume : Measure Spacetime) volume
  have his := (hmp.integrable_comp_emb
    (MeasurableEquiv.shearAddRight Spacetime).measurableEmbedding).mpr
      (by simpa only [← Measure.volume_eq_prod] using hi)
  calc
    _ = ∫ p, F p := by
      rw [Measure.volume_eq_prod, integral_prod _ (by simpa only [← Measure.volume_eq_prod] using hi)]
      simp_rw [F, integral_pair_fibre M hm f]
      rw [integral_indicator hm]
    _ = ∫ p : Spacetime × Spacetime, F (p.1, p.1 + p.2) := by
      rw [Measure.volume_eq_prod]
      exact (hmp.integral_comp (MeasurableEquiv.shearAddRight Spacetime).measurableEmbedding F).symm
    _ = ∫ z, (causalFuture 0).indicator f z * translatedOverlap M z := by
      rw [Measure.volume_eq_prod]
      calc
        _ = ∫ z, ∫ x, F (x, x + z) := integral_prod_symm _ his
        _ = _ := by
          simp_rw [F, pair_shear, integral_const_mul, integral_indicator hm, translatedOverlap]
    _ = _ := by
      simp_rw [← indicator_mul_left]
      exact integral_indicator (isClosed_causalFuture 0).measurableSet

/-- Absolute integrability is transported through the same shear, before
performing the signed integral or any cancellation. -/
theorem integrableOn_overlap_weight {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (f : Spacetime → ℝ) (hf : Continuous f) :
    IntegrableOn (fun z => f z * translatedOverlap M z) (causalFuture 0) := by
  have hi := integrable_pair hm hb hf
  have hmp := measurePreserving_prod_add (volume : Measure Spacetime) volume
  have his := (hmp.integrable_comp_emb
    (MeasurableEquiv.shearAddRight Spacetime).measurableEmbedding).mpr
      (by simpa only [← Measure.volume_eq_prod] using hi)
  have hj := his.integral_prod_right
  change Integrable (fun z => ∫ x,
    (pairSet M).indicator (fun p => f (p.2 - p.1)) (x, x + z)) at hj
  simp_rw [pair_shear, integral_const_mul, integral_indicator hm] at hj
  change Integrable (fun z => (causalFuture 0).indicator f z * translatedOverlap M z) at hj
  simp_rw [← indicator_mul_left] at hj
  exact (integrable_indicator_iff (isClosed_causalFuture 0).measurableSet).mp hj

/-- Exact finite-density reduction of the unchanged action. The outer square
root and inner density are both retained; the entire signed BDG kernel remains. -/
theorem continuumMean_eq_translatedOverlap {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) :
    continuumMean ρ M = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real M - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) * translatedOverlap M z) := by
  have he (x y : Spacetime) : intervalSq 0 (y - x) = intervalSq x y := by
    simp [intervalSq, spatialSeparationSq]
  have hc : Continuous (fun z => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2)) := by
    unfold bdgKernel bdgPolynomial intervalSq spatialSeparationSq
    fun_prop
  have h := integral_causalPair_eq_overlap hm hb _ hc
  simp_rw [he] at h
  simp only [continuumMean, integral_const, measureReal_restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul, mul_one]
  rw [h]

end BoundaryDraft
