import BoundaryDraft.DiscreteBDG

/-!
# Exact Poisson averaging of the signed discrete action

This layer uses the actual finite sprinkling probability. No causal convexity
is needed: the interval rate still uses volume restricted to the region.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

noncomputable section
namespace BoundaryDraft
open FiniteConfiguration

/-- Expected layer indicator for an ordered strict causal pair. -/
def poissonLayerMean (S : FiniteSprinkling) (k : ℕ) (x y : Spacetime) : ℝ :=
  if y ∈ causalFuture x ∧ x ≠ y then
    (poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k).toReal else 0

theorem measurable_poissonLayerMean (S : FiniteSprinkling) (k : ℕ) :
    Measurable (fun p : Spacetime × Spacetime => poissonLayerMean S k p.1 p.2) := by
  have hr : Measurable (fun p : Spacetime × Spacetime =>
      (S.intensity (causalIntervalInterior p.1 p.2)).toReal) :=
    (measurable_measure_prodMk_left measurableSet_causalIntervalInterior_joint).ennreal_toReal
  have hp : MeasurableSet {p : Spacetime × Spacetime | p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2} :=
    measurableSet_causalRelation.inter (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  have he (r : ℝ≥0) : (poissonPMF r k).toReal = poissonPMFReal r k :=
    ENNReal.toReal_ofReal poissonPMFReal_nonneg
  simp only [poissonLayerMean, he, poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal]
  exact Measurable.ite hp ((hr.neg.exp.mul (hr.pow_const k)).div_const _) measurable_const

theorem poissonLayerMean_nonneg (S : FiniteSprinkling) (k : ℕ) (x y : Spacetime) :
    0 ≤ poissonLayerMean S k x y := by
  unfold poissonLayerMean
  split_ifs <;> positivity

theorem poissonLayerMean_le_one (S : FiniteSprinkling) (k : ℕ) (x y : Spacetime) :
    poissonLayerMean S k x y ≤ 1 := by
  unfold poissonLayerMean
  split_ifs
  · exact (ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one
  · norm_num

theorem integrable_poissonLayerMean (S : FiniteSprinkling) (k : ℕ) :
    Integrable (fun p : Spacetime × Spacetime => poissonLayerMean S k p.1 p.2)
      (S.intensity.prod S.intensity) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_poissonLayerMean S k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (poissonLayerMean_nonneg S k p.1 p.2)]
    exact poissonLayerMean_le_one S k p.1 p.2

theorem integrable_poissonLayerMean_section (S : FiniteSprinkling) (k : ℕ) (x : Spacetime) :
    Integrable (poissonLayerMean S k x) S.intensity := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_poissonLayerMean S k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖poissonLayerMean S k x y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (poissonLayerMean_nonneg S k x y)]
    exact poissonLayerMean_le_one S k x y

/-- Campbell--Mecke and the proved count law, now as a real expectation.
Absolute integrability on both sides is established separately. -/
theorem integral_intervalLayer (S : FiniteSprinkling) (k : ℕ) :
    (∫ c, (intervalLayer k c : ℝ) ∂S.probability) =
      ∫ x, ∫ y, poissonLayerMean S k x y ∂S.intensity ∂S.intensity := by
  have hc (c : Multiset Spacetime) : ENNReal.ofReal (intervalLayer k c : ℝ) =
      intervalPairSum (fun n => if n = k then (1 : ℝ≥0∞) else 0) c := by
    rw [ENNReal.ofReal_natCast]
    simp only [intervalLayer, intervalPairSum_eq_sum, Nat.cast_multiset_sum,
      Multiset.map_map, Function.comp_def, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun c => Nat.cast_nonneg (intervalLayer k c))
    (integrable_intervalLayer S k).aestronglyMeasurable]
  simp_rw [hc]
  rw [lintegral_intervalLayer]
  have he (x y : Spacetime) : ENNReal.ofReal (poissonLayerMean S k x y) =
      if y ∈ causalFuture x ∧ x ≠ y then
        poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k else 0 := by
    unfold poissonLayerMean
    split_ifs
    · exact ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one _ _) (by simp)))
    · simp
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => integral_nonneg (poissonLayerMean_nonneg S k x))
    (integrable_poissonLayerMean S k).integral_prod_left.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_poissonLayerMean_section S k x)
    (Filter.Eventually.of_forall (poissonLayerMean_nonneg S k x))]
  simp_rw [he]

/-- All four signed layers, with the true restricted interval rate. -/
def poissonBDGMean (S : FiniteSprinkling) (x y : Spacetime) : ℝ :=
  if y ∈ causalFuture x ∧ x ≠ y then
    bdgKernel (S.intensity (causalIntervalInterior x y)).toReal else 0

/-- The factorials come from the Poisson law. No layer or sign is dropped. -/
theorem poissonBDGMean_eq_sum (S : FiniteSprinkling) (x y : Spacetime) :
    poissonBDGMean S x y =
      ∑ k ∈ Finset.range 4, bdgLayerWeight k * poissonLayerMean S k x y := by
  by_cases hxy : y ∈ causalFuture x ∧ x ≠ y
  · simp only [poissonBDGMean, poissonLayerMean, hxy.1, hxy.2, ne_eq,
      not_false_eq_true, and_self, if_true]
    have he (k : ℕ) : (poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k).toReal =
        Real.exp (-(S.intensity (causalIntervalInterior x y)).toReal) *
          (S.intensity (causalIntervalInterior x y)).toReal ^ k / k.factorial := by
      rw [show (poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k).toReal =
        poissonPMFReal (S.intensity (causalIntervalInterior x y)).toNNReal k from
          ENNReal.toReal_ofReal poissonPMFReal_nonneg]
      simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal]
    simp_rw [he]
    exact (bdgLayerWeight_kernel _).symm
  · simp [poissonBDGMean, poissonLayerMean, hxy]

theorem integrable_poissonBDGMean (S : FiniteSprinkling) :
    Integrable (fun p : Spacetime × Spacetime => poissonBDGMean S p.1 p.2)
      (S.intensity.prod S.intensity) := by
  simp only [funext₂ (poissonBDGMean_eq_sum S)]
  exact integrable_finset_sum _ fun k _ => (integrable_poissonLayerMean S k).const_mul _

theorem integrable_poissonBDGMean_section (S : FiniteSprinkling) (x : Spacetime) :
    Integrable (poissonBDGMean S x) S.intensity := by
  simp only [funext (poissonBDGMean_eq_sum S x)]
  exact integrable_finset_sum _ fun k _ => (integrable_poissonLayerMean_section S k x).const_mul _

/-- The exact finite-density signed pair expectation, before geometric
identification of interval volume. -/
theorem integral_intervalPairSum_bdg (S : FiniteSprinkling) :
    (∫ c, intervalPairSum bdgLayerWeight c ∂S.probability) =
      ∫ x, ∫ y, poissonBDGMean S x y ∂S.intensity ∂S.intensity := by
  have he (c : Multiset Spacetime) : intervalPairSum bdgLayerWeight c =
      ∑ k ∈ Finset.range 4, bdgLayerWeight k * (intervalLayer k c : ℝ) := by
    rw [intervalPairSum_bdgLayerWeight]
    norm_num [Finset.sum_range_succ, bdgLayerWeight]
    ring
  simp_rw [he, poissonBDGMean_eq_sum]
  rw [integral_finset_sum _ (fun k _ => (integrable_intervalLayer S k).const_mul _)]
  simp_rw [integral_finset_sum _ (fun k _ =>
    (integrable_poissonLayerMean_section S k _).const_mul _), integral_const_mul]
  rw [integral_finset_sum _ (fun k _ =>
    (integrable_poissonLayerMean S k).integral_prod_left.const_mul _)]
  simp_rw [integral_const_mul, integral_intervalLayer]

/-- First factorial moment in real units. -/
theorem FiniteSprinkling.integral_card (S : FiniteSprinkling) :
    (∫ c : Multiset Spacetime, (c.card : ℝ) ∂S.probability) =
      S.density * (volume S.region).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (μ := S.probability)
    (f := fun c : Multiset Spacetime => (c.card : ℝ))
    (Filter.Eventually.of_forall fun c => Nat.cast_nonneg c.card)
    (FinitePoisson.integrable_card S.intensity).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, FiniteSprinkling.probability, FinitePoisson.lintegral_card]
  rw [S.intensity_toReal MeasurableSet.univ, univ_inter]

/-- Exact expectation of the original discrete action under its actual
probability measure, still using the restricted interval rate. -/
theorem FiniteSprinkling.integral_discreteBDGAction (S : FiniteSprinkling) :
    (∫ c, discreteBDGAction S.density c ∂S.probability) = bdgNormalization S.density *
      (S.density * (volume S.region).toReal -
        ∫ x, ∫ y, poissonBDGMean S x y ∂S.intensity ∂S.intensity) := by
  simp_rw [discreteBDGAction_eq_pairSum]
  rw [integral_const_mul, integral_sub (μ := S.probability)
    (FinitePoisson.integrable_card S.intensity)
    (integrable_intervalPairSum S bdgLayerWeight 16 (by norm_num) abs_bdgLayerWeight_le),
    S.integral_card, integral_intervalPairSum_bdg]

end BoundaryDraft
