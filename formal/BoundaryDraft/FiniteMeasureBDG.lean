import BoundaryDraft.PoissonExpectation

/-!
# The four-dimensional BDG observable for a finite intensity measure

Only the coordinate causal order is used here, never a flat interval-volume
formula. The existing generic Poisson law, count law and reduced Mecke proofs
supply the probability input. The original flat sprinkling API is unchanged.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

noncomputable section
namespace BoundaryDraft
namespace FiniteMeasureBDG
open FiniteConfiguration

variable (μ : Measure Spacetime) [IsFiniteMeasure μ]

/-- Poisson probability of an exclusive-interval count, without a pair mask. -/
def layerProbability (k : ℕ) (x y : Spacetime) : ℝ :=
  (poissonPMF (μ (causalIntervalInterior x y)).toNNReal k).toReal

theorem measurable_layerProbability (k : ℕ) :
    Measurable (fun p : Spacetime × Spacetime => layerProbability μ k p.1 p.2) := by
  have hr : Measurable (fun p : Spacetime × Spacetime =>
      (μ (causalIntervalInterior p.1 p.2)).toReal) :=
    (measurable_measure_prodMk_left measurableSet_causalIntervalInterior_joint).ennreal_toReal
  have he (r : ℝ≥0) : (poissonPMF r k).toReal = poissonPMFReal r k :=
    ENNReal.toReal_ofReal poissonPMFReal_nonneg
  simp only [layerProbability, he, poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal]
  exact (hr.neg.exp.mul (hr.pow_const k)).div_const _

omit [IsFiniteMeasure μ] in
theorem layerProbability_nonneg (k : ℕ) (x y : Spacetime) :
    0 ≤ layerProbability μ k x y := ENNReal.toReal_nonneg

omit [IsFiniteMeasure μ] in
theorem layerProbability_le_one (k : ℕ) (x y : Spacetime) :
    layerProbability μ k x y ≤ 1 :=
  (ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one

/-- Ordered strict causal pairs; the diagonal is excluded, not the null cone. -/
def layerMean (k : ℕ) (x y : Spacetime) : ℝ :=
  if y ∈ causalFuture x ∧ x ≠ y then layerProbability μ k x y else 0

theorem measurable_layerMean (k : ℕ) :
    Measurable (fun p : Spacetime × Spacetime => layerMean μ k p.1 p.2) := by
  exact Measurable.ite
    (measurableSet_causalRelation.inter (isClosed_eq continuous_fst continuous_snd).measurableSet.compl)
    (measurable_layerProbability μ k) measurable_const

omit [IsFiniteMeasure μ] in
theorem layerMean_nonneg (k : ℕ) (x y : Spacetime) : 0 ≤ layerMean μ k x y := by
  unfold layerMean
  split_ifs
  · exact layerProbability_nonneg μ k x y
  · exact le_rfl

omit [IsFiniteMeasure μ] in
theorem layerMean_le_one (k : ℕ) (x y : Spacetime) : layerMean μ k x y ≤ 1 := by
  unfold layerMean
  split_ifs
  · exact layerProbability_le_one μ k x y
  · norm_num

theorem integrable_layerMean (k : ℕ) :
    Integrable (fun p : Spacetime × Spacetime => layerMean μ k p.1 p.2) (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_layerMean μ k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (layerMean_nonneg μ k p.1 p.2)]
    exact layerMean_le_one μ k p.1 p.2

theorem integrable_layerMean_section (k : ℕ) (x : Spacetime) :
    Integrable (layerMean μ k x) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_layerMean μ k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖layerMean μ k x y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (layerMean_nonneg μ k x y)]
    exact layerMean_le_one μ k x y

theorem integrable_pairSum (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) : Integrable (intervalPairSum f) (FinitePoisson.law μ) := by
  apply FinitePoisson.integrable_pairSum μ (jointMeasurable_intervalPairTerm f) C
  intro x y c
  split_ifs
  · exact hf _
  · simpa using hC

theorem integrable_layer (k : ℕ) :
    Integrable (fun c => (intervalLayer k c : ℝ)) (FinitePoisson.law μ) := by
  simp only [funext (intervalLayer_cast k)]
  apply integrable_pairSum μ _ 1 (by norm_num)
  intro n
  split_ifs <;> norm_num

/-- The count law and two-point Mecke give every layer expectation. -/
theorem integral_layer (k : ℕ) :
    (∫ c, (intervalLayer k c : ℝ) ∂FinitePoisson.law μ) =
      ∫ x, ∫ y, layerMean μ k x y ∂μ ∂μ := by
  have hc (c : Multiset Spacetime) : ENNReal.ofReal (intervalLayer k c : ℝ) =
      intervalPairSum (fun n => if n = k then (1 : ℝ≥0∞) else 0) c := by
    rw [ENNReal.ofReal_natCast]
    simp only [intervalLayer, intervalPairSum_eq_sum, Nat.cast_multiset_sum,
      Multiset.map_map, Function.comp_def, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun c => Nat.cast_nonneg (intervalLayer k c))
    (integrable_layer μ k).aestronglyMeasurable]
  simp_rw [hc]
  rw [intervalPairSum, FinitePoisson.lintegral_pairSum μ
    (jointMeasurable_intervalPairTerm (fun n => if n = k then (1 : ℝ≥0∞) else 0))]
  have he (x y : Spacetime) :
      (∫⁻ c, if y ∈ causalFuture x ∧ x ≠ y then
        (if intervalCount x y c = k then (1 : ℝ≥0∞) else 0) else 0 ∂FinitePoisson.law μ) =
      ENNReal.ofReal (layerMean μ k x y) := by
    by_cases hxy : y ∈ causalFuture x ∧ x ≠ y
    · simp only [layerMean, layerProbability, hxy.1, hxy.2, ne_eq,
        not_false_eq_true, and_self, if_true]
      have hm := (measurable_intervalCount x y) (measurableSet_singleton k)
      have hi := lintegral_indicator (μ := FinitePoisson.law μ) hm (fun _ => (1 : ℝ≥0∞))
      have hp := FinitePoisson.count_probability μ (measurableSet_causalIntervalInterior x y) k
      rw [ENNReal.ofReal_toReal (ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one _ _) (by simp))), ← hp]
      simpa only [Set.indicator, mem_preimage, mem_singleton_iff, lintegral_const,
        Measure.restrict_apply_univ, one_mul, intervalCount] using hi
    · simp [hxy, layerMean]
  simp_rw [he]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => integral_nonneg (layerMean_nonneg μ k x))
    (integrable_layerMean μ k).integral_prod_left.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_layerMean_section μ k x)
    (Filter.Eventually.of_forall (layerMean_nonneg μ k x))]

omit [IsFiniteMeasure μ] in
/-- Exact signed generating kernel at the actual interval rate. -/
theorem kernel_eq_sum (x y : Spacetime) :
    bdgKernel (μ (causalIntervalInterior x y)).toReal =
      ∑ k ∈ Finset.range 4, bdgLayerWeight k * layerProbability μ k x y := by
  have he (k : ℕ) : layerProbability μ k x y =
      Real.exp (-(μ (causalIntervalInterior x y)).toReal) *
        (μ (causalIntervalInterior x y)).toReal ^ k / k.factorial := by
    unfold layerProbability
    rw [show (poissonPMF (μ (causalIntervalInterior x y)).toNNReal k).toReal =
      poissonPMFReal (μ (causalIntervalInterior x y)).toNNReal k from
        ENNReal.toReal_ofReal poissonPMFReal_nonneg]
    simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal]
  simp_rw [he]
  exact (bdgLayerWeight_kernel _).symm

/-- All pairs, before masking, have an integrable signed kernel. This statement
also permits a different finite endpoint measure. -/
theorem integrable_kernel (ν : Measure Spacetime) [IsFiniteMeasure ν] :
    Integrable (fun p : Spacetime × Spacetime =>
      bdgKernel (μ (causalIntervalInterior p.1 p.2)).toReal) (ν.prod ν) := by
  simp_rw [kernel_eq_sum]
  apply integrable_finset_sum
  intro k _
  apply Integrable.const_mul
  apply (integrable_const (1 : ℝ)).mono' (measurable_layerProbability μ k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (layerProbability_nonneg μ k p.1 p.2)]
    exact layerProbability_le_one μ k p.1 p.2

/-- Every endpoint section is also integrable, not merely almost every one. -/
theorem integrable_kernel_section (ν : Measure Spacetime) [IsFiniteMeasure ν] (x : Spacetime) :
    Integrable (fun y => bdgKernel (μ (causalIntervalInterior x y)).toReal) ν := by
  simp_rw [kernel_eq_sum]
  apply integrable_finset_sum
  intro k _
  apply Integrable.const_mul
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_layerProbability μ k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖layerProbability μ k x y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (layerProbability_nonneg μ k x y)]
    exact layerProbability_le_one μ k x y

/-- Signed ordered-pair kernel, with the selected diagonal removed. -/
def pairMean (x y : Spacetime) : ℝ :=
  if y ∈ causalFuture x ∧ x ≠ y then bdgKernel (μ (causalIntervalInterior x y)).toReal else 0

omit [IsFiniteMeasure μ] in
theorem pairMean_eq_sum (x y : Spacetime) :
    pairMean μ x y = ∑ k ∈ Finset.range 4, bdgLayerWeight k * layerMean μ k x y := by
  by_cases hxy : y ∈ causalFuture x ∧ x ≠ y
  · simpa only [pairMean, layerMean, hxy.1, hxy.2, ne_eq,
      not_false_eq_true, and_self, if_true] using kernel_eq_sum μ x y
  · simp [pairMean, layerMean, hxy]

theorem integrable_pairMean :
    Integrable (fun p : Spacetime × Spacetime => pairMean μ p.1 p.2) (μ.prod μ) := by
  simp only [funext₂ (pairMean_eq_sum μ)]
  exact integrable_finset_sum _ fun k _ => (integrable_layerMean μ k).const_mul _

theorem integrable_pairMean_section (x : Spacetime) : Integrable (pairMean μ x) μ := by
  simp only [funext (pairMean_eq_sum μ x)]
  exact integrable_finset_sum _ fun k _ => (integrable_layerMean_section μ k x).const_mul _

theorem integral_pairSum_bdg :
    (∫ c, intervalPairSum bdgLayerWeight c ∂FinitePoisson.law μ) =
      ∫ x, ∫ y, pairMean μ x y ∂μ ∂μ := by
  have he (c : Multiset Spacetime) : intervalPairSum bdgLayerWeight c =
      ∑ k ∈ Finset.range 4, bdgLayerWeight k * (intervalLayer k c : ℝ) := by
    rw [intervalPairSum_bdgLayerWeight]
    norm_num [Finset.sum_range_succ, bdgLayerWeight]
    ring
  simp_rw [he, pairMean_eq_sum]
  rw [integral_finset_sum _ (fun k _ => (integrable_layer μ k).const_mul _)]
  simp_rw [integral_finset_sum _ (fun k _ =>
    (integrable_layerMean_section μ k _).const_mul _), integral_const_mul]
  rw [integral_finset_sum _ (fun k _ =>
    (integrable_layerMean μ k).integral_prod_left.const_mul _)]
  simp_rw [integral_const_mul, integral_layer]

theorem integral_card :
    (∫ c : Multiset Spacetime, (c.card : ℝ) ∂FinitePoisson.law μ) = (μ univ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (μ := FinitePoisson.law μ)
    (f := fun c : Multiset Spacetime => (c.card : ℝ))
    (Filter.Eventually.of_forall fun c => Nat.cast_nonneg c.card)
    (FinitePoisson.integrable_card μ).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, FinitePoisson.lintegral_card]

theorem integrable_action (ρ : ℝ) :
    Integrable (discreteBDGAction ρ) (FinitePoisson.law μ) := by
  simp only [funext (discreteBDGAction_eq_pairSum ρ)]
  exact ((FinitePoisson.integrable_card μ).sub
    (integrable_pairSum μ bdgLayerWeight 16 (by norm_num) abs_bdgLayerWeight_le)).const_mul _

/-- Both factorial moments enter; no expectation identity is an input. -/
theorem integral_action (ρ : ℝ) :
    (∫ c, discreteBDGAction ρ c ∂FinitePoisson.law μ) = bdgNormalization ρ *
      ((μ univ).toReal - ∫ x, ∫ y, pairMean μ x y ∂μ ∂μ) := by
  simp_rw [discreteBDGAction_eq_pairSum]
  rw [integral_const_mul, integral_sub (FinitePoisson.integrable_card μ)
    (integrable_pairSum μ bdgLayerWeight 16 (by norm_num) abs_bdgLayerWeight_le),
    integral_card, integral_pairSum_bdg]

end FiniteMeasureBDG

/-- Deterministic unweighted observable, defined without a probability law or
continuum limit. The measure already isolates the sprinkled region. -/
def finiteMeasureAction (μ : Measure Spacetime) (ρ : ℝ) : ℝ :=
  (4 / Real.sqrt 6) * Real.sqrt ρ * ((μ univ).toReal -
    ρ * ∫ x, ∫ y in causalFuture x,
      bdgKernel (ρ * (μ (causalIntervalInterior x y)).toReal) ∂μ ∂μ)

/-- The diagonal is null for atomless measures. Null-related pairs are kept. -/
theorem finiteMeasureAction_expectation (μ : Measure Spacetime) [IsFiniteMeasure μ]
    [NoAtoms μ] {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteBDGAction ρ c ∂FinitePoisson.law (ENNReal.ofReal ρ • μ)) =
      finiteMeasureAction μ ρ := by
  letI : IsFiniteMeasure (ENNReal.ofReal ρ • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)⟩
  rw [FiniteMeasureBDG.integral_action]
  have he (x : Spacetime) :
      (∫ y, FiniteMeasureBDG.pairMean (ENNReal.ofReal ρ • μ) x y ∂μ) =
      ∫ y in causalFuture x, bdgKernel (ρ * (μ (causalIntervalInterior x y)).toReal) ∂μ := by
    rw [← integral_indicator (isClosed_causalFuture x).measurableSet]
    apply integral_congr_ae
    have hne : ∀ᵐ y ∂μ, y ≠ x := by simp [ae_iff]
    filter_upwards [hne] with y hy
    have hy' : x ≠ y := Ne.symm hy
    simp only [FiniteMeasureBDG.pairMean, Measure.smul_apply, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ.le]
    by_cases hc : y ∈ causalFuture x <;> simp [hc, hy']
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hρ.le, smul_eq_mul,
    integral_const_mul, he, Measure.smul_apply, ENNReal.toReal_mul]
  rw [show ρ * (μ univ).toReal - ρ * (ρ *
      (∫ x, ∫ y in causalFuture x, bdgKernel (ρ * (μ (causalIntervalInterior x y)).toReal) ∂μ ∂μ)) =
      ρ * ((μ univ).toReal - ρ *
      (∫ x, ∫ y in causalFuture x, bdgKernel (ρ * (μ (causalIntervalInterior x y)).toReal) ∂μ ∂μ)) by ring,
    ← mul_assoc, bdgNormalization_mul_density hρ]
  rfl

end BoundaryDraft
