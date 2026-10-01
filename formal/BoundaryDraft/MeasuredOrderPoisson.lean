import BoundaryDraft.MeasuredOrder
import BoundaryDraft.PoissonCounts
import BoundaryDraft.PoissonIntegration
import BoundaryDraft.PoissonSimplicity

/-!
# Finite-measure order-layer expectations

Only a measurable order and a finite measure are used. Reduced Mecke, count
laws and factorial moments are reused from the generic probability API.
Atomlessness is needed for simplicity, not for the layer identity itself.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace BoundaryDraft
namespace MeasuredOrder
open FiniteConfiguration
variable {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α)
variable (μ : Measure α) [IsFiniteMeasure μ]

def layerProbability (k : ℕ) (x y : α) : ℝ :=
  (poissonPMF (μ (O.interval x y)).toNNReal k).toReal

omit [IsFiniteMeasure μ] in
theorem layerProbability_eq (k : ℕ) (x y : α) :
    O.layerProbability μ k x y = Real.exp (-(μ (O.interval x y)).toReal) *
      (μ (O.interval x y)).toReal ^ k / k.factorial := by
  unfold layerProbability
  rw [show (poissonPMF (μ (O.interval x y)).toNNReal k).toReal =
    poissonPMFReal (μ (O.interval x y)).toNNReal k from
      ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal]

theorem measurable_layerProbability (k : ℕ) :
    Measurable (fun p : α × α => O.layerProbability μ k p.1 p.2) := by
  have hr : Measurable (fun p : α × α => (μ (O.interval p.1 p.2)).toReal) :=
    (measurable_measure_prodMk_left O.measurable_interval_joint).ennreal_toReal
  simp only [funext₂ (O.layerProbability_eq μ k)]
  exact (hr.neg.exp.mul (hr.pow_const k)).div_const _

omit [IsFiniteMeasure μ] in
theorem layerProbability_nonneg (k : ℕ) (x y : α) :
    0 ≤ O.layerProbability μ k x y := ENNReal.toReal_nonneg

omit [IsFiniteMeasure μ] in
theorem layerProbability_le_one (k : ℕ) (x y : α) : O.layerProbability μ k x y ≤ 1 :=
  (ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one

/-- Strict pairs exclude the diagonal but retain null-related endpoints. -/
def layerMean (k : ℕ) (x y : α) : ℝ :=
  if O.Rel x y ∧ x ≠ y then O.layerProbability μ k x y else 0

theorem measurable_layerMean (k : ℕ) :
    Measurable (fun p : α × α => O.layerMean μ k p.1 p.2) :=
  Measurable.ite (O.measurable_rel.inter O.measurable_diagonal.compl)
    (O.measurable_layerProbability μ k) measurable_const

omit [IsFiniteMeasure μ] in
theorem layerMean_nonneg (k : ℕ) (x y : α) : 0 ≤ O.layerMean μ k x y := by
  unfold layerMean
  split_ifs
  · exact O.layerProbability_nonneg μ k x y
  · exact le_rfl

omit [IsFiniteMeasure μ] in
theorem layerMean_le_one (k : ℕ) (x y : α) : O.layerMean μ k x y ≤ 1 := by
  unfold layerMean
  split_ifs
  · exact O.layerProbability_le_one μ k x y
  · norm_num

theorem integrable_layerMean (k : ℕ) :
    Integrable (fun p : α × α => O.layerMean μ k p.1 p.2) (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono' (O.measurable_layerMean μ k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (O.layerMean_nonneg μ k p.1 p.2)]
    exact O.layerMean_le_one μ k p.1 p.2

theorem integrable_layerMean_section (k : ℕ) (x : α) :
    Integrable (O.layerMean μ k x) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((O.measurable_layerMean μ k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖O.layerMean μ k x y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (O.layerMean_nonneg μ k x y)]
    exact O.layerMean_le_one μ k x y

/-- Absolute integrability from the second factorial moment, with no bound on
configuration cardinality. -/
theorem integrable_layer (k : ℕ) :
    Integrable (fun c => (O.layer k c : ℝ)) (FinitePoisson.law μ) := by
  simp only [funext (O.layer_cast k)]
  apply FinitePoisson.integrable_pairSum μ
    (O.jointMeasurable_pairTerm (fun n => if n = k then (1 : ℝ) else 0)) 1
  intro x y c
  dsimp only
  split_ifs <;> norm_num

/-- Exact finite-measure layer identity, with the ACTUAL exclusive-interval
measure. No causal-convexity or flat-volume substitution is made. -/
theorem integral_layer (k : ℕ) :
    (∫ c, (O.layer k c : ℝ) ∂FinitePoisson.law μ) =
      ∫ x, ∫ y, O.layerMean μ k x y ∂μ ∂μ := by
  have hc (c : Multiset α) : ENNReal.ofReal (O.layer k c : ℝ) =
      O.intervalPairSum (fun n => if n = k then (1 : ℝ≥0∞) else 0) c := by
    rw [ENNReal.ofReal_natCast]
    simp only [layer, intervalPairSum_eq_sum, Nat.cast_multiset_sum,
      Multiset.map_map, Function.comp_def, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun c => Nat.cast_nonneg (O.layer k c))
    (O.integrable_layer μ k).aestronglyMeasurable]
  simp_rw [hc]
  rw [intervalPairSum, FinitePoisson.lintegral_pairSum μ
    (O.jointMeasurable_pairTerm (fun n => if n = k then (1 : ℝ≥0∞) else 0))]
  have he (x y : α) :
      (∫⁻ c, if O.Rel x y ∧ x ≠ y then
        (if O.intervalCount x y c = k then (1 : ℝ≥0∞) else 0) else 0 ∂FinitePoisson.law μ) =
      ENNReal.ofReal (O.layerMean μ k x y) := by
    by_cases hxy : O.Rel x y ∧ x ≠ y
    · simp only [layerMean, layerProbability, hxy.1, hxy.2, ne_eq,
        not_false_eq_true, and_self, if_true]
      have hm := (O.measurable_intervalCount x y) (measurableSet_singleton k)
      have hi := lintegral_indicator (μ := FinitePoisson.law μ) hm (fun _ => (1 : ℝ≥0∞))
      have hp := FinitePoisson.count_probability μ (O.measurable_interval x y) k
      rw [ENNReal.ofReal_toReal (ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one _ _) (by simp))), ← hp]
      simpa only [Set.indicator, mem_preimage, mem_singleton_iff, lintegral_const,
        Measure.restrict_apply_univ, one_mul, intervalCount] using hi
    · simp [hxy, layerMean]
  simp_rw [he]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => integral_nonneg (O.layerMean_nonneg μ k x))
    (O.integrable_layerMean μ k).integral_prod_left.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [ofReal_integral_eq_lintegral_ofReal (O.integrable_layerMean_section μ k x)
    (Filter.Eventually.of_forall (O.layerMean_nonneg μ k x))]

/-- The finite-order interpretation holds almost surely for any finite
atomless intensity supported in the requested measurable set. -/
theorem ae_supported_layers [NoAtoms μ] {M : Set α} (hM : MeasurableSet M) (hμ : μ Mᶜ = 0) :
    ∀ᵐ c ∂FinitePoisson.law μ, (∀ x ∈ c, x ∈ M) ∧ c.Nodup ∧
      ∀ k, O.layer k c = (O.layerPairs k c).card := by
  filter_upwards [FinitePoisson.ae_supported μ hM hμ,
    FinitePoisson.ae_nodup μ O.measurable_diagonal] with c hs hc
  exact ⟨hs, hc, O.layer_eq_card hc⟩

end MeasuredOrder
end BoundaryDraft
