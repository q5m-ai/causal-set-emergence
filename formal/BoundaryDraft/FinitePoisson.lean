import BoundaryDraft.FiniteConfiguration
import Mathlib.Probability.Distributions.Poisson

/-!
# Finite Poisson configuration measure and reduced Campbell--Mecke identity

The Janossy construction uses unnormalised finite product measures. In
particular it requires no choice of a uniform point in an empty region.
No count or expectation law is a field of the construction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

noncomputable section

namespace BoundaryDraft
namespace FinitePoisson

open FiniteConfiguration

variable {α β : Type*} [MeasurableSpace α]

/-- The Janossy coefficient. The intensity itself is carried by the product
measure, rather than by a normalised location distribution. -/
def weight (μ : Measure α) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(μ univ).toReal) / n.factorial)

/-- A genuine measure on unordered finite configurations. All probability
results below require a finite intensity measure. -/
def law (μ : Measure α) : Measure (Multiset α) :=
  Measure.sum fun n : ℕ => weight μ n •
    Measure.map (ofTuple : (Fin n → α) → Multiset α) (Measure.pi fun _ => μ)

variable (μ : Measure α) [IsFiniteMeasure μ]

theorem weight_mul_pow (n : ℕ) :
    weight μ n * μ univ ^ n = poissonPMF (μ univ).toNNReal n := by
  change _ = ENNReal.ofReal (poissonPMFReal (μ univ).toNNReal n)
  rw [weight, ← ENNReal.ofReal_toReal (measure_ne_top μ univ)]
  rw [← ENNReal.ofReal_pow (ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal, div_mul_eq_mul_div]

instance isProbabilityMeasure_law : IsProbabilityMeasure (law μ) := by
  constructor
  rw [law, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_ofTuple _) MeasurableSet.univ,
    preimage_univ, Measure.pi_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [weight_mul_pow]
  exact (poissonPMF (μ univ).toNNReal).tsum_coe

omit [IsFiniteMeasure μ] in
/-- Stratum-by-stratum integration against the constructed measure. -/
theorem lintegral_law {f : Multiset α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ c, f c ∂law μ) =
      ∑' n : ℕ, weight μ n * ∫⁻ v : Fin n → α, f (ofTuple v) ∂Measure.pi (fun _ => μ) := by
  simp only [law, lintegral_sum_measure, lintegral_smul_measure,
    lintegral_map hf (measurable_ofTuple _), smul_eq_mul]

omit [IsFiniteMeasure μ] in
/-- Factorial cancellation underlying the reduced point identity. -/
theorem weight_succ_mul (n : ℕ) : weight μ (n + 1) * (n + 1 : ℕ) = weight μ n := by
  rw [weight, weight, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- All choices of the removed index have the same product integral. -/
theorem lintegral_remove {F : α → Multiset α → ℝ≥0∞} (hF : JointMeasurable F)
    (n : ℕ) (i : Fin (n + 1)) :
    (∫⁻ v : Fin (n + 1) → α, F (v i) (ofTuple (i.removeNth v))
      ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ v : Fin n → α, F x (ofTuple v) ∂Measure.pi (fun _ => μ) ∂μ := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  rw [← lintegral_prod _ (hF n).aemeasurable]
  exact h.lintegral_comp (hF n)

/-- Measurability of the parameterised configuration integral follows from
Tonelli on every finite stratum, not an assumed quotient-product rule. -/
theorem measurable_lintegral [MeasurableSpace β] {F : β → Multiset α → ℝ≥0∞}
    (hF : JointMeasurable F) : Measurable (fun x => ∫⁻ c, F x c ∂law μ) := by
  simp_rw [lintegral_law μ (hF.section _)]
  exact Measurable.ennreal_tsum fun n =>
    measurable_const.mul (hF n).lintegral_prod_right

/-- Reduced finite Campbell--Mecke: the remainder after selecting a point is
an independent copy of the same finite Poisson configuration. The test
function may depend on the whole remainder. -/
theorem lintegral_pointSum {F : α → Multiset α → ℝ≥0∞} (hF : JointMeasurable F) :
    (∫⁻ c, pointSum F c ∂law μ) = ∫⁻ x, ∫⁻ c, F x c ∂law μ ∂μ := by
  rw [lintegral_law μ (measurable_pointSum hF), tsum_eq_zero_add' ENNReal.summable]
  simp only [ofTuple_zero, pointSum_zero, lintegral_zero, mul_zero, zero_add]
  simp_rw [pointSum_ofTuple]
  have hsum (n : ℕ) :
      (∫⁻ v : Fin (n + 1) → α, ∑ i, F (v i) (ofTuple (i.removeNth v))
        ∂Measure.pi (fun _ => μ)) =
      (n + 1 : ℕ) * ∫⁻ x, ∫⁻ v : Fin n → α, F x (ofTuple v)
        ∂Measure.pi (fun _ => μ) ∂μ := by
    rw [lintegral_finset_sum]
    · simp_rw [lintegral_remove μ hF]
      simp
    · intro i _
      exact (hF n).comp (show Measurable (fun v : Fin (n + 1) → α =>
        (v i, i.removeNth v)) from (measurable_pi_apply i).prodMk
          (measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)))
  simp_rw [hsum, ← mul_assoc, weight_succ_mul]
  simp_rw [lintegral_law μ (hF.section _)]
  rw [lintegral_tsum]
  · congr 1
    funext n
    exact (lintegral_const_mul _ ((hF n).lintegral_prod_right)).symm
  · intro n
    exact (measurable_const.mul (hF n).lintegral_prod_right).aemeasurable

/-- The reduced two-point identity retains arbitrary dependence on the
residual configuration, as required by interval-layer observables. -/
theorem lintegral_pairSum {F : α → α → Multiset α → ℝ≥0∞}
    (hF : JointMeasurable (fun p : α × α => F p.1 p.2)) :
    (∫⁻ c, pairSum F c ∂law μ) =
      ∫⁻ x, ∫⁻ y, ∫⁻ c, F x y c ∂law μ ∂μ ∂μ := by
  rw [pairSum, lintegral_pointSum μ (jointMeasurable_pointSum hF)]
  apply lintegral_congr
  intro x
  apply lintegral_pointSum μ
  intro n
  exact (hF n).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

end FinitePoisson
end BoundaryDraft
