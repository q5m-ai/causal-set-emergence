import BoundaryDraft.PoissonExpectation
import BoundaryDraft.ExpectationGeometry

/-!
# Finite-density expectation bridge

The expectation is an integral of the original discrete action against the
constructed Poisson law. Neither the discrete action nor continuumMean is
redefined. Causal convexity identifies restricted interval volumes; all null
endpoint pairs are handled by an almost-everywhere argument.
-/

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace BoundaryDraft

/-- Normalized expected discrete action, not a continuum-defined substitute.
For measurable finite-volume regions and positive density the measure here
is exactly `FiniteSprinkling.probability`. -/
def expectedBDGAction (ρ : ℝ) (M : Set Spacetime) : ℝ :=
  ∫ c, discreteBDGAction ρ c ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)

/-- Geometric input only. Boundedness is stronger than the finite-volume input
needed by the probability construction, and gives compact kernel domination. -/
structure BoundedCausalRegion (M : Set Spacetime) : Prop where
  measurable : MeasurableSet M
  bounded : Bornology.IsBounded M
  causallyConvex : CausallyConvex M

/-- The checked geometric input constructs an actual sprinkling at each
positive density; no expectation identity is a field. -/
def BoundedCausalRegion.sprinkling {M : Set Spacetime} (hM : BoundedCausalRegion M)
    (ρ : ℝ) (hρ : 0 < ρ) : FiniteSprinkling where
  region := M
  measurable_region := hM.measurable
  finite_volume := hM.bounded.measure_lt_top
  density := ρ
  density_pos := hρ

/-- Absolute integrability of the actual bilocal kernel, derived by compact
domination for every bounded region, independently of causal convexity. -/
theorem integrableOn_bilocal_bdg {M : Set Spacetime} (hM : Bornology.IsBounded M) (ρ : ℝ) :
    IntegrableOn (fun p : Spacetime × Spacetime =>
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
      {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ causalFuture p.1} := by
  have hc : Continuous (fun p : Spacetime × Spacetime =>
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2)) := by
    unfold bdgKernel bdgPolynomial
    have := continuous_intervalSq
    fun_prop
  exact (hc.continuousOn.integrableOn_compact
    (hM.isCompact_closure.prod hM.isCompact_closure)).mono_set
      (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩)

/-- Both intensity factors are retained. The diagonal and null cone are null
for product Lebesgue integration, not absent from the causal-set definition. -/
theorem FiniteSprinkling.integral_poissonBDGMean (S : FiniteSprinkling)
    (hconv : CausallyConvex S.region) :
    (∫ x, ∫ y, poissonBDGMean S x y ∂S.intensity ∂S.intensity) =
      S.density ^ 2 * ∫ x in S.region, ∫ y in S.region ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * S.density * intervalSq x y ^ 2) := by
  simp only [FiniteSprinkling.intensity, integral_smul_measure,
    ENNReal.toReal_ofReal S.density_pos.le, smul_eq_mul, integral_const_mul]
  rw [← mul_assoc, ← pow_two]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem S.measurable_region] with x hx
  have he : (∫ y in S.region, poissonBDGMean S x y) =
      ∫ y in S.region, (causalFuture x).indicator
        (fun y => bdgKernel ((Real.pi / 24) * S.density * intervalSq x y ^ 2)) y := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem S.measurable_region,
      (ae_causalFuture_chronological x).filter_mono (ae_restrict_le)] with y hy hxy
    by_cases hc : y ∈ causalFuture x
    · obtain ⟨ht, hne⟩ := hxy hc
      simp only [poissonBDGMean, hc, hne, ne_eq, not_false_eq_true, and_self, if_true,
        indicator_of_mem hc, S.interval_rate hconv hx hy ht]
    · simp [poissonBDGMean, hc]
  rw [he, integral_indicator (isClosed_causalFuture x).measurableSet,
    Measure.restrict_restrict (isClosed_causalFuture x).measurableSet, inter_comm]

/-- Exact finite-density identity under finite volume, measurability and
causal convexity. Absolute integrability of the discrete action was derived
from factorial moments; no limiting argument or bridge premise is used. -/
theorem FiniteSprinkling.expectation_eq_continuumMean (S : FiniteSprinkling)
    (hconv : CausallyConvex S.region) :
    (∫ c, discreteBDGAction S.density c ∂S.probability) =
      continuumMean S.density S.region := by
  rw [S.integral_discreteBDGAction, S.integral_poissonBDGMean hconv]
  unfold continuumMean
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
  rw [show S.density * (volume S.region).toReal - S.density ^ 2 *
      (∫ x in S.region, ∫ y in S.region ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * S.density * intervalSq x y ^ 2)) =
      S.density * ((volume S.region).toReal - S.density *
        (∫ x in S.region, ∫ y in S.region ∩ causalFuture x,
          bdgKernel ((Real.pi / 24) * S.density * intervalSq x y ^ 2))) by ring,
    ← mul_assoc, bdgNormalization_mul_density S.density_pos]

/-- Null-volume regions have zero expected action, including nonempty ones. -/
theorem FiniteSprinkling.expectation_zero_of_volume_zero (S : FiniteSprinkling)
    (hS : volume S.region = 0) :
    (∫ c, discreteBDGAction S.density c ∂S.probability) = 0 := by
  calc
    _ = ∫ _c, (0 : ℝ) ∂S.probability := by
      apply integral_congr_ae
      filter_upwards [S.ae_empty_of_volume_zero hS] with c hc
      simp [hc, discreteBDGAction, intervalLayer, intervalPairSum,
        FiniteConfiguration.pairSum, FiniteConfiguration.pointSum]
    _ = 0 := integral_zero _ _

theorem BoundedCausalRegion.integrable_discreteBDGAction {M : Set Spacetime}
    (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (discreteBDGAction ρ)
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)) :=
  BoundaryDraft.integrable_discreteBDGAction (hM.sprinkling ρ hρ)

theorem BoundedCausalRegion.expectedBDGAction_eq {M : Set Spacetime}
    (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ M = continuumMean ρ M :=
  (hM.sprinkling ρ hρ).expectation_eq_continuumMean hM.causallyConvex

theorem GraphCapData.boundedCausalRegion {h : Spatial → ℝ} (hh : GraphCapData h) :
    BoundedCausalRegion (graphCapRegion h) :=
  ⟨hh.measurableSet_cap, hh.isBounded_cap, hh.causallyConvex⟩

theorem boundedCausalRegion_nullCap (T a : ℝ) (hT : 0 < T) :
    BoundedCausalRegion (nullCapRegion T a) :=
  ⟨measurableSet_nullCapRegion T a, isBounded_nullCapRegion T a hT,
    causallyConvex_nullCap T a⟩

end BoundaryDraft
