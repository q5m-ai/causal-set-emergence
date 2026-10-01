import BoundaryDraft.DimensionMeasureExpectation
import BoundaryDraft.DimensionIntervalCompatibility

/-!
# Minkowski specialization of the dimension-indexed expectation bridge

Spatial dimension n > 0 means physical integer dimension d = n+1 ≥ 2. The
finite Poisson law is constructed from restricted canonical volume. First the
actual restricted-interval identity is derived for any finite-volume measurable
region. Only afterwards is #91's geometric volume theorem used under ambient
causal convexity. The independent weighted action is specialized at weight one.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- Closed Minkowski order, not the product order on time and space. -/
def dimensionMeasuredOrder (n : ℕ) : MeasuredOrder (DimensionSpacetime n) where
  order := dimensionCausalOrder n
  measurable_rel := measurableSet_dimensionCausalRelation

@[simp] theorem dimensionMeasuredOrder_interval {n : ℕ} (x y : DimensionSpacetime n) :
    (dimensionMeasuredOrder n).interval x y = dimensionCausalIntervalInterior x y := rfl

/-- Only geometric/density input; all probability and expectation facts follow. -/
structure DimensionSprinkling (n : ℕ) where
  region : Set (DimensionSpacetime n)
  measurable_region : MeasurableSet region
  finite_volume : volume region < ∞
  density : ℝ
  density_pos : 0 < density

namespace DimensionSprinkling
variable {n : ℕ} (S : DimensionSprinkling n)

def intensity : Measure (DimensionSpacetime n) :=
  ENNReal.ofReal S.density • volume.restrict S.region

instance : IsFiniteMeasure S.intensity := ⟨by
  simp only [intensity, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top S.finite_volume⟩

instance : NoAtoms S.intensity := ⟨fun x => by simp [intensity]⟩

def probability : Measure (Multiset (DimensionSpacetime n)) := FinitePoisson.law S.intensity

instance : IsProbabilityMeasure S.probability := FinitePoisson.isProbabilityMeasure_law S.intensity

theorem ae_supported : ∀ᵐ c ∂S.probability, ∀ x ∈ c, x ∈ S.region := by
  apply FinitePoisson.ae_supported S.intensity S.measurable_region
  simp [intensity, Measure.restrict_apply S.measurable_region.compl]

theorem ae_nodup : ∀ᵐ c ∂S.probability, c.Nodup :=
  FinitePoisson.ae_nodup S.intensity (dimensionMeasuredOrder n).measurable_diagonal

theorem ae_empty_of_volume_zero (hS : volume S.region = 0) :
    ∀ᵐ c ∂S.probability, c = 0 := by
  apply FinitePoisson.ae_empty S.intensity
  simp [intensity, Measure.restrict_eq_zero.mpr hS]

theorem integrable_action :
    Integrable (discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density) S.probability :=
  integrable_discreteDimensionAction _ _ _ S.intensity

theorem ae_action_eq_finite_order :
    ∀ᵐ c ∂S.probability, (∀ x ∈ c, x ∈ S.region) ∧ c.Nodup ∧
      discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density c =
        S.density ^ (2 / ((n + 1 : ℕ) : ℝ) - 1) *
          (dimensionPointCoefficient (n + 1) * c.toFinset.card - dimensionPairCoefficient (n + 1) *
            ∑ k ∈ Finset.range (dimensionFactorCount (n + 1) + 1), dimensionLayerWeight (n + 1) k *
              ((dimensionMeasuredOrder n).layerPairs k c).card) := by
  filter_upwards [S.ae_supported, S.ae_nodup] with c hs hc
  refine ⟨hs, hc, ?_⟩
  simp only [discreteDimensionAction, (dimensionMeasuredOrder n).layer_eq_card hc,
    Multiset.toFinset_card_of_nodup hc]

/-- Exact identity before convexity: the rate uses the part of the exclusive
interval INSIDE the sprinkled region, not an ambient proper-time surrogate. -/
theorem expectation_eq_restricted :
    (∫ c, discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density c ∂S.probability) =
      S.density ^ (2 / ((n + 1 : ℕ) : ℝ)) *
        (dimensionPointCoefficient (n + 1) * (volume S.region).toReal -
          dimensionPairCoefficient (n + 1) * S.density * ∫ x in S.region,
            ∫ y in S.region ∩ dimensionCausalFuture x, dimensionKernel (n + 1)
              (S.density * (dimensionRestrictedIntervalVolume S.region x y).toReal)) := by
  letI : IsFiniteMeasure (volume.restrict S.region) := ⟨by
    simpa only [Measure.restrict_apply_univ] using S.finite_volume⟩
  change (∫ c, discreteDimensionAction _ _ _ c ∂FinitePoisson.law
    (ENNReal.ofReal S.density • volume.restrict S.region)) = _
  rw [dimensionFiniteMeasureAction_expectation _ _ _ S.density_pos, dimensionFiniteMeasureAction]
  simp only [Measure.restrict_apply_univ, dimensionMeasuredOrder_interval,
    Measure.restrict_apply (measurableSet_dimensionCausalIntervalInterior _ _)]
  congr 2
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∫ y in dimensionCausalFuture x, _ ∂volume.restrict S.region) = _
    rw [Measure.restrict_restrict (measurableSet_dimensionCausalFuture x), inter_comm]
    rfl

/-- The actual interval rate is identified using ambient causal convexity and
#91's proved volume law; all causal pairs, including null ones, are covered. -/
theorem restricted_rate (hn : 0 < n) (hconv : DimensionCausallyConvex S.region)
    {x y : DimensionSpacetime n} (hx : x ∈ S.region) (hy : y ∈ S.region)
    (hxy : y ∈ dimensionCausalFuture x) :
    (dimensionRestrictedIntervalVolume S.region x y).toReal =
      dimensionIntervalCoefficient (n + 1) * dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2) := by
  rw [dimensionRestrictedIntervalVolume_eq_properTime hn hconv hx hy hxy,
    ENNReal.toReal_ofReal (mul_nonneg (dimensionIntervalCoefficient_pos _ (by omega)).le
      (Real.rpow_nonneg (dimensionIntervalSq_nonneg hxy) _))]

/-- Exact physical finite-density identity in every supported dimension. No
mass, jet, cancellation, limit or bridge identity is an admissibility field. -/
theorem expectation_eq_weightedAction (hn : 0 < n) (hconv : DimensionCausallyConvex S.region) :
    (∫ c, discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density c ∂S.probability) =
      dimensionWeightedAction n (dimensionPointCoefficient (n + 1)) (dimensionPairCoefficient (n + 1))
        (dimensionIntervalCoefficient (n + 1)) S.density S.region (fun _ => 1) := by
  rw [S.expectation_eq_restricted, dimensionWeightedAction]
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one, one_mul]
  congr 2
  congr 1
  apply setIntegral_congr_fun S.measurable_region
  intro x hx
  apply setIntegral_congr_fun (S.measurable_region.inter (measurableSet_dimensionCausalFuture x))
  intro y hy
  dsimp only
  rw [S.restricted_rate hn hconv hx hy.1 hy.2]
  unfold dimensionBilocalKernel
  congr 1
  ring

end DimensionSprinkling

/-- Expectation is defined from the discrete observable and constructed law. -/
def dimensionExpectedAction (n : ℕ) (ρ : ℝ) (M : Set (DimensionSpacetime n)) : ℝ :=
  ∫ c, discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) ρ c
    ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)

/-- Bounded physical-region interface, with purely geometric assumptions. -/
structure DimensionBoundedCausalRegion {n : ℕ} (M : Set (DimensionSpacetime n)) : Prop where
  measurable : MeasurableSet M
  bounded : Bornology.IsBounded M
  causallyConvex : DimensionCausallyConvex M

def DimensionBoundedCausalRegion.sprinkling {n : ℕ} {M : Set (DimensionSpacetime n)}
    (hM : DimensionBoundedCausalRegion M) (ρ : ℝ) (hρ : 0 < ρ) : DimensionSprinkling n :=
  ⟨M, hM.measurable, hM.bounded.measure_lt_top, ρ, hρ⟩

theorem DimensionBoundedCausalRegion.expectedAction_eq {n : ℕ} (hn : 0 < n)
    {M : Set (DimensionSpacetime n)} (hM : DimensionBoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionExpectedAction n ρ M = dimensionWeightedAction n (dimensionPointCoefficient (n + 1))
      (dimensionPairCoefficient (n + 1)) (dimensionIntervalCoefficient (n + 1)) ρ M (fun _ => 1) :=
  (hM.sprinkling ρ hρ).expectation_eq_weightedAction hn hM.causallyConvex

end BoundaryDraft
