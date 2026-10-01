import BoundaryDraft.DimensionExpectationCompatibility

/-! Independent finite-measure/physical contracts and finite configurations for #77.
The arbitrary-dimensional theorem is not a finite table of regressions. -/

open MeasureTheory Set BoundaryDraft
open BoundaryDraft.FiniteConfiguration
open scoped BigOperators ENNReal Classical
noncomputable section
namespace DimensionExpectationRegression

-- Both the law and the action are expanded independently of deterministic integrals.
example (n : ℕ) (hn : 0 < n) (M : Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M) (hc : DimensionCausallyConvex M)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ c : Multiset (DimensionSpacetime n), ρ ^ (2 / ((n + 1 : ℕ) : ℝ) - 1) *
      (dimensionPointCoefficient (n + 1) * c.card - dimensionPairCoefficient (n + 1) *
        ∑ k ∈ Finset.range (dimensionFactorCount (n + 1) + 1), dimensionLayerWeight (n + 1) k *
          ((dimensionMeasuredOrder n).layer k c : ℝ))
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)) =
      ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) * (dimensionPointCoefficient (n + 1) * (∫ _x in M, (1 : ℝ)) -
        dimensionPairCoefficient (n + 1) * ρ * ∫ x in M, ∫ y in M ∩ dimensionCausalFuture x,
          dimensionKernel (n + 1) (dimensionIntervalCoefficient (n + 1) * ρ *
            ((y.1 - x.1) ^ 2 - ‖y.2 - x.2‖ ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))) := by
  simpa only [dimensionExpectedAction, discreteDimensionAction, dimensionWeightedAction,
    dimensionBilocalKernel, dimensionIntervalSq, one_mul] using
      (DimensionBoundedCausalRegion.expectedAction_eq hn ⟨hm, hb, hc⟩ hρ)

-- Non-convex regions use their restricted interval, with both endpoint density factors.
example (n : ℕ) (S : DimensionSprinkling n) :
    (∫ c, discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density c ∂S.probability) =
      S.density ^ (2 / ((n + 1 : ℕ) : ℝ)) *
        (dimensionPointCoefficient (n + 1) * (volume S.region).toReal -
          dimensionPairCoefficient (n + 1) * S.density * ∫ x in S.region,
            ∫ y in S.region ∩ dimensionCausalFuture x, dimensionKernel (n + 1)
              (S.density * (volume (dimensionCausalIntervalInterior x y ∩ S.region)).toReal)) :=
  S.expectation_eq_restricted

-- The finite-measure statement is genuinely independent of Minkowski geometry.
example {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α) (μ : Measure α)
    [IsFiniteMeasure μ] (k : ℕ) :
    (∫ c, (O.layer k c : ℝ) ∂FinitePoisson.law μ) =
      ∫ x, ∫ y, if O.Rel x y ∧ x ≠ y then
        Real.exp (-(μ (O.interval x y)).toReal) * (μ (O.interval x y)).toReal ^ k / k.factorial
      else 0 ∂μ ∂μ := by
  simpa only [MeasuredOrder.layerMean, O.layerProbability_eq] using O.integral_layer μ k

example {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α) (μ : Measure α)
    [IsFiniteMeasure μ] [NoAtoms μ] (d : ℕ) (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, ρ ^ (-((d : ℝ) - 2) / d) *
      (dimensionPointCoefficient d * c.card - dimensionPairCoefficient d *
        ∑ k ∈ Finset.range (dimensionFactorCount d + 1), dimensionLayerWeight d k * (O.layer k c : ℝ))
      ∂FinitePoisson.law (ENNReal.ofReal ρ • μ)) =
      ρ ^ (2 / (d : ℝ)) * (dimensionPointCoefficient d * (μ univ).toReal -
        dimensionPairCoefficient d * ρ * ∫ x, ∫ y in {y | O.Rel x y},
          dimensionKernel d (ρ * (μ (O.interval x y)).toReal) ∂μ ∂μ) := by
  simpa only [discreteDimensionAction, dimension_discrete_exponent d hd,
    dimensionFiniteMeasureAction] using dimensionFiniteMeasureAction_expectation O d μ hρ

example (n : ℕ) : JointMeasurable (fun p : DimensionSpacetime n × DimensionSpacetime n =>
    (dimensionMeasuredOrder n).intervalCount p.1 p.2) :=
  (dimensionMeasuredOrder n).jointMeasurable_intervalCount

example (n k : ℕ) : Measurable ((dimensionMeasuredOrder n).layer k) :=
  (dimensionMeasuredOrder n).measurable_layer k

example (n : ℕ) (S : DimensionSprinkling n) :
    Integrable (discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density) S.probability :=
  S.integrable_action

example (n : ℕ) (S : DimensionSprinkling n) : IsProbabilityMeasure S.probability := inferInstance

example (n : ℕ) (S : DimensionSprinkling n) :
    ∀ᵐ c ∂S.probability, (∀ x ∈ c, x ∈ S.region) ∧ c.Nodup := by
  filter_upwards [S.ae_supported, S.ae_nodup] with c hs hc
  exact ⟨hs, hc⟩

example (n : ℕ) (S : DimensionSprinkling n) (hz : volume S.region = 0) :
    ∀ᵐ c ∂S.probability, discreteDimensionAction (dimensionMeasuredOrder n) (n + 1) S.density c = 0 := by
  filter_upwards [S.ae_empty_of_volume_zero hz] with c hc
  simp [hc, discreteDimensionAction, MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum]

-- Odd-dimensional coefficients are not copied from 2D/4D. Factorials matter.
example : dimensionLayerWeight 3 0 = 1 ∧ dimensionLayerWeight 3 1 = -27 / 8 ∧
    dimensionLayerWeight 3 2 = 9 / 4 ∧ (dimensionPolynomial 3).coeff 2 = 9 / 8 := by
  norm_num [dimensionLayerWeight, dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_derivative, Nat.factorial]

example : dimensionLayerWeight 4 2 = 16 ∧ (dimensionPolynomial 4).coeff 2 = 8 := by
  norm_num [dimensionLayerWeight, dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_derivative, Nat.factorial]

example (d k : ℕ) (hk : d / 2 + 1 < k) : dimensionLayerWeight d k = 0 :=
  dimensionLayerWeight_zero d k hk

private def axis (t : ℝ) : DimensionSpacetime 1 := (t, 0)
private def chain : Multiset (DimensionSpacetime 1) :=
  axis 0 ::ₘ axis 1 ::ₘ axis 2 ::ₘ axis 3 ::ₘ axis 4 ::ₘ 0

-- All 2D action layers and a layer beyond the cutoff are exercised.
example : (dimensionMeasuredOrder 1).layer 0 chain = 4 ∧
    (dimensionMeasuredOrder 1).layer 1 chain = 3 ∧
    (dimensionMeasuredOrder 1).layer 2 chain = 2 ∧
    (dimensionMeasuredOrder 1).layer 3 chain = 1 := by
  norm_num [MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum, chain,
    MeasuredOrder.Rel, dimensionMeasuredOrder, dimensionCausalOrder, MeasuredOrder.intervalCount,
    count_cons, MeasuredOrder.interval, dimensionCausalIntervalInterior, dimensionCausalInterval,
    dimensionCausalFuture, axis, Prod.ext_iff]

example (ρ : ℝ) : discreteDimensionAction (dimensionMeasuredOrder 1) 2 ρ chain = 10 := by
  rw [discreteDimensionAction_two]
  norm_num [MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum, chain,
    MeasuredOrder.Rel, dimensionMeasuredOrder, dimensionCausalOrder, MeasuredOrder.intervalCount,
    count_cons, MeasuredOrder.interval, dimensionCausalIntervalInterior, dimensionCausalInterval,
    dimensionCausalFuture, axis, Prod.ext_iff]

-- Repeated endpoints never generate a spurious self-pair.
example (n : ℕ) (x : DimensionSpacetime n) (ρ : ℝ) :
    discreteDimensionAction (dimensionMeasuredOrder n) 2 ρ (x ::ₘ x ::ₘ 0) = 4 := by
  rw [discreteDimensionAction_two]
  norm_num [MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum]

private def line (r : ℝ) : DimensionSpatial 1 := (WithLp.equiv 2 _).symm (fun _ => r)
private theorem norm_line (r : ℝ) : ‖line r‖ = |r| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  simp [line, PiLp.norm_sq_eq_of_L2]

-- Null-related intermediate points are counted; reinserting endpoints is harmless.
example : (dimensionMeasuredOrder 1).intervalCount 0 (2, line 2)
    ((0 : DimensionSpacetime 1) ::ₘ (1, line 1) ::ₘ (2, line 2) ::ₘ 0) = 1 := by
  have hsub : line 2 - line 1 = line 1 := by ext i; norm_num [line]
  norm_num [MeasuredOrder.intervalCount, count_cons, dimensionMeasuredOrder_interval,
    dimensionCausalIntervalInterior, dimensionCausalInterval, dimensionCausalFuture, hsub, norm_line]

-- A non-convex zero-volume region containing timelike endpoints must NOT use
-- its positive ambient interval volume as the Poisson rate.
example : dimensionRestrictedIntervalVolume ({0, (2, 0)} : Set (DimensionSpacetime 1)) 0 (2, 0) = 0 ∧
    volume (dimensionCausalInterval (0 : DimensionSpacetime 1) (2, 0)) = 2 := by
  constructor
  · have he : dimensionCausalIntervalInterior (0 : DimensionSpacetime 1) (2, 0) ∩ {0, (2, 0)} = ∅ := by
      ext z
      simp [dimensionCausalIntervalInterior]
    rw [dimensionRestrictedIntervalVolume, he, measure_empty]
  · rw [volume_dimensionStandardInterval 1 (by omega) 2 (by norm_num), dimensionIntervalCoefficient_two]
    norm_num

-- Exact probability/observable transport, without a causal-convexity premise.
example (S : DimensionSprinkling 3) :
    Measure.map (fun c => c.map (dimensionSpacetimeCoordinates 3)) S.probability =
      S.toFour.probability := S.four_probability.map_eq

example (ρ : ℝ) (hρ : 0 < ρ) (c : Multiset (DimensionSpacetime 3)) :
    discreteDimensionAction (dimensionMeasuredOrder 3) 4 ρ c =
      discreteBDGAction ρ (c.map (dimensionSpacetimeCoordinates 3)) := discreteDimensionAction_four hρ c

example (ρ : ℝ) (hρ : 0 < ρ) (M : Set (DimensionSpacetime 3))
    (hm : MeasurableSet M) (hv : volume M < ∞) :
    dimensionExpectedAction 3 ρ M = expectedBDGAction ρ (dimensionSpacetimeCoordinates 3 '' M) :=
  dimensionExpectedAction_four hρ hm hv

end DimensionExpectationRegression
