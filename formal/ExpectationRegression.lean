import BoundaryDraft

/-!
Independent expectation contracts. The main tests expand both the probability
measure and the discrete signed action, rather than testing only a goal alias.
No variance or convergence assertion for individual configurations is made.
-/

open BoundaryDraft MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal Classical

noncomputable section
namespace ExpectationRegression

-- The actual constructed measure, not an arbitrary measure satisfying Mecke.
example (M : Set Spacetime) (hM : MeasurableSet M) (hv : volume M < ∞)
    (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)) :=
  inferInstanceAs (IsProbabilityMeasure (FiniteSprinkling.probability ⟨M, hM, hv, ρ, hρ⟩))

-- Expand the normalized finite action and both continuum integrals. The only
-- extra geometric condition beyond finite sprinkling is interval containment.
example (M : Set Spacetime) (hM : MeasurableSet M) (hv : volume M < ∞)
    (hc : ∀ x ∈ M, ∀ y ∈ M, causalInterval x y ⊆ M) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime,
      (4 / (Real.sqrt 6 * Real.sqrt ρ)) *
        ((c.card : ℝ) - intervalLayer 0 c + 9 * intervalLayer 1 c -
          16 * intervalLayer 2 c + 8 * intervalLayer 3 c)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ((∫ _x in M, (1 : ℝ)) - ρ *
        ∫ x in M, ∫ y in M ∩ causalFuture x,
          bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) :=
  (FiniteSprinkling.expectation_eq_continuumMean ⟨M, hM, hv, ρ, hρ⟩ hc)

-- Almost-sure simplicity also identifies the expectation of actual finite
-- causal-set cardinalities, not merely an auxiliary multiset observable.
example (S : FiniteSprinkling) (hc : CausallyConvex S.region) :
    (∫ c, bdgNormalization S.density *
      ((Fintype.card (CausalPoint c) : ℝ) - (causalLayerPairs 0 c).card +
        9 * (causalLayerPairs 1 c).card - 16 * (causalLayerPairs 2 c).card +
        8 * (causalLayerPairs 3 c).card) ∂S.probability) =
      continuumMean S.density S.region := by
  calc
    _ = ∫ c, discreteBDGAction S.density c ∂S.probability := by
      apply integral_congr_ae
      filter_upwards [S.ae_discreteBDGAction_eq_finite_order] with c h
      exact h.2.symm
    _ = _ := S.expectation_eq_continuumMean hc

-- Absolute integrability is discharged, not left as an expectation premise.
example (M : Set Spacetime) (hM : BoundedCausalRegion M) (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (discreteBDGAction ρ)
        (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)) ∧
      IntegrableOn (fun p : Spacetime × Spacetime =>
        bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
        {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ causalFuture p.1} :=
  ⟨hM.integrable_discreteBDGAction hρ, integrableOn_bilocal_bdg hM.bounded ρ⟩

-- The rate stays restricted to the region until causal convexity is proved.
example (S : FiniteSprinkling) (k : ℕ) :
    (∫ c, (intervalLayer k c : ℝ) ∂S.probability) =
      ∫ x, ∫ y, if y ∈ causalFuture x ∧ x ≠ y then
        (poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k).toReal else 0
        ∂S.intensity ∂S.intensity := integral_intervalLayer S k

example (S : FiniteSprinkling) (hc : CausallyConvex S.region) (x y : Spacetime)
    (hx : x ∈ S.region) (hy : y ∈ S.region) (ht : y ∈ chronologicalFuture x) :
    (S.intensity (causalIntervalInterior x y)).toReal =
      (Real.pi / 24) * S.density * intervalSq x y ^ 2 := S.interval_rate hc hx hy ht

-- All four factorial-weighted coefficients, including the negative cubic.
example (z : ℝ) : Real.exp (-z) - 9 * (Real.exp (-z) * z) +
    16 * (Real.exp (-z) * z ^ 2 / 2) - 8 * (Real.exp (-z) * z ^ 3 / 6) =
      bdgKernel z := by
  convert bdgLayerWeight_kernel z using 1
  norm_num [Finset.sum_range_succ, bdgLayerWeight, Nat.factorial]
  ring

example : bdgKernel 1 < 0 := by
  have he : bdgKernel 1 = -(4 / 3) * Real.exp (-1) := by
    norm_num [bdgKernel, bdgPolynomial]
  rw [he]
  exact mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)

-- Translated/boosted interval volume, not only the standard time-axis moment.
example (x y : Spacetime) (hxy : y ∈ chronologicalFuture x) :
    volume (causalInterval x y) = ENNReal.ofReal ((Real.pi / 24) * intervalSq x y ^ 2) :=
  volume_causalInterval_timelike_eq_ofReal x y hxy

example (x y : Spacetime) :
    volume (causalIntervalInterior x y) = volume (causalInterval x y) :=
  volume_causalIntervalInterior x y

-- Self-pairs are zero in the discrete reduced sum even though K(0) = 1.
example (S : FiniteSprinkling) (x : Spacetime) : poissonBDGMean S x x = 0 := by
  simp [poissonBDGMean]

example (x : Spacetime) : volume {y : Spacetime | intervalSq x y = 0} = 0 :=
  volume_nullCone_at x

example (S : FiniteSprinkling) (hS : volume S.region = 0) :
    (∫ c, discreteBDGAction S.density c ∂S.probability) = 0 :=
  S.expectation_zero_of_volume_zero hS

-- Nonempty zero-volume regions are handled without a uniform-point choice.
example (ρ : ℝ) (hρ : 0 < ρ) (x : Spacetime) : expectedBDGAction ρ {x} = 0 :=
  FiniteSprinkling.expectation_zero_of_volume_zero
    ⟨{x}, measurableSet_singleton x, by simp, ρ, hρ⟩ (by simp)

example (ρ : ℝ) (hρ : 0 < ρ) : expectedBDGAction ρ ∅ = 0 :=
  FiniteSprinkling.expectation_zero_of_volume_zero
    ⟨∅, MeasurableSet.empty, by simp, ρ, hρ⟩ (by simp)

-- The graph-cap expectation theorem uses the old geometric data verbatim.
example (h : Spatial → ℝ) (hh : GraphCapData h) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ c, discreteBDGAction ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (graphCapRegion h))) =
        continuumMean ρ (graphCapRegion h) := hh.expectedBDGAction_eq hρ

-- Expand the general expected limit and canonical measure independently.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => ∫ c, discreteBDGAction ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (graphCapRegion h))) atTop
      (𝓝 (∫ x : JointSpace, 1 / ‖graphGradient h x‖
        ∂(ENNReal.ofReal (Real.pi / 4) •
          (μH[2] : Measure JointSpace).restrict (graphClosedPositive h ∩ {x | h x = 0})))) :=
  hh.expectedBDGAction_limit

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion h)) atTop
      (𝓝 (∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h)) :=
  hh.expectedBDGAction_limit_eq_angle

-- No stronger ellipsoid or null-cap hypotheses than the original theorems.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion (ellipsoidProfile a b))) atTop
      (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a)) :=
  ellipsoid_expectedBDGAction_limit a b ha hb

example : Tendsto (fun ρ => expectedBDGAction ρ
    (graphCapRegion (ellipsoidProfile (1 / 4) ![1, 2, 3]))) atTop (𝓝 (48 * Real.pi)) := by
  convert ellipsoid_expectedBDGAction_limit (1 / 4) ![1, 2, 3] (by norm_num)
    (by intro i; fin_cases i <;> norm_num) using 1
  norm_num [Fin.prod_univ_succ]
  ring

example (T a : ℝ) (ha : 0 < a) (haT : a < T) :
    Tendsto (fun ρ => expectedBDGAction ρ (nullCapRegion T a)) atTop
      (𝓝 (nullJointArea T a)) := nullCap_expectedBDGAction_limit T a ha haT

example (ρ : ℝ) (hρ : 0 < ρ) :
    expectedBDGAction ρ (nullCapRegion 2 1) = continuumMean ρ (nullCapRegion 2 1) :=
  nullCap_expectedBDGAction_eq 2 1 (by norm_num) hρ

example : Tendsto (fun ρ => expectedBDGAction ρ (nullCapRegion 2 1)) atTop
    (𝓝 (3 * Real.pi)) := by
  convert nullCap_expectedBDGAction_limit 2 1 (by norm_num) (by norm_num) using 1
  simp only [nullJointArea]
  congr 1
  ring

-- An interior critical point is still permitted in the expectation theorem.
def quarticProfile : Spatial → ℝ := dampedEllipsoidProfile (1 / 4) (fun _ => 1)

theorem quartic_expected_limit_and_critical :
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion quarticProfile)) atTop
      (𝓝 (graphBoundaryIntegral quarticProfile)) ∧
    quarticProfile 0 = 3 / 16 ∧ fderiv ℝ (fun x : JointSpace => quarticProfile x) 0 = 0 := by
  refine ⟨(dampedEllipsoid_admissible _ _ (by norm_num) (by norm_num)
    (fun _ => by norm_num)).expectedBDGAction_limit, ?_, ?_⟩
  · norm_num [quarticProfile, dampedEllipsoidProfile, ellipsoidProfile]
  · have hd := (hasGradientAt_ellipsoidProfile (1 / 4) (fun _ => 1) 0).hasFDerivAt
    have hz : ellipsoidGradient (1 / 4) (fun _ => 1) 0 = 0 := by
      ext i
      simp [ellipsoidGradient]
    have hg := hd.sub ((hasDerivAt_pow 2 (ellipsoidProfile (1 / 4) (fun _ => 1) 0)).comp_hasFDerivAt 0 hd)
    calc
      _ = _ := hg.fderiv
      _ = 0 := by rw [hz]; simp

end ExpectationRegression
