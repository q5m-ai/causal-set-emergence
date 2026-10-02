import BoundaryDraft.IndependentFaceLimit
import BoundaryDraft.TwoFaceLimit
import BoundaryDraft.EllipsoidHausdorff

/-! Independent full-contract regressions for #109. The actual bilocal action,
restricted Poisson law, signed discrete layers and canonical Lorentzian target
are expanded, not replaced by goal aliases or the quadratic short model.
The old contracts are checked separately and remain unchanged. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

-- Full deterministic observable: original point term, both integrals, signed
-- kernel, density factors and Lorentzian (not Euclidean graph) area measure.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    Tendsto (fun ρ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ _x in twoFaceRegion h f, (1 : ℝ)) - ρ *
        ∫ x in twoFaceRegion h f, ∫ y in twoFaceRegion h f ∩ causalFuture x,
          bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2))) atTop
      (𝓝 (∫ x, twoFaceCosh h f x / Real.sqrt (twoFaceCosh h f x ^ 2 - 1)
        ∂(ENNReal.ofReal (Real.pi / 4) •
          (μH[2] : Measure JointSpace).restrict (graphJoint h)).withDensity
            (fun x => ENNReal.ofReal
              (Real.sqrt (1 - ‖twoFaceTangentialGradient h f x‖ ^ 2))))) :=
  hf.twoFaceLimit

-- The actual unsmeared finite action under the constructed restricted law.
-- No expectation, integrability or asymptotic premise is supplied by a caller.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    Tendsto (fun ρ => ∫ c : Multiset Spacetime,
      (4 / (Real.sqrt 6 * Real.sqrt ρ)) *
        ((c.card : ℝ) - intervalLayer 0 c + 9 * intervalLayer 1 c -
          16 * intervalLayer 2 c + 8 * intervalLayer 3 c)
        ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) atTop
      (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f)) :=
  hf.expectedBDGAction_limit

-- All bridge inputs are derived, including containment of CLOSED ambient
-- intervals; the probability law and absolute integrability are not hypotheses.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ x ∈ twoFaceRegion h f, ∀ y ∈ twoFaceRegion h f,
      causalInterval x y ⊆ twoFaceRegion h f) ∧
    IsProbabilityMeasure (FinitePoisson.law
      (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) ∧
    Integrable (discreteBDGAction ρ) (FinitePoisson.law
      (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) :=
  ⟨hf.causallyConvex_region,
    inferInstanceAs (IsProbabilityMeasure (hf.boundedCausalRegion.sprinkling ρ hρ).probability),
    hf.boundedCausalRegion.integrable_discreteBDGAction hρ⟩

-- One common FIXED cutoff from the actual short producer works for both
-- pieces. Neither a sequence of cutoffs nor a limit delta -> 0 is used.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
        (𝓝 (twoFaceBoundaryIntegral h f)) ∧
      Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
        ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hs⟩ := hf.exists_shortContinuumMean_limit
  exact ⟨δ, hδ, hs δ hδ le_rfl, hf.tendsto_normalized_longOverlap hδ⟩

-- The finite-density split includes the actual density, with the negative
-- signed prefactor; it is not a decomposition assumed in admissibility.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (ρ δ : ℝ) (hδ : 0 < δ) :
    continuumMean ρ (twoFaceRegion h f) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        (volume.real (twoFaceRegion h f) - ρ *
          ∫ z in causalFuture 0 \ longFuture δ,
            bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
              translatedOverlap (twoFaceRegion h f) z) -
      (4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
        longOverlapDensity (twoFaceRegion h f) δ σ *
          bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) :=
  hf.continuumMean_eq_short_sub_density hδ ρ

-- Cutoff equality stays in long, even on the null boundary.
example (δ : ℝ) (z : Spacetime) (hz : z ∈ causalFuture 0)
    (he : z 0 + spatialDistance 0 (spatialPart z) = δ) :
    z ∈ longFuture δ ∧ z ∉ shortFuture δ :=
  ⟨⟨hz, he.ge⟩, fun hs => hs.2 ⟨hz, he.ge⟩⟩

-- Future Hessian and its divergence flux are retained without an old cap
-- slope bound. This is the absolute normalized coefficient, not a difference.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    ((2 * Real.pi * graphBoundaryIntegral h) - 3 * ((2 * Real.pi / 3) *
      ((∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) +
        ∫ x, ‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖ ∂graphSurfaceMeasure h))) /
      (2 * Real.pi) = ∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f :=
  hf.absoluteShortCoefficient_identification

-- The steep capsule stays excluded from BOTH old coordinate contracts, and
-- keeps its positive-height critical point in the full/expected theorem.
example : ¬AdmissibleTwoFace steepCapsuleHeight steepCapsuleFuture ∧
    ¬AdmissibleGraphCap steepCapsuleHeight ∧ steepCapsuleHeight 0 = 3 / 4 ∧
    fderiv ℝ (fun x : JointSpace => steepCapsuleHeight x) 0 = 0 ∧
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion steepCapsuleHeight steepCapsuleFuture))
      atTop (𝓝 (twoFaceBoundaryIntegral steepCapsuleHeight steepCapsuleFuture)) ∧
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion steepCapsuleHeight steepCapsuleFuture))
      atTop (𝓝 (twoFaceBoundaryIntegral steepCapsuleHeight steepCapsuleFuture)) :=
  ⟨steepCapsule_not_old_twoFace, steepCapsule_not_old_cap,
    steepCapsule_positive_critical.1, steepCapsule_positive_critical.2,
    steepCapsule_admissible.twoFaceLimit, steepCapsule_admissible.expectedBDGAction_limit⟩

-- Every symmetric unequal-axis member, including the variable-angle witness
-- a=3/4, b=(1,2,3) in IndependentFaceRegression. No constant-angle premise.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, a < b i) :
    Tendsto (fun ρ => continuumMean ρ
      (twoFaceRegion (ellipsoidProfile a b) (ellipsoidProfile (a / 2) b))) atTop
        (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile a b) (ellipsoidProfile (a / 2) b))) ∧
    Tendsto (fun ρ => expectedBDGAction ρ
      (twoFaceRegion (ellipsoidProfile a b) (ellipsoidProfile (a / 2) b))) atTop
        (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile a b) (ellipsoidProfile (a / 2) b))) :=
  ⟨(symmetricEllipsoid_independent a b ha hb).twoFaceLimit,
    (symmetricEllipsoid_independent a b ha hb).expectedBDGAction_limit⟩

-- Instantiate the concrete nonconstant-angle witness, rather than relying
-- only on a universally quantified calibration with uninstantiated hypotheses.
example :
    Tendsto (fun ρ => continuumMean ρ
      (twoFaceRegion (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]))) atTop
      (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]))) ∧
    Tendsto (fun ρ => expectedBDGAction ρ
      (twoFaceRegion (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]))) atTop
      (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]))) := by
  have hf := symmetricEllipsoid_independent (3 / 4) ![1, 2, 3] (by norm_num)
    (by intro i; fin_cases i <;> norm_num)
  exact ⟨hf.twoFaceLimit, hf.expectedBDGAction_limit⟩

-- A large cutoff, not constrained by the local Taylor radius, follows only
-- AFTER full assembly. Two arbitrary fixed positive cutoffs have zero difference.
example (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion steepCapsuleHeight steepCapsuleFuture) -
      shortContinuumMean ρ ε (twoFaceRegion steepCapsuleHeight steepCapsuleFuture)) atTop (𝓝 0) :=
  steepCapsule_admissible.tendsto_short_sub_short hδ hε

-- Every old member can use the new absolute route without invoking its old
-- action proof. Both old public theorem contracts also still elaborate.
example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) ∧
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) :=
  ⟨hf.toIndependentTwoFace.twoFaceLimit, hf.toIndependentTwoFace.expectedBDGAction_limit⟩

example : TwoFaceLimitGoal := twoFaceLimitGoal
example : TwoFaceExpectedLimitGoal := twoFaceExpectedLimitGoal
example : IndependentTwoFaceLimitGoal := independentTwoFaceLimitGoal
example : IndependentTwoFaceExpectedLimitGoal := independentTwoFaceExpectedLimitGoal

-- Original planar unequal-axis cases retain their EXACT old hypotheses and
-- target, but these two proofs now go through class E's absolute theorem.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b))) atTop
      (𝓝 ((2 * Real.pi / a) * (b 0 * b 1 * b 2))) ∧
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion (ellipsoidProfile a b))) atTop
      (𝓝 ((2 * Real.pi / a) * (b 0 * b 1 * b 2))) := by
  have hf := planarEllipsoid_independent a b ha hb
  have he : twoFaceBoundaryIntegral (ellipsoidProfile a b) (fun _ => 0) =
      (2 * Real.pi / a) * (b 0 * b 1 * b 2) := by
    rw [(ellipsoid_admissible a b ha hb).twoFaceBoundaryIntegral_planar,
      graphBoundaryIntegral_ellipsoid a b ha hb]
    simp [Fin.prod_univ_succ]
    ring
  constructor
  · simpa only [twoFaceRegion_planar, he] using hf.twoFaceLimit
  · simpa only [twoFaceRegion_planar, he] using hf.expectedBDGAction_limit

-- Empty geometry with unrestricted exterior raw future data still qualifies;
-- no global smoothness, nonempty joint or positive volume is silently required.
example (f : Spatial → ℝ) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion (fun _ => -1) f)) atTop
      (𝓝 (twoFaceBoundaryIntegral (fun _ => -1) f)) ∧
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion (fun _ => -1) f)) atTop
      (𝓝 (twoFaceBoundaryIntegral (fun _ => -1) f)) := by
  have hf : AdmissibleIndependentTwoFace (fun _ => -1) f := {
    bounded_positive := by norm_num
    smooth_near := fun _ _ => contDiffAt_const
    boundary_zero := by norm_num
    regular_zero := by norm_num
    smooth_future := by norm_num [graphClosedPositive]
    envelopes := ⟨fun _ => 0, fun _ => 0, ⟨0, le_rfl, zero_lt_one, by simp⟩,
      ⟨0, le_rfl, zero_lt_one, by simp⟩, by norm_num, by norm_num [graphClosedPositive]⟩ }
  exact ⟨hf.twoFaceLimit, hf.expectedBDGAction_limit⟩
