import BoundaryDraft.Pilot3Limit
import BoundaryDraft.Pilot3Annulus
import BoundaryDraft.DimensionFourGeometry
import BoundaryDraft.ExpectedLimits

/-!
Standalone full-contract regressions for #80. Expand the original bilocal
observable, finite Poisson law/discrete layers and canonical Lorentzian target.
No jet, short/long limit, integrability or desired target identity is a premise.
The old 4D calibration is checked separately, never substituted for a 3D proof.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

example : Pilot3DeterministicGoal := pilot3DeterministicGoal
example : Pilot3ExpectedGoal := pilot3ExpectedGoal

-- Complete causal-pair action: point term, both density factors and the actual
-- signed 3D kernel, not a short model or a regulated wedge observable.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    Tendsto (fun ρ => ρ ^ (2 / 3 : ℝ) *
      (dimensionPointCoefficient 3 * (∫ _p in pilot3Region h f, (1 : ℝ)) -
        dimensionPairCoefficient 3 * ρ * ∫ p in pilot3Region h f,
          ∫ q in pilot3Region h f ∩ dimensionCausalFuture p,
            dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ *
              ((q.1 - p.1) ^ 2 - ‖q.2 - p.2‖ ^ 2) ^ (3 / 2 : ℝ)))) atTop
      (𝓝 (∫ x, pilot3Cosh h f x / Real.sqrt (pilot3Cosh h f x ^ 2 - 1)
        ∂((μH[1] : Measure Pilot3Space).restrict (pilot3SpatialJoint h)).withDensity
          (fun x => ENNReal.ofReal (Real.sqrt (1 - ‖pilot3TangentialGradient h f x‖ ^ 2))))) := by
  simpa only [pilot3Action, dimensionWeightedAction, dimensionBilocalKernel,
    dimensionIntervalSq, one_mul, Nat.reduceAdd, Nat.cast_ofNat, pilot3BoundaryIntegral,
    pilot3Weight, pilot3ProjectedArea, pilot3SurfaceMeasure, pilot3AreaDensity] using hf.action_limit

-- Independently constructed probability law and the genuine discrete action.
-- Layer coefficients contain their factorials; no expectation is defined by
-- the deterministic integral and no bounded-cardinality premise is introduced.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    Tendsto (fun ρ => ∫ c : Multiset Pilot3Spacetime,
      ρ ^ (2 / 3 - 1 : ℝ) * (dimensionPointCoefficient 3 * c.card -
        dimensionPairCoefficient 3 * ∑ k ∈ Finset.range (dimensionFactorCount 3 + 1),
          dimensionLayerWeight 3 k * ((dimensionMeasuredOrder 2).layer k c : ℝ))
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (pilot3Region h f))) atTop
        (𝓝 (∫ x, pilot3Weight h f x ∂pilot3ProjectedArea h f)) := by
  simpa only [dimensionExpectedAction, discreteDimensionAction, Nat.reduceAdd,
    Nat.cast_ofNat, pilot3BoundaryIntegral] using hf.expectedAction_limit

-- Probability and integrability are derived from the geometric constructor.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (FinitePoisson.law
      (ENNReal.ofReal ρ • volume.restrict (pilot3Region h f))) ∧
    Integrable (discreteDimensionAction (dimensionMeasuredOrder 2) 3 ρ)
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (pilot3Region h f))) :=
  ⟨inferInstanceAs (IsProbabilityMeasure (hf.boundedCausalRegion.sprinkling ρ hρ).probability),
    (hf.boundedCausalRegion.sprinkling ρ hρ).integrable_action⟩

-- One common FIXED cutoff, with the actual signed split at every density.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ ρ, pilot3Action ρ h f = pilot3ShortAction ρ δ h f + pilot3LongAction ρ δ h f) ∧
      Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop (𝓝 (pilot3BoundaryIntegral h f)) ∧
      Tendsto (fun ρ => pilot3LongAction ρ δ h f) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hs⟩ := hf.exists_shortAction_limit
  exact ⟨δ, hδ, fun ρ => hf.action_eq_short_add_long ρ δ,
    hs δ hδ le_rfl, hf.tendsto_longAction hδ⟩

-- Equality stays in long for all future-causal displacements, including nulls.
example (δ : ℝ) (z : Pilot3Spacetime) (hz : z ∈ dimensionCausalFuture 0)
    (he : z.1 + ‖z.2‖ = δ) : z ∈ pilot3LongFuture δ ∧ z ∉ pilot3ShortFuture δ :=
  ⟨⟨hz, he.ge⟩, fun hs => hs.2 ⟨hz, he.ge⟩⟩

-- Cutoff independence follows after assembly; no smallness or uniformity premise.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    Tendsto (fun ρ => pilot3ShortAction ρ δ h f - pilot3ShortAction ρ ε h f) atTop (𝓝 0) :=
  hf.tendsto_short_sub_short hδ hε

-- Both limits use the independent intrinsic measure on the actual spacetime joint.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    Tendsto (fun ρ => pilot3Action ρ h f) atTop
      (𝓝 (∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f)) ∧
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region h f)) atTop
      (𝓝 (∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f)) :=
  ⟨hf.action_limit_joint, hf.expectedAction_limit_joint⟩

-- Nonempty curved future, actual nonzero second derivative and a retained
-- positive-height critical point, in BOTH unconditional full limits.
example : (-1 / 8, (0 : Pilot3Space)) ∈ pilot3Region pilot3BallHeight pilot3SineFuture ∧
    deriv (deriv (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0]))) (1 / 2) ≠ 0 ∧
    (0 < pilot3BallHeight 0 ∧ fderiv ℝ pilot3BallHeight 0 = 0) ∧
    Tendsto (fun ρ => pilot3Action ρ pilot3BallHeight pilot3SineFuture) atTop
      (𝓝 (pilot3BoundaryIntegral pilot3BallHeight pilot3SineFuture)) ∧
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region pilot3BallHeight pilot3SineFuture))
      atTop (𝓝 (pilot3BoundaryIntegral pilot3BallHeight pilot3SineFuture)) :=
  ⟨pilot3BallSine_nonempty, pilot3SineFuture_curved.1, pilot3BallHeight_critical,
    pilot3BallSine_admissible.action_limit, pilot3BallSine_admissible.expectedAction_limit⟩

-- Planar recovery is a CONSEQUENCE, not an auxiliary planar-base premise.
example :
    Tendsto (fun ρ => pilot3Action ρ pilot3BallHeight (fun _ => 0)) atTop
      (𝓝 (∫ x, 1 / ‖pilot3Gradient pilot3BallHeight x‖ ∂pilot3SurfaceMeasure pilot3BallHeight)) ∧
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region pilot3BallHeight (fun _ => 0))) atTop
      (𝓝 (∫ x, 1 / ‖pilot3Gradient pilot3BallHeight x‖ ∂pilot3SurfaceMeasure pilot3BallHeight)) := by
  simpa only [pilot3BoundaryIntegral_planar pilot3BallPlanar_admissible] using
    And.intro pilot3BallPlanar_admissible.action_limit pilot3BallPlanar_admissible.expectedAction_limit

-- All components and all partners: no bilocal-action additivity assertion.
example : pilot3SpatialJoint pilot3DisconnectedHeight =
      Metric.sphere (0 : Pilot3Space) 1 ∪ Metric.sphere pilot3OtherCenter 1 ∧
    Tendsto (fun ρ => pilot3Action ρ pilot3DisconnectedHeight pilot3SineFuture) atTop
      (𝓝 (pilot3BoundaryIntegral pilot3DisconnectedHeight pilot3SineFuture)) ∧
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region pilot3DisconnectedHeight pilot3SineFuture))
      atTop (𝓝 (pilot3BoundaryIntegral pilot3DisconnectedHeight pilot3SineFuture)) :=
  ⟨pilot3Disconnected_joint, pilot3DisconnectedSine_admissible.action_limit,
    pilot3DisconnectedSine_admissible.expectedAction_limit⟩

-- Both annular boundaries and the retained interior critical circle.
example : pilot3SpatialJoint pilot3AnnularHeight =
      Metric.sphere (0 : Pilot3Space) 1 ∪ Metric.sphere (0 : Pilot3Space) 2 ∧
    (∃ x : Pilot3Space, 0 < pilot3AnnularHeight x ∧ fderiv ℝ pilot3AnnularHeight x = 0) ∧
    Tendsto (fun ρ => pilot3Action ρ pilot3AnnularHeight pilot3SineFuture) atTop
      (𝓝 (pilot3BoundaryIntegral pilot3AnnularHeight pilot3SineFuture)) ∧
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region pilot3AnnularHeight pilot3SineFuture))
      atTop (𝓝 (pilot3BoundaryIntegral pilot3AnnularHeight pilot3SineFuture)) :=
  ⟨pilot3Annular_joint, pilot3Annular_critical_nonempty, pilot3AnnularSine_admissible.action_limit,
    pilot3AnnularSine_admissible.expectedAction_limit⟩

-- Empty geometry is allowed, but is not the sole witness of the new theorem.
example : Tendsto (fun ρ => pilot3Action ρ (fun _ => 0) (fun _ => 0)) atTop (𝓝 0) ∧
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region (fun _ => 0) (fun _ => 0))) atTop (𝓝 0) := by
  simpa [pilot3BoundaryIntegral, pilot3ProjectedArea, pilot3SurfaceMeasure,
    pilot3SpatialJoint, pilot3ClosedPositive] using
    And.intro pilot3Empty_admissible.action_limit pilot3Empty_admissible.expectedAction_limit

-- EVERY original 4D C3 member keeps its old hypotheses and intrinsic target.
-- This is separate compatibility, not a lift of the smooth 3D theorem.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    Tendsto (fun ρ => dimensionWeightedAction 3 (dimensionPointCoefficient 4)
      (dimensionPairCoefficient 4) (dimensionIntervalCoefficient 4) ρ
        (dimensionFourTwoFaceRegion h f) (fun _ => 1)) atTop (𝓝 (dimensionFourBoundaryIntegral h f)) ∧
    Tendsto (fun ρ => dimensionExpectedAction 3 ρ (dimensionFourTwoFaceRegion h f)) atTop
      (𝓝 (dimensionFourBoundaryIntegral h f)) := by
  refine ⟨hf.dimensionFour_limit_compatibility, ?_⟩
  rw [hf.dimensionFour_boundaryIntegral]
  apply hf.expectedBDGAction_limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hf.dimensionFour_expectation hρ).symm

example : TwoFaceLimitGoal := twoFaceLimitGoal
example : TwoFaceExpectedLimitGoal := twoFaceExpectedLimitGoal

-- The unchanged original unequal-axis calibration remains 48*pi in 4D.
example : Tendsto (fun ρ => continuumMean ρ
    (graphCapRegion (ellipsoidProfile (1 / 4) ![1, 2, 3]))) atTop (𝓝 (48 * Real.pi)) ∧
    Tendsto (fun ρ => expectedBDGAction ρ
      (graphCapRegion (ellipsoidProfile (1 / 4) ![1, 2, 3]))) atTop (𝓝 (48 * Real.pi)) := by
  have hb : ∀ i : Fin 3, 2 * (1 / 4 : ℝ) < ![1, 2, 3] i := by
    intro i
    fin_cases i <;> norm_num
  constructor
  · convert ellipsoidLimitGoal (1 / 4) ![1, 2, 3] (by norm_num) hb using 1
    norm_num [Fin.prod_univ_succ]
    ring
  · convert ellipsoid_expectedBDGAction_limit (1 / 4) ![1, 2, 3] (by norm_num) hb using 1
    norm_num [Fin.prod_univ_succ]
    ring
