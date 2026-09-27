import BoundaryDraft

/-! Independent checks of the OPEN contract and its nonvacuous instances.
These are not proofs of either new asymptotic goal. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology

noncomputable section

-- The deterministic target keeps the existing four-dimensional action.
example : TwoFaceLimitGoal =
    (∀ h f, AdmissibleTwoFace h f →
      Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
        (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f))) := rfl

-- This is the actual expectation of the existing observable and Poisson law.
example : TwoFaceExpectedLimitGoal =
    (∀ h f, AdmissibleTwoFace h f →
      Tendsto (fun ρ => ∫ c, discreteBDGAction ρ c
        ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) atTop
          (𝓝 (twoFaceBoundaryIntegral h f))) := rfl

-- No raw-height Lipschitz assumption or exclusion of critical points is added.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    AdmissibleTwoFace h (fun _ => 0) := hh.twoFace_planar

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h (fun _ => 0))) atTop
      (𝓝 (graphBoundaryIntegral h)) := by
  simpa using hh.graphCapLimit

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h (fun _ => 0))) atTop
      (𝓝 (graphBoundaryIntegral h)) := by
  simpa using hh.expectedBDGAction_limit

-- The original nonquadratic cap is still admitted; its existing critical-point
-- regressions in GraphCapRegression are intentionally unchanged.
example : AdmissibleTwoFace (dampedEllipsoidProfile (1 / 4) (fun _ => 1)) (fun _ => 0) :=
  (dampedEllipsoid_admissible _ _ (by norm_num) (by norm_num)
    (fun _ => by norm_num)).twoFace_planar

example : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (dampedEllipsoidProfile (1 / 4) (fun _ => 1)) (twoFaceSine c) :=
  (dampedEllipsoid_admissible _ _ (by norm_num) (by norm_num)
    (fun _ => by norm_num)).exists_twoFace_sine

-- Nonplanarity occurs ON the future face, not merely in an exterior extension.
example : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    (∀ s ∈ ({0, Real.pi / 2, Real.pi} : Set ℝ),
      0 < ellipsoidProfile (1 / 4) (fun _ => 4) ![s, 0, 0]) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 :=
  twoFace_curved_nonvacuity

-- Neither the region-constructor goal nor the deterministic limit is assumed
-- by admissibility. Only this conditional bridge implication is already proved.
example (hg : TwoFaceRegionGoal) (hl : TwoFaceLimitGoal) : TwoFaceExpectedLimitGoal :=
  twoFace_expectedLimit_of_region_and_limit hg hl
