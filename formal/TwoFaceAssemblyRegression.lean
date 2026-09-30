import BoundaryDraft

/-!
Independent contracts for the original two-face goals and fixed-cutoff
assembly interface. The curved regressions retain the old nonaffinity witness
and require unconditional deterministic and expectation limits. Original
planar and null limits remain unchanged.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

-- The ORIGINAL goal propositions, with no analytic premises or new aliases.
example : TwoFaceLimitGoal := twoFaceLimitGoal
example : TwoFaceExpectedLimitGoal := twoFaceExpectedLimitGoal

-- Expand the independently defined target; the only hypothesis is the
-- original admissibility class, not an overlap jet or short-limit assertion.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f)) := hf.twoFaceLimit

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f)) := hf.expectedBDGAction_limit

-- Expand the actual short action and its sharp domain, not a new goal alias.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f) -
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        (volume.real (twoFaceRegion h f) - ρ * ∫ z in
          {z | z ∈ causalFuture 0 ∧ z 0 + spatialDistance 0 (spatialPart z) < δ},
          bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
            translatedOverlap (twoFaceRegion h f) z)) atTop (𝓝 0) := by
  simpa only [shortContinuumMean, shortFuture_eq] using
    hf.tendsto_continuumMean_sub_short hδ

-- The target is independently defined by induced area, not the action itself.
-- The old equivalence remains available alongside the unconditional proofs.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f)) ↔
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f)) :=
  hf.tendsto_expectedBDGAction_iff.trans (hf.tendsto_continuumMean_iff_short hδ)

-- All original planar caps, not just quadrics or globally noncritical heights.
example {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (graphCapRegion h)) atTop
      (𝓝 (∫ x, 1 / ‖graphGradient h x‖ ∂graphSurfaceMeasure h)) :=
  hh.shortContinuumMean_limit hδ

-- Keep the original positive-axis/slope hypotheses and the unequal-axis value.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (graphCapRegion (ellipsoidProfile a b)))
      atTop (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a)) := by
  simpa only [graphBoundaryIntegral_ellipsoid a b ha hb] using
    (ellipsoid_admissible a b ha hb).shortContinuumMean_limit hδ

-- A genuinely curved future face, with its old nonaffinity witness retained.
-- Two ARBITRARY fixed positive cutoffs, not an asserted uniform cutoff limit.
example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 ∧
    Tendsto (fun ρ =>
      shortContinuumMean ρ δ (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4))
        (twoFaceSine c)) -
      shortContinuumMean ρ ε (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4))
        (twoFaceSine c))) atTop (𝓝 0) := by
  obtain ⟨c, hc, hf, _, hn⟩ := twoFace_curved_nonvacuity
  exact ⟨c, hc, hf, hn, hf.tendsto_short_sub_short hδ hε⟩

-- Unconditional action and expectation limits for the existing genuinely
-- curved example; nonaffinity is retained rather than replaced by a plane.
example : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 ∧
    Tendsto (fun ρ => continuumMean ρ
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c))) atTop
      (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c))) ∧
    Tendsto (fun ρ => expectedBDGAction ρ
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c))) atTop
      (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c))) := by
  obtain ⟨c, hc, hf, _, hn⟩ := twoFace_curved_nonvacuity
  exact ⟨c, hc, hf, hn, hf.twoFaceLimit, hf.expectedBDGAction_limit⟩

-- The concrete null cap is a separate theorem, not a singular-angle instance.
example (T a : ℝ) (ha : 0 < a) (haT : a < T) :
    Tendsto (fun ρ => expectedBDGAction ρ (nullCapRegion T a)) atTop
      (𝓝 (nullJointArea T a)) := nullCap_expectedBDGAction_limit T a ha haT
