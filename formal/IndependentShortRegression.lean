import BoundaryDraft.IndependentShortLimit
import BoundaryDraft.EllipsoidHausdorff

/-! Independent contracts for #107: actual absolute overlap, the original
point/pair normalization, primitive derivative control, all four density
modes, fixed-cutoff quantifiers, and old/new geometries. No full or expected
action limit is inferred. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

-- The raw/envelope equality includes null displacement and the vertex and
-- requires no global raw-future continuity or combined slope budget.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : JointSpace), x ∈ graphClosedPositive h →
      ∀ z : ℝ × JointSpace, ‖z.2‖ ≤ ε → ‖z.2‖ ≤ z.1 →
        max 0 (hf.upperEnvelope (x + z.2) - z.1 - hf.lowerEnvelope x) =
          max 0 (h x - (z.1 - f (x + z.2) + f x)) := by
  obtain ⟨ε, κ, N⟩ := hf.exists_rawFaceNeighborhood
  exact ⟨ε, N.radius_pos, fun _ hx _ hz hc => hf.raw_envelope_positivePart N hz hc hx⟩

-- Independent expansion of the final observable, including its point term,
-- original kernel, original density powers, sharp cutoff, and intrinsic target.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => (4 / Real.sqrt 6) * Real.sqrt ρ *
        (volume.real (twoFaceRegion h f) - ρ * ∫ z in causalFuture 0 \ longFuture δ,
          bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
            translatedOverlap (twoFaceRegion h f) z)) atTop
        (𝓝 (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f)) := by
  simpa only [shortContinuumMean, shortFuture, twoFaceBoundaryIntegral] using
    hf.exists_shortContinuumMean_limit

-- Full primitive derivative bounds, not merely a value-only cubic estimate.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    ∃ (R : (ℝ × JointSpace) → ℝ) (δ T : ℝ), Measurable R ∧ 0 < δ ∧ 0 ≤ T ∧
      ContDiffOn ℝ 2 R (Metric.ball 0 δ) ∧
      (∀ z ∈ Metric.ball 0 δ,
        ‖R z‖ ≤ T * ‖z‖ ^ 3 ∧ ‖fderiv ℝ R z‖ ≤ T * ‖z‖ ^ 2 ∧
          ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ T * ‖z‖) ∧
      ∀ z ∈ Metric.ball 0 δ, ‖z.2‖ ≤ z.1 →
        translatedOverlap (twoFaceRegion h f) (Fin.cons z.1 z.2) =
          volume.real (twoFaceRegion h f) - z.1 * volume.real {x : JointSpace | 0 < h x} +
          (∫ x in {x : JointSpace | 0 < h x}, inner (𝕜 := ℝ) (graphGradient f x) z.2) +
          (1 / 2 : ℝ) * (∫ x in {x : JointSpace | 0 < h x},
            fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x z.2 z.2) +
          (1 / 2 : ℝ) * (∫ x, (z.1 - inner (𝕜 := ℝ) (graphGradient f x) z.2) ^ 2 /
            ‖graphGradient h x‖ ∂graphSurfaceMeasure h) + R z := by
  obtain ⟨R, δ, T, hm, hd, hb, he⟩ := hf.exists_absoluteOverlap_remainder
  exact ⟨R, δ, T, hm, hd, hb.nonneg, hb.smooth,
    fun z hz => ⟨hb.value z hz, hb.first z hz, hb.second z hz⟩, he⟩

-- All four radial densities are attached to the existing shortOverlapDensity.
-- The same remainder and derivative constant work at smaller fixed cutoffs.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    ∃ (R : Displacement → ℝ) (δ₀ T : ℝ), Measurable R ∧ 0 < δ₀ ∧
      ShortNullRemainder.CubicBounds R δ₀ T ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ σ : ℝ, 0 < σ →
        shortOverlapDensity (twoFaceRegion h f) δ σ =
          (4 * Real.pi * volume.real (twoFaceRegion h f)) * shortRadialConstant δ σ +
          (-4 * Real.pi * volume.real {x : JointSpace | 0 < h x}) * shortRadialTime δ σ +
          (2 * Real.pi * graphBoundaryIntegral h) * shortRadialTimeSquare δ σ +
          ((2 * Real.pi / 3) *
            ((∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) +
              ∫ x, ‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖ ∂graphSurfaceMeasure h)) *
                shortRadialQuadratic δ σ + ShortNullRemainder.density R δ σ := by
  simpa only [AbsoluteShortModel.density, twoFaceShortCoefficient] using
    hf.exists_shortOverlapDensity_decomposition

-- The steep capsule is not an old-class cap. Its positive-height critical
-- point remains present while its ACTUAL short action now has a limit.
example : ¬AdmissibleGraphCap steepCapsuleHeight ∧ steepCapsuleHeight 0 = 3 / 4 ∧
    fderiv ℝ (fun x : JointSpace => steepCapsuleHeight x) 0 = 0 ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion steepCapsuleHeight steepCapsuleFuture)) atTop
        (𝓝 (twoFaceBoundaryIntegral steepCapsuleHeight steepCapsuleFuture)) :=
  ⟨steepCapsule_not_old_cap, steepCapsule_positive_critical.1, steepCapsule_positive_critical.2,
    steepCapsule_admissible.exists_shortContinuumMean_limit⟩

-- The unequal-axis symmetric member has the distinct joint angles already
-- checked in IndependentFaceRegression; this instantiates its actual limit.
example : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => shortContinuumMean ρ δ
      (twoFaceRegion (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]))) atTop
      (𝓝 (twoFaceBoundaryIntegral (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]))) := by
  apply (symmetricEllipsoid_independent (3 / 4) ![1, 2, 3] (by norm_num) ?_).exists_shortContinuumMean_limit
  intro i
  fin_cases i <;> norm_num

-- Original members use the new absolute route, without calling the old limit.
example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
        (𝓝 (twoFaceBoundaryIntegral h f)) := hf.toIndependentTwoFace.exists_shortContinuumMean_limit

private theorem axes : ∀ i : Fin 3, 2 * (1 / 4 : ℝ) < ![1, 2, 3] i := by
  intro i
  fin_cases i <;> norm_num

example : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => shortContinuumMean ρ δ
      (twoFaceRegion (ellipsoidProfile (1 / 4) ![1, 2, 3]) (fun _ => 0))) atTop (𝓝 (48 * Real.pi)) := by
  have he : twoFaceBoundaryIntegral (ellipsoidProfile (1 / 4) ![1, 2, 3]) (fun _ => 0) =
      48 * Real.pi := by
    rw [(ellipsoid_admissible _ _ (by norm_num) axes).twoFaceBoundaryIntegral_planar,
      graphBoundaryIntegral_ellipsoid _ _ (by norm_num) axes]
    norm_num [Fin.prod_univ_succ]
    ring
  simpa only [he] using
    (planarEllipsoid_independent _ _ (by norm_num) axes).exists_shortContinuumMean_limit

-- Arbitrary, even discontinuous exterior raw future data are allowed when
-- the region is empty. No global differentiability was smuggled into E.
example (f : Spatial → ℝ) : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion (fun _ => -1) f)) atTop
      (𝓝 (twoFaceBoundaryIntegral (fun _ => -1) f)) := by
  have hf : AdmissibleIndependentTwoFace (fun _ => -1) f := {
    bounded_positive := by norm_num
    smooth_near := fun _ _ => contDiffAt_const
    boundary_zero := by norm_num
    regular_zero := by norm_num
    smooth_future := by norm_num [graphClosedPositive]
    envelopes := ⟨fun _ => 0, fun _ => 0, ⟨0, le_rfl, zero_lt_one, by simp⟩,
      ⟨0, le_rfl, zero_lt_one, by simp⟩, by norm_num, by norm_num [graphClosedPositive]⟩ }
  exact hf.exists_shortContinuumMean_limit
