import BoundaryDraft.TwoFaceGeometry
import BoundaryDraft.OverlapDensity

/-!
# Exact overlap and Poisson expectation for admissible two-face regions

Specializations of the existing overlap, fixed-positive-cutoff density, and
expectation bridge. The region, signed kernel, density, discrete observable,
and Poisson law are unchanged. No overlap expansion or limit is proved here.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section
namespace BoundaryDraft
namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- Positive-part vertical overlap for every future-causal displacement,
including macroscopic null displacements and the vertex. -/
theorem translatedOverlap_causal {s : ℝ} {a : Spatial}
    (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoFaceRegion h f) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (f (x + a) - s - (f x - max 0 (h x))) := by
  rw [twoFaceRegion_eq_twoGraphRegion]
  exact translatedOverlap_twoGraph_causal hf.strictGraphLipschitz_lower
    hf.strictGraphLipschitz_upper (by rw [← twoFaceRegion_eq_twoGraphRegion]; exact hf.isBounded_region) hz

theorem measurable_overlap : Measurable (translatedOverlap (twoFaceRegion h f)) :=
  measurable_translatedOverlap hf.measurableSet_region

theorem overlap_bounds (z : Spacetime) :
    0 ≤ translatedOverlap (twoFaceRegion h f) z ∧
      translatedOverlap (twoFaceRegion h f) z ≤ volume.real (twoFaceRegion h f) :=
  ⟨translatedOverlap_nonneg _ z,
    translatedOverlap_le_volume hf.measurableSet_region hf.isBounded_region z⟩

theorem hasCompactSupport_overlap : HasCompactSupport (translatedOverlap (twoFaceRegion h f)) :=
  hasCompactSupport_translatedOverlap hf.isBounded_region

theorem integrableOn_overlap_weight (w : Spacetime → ℝ) (hw : Continuous w) :
    IntegrableOn (fun z => w z * translatedOverlap (twoFaceRegion h f) z) (causalFuture 0) :=
  BoundaryDraft.integrableOn_overlap_weight hf.measurableSet_region hf.isBounded_region w hw

/-- The entire signed bilocal term, with both density factors retained. -/
theorem continuumMean_eq_overlap (ρ : ℝ) :
    continuumMean ρ (twoFaceRegion h f) = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (twoFaceRegion h f) - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          translatedOverlap (twoFaceRegion h f) z) :=
  continuumMean_eq_translatedOverlap hf.measurableSet_region hf.isBounded_region ρ

/-- The same representation with the exact spatial positive-part formula
inserted, not a replacement action or a truncated kernel. -/
theorem continuumMean_eq_graphOverlap (ρ : ℝ) :
    continuumMean ρ (twoFaceRegion h f) = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (twoFaceRegion h f) - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          ∫ x : Spatial, max 0 (f (x + spatialPart z) - z 0 - (f x - max 0 (h x)))) := by
  rw [hf.continuumMean_eq_overlap]
  congr 3
  apply setIntegral_congr_fun (isClosed_causalFuture 0).measurableSet
  intro z hz
  have he : Fin.cons (z 0) (spatialPart z) = z := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  dsimp only
  congr 1
  simpa only [he] using hf.translatedOverlap_causal (s := z 0) (a := spatialPart z)
    (by simpa only [he] using hz)

/-- Integrability concerns the actual discrete observable under the existing
finite Poisson law, not an assumed or continuum-defined expectation. -/
theorem integrable_discreteBDGAction {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (discreteBDGAction ρ)
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) :=
  hf.boundedCausalRegion.integrable_discreteBDGAction hρ

theorem expectedBDGAction_eq {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (twoFaceRegion h f) = continuumMean ρ (twoFaceRegion h f) :=
  hf.boundedCausalRegion.expectedBDGAction_eq hρ

theorem expectedBDGAction_eq_overlap {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (twoFaceRegion h f) = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (twoFaceRegion h f) - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          translatedOverlap (twoFaceRegion h f) z) :=
  (hf.expectedBDGAction_eq hρ).trans (hf.continuumMean_eq_overlap ρ)

theorem expectedBDGAction_eq_graphOverlap {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (twoFaceRegion h f) = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (twoFaceRegion h f) - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          ∫ x : Spatial, max 0 (f (x + spatialPart z) - z 0 - (f x - max 0 (h x)))) :=
  (hf.expectedBDGAction_eq hρ).trans (hf.continuumMean_eq_graphOverlap ρ)

/-- The existing density is used verbatim, with the actual two-face region. -/
theorem measurable_longOverlapDensity (δ : ℝ) :
    Measurable (longOverlapDensity (twoFaceRegion h f) δ) :=
  BoundaryDraft.measurable_longOverlapDensity hf.measurableSet_region δ

theorem longOverlapDensityENN_lt_top {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) :
    longOverlapDensityENN (twoFaceRegion h f) δ σ < ⊤ :=
  BoundaryDraft.longOverlapDensityENN_lt_top hf.measurableSet_region hf.isBounded_region hδ σ

theorem bounded_longOverlapDensity {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |longOverlapDensity (twoFaceRegion h f) δ σ| ≤ C :=
  BoundaryDraft.bounded_longOverlapDensity hf.measurableSet_region hf.isBounded_region hδ

theorem integrable_longOverlapDensity {δ : ℝ} (hδ : 0 < δ) :
    Integrable (longOverlapDensity (twoFaceRegion h f) δ) :=
  BoundaryDraft.integrable_longOverlapDensity hf.measurableSet_region hf.isBounded_region hδ

theorem hasCompactSupport_longOverlapDensity {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (longOverlapDensity (twoFaceRegion h f) δ) :=
  BoundaryDraft.hasCompactSupport_longOverlapDensity hf.isBounded_region hδ

theorem map_longOverlapMeasure {δ : ℝ} (hδ : 0 < δ) :
    Measure.map (intervalSq 0) (longOverlapMeasure (twoFaceRegion h f) δ) =
      volume.withDensity (longOverlapDensityENN (twoFaceRegion h f) δ) :=
  BoundaryDraft.map_longOverlapMeasure hf.measurableSet_region hδ

theorem integrable_longOverlapDensity_weight {δ : ℝ} (hδ : 0 < δ)
    (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable (fun σ => w σ * longOverlapDensity (twoFaceRegion h f) δ σ) :=
  BoundaryDraft.integrable_longOverlapDensity_weight hf.measurableSet_region hf.isBounded_region hδ w hw

theorem integral_longOverlap {δ : ℝ} (hδ : 0 < δ) (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ z in longFuture δ, w (intervalSq 0 z) * translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ, w σ * longOverlapDensity (twoFaceRegion h f) δ σ :=
  BoundaryDraft.integral_longOverlap hf.measurableSet_region hf.isBounded_region hδ w hw

theorem integral_longOverlap_bdg {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ, bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) *
        longOverlapDensity (twoFaceRegion h f) δ σ :=
  BoundaryDraft.integral_longOverlap_bdg hf.measurableSet_region hf.isBounded_region hδ ρ

end AdmissibleTwoFace

/-- Geometry is discharged; the deterministic two-face limit remains an
explicit, unproved premise. No asymptotic result follows from geometry alone. -/
theorem twoFace_expectedLimit_of_limit (hlimit : TwoFaceLimitGoal) : TwoFaceExpectedLimitGoal :=
  twoFace_expectedLimit_of_region_and_limit twoFaceRegionGoal hlimit

end BoundaryDraft
