import BoundaryDraft.HausdorffPlane
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Identifying a measure from its infinitesimal ball density

This is the Lebesgue-differentiation step used in the graph area argument.  It
is independent of the planar normalization and of the particular graph: once
a locally finite measure is absolutely continuous and its ratios on shrinking
closed balls converge everywhere to a measurable density, the measure is the
corresponding `withDensity` measure.
-/

open MeasureTheory Filter Metric
open scoped Topology MeasureTheory ENNReal
noncomputable section
namespace BoundaryDraft

/-- The normalized two-dimensional Hausdorff measure in ambient Euclidean
three-space. -/
def normalizedHausdorffTwo : Measure JointSpace :=
  ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure JointSpace)

/-- Pull normalized ambient Hausdorff measure back along a scalar graph. -/
def surfaceGraphPullbackMeasure (g : SurfacePlane → ℝ) : Measure SurfacePlane :=
  Measure.comap (surfaceGraph g) normalizedHausdorffTwo

theorem surfaceGraphPullbackMeasure_apply {g : SurfacePlane → ℝ} (hg : Continuous g)
    (s : Set SurfacePlane) :
    surfaceGraphPullbackMeasure g s =
      ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure JointSpace) (surfaceGraph g '' s) := by
  rw [surfaceGraphPullbackMeasure,
    (continuous_measurableEmbedding_surfaceGraph hg).comap_apply]
  simp [normalizedHausdorffTwo]

/-- An absolutely continuous locally finite measure is determined by an
everywhere-computed closed-ball density.  The almost-everywhere differentiation
theorem supplies the same limit as the Radon--Nikodym derivative; uniqueness of
limits identifies the two densities. -/
theorem measure_eq_withDensity_of_tendsto_closedBall_ratio
    (ρ : Measure SurfacePlane) [IsLocallyFiniteMeasure ρ] (f : SurfacePlane → ℝ≥0∞)
    (hρ : ρ ≪ volume)
    (hlim : ∀ x, Tendsto
      (fun r => ρ (closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (f x))) :
    ρ = volume.withDensity f := by
  have hderiv : ρ.rnDeriv volume =ᵐ[volume] f := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv ρ volume] with x hx
    exact tendsto_nhds_unique hx (hlim x)
  rw [← Measure.withDensity_rnDeriv_eq ρ volume hρ]
  exact withDensity_congr_ae hderiv

/-- It is enough to compute the ball density almost everywhere rather than at
every point. -/
theorem measure_eq_withDensity_of_ae_tendsto_closedBall_ratio
    (ρ : Measure SurfacePlane) [IsLocallyFiniteMeasure ρ] (f : SurfacePlane → ℝ≥0∞)
    (hρ : ρ ≪ volume)
    (hlim : ∀ᵐ x ∂volume, Tendsto
      (fun r => ρ (closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (f x))) :
    ρ = volume.withDensity f := by
  have hderiv : ρ.rnDeriv volume =ᵐ[volume] f := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv ρ volume, hlim] with x hx h'x
    exact tendsto_nhds_unique hx h'x
  rw [← Measure.withDensity_rnDeriv_eq ρ volume hρ]
  exact withDensity_congr_ae hderiv

end BoundaryDraft
