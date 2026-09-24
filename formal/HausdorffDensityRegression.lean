import BoundaryDraft.HausdorffDensity

/-!
Regression checks for graph pullback measures and the closed-ball density
uniqueness theorem used by the graph-area argument.
-/

open MeasureTheory Filter Metric
open scoped Topology MeasureTheory ENNReal
noncomputable section
namespace BoundaryDraft

example (g : SurfacePlane → ℝ) (hg : Continuous g) (s : Set SurfacePlane) :
    surfaceGraphPullbackMeasure g s =
      ENNReal.ofReal (Real.pi / 4) *
        (μH[2] : Measure JointSpace) (surfaceGraph g '' s) :=
  surfaceGraphPullbackMeasure_apply hg s

example (L : SurfacePlane →L[ℝ] ℝ) : Function.Injective (surfaceGraphDerivative L) :=
  surfaceGraphDerivative_injective L

example (ρ : Measure SurfacePlane) [IsLocallyFiniteMeasure ρ]
    (f : SurfacePlane → ℝ≥0∞) (hρ : ρ ≪ volume)
    (hlim : ∀ᵐ x ∂volume, Tendsto
      (fun r => ρ (closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (f x))) :
    ρ = volume.withDensity f :=
  measure_eq_withDensity_of_ae_tendsto_closedBall_ratio ρ f hρ hlim

end BoundaryDraft
