import BoundaryDraft.IndependentFaceSurface
import BoundaryDraft.IndependentFaceExamples
import BoundaryDraft.GraphDivergence

/-!
# Public independent-envelope geometry package

This imports class E, its actual region/strata, unchanged intrinsic joint-area
and positive-angle target, finite-density Poisson equality, examples, and the
slope-independent regular-height/collar/divergence interfaces. It contains no
enlarged-class overlap Taylor theorem or asymptotic assembly.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- Forget the causal-envelope data when only regular height geometry and a
smooth observable are needed. No analytic conclusion is stored in this pair. -/
theorem AdmissibleIndependentTwoFace.toRegularHeightPair {h f : Spatial → ℝ}
    (hf : AdmissibleIndependentTwoFace h f) : RegularHeightPair h f :=
  ⟨hf.toRegularHeight, hf.smooth_future⟩

/-- Spatial divergence with the actual raw future germ and the original
normalized Hausdorff surface measure. This identifies a geometric flux, not
an action coefficient or limit by itself. -/
theorem AdmissibleIndependentTwoFace.spatial_divergence {h f : Spatial → ℝ}
    (hf : AdmissibleIndependentTwoFace h f) :
    (∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) =
      -(∫ x, inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h) := hf.toRegularHeightPair.spatial_divergence

end BoundaryDraft
