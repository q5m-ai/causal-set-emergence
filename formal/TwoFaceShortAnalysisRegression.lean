import BoundaryDraft.TwoFaceCoefficient
import BoundaryDraft.GraphDivergence
import BoundaryDraft.SphereQuadraticMoments
import BoundaryDraft.ShortRadialQuadraticLimit
import BoundaryDraft.ShortTaylorRemainder
import BoundaryDraft.MovingCollarJet
import BoundaryDraft.TwoFaceShortReduction

/-!
Independent contracts for the short-displacement analytic components.
The geometric identities below use the original admissibility hypotheses;
the explicitly generic remainder lemma does not substitute for the geometric
producer or for the end-to-end goal regressions.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

-- The original kernel, signed logarithmic moments and endpoint integrability.
example : IntegrableOn (fun z : ℝ => z * Real.log z * bdgKernel (z ^ 2)) (Ioi 0) :=
  integrableOn_bdgKernel_transverse_log_one

example : (∫ z : ℝ in Ioi 0, z * Real.log z * bdgKernel (z ^ 2)) = 1 / 12 :=
  integral_bdgKernel_transverse_log_one

example : (∫ z : ℝ in Ioi 0, z ^ 2 * Real.log z * bdgKernel (z ^ 2)) =
    -Real.sqrt Real.pi / 12 := integral_bdgKernel_transverse_log_two

-- Actual, unnormalized full-sphere measure; no probability-measure rescaling.
example (u v : JointSpace) :
    (∫ ω : OverlapSphere, inner (𝕜 := ℝ) u ω.val * inner (𝕜 := ℝ) v ω.val
      ∂overlapSphereMeasure) = (4 * Real.pi / 3) * inner (𝕜 := ℝ) u v :=
  integral_overlapSphere_inner_mul u v

-- The sharp fixed cutoff is arbitrary, not chosen to be one or sent to zero.
example {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * (Real.sqrt ρ * ρ *
      ∫ σ : ℝ in Ioi 0, shortRadialQuadratic δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))) atTop (𝓝 (-3 / (2 * Real.pi))) :=
  bdg_shortRadialQuadratic_action_limit hδ

-- No global noncritical-height assumption and no assumed divergence theorem.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    (∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) =
      -(∫ x, inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h) := hf.spatial_divergence

-- The geometric target is the original induced-area integral, not a definition
-- by an action limit or by the local polynomial coefficient.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    (∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f) - graphBoundaryIntegral h =
      ∫ x, (inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) -
        ‖graphGradient f x‖ ^ 2) / ‖graphGradient h x‖ ∂graphSurfaceMeasure h :=
  hf.boundaryIntegral_sub_planar

-- The planar comparison cancels exactly the original point term.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    volume.real (twoFaceRegion h f) = volume.real (graphCapRegion h) :=
  hf.volume_region_eq_planar

-- Primitive local regularity and vanishing jets, NOT an assumed short limit,
-- suffice for a measurable remainder on one fixed positive neighborhood.
example {R : ShortNullRemainder.Space → ℝ} (hR : ContDiffAt ℝ 3 R 0)
    (h₀ : R 0 = 0) (h₁ : fderiv ℝ R 0 = 0) (h₂ : fderiv ℝ (fderiv ℝ R) 0 = 0) :
    ∃ (G : ShortNullRemainder.Space → ℝ) (δ T : ℝ), Measurable G ∧ 0 < δ ∧
      ShortNullRemainder.CubicBounds G δ T ∧ EqOn G R (Metric.ball 0 δ) :=
  ShortNullRemainder.exists_measurable_cubicRemainder hR h₀ h₁ h₂
