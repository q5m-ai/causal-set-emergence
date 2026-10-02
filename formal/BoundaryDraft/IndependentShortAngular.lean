import BoundaryDraft.IndependentShortJet
import BoundaryDraft.AbsoluteShortModel

/-!
# Full-sphere coefficients of the actual absolute short overlap

The constant, time-linear and both quadratic terms are retained. The spatial
Hessian is identified by the proved unweighted divergence theorem, not omitted
or replaced by a fitted coefficient.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The absolute quadratic polynomial, using the original point volume. The
height boundary integral here is a geometric reciprocal-gradient integral,
not an invocation of a same-height cap's action or causal convexity. -/
def absoluteShortPolynomial (h f : Spatial → ℝ) (z : Displacement) : ℝ :=
  volume.real (twoFaceRegion h f) - z.1 * volume.real {x : JointSpace | 0 < h x} +
    (1 / 2 : ℝ) * z.1 ^ 2 * graphBoundaryIntegral h + twoFaceShortPolynomial h f z

namespace AbsoluteShortModel
/-- An intermediate angular identity for the actual observable. Geometry must
produce it; this is not a field of admissibility. -/
def AngularExpansion (M : Set Spacetime) (δ : ℝ) (R : Displacement → ℝ)
    (V ℓ α β : ℝ) : Prop :=
  ∀ σ, 0 < σ → ∀ v ∈ Ioo (0 : ℝ) δ, σ ≤ v ^ 2 →
    (∫ ω : OverlapSphere,
      (translatedOverlap M (properTimeDisplacement ω ![σ,v]) -
        R (ShortNullRemainder.point ω v σ)) ∂overlapSphereMeasure) =
      4 * Real.pi * V + ℓ * ((v + σ / v) / 2) +
        α * ((v + σ / v) / 2) ^ 2 + β * ((v - σ / v) / 2) ^ 2
end AbsoluteShortModel

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

theorem absoluteShortPolynomial_eq_expanded (z : Displacement) :
    absoluteShortPolynomial h f z =
      volume.real (twoFaceRegion h f) - z.1 * volume.real {x : JointSpace | 0 < h x} +
      (∫ x in {x : JointSpace | 0 < h x}, inner (𝕜 := ℝ) (graphGradient f x) z.2) +
      (1 / 2 : ℝ) * (∫ x in {x : JointSpace | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x z.2 z.2) +
      (1 / 2 : ℝ) * (∫ x, (z.1 - inner (𝕜 := ℝ) (graphGradient f x) z.2) ^ 2 /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h) := by
  have hi₀ := hf.toRegularHeight.integrable_reciprocal_slope.const_mul (z.1 ^ 2)
  have hi₁ := hf.toRegularHeightPair.integrable_graphSurface_inner_mul_div z.2 z.2
  have hi₂ := (hf.toRegularHeightPair.integrable_graphSurface_inner_div z.2).const_mul (2 * z.1)
  have he : (∫ x, (z.1 - inner (𝕜 := ℝ) (graphGradient f x) z.2) ^ 2 /
      ‖graphGradient h x‖ ∂graphSurfaceMeasure h) = z.1 ^ 2 * graphBoundaryIntegral h +
      ∫ x, (inner (𝕜 := ℝ) (graphGradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2) / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h := by
    have hic : Integrable (fun x => (inner (𝕜 := ℝ) (graphGradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2) / ‖graphGradient h x‖)
          (graphSurfaceMeasure h) := (hi₁.sub hi₂).congr (Eventually.of_forall fun x => by
            dsimp only [Pi.sub_apply]; ring)
    rw [graphBoundaryIntegral, ← integral_const_mul, ← integral_add hi₀ hic]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he, absoluteShortPolynomial, twoFaceShortPolynomial]
  ring

theorem integral_overlapSphere_absoluteShortPolynomial (s r : ℝ) :
    (∫ ω : OverlapSphere, absoluteShortPolynomial h f (s, r • ω.val) ∂overlapSphereMeasure) =
      4 * Real.pi * volume.real (twoFaceRegion h f) +
      (-4 * Real.pi * volume.real {x : JointSpace | 0 < h x}) * s +
      (2 * Real.pi * graphBoundaryIntegral h) * s ^ 2 + twoFaceShortCoefficient h f * r ^ 2 := by
  let C := volume.real (twoFaceRegion h f) - s * volume.real {x : JointSpace | 0 < h x} +
    (1 / 2 : ℝ) * s ^ 2 * graphBoundaryIntegral h
  change (∫ ω : OverlapSphere, C + twoFaceShortPolynomial h f (s, r • ω.val) ∂overlapSphereMeasure) = _
  rw [integral_add (integrable_const C) (hf.toRegularHeightPair.integrable_overlapSphere_twoFaceShortPolynomial s r),
    hf.toRegularHeightPair.integral_overlapSphere_twoFaceShortPolynomial]
  simp only [integral_const, smul_eq_mul]
  rw [overlapSphere_mass]
  dsimp [C]
  ring

/-- The full normalized coefficient equals the independently defined intrinsic
angle/area integral. The divergence contribution of the future Hessian remains. -/
theorem absoluteShortCoefficient_identification :
    ((2 * Real.pi * graphBoundaryIntegral h) - 3 * twoFaceShortCoefficient h f) /
      (2 * Real.pi) = twoFaceBoundaryIntegral h f := by
  have he := hf.twoFaceShortCoefficient_identification
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hπ] at he ⊢
  nlinarith

/-- Geometry produces the actual angular expansion and measurable primitive
remainder with derivative control on one common, fixed positive ball. -/
theorem exists_absoluteAngularExpansion :
    ∃ (R : Displacement → ℝ) (δ T : ℝ), Measurable R ∧ 0 < δ ∧
      ShortNullRemainder.CubicBounds R δ T ∧
      AbsoluteShortModel.AngularExpansion (twoFaceRegion h f) δ R
        (volume.real (twoFaceRegion h f))
        (-4 * Real.pi * volume.real {x : JointSpace | 0 < h x})
        (2 * Real.pi * graphBoundaryIntegral h) (twoFaceShortCoefficient h f) := by
  obtain ⟨R, δ, T, hR, hδ, hB, hj⟩ := hf.exists_absoluteOverlap_remainder
  refine ⟨R, δ, T, hR, hδ, hB, ?_⟩
  intro σ hσ v hv hσv
  have hquot : 0 ≤ σ / v := div_nonneg hσ.le hv.1.le
  have hquotv : σ / v ≤ v := (div_le_iff₀ hv.1).mpr (by nlinarith only [hσv])
  have he (ω : OverlapSphere) :
      translatedOverlap (twoFaceRegion h f) (properTimeDisplacement ω ![σ,v]) -
        R (ShortNullRemainder.point ω v σ) =
          absoluteShortPolynomial h f ((v + σ / v) / 2, ((v - σ / v) / 2) • ω.val) := by
    have hp : ShortNullRemainder.point ω v σ ∈ Metric.ball (0 : Displacement) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (ShortNullRemainder.norm_point_le ω hv.1 ⟨hσ.le, hσv⟩).trans_lt hv.2
    have hc : ‖(ShortNullRemainder.point ω v σ).2‖ ≤ (ShortNullRemainder.point ω v σ).1 := by
      simp only [ShortNullRemainder.point, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      rw [abs_of_nonneg (by linarith : 0 ≤ (v - σ / v) / 2)]
      linarith
    have hh := hj _ hp hc
    rw [← hf.absoluteShortPolynomial_eq_expanded] at hh
    change translatedOverlap (twoFaceRegion h f) (properTimeDisplacement ω ![σ,v]) =
      absoluteShortPolynomial h f (ShortNullRemainder.point ω v σ) + R (ShortNullRemainder.point ω v σ) at hh
    rw [hh, add_sub_cancel_right]
    rfl
  rw [integral_congr_ae (Eventually.of_forall he)]
  exact hf.integral_overlapSphere_absoluteShortPolynomial _ _

end AdmissibleIndependentTwoFace
end BoundaryDraft
