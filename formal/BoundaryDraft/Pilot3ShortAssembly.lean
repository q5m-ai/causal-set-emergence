import BoundaryDraft.Pilot3ShortAngular
import BoundaryDraft.Pilot3ShortDensity
import BoundaryDraft.Pilot3ShortRemainder
import BoundaryDraft.Pilot3ShortResponse

/-!
# The actual short density: signed model plus controlled remainder

The fibre identity below concerns the original overlap, not a replacement
observable. Absolute integrability precedes every signed split and Fubini
interchange. The circle moments and the exact sharp radial primitives supply
the model coefficients; the point term stays in the original short action.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A sharp fibre of a displacement observable, retaining its moving closure. -/
def pilot3ShortFibre (F : Pilot3Spacetime → ℝ) (σ : ℝ) (p : Pilot3Circle × ℝ) : ℝ :=
  if σ ≤ p.2 ^ 2 then pilot3ShortNullJacobian p.2 σ * F (pilot3NullPoint p.1 p.2 σ) else 0

theorem measurable_pilot3ShortFibre {F : Pilot3Spacetime → ℝ} (hF : Measurable F) (σ : ℝ) :
    Measurable (pilot3ShortFibre F σ) := by
  have hp : Measurable (fun p : Pilot3Circle × ℝ => pilot3NullPoint p.1 p.2 σ) := by
    unfold pilot3NullPoint
    fun_prop
  have hj : Measurable (fun p : Pilot3Circle × ℝ => pilot3ShortNullJacobian p.2 σ) := by
    unfold pilot3ShortNullJacobian pilot3NullJacobian
    fun_prop
  exact Measurable.ite (measurableSet_le measurable_const (measurable_snd.pow_const 2))
    (hj.mul (hF.comp hp)) measurable_const

private theorem pilot3_short_fibre_ae (δ : ℝ) :
    ∀ᵐ p : Pilot3Circle × ℝ ∂pilot3CircleMeasure.prod (volume.restrict (Ioo 0 δ)),
      p.2 ∈ Ioo 0 δ :=
  (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
    (Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)

/-- The primitive cubic bound supplies actual absolute integrability on the
same real-coordinate domain as the geometric density. -/
theorem integrable_pilot3ShortFibre_remainder {R : Pilot3Spacetime → ℝ} {δ T σ : ℝ}
    (hR : Measurable R) (hb : Pilot3ShortRemainder.CubicBounds R δ T) (hσ : 0 ≤ σ) :
    Integrable (pilot3ShortFibre R σ)
      (pilot3CircleMeasure.prod (volume.restrict (Ioo 0 δ))) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  apply (integrable_const (T * δ ^ 3)).mono'
    (measurable_pilot3ShortFibre hR σ).aestronglyMeasurable
  filter_upwards [pilot3_short_fibre_ae δ] with p hp
  exact hb.parameterFibre_bound (p.1, ⟨p.2, hp⟩) hσ

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

/-- Exact decomposition of the actual density after obtaining the geometric
Taylor remainder. The cutoff is sharp throughout, including closed fibres. -/
theorem shortDensity_eq_model_add_remainder {R : Pilot3Spacetime → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hR : Measurable R) (hb : Pilot3ShortRemainder.CubicBounds R δ T)
    (he : ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ, ‖z.2‖ ≤ z.1 →
      pilot3Overlap h f z = pilot3AbsoluteShortPolynomial h f z + R z)
    {σ : ℝ} (hσ : 0 < σ) :
    pilot3ShortOverlapDensity h f δ σ =
      Pilot3ShortResponse.modelDensity δ (volume.real (pilot3Region h f))
        (pilot3ShortLinearCoefficient h) (pilot3ShortTimeCoefficient h)
        (pilot3ShortSpaceCoefficient h f) σ + Pilot3ShortRemainder.density R δ σ := by
  let μ := pilot3CircleMeasure.prod (volume.restrict (Ioo (0 : ℝ) δ))
  have hA : Integrable (pilot3ShortFibre (pilot3Overlap h f) σ) μ :=
    integrable_pilot3ShortOverlapFibre hf δ hσ.le
  have hR' : Integrable (pilot3ShortFibre R σ) μ :=
    integrable_pilot3ShortFibre_remainder hR hb hσ.le
  have he' : ∀ᵐ p ∂μ, pilot3ShortFibre (pilot3Overlap h f) σ p =
      pilot3ShortFibre (pilot3AbsoluteShortPolynomial h f) σ p + pilot3ShortFibre R σ p := by
    filter_upwards [pilot3_short_fibre_ae δ] with p hp
    by_cases hs : σ ≤ p.2 ^ 2
    · simp only [pilot3ShortFibre, if_pos hs]
      rw [he _ (Pilot3ShortRemainder.CubicBounds.point_mem p.1 hp ⟨hσ.le, hs⟩)
        (pilot3NullPoint_causal p.1 hp.1 ⟨hσ.le, hs⟩), mul_add]
    · simp only [pilot3ShortFibre, if_neg hs, add_zero]
  have hP : Integrable (pilot3ShortFibre (pilot3AbsoluteShortPolynomial h f) σ) μ := by
    apply (hA.sub hR').congr
    filter_upwards [he'] with p hp
    change pilot3ShortFibre (pilot3Overlap h f) σ p - pilot3ShortFibre R σ p = _
    linarith
  have hAeq : pilot3ShortOverlapDensity h f δ σ =
      ∫ p, pilot3ShortFibre (pilot3Overlap h f) σ p ∂μ := by
    rw [pilot3ShortOverlapDensity_eq_average hf δ hσ.le, integral_prod _ hA]
    rfl
  have hReq : Pilot3ShortRemainder.density R δ σ = ∫ p, pilot3ShortFibre R σ p ∂μ := by
    rw [hb.density_eq_iterated hR hσ.le, integral_prod _ hR']
    rfl
  have hPeq : (∫ p, pilot3ShortFibre (pilot3AbsoluteShortPolynomial h f) σ p ∂μ) =
      Pilot3ShortResponse.modelDensity δ (volume.real (pilot3Region h f))
        (pilot3ShortLinearCoefficient h) (pilot3ShortTimeCoefficient h)
        (pilot3ShortSpaceCoefficient h f) σ := by
    rw [integral_prod_symm _ hP, Pilot3ShortResponse.modelDensity_eq_fibre hδ hσ]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v _
    by_cases hs : σ ≤ v ^ 2
    · simp only [pilot3ShortFibre, if_pos hs]
      rw [integral_const_mul]
      change pilot3ShortNullJacobian v σ * (∫ ω : Pilot3Circle,
        pilot3AbsoluteShortPolynomial h f ((v + σ / v) / 2, ((v - σ / v) / 2) • ω.val)
          ∂pilot3CircleMeasure) = _
      rw [hf.integral_pilot3Circle_absoluteShortPolynomial]
    · simp only [pilot3ShortFibre, if_neg hs, integral_zero]
  rw [hAeq, hReq, ← hPeq, ← integral_add hP hR']
  exact integral_congr_ae he'

/-- The original short action is the exact sharp model plus its controlled
signed remainder. The physical point term occurs exactly once. -/
theorem shortAction_eq_model_add_remainder {R : Pilot3Spacetime → ℝ} {δ T ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hR : Measurable R)
    (hb : Pilot3ShortRemainder.CubicBounds R δ T)
    (he : ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ, ‖z.2‖ ≤ z.1 →
      pilot3Overlap h f z = pilot3AbsoluteShortPolynomial h f z + R z) :
    pilot3ShortAction ρ δ h f =
      Pilot3ShortResponse.modelAction δ (volume.real (pilot3Region h f))
        (pilot3ShortLinearCoefficient h) (pilot3ShortTimeCoefficient h)
        (pilot3ShortSpaceCoefficient h f) ρ +
      (-dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) * ∫ σ : ℝ in Ioi 0,
        Pilot3ShortRemainder.density R δ σ *
          dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) := by
  have hc := dimensionIntervalCoefficient_pos 3 (by norm_num)
  have hM := Pilot3ShortResponse.integrable_modelDensity hδ hc hρ
    (volume.real (pilot3Region h f)) (pilot3ShortLinearCoefficient h)
      (pilot3ShortTimeCoefficient h) (pilot3ShortSpaceCoefficient h f)
  have hRi := hb.integrableOn_density_mul_kernel hR hc hρ
  rw [hf.shortAction_eq_density ρ δ]
  have hi : (∫ σ : ℝ in Ioi 0,
      dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
        pilot3ShortOverlapDensity h f δ σ) =
      (∫ σ : ℝ in Ioi 0, Pilot3ShortResponse.modelDensity δ (volume.real (pilot3Region h f))
        (pilot3ShortLinearCoefficient h) (pilot3ShortTimeCoefficient h)
        (pilot3ShortSpaceCoefficient h f) σ *
          dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) +
      ∫ σ : ℝ in Ioi 0, Pilot3ShortRemainder.density R δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) := by
    rw [← integral_add hM hRi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro σ hσ
    dsimp only
    rw [hf.shortDensity_eq_model_add_remainder hδ hR hb he hσ]
    ring
  rw [hi, Pilot3ShortResponse.modelAction, ← Pilot3ShortResponse.rho_normalization hρ]
  ring

end SmoothPilot3
end BoundaryDraft
