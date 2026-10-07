import BoundaryDraft.TwoDCoordinates
import BoundaryDraft.ShortDisplacementCoordinates

/-!
# Short-cone transport with the genuine 2D Jacobian

Both spatial directions and all null fibres are retained. Unlike higher
spatial dimensions the radial weight is ONE even at radius zero; the single
vertex is removed only by an explicit ambient measure-zero argument.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

def twoDProperTimeDisplacement (ω : TwoDDirection) (p : Plane) : TwoDSpacetime :=
  twoDRayDisplacement ω.val (p 0) (p 1)

theorem measurable_twoDProperTimeDisplacement :
    Measurable (fun p : TwoDDirection × Plane => twoDProperTimeDisplacement p.1 p.2) :=
  measurable_twoDRayDisplacement

theorem twoD_intervalSq_properTimeDisplacement (ω : TwoDDirection) (p : Plane) (hp : p 1 ≠ 0) :
    dimensionIntervalSq 0 (twoDProperTimeDisplacement ω p) = p 0 := by
  simp only [dimensionIntervalSq, twoDProperTimeDisplacement, twoDRayDisplacement,
    Prod.fst_zero, Prod.snd_zero, sub_zero, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, sq_abs]
  field_simp
  ring

theorem twoD_polar_mem_shortFuture {δ t r : ℝ} (ω : TwoDDirection) (hr : 0 ≤ r) :
    (t, r • ω.val) ∈ twoDShortFuture δ ↔ r ≤ t ∧ t + r < δ := by
  simp only [twoDShortFuture_eq, mem_setOf_eq, dimensionCausalFuture,
    Prod.fst_zero, Prod.snd_zero, sub_zero, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, abs_of_nonneg hr]

theorem lintegral_twoDShortFuture_properTime (δ : ℝ)
    (F : TwoDSpacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in twoDShortFuture δ, F z) = ∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
      ENNReal.ofReal (twoDNullJacobian (p 0) (p 1)) *
        F (twoDProperTimeDisplacement ω p)) ∂twoDDirectionMeasure := by
  classical
  rw [← lintegral_indicator (measurableSet_twoDShortFuture δ),
    lintegral_twoDSpacetime_polar _ (hF.indicator (measurableSet_twoDShortFuture δ))]
  apply lintegral_congr
  intro ω
  have he : (fun p : Plane => (Ici (0 : ℝ)).indicator
      (fun r => (twoDShortFuture δ).indicator F (p 0, r • ω.val)) (p 1)) =ᵐ[volume]
      (shortRadialDomain δ).indicator (fun p => F (p 0, p 1 • ω.val)) := by
    filter_upwards [(countable_singleton (0 : Plane)).ae_not_mem volume] with p hp0
    by_cases hr : 0 ≤ p 1
    · rw [indicator_of_mem (show p 1 ∈ Ici (0 : ℝ) from hr)]
      have hm := twoD_polar_mem_shortFuture (δ := δ) (t := p 0) ω hr
      by_cases hmem : (p 0, p 1 • ω.val) ∈ twoDShortFuture δ
      · obtain ⟨hrt, hc⟩ := hm.mp hmem
        rw [indicator_of_mem hmem]
        have hpos : 0 < p 0 + p 1 := by
          by_contra hn
          have ht : p 0 = 0 := by linarith
          have hr0 : p 1 = 0 := by linarith
          apply hp0
          change p = 0
          ext i
          fin_cases i <;> assumption
        rw [indicator_of_mem (show p ∈ shortRadialDomain δ from ⟨hr, hrt, hpos, hc⟩)]
      · have hn : p ∉ shortRadialDomain δ := fun hp => hmem (hm.mpr ⟨hp.2.1, hp.2.2.2⟩)
        rw [indicator_of_not_mem hmem, indicator_of_not_mem hn]
    · have hn : p ∉ shortRadialDomain δ := fun hp => hr hp.1
      simp [hr, hn]
  rw [lintegral_congr_ae he, lintegral_indicator (measurableSet_shortRadialDomain δ),
    lintegral_shortRadial_properTime]
  rfl

end BoundaryDraft
