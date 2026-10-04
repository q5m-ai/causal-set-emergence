import BoundaryDraft.Pilot3NullCoordinates
import BoundaryDraft.ShortDisplacementCoordinates

/-!
# Exact short-cone null transport in physical dimension three

Only the dimension-independent time/radius change-of-variables lemmas are
reused from `ShortDisplacementCoordinates`. Spatial polar measure is r dr,
not r² dr. The ordinary full circle and the complete sharp short domain are
retained; the vertex has zero radial weight and null displacements remain.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

def pilot3ProperTimeDisplacement (ω : Pilot3Circle) (p : Plane) : Pilot3Spacetime :=
  pilot3NullPoint ω (p 1) (p 0)

theorem measurable_pilot3ProperTimeDisplacement :
    Measurable (fun p : Pilot3Circle × Plane => pilot3ProperTimeDisplacement p.1 p.2) := by
  unfold pilot3ProperTimeDisplacement pilot3NullPoint
  fun_prop

theorem pilot3_intervalSq_properTimeDisplacement (ω : Pilot3Circle) (p : Plane) (hp : p 1 ≠ 0) :
    dimensionIntervalSq 0 (pilot3ProperTimeDisplacement ω p) = p 0 := by
  simp only [dimensionIntervalSq, pilot3ProperTimeDisplacement, pilot3NullPoint,
    Prod.fst_zero, Prod.snd_zero, sub_zero, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, sq_abs]
  field_simp
  ring

theorem pilot3_polar_mem_shortFuture {δ t r : ℝ} (ω : Pilot3Circle) (hr : 0 ≤ r) :
    (t, r • ω.val) ∈ pilot3ShortFuture δ ↔ r ≤ t ∧ t + r < δ := by
  simp only [pilot3ShortFuture_eq_norm, mem_setOf_eq, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, abs_of_nonneg hr]

/-- Exact nonnegative transport. The single zero of the 3D Jacobian at the
moving lower endpoint is kept, rather than replaced by the 4D double zero. -/
theorem lintegral_pilot3ShortFuture_properTime (δ : ℝ)
    (F : Pilot3Spacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in pilot3ShortFuture δ, F z) = ∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
      ENNReal.ofReal (pilot3ShortNullJacobian (p 1) (p 0)) *
        F (pilot3ProperTimeDisplacement ω p)) ∂pilot3CircleMeasure := by
  rw [← lintegral_indicator (measurableSet_pilot3ShortFuture δ),
    lintegral_pilot3Spacetime_polar _ (hF.indicator (measurableSet_pilot3ShortFuture δ))]
  apply lintegral_congr
  intro ω
  have he (p : Plane) :
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal r *
        (pilot3ShortFuture δ).indicator F (p 0, r • ω.val)) (p 1) =
      (shortRadialDomain δ).indicator (fun p => ENNReal.ofReal (p 1) * F (p 0, p 1 • ω.val)) p := by
    by_cases hr : 0 ≤ p 1
    · rw [indicator_of_mem (show p 1 ∈ Ici (0 : ℝ) from hr)]
      have hm := pilot3_polar_mem_shortFuture (δ := δ) (t := p 0) ω hr
      by_cases hmem : (p 0, p 1 • ω.val) ∈ pilot3ShortFuture δ
      · obtain ⟨hrt, hc⟩ := hm.mp hmem
        rw [indicator_of_mem hmem]
        by_cases hpos : 0 < p 0 + p 1
        · rw [indicator_of_mem (show p ∈ shortRadialDomain δ from ⟨hr, hrt, hpos, hc⟩)]
        · have hz : p 1 = 0 := by linarith
          have hn : p ∉ shortRadialDomain δ := fun hp => hpos hp.2.2.1
          rw [indicator_of_not_mem hn, hz]
          simp
      · have hn : p ∉ shortRadialDomain δ := fun hp => hmem (hm.mpr ⟨hp.2.1, hp.2.2.2⟩)
        rw [indicator_of_not_mem hmem, indicator_of_not_mem hn, mul_zero]
    · have hn : p ∉ shortRadialDomain δ := fun hp => hr hp.1
      simp [hr, hn]
  simp_rw [he]
  rw [lintegral_indicator (measurableSet_shortRadialDomain δ), lintegral_shortRadial_properTime]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_shortProperTimeDomain δ)] with p hp
  have hv := hp.2.2.1
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, pilot3ProperTimeDisplacement, pilot3NullPoint]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * p 1))]
  congr 2
  rw [pilot3ShortNullJacobian_eq hv.ne']
  ring

end BoundaryDraft
