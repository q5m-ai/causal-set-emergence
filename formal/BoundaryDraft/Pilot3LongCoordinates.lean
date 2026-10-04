import BoundaryDraft.Pilot3Displacement
import BoundaryDraft.OverlapCoordinates

/-!
# Three-dimensional polar/null transport

Only the two-dimensional time/radius change of variables is reused from the
4D proof. The spatial polar exponent is ONE and the resulting Jacobian is
`(1 - σ/v²)/4`. Circle measure is ordinary full area, of total mass `2*pi`.
-/

open MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

abbrev Pilot3Circle := Metric.sphere (0 : Pilot3Space) 1

def pilot3CircleMeasure : Measure Pilot3Circle := (volume : Measure Pilot3Space).toSphere

instance : IsFiniteMeasure pilot3CircleMeasure :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure Pilot3Space).toSphere)

theorem pilot3Circle_mass : pilot3CircleMeasure.real univ = 2 * Real.pi := by
  rw [pilot3CircleMeasure, Measure.toSphere_real_apply_univ]
  norm_num [Measure.real, EuclideanSpace.volume_ball]
  rw [Real.sq_sqrt Real.pi_pos.le]

/-- The full radial Jacobian, before the ordinary circle integral. -/
def pilot3NullJacobian (σ v : ℝ) : ℝ := (1 - σ / v ^ 2) / 4

theorem pilot3NullJacobian_eq {σ v : ℝ} (hv : v ≠ 0) :
    pilot3NullJacobian σ v = (1 / (2 * v)) * ((v - σ / v) / 2) := by
  unfold pilot3NullJacobian
  field_simp
  ring

theorem pilot3NullJacobian_bounds {σ v : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    0 ≤ pilot3NullJacobian σ v ∧ pilot3NullJacobian σ v ≤ 1 / 4 := by
  have hs : σ / v ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hv)).mpr hσ.2
  have hn : 0 ≤ σ / v ^ 2 := div_nonneg hσ.1 (sq_nonneg v)
  unfold pilot3NullJacobian
  constructor <;> linarith

theorem measurable_pilot3RayDisplacement :
    Measurable (fun p : Pilot3Circle × Plane => pilot3RayDisplacement p.1.val (p.2 0) (p.2 1)) := by
  unfold pilot3RayDisplacement
  apply Measurable.prodMk (by fun_prop)
  exact Measurable.smul (by fun_prop) (measurable_subtype_coe.comp measurable_fst)

theorem lintegral_pilot3Spatial_polar (F : Pilot3Space → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal r * F (r • ω.val)) ∂pilot3CircleMeasure := by
  have hp := (volume : Measure Pilot3Space).measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : ({(0 : Pilot3Space)}ᶜ : Set Pilot3Space), F x.val
        ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p : Pilot3Circle × Ioi (0 : ℝ), F (p.2.val • p.1.val)
        ∂pilot3CircleMeasure.prod (Measure.volumeIoiPow 1) := by
      have ht := hp.symm (homeomorphUnitSphereProd Pilot3Space).toMeasurableEquiv
      simpa [pilot3CircleMeasure, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace] using (ht.lintegral_comp (hF.comp measurable_subtype_coe)).symm
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro ω
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      simp only [pow_one]
      exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal r * F (r • ω.val))

/-- Polar Fubini for arbitrary measurable observables, not radial ones only. -/
theorem lintegral_pilot3Spacetime_polar (F : Pilot3Spacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z) = ∫⁻ ω, (∫⁻ p : Plane, (Ici (0 : ℝ)).indicator
      (fun r => ENNReal.ofReal r * F (p 0, r • ω.val)) (p 1)) ∂pilot3CircleMeasure := by
  let k := fun (t : ℝ) (ω : Pilot3Circle) (r : ℝ) => ENNReal.ofReal r * F (t, r • ω.val)
  have hk : Measurable (fun p : (ℝ × Pilot3Circle) × ℝ => k p.1.1 p.1.2 p.2) := by
    dsimp [k]
    exact Measurable.mul (by fun_prop) (hF.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.smul (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)))))
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : Pilot3Space, F (t, x) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    _ = ∫⁻ t : ℝ, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), k t ω r) ∂pilot3CircleMeasure := by
      apply lintegral_congr
      intro t
      exact lintegral_pilot3Spatial_polar _ (hF.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ ω, (∫⁻ t : ℝ, ∫⁻ r in Ici (0 : ℝ), k t ω r) ∂pilot3CircleMeasure := by
      rw [lintegral_lintegral_swap hk.lintegral_prod_right.aemeasurable]
      simp_rw [Measure.restrict_congr_set Ioi_ae_eq_Ici]
    _ = _ := by
      apply lintegral_congr
      intro ω
      have hm : Measurable (fun p : ℝ × ℝ => (Ici (0 : ℝ)).indicator (k p.1 ω) p.2) := by
        have hh := hk.comp ((measurable_fst.prodMk (measurable_const (a := ω))).prodMk measurable_snd)
        simpa only [← indicator_comp_right, Function.comp_def] using
          hh.indicator (measurableSet_Ici.preimage measurable_snd)
      have he := (volume_preserving_finTwoArrow ℝ).lintegral_comp hm
      simp only [Function.comp_def, MeasurableEquiv.finTwoArrow_apply] at he
      change _ = ∫⁻ p : Plane, (Ici (0 : ℝ)).indicator (k (p 0) ω) (p 1)
      rw [he, Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
      simp_rw [lintegral_indicator measurableSet_Ici]

theorem pilot3Polar_mem_longFuture {δ t r : ℝ} (ω : Pilot3Circle) (hr : 0 ≤ r) :
    (t, r • ω.val) ∈ pilot3LongFuture δ ↔ ![t,r] ∈ longRadialDomain δ := by
  have hω := mem_sphere_zero_iff_norm.mp ω.property
  simp only [pilot3LongFuture, dimensionCausalFuture, mem_setOf_eq, Prod.fst_zero,
    Prod.snd_zero, sub_zero, norm_smul, Real.norm_eq_abs, hω, mul_one, abs_of_nonneg hr,
    longRadialDomain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  tauto

/-- Full nonnegative transport. Null endpoints are retained in the domain. -/
theorem lintegral_pilot3LongFuture_properTime {δ : ℝ} (hδ : 0 < δ)
    (F : Pilot3Spacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in pilot3LongFuture δ, F z) = ∫⁻ ω, (∫⁻ p in properTimeDomain δ,
      ENNReal.ofReal (pilot3NullJacobian (p 0) (p 1)) *
        F (pilot3RayDisplacement ω.val (p 0) (p 1))) ∂pilot3CircleMeasure := by
  rw [← lintegral_indicator (measurableSet_pilot3LongFuture δ),
    lintegral_pilot3Spacetime_polar _ (hF.indicator (measurableSet_pilot3LongFuture δ))]
  apply lintegral_congr
  intro ω
  have he (p : Plane) : (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal r *
      (pilot3LongFuture δ).indicator F (p 0, r • ω.val)) (p 1) =
      (longRadialDomain δ).indicator (fun p => ENNReal.ofReal (p 1) * F (p 0, (p 1) • ω.val)) p := by
    by_cases hr : 0 ≤ p 1
    · have hp : (![p 0,p 1] : Plane) = p := by ext i; fin_cases i <;> rfl
      have hm := pilot3Polar_mem_longFuture (δ := δ) (t := p 0) ω hr
      rw [hp] at hm
      by_cases hx : p ∈ longRadialDomain δ
      · simp [hr, indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
      · simp [hr, indicator_of_not_mem (fun h => hx (hm.mp h)), indicator_of_not_mem hx]
    · have hp : p ∉ longRadialDomain δ := fun hp => hr hp.1
      simp [hr, hp]
  simp_rw [he]
  have hm : MeasurableSet (longRadialDomain δ) :=
    ((isClosed_le continuous_const (continuous_apply 1)).inter
      ((isClosed_le (continuous_apply 1) (continuous_apply 0)).inter
        (isClosed_le continuous_const ((continuous_apply 0).add (continuous_apply 1))))).measurableSet
  rw [lintegral_indicator hm, lintegral_longRadial_properTime hδ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_properTimeDomain δ)] with p hp
  have hv := hδ.trans_le hp.2.2
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    pilot3RayDisplacement]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * p 1)),
    ← pilot3NullJacobian_eq hv.ne']

end BoundaryDraft
