import BoundaryDraft.TwoDDisplacement
import BoundaryDraft.TwoDTubes
import BoundaryDraft.OverlapCoordinates

/-!
# One-space-dimensional null transport for the canonical 2D action

The angular domain is the WHOLE zero-sphere (both spatial directions).
Its measure has total mass two; the spatial radial exponent is ZERO.
The resulting null Jacobian is exactly `1/(2*v)`, not the 3D or 4D one.
Only the dimension-independent time/radius diffeomorphism is reused.
-/

open MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

abbrev TwoDDirection := Metric.sphere (0 : TwoDSpace) 1

def twoDDirectionMeasure : Measure TwoDDirection := (volume : Measure TwoDSpace).toSphere

instance : IsFiniteMeasure twoDDirectionMeasure :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure TwoDSpace).toSphere)

theorem twoDDirection_mass : twoDDirectionMeasure.real univ = 2 := by
  rw [twoDDirectionMeasure, Measure.toSphere_real_apply_univ]
  norm_num [Measure.real, EuclideanSpace.volume_ball]
  have hG : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  have he : Real.sqrt Real.pi / (Real.sqrt Real.pi / 2) = 2 := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  rw [hG, he]
  norm_num

/-- The full radial Jacobian before integrating BOTH spatial directions. -/
def twoDNullJacobian (_σ v : ℝ) : ℝ := 1 / (2 * v)

theorem twoDNullJacobian_pos (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    0 < twoDNullJacobian σ v := by unfold twoDNullJacobian; positivity

theorem twoDNullJacobian_le (σ : ℝ) {δ v : ℝ} (hδ : 0 < δ) (hv : δ ≤ v) :
    twoDNullJacobian σ v ≤ 1 / (2 * δ) := by
  unfold twoDNullJacobian
  gcongr

theorem measurable_twoDRayDisplacement :
    Measurable (fun p : TwoDDirection × Plane => twoDRayDisplacement p.1.val (p.2 0) (p.2 1)) := by
  unfold twoDRayDisplacement
  apply Measurable.prodMk (by fun_prop)
  exact Measurable.smul (by fun_prop) (measurable_subtype_coe.comp measurable_fst)

theorem lintegral_twoDSpatial_polar (F : TwoDSpace → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
      F (r • ω.val)) ∂twoDDirectionMeasure := by
  have hp := (volume : Measure TwoDSpace).measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : ({(0 : TwoDSpace)}ᶜ : Set TwoDSpace), F x.val
        ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p : TwoDDirection × Ioi (0 : ℝ), F (p.2.val • p.1.val)
        ∂twoDDirectionMeasure.prod (Measure.volumeIoiPow 0) := by
      have ht := hp.symm (homeomorphUnitSphereProd TwoDSpace).toMeasurableEquiv
      simpa [twoDDirectionMeasure, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace] using (ht.lintegral_comp (hF.comp measurable_subtype_coe)).symm
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro ω
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      simp only [Pi.mul_apply, pow_zero, ENNReal.ofReal_one, one_mul]
      exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => F (r • ω.val))

/-- Polar Fubini for arbitrary measurable observables, not radial ones only. -/
theorem lintegral_twoDSpacetime_polar (F : TwoDSpacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z) = ∫⁻ ω, (∫⁻ p : Plane, (Ici (0 : ℝ)).indicator
      (fun r => F (p 0, r • ω.val)) (p 1)) ∂twoDDirectionMeasure := by
  let k := fun (t : ℝ) (ω : TwoDDirection) (r : ℝ) => F (t, r • ω.val)
  have hk : Measurable (fun p : (ℝ × TwoDDirection) × ℝ => k p.1.1 p.1.2 p.2) := by
    dsimp [k]
    exact hF.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.smul (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))))
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : TwoDSpace, F (t, x) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    _ = ∫⁻ t : ℝ, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), k t ω r) ∂twoDDirectionMeasure := by
      apply lintegral_congr
      intro t
      exact lintegral_twoDSpatial_polar _ (hF.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ ω, (∫⁻ t : ℝ, ∫⁻ r in Ici (0 : ℝ), k t ω r) ∂twoDDirectionMeasure := by
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

theorem twoDPolar_mem_longFuture {δ t r : ℝ} (ω : TwoDDirection) (hr : 0 ≤ r) :
    (t, r • ω.val) ∈ twoDLongFuture δ ↔ ![t,r] ∈ longRadialDomain δ := by
  have hω := mem_sphere_zero_iff_norm.mp ω.property
  simp only [twoDLongFuture, dimensionCausalFuture, mem_setOf_eq, Prod.fst_zero,
    Prod.snd_zero, sub_zero, norm_smul, Real.norm_eq_abs, hω, mul_one, abs_of_nonneg hr,
    longRadialDomain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  tauto

/-- Full nonnegative transport. Null endpoints are retained in the domain. -/
theorem lintegral_twoDLongFuture_properTime {δ : ℝ} (hδ : 0 < δ)
    (F : TwoDSpacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in twoDLongFuture δ, F z) = ∫⁻ ω, (∫⁻ p in properTimeDomain δ,
      ENNReal.ofReal (twoDNullJacobian (p 0) (p 1)) *
        F (twoDRayDisplacement ω.val (p 0) (p 1))) ∂twoDDirectionMeasure := by
  rw [← lintegral_indicator (measurableSet_twoDLongFuture δ),
    lintegral_twoDSpacetime_polar _ (hF.indicator (measurableSet_twoDLongFuture δ))]
  apply lintegral_congr
  intro ω
  have he (p : Plane) : (Ici (0 : ℝ)).indicator (fun r =>
      (twoDLongFuture δ).indicator F (p 0, r • ω.val)) (p 1) =
      (longRadialDomain δ).indicator (fun p => F (p 0, (p 1) • ω.val)) p := by
    by_cases hr : 0 ≤ p 1
    · have hp : (![p 0,p 1] : Plane) = p := by ext i; fin_cases i <;> rfl
      have hm := twoDPolar_mem_longFuture (δ := δ) (t := p 0) ω hr
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
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    twoDRayDisplacement]
  rfl

end BoundaryDraft
