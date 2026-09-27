import BoundaryDraft.TranslatedOverlap
import BoundaryDraft.CausalInterval
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Displacement coordinates

The angular measure is the full Euclidean polar sphere measure. Radial null
coordinates here are unscaled: `u = t-r`, `v = t+r`.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal

noncomputable section
namespace BoundaryDraft

abbrev OverlapSpace := EuclideanSpace ℝ (Fin 3)
abbrev OverlapSphere := Metric.sphere (0 : OverlapSpace) 1

def overlapSphereMeasure : Measure OverlapSphere := (volume : Measure OverlapSpace).toSphere

instance : IsFiniteMeasure overlapSphereMeasure :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure OverlapSpace).toSphere)

def spatialPolar (ω : OverlapSphere) (r : ℝ) : Spatial :=
  WithLp.equiv 2 _ (r • ω.val)

theorem overlapSphere_mass : overlapSphereMeasure.real univ = 4 * Real.pi := by
  rw [overlapSphereMeasure, Measure.toSphere_real_apply_univ]
  norm_num [Measure.real, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem lintegral_spatial_polar (f : Spatial → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ 2) * f (spatialPolar ω r)) ∂overlapSphereMeasure := by
  let g : OverlapSpace → ℝ≥0∞ := fun x => f (WithLp.equiv 2 _ x)
  have hg : Measurable g := hf.comp (PiLp.continuous_equiv 2 _).measurable
  have he := PiLp.volume_preserving_equiv (Fin 3)
  have hp := (volume : Measure OverlapSpace).measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : OverlapSpace, g x := (he.lintegral_comp hf).symm
    _ = ∫⁻ x : ({(0 : OverlapSpace)}ᶜ : Set OverlapSpace), g x.val
        ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫⁻ p : OverlapSphere × Ioi (0 : ℝ), g (p.2.val • p.1.val)
        ∂overlapSphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have ht := hp.symm (homeomorphUnitSphereProd OverlapSpace).toMeasurableEquiv
      have hh := ht.lintegral_comp (hg.comp measurable_subtype_coe)
      simpa [overlapSphereMeasure, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace] using hh.symm
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro ω
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      change (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.val ^ 2) * f (spatialPolar ω r.val)
        ∂volume.comap Subtype.val) = _
      exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ 2) * f (spatialPolar ω r))

theorem measurable_spatialPolar :
    Measurable (fun p : OverlapSphere × ℝ => spatialPolar p.1 p.2) := by
  unfold spatialPolar
  exact (PiLp.continuous_equiv 2 _).measurable.comp
    (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst))

/-- Polar disintegration for arbitrary measurable four-dimensional observables.
There is no angular symmetry assumption. -/
theorem lintegral_spacetime_polar (f : Spacetime → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z) = ∫⁻ ω, (∫⁻ p : Plane,
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ 2) *
        f (Fin.cons (p 0) (spatialPolar ω r))) (p 1)) ∂overlapSphereMeasure := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm _
  have hea (t : ℝ) (x : Spatial) : e (t,x) = Fin.cons t x := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  have hcons : Measurable (fun p : ℝ × Spatial => (Fin.cons p.1 p.2 : Spacetime)) := by
    convert e.measurable using 1
    funext p
    exact (hea p.1 p.2).symm
  let k := fun (t : ℝ) (ω : OverlapSphere) (r : ℝ) =>
    ENNReal.ofReal (r ^ 2) * f (Fin.cons t (spatialPolar ω r))
  have hk : Measurable (fun p : (ℝ × OverlapSphere) × ℝ => k p.1.1 p.1.2 p.2) := by
    dsimp [k]
    apply Measurable.mul (by fun_prop)
    exact hf.comp (hcons.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_spatialPolar.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : Spatial, f (Fin.cons t x) := by
      rw [← he.lintegral_comp hf, Measure.volume_eq_prod]
      calc
        _ = ∫⁻ t : ℝ, ∫⁻ x : Spatial, f (e (t,x)) :=
          lintegral_prod _ (hf.comp e.measurable).aemeasurable
        _ = _ := by simp_rw [hea]
    _ = ∫⁻ t : ℝ, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), k t ω r) ∂overlapSphereMeasure := by
      apply lintegral_congr
      intro t
      exact lintegral_spatial_polar _ (hf.comp (hcons.comp (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ ω, (∫⁻ t : ℝ, ∫⁻ r in Ici (0 : ℝ), k t ω r) ∂overlapSphereMeasure := by
      rw [lintegral_lintegral_swap (hk.lintegral_prod_right.aemeasurable)]
      simp_rw [Measure.restrict_congr_set Ioi_ae_eq_Ici]
    _ = _ := by
      apply lintegral_congr
      intro ω
      have hm : Measurable (fun p : ℝ × ℝ => (Ici (0 : ℝ)).indicator (k p.1 ω) p.2) := by
        have hh := hk.comp ((measurable_fst.prodMk (measurable_const (a := ω))).prodMk measurable_snd)
        simpa only [← indicator_comp_right, Function.comp_def] using
          hh.indicator (measurableSet_Ici.preimage measurable_snd)
      have hem := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
      rw [← hem.lintegral_comp (show Measurable (fun p : Plane =>
        (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ 2) *
          f (Fin.cons (p 0) (spatialPolar ω r))) (p 1)) from
          hm.comp (volume_preserving_finTwoArrow ℝ).measurable),
        Measure.volume_eq_prod]
      change _ = ∫⁻ p : ℝ × ℝ, (Ici (0 : ℝ)).indicator (k p.1 ω) p.2 ∂volume.prod volume
      rw [lintegral_prod _ hm.aemeasurable]
      simp_rw [lintegral_indicator measurableSet_Ici]

/-- The inverse unscaled radial-null map on the time-radius plane. -/
def radialNullMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; -1/2, 1/2]

theorem radialNullMatrix_apply (p : Plane) : Matrix.toLin' radialNullMatrix p =
    ![(p 0 + p 1) / 2, (p 1 - p 0) / 2] := by
  ext i
  fin_cases i <;> simp [radialNullMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] <;> ring

theorem det_radialNullMatrix : radialNullMatrix.det = (1 : ℝ) / 2 := by
  norm_num [radialNullMatrix, Matrix.det_fin_two]

theorem radialNull_domain (u v : ℝ) :
    (0 ≤ (v-u)/2 ∧ (v-u)/2 ≤ (u+v)/2) ↔ (0 ≤ u ∧ u ≤ v) := by
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem radialNull_intervalSq (u v : ℝ) (ω : OverlapSphere) :
    intervalSq 0 (Fin.cons ((u+v)/2) (spatialPolar ω ((v-u)/2))) = u*v := by
  have hw : ∑ i : Fin 3, ω.val i ^ 2 = 1 := by
    have h := PiLp.norm_sq_eq_of_L2 _ ω.val
    rw [show ‖ω.val‖ = 1 from mem_sphere_zero_iff_norm.mp ω.property] at h
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm
  have hp (r : ℝ) : ∑ i : Fin 3, spatialPolar ω r i ^ 2 = r ^ 2 := by
    change (∑ i : Fin 3, (r * ω.val i) ^ 2) = _
    simp only [mul_pow, ← Finset.mul_sum, hw, mul_one]
  simp only [intervalSq, spatialSeparationSq, Fin.cons_zero, Pi.zero_apply, sub_zero,
    Fin.cons_succ, hp]
  ring

/-- The full radial Jacobian, before angular integration. -/
theorem radialNull_jacobian (u v : ℝ) :
    |radialNullMatrix.det| * ((v-u)/2)^2 = (v-u)^2/8 := by
  rw [det_radialNullMatrix, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  ring

/-- Proper-time-square and long-null-coordinate domain, at a fixed cutoff. -/
def properTimeDomain (δ : ℝ) : Set Plane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ p 1 ^ 2 ∧ δ ≤ p 1}

def longRadialDomain (δ : ℝ) : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ p 0 ∧ δ ≤ p 0 + p 1}

/-- From `(sigma,v)` directly to `(t,r)`. -/
def properTimeRadial (p : Plane) : Plane :=
  ![(p 1 + p 0 / p 1) / 2, (p 1 - p 0 / p 1) / 2]

theorem properTimeRadial_image {δ : ℝ} (hδ : 0 < δ) :
    properTimeRadial '' properTimeDomain δ = longRadialDomain δ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hv : 0 < q 1 := hδ.trans_le hq.2.2
    have hs : 0 ≤ q 0 / q 1 := div_nonneg hq.1 hv.le
    have hsv : q 0 / q 1 ≤ q 1 := (div_le_iff₀ hv).mpr (by nlinarith [hq.2.1])
    change 0 ≤ (q 1-q 0/q 1)/2 ∧ (q 1-q 0/q 1)/2 ≤ (q 1+q 0/q 1)/2 ∧ _
    simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨by linarith, by linarith, by linarith [hq.2.2]⟩
  · intro hp
    have hv : 0 < p 0 + p 1 := hδ.trans_le hp.2.2
    refine ⟨![p 0 ^ 2 - p 1 ^ 2, p 0 + p 1], ?_, ?_⟩
    · simp only [properTimeDomain, mem_setOf_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact ⟨by nlinarith [hp.1, hp.2.1], by nlinarith [hp.1, hp.2.1], hp.2.2⟩
    · have he : (p 0 ^ 2 - p 1 ^ 2) / (p 0 + p 1) = p 0 - p 1 := by
        apply (div_eq_iff hv.ne').mpr
        ring
      ext i
      fin_cases i <;> simp [properTimeRadial, he]

theorem properTimeRadial_injOn {δ : ℝ} (hδ : 0 < δ) :
    InjOn properTimeRadial (properTimeDomain δ) := by
  intro p hp q hq he
  have h0 := congrFun he (0 : Fin 2)
  have h1 := congrFun he (1 : Fin 2)
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hv : p 1 = q 1 := by linarith
  have hne : q 1 ≠ 0 := (hδ.trans_le hq.2.2).ne'
  have hs : p 0 = q 0 := by
    rw [hv] at h0 h1
    exact (div_left_inj' hne).mp (by linarith : p 0 / q 1 = q 0 / q 1)
  ext i
  fin_cases i <;> assumption

/-- The derivative is an actual two-dimensional linear map, not a Jacobian premise. -/
def properTimeRadialDerivative (p : Plane) : Plane →L[ℝ] Plane :=
  let d : Plane →L[ℝ] ℝ := (p 1)⁻¹ • ContinuousLinearMap.proj 0 -
    (p 0 / p 1 ^ 2) • ContinuousLinearMap.proj 1
  ContinuousLinearMap.pi fun i => if i = 0 then
    (1/2 : ℝ) • (ContinuousLinearMap.proj 1 + d) else
    (1/2 : ℝ) • (ContinuousLinearMap.proj 1 - d)

theorem hasFDerivAt_properTimeRadial (p : Plane) (hp : p 1 ≠ 0) :
    HasFDerivAt properTimeRadial (properTimeRadialDerivative p) p := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := p)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := p)
  have hd := h0.mul ((hasDerivAt_inv hp).comp_hasFDerivAt p h1)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert (h1.add hd).const_smul (1/2 : ℝ) using 1
    · ext q
      simp [properTimeRadial, div_eq_mul_inv]
      ring
    · ext q
      simp [properTimeRadialDerivative, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
      field_simp
      ring
  · convert (h1.sub hd).const_smul (1/2 : ℝ) using 1
    · ext q
      simp [properTimeRadial, div_eq_mul_inv]
      ring
    · ext q
      simp [properTimeRadialDerivative, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
      field_simp
      ring

theorem det_properTimeRadialDerivative (p : Plane) :
    (properTimeRadialDerivative p).det = 1 / (2 * p 1) := by
  change (properTimeRadialDerivative p).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 2)), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, properTimeRadialDerivative,
    Pi.basisFun_apply, div_eq_mul_inv]
  ring

theorem measurableSet_properTimeDomain (δ : ℝ) : MeasurableSet (properTimeDomain δ) := by
  apply MeasurableSet.inter
  · exact (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  · exact ((isClosed_le (continuous_apply 0) ((continuous_apply 1).pow 2)).inter
      (isClosed_le continuous_const (continuous_apply 1))).measurableSet

/-- Exact measure transformation at a fixed positive long-displacement cutoff.
It applies to arbitrary nonnegative observables, without overlap smoothness. -/
theorem lintegral_longRadial_properTime {δ : ℝ} (hδ : 0 < δ) (f : Plane → ℝ≥0∞) :
    (∫⁻ p in longRadialDomain δ, f p) = ∫⁻ p in properTimeDomain δ,
      ENNReal.ofReal (1 / (2 * p 1)) * f (properTimeRadial p) := by
  rw [← properTimeRadial_image hδ]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_properTimeDomain δ)
    (fun p hp => (hasFDerivAt_properTimeRadial p (hδ.trans_le hp.2.2).ne').hasFDerivWithinAt)
    (properTimeRadial_injOn hδ)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_properTimeDomain δ)] with p hp
  have hv := hδ.trans_le hp.2.2
  rw [det_properTimeRadialDerivative, abs_of_pos (by positivity : 0 < 1 / (2 * p 1))]

theorem spatialDistance_spatialPolar (ω : OverlapSphere) (r : ℝ) :
    spatialDistance 0 (spatialPolar ω r) = |r| := by
  unfold spatialDistance
  simp only [sub_zero]
  change ‖r • ω.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp ω.property, mul_one]

/-- Closed long-displacement part of the full future cone. -/
def longFuture (δ : ℝ) : Set Spacetime :=
  {z | z ∈ causalFuture 0 ∧ δ ≤ z 0 + spatialDistance 0 (spatialPart z)}

theorem measurableSet_longFuture (δ : ℝ) : MeasurableSet (longFuture δ) := by
  apply (isClosed_causalFuture 0).measurableSet.inter
  change MeasurableSet {z : Spacetime | δ ≤ z 0 + spatialDistance 0 (spatialPart z)}
  apply (isClosed_le continuous_const ?_).measurableSet
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  have hd : Continuous (fun z => spatialDistance 0 (spatialPart z)) := by
    simpa only [spatialDistance, sub_zero] using
      ((PiLp.continuous_equiv_symm 2 _).comp hs).norm
  exact (continuous_apply 0).add hd

theorem polar_mem_longFuture {δ t r : ℝ} (ω : OverlapSphere) (hr : 0 ≤ r) :
    Fin.cons t (spatialPolar ω r) ∈ longFuture δ ↔
      ![t,r] ∈ longRadialDomain δ := by
  have hd := spatialDistance_spatialPolar ω r
  have hs : spatialSeparationSq 0 (Fin.cons t (spatialPolar ω r)) = r ^ 2 := by
    have hh : spatialDistance 0 (spatialPolar ω r)^2 = |r|^2 := congrArg (fun a : ℝ => a^2) hd
    simpa only [spatialDistance_sq, spatialSeparationSq, Pi.zero_apply, sub_zero,
      Fin.cons_succ, sq_abs] using hh
  simp only [longFuture, mem_setOf_eq, causalFuture, Pi.zero_apply, Fin.cons_zero,
    sub_zero, hs, spatialPart_cons, hd, abs_of_nonneg hr, longRadialDomain,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨⟨ht, hrt⟩, hc⟩
    exact ⟨hr, (sq_le_sq₀ hr ht).mp hrt, hc⟩
  · rintro ⟨_, hrt, hc⟩
    exact ⟨⟨hr.trans hrt, (sq_le_sq₀ hr (hr.trans hrt)).mpr hrt⟩, hc⟩

/-- Full angular and proper-time disintegration, before inserting any kernel.
Null endpoints are retained, and no signed cancellation is used to justify it. -/
theorem lintegral_longFuture_properTime {δ : ℝ} (hδ : 0 < δ)
    (f : Spacetime → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in longFuture δ, f z) = ∫⁻ ω, (∫⁻ p in properTimeDomain δ,
      ENNReal.ofReal ((p 1 - p 0 / p 1)^2 / (8 * p 1)) *
        f (Fin.cons ((p 1 + p 0 / p 1)/2) (spatialPolar ω ((p 1 - p 0 / p 1)/2))))
      ∂overlapSphereMeasure := by
  rw [← lintegral_indicator (measurableSet_longFuture δ),
    lintegral_spacetime_polar _ (hf.indicator (measurableSet_longFuture δ))]
  apply lintegral_congr
  intro ω
  have he (p : Plane) :
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ 2) *
        (longFuture δ).indicator f (Fin.cons (p 0) (spatialPolar ω r))) (p 1) =
      (longRadialDomain δ).indicator (fun p => ENNReal.ofReal (p 1 ^ 2) *
        f (Fin.cons (p 0) (spatialPolar ω (p 1)))) p := by
    by_cases hr : 0 ≤ p 1
    · have hp : (![p 0,p 1] : Plane) = p := by ext i; fin_cases i <;> rfl
      have hm := polar_mem_longFuture (δ := δ) (t := p 0) ω hr
      rw [hp] at hm
      by_cases hmem : p ∈ longRadialDomain δ
      · simp [hr, indicator_of_mem (hm.mpr hmem), indicator_of_mem hmem]
      · simp [hr, indicator_of_not_mem (fun h => hmem (hm.mp h)), indicator_of_not_mem hmem]
    · have hp : p ∉ longRadialDomain δ := fun hp => hr hp.1
      simp [hr, hp]
  simp_rw [he]
  have hm : MeasurableSet (longRadialDomain δ) := by
    exact ((isClosed_le continuous_const (continuous_apply 1)).inter
      ((isClosed_le (continuous_apply 1) (continuous_apply 0)).inter
        (isClosed_le continuous_const ((continuous_apply 0).add (continuous_apply 1))))).measurableSet
  rw [lintegral_indicator hm, lintegral_longRadial_properTime hδ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_properTimeDomain δ)] with p hp
  have hv := hδ.trans_le hp.2.2
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * p 1))]
  congr 2
  ring

end BoundaryDraft
