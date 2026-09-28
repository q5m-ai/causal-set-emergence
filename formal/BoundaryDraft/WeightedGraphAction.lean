import BoundaryDraft.ActionTransport

/-!
# First-endpoint localization of the unchanged action

A weight partitions the outer endpoint, never the set of allowed partners.
At weight one this is exactly `continuumMean`. The graph-cap reduction uses
complete future slices before signed cancellation. No wedge or curved-face
limit is assumed by this API.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- A first-endpoint observable of the original bilocal action. The second
endpoint still ranges over the entire region, including cross-patch pairs. -/
def weightedContinuumMean (ρ : ℝ) (M : Set Spacetime) (w : Spacetime → ℝ) : ℝ :=
  (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ x in M, w x) - ρ * ∫ x in M, w x * ∫ y in M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2))

@[simp] theorem weightedContinuumMean_one (ρ : ℝ) (M : Set Spacetime) :
    weightedContinuumMean ρ M (fun _ => 1) = continuumMean ρ M := by
  simp [weightedContinuumMean, continuumMean]

/-- Compact domination of the weighted pair integrand, before any signed
Fubini or cancellation. No positivity of the weight or kernel is needed. -/
theorem integrableOn_weighted_bilocal {M : Set Spacetime} (hb : Bornology.IsBounded M)
    (ρ : ℝ) {w : Spacetime → ℝ} (hw : Continuous w) :
    IntegrableOn (fun p : Spacetime × Spacetime => w p.1 *
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
      {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ causalFuture p.1} := by
  have hc : Continuous (fun p : Spacetime × Spacetime => w p.1 *
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2)) := by
    unfold bdgKernel bdgPolynomial intervalSq spatialSeparationSq
    fun_prop
  exact (hc.continuousOn.integrableOn_compact
    (hb.isCompact_closure.prod hb.isCompact_closure)).mono_set
      (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩)

private theorem weighted_outer_integrable {M : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (ρ : ℝ) {w : Spacetime → ℝ} (hw : Continuous w) :
    IntegrableOn (fun x => w x * ∫ y in M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) M := by
  simpa only [mul_comm] using (integrableOn_bdg_outer hm hb ρ).mul_continuousOn_of_subset
    hw.continuousOn hm hb.isCompact_closure subset_closure

/-- Exact linearity on bounded measurable regions. It partitions sources,
not region-restricted actions on separate chart pieces. -/
theorem weightedContinuumMean_add {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) {w v : Spacetime → ℝ}
    (hw : Continuous w) (hv : Continuous v) :
    weightedContinuumMean ρ M (w + v) =
      weightedContinuumMean ρ M w + weightedContinuumMean ρ M v := by
  have iw : IntegrableOn w M :=
    (hw.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have iv : IntegrableOn v M :=
    (hv.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  simp only [weightedContinuumMean, Pi.add_apply, add_mul]
  rw [integral_add iw iv,
    integral_add (weighted_outer_integrable hm hb ρ hw) (weighted_outer_integrable hm hb ρ hv)]
  ring

/-- The artificial complement is subtracted exactly at finite density; it is
not asserted to vanish on its own. -/
theorem weightedContinuumMean_complement {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) {w : Spacetime → ℝ} (hw : Continuous w) :
    weightedContinuumMean ρ M w = continuumMean ρ M -
      weightedContinuumMean ρ M (fun x => 1 - w x) := by
  have h := weightedContinuumMean_add hm hb ρ hw
    (v := fun x => 1 - w x) (continuous_const.sub hw)
  have he : w + (fun x => 1 - w x) = (fun _ => 1) := by ext x; simp
  rw [he, weightedContinuumMean_one] at h
  linarith

/-- Covariance substitutes both endpoints and pulls the observable back
through the full affine inverse. -/
theorem PoincareEquiv.weightedContinuumMean_image (F : PoincareEquiv)
    (ρ : ℝ) (M : Set Spacetime) (w : Spacetime → ℝ) :
    weightedContinuumMean ρ (F '' M) (fun x => w (F.symm x)) =
      weightedContinuumMean ρ M w := by
  unfold weightedContinuumMean
  rw [F.integral_image, F.integral_image]
  simp only [F.symm_apply_apply]
  congr 3
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← F.image_future_inter, F.integral_image]
  simp only [F.intervalSq_map]

/-- Positive dilation with the observable transported, not held fixed in the
old coordinates. Both endpoints contribute their volume Jacobians. -/
theorem weightedContinuumMean_dilate {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (M : Set Spacetime) (w : Spacetime → ℝ) :
    weightedContinuumMean ρ (dilateRegion s M) (fun x => w (s⁻¹ • x)) =
      s ^ 2 * weightedContinuumMean (ρ * s ^ 4) M w := by
  unfold weightedContinuumMean
  rw [integral_dilateRegion hs, integral_dilateRegion hs]
  simp only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  simp_rw [← dilateRegion_future_inter hs, integral_dilateRegion hs, intervalSq_smul]
  have he (x y : Spacetime) : (Real.pi / 24) * ρ * (s ^ 2 * intervalSq x y) ^ 2 =
      (Real.pi / 24) * (ρ * s ^ 4) * intervalSq x y ^ 2 := by ring
  simp_rw [he, show ∀ a b : ℝ, a * (s ^ 4 * b) = s ^ 4 * (a * b) from fun a b => by ring,
    integral_const_mul]
  have hsqrt : Real.sqrt (ρ * s ^ 4) = Real.sqrt ρ * s ^ 2 := by
    rw [Real.sqrt_mul hρ.le, show s ^ 4 = (s ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg s)]
  rw [hsqrt]
  ring

/-- Weighted vertical Fubini for a spatial observable. Compact domination
precedes the interchange, and only one-dimensional endpoints are removed. -/
theorem integral_graphCap_weighted_depth (h : Spatial → ℝ) (hh : GraphCapData h)
    (a : Spatial → ℝ) (ha : Continuous a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in graphCapRegion h, a (spatialPart p) * f (-p 0)) =
      ∫ x in {x | 0 < h x}, a x * ∫ t in (0 : ℝ)..h x, f t := by
  have hc : Continuous (fun p : Spacetime => a (spatialPart p) * f (-p 0)) := by
    unfold spatialPart
    fun_prop
  have hi := integrableOn_graphCap h hh _ hc
  rw [← integral_indicator hh.measurableSet_cap,
    integral_spacetime_fibres _ ((integrable_indicator_iff hh.measurableSet_cap).mpr hi),
    ← integral_indicator hh.measurableSet_positive]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have he (t : ℝ) : (graphCapRegion h).indicator
        (fun p : Spacetime => a (spatialPart p) * f (-p 0)) (Fin.cons t x) =
        (Ioo (-h x) 0).indicator (fun t => a x * f (-t)) t := by
      simp [Set.indicator, graphCapRegion]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo, integral_const_mul]
    by_cases hx : 0 < h x
    · rw [Set.indicator_of_mem (show x ∈ {x | 0 < h x} from hx),
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : -h x ≤ 0)]
      congr 1
      simpa only [neg_zero, neg_neg] using
        (intervalIntegral.integral_comp_neg (a := -h x) (b := 0) f)
    · rw [Set.indicator_of_not_mem (show x ∉ {x | 0 < h x} from hx),
        Ioo_eq_empty_of_le (by linarith : (0 : ℝ) ≤ -h x), setIntegral_empty, mul_zero]

/-- Exact reduction with a signed spatial first-endpoint weight. This is a
consequence of the original complete future integral, not a definition of the
weighted action in terms of its prospective boundary limit. -/
theorem weighted_graphCap_reduction (h : Spatial → ℝ) (hh : GraphCapData h)
    (a : Spatial → ℝ) (ha : Continuous a) (ρ : ℝ) :
    weightedContinuumMean ρ (graphCapRegion h) (fun p => a (spatialPart p)) =
      ∫ x in {x | 0 < h x}, a x * planeKernel ρ (h x) := by
  have ha' : Continuous (fun p : Spacetime => a (spatialPart p)) := by
    unfold spatialPart
    fun_prop
  have hi1 := integrableOn_graphCap h hh _ ha'
  have hiQ : IntegrableOn (fun x => a (spatialPart x) * coneRadialIntegral ρ (-x 0))
      (graphCapRegion h) := integrableOn_graphCap h hh _
        (ha'.mul ((continuous_coneRadialIntegral ρ).comp ((continuous_apply 0).neg)))
  have hinner : (∫ x in graphCapRegion h, a (spatialPart x) *
      ∫ y in graphCapRegion h ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
      ∫ x in graphCapRegion h, a (spatialPart x) * coneRadialIntegral ρ (-x 0) := by
    apply setIntegral_congr_fun hh.measurableSet_cap
    intro x hx
    dsimp only
    rw [graphCap_future_integral h hh ρ x hx,
      coneIntegral_eq_radial ρ (-x 0) (neg_nonneg.mpr hx.2.le)]
  let L := fun t => (4 / Real.sqrt 6) * Real.sqrt ρ * (1 - ρ * coneRadialIntegral ρ t)
  have hL : Continuous L := continuous_const.mul
    (continuous_const.sub (continuous_const.mul (continuous_coneRadialIntegral ρ)))
  unfold weightedContinuumMean
  dsimp only
  rw [hinner, ← integral_const_mul, ← integral_sub hi1 (hiQ.const_mul ρ),
    ← integral_const_mul]
  have he (x : Spacetime) : (4 / Real.sqrt 6) * Real.sqrt ρ *
      (a (spatialPart x) - ρ * (a (spatialPart x) * coneRadialIntegral ρ (-x 0))) =
      a (spatialPart x) * L (-x 0) := by dsimp [L]; ring
  simp_rw [he]
  rw [integral_graphCap_weighted_depth h hh a ha L hL]
  apply setIntegral_congr_fun hh.measurableSet_positive
  intro x _
  dsimp only
  rw [show (∫ t in (0 : ℝ)..h x, L t) = planeKernel ρ (h x) from
    integral_radial_actionDensity ρ (h x)]

end BoundaryDraft
