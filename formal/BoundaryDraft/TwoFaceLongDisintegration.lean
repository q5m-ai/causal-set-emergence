import BoundaryDraft.LongEnvelopeData

/-! Exact finite-density transport from the existing overlap to spatial gap fibres.
The cutoff is fixed and the polar sphere retains its full mass. -/

open MeasureTheory Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000

noncomputable section
namespace BoundaryDraft

private def gapWeight (σ v : ℝ) : ℝ := (v - σ / v)^2 / (8 * v)

private theorem measurable_gap {h f : Spatial → ℝ} (hf : LongEnvelopeData h f) :
    Measurable (fun p : ((ℝ × OverlapSphere) × Spatial) × ℝ =>
      max 0 (twoFaceRayGap h f p.1.2 p.1.1.2 p.1.1.1 p.2)) := by
  have hh := hf.toRegularHeight.continuous_positivePart.measurable
  have hff := hf.strictGraphLipschitz_upper.continuous.measurable
  unfold twoFaceRayGap twoFaceGap
  apply Measurable.max measurable_const
  exact ((hh.comp (measurable_snd.comp measurable_fst)).add
    (hff.comp ((measurable_snd.comp measurable_fst).add
      (measurable_spatialPolar.comp
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (by fun_prop)))))).sub
      (hff.comp (measurable_snd.comp measurable_fst)) |>.sub (by fun_prop)

/-- Joint measurability, including the Jacobian and the closed cutoff. -/
theorem LongEnvelopeData.measurable_longGapIntegrand {h f : Spatial → ℝ}
    (hf : LongEnvelopeData h f) (δ : ℝ) :
    Measurable (fun p : ((ℝ × OverlapSphere) × Spatial) × ℝ =>
      (Ici δ).indicator (fun v =>
        ENNReal.ofReal ((v - p.1.1.1 / v)^2 / (8*v)) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f p.1.2 p.1.1.2 p.1.1.1 v))) p.2) := by
  have hm : Measurable (fun p : ((ℝ × OverlapSphere) × Spatial) × ℝ =>
      ENNReal.ofReal (gapWeight p.1.1.1 p.2) *
        ENNReal.ofReal (max 0 (twoFaceRayGap h f p.1.2 p.1.1.2 p.1.1.1 p.2))) :=
    (by unfold gapWeight; fun_prop : Measurable (fun p : ((ℝ × OverlapSphere) × Spatial) × ℝ =>
      ENNReal.ofReal (gapWeight p.1.1.1 p.2))).mul (measurable_gap hf).ennreal_ofReal
  simpa only [← indicator_comp_right, Function.comp_def] using
    hm.indicator (measurableSet_Ici.preimage measurable_snd)

/-- The positive spatial gap is integrable at every causal displacement. -/
private theorem gap_integrable {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) :
    Integrable (fun x : Spatial => max 0 (twoFaceGap h f x (x + a) s)) := by
  have hc : Continuous (fun x : Spatial => max 0 (twoFaceGap h f x (x + a) s)) := by
    unfold twoFaceGap
    exact (continuous_const.max (((hf.toRegularHeight.continuous_positivePart).add
      (hf.strictGraphLipschitz_upper.continuous.comp (continuous_id.add continuous_const))).sub
      hf.strictGraphLipschitz_upper.continuous |>.sub continuous_const))
  have hle (x : Spatial) : max 0 (twoFaceGap h f x (x + a) s) ≤ max 0 (h x) := by
    obtain ⟨η, hη, hη1, hfl⟩ := hf.strictGraphLipschitz_upper
    have hd := spatialDistance_le_of_causalFuture 0 (Fin.cons s a) hz
    have he : spatialDistance (x + a) x = spatialDistance (spatialPart 0) a := by
      apply (sq_eq_sq₀ (spatialDistance_nonneg _ _) (spatialDistance_nonneg _ _)).mp
      simp [spatialDistance_sq, spatialPart]
    have hs : f (x + a) - f x ≤ s := by
      calc
        _ ≤ |f (x + a) - f x| := le_abs_self _
        _ ≤ η * spatialDistance (x + a) x := hfl _ _
        _ ≤ spatialDistance (spatialPart 0) a := by
          rw [he]
          exact mul_le_of_le_one_left (spatialDistance_nonneg _ _) hη1.le
        _ ≤ s := by simpa using hd
    simp only [twoFaceGap]
    exact max_le (le_max_left _ _) (by linarith)
  have hi : Integrable (fun x : Spatial => max 0 (h x)) :=
    hf.toRegularHeight.continuous_positivePart.integrable_of_hasCompactSupport
      hf.toRegularHeight.hasCompactSupport_positivePart
  apply Integrable.mono' hi hc.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ max 0 (twoFaceGap h f x (x + a) s) from le_max_left _ _),
    abs_of_nonneg (show 0 ≤ max 0 (h x) from le_max_left _ _)] using hle x

/-- The lower endpoint is δ on this proved right neighborhood only. -/
theorem max_cutoff_sqrt_eq {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) : max δ (Real.sqrt σ) = δ := by
  apply max_eq_left
  have hr := Real.sqrt_nonneg σ
  have hsq := Real.sq_sqrt hσ
  nlinarith

private theorem ray_causal {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) (hv : δ ≤ v) (ω : OverlapSphere) :
    properTimeDisplacement ω ![σ,v] ∈ causalFuture 0 := by
  have hv0 : 0 < v := hδ.trans_le hv
  have hsq : σ ≤ v ^ 2 := le_of_lt (lt_of_lt_of_le hs (by nlinarith))
  have hr : 0 ≤ (v - σ / v) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact sub_nonneg.mpr ((div_le_iff₀ hv0).mpr (by nlinarith))
  have ht : (v - σ / v) / 2 ≤ (v + σ / v) / 2 := by
    have : 0 ≤ σ / v := div_nonneg hσ hv0.le
    linarith
  have hp := (polar_mem_longFuture (δ := δ) (t := (v + σ / v)/2)
    (r := (v - σ / v)/2) ω hr).mpr
    (show ![(v + σ / v)/2,(v - σ / v)/2] ∈ longRadialDomain δ by
      simpa only [longRadialDomain, mem_setOf_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] using
          (show 0 ≤ (v - σ/v)/2 ∧ (v - σ/v)/2 ≤ (v + σ/v)/2 ∧
            δ ≤ (v + σ/v)/2 + (v - σ/v)/2 from ⟨hr, ht, by linarith⟩))
  exact hp.1

/-- The x-integral conversion is pointwise, not merely almost everywhere in σ.
Its finite value follows from compact support of the original cap envelope. -/
theorem LongEnvelopeData.ofReal_integral_gap_eq_lintegral {h f : Spatial → ℝ}
    (hf : LongEnvelopeData h f) {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) (hv : δ ≤ v) (ω : OverlapSphere) :
    ENNReal.ofReal (∫ x : Spatial, max 0 (twoFaceRayGap h f x ω σ v)) =
      ∫⁻ x : Spatial, ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v)) := by
  have hz := ray_causal hδ hσ hs hv ω
  have hi := gap_integrable hf hz
  have hn : ∀ x : Spatial, 0 ≤ max 0 (twoFaceRayGap h f x ω σ v) :=
    fun _ => le_max_left _ _
  exact ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)

/-- The spatial gap lintegral is finite for each admissible ray, not just a.e.
in direction or proper-time square. -/
theorem LongEnvelopeData.lintegral_gap_lt_top {h f : Spatial → ℝ}
    (hf : LongEnvelopeData h f) {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) (hv : δ ≤ v) (ω : OverlapSphere) :
    (∫⁻ x : Spatial, ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) < ⊤ := by
  rw [← hf.ofReal_integral_gap_eq_lintegral hδ hσ hs hv ω]
  exact ENNReal.ofReal_lt_top

/-- Tonelli is applied to the nonnegative gap BEFORE any real-valued Fubini.
The spatial integral is converted only after proving its integrability. -/
theorem LongEnvelopeData.longOverlapDensityENN_eq_gap_fibres {h f : Spatial → ℝ}
    (hf : LongEnvelopeData h f) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) :
    longOverlapDensityENN (twoFaceRegion h f) δ σ =
      ∫⁻ ω, (∫⁻ x : Spatial, ∫⁻ v in Ici δ,
        ENNReal.ofReal ((v - σ/v)^2 / (8*v)) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v)))
        ∂overlapSphereMeasure := by
  rw [longOverlapDensityENN_eq_average _ hδ hσ, max_cutoff_sqrt_eq hδ hσ hs]
  have hj (v : ℝ) (hv : δ ≤ v) : 0 ≤ gapWeight σ v := by
    unfold gapWeight
    exact div_nonneg (sq_nonneg _) (by have : 0 < v := hδ.trans_le hv; positivity)
  have hswap (ω : OverlapSphere) :
      (∫⁻ v in Ici δ, ∫⁻ x : Spatial,
        ENNReal.ofReal (gapWeight σ v) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) =
      ∫⁻ x : Spatial, ∫⁻ v in Ici δ,
        ENNReal.ofReal (gapWeight σ v) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v)) := by
    have hmeas : Measurable (fun p : Spatial × ℝ =>
        ENNReal.ofReal (gapWeight σ p.2) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f p.1 ω σ p.2))) :=
      (by
        have hg : Measurable (fun p : Spatial × ℝ =>
            max 0 (twoFaceRayGap h f p.1 ω σ p.2)) :=
          (measurable_gap hf).comp
            (((measurable_const.prodMk measurable_const).prodMk measurable_fst).prodMk measurable_snd)
        exact (by unfold gapWeight; fun_prop : Measurable (fun p : Spatial × ℝ =>
          ENNReal.ofReal (gapWeight σ p.2))).mul hg.ennreal_ofReal)
    exact (lintegral_lintegral_swap (μ := (volume : Measure Spatial))
      (ν := volume.restrict (Ici δ))
      (f := fun x v => ENNReal.ofReal (gapWeight σ v) *
        ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) hmeas.aemeasurable).symm
  simp only [gapWeight] at hswap
  apply lintegral_congr
  intro ω
  rw [← hswap ω]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
  have he := hf.translatedOverlap_eq_gap (ray_causal hδ hσ hs hv ω)
  have he' : translatedOverlap (twoFaceRegion h f) (properTimeDisplacement ω ![σ,v]) =
      ∫ x : Spatial, max 0 (twoFaceRayGap h f x ω σ v) := by
    simpa only [properTimeDisplacement, twoFaceRayGap, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] using he
  have hi := hf.ofReal_integral_gap_eq_lintegral hδ hσ hs hv ω
  rw [he', hi]
  change ENNReal.ofReal (gapWeight σ v) * _ = _
  have hg : Measurable (fun x : Spatial =>
      ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) :=
    ((measurable_gap hf).comp
      (((measurable_const.prodMk measurable_const).prodMk measurable_id).prodMk measurable_const)).ennreal_ofReal
  exact (lintegral_const_mul _ hg).symm

private def fibreENN (h f : Spatial → ℝ) (δ σ : ℝ) (ω : OverlapSphere)
    (x : Spatial) : ℝ≥0∞ :=
  ∫⁻ v in Ici δ, ENNReal.ofReal (gapWeight σ v) *
    ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))

private def spatialENN (h f : Spatial → ℝ) (δ σ : ℝ) (ω : OverlapSphere) : ℝ≥0∞ :=
  ∫⁻ x : Spatial, fibreENN h f δ σ ω x

/-- Finiteness is established before converting the threefold integral to ℝ. -/
theorem LongEnvelopeData.longOverlapDensity_eq_gap_fibres {h f : Spatial → ℝ}
    (hf : LongEnvelopeData h f) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ ω, (∫ x : Spatial, ∫ v in Ici δ,
        ((v - σ/v)^2 / (8*v)) * max 0 (twoFaceRayGap h f x ω σ v))
        ∂overlapSphereMeasure := by
  have he := hf.longOverlapDensityENN_eq_gap_fibres hδ hσ hs
  have ht := hf.longOverlapDensityENN_lt_top hδ σ
  have hj (v : ℝ) (hv : v ∈ Ici δ) : 0 ≤ gapWeight σ v := by
    unfold gapWeight
    exact div_nonneg (sq_nonneg _) (by have : 0 < v := hδ.trans_le hv; positivity)
  have hF : Measurable (fun p : (OverlapSphere × Spatial) × ℝ =>
      (Ici δ).indicator (fun v => ENNReal.ofReal (gapWeight σ v) *
        ENNReal.ofReal (max 0 (twoFaceRayGap h f p.1.2 p.1.1 σ v))) p.2) := by
    have hmap : Measurable (fun p : (OverlapSphere × Spatial) × ℝ =>
        (((σ, p.1.1), p.1.2), p.2)) := by fun_prop
    exact (hf.measurable_longGapIntegrand δ).comp hmap
  have hX : Measurable (fun p : OverlapSphere × Spatial =>
      fibreENN h f δ σ p.1 p.2) := by
    simpa only [fibreENN, ← lintegral_indicator measurableSet_Ici] using
      (hF.lintegral_prod_right' (ν := (volume : Measure ℝ)))
  have hΩ : Measurable (spatialENN h f δ σ) := by
    exact hX.lintegral_prod_right' (ν := (volume : Measure Spatial))
  have hfin : (∫⁻ ω, spatialENN h f δ σ ω ∂overlapSphereMeasure) < ⊤ := by
    rw [he] at ht
    exact ht
  have hωfin : ∀ᵐ ω ∂overlapSphereMeasure, spatialENN h f δ σ ω < ⊤ :=
    ae_lt_top hΩ hfin.ne
  have hinner (ω : OverlapSphere) (x : Spatial) :
      (∫ v in Ici δ, gapWeight σ v * max 0 (twoFaceRayGap h f x ω σ v)) =
        (fibreENN h f δ σ ω x).toReal := by
    have hsection : Measurable (fun v : ℝ =>
        (Ici δ).indicator (fun v => ENNReal.ofReal (gapWeight σ v) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) v) :=
      hF.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
    have hpoint (v : ℝ) :
        ((Ici δ).indicator (fun v => ENNReal.ofReal (gapWeight σ v) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) v).toReal =
          (Ici δ).indicator (fun v => gapWeight σ v *
            max 0 (twoFaceRayGap h f x ω σ v)) v := by
      by_cases hv : v ∈ Ici δ
      · simp only [indicator_of_mem hv, ← ENNReal.ofReal_mul (hj v hv),
          ENNReal.toReal_ofReal (mul_nonneg (hj v hv) (le_max_left _ _))]
      · simp only [indicator_of_not_mem hv, ENNReal.toReal_zero]
    rw [← integral_indicator measurableSet_Ici]
    simp_rw [← hpoint]
    simpa only [fibreENN, ← lintegral_indicator measurableSet_Ici] using
      (integral_toReal (μ := (volume : Measure ℝ)) hsection.aemeasurable
      (Filter.Eventually.of_forall fun v => by
        by_cases hv : v ∈ Ici δ
        · simp only [indicator_of_mem hv]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
        · simp [hv]))
  have hspatial (ω : OverlapSphere) (hw : spatialENN h f δ σ ω < ⊤) :
      (∫ x : Spatial, ∫ v in Ici δ,
        gapWeight σ v * max 0 (twoFaceRayGap h f x ω σ v)) =
        (spatialENN h f δ σ ω).toReal := by
    simp_rw [hinner ω]
    have hx : Measurable (fibreENN h f δ σ ω) :=
      hX.comp (measurable_const.prodMk measurable_id)
    exact integral_toReal hx.aemeasurable (ae_lt_top hx hw.ne)
  rw [longOverlapDensity, he]
  change (∫⁻ ω, spatialENN h f δ σ ω ∂overlapSphereMeasure).toReal = _
  have hreal : (∫ ω, (spatialENN h f δ σ ω).toReal ∂overlapSphereMeasure) =
      (∫⁻ ω, spatialENN h f δ σ ω ∂overlapSphereMeasure).toReal :=
    integral_toReal hΩ.aemeasurable hωfin
  rw [← hreal]
  apply integral_congr_ae
  filter_upwards [hωfin] with ω hw
  exact (hspatial ω hw).symm

/-- Under uniform upper clearance the finite closed fibre equals the
untruncated one. The direction/spatial order and full sphere measure persist. -/
theorem LongEnvelopeData.longOverlapDensity_eq_gap_fibres_Icc {h f : Spatial → ℝ}
    (hf : LongEnvelopeData h f) {δ σ V : ℝ} (hδ : 0 < δ)
    (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ (ω : OverlapSphere) (x : Spatial) (v : ℝ), V < v →
      twoFaceRayGap h f x ω σ v ≤ 0) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ ω, (∫ x : Spatial, ∫ v in Icc δ V,
        ((v - σ/v)^2 / (8*v)) * max 0 (twoFaceRayGap h f x ω σ v))
        ∂overlapSphereMeasure := by
  rw [hf.longOverlapDensity_eq_gap_fibres hδ hσ hs]
  apply integral_congr_ae
  filter_upwards with ω
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : v ∈ Icc δ V
  · rw [indicator_of_mem hv, indicator_of_mem (show v ∈ Ici δ from hv.1)]
  · rw [indicator_of_not_mem hv]
    by_cases hlow : v ∈ Ici δ
    · rw [indicator_of_mem hlow]
      have : V < v := lt_of_not_ge (fun h => hv ⟨hlow, h⟩)
      rw [max_eq_left (hclear ω x v this), mul_zero]
    · rw [indicator_of_not_mem hlow]

/- Original contracts and callers are retained verbatim as specializations. -/
namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem measurable_longGapIntegrand (δ : ℝ) :
    Measurable (fun p : ((ℝ × OverlapSphere) × Spatial) × ℝ =>
      (Ici δ).indicator (fun v =>
        ENNReal.ofReal ((v - p.1.1.1 / v)^2 / (8*v)) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f p.1.2 p.1.1.2 p.1.1.1 v))) p.2) :=
  hf.toLongEnvelopeData.measurable_longGapIntegrand δ

theorem ofReal_integral_gap_eq_lintegral {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) (hv : δ ≤ v) (ω : OverlapSphere) :
    ENNReal.ofReal (∫ x : Spatial, max 0 (twoFaceRayGap h f x ω σ v)) =
      ∫⁻ x : Spatial, ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v)) :=
  hf.toLongEnvelopeData.ofReal_integral_gap_eq_lintegral hδ hσ hs hv ω

theorem lintegral_gap_lt_top {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) (hv : δ ≤ v) (ω : OverlapSphere) :
    (∫⁻ x : Spatial, ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v))) < ⊤ :=
  hf.toLongEnvelopeData.lintegral_gap_lt_top hδ hσ hs hv ω

theorem longOverlapDensityENN_eq_gap_fibres {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) :
    longOverlapDensityENN (twoFaceRegion h f) δ σ =
      ∫⁻ ω, (∫⁻ x : Spatial, ∫⁻ v in Ici δ,
        ENNReal.ofReal ((v - σ/v)^2 / (8*v)) *
          ENNReal.ofReal (max 0 (twoFaceRayGap h f x ω σ v)))
        ∂overlapSphereMeasure :=
  hf.toLongEnvelopeData.longOverlapDensityENN_eq_gap_fibres hδ hσ hs

theorem longOverlapDensity_eq_gap_fibres {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ ω, (∫ x : Spatial, ∫ v in Ici δ,
        ((v - σ/v)^2 / (8*v)) * max 0 (twoFaceRayGap h f x ω σ v))
        ∂overlapSphereMeasure :=
  hf.toLongEnvelopeData.longOverlapDensity_eq_gap_fibres hδ hσ hs

theorem longOverlapDensity_eq_gap_fibres_Icc {δ σ V : ℝ} (hδ : 0 < δ)
    (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ (ω : OverlapSphere) (x : Spatial) (v : ℝ), V < v →
      twoFaceRayGap h f x ω σ v ≤ 0) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ ω, (∫ x : Spatial, ∫ v in Icc δ V,
        ((v - σ/v)^2 / (8*v)) * max 0 (twoFaceRayGap h f x ω σ v))
        ∂overlapSphereMeasure :=
  hf.toLongEnvelopeData.longOverlapDensity_eq_gap_fibres_Icc hδ hσ hs hclear

end AdmissibleTwoFace
end BoundaryDraft
