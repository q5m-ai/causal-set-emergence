import BoundaryDraft.TwoFaceLongGeometry
import BoundaryDraft.TwoFaceLongDisintegration
import BoundaryDraft.AveragedQuadraticJet
import BoundaryDraft.NullTransverseCancellation

/-!
# Fixed-cutoff cancellation for the actual long-overlap contribution

The geometric fibre jets are averaged on a compact active spatial set. Three
fixed positive probes establish coefficient integrability without measurable
root selection or continuity at cutoff contact. Nonnegative disintegration
supplies integrability before real Fubini. No admissibility, density, kernel,
or action definition is changed.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval ENNReal

set_option maxHeartbeats 1000000

noncomputable section
namespace BoundaryDraft

namespace TwoFaceLongNull

/-- Three fixed probes recover integrable coefficients from integrable fibres
and a common integrable normalized-remainder bound. No root is selected. -/
theorem integrable_coefficients_of_three_probes
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : α → ℝ → ℝ) (C0 C1 C2 D : α → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hF : ∀ σ ∈ Ioc 0 ε, Integrable (fun a => F a σ) μ)
    (hm : Measurable C0 ∧ Measurable C1 ∧ Measurable C2)
    (hD : Integrable D μ)
    (hb : ∀ a, ∀ σ ∈ Ioc 0 ε,
      |F a σ - (C0 a + C1 a * σ + C2 a * σ ^ 2)| / σ ^ 2 ≤ D a) :
    Integrable C0 μ ∧ Integrable C1 μ ∧ Integrable C2 μ := by
  let P := fun (σ : ℝ) (a : α) => C0 a + C1 a * σ + C2 a * σ ^ 2
  have hi (σ : ℝ) (hσ : σ ∈ Ioc 0 ε) : Integrable (P σ) μ := by
    have hR : Integrable (fun a => F a σ - P σ a) μ := by
      apply (hD.mul_const (σ ^ 2)).mono'
        ((hF σ hσ).aestronglyMeasurable.sub
          (((hm.1.add (hm.2.1.mul_const σ)).add
            (hm.2.2.mul_const (σ ^ 2))).aestronglyMeasurable))
      filter_upwards with a
      simpa only [Real.norm_eq_abs] using
        (div_le_iff₀ (sq_pos_of_pos hσ.1)).mp (hb a σ hσ)
    apply ((hF σ hσ).sub hR).congr
    filter_upwards with a
    dsimp [P]
    ring
  let s := ε / 3
  have hs : s ≠ 0 := ne_of_gt (by dsimp [s]; positivity)
  have h1 := hi s (by dsimp [s]; constructor <;> linarith)
  have h2 := hi (2 * s) (by dsimp [s]; constructor <;> linarith)
  have h3 := hi (3 * s) (by dsimp [s]; constructor <;> linarith)
  refine ⟨?_, ?_, ?_⟩
  · apply (((h1.const_mul 3).sub (h2.const_mul 3)).add h3).congr
    filter_upwards with a
    dsimp [P]
    ring
  · apply ((((h1.const_mul (-5)).add (h2.const_mul 8)).sub
      (h3.const_mul 3)).div_const (2 * s)).congr
    filter_upwards with a
    dsimp [P]
    field_simp
    ring
  · apply (((h1.sub (h2.const_mul 2)).add h3).div_const (2 * s ^ 2)).congr
    filter_upwards with a
    dsimp [P]
    field_simp
    ring

abbrev Parameter := OverlapSphere × Spatial

/-- The actual nonnegative integrand with both finite length cutoffs. -/
def integrandENN (h f : Spatial → ℝ) (δ V σ : ℝ) (p : Parameter × ℝ) : ℝ≥0∞ :=
  (Icc δ V).indicator (fun v =>
    ENNReal.ofReal (TwoFaceLongGeometry.weight σ v) *
      ENNReal.ofReal (max 0 (twoFaceRayGap h f p.1.2 p.1.1 σ v))) p.2

def fibreENN (h f : Spatial → ℝ) (δ V σ : ℝ) (p : Parameter) : ℝ≥0∞ :=
  ∫⁻ v, integrandENN h f δ V σ (p, v)

namespace Envelope

/-- WP3's joint measurability, with only the additional upper cutoff. -/
theorem measurable_integrandENN {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
    (δ V σ : ℝ) : Measurable (integrandENN h f δ V σ) := by
  have hmap : Measurable (fun p : Parameter × ℝ => (((σ, p.1.1), p.1.2), p.2)) := by
    fun_prop
  have hm := ((hf.measurable_longGapIntegrand δ).comp hmap).indicator
    ((measurableSet_Iic (a := V)).preimage (measurable_snd (α := Parameter)))
  convert hm using 1
  funext p
  by_cases hlo : δ ≤ p.2 <;> by_cases hhi : p.2 ≤ V <;>
    simp [integrandENN, TwoFaceLongGeometry.weight, hlo, hhi, mem_Icc, mem_Ici, mem_Iic]

theorem measurable_fibreENN {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
    (δ V σ : ℝ) : Measurable (fibreENN h f δ V σ) :=
  (measurable_integrandENN hf δ V σ).lintegral_prod_right'

/-- Oriented `δ..V` equals closed `Icc δ V` because δ ≤ V and Lebesgue
endpoints are null. The ENNReal conversion is pointwise in every parameter. -/
theorem fibre_eq_toReal {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
    {δ V : ℝ} (hδ : 0 < δ) (hV : δ ≤ V) (σ : ℝ) (p : Parameter) :
    MonotoneHinge.fibre (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ =
      (fibreENN h f δ V σ p).toReal := by
  have hm := (measurable_integrandENN hf δ V σ).comp
    ((measurable_const (a := p)).prodMk measurable_id)
  have hpoint (v : ℝ) : (integrandENN h f δ V σ (p, v)).toReal =
      (Icc δ V).indicator (fun v => TwoFaceLongGeometry.weight σ v *
        max 0 (twoFaceRayGap h f p.2 p.1 σ v)) v := by
    by_cases hv : v ∈ Icc δ V
    · have hw : 0 ≤ TwoFaceLongGeometry.weight σ v :=
        div_nonneg (sq_nonneg _) (by have := hδ.trans_le hv.1; positivity)
      simp only [integrandENN, indicator_of_mem hv, ← ENNReal.ofReal_mul hw,
        ENNReal.toReal_ofReal (mul_nonneg hw (le_max_left _ _))]
    · simp [integrandENN, hv]
  rw [MonotoneHinge.fibre_eq_setIntegral _ _ hV,
    ← integral_indicator measurableSet_Icc]
  simp_rw [← hpoint]
  exact integral_toReal hm.aemeasurable (Eventually.of_forall fun v => by
    by_cases hv : v ∈ Icc δ V
    · simp only [integrandENN, indicator_of_mem hv]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · simp [integrandENN, hv])

/-- Tonelli and WP3's finite triple identity dominate the finite fibre integral
on the UNRESTRICTED direction × spatial parameter space. -/
theorem lintegral_fibreENN_lt_top {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) (V : ℝ) :
    (∫⁻ p, fibreENN h f δ V σ p ∂(overlapSphereMeasure.prod volume)) < ⊤ := by
  rw [lintegral_prod _ (measurable_fibreENN hf δ V σ).aemeasurable]
  apply lt_of_le_of_lt _ (hf.longOverlapDensityENN_lt_top hδ σ)
  rw [hf.longOverlapDensityENN_eq_gap_fibres hδ hσ hs]
  apply lintegral_mono
  intro ω
  apply lintegral_mono
  intro x
  change (∫⁻ v, integrandENN h f δ V σ ((ω, x), v)) ≤ _
  simp only [integrandENN, lintegral_indicator measurableSet_Icc]
  exact lintegral_mono_set Icc_subset_Ici_self

/-- Measurability and absolute integrability are proved before real Fubini. -/
theorem measurable_integrable_fibre {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
    {δ V σ : ℝ} (hδ : 0 < δ) (hV : δ ≤ V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) :
    Measurable (fun p : Parameter => MonotoneHinge.fibre
      (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ) ∧
    Integrable (fun p : Parameter => MonotoneHinge.fibre
      (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ)
      (overlapSphereMeasure.prod volume) := by
  simp_rw [fibre_eq_toReal hf hδ hV]
  exact ⟨(measurable_fibreENN hf δ V σ).ennreal_toReal,
    integrable_toReal_of_lintegral_ne_top (measurable_fibreENN hf δ V σ).aemeasurable
      (lintegral_fibreENN_lt_top hf hδ hσ hs V).ne⟩

end Envelope

/- Original helper contracts remain available. -/
theorem measurable_integrandENN {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (δ V σ : ℝ) : Measurable (integrandENN h f δ V σ) :=
  Envelope.measurable_integrandENN hf.toLongEnvelopeData δ V σ

theorem measurable_fibreENN {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (δ V σ : ℝ) : Measurable (fibreENN h f δ V σ) :=
  Envelope.measurable_fibreENN hf.toLongEnvelopeData δ V σ

theorem fibre_eq_toReal {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ V : ℝ} (hδ : 0 < δ) (hV : δ ≤ V) (σ : ℝ) (p : Parameter) :
    MonotoneHinge.fibre (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ =
      (fibreENN h f δ V σ p).toReal :=
  Envelope.fibre_eq_toReal hf.toLongEnvelopeData hδ hV σ p

theorem lintegral_fibreENN_lt_top {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) (V : ℝ) :
    (∫⁻ p, fibreENN h f δ V σ p ∂(overlapSphereMeasure.prod volume)) < ⊤ :=
  Envelope.lintegral_fibreENN_lt_top hf.toLongEnvelopeData hδ hσ hs V

theorem measurable_integrable_fibre {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ V σ : ℝ} (hδ : 0 < δ) (hV : δ ≤ V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) :
    Measurable (fun p : Parameter => MonotoneHinge.fibre
      (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ) ∧
    Integrable (fun p : Parameter => MonotoneHinge.fibre
      (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ)
      (overlapSphereMeasure.prod volume) :=
  Envelope.measurable_integrable_fibre hf.toLongEnvelopeData hδ hV hσ hs

end TwoFaceLongNull

/-- The actual density vanishes on the negative half-line. Its point value at
zero need not be identified with any expansion coefficient. -/
theorem integral_longOverlapDensity_eq_Ioi (M : Set Spacetime) (δ : ℝ) (w : ℝ → ℝ) :
    (∫ σ : ℝ, w σ * longOverlapDensity M δ σ) =
      ∫ σ : ℝ in Ioi 0, w σ * longOverlapDensity M δ σ := by
  rw [← integral_Ici_eq_integral_Ioi]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro σ hσ
  have hneg : σ < 0 := lt_of_not_ge hσ
  simp [longOverlapDensity, longOverlapDensityENN_negative M δ hneg]

namespace LongEnvelopeData

variable {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
include hf

/-- Exact pointwise product-space identification on the entire range
`0 ≤ σ < δ²`, including zero. Finiteness precedes real Fubini, and the
oriented/closed interval replacement removes only a Lebesgue-null endpoint. -/
theorem longOverlapDensity_eq_parameterFibre {δ V σ : ℝ}
    (hδ : 0 < δ) (hV : δ < V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ (x : Spatial) (ω : OverlapSphere), twoFaceRayGap h f x ω 0 V ≤ 0) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ p : TwoFaceLongNull.Parameter, MonotoneHinge.fibre
        (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ
        ∂(overlapSphereMeasure.prod volume) := by
  obtain ⟨η, _, hη, hlip⟩ := hf.strictGraphLipschitz_upper
  have ht (ω : OverlapSphere) (x : Spatial) (v : ℝ) (hv : V < v) :
      twoFaceRayGap h f x ω σ v ≤ 0 :=
    twoFaceRayGap_nonpos_of_cutoff hη hlip h x ω (hδ.trans hV) hσ hv.le (hclear x ω)
  rw [integral_prod _ (TwoFaceLongNull.Envelope.measurable_integrable_fibre hf hδ hV.le hσ hs).2,
    hf.longOverlapDensity_eq_gap_fibres_Icc hδ hσ hs ht]
  apply integral_congr_ae
  filter_upwards with ω
  apply integral_congr_ae
  filter_upwards with x
  exact (MonotoneHinge.fibre_eq_setIntegral (twoFaceRayGap h f x ω)
    TwoFaceLongGeometry.weight hV.le σ).symm

/-- The unchanged actual density has a right quadratic jet for EVERY fixed
positive cutoff. The finite active domain, coefficient integrability, common
neighborhood, and pointwise (not merely a.e.) density identity are derived. -/
theorem longOverlapDensity_right_quadratic_jet {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 b2 : ℝ,
      (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
        (b0 + b1 * σ + b2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, hc, hA, hM, hB, hall⟩ :=
    TwoFaceLongGeometry.Envelope.exists_hypotheses hf hδ
  let e := min ε (δ ^ 2 / 2)
  have he : 0 < e := lt_min hε (by positivity)
  have hsmall {σ : ℝ} (hσ : σ ∈ Ioc 0 e) : σ ∈ Ioc 0 ε ∧ σ < δ ^ 2 := by
    have hle := hσ.2.trans (min_le_right ε (δ ^ 2 / 2))
    exact ⟨⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩, by nlinarith [sq_pos_of_pos hδ]⟩
  let F := fun (p : TwoFaceLongNull.Parameter) σ => MonotoneHinge.fibre
    (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ
  let C0 := fun p : TwoFaceLongNull.Parameter => MonotoneHinge.F0
    (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V
  let C1 := fun p : TwoFaceLongNull.Parameter => MonotoneHinge.F1
    (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V
  let C2 := fun p : TwoFaceLongNull.Parameter => MonotoneHinge.F2
    (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V
  let D := MonotoneHinge.remainderBound δ V c A M B
  have hD0 : 0 ≤ D := by
    dsimp [D, MonotoneHinge.remainderBound]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (sub_nonneg.mpr hV.le))
      (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hM (sq_nonneg A)) hc.le))
  have hj (p : TwoFaceLongNull.Parameter) :
      (fun σ => F p σ - (C0 p + C1 p * σ + C2 p * σ ^ 2)) =o[𝓝[>] 0]
        (fun σ => σ ^ 2) := (hall p.2 p.1).right_quadratic_jet
  have hb (p : TwoFaceLongNull.Parameter) (σ : ℝ) (hσ : σ ∈ Ioc 0 e) :
      |F p σ - (C0 p + C1 p * σ + C2 p * σ ^ 2)| / σ ^ 2 ≤ D :=
    (hall p.2 p.1).normalized_remainder_bound (hsmall hσ).1
  have hFi (σ : ℝ) (hσ : σ ∈ Ioc 0 e) :
      Measurable (fun p => F p σ) ∧
        Integrable (fun p => F p σ) (overlapSphereMeasure.prod volume) :=
    TwoFaceLongNull.Envelope.measurable_integrable_fibre hf hδ hV.le hσ.1.le (hsmall hσ).2
  have hm := AveragedQuadraticJet.measurable_coefficients_of_right_jet
    F C0 C1 C2 he (fun σ hσ => (hFi σ hσ).1) hj
  -- The endpoint-height margin supplies one compact active spatial set.
  obtain ⟨m, hmpos, hmargin⟩ := hf.exists_gap_height_margin
  let S : Set Spatial := (WithLp.equiv 2 (Fin 3 → ℝ)) ''
    TwoFaceLongGeometry.tube h (m * δ / 2)
  have hS : IsCompact S := (TwoFaceLongGeometry.compact_tube_of_regular hf.toRegularHeight _).image
    (PiLp.continuous_equiv 2 _)
  let P : Set TwoFaceLongNull.Parameter := univ ×ˢ S
  have hPm : MeasurableSet P := MeasurableSet.univ.prod hS.measurableSet
  have hPf : (overlapSphereMeasure.prod volume) P < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_lt_top _ _) hS.measure_lt_top
  let μ := (overlapSphereMeasure.prod volume).restrict P
  haveI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hPf⟩
  have hinactive (p : TwoFaceLongNull.Parameter) (hp : p ∉ P) :
      twoFaceRayGap h f p.2 p.1 0 δ ≤ 0 := by
    by_contra! hg
    have hx := (TwoFaceLongGeometry.old_endpoint_margin hmpos hδ hmargin p.2 p.1
      le_rfl hg.le).1
    have hxS : p.2 ∈ S := ⟨(WithLp.equiv 2 _).symm p.2,
      TwoFaceLongGeometry.mem_tube_of_margin (by positivity) _ hx, rfl⟩
    exact hp ⟨mem_univ _, hxS⟩
  -- All coefficients, including the discontinuous contact coefficient, and
  -- every small right fibre vanish off this finite-measure parameter set.
  have hCzero (p : TwoFaceLongNull.Parameter) (hp : p ∉ P) :
      C0 p = 0 ∧ C1 p = 0 ∧ C2 p = 0 :=
    MonotoneHinge.coefficients_zero (hinactive p hp)
  have hFzero (σ : ℝ) (hσ : σ ∈ Ioc 0 e) (p : TwoFaceLongNull.Parameter)
      (hp : p ∉ P) : F p σ = 0 :=
    (hall p.2 p.1).fibre_zero (hinactive p hp) (Ioc_subset_Icc_self (hsmall hσ).1)
  have hDi : Integrable (fun _p : TwoFaceLongNull.Parameter => D) μ := integrable_const D
  obtain ⟨hC0, hC1, hC2⟩ := TwoFaceLongNull.integrable_coefficients_of_three_probes
    F C0 C1 C2 (fun _ => D) he (fun σ hσ => (hFi σ hσ).2.integrableOn) hm hDi hb
  -- Extend coefficient integrability by zero to the actual full product
  -- measure. There is no assumption of coefficient continuity at contact.
  have extend (C : TwoFaceLongNull.Parameter → ℝ) (hi : Integrable C μ)
      (hz : ∀ p, p ∉ P → C p = 0) :
      Integrable C (overlapSphereMeasure.prod volume) := by
    apply ((show IntegrableOn C P (overlapSphereMeasure.prod volume) from hi).integrable_indicator
      hPm).congr
    filter_upwards with p
    by_cases hp : p ∈ P
    · simp [hp]
    · simp [hp, hz p hp]
  have hC0full := extend C0 hC0 (fun p hp => (hCzero p hp).1)
  have hC1full := extend C1 hC1 (fun p hp => (hCzero p hp).2.1)
  have hC2full := extend C2 hC2 (fun p hp => (hCzero p hp).2.2)
  -- The integrable dominator is an indicator, never a positive constant on
  -- all of Spatial. The fibre itself remains unrestricted in the average.
  let DP := P.indicator (fun _p : TwoFaceLongNull.Parameter => D)
  have hDP : Integrable DP (overlapSphereMeasure.prod volume) :=
    (show IntegrableOn (fun _p => D) P (overlapSphereMeasure.prod volume) from hDi).integrable_indicator
      hPm
  have hDP0 (p : TwoFaceLongNull.Parameter) : 0 ≤ DP p := by
    by_cases hp : p ∈ P <;> simp [DP, hp, hD0]
  have hbP (p : TwoFaceLongNull.Parameter) (σ : ℝ) (hσ : σ ∈ Ioc 0 e) :
      |F p σ - (C0 p + C1 p * σ + C2 p * σ ^ 2)| / σ ^ 2 ≤ DP p := by
    by_cases hp : p ∈ P
    · simpa only [DP, indicator_of_mem hp] using hb p σ hσ
    · obtain ⟨h0, h1, h2⟩ := hCzero p hp
      simp [DP, hp, hFzero σ hσ p hp, h0, h1, h2]
  have havg := AveragedQuadraticJet.averaged_right_quadratic_jet F C0 C1 C2
    DP he hj hbP hDP0 hDP (fun σ hσ => (hFi σ hσ).1)
    hm.1 hm.2.1 hm.2.2 hC0full hC1full hC2full
  refine ⟨∫ p, C0 p ∂(overlapSphereMeasure.prod volume),
    ∫ p, C1 p ∂(overlapSphereMeasure.prod volume),
    ∫ p, C2 p ∂(overlapSphereMeasure.prod volume), ?_⟩
  apply havg.congr' _ EventuallyEq.rfl
  filter_upwards [MonotoneHinge.eventually_right he] with σ hσ
  rw [hf.longOverlapDensity_eq_parameterFibre hδ hV hσ.1.le (hsmall hσ).2
    (fun x ω => (hall x ω).clearance.le)]

/-- Absolute integrability of the original long-displacement overlap integrand,
with the complete signed kernel and its unchanged interval coefficient. -/
theorem integrableOn_longOverlap_bdg (δ ρ : ℝ) :
    IntegrableOn (fun z => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) (longFuture δ) := by
  apply (hf.integrableOn_overlap_weight _ (by
    unfold bdgKernel bdgPolynomial intervalSq spatialSeparationSq
    fun_prop)).mono_set
  exact fun _ hz => hz.1

/-- Exact positive-half-line version of the existing whole-line identity.
Atomlessness removes only the endpoint, not any surrounding near-null layer. -/
theorem integral_longOverlap_bdg_Ioi {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ in Ioi 0, longOverlapDensity (twoFaceRegion h f) δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) := by
  rw [hf.integral_longOverlap_bdg hδ ρ, integral_longOverlapDensity_eq_Ioi]
  congr 1
  funext σ
  exact mul_comm _ _

/-- Absolute integrability on the half-line is discharged from geometry, not
left to a future caller of the conditional cancellation theorem. -/
theorem integrableOn_longOverlapDensity_bdg (δ ρ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ *
      bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (Ioi 0) := by
  have hi := hf.integrable_longOverlapDensity_weight hδ
    (fun σ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (by
      unfold bdgKernel bdgPolynomial
      fun_prop)
  simpa only [mul_comm] using hi.integrableOn (s := Ioi 0)

/-- Unconditional fixed-positive-cutoff geometric cancellation with the
original signed kernel, interval coefficient, and full pair normalization. -/
theorem tendsto_longOverlap {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  obtain ⟨b₀, b₁, b₂, hj⟩ := hf.longOverlapDensity_right_quadratic_jet hδ
  obtain ⟨C, _, hC⟩ := hf.bounded_longOverlapDensity hδ
  have he := bdgKernel_transverse_cancellation
    (longOverlapDensity (twoFaceRegion h f) δ) (hf.measurable_longOverlapDensity δ)
    C (fun σ _ => by simpa only [Real.norm_eq_abs] using hC σ)
    b₀ b₁ b₂ hj (Real.pi / 24) (by positivity)
  simpa only [← hf.integral_longOverlap_bdg_Ioi hδ] using he

/-- The signed contribution in the original action has BOTH density factors.
The point term and the short-displacement pair term are not included here. -/
theorem tendsto_normalized_longOverlap {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  have he := (hf.tendsto_longOverlap hδ).const_mul
    (-(4 / Real.sqrt 6))
  simp only [mul_zero] at he
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hp : ρ ^ (3 / 2 : ℝ) = Real.sqrt ρ * ρ := by
    calc
      _ = ρ ^ ((1 / 2 : ℝ) + 1) := by congr 1; norm_num
      _ = ρ ^ (1 / 2 : ℝ) * ρ ^ (1 : ℝ) := Real.rpow_add hρ _ _
      _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
  rw [hp]
  ring

end LongEnvelopeData

/- Preserve the original public theorem contracts and downstream callers. -/
namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem longOverlapDensity_eq_parameterFibre {δ V σ : ℝ}
    (hδ : 0 < δ) (hV : δ < V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ (x : Spatial) (ω : OverlapSphere), twoFaceRayGap h f x ω 0 V ≤ 0) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ p : TwoFaceLongNull.Parameter, MonotoneHinge.fibre
        (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V σ
        ∂(overlapSphereMeasure.prod volume) :=
  hf.toLongEnvelopeData.longOverlapDensity_eq_parameterFibre hδ hV hσ hs hclear

theorem longOverlapDensity_right_quadratic_jet {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 b2 : ℝ,
      (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
        (b0 + b1 * σ + b2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) :=
  hf.toLongEnvelopeData.longOverlapDensity_right_quadratic_jet hδ

theorem integrableOn_longOverlap_bdg (δ ρ : ℝ) :
    IntegrableOn (fun z => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) (longFuture δ) :=
  hf.toLongEnvelopeData.integrableOn_longOverlap_bdg δ ρ

theorem integral_longOverlap_bdg_Ioi {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ in Ioi 0, longOverlapDensity (twoFaceRegion h f) δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) :=
  hf.toLongEnvelopeData.integral_longOverlap_bdg_Ioi hδ ρ

theorem integrableOn_longOverlapDensity_bdg (δ ρ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ *
      bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (Ioi 0) :=
  hf.toLongEnvelopeData.integrableOn_longOverlapDensity_bdg δ ρ hδ

theorem tendsto_longOverlap {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) :=
  hf.toLongEnvelopeData.tendsto_longOverlap hδ

theorem tendsto_normalized_longOverlap {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) :=
  hf.toLongEnvelopeData.tendsto_normalized_longOverlap hδ

end AdmissibleTwoFace
end BoundaryDraft
