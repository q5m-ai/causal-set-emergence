import BoundaryDraft.TwoDCoordinates
import BoundaryDraft.MonotoneHingeIntegral

/-!
# Actual 2D long fibres satisfy the checked monotone-hinge theorem

All constants precede both source/direction quantifiers. The old-active compact
perturbation tube includes lost contacts and completely closing fibres. The
Jacobian is two-dimensional; no 4D analytic theorem is specialized as though
it were dimension-free. No interior height-gradient assumption is introduced.
-/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDLongGeometry

set_option maxHeartbeats 1000000

abbrev Parameters := ℝ × (ℝ × (ℝ × (TwoDSpace × TwoDSpace)))

def endpoint (p : Parameters) : TwoDSpace :=
  p.2.2.2.1 + ((p.2.1 - p.1 / p.2.1) / 2) • p.2.2.2.2

def gap (f : TwoDSpace → ℝ) (p : Parameters) : ℝ :=
  p.2.2.1 + f (endpoint p) - (p.2.1 + p.1 / p.2.1) / 2

def product (f : TwoDSpace → ℝ) (p : Parameters) : ℝ :=
  twoDNullJacobian p.1 p.2.1 * gap f p

def parameters (h f : TwoDSpace → ℝ) (x : TwoDSpace) (ω : TwoDDirection)
    (σ v : ℝ) : Parameters := (σ, v, max 0 (h x) - f x, x, ω.val)

def sigmaDirection : Parameters := (1, 0)

def first (f : TwoDSpace → ℝ) (p : Parameters) : ℝ := fderiv ℝ (product f) p sigmaDirection

def second (f : TwoDSpace → ℝ) (p : Parameters) : ℝ := fderiv ℝ (first f) p sigmaDirection

@[simp] theorem gap_parameters (h f : TwoDSpace → ℝ) (x : TwoDSpace) (ω : TwoDDirection)
    (σ v : ℝ) : gap f (parameters h f x ω σ v) = twoDRayGap h f x ω.val σ v := by
  dsimp [gap, endpoint, parameters, twoDRayGap, twoDOverlapGap, twoDRayDisplacement]
  ring

@[simp] theorem product_parameters (h f : TwoDSpace → ℝ) (x : TwoDSpace) (ω : TwoDDirection)
    (σ v : ℝ) : product f (parameters h f x ω σ v) =
      twoDNullJacobian σ v * twoDRayGap h f x ω.val σ v := by
  simp only [product, gap_parameters]
  rfl

theorem smooth_weight {σ v : ℝ} (hv : v ≠ 0) :
    ContDiffAt ℝ 3 (fun p : ℝ × ℝ => twoDNullJacobian p.1 p.2) (σ, v) :=
  contDiffAt_const.div (contDiffAt_const.mul contDiffAt_snd) (mul_ne_zero (by norm_num) hv)

theorem smooth_gap {f : TwoDSpace → ℝ} {p : Parameters} (hv : p.2.1 ≠ 0)
    (hf : ContDiffAt ℝ 3 f (endpoint p)) : ContDiffAt ℝ 3 (gap f) p := by
  have he : ContDiffAt ℝ 3 endpoint p :=
    contDiffAt_snd.snd.snd.fst.add
      (((contDiffAt_snd.fst.sub (contDiffAt_fst.div contDiffAt_snd.fst hv)).div_const 2).smul
        contDiffAt_snd.snd.snd.snd)
  exact (contDiffAt_snd.snd.fst.add (hf.comp p he)).sub
    ((contDiffAt_snd.fst.add (contDiffAt_fst.div contDiffAt_snd.fst hv)).div_const 2)

theorem smooth_product {f : TwoDSpace → ℝ} {p : Parameters} (hv : p.2.1 ≠ 0)
    (hf : ContDiffAt ℝ 3 f (endpoint p)) : ContDiffAt ℝ 3 (product f) p := by
  unfold product
  apply ContDiffAt.mul
  · exact (smooth_weight (σ := p.1) hv).comp (f := fun q : Parameters => (q.1, q.2.1))
      p (contDiffAt_fst.prodMk contDiffAt_snd.fst)
  · exact smooth_gap hv hf

theorem smooth_first {f : TwoDSpace → ℝ} {p : Parameters}
    (hp : ContDiffAt ℝ 3 (product f) p) : ContDiffAt ℝ 2 (first f) p :=
  (hp.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const

theorem continuous_second {f : TwoDSpace → ℝ} {p : Parameters}
    (hp : ContDiffAt ℝ 3 (product f) p) : ContinuousAt (second f) p :=
  (((smooth_first hp).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).continuousAt

private theorem parameters_deriv (h f : TwoDSpace → ℝ) (x : TwoDSpace) (ω : TwoDDirection)
    (σ v : ℝ) : HasDerivAt (fun s => parameters h f x ω s v) sigmaDirection σ :=
  (hasDerivAt_id σ).prodMk (hasDerivAt_const σ _)

theorem product_derivative {h f : TwoDSpace → ℝ} {x : TwoDSpace} {ω : TwoDDirection} {σ v : ℝ}
    (hp : ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v)) :
    HasDerivAt (fun s => twoDNullJacobian s v * twoDRayGap h f x ω.val s v)
      (first f (parameters h f x ω σ v)) σ := by
  simpa only [Function.comp_def, product_parameters] using
    (hp.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt σ (parameters_deriv h f x ω σ v)

theorem product_second_derivative {h f : TwoDSpace → ℝ} {x : TwoDSpace} {ω : TwoDDirection} {σ v : ℝ}
    (hp : ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v)) :
    HasDerivAt (fun s => MonotoneHinge.productD1 (twoDRayGap h f x ω.val) twoDNullJacobian s v)
      (second f (parameters h f x ω σ v)) σ := by
  have hd := ((smooth_first hp).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt σ
    (parameters_deriv h f x ω σ v)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(parameters_deriv h f x ω σ v).continuousAt.eventually (hp.eventually (by norm_num))]
    with s hs
  exact (product_derivative hs).deriv

theorem product_derivative_identities {h f : TwoDSpace → ℝ} {x : TwoDSpace}
    {ω : TwoDDirection} {σ v : ℝ} (hp : ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v)) :
    MonotoneHinge.productD1 (twoDRayGap h f x ω.val) twoDNullJacobian σ v =
      first f (parameters h f x ω σ v) ∧
    MonotoneHinge.productD2 (twoDRayGap h f x ω.val) twoDNullJacobian σ v =
      second f (parameters h f x ω σ v) :=
  ⟨(product_derivative hp).deriv, (product_second_derivative hp).deriv⟩

abbrev Index := (TwoDSpace × TwoDDirection) × (ℝ × ℝ)

def indexParameters (h f : TwoDSpace → ℝ) (p : Index) : Parameters :=
  parameters h f p.1.1 p.1.2 p.2.1 p.2.2

def activeBox (h f : TwoDSpace → ℝ) (a δ V ε : ℝ) : Set Index :=
  ((twoDHeightTube h a ×ˢ univ) ×ˢ (Icc 0 ε ×ˢ Icc δ V)) ∩
    {p | 0 ≤ twoDRayGap h f p.1.1 p.1.2.val 0 p.2.2}

theorem continuous_parameters {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    Continuous (indexParameters h f) := by
  change Continuous (fun p : Index => (p.2.1, p.2.2,
    max 0 (h p.1.1) - f p.1.1, p.1.1, p.1.2.val))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (((hf.continuous_positivePart.sub hf.continuous_future).comp continuous_fst.fst).prodMk
      (continuous_fst.fst.prodMk (continuous_subtype_val.comp continuous_fst.snd))))

theorem continuous_null {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) :
    Continuous (fun p : Index => twoDRayGap h f p.1.1 p.1.2.val 0 p.2.2) := by
  simp only [twoDRayGap, twoDOverlapGap, twoDRayDisplacement, zero_div, sub_zero, add_zero]
  exact (((hf.continuous_positivePart.comp continuous_fst.fst).add (hf.continuous_future.comp
    (continuous_fst.fst.add ((continuous_snd.snd.div_const 2).smul
      (continuous_subtype_val.comp continuous_fst.snd))))).sub
    (hf.continuous_future.comp continuous_fst.fst)).sub (continuous_snd.snd.div_const 2)

theorem compact_activeBox {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (a δ V ε : ℝ) :
    IsCompact (activeBox h f a δ V ε) :=
  (((hf.isCompact_heightTube a).prod isCompact_univ).prod (isCompact_Icc.prod isCompact_Icc)).inter_right
    (isClosed_le continuous_const (continuous_null hf))

/-- Common primitive hypotheses, all derived from the original pilot class. -/
theorem exists_hypotheses {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ε c A M B : ℝ, δ < V ∧ 0 < ε ∧ ε < δ ^ 2 ∧ 0 < c ∧ 0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (x : TwoDSpace) (ω : TwoDDirection),
        MonotoneHinge.Hypotheses (twoDRayGap h f x ω.val) twoDNullJacobian δ V ε c A M B := by
  obtain ⟨κ, η, ε, C, _, hε, hesq, htube⟩ := hf.exists_long_perturbationTube δ hδ
  obtain ⟨V₀, hV₀, hlength⟩ := hf.exists_long_length_bound
  let V := max δ V₀ + 1
  have hV : δ < V := by dsimp [V]; linarith [le_max_left δ V₀]
  have hVV : V₀ < V := by dsimp [V]; linarith [le_max_right δ V₀]
  have hm : 0 < 1 - κ - η := by linarith [C.budget]
  have hη : η < 1 := by linarith [C.height_nonneg, C.budget]
  have hη0 := C.future_nonneg
  let c := (1 - η) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let A := (1 + η) / (2 * δ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsmooth (x : TwoDSpace) (ω : TwoDDirection) {σ v : ℝ}
      (hσ : σ ∈ Icc 0 ε) (hv : v ∈ MonotoneHinge.active (twoDRayGap h f x ω.val) δ V) :
      ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v) :=
    smooth_product (ne_of_gt (hδ.trans_le hv.1.1))
      ((hf.future_smoothAt _ (htube x ω.val v σ (mem_sphere_zero_iff_norm.mp ω.property)
        hv.1.1 hσ hv.2).2.2.1).of_le (WithTop.coe_le_coe.mpr le_top))
  let K := activeBox h f ((1 - κ - η) * δ / 2) δ V ε
  have hK : IsCompact K := compact_activeBox hf _ _ _ _
  have hsK (p : Index) (hp : p ∈ K) : ContDiffAt ℝ 3 (product f) (indexParameters h f p) :=
    hsmooth p.1.1 p.1.2 hp.1.2.1 ⟨hp.1.2.2, hp.2⟩
  have hcont2 : ContinuousOn (fun p => second f (indexParameters h f p)) K := fun p hp =>
    ((continuous_second (hsK p hp)).comp (continuous_parameters hf).continuousAt).continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hcont2
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => twoDNullJacobian p.1 p.2)
      (Icc 0 ε ×ˢ Icc δ V) := fun _ hp =>
    (smooth_weight (ne_of_gt (hδ.trans_le hp.2.1))).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcontW
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨V, ε, c, A, M, B, hV, hε, hesq, hc, hA, hM, hB, ?_⟩
  intro x ω
  have hω : ‖ω.val‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hpc (σ : ℝ) : Continuous (fun v => parameters h f x ω σ v) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hz : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, hε.le⟩
  have hfuture {σ v : ℝ} (hσ : σ ∈ Icc 0 ε)
      (hv : v ∈ MonotoneHinge.active (twoDRayGap h f x ω.val) δ V) :
      ContDiffAt ℝ 3 f (endpoint (parameters h f x ω σ v)) :=
    (hf.future_smoothAt _ (htube x ω.val v σ hω hv.1.1 hσ hv.2).2.2.1).of_le (WithTop.coe_le_coe.mpr le_top)
  refine {
    cutoff_lt := hV, epsilon_pos := hε, transverse_pos := hc, speed_nonneg := hA,
    weight_nonneg := hM, second_nonneg := hB,
    null_continuous := ?_, null_decrease := ?_, clearance := ?_, nonopening := ?_,
    gap_continuous := ?_, weight_continuous := ?_, gap_differentiable := ?_,
    weight_continuousAt := ?_, product_deriv := ?_, product_deriv2 := ?_,
    first_continuous := ?_, second_continuous := ?_, weight_bound := ?_, second_bound := ?_ }
  · exact ((continuous_null hf).comp (show Continuous (fun v : ℝ => ((x, ω), (0, v))) from
      continuous_const.prodMk (continuous_const.prodMk continuous_id))).continuousOn
  · intro v _ w _ hvw
    have ht := C.nullGap_decrease hvw x ω.val hω
    dsimp [c]
    linarith
  · apply lt_of_not_ge
    intro hn
    exact (not_le_of_gt hVV) (hlength x ω.val V 0 hω (hδ.trans hV) le_rfl hn)
  · intro σ hσ v hv
    have ht := C.rayGap_sigma_bounds hσ.1 (hδ.trans_le hv.1) x ω.val hω
    have hlo : (1 + η) * σ / (2 * v) ≤ A * σ := by
      calc
        _ ≤ (1 + η) * σ / (2 * δ) := by
          apply div_le_div_of_nonneg_left (mul_nonneg (by linarith [C.future_nonneg]) hσ.1) (by positivity)
          linarith [hv.1]
        _ = _ := by dsimp [A]; ring
    have hhi : 0 ≤ (1 - η) * σ / (2 * v) :=
      div_nonneg (mul_nonneg (by linarith) hσ.1) (by linarith [hv.1])
    simp only [sub_zero, neg_mul, neg_div] at ht
    constructor <;> linarith [ht.1, ht.2]
  · intro σ hσ v hv
    have hs := smooth_gap (ne_of_gt (hδ.trans_le hv.1.1)) (hfuture hσ hv)
    simpa only [Function.comp_def, gap_parameters] using
      (hs.continuousAt.comp (hpc σ).continuousAt).continuousWithinAt
  · intro σ _ v hv
    exact ((smooth_weight (σ := σ) (ne_of_gt (hδ.trans_le hv.1.1))).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  · intro v hv
    have hs := smooth_gap (ne_of_gt (hδ.trans_le hv.1.1)) (hfuture hz hv)
    have hp : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => parameters h f x ω p.1 p.2) (0, v) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_const)
    simpa only [Function.comp_def, gap_parameters] using (hs.comp (0, v) hp).differentiableAt (by norm_num)
  · intro v hv
    exact (smooth_weight (ne_of_gt (hδ.trans_le hv.1.1))).continuousAt
  · intro v hv σ hσ
    exact (product_derivative (hsmooth x ω hσ hv)).differentiableAt.hasDerivAt
  · intro v hv σ hσ
    exact (product_second_derivative (hsmooth x ω hσ hv)).differentiableAt.hasDerivAt
  · have he : ContinuousOn (fun v => first f (parameters h f x ω 0 v))
        (MonotoneHinge.active (twoDRayGap h f x ω.val) δ V) := fun _ hv =>
      ((smooth_first (hsmooth x ω hz hv)).continuousAt.comp (hpc 0).continuousAt).continuousWithinAt
    exact he.congr (fun _ hv => (product_derivative_identities (hsmooth x ω hz hv)).1)
  · have he : ContinuousOn (fun v => second f (parameters h f x ω 0 v))
        (MonotoneHinge.active (twoDRayGap h f x ω.val) δ V) := fun _ hv =>
      ((continuous_second (hsmooth x ω hz hv)).comp (hpc 0).continuousAt).continuousWithinAt
    exact he.congr (fun _ hv => (product_derivative_identities (hsmooth x ω hz hv)).2)
  · intro σ hσ v hv
    calc
      _ ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ (σ, v) ⟨hσ, hv.1⟩
      _ ≤ M := le_max_right _ _
  · intro σ hσ v hv
    rw [(product_derivative_identities (hsmooth x ω hσ hv)).2]
    have hp : ((x, ω), (σ, v)) ∈ K :=
      ⟨⟨⟨(htube x ω.val v σ hω hv.1.1 hσ hv.2).1, mem_univ _⟩, hσ, hv.1⟩, hv.2⟩
    calc
      _ ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ _ hp
      _ ≤ B := le_max_right _ _

end TwoDLongGeometry
end BoundaryDraft
