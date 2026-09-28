import BoundaryDraft.TwoFaceNullGap
import BoundaryDraft.MonotoneHingeIntegral

/-!
# Uniform geometric hypotheses for the long-coordinate hinge

This is a fibre theorem, not spatial/directional disintegration or the averaged
long-null cancellation theorem. The gap and the Jacobian are unchanged.

The compact tube is a positive superlevel set of the continuous positive-part
height, contained in the compact closed positive region. The old active
endpoints have twice the tube's height margin. A common proper-time interval
keeps every perturbed endpoint in the tube. No positive-height noncriticality,
spatial contact transversality, or lower bound on root-to-cutoff distance enters.

For differentiation we freeze `max 0 (h x) - f x` as a scalar parameter. Thus
we never differentiate the positive-part height. Partial derivatives below
are derivatives of the actual smooth product, not extra analytic premises.

## Common constants and compact sets

Choose `κ, η` from the slope budget and `m > 0` from the already proved
`exists_gap_height_margin`. Let `H ≥ 0` bound the positive-part height globally.
The proof uses `c = (1-η)/2`, `A = (1+η)/(2*δ)`,
`V = δ + (H+1)/c` and `ε = m*δ^2/2`. Since `κ < 1`, moving the endpoint
by at most `ε/(2*δ)` loses at most `m*δ/4` in positive-part height.
The fixed active spatial set is `tube h (m*δ/2)`, and the perturbed-endpoint
tube is `tube h (m*δ/4)`. Both are compact; the latter is contained in `{h>0}`.

`M` is the nonnegative part of a compact bound on the actual weight on
`[0,ε] × [δ,V]`. `B` is the nonnegative part of a compact bound on `second`
over `activeBox`. The identities proved below identify it with `productD2`.
`future_derivative_bounds` separately extracts uniform bounds on `Df` and
`D(Df)` on the spatial tube. For the product bound we compactify the full
product directly, rather than assembling larger bounds term by term.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval

noncomputable section
namespace BoundaryDraft
namespace TwoFaceLongGeometry

/-- The actual proper-time Jacobian. -/
def weight (σ v : ℝ) : ℝ := (v - σ / v) ^ 2 / (8 * v)

/-- A fixed compact positive-height tube (in the Euclidean spatial topology). -/
def tube (h : Spatial → ℝ) (a : ℝ) : Set JointSpace :=
  graphClosedPositive h ∩ {x | a ≤ max 0 (h x)}

theorem compact_tube {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (a : ℝ) :
    IsCompact (tube h a) := by
  apply hf.toGraphCapData.isCompact_closedPositive.inter_right
  exact isClosed_le continuous_const
    (hf.toGraphCapData.continuous_positivePart.comp (PiLp.continuous_equiv 2 _))

theorem tube_positive {h : Spatial → ℝ} {a : ℝ} (ha : 0 < a)
    {x : JointSpace} (hx : x ∈ tube h a) : 0 < h x := by
  have := ha.trans_le hx.2
  simpa only [lt_max_iff, lt_self_iff_false, false_or] using this

/-- The original local C³ germs give uniform bounds on both spatial
Fréchet derivatives on this tube. This includes positive-height critical points. -/
theorem future_derivative_bounds {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (a : ℝ) : ∃ D₁ D₂ : ℝ, 0 ≤ D₁ ∧ 0 ≤ D₂ ∧
      ∀ y ∈ tube h a,
        ‖fderiv ℝ (fun z : JointSpace => f z) y‖ ≤ D₁ ∧
        ‖fderiv ℝ (fderiv ℝ (fun z : JointSpace => f z)) y‖ ≤ D₂ := by
  have h₁ : ContinuousOn (fderiv ℝ (fun z : JointSpace => f z)) (tube h a) := by
    intro y hy
    exact ((hf.smooth_future y hy.1).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
  have h₂ : ContinuousOn (fderiv ℝ (fderiv ℝ (fun z : JointSpace => f z))) (tube h a) := by
    intro y hy
    exact (((hf.smooth_future y hy.1).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨D₁, hD₁⟩ := (compact_tube hf a).exists_bound_of_continuousOn
    (f := fderiv ℝ (fun z : JointSpace => f z)) h₁
  obtain ⟨D₂, hD₂⟩ := (compact_tube hf a).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ (fun z : JointSpace => f z))) h₂
  exact ⟨max 0 D₁, max 0 D₂, le_max_left _ _, le_max_left _ _, fun y hy =>
    ⟨(hD₁ y hy).trans (le_max_right _ _), (hD₂ y hy).trans (le_max_right _ _)⟩⟩

/-- The old null endpoints have a uniform height margin, including contact. -/
theorem old_endpoint_margin {h f : Spatial → ℝ} {m δ v : ℝ}
    (hm : 0 < m) (hδ : 0 < δ)
    (hmargin : ∀ (x y : Spatial) (s : ℝ), spatialDistance x y ≤ s →
      0 ≤ twoFaceGap h f x y s → m * s ≤ max 0 (h x) ∧ m * s ≤ max 0 (h y))
    (x : Spatial) (ω : OverlapSphere) (hv : δ ≤ v)
    (hg : 0 ≤ twoFaceRayGap h f x ω 0 v) :
    m * δ / 2 ≤ max 0 (h x) ∧
      m * δ / 2 ≤ max 0 (h (x + spatialPolar ω (v / 2))) := by
  have hd : spatialDistance x (x + spatialPolar ω (v / 2)) = v / 2 := by
    simpa [spatialPolar, abs_of_nonneg (show 0 ≤ v / 2 by linarith)] using
      spatialDistance_polar_ray x ω 0 (v / 2)
  have hg' : 0 ≤ twoFaceGap h f x (x + spatialPolar ω (v / 2)) (v / 2) := by
    simpa [twoFaceRayGap] using hg
  have hb := hmargin x _ (v / 2) hd.le hg'
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hv hm.le]

/-- Uniform tube containment for ALL parameters on the old active interval,
even if the perturbed gap has already become negative. -/
theorem perturbed_endpoint_margin {h f : Spatial → ℝ} {κ m δ ε σ v : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 < m) (hδ : 0 < δ)
    (hh : ∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * spatialDistance x y)
    (hmargin : ∀ (x y : Spatial) (s : ℝ), spatialDistance x y ≤ s →
      0 ≤ twoFaceGap h f x y s → m * s ≤ max 0 (h x) ∧ m * s ≤ max 0 (h y))
    (hε : κ * ε / (2 * δ) ≤ m * δ / 4)
    (x : Spatial) (ω : OverlapSphere) (hv : δ ≤ v) (hσ : σ ∈ Icc 0 ε)
    (hg : 0 ≤ twoFaceRayGap h f x ω 0 v) :
    m * δ / 4 ≤ max 0 (h (x + spatialPolar ω ((v - σ / v) / 2))) := by
  have hb := (old_endpoint_margin hm hδ hmargin x ω hv hg).2
  have hd : (v - σ / v) / 2 - v / 2 = -(σ / (2 * v)) := by ring
  have hl := (abs_le.mp (hh (x + spatialPolar ω (v / 2))
    (x + spatialPolar ω ((v - σ / v) / 2)))).2
  rw [spatialDistance_polar_ray, hd, abs_neg,
    abs_of_nonneg (div_nonneg hσ.1 (by linarith))] at hl
  have he : κ * (σ / (2 * v)) ≤ κ * ε / (2 * δ) := by
    have hε0 := hσ.1.trans hσ.2
    rw [← mul_div_assoc]
    gcongr
    exact hσ.2
  linarith

/-- Smooth ambient parameters: proper-time square, length, frozen height-minus-
future-value, base point, direction. Directions are not differentiated on a sphere. -/
abbrev Parameters := ℝ × (ℝ × (ℝ × (JointSpace × JointSpace)))

def endpoint (p : Parameters) : JointSpace :=
  p.2.2.2.1 + ((p.2.1 - p.1 / p.2.1) / 2) • p.2.2.2.2

def gap (f : Spatial → ℝ) (p : Parameters) : ℝ :=
  p.2.2.1 + f (endpoint p) - (p.2.1 + p.1 / p.2.1) / 2

def product (f : Spatial → ℝ) (p : Parameters) : ℝ :=
  weight p.1 p.2.1 * gap f p

def parameters (h f : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    (σ v : ℝ) : Parameters :=
  (σ, v, max 0 (h x) - f x, (WithLp.equiv 2 _).symm x, ω.val)

/-- Constant direction of differentiation in proper-time square. -/
def sigmaDirection : Parameters := (1, 0)

def first (f : Spatial → ℝ) (p : Parameters) : ℝ :=
  fderiv ℝ (product f) p sigmaDirection

def second (f : Spatial → ℝ) (p : Parameters) : ℝ :=
  fderiv ℝ (first f) p sigmaDirection

@[simp] theorem gap_parameters (h f : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    (σ v : ℝ) : gap f (parameters h f x ω σ v) = twoFaceRayGap h f x ω σ v := by
  have he : (endpoint (parameters h f x ω σ v) : Spatial) =
      x + spatialPolar ω ((v - σ / v) / 2) := by ext i; rfl
  simp only [gap, he, twoFaceRayGap, twoFaceGap]
  dsimp only [parameters]
  ring

@[simp] theorem product_parameters (h f : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    (σ v : ℝ) : product f (parameters h f x ω σ v) =
      weight σ v * twoFaceRayGap h f x ω σ v := by
  simp only [product, gap_parameters]
  rfl

theorem smooth_weight {σ v : ℝ} (hv : v ≠ 0) :
    ContDiffAt ℝ 3 (fun p : ℝ × ℝ => weight p.1 p.2) (σ, v) := by
  exact ((contDiffAt_snd.sub (contDiffAt_fst.div contDiffAt_snd hv)).pow 2).div
    (contDiffAt_const.mul contDiffAt_snd) (mul_ne_zero (by norm_num) hv)

theorem smooth_gap {f : Spatial → ℝ} {p : Parameters} (hv : p.2.1 ≠ 0)
    (hf : ContDiffAt ℝ 3 (fun y : JointSpace => f y) (endpoint p)) :
    ContDiffAt ℝ 3 (gap f) p := by
  have he : ContDiffAt ℝ 3 endpoint p := by
    exact contDiffAt_snd.snd.snd.fst.add
      (((contDiffAt_snd.fst.sub (contDiffAt_fst.div contDiffAt_snd.fst hv)).div_const 2).smul
        contDiffAt_snd.snd.snd.snd)
  exact (contDiffAt_snd.snd.fst.add (hf.comp p he)).sub
    ((contDiffAt_snd.fst.add (contDiffAt_fst.div contDiffAt_snd.fst hv)).div_const 2)

theorem smooth_product {f : Spatial → ℝ} {p : Parameters} (hv : p.2.1 ≠ 0)
    (hf : ContDiffAt ℝ 3 (fun y : JointSpace => f y) (endpoint p)) :
    ContDiffAt ℝ 3 (product f) p := by
  exact ((smooth_weight hv).comp p (contDiffAt_fst.prodMk contDiffAt_snd.fst)).mul
    (smooth_gap hv hf)

theorem smooth_first {f : Spatial → ℝ} {p : Parameters}
    (hp : ContDiffAt ℝ 3 (product f) p) : ContDiffAt ℝ 2 (first f) p :=
  (hp.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const

theorem continuous_second {f : Spatial → ℝ} {p : Parameters}
    (hp : ContDiffAt ℝ 3 (product f) p) : ContinuousAt (second f) p :=
  (((smooth_first hp).fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiffAt_const).continuousAt

private theorem parameters_deriv (h f : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    (σ v : ℝ) : HasDerivAt (fun s => parameters h f x ω s v) sigmaDirection σ := by
  exact (hasDerivAt_id σ).prodMk (hasDerivAt_const σ _)

/-- First derivative identity for the actual product, obtained by the chain rule. -/
theorem product_derivative {h f : Spatial → ℝ} {x : Spatial} {ω : OverlapSphere} {σ v : ℝ}
    (hp : ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v)) :
    HasDerivAt (fun s => weight s v * twoFaceRayGap h f x ω s v)
      (first f (parameters h f x ω σ v)) σ := by
  simpa only [Function.comp_def, product_parameters] using
    (hp.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt σ
      (parameters_deriv h f x ω σ v)

/-- Second derivative identity; equality of first derivatives is justified on
an ambient neighborhood, not merely on the closed parameter interval. -/
theorem product_second_derivative {h f : Spatial → ℝ} {x : Spatial}
    {ω : OverlapSphere} {σ v : ℝ}
    (hp : ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v)) :
    HasDerivAt (fun s => MonotoneHinge.productD1 (twoFaceRayGap h f x ω) weight s v)
      (second f (parameters h f x ω σ v)) σ := by
  have hd := ((smooth_first hp).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt σ
    (parameters_deriv h f x ω σ v)
  apply hd.congr_of_eventuallyEq
  have hc := (parameters_deriv h f x ω σ v).continuousAt
  filter_upwards [hc.eventually (hp.eventually (by norm_num))] with s hs
  exact (product_derivative hs).deriv

/-- Identities used for continuity and compact bounds: both are proved
identities of derivatives of `weight * twoFaceRayGap`. -/
theorem product_derivative_identities {h f : Spatial → ℝ} {x : Spatial}
    {ω : OverlapSphere} {σ v : ℝ}
    (hp : ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v)) :
    MonotoneHinge.productD1 (twoFaceRayGap h f x ω) weight σ v =
      first f (parameters h f x ω σ v) ∧
    MonotoneHinge.productD2 (twoFaceRayGap h f x ω) weight σ v =
      second f (parameters h f x ω σ v) :=
  ⟨(product_derivative hp).deriv, (product_second_derivative hp).deriv⟩

/-- Explicit first derivative of the actual Jacobian. -/
theorem weight_derivative (σ : ℝ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun s => weight s v) (-(v - σ / v) / (4 * v ^ 2)) σ := by
  convert ((((hasDerivAt_id σ).div_const v).const_sub v).pow 2).div_const (8 * v) using 1
  field_simp
  ring

/-- Explicit second derivative of the actual Jacobian. -/
theorem weight_second_derivative (σ : ℝ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun s => -(v - s / v) / (4 * v ^ 2)) (1 / (4 * v ^ 3)) σ := by
  convert ((((hasDerivAt_id σ).div_const v).const_sub v).neg).div_const (4 * v ^ 2) using 1
  field_simp
  ring

/-- Leibniz's formula with the actual Jacobian, not a derivative premise. -/
theorem productD1_formula {h f : Spatial → ℝ} {x : Spatial} {ω : OverlapSphere}
    {σ v : ℝ} (hv : v ≠ 0)
    (hg : ContDiffAt ℝ 3 (fun s => twoFaceRayGap h f x ω s v) σ) :
    MonotoneHinge.productD1 (twoFaceRayGap h f x ω) weight σ v =
      -(v - σ / v) / (4 * v ^ 2) * twoFaceRayGap h f x ω σ v +
        weight σ v * deriv (fun s => twoFaceRayGap h f x ω s v) σ := by
  exact ((weight_derivative σ hv).mul (hg.differentiableAt (by norm_num)).hasDerivAt).deriv

/-- The complete product second derivative, including BOTH cross terms.
The derivative of the gap is allowed to vanish; no spatial transversality is used. -/
theorem productD2_formula {h f : Spatial → ℝ} {x : Spatial} {ω : OverlapSphere}
    {σ v : ℝ} (hv : v ≠ 0)
    (hg : ContDiffAt ℝ 3 (fun s => twoFaceRayGap h f x ω s v) σ) :
    MonotoneHinge.productD2 (twoFaceRayGap h f x ω) weight σ v =
      twoFaceRayGap h f x ω σ v / (4 * v ^ 3) +
        2 * (-(v - σ / v) / (4 * v ^ 2)) *
          deriv (fun s => twoFaceRayGap h f x ω s v) σ +
        weight σ v * deriv (fun s => deriv (fun t => twoFaceRayGap h f x ω t v) s) σ := by
  have hg₁ := (hg.differentiableAt (by norm_num)).hasDerivAt
  have hgd : ContDiffAt ℝ 2 (fun s => deriv (fun t => twoFaceRayGap h f x ω t v) s) σ :=
    (hg.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hg₂ := (hgd.differentiableAt (by norm_num)).hasDerivAt
  have hd := ((weight_second_derivative σ hv).mul hg₁).add ((weight_derivative σ hv).mul hg₂)
  have he : (fun s => MonotoneHinge.productD1 (twoFaceRayGap h f x ω) weight s v) =ᶠ[𝓝 σ]
      (fun s => -(v - s / v) / (4 * v ^ 2) * twoFaceRayGap h f x ω s v +
        weight s v * deriv (fun t => twoFaceRayGap h f x ω t v) s) := by
    filter_upwards [hg.eventually (by norm_num)] with s hs
    exact productD1_formula hv hs
  have hr := (hd.congr_of_eventuallyEq he).deriv
  dsimp only [MonotoneHinge.productD2]
  rw [hr]
  ring

/-- Compact parameter domain before mapping to the ambient smooth product. -/
abbrev Index := (JointSpace × OverlapSphere) × (ℝ × ℝ)

def indexParameters (h f : Spatial → ℝ) (p : Index) : Parameters :=
  parameters h f p.1.1 p.1.2 p.2.1 p.2.2

def activeBox (h f : Spatial → ℝ) (a δ V ε : ℝ) : Set Index :=
  ((tube h a ×ˢ univ) ×ˢ (Icc 0 ε ×ˢ Icc δ V)) ∩
    {p | 0 ≤ twoFaceRayGap h f p.1.1 p.1.2 0 p.2.2}

theorem continuous_parameters {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    Continuous (indexParameters h f) := by
  have he := PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)
  have hH := hf.toGraphCapData.continuous_positivePart.comp he
  have hF := hf.strictGraphLipschitz_upper.continuous.comp he
  change Continuous (fun p : Index => (p.2.1, p.2.2,
    max 0 (h p.1.1) - f p.1.1, p.1.1, p.1.2.val))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (((hH.sub hF).comp continuous_fst.fst).prodMk
      (continuous_fst.fst.prodMk (continuous_subtype_val.comp continuous_fst.snd))))

theorem continuous_null {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    Continuous (fun p : Index => twoFaceRayGap h f p.1.1 p.1.2 0 p.2.2) := by
  have he := PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)
  have hH := hf.toGraphCapData.continuous_positivePart.comp he
  have hF := hf.strictGraphLipschitz_upper.continuous.comp he
  have hh : Continuous (fun p : Index =>
      max 0 (h p.1.1) + f (p.1.1 + (p.2.2 / 2) • p.1.2.val : JointSpace) -
        f p.1.1 - p.2.2 / 2) :=
    (((hH.comp continuous_fst.fst).add (hF.comp
      (continuous_fst.fst.add ((continuous_snd.snd.div_const 2).smul
        (continuous_subtype_val.comp continuous_fst.snd))))).sub
      (hF.comp continuous_fst.fst)).sub (continuous_snd.snd.div_const 2)
  convert hh using 1
  funext p
  simp only [twoFaceRayGap, twoFaceGap, zero_div, sub_zero, add_zero]
  rfl

theorem compact_activeBox {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (a δ V ε : ℝ) : IsCompact (activeBox h f a δ V ε) := by
  exact (((compact_tube hf a).prod isCompact_univ).prod
    (isCompact_Icc.prod isCompact_Icc)).inter_right
      (isClosed_le continuous_const (continuous_null hf))

/-- A positive superlevel bound gives membership without any exterior regularity. -/
theorem mem_tube_of_margin {h : Spatial → ℝ} {a : ℝ} (ha : 0 < a)
    (x : Spatial) (hx : a ≤ max 0 (h x)) :
    (WithLp.equiv 2 _).symm x ∈ tube h a := by
  refine ⟨subset_closure ?_, hx⟩
  have hp := ha.trans_le hx
  simpa only [mem_setOf_eq, lt_max_iff, lt_self_iff_false, false_or] using hp

/-- Common constants for EVERY spatial point and direction, derived from the
unchanged admissibility. `B` is a compact bound on the proved second derivative
of the full product, rather than an assumed analytic bound. -/
theorem exists_hypotheses {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ε c A M B : ℝ, δ < V ∧ 0 < ε ∧ 0 < c ∧ 0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (x : Spatial) (ω : OverlapSphere),
        MonotoneHinge.Hypotheses (twoFaceRayGap h f x ω) weight δ V ε c A M B := by
  obtain ⟨κ, η, hκ, hη, hbudget, hh, hfl⟩ := hf.slope_budget
  obtain ⟨m, hm, hmargin⟩ := hf.exists_gap_height_margin
  obtain ⟨H₀, hH₀⟩ := hf.toGraphCapData.hasCompactSupport_positivePart.exists_bound_of_continuous
    hf.toGraphCapData.continuous_positivePart
  let H := max 0 H₀
  have hH : ∀ x, max 0 (h x) ≤ H := by
    intro x
    calc
      _ ≤ |max 0 (h x)| := le_abs_self _
      _ ≤ H₀ := by simpa only [Real.norm_eq_abs] using hH₀ x
      _ ≤ H := le_max_right _ _
  let c := (1 - η) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let A := (1 + η) / (2 * δ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let V := δ + (H + 1) / c
  have hV : δ < V := by
    have hH0 : 0 ≤ H := le_max_left _ _
    dsimp [V]
    exact lt_add_of_pos_right _ (div_pos (by linarith) hc)
  let ε := m * δ ^ 2 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let a := m * δ / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hsmall : κ * ε / (2 * δ) ≤ m * δ / 4 := by
    have he : ε / (2 * δ) = m * δ / 4 := by
      dsimp [ε]
      field_simp
      ring
    rw [mul_div_assoc, he]
    exact mul_le_of_le_one_left ha.le (by linarith)
  have htube (x : Spatial) (ω : OverlapSphere) {σ v : ℝ}
      (hσ : σ ∈ Icc 0 ε) (hv : δ ≤ v) (hg : 0 ≤ twoFaceRayGap h f x ω 0 v) :
      endpoint (parameters h f x ω σ v) ∈ tube h a := by
    have hb := perturbed_endpoint_margin hκ hm hδ hh hmargin hsmall x ω hv hσ hg
    exact mem_tube_of_margin ha _ hb
  have hsmooth (x : Spatial) (ω : OverlapSphere) {σ v : ℝ}
      (hσ : σ ∈ Icc 0 ε) (hv : v ∈ MonotoneHinge.active (twoFaceRayGap h f x ω) δ V) :
      ContDiffAt ℝ 3 (product f) (parameters h f x ω σ v) :=
    smooth_product (ne_of_gt (hδ.trans_le hv.1.1))
      (hf.smooth_future _ (htube x ω hσ hv.1.1 hv.2).1)
  let K := activeBox h f (m * δ / 2) δ V ε
  have hK : IsCompact K := compact_activeBox hf _ _ _ _
  have hsK (p : Index) (hp : p ∈ K) : ContDiffAt ℝ 3 (product f) (indexParameters h f p) :=
    hsmooth p.1.1 p.1.2 hp.1.2.1 ⟨hp.1.2.2, hp.2⟩
  have hcont2 : ContinuousOn (fun p => second f (indexParameters h f p)) K := by
    intro p hp
    exact ((continuous_second (hsK p hp)).comp
      (continuous_parameters hf).continuousAt).continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    (f := fun p => second f (indexParameters h f p)) hcont2
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => weight p.1 p.2)
      (Icc 0 ε ×ˢ Icc δ V) := by
    intro p hp
    exact (smooth_weight (ne_of_gt (hδ.trans_le hp.2.1))).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => weight p.1 p.2) hcontW
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨V, ε, c, A, M, B, hV, hε, hc, hA, hM, hB, ?_⟩
  intro x ω
  have hpc (σ : ℝ) : Continuous (fun v => parameters h f x ω σ v) := by
    exact continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hz : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, hε.le⟩
  refine {
    cutoff_lt := hV
    epsilon_pos := hε
    transverse_pos := hc
    speed_nonneg := hA
    weight_nonneg := hM
    second_nonneg := hB
    null_continuous := ?_
    null_decrease := ?_
    clearance := ?_
    nonopening := ?_
    gap_continuous := ?_
    weight_continuous := ?_
    gap_differentiable := ?_
    weight_continuousAt := ?_
    product_deriv := ?_
    product_deriv2 := ?_
    first_continuous := ?_
    second_continuous := ?_
    weight_bound := ?_
    second_bound := ?_ }
  · exact ((continuous_null hf).comp
      (show Continuous (fun v : ℝ => (((WithLp.equiv 2 _).symm x, ω), (0, v))) from
        continuous_const.prodMk (continuous_const.prodMk continuous_id))).continuousOn
  · intro v _ w _ hvw
    convert twoFaceRayGap_null_sub_le hfl h x ω hvw using 1
    dsimp [c]
    ring
  · have hn := twoFaceRayGap_null_sub_le hfl h x ω (show 0 ≤ V by linarith)
    have hzero : twoFaceRayGap h f x ω 0 0 = max 0 (h x) := by
      simp [twoFaceRayGap, twoFaceGap, spatialPolar]
    rw [hzero] at hn
    have he : c * V = c * δ + (H + 1) := by dsimp [V]; field_simp; ring
    have hd := mul_pos hc hδ
    have hx := hH x
    dsimp [c] at he hd
    nlinarith
  · intro σ hσ v hv
    have ht := twoFaceRayGap_transverse_bounds hfl h x ω (hδ.trans_le hv.1) hσ.1
    have hlo : (1 + η) * σ / (2 * v) ≤ A * σ := by
      calc
        _ ≤ (1 + η) * σ / (2 * δ) := by
          apply div_le_div_of_nonneg_left (mul_nonneg (by linarith) hσ.1) (by positivity)
          linarith [hv.1]
        _ = _ := by dsimp [A]; ring
    have hhi : -(1 - η) * (σ - 0) / (2 * v) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hσ.1])) (by linarith [hv.1])
    simp only [sub_zero, neg_mul, neg_div] at ht hhi
    constructor <;> linarith [ht.1, ht.2]
  · intro σ hσ v hv
    have hs := smooth_gap (ne_of_gt (hδ.trans_le hv.1.1))
      (hf.smooth_future _ (htube x ω hσ hv.1.1 hv.2).1)
    simpa only [Function.comp_def, gap_parameters] using
      (hs.continuousAt.comp (hpc σ).continuousAt).continuousWithinAt
  · intro σ _ v hv
    exact ((smooth_weight (σ := σ) (ne_of_gt (hδ.trans_le hv.1.1))).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  · intro v hv
    have hs := smooth_gap (ne_of_gt (hδ.trans_le hv.1.1))
      (hf.smooth_future _ (htube x ω hz hv.1.1 hv.2).1)
    have hp : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => parameters h f x ω p.1 p.2) (0, v) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_const)
    simpa only [Function.comp_def, gap_parameters] using
      (hs.comp (0, v) hp).differentiableAt (by norm_num)
  · intro v hv
    exact (smooth_weight (ne_of_gt (hδ.trans_le hv.1.1))).continuousAt
  · intro v hv σ hσ
    exact (product_derivative (hsmooth x ω hσ hv)).differentiableAt.hasDerivAt
  · intro v hv σ hσ
    exact (product_second_derivative (hsmooth x ω hσ hv)).differentiableAt.hasDerivAt
  · have he : ContinuousOn (fun v => first f (parameters h f x ω 0 v))
        (MonotoneHinge.active (twoFaceRayGap h f x ω) δ V) := by
      intro v hv
      exact (((smooth_first (hsmooth x ω hz hv)).continuousAt).comp
        (hpc 0).continuousAt).continuousWithinAt
    exact he.congr (fun v hv => (product_derivative_identities (hsmooth x ω hz hv)).1)
  · have he : ContinuousOn (fun v => second f (parameters h f x ω 0 v))
        (MonotoneHinge.active (twoFaceRayGap h f x ω) δ V) := by
      intro v hv
      exact ((continuous_second (hsmooth x ω hz hv)).comp
        (hpc 0).continuousAt).continuousWithinAt
    exact he.congr (fun v hv => (product_derivative_identities (hsmooth x ω hz hv)).2)
  · intro σ hσ v hv
    calc
      _ ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ (σ, v) ⟨hσ, hv.1⟩
      _ ≤ M := le_max_right _ _
  · intro σ hσ v hv
    rw [(product_derivative_identities (hsmooth x ω hσ hv)).2]
    have hx := (old_endpoint_margin hm hδ hmargin x ω hv.1.1 hv.2).1
    have hp : (((WithLp.equiv 2 _).symm x, ω), (σ, v)) ∈ K :=
      ⟨⟨⟨mem_tube_of_margin (by positivity) x hx, mem_univ _⟩, hσ, hv.1⟩, hv.2⟩
    calc
      _ ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ _ hp
      _ ≤ B := le_max_right _ _

/-- Geometric specialization of the three regimes, right quadratic jet and
common normalized-remainder bound. The same constants precede BOTH fibre
quantifiers. This is pointwise little-o with uniform domination, not uniform
little-o and not yet an averaged-density theorem. -/
theorem geometric_specialization {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ε c A M B : ℝ, δ < V ∧ 0 < ε ∧ 0 < c ∧ 0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (x : Spatial) (ω : OverlapSphere),
        let g := twoFaceRayGap h f x ω
        MonotoneHinge.Hypotheses g weight δ V ε c A M B ∧
        ((g 0 δ < 0 ∧ ∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre g weight δ V σ = 0) ∨
          (g 0 δ = 0 ∧ ∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre g weight δ V σ = 0) ∨
          (0 < g 0 δ ∧ ∃! R : ℝ, R ∈ Ioo δ V ∧ g 0 R = 0)) ∧
        ((fun σ => MonotoneHinge.fibre g weight δ V σ -
          (MonotoneHinge.F0 g weight δ V + MonotoneHinge.F1 g weight δ V * σ +
            MonotoneHinge.F2 g weight δ V * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2)) ∧
        (∀ σ ∈ Ioc 0 ε,
          |MonotoneHinge.fibre g weight δ V σ -
            (MonotoneHinge.F0 g weight δ V + MonotoneHinge.F1 g weight δ V * σ +
              MonotoneHinge.F2 g weight δ V * σ ^ 2)| / σ ^ 2 ≤
                MonotoneHinge.remainderBound δ V c A M B) ∧
        (∀ R ∈ Ioo δ V, g 0 R = 0 →
          MonotoneHinge.F0 g weight δ V = (∫ v in δ..R, weight 0 v * g 0 v) ∧
          MonotoneHinge.F1 g weight δ V = (∫ v in δ..R, deriv (fun s => weight s v * g s v) 0) ∧
          MonotoneHinge.F2 g weight δ V =
            (1 / 2 * ∫ v in δ..R, deriv (fun s => deriv (fun t => weight t v * g t v) s) 0) +
              weight 0 R * (deriv (fun s => g s R) 0) ^ 2 / (2 * (-deriv (g 0) R))) := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, hc, hA, hM, hB, hall⟩ := exists_hypotheses hf hδ
  refine ⟨V, ε, c, A, M, B, hV, hε, hc, hA, hM, hB, ?_⟩
  intro x ω
  have hh := hall x ω
  exact ⟨hh, hh.three_regimes, hh.right_quadratic_jet,
    fun _ hσ => hh.normalized_remainder_bound hσ,
    fun _ hR hz => hh.coefficients_of_root hR hz⟩

end TwoFaceLongGeometry
end BoundaryDraft
