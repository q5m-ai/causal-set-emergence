import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Monotone, non-opening hinge fibres

Geometry-independent analysis for #61. The parameter is proper-time *square*;
all quadratic coefficients are coefficients of `σ ^ 2`, not second derivatives.
The old active interval is fixed before expanding the smooth product `J * g`.
The lost layer is treated separately; no contact set is discarded as null.

## Proof

* Quantitative decrease and the IVT identify the unique old root in the active
  regime. Non-opening makes both other regimes identically zero on the right.
* On the fixed old interval, ordinary scalar Peano expansion and a twice-applied
  mean value bound give a dominated quadratic remainder.
* The correction is the integral of `J * max 0 (-g)` over that interval. It is
  supported within `A * σ / c` of the old root, has height at most `M * A * σ`,
  and hence has normalized absolute value at most `M * A ^ 2 / c`.
* For a fixed active fibre, substitute `v = R - σ * u`. Joint differentiability
  of `g` and continuity of `J` identify a triangular limiting profile. Its area
  gives the contact coefficient, including the factor `1/2`. This avoids an
  implicit-function theorem and even avoids selecting a perturbed root.
* Only the pointwise rescaling argument uses a neighborhood depending on `R-δ`.
  The final domination bound holds for EVERY `0 < σ ≤ ε`, including fibres
  which have already closed at that value of `σ`.

This module does not identify any geometric density, perform spatial/directional
averaging, or resolve #61. It supplies the abstract fibre result for those steps.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval

noncomputable section
namespace BoundaryDraft
namespace MonotoneHinge

/-- The actual hinge integral (an oriented interval integral). -/
def fibre (g J : ℝ → ℝ → ℝ) (δ V σ : ℝ) : ℝ :=
  ∫ v in δ..V, J σ v * max 0 (g σ v)

/-- The old active set includes contact. -/
def active (g : ℝ → ℝ → ℝ) (δ V : ℝ) : Set ℝ :=
  {v ∈ Icc δ V | 0 ≤ g 0 v}

/-- First parameter derivative of the *product*. -/
def productD1 (g J : ℝ → ℝ → ℝ) (σ v : ℝ) : ℝ :=
  deriv (fun s => J s v * g s v) σ

/-- Second derivative, NOT the quadratic coefficient. -/
def productD2 (g J : ℝ → ℝ → ℝ) (σ v : ℝ) : ℝ :=
  deriv (fun s => productD1 g J s v) σ

/-- A convenient common right neighborhood, including its right endpoint. -/
theorem eventually_right {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in 𝓝[>] 0, σ ∈ Ioc 0 ε :=
  Ioc_mem_nhdsGT hε

/-- Elementary second-order Peano formula. Only differentiability of the first
 derivative at zero, and existence of the first derivative nearby, are needed. -/
theorem quadratic_peano {f f' : ℝ → ℝ} {ε b : ℝ} (hε : 0 < ε)
    (hf : ∀ s ∈ Icc 0 ε, HasDerivAt f (f' s) s)
    (hf' : HasDerivAt f' b 0) :
    (fun s => f s - (f 0 + f' 0 * s + b / 2 * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2) := by
  have hfirst : (fun s => f' s - f' 0 - s * b) =o[𝓝[Icc 0 ε] 0]
      (fun s => (s - 0) ^ 1) := by
    simpa only [sub_zero, smul_eq_mul, pow_one] using
      (hasDerivAt_iff_isLittleO.mp hf').mono nhdsWithin_le_nhds
  have hd (s : ℝ) (hs : s ∈ Icc 0 ε) :
      HasDerivWithinAt (fun t => f t - (f 0 + f' 0 * t + b / 2 * t ^ 2))
        (f' s - f' 0 - s * b) (Icc 0 ε) s := by
    convert ((hf s hs).sub (((hasDerivAt_const s (f 0)).add
      ((hasDerivAt_id s).const_mul (f' 0))).add
        (((hasDerivAt_id s).pow 2).const_mul (b / 2)))).hasDerivWithinAt using 1
    simp only [id_eq]
    ring
  have h := (convex_Icc (0 : ℝ) ε).isLittleO_pow_succ_real
    (left_mem_Icc.mpr hε.le) hd hfirst
  simpa using h.mono (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, hε⟩))

/-- A uniform normalized Taylor bound on the SUPPLIED interval. Its radius
 does not depend on the value of `f 0`, or any active-interval length. -/
theorem quadratic_bound {f f' f'' : ℝ → ℝ} {ε B s : ℝ}
    (hB : 0 ≤ B) (hs : s ∈ Ioc 0 ε)
    (hf : ∀ t ∈ Icc 0 ε, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc 0 ε, HasDerivAt f' (f'' t) t)
    (hb : ∀ t ∈ Icc 0 ε, |f'' t| ≤ B) :
    |f s - (f 0 + f' 0 * s + f'' 0 / 2 * s ^ 2)| / s ^ 2 ≤ 2 * B := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 ε := Icc_subset_Icc_right hs.2
  have hfirst (t : ℝ) (ht : t ∈ Icc 0 s) : |f' t - f' 0| ≤ B * t := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      norm_image_sub_le_of_norm_deriv_le_segment'
        (fun x hx => (hf' x (hsub hx)).hasDerivWithinAt)
        (fun x hx => hb x (hsub (Ico_subset_Icc_self hx))) t ht
  have hlin : |f s - (f 0 + f' 0 * s)| ≤ B * s ^ 2 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t => f t - f' 0 * t) (f' := fun t => f' t - f' 0)
      (a := 0) (b := s) (C := B * s)
      (fun x hx => by
        simpa using ((hf x (hsub hx)).sub
          ((hasDerivAt_id x).const_mul (f' 0))).hasDerivWithinAt)
      (fun x hx => (hfirst x (Ico_subset_Icc_self hx)).trans
        (mul_le_mul_of_nonneg_left hx.2.le hB)) s ⟨hs.1.le, le_rfl⟩
    simpa only [Real.norm_eq_abs, mul_zero, sub_zero, sub_sub, mul_assoc, ← pow_two, add_comm (f' 0 * s)] using h
  have hzero := hb 0 ⟨le_rfl, hs.1.le.trans hs.2⟩
  have hsq : 0 < s ^ 2 := sq_pos_of_pos hs.1
  apply (div_le_iff₀ hsq).mpr
  calc
    _ = |(f s - (f 0 + f' 0 * s)) - f'' 0 / 2 * s ^ 2| := by congr 1; ring
    _ ≤ |f s - (f 0 + f' 0 * s)| + |f'' 0 / 2 * s ^ 2| := abs_sub _ _
    _ ≤ B * s ^ 2 + B / 2 * s ^ 2 := by
      apply add_le_add hlin
      rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg s)]
      norm_num
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hzero (by norm_num))
        (sq_nonneg s)
    _ ≤ 2 * B * s ^ 2 := by nlinarith [mul_nonneg hB hsq.le]

/-- Primitive assumptions. The regularity fields are local differential and
 continuity facts implied by C² germs near `[0, ε] × active g δ V`.
 No expansion, integral identity, root, remainder, or limit is a field.
 No regularity at all is required where the old gap is negative.
 Only the two bounds actually needed for remainder domination are retained:
 `M` bounds the weight and `B` bounds the second derivative of the product.
 Continuity on the compact active interval supplies integrability of the
 product and both coefficients; additional supplied bounds on them are harmless. -/
structure Hypotheses (g J : ℝ → ℝ → ℝ) (δ V ε c A M B : ℝ) : Prop where
  cutoff_lt : δ < V
  epsilon_pos : 0 < ε
  transverse_pos : 0 < c
  speed_nonneg : 0 ≤ A
  weight_nonneg : 0 ≤ M
  second_nonneg : 0 ≤ B
  null_continuous : ContinuousOn (g 0) (Icc δ V)
  null_decrease : ∀ v ∈ Icc δ V, ∀ w ∈ Icc δ V, v ≤ w →
    g 0 w - g 0 v ≤ -c * (w - v)
  clearance : g 0 V < 0
  nonopening : ∀ σ ∈ Icc 0 ε, ∀ v ∈ Icc δ V,
    -A * σ ≤ g σ v - g 0 v ∧ g σ v - g 0 v ≤ 0
  gap_continuous : ∀ σ ∈ Icc 0 ε, ContinuousOn (g σ) (active g δ V)
  weight_continuous : ∀ σ ∈ Icc 0 ε, ContinuousOn (J σ) (active g δ V)
  gap_differentiable : ∀ v ∈ active g δ V,
    DifferentiableAt ℝ (fun p : ℝ × ℝ => g p.1 p.2) (0, v)
  weight_continuousAt : ∀ v ∈ active g δ V,
    ContinuousAt (fun p : ℝ × ℝ => J p.1 p.2) (0, v)
  product_deriv : ∀ v ∈ active g δ V, ∀ σ ∈ Icc 0 ε,
    HasDerivAt (fun s => J s v * g s v) (productD1 g J σ v) σ
  product_deriv2 : ∀ v ∈ active g δ V, ∀ σ ∈ Icc 0 ε,
    HasDerivAt (fun s => productD1 g J s v) (productD2 g J σ v) σ
  first_continuous : ContinuousOn (productD1 g J 0) (active g δ V)
  second_continuous : ContinuousOn (productD2 g J 0) (active g δ V)
  weight_bound : ∀ σ ∈ Icc 0 ε, ∀ v ∈ active g δ V, |J σ v| ≤ M
  second_bound : ∀ σ ∈ Icc 0 ε, ∀ v ∈ active g δ V, |productD2 g J σ v| ≤ B

variable {g J : ℝ → ℝ → ℝ} {δ V ε c A M B : ℝ}

namespace Hypotheses

variable (h : Hypotheses g J δ V ε c A M B)
include h

/-- Quantitative null decrease implies strict antitonicity. -/
theorem strictAnti : StrictAntiOn (g 0) (Icc δ V) := by
  intro v hv w hw hvw
  have := h.null_decrease v hv w hw hvw.le
  have := mul_pos h.transverse_pos (sub_pos.mpr hvw)
  linarith

/-- Both inactive and exact-cutoff-contact fibres vanish on the entire common
 right interval, with no exceptional-set hypothesis. -/
theorem fibre_zero (hg : g 0 δ ≤ 0) {σ : ℝ} (hσ : σ ∈ Icc 0 ε) :
    fibre g J δ V σ = 0 := by
  unfold fibre
  apply intervalIntegral.integral_zero_ae
  filter_upwards with v hv
  rw [uIoc_of_le h.cutoff_lt.le] at hv
  have ht := (h.nonopening σ hσ v (Ioc_subset_Icc_self hv)).2
  have hn := h.strictAnti.antitoneOn (left_mem_Icc.mpr h.cutoff_lt.le)
    (Ioc_subset_Icc_self hv) hv.1.le
  rw [max_eq_left (by linarith : g σ v ≤ 0), mul_zero]

/-- The active regime has exactly one old root, strictly between the endpoints. -/
theorem exists_unique_root (hg : 0 < g 0 δ) :
    ∃! R : ℝ, R ∈ Ioo δ V ∧ g 0 R = 0 := by
  obtain ⟨R, hR, hz⟩ := intermediate_value_Ioo' h.cutoff_lt.le h.null_continuous
    (show (0 : ℝ) ∈ Ioo (g 0 V) (g 0 δ) from ⟨h.clearance, hg⟩)
  refine ⟨R, ⟨hR, hz⟩, ?_⟩
  intro S hS
  exact h.strictAnti.injOn (Ioo_subset_Icc_self hS.1)
    (Ioo_subset_Icc_self hR) (hS.2.trans hz.symm)

/-- A root identifies the full old active interval, including its endpoint. -/
theorem active_eq {R : ℝ} (hR : R ∈ Ioo δ V) (hz : g 0 R = 0) :
    active g δ V = Icc δ R := by
  ext v
  constructor
  · rintro ⟨hv, hg⟩
    refine ⟨hv.1, ?_⟩
    by_contra! hvR
    have := h.strictAnti (Ioo_subset_Icc_self hR) hv hvR
    linarith
  · intro hv
    refine ⟨⟨hv.1, hv.2.trans hR.2.le⟩, ?_⟩
    have := h.strictAnti.antitoneOn ⟨hv.1, hv.2.trans hR.2.le⟩
      (Ioo_subset_Icc_self hR) hv.2
    linarith

/-! ## The fixed old active interval -/

/-- The smooth part, integrated over the OLD active interval. -/
def fixed (R σ : ℝ) : ℝ := ∫ v in δ..R, J σ v * g σ v

/-- The normalized scalar product remainder, before integration. -/
def productRemainder (σ v : ℝ) : ℝ :=
  (J σ v * g σ v - (J 0 v * g 0 v + productD1 g J 0 v * σ +
    productD2 g J 0 v / 2 * σ ^ 2)) / σ ^ 2

/-- The fixed-interval quadratic polynomial. -/
def fixedPolynomial (R σ : ℝ) : ℝ :=
  (∫ v in δ..R, J 0 v * g 0 v) +
    (∫ v in δ..R, productD1 g J 0 v) * σ +
    (1 / 2 * ∫ v in δ..R, productD2 g J 0 v) * σ ^ 2

variable {R : ℝ} (hR : R ∈ Ioo δ V) (hz : g 0 R = 0)
include hR hz

private theorem old_mem : Icc δ R ⊆ active g δ V := by
  rw [h.active_eq hR hz]

private theorem product_cont {σ : ℝ} (hσ : σ ∈ Icc 0 ε) :
    ContinuousOn (fun v => J σ v * g σ v) (Icc δ R) :=
  ((h.weight_continuous σ hσ).mul (h.gap_continuous σ hσ)).mono (h.old_mem hR hz)

private theorem productRemainder_cont {σ : ℝ} (hσ : σ ∈ Icc 0 ε) :
    ContinuousOn (productRemainder (g := g) (J := J) σ) (Icc δ R) :=
  ((h.product_cont hR hz hσ).sub
    (((h.product_cont hR hz ⟨le_rfl, h.epsilon_pos.le⟩).add
      ((h.first_continuous.mono (h.old_mem hR hz)).mul continuousOn_const)).add
      (((h.second_continuous.mono (h.old_mem hR hz)).div_const 2).mul
        continuousOn_const))).div_const _

/-- Polynomial subtraction and division commute with the fixed integral. -/
theorem fixed_remainder_eq {σ : ℝ} (hσ : σ ∈ Icc 0 ε) :
    (fixed (g := g) (J := J) (δ := δ) R σ -
      fixedPolynomial (g := g) (J := J) (δ := δ) R σ) / σ ^ 2 =
        ∫ v in δ..R, productRemainder (g := g) (J := J) σ v := by
  have hi0 := (h.product_cont hR hz ⟨le_rfl, h.epsilon_pos.le⟩).intervalIntegrable_of_Icc (μ := volume) hR.1.le
  have hi1 := (h.first_continuous.mono (h.old_mem hR hz)).intervalIntegrable_of_Icc (μ := volume) hR.1.le
  have hi2 := (h.second_continuous.mono (h.old_mem hR hz)).intervalIntegrable_of_Icc (μ := volume) hR.1.le
  unfold productRemainder fixed fixedPolynomial
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((h.product_cont hR hz hσ).intervalIntegrable_of_Icc hR.1.le)
    ((hi0.add (hi1.mul_const σ)).add ((hi2.div_const 2).mul_const (σ ^ 2))),
    intervalIntegral.integral_add (hi0.add (hi1.mul_const σ))
      ((hi2.div_const 2).mul_const (σ ^ 2)),
    intervalIntegral.integral_add hi0 (hi1.mul_const σ)]
  simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_div]
  ring

/-- Pointwise right little-o for the fixed integral, via dominated convergence
 of the ordinary scalar Taylor remainders. -/
theorem fixed_remainder_limit :
    Tendsto (fun σ => (fixed (g := g) (J := J) (δ := δ) R σ -
      fixedPolynomial (g := g) (J := J) (δ := δ) R σ) / σ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun σ => ∫ v in δ..R, productRemainder (g := g) (J := J) σ v)
      (𝓝[>] 0) (𝓝 (∫ _ in δ..R, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B)
    · filter_upwards [eventually_right h.epsilon_pos] with σ hσ
      exact ((h.productRemainder_cont hR hz (Ioc_subset_Icc_self hσ)).intervalIntegrable_of_Icc
        hR.1.le).def'.aestronglyMeasurable
    · filter_upwards [eventually_right h.epsilon_pos] with σ hσ
      filter_upwards with v hv
      rw [uIoc_of_le hR.1.le] at hv
      simpa only [productRemainder, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg σ)] using
        quadratic_bound h.second_nonneg hσ
          (h.product_deriv v (h.old_mem hR hz (Ioc_subset_Icc_self hv)))
          (h.product_deriv2 v (h.old_mem hR hz (Ioc_subset_Icc_self hv)))
          (fun s hs => h.second_bound s hs v (h.old_mem hR hz (Ioc_subset_Icc_self hv)))
    · exact intervalIntegrable_const
    · filter_upwards with v hv
      rw [uIoc_of_le hR.1.le] at hv
      exact (quadratic_peano h.epsilon_pos
        (h.product_deriv v (h.old_mem hR hz (Ioc_subset_Icc_self hv)))
        (h.product_deriv2 v (h.old_mem hR hz (Ioc_subset_Icc_self hv)) 0
          ⟨le_rfl, h.epsilon_pos.le⟩)).tendsto_div_nhds_zero
  simp only [intervalIntegral.integral_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_right h.epsilon_pos] with σ hσ
  exact (h.fixed_remainder_eq hR hz (Ioc_subset_Icc_self hσ)).symm

/-- Uniform fixed-part domination on the whole supplied right interval. -/
theorem fixed_remainder_bound {σ : ℝ} (hσ : σ ∈ Ioc 0 ε) :
    |(fixed (g := g) (J := J) (δ := δ) R σ -
      fixedPolynomial (g := g) (J := J) (δ := δ) R σ) / σ ^ 2| ≤ 2 * B * (V - δ) := by
  rw [h.fixed_remainder_eq hR hz (Ioc_subset_Icc_self hσ)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := δ) (b := R) (f := productRemainder (g := g) (J := J) σ) (C := 2 * B) (by
      intro v hv
      rw [uIoc_of_le hR.1.le] at hv
      simpa only [productRemainder, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg σ)] using
        quadratic_bound h.second_nonneg hσ
          (h.product_deriv v (h.old_mem hR hz (Ioc_subset_Icc_self hv)))
          (h.product_deriv2 v (h.old_mem hR hz (Ioc_subset_Icc_self hv)))
          (fun s hs => h.second_bound s hs v (h.old_mem hR hz (Ioc_subset_Icc_self hv))))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hR.1.le)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hR.2.le δ)
    (mul_nonneg (by norm_num) h.second_nonneg))

/-! ## Localization and domination of the lost layer -/

/-- The local correction: `max 0 g - g = max 0 (-g)`. -/
def loss (σ v : ℝ) : ℝ := J σ v * max 0 (-g σ v)

private theorem loss_cont {σ : ℝ} (hσ : σ ∈ Icc 0 ε) :
    ContinuousOn (loss (g := g) (J := J) σ) (Icc δ R) :=
  ((h.weight_continuous σ hσ).mul (continuousOn_const.sup
    (h.gap_continuous σ hσ).neg)).mono (h.old_mem hR hz)

omit h hR hz in
private theorem hinge_identity (σ v : ℝ) :
    J σ v * max 0 (g σ v) = J σ v * g σ v + loss (g := g) (J := J) σ v := by
  unfold loss
  rcases le_total 0 (g σ v) with hv | hv
  · rw [max_eq_right hv, max_eq_left (neg_nonpos.mpr hv)]
    ring
  · rw [max_eq_left hv, max_eq_right (neg_nonneg.mpr hv)]
    ring

/-- The actual fibre equals its smooth fixed part plus the lost-layer correction. -/
theorem fibre_eq_fixed_add_loss {σ : ℝ} (hσ : σ ∈ Icc 0 ε) :
    fibre g J δ V σ = fixed (g := g) (J := J) (δ := δ) R σ +
      ∫ v in δ..R, loss (g := g) (J := J) σ v := by
  have htail (v : ℝ) (hv : v ∈ Icc R V) : J σ v * max 0 (g σ v) = 0 := by
    have hgv : v ∈ Icc δ V := ⟨hR.1.le.trans hv.1, hv.2⟩
    have ht := (h.nonopening σ hσ v hgv).2
    have hn := h.strictAnti.antitoneOn (Ioo_subset_Icc_self hR) hgv hv.1
    rw [max_eq_left (by linarith : g σ v ≤ 0), mul_zero]
  have hitail : IntervalIntegrable (fun v => J σ v * max 0 (g σ v)) volume R V := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
    rw [uIoc_of_le hR.2.le] at hv
    exact (htail v (Ioc_subset_Icc_self hv)).symm
  have hzero : (∫ v in R..V, J σ v * max 0 (g σ v)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with v hv
    rw [uIoc_of_le hR.2.le] at hv
    exact htail v (Ioc_subset_Icc_self hv)
  have hic := (((h.weight_continuous σ hσ).mul
    ((continuousOn_const (c := (0 : ℝ))).sup (h.gap_continuous σ hσ))).mono (h.old_mem hR hz)).intervalIntegrable_of_Icc (μ := volume) hR.1.le
  unfold fibre fixed
  rw [← intervalIntegral.integral_add_adjacent_intervals hic hitail, hzero, add_zero]
  simp_rw [hinge_identity]
  exact intervalIntegral.integral_add
    ((h.product_cont hR hz hσ).intervalIntegrable_of_Icc hR.1.le)
    ((h.loss_cont hR hz hσ).intervalIntegrable_of_Icc hR.1.le)

/-- Every lost point lies within `A * σ / c` of the old root. -/
theorem crossing_layer {σ v : ℝ} (hσ : σ ∈ Icc 0 ε) (hv : v ∈ Icc δ R)
    (hg : g σ v ≤ 0) : R - v ≤ A * σ / c := by
  have ht := (h.nonopening σ hσ v ⟨hv.1, hv.2.trans hR.2.le⟩).1
  have hn := h.null_decrease v ⟨hv.1, hv.2.trans hR.2.le⟩ R
    (Ioo_subset_Icc_self hR) hv.2
  apply (le_div_iff₀ h.transverse_pos).mpr
  nlinarith

/-- Away from that layer the correction is exactly zero. -/
theorem loss_zero {σ v : ℝ} (hσ : σ ∈ Icc 0 ε) (hv : v ∈ Icc δ R)
    (hvfar : v ≤ R - A * σ / c) : loss (g := g) (J := J) σ v = 0 := by
  have ht := (h.nonopening σ hσ v ⟨hv.1, hv.2.trans hR.2.le⟩).1
  have hn := h.null_decrease v ⟨hv.1, hv.2.trans hR.2.le⟩ R
    (Ioo_subset_Icc_self hR) hv.2
  have hwidth : A * σ ≤ c * (R - v) := by
    have := (div_le_iff₀ h.transverse_pos).mp (show A * σ / c ≤ R - v by linarith)
    nlinarith
  unfold loss
  rw [max_eq_left (by linarith : -g σ v ≤ 0), mul_zero]

/-- Pointwise size bound throughout the old active interval. -/
theorem loss_bound {σ v : ℝ} (hσ : σ ∈ Icc 0 ε) (hv : v ∈ Icc δ R) :
    |loss (g := g) (J := J) σ v| ≤ M * A * σ := by
  have hm := h.old_mem hR hz hv
  have ht := (h.nonopening σ hσ v hm.1).1
  have hmax : max 0 (-g σ v) ≤ A * σ := max_le (mul_nonneg h.speed_nonneg hσ.1)
    (by linarith [hm.2])
  unfold loss
  rw [abs_mul, abs_of_nonneg (show 0 ≤ max 0 (-g σ v) from le_max_left _ _)]
  calc
    _ ≤ M * (A * σ) := mul_le_mul (h.weight_bound σ hσ v hm) hmax
      (le_max_left _ _) h.weight_nonneg
    _ = _ := by ring

/-- The entire lost-layer integral has a quadratic bound, including fibres
 whose active interval is shorter than the nominal crossing-layer width. -/
theorem loss_integral_bound {σ : ℝ} (hσ : σ ∈ Ioc 0 ε) :
    |(∫ v in δ..R, loss (g := g) (J := J) σ v) / σ ^ 2| ≤ M * A ^ 2 / c := by
  have hs := Ioc_subset_Icc_self hσ
  have hwidth : 0 ≤ A * σ / c := div_nonneg (mul_nonneg h.speed_nonneg hs.1) h.transverse_pos.le
  have hi := (h.loss_cont hR hz hs).intervalIntegrable_of_Icc (μ := volume) hR.1.le
  have hM := h.weight_nonneg
  have hA := h.speed_nonneg
  have habs : |∫ v in δ..R, loss (g := g) (J := J) σ v| ≤
      (M * A * σ) * (A * σ / c) := by
    by_cases hshort : R - A * σ / c ≤ δ
    · have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := δ) (b := R) (f := loss (g := g) (J := J) σ) (by
          intro v hv
          rw [uIoc_of_le hR.1.le] at hv
          exact h.loss_bound hR hz hs (Ioc_subset_Icc_self hv))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hR.1.le)] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg hM hA) hs.1))
    · have hl : δ ≤ R - A * σ / c := (lt_of_not_ge hshort).le
      have hr : R - A * σ / c ≤ R := by linarith
      have hi1 := hi.mono_set (by
        rw [uIcc_of_le hl, uIcc_of_le hR.1.le]
        exact Icc_subset_Icc_right hr)
      have hi2 := hi.mono_set (by
        rw [uIcc_of_le hr, uIcc_of_le hR.1.le]
        exact Icc_subset_Icc_left hl)
      have hzero : (∫ v in δ..(R - A * σ / c), loss (g := g) (J := J) σ v) = 0 := by
        apply intervalIntegral.integral_zero_ae
        filter_upwards with v hv
        rw [uIoc_of_le hl] at hv
        exact h.loss_zero hR hz hs ⟨hv.1.le, hv.2.trans hr⟩ hv.2
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hzero, zero_add]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := R - A * σ / c) (b := R) (f := loss (g := g) (J := J) σ) (by
          intro v hv
          rw [uIoc_of_le hr] at hv
          exact h.loss_bound hR hz hs ⟨hl.trans hv.1.le, hv.2⟩)
      simpa only [Real.norm_eq_abs, sub_sub_cancel, abs_of_nonneg hwidth] using hb
  rw [abs_div, abs_of_nonneg (sq_nonneg σ)]
  apply (div_le_iff₀ (sq_pos_of_pos hσ.1)).mpr
  calc
    _ ≤ _ := habs
    _ = _ := by ring

/-! ## The moving-contact coefficient -/

/-- The moving-contact COEFFICIENT of `σ ^ 2`. -/
def contactCoefficient (R : ℝ) : ℝ :=
  J 0 R * (deriv (fun s => g s R) 0) ^ 2 / (2 * (-deriv (g 0) R))

private theorem root_active : R ∈ active g δ V :=
  h.old_mem hR hz (right_mem_Icc.mpr hR.1.le)

/-- Differentiability along a rescaled ray through the old contact. -/
theorem gap_line_deriv (u : ℝ) :
    HasDerivAt (fun s => g s (R - s * u))
      (deriv (fun s => g s R) 0 - u * deriv (g 0) R) 0 := by
  let L := fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) (0, R)
  have hd : HasFDerivAt (fun p : ℝ × ℝ => g p.1 p.2) L (0, R) :=
    (h.gap_differentiable R (h.root_active hR hz)).hasFDerivAt
  have ha : HasDerivAt (fun s => g s R) (L (1, 0)) 0 := by
    simpa only [Function.comp_def, id_eq] using
      hd.comp_hasDerivAt (f := fun s : ℝ => (s, R)) 0
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) R))
  have hb : HasDerivAt (g 0) (L (0, 1)) R :=
    hd.comp_hasDerivAt R ((hasDerivAt_const R 0).prodMk (hasDerivAt_id R))
  have hp : HasDerivAt (fun s : ℝ => (s, R - s * u)) (1, -u) 0 := by
    simpa using (hasDerivAt_id 0).prodMk (((hasDerivAt_id 0).mul_const u).const_sub R)
  have hdline := hd.comp_hasDerivAt_of_eq 0 hp (by simp)
  rw [ha.deriv, hb.deriv]
  convert hdline using 1
  have hv : (1, -u) = (1, 0) - u • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  rw [hv, map_sub, map_smul]
  rfl

private theorem gap_sigma_deriv : HasDerivAt (fun s => g s R) (deriv (fun s => g s R) 0) 0 := by
  simpa using h.gap_line_deriv hR hz 0

private theorem gap_v_deriv : HasDerivAt (g 0) (deriv (g 0) R) R := by
  have hd := (h.gap_differentiable R (h.root_active hR hz)).hasFDerivAt.comp_hasDerivAt R
    ((hasDerivAt_const R 0).prodMk (hasDerivAt_id R))
  exact hd.differentiableAt.hasDerivAt

/-- The two contact derivatives inherit the supplied finite-difference bounds. -/
theorem contact_derivative_bounds :
    -A ≤ deriv (fun s => g s R) 0 ∧ deriv (fun s => g s R) 0 ≤ 0 ∧
      deriv (g 0) R ≤ -c := by
  have ha : Tendsto (fun s => g s R / s) (𝓝[>] 0)
      (𝓝 (deriv (fun s => g s R) 0)) := by
    simpa [hz, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h.gap_sigma_deriv hR hz).tendsto_slope_zero_right
  have he : ∀ᶠ s in 𝓝[>] (0 : ℝ), -A ≤ g s R / s ∧ g s R / s ≤ 0 := by
    filter_upwards [eventually_right h.epsilon_pos] with s hs
    have ht := h.nonopening s (Ioc_subset_Icc_self hs) R (Ioo_subset_Icc_self hR)
    constructor
    · apply (le_div_iff₀ hs.1).mpr
      linarith [ht.1]
    · apply (div_le_iff₀ hs.1).mpr
      linarith [ht.2]
  refine ⟨ge_of_tendsto ha (he.mono fun _ hx => hx.1),
    le_of_tendsto ha (he.mono fun _ hx => hx.2), ?_⟩
  have hb : Tendsto (fun s => (g 0 (R + s) - g 0 R) / s) (𝓝[>] 0)
      (𝓝 (deriv (g 0) R)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h.gap_v_deriv hR hz).tendsto_slope_zero_right
  apply le_of_tendsto hb
  filter_upwards [eventually_right (sub_pos.mpr hR.2)] with s hs
  apply (div_le_iff₀ hs.1).mpr
  have hn := h.null_decrease R (Ioo_subset_Icc_self hR) (R + s)
    ⟨by linarith [hR.1, hs.1], by linarith [hs.2]⟩ (by linarith [hs.1])
  simpa using hn

/-- The rescaled correction integrand. -/
def rescaledLoss (R σ u : ℝ) : ℝ := loss (g := g) (J := J) σ (R - σ * u) / σ

omit h hR hz in
private theorem rescaledLoss_eq {σ : ℝ} (hσ : 0 < σ) (R u : ℝ) :
    rescaledLoss (g := g) (J := J) R σ u =
      J σ (R - σ * u) * max 0 (-g σ (R - σ * u) / σ) := by
  unfold rescaledLoss loss
  rw [mul_div_assoc, ← max_div_div_right hσ.le, zero_div]

/-- First-order linearization of the gap gives the complete boundary-layer
 profile. This does not require a perturbed root to exist for all `σ ≤ ε`. -/
theorem rescaledLoss_limit (u : ℝ) :
    Tendsto (fun σ => rescaledLoss (g := g) (J := J) R σ u) (𝓝[>] 0)
      (𝓝 (J 0 R * max 0 (-(deriv (fun s => g s R) 0 - u * deriv (g 0) R)))) := by
  have hg : Tendsto (fun σ => g σ (R - σ * u) / σ) (𝓝[>] 0)
      (𝓝 (deriv (fun s => g s R) 0 - u * deriv (g 0) R)) := by
    simpa [hz, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h.gap_line_deriv hR hz u).tendsto_slope_zero_right
  have hp : Tendsto (fun σ : ℝ => (σ, R - σ * u)) (𝓝[>] 0) (𝓝 (0, R)) := by
    have hc : ContinuousAt (fun σ : ℝ => (σ, R - σ * u)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hj := (h.weight_continuousAt R (h.root_active hR hz)).tendsto.comp hp
  have hl := hj.mul ((tendsto_const_nhds (x := (0 : ℝ))).sup_nhds hg.neg)
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simpa only [neg_div] using (rescaledLoss_eq hσ R u).symm

omit h hR hz in
private theorem rescaled_mem {K σ u : ℝ} (hσ : 0 ≤ σ)
    (hδ : δ ≤ R - σ * K) (hu : u ∈ Icc 0 K) : R - σ * u ∈ Icc δ R := by
  constructor
  · exact hδ.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left hu.2 hσ) R)
  · exact sub_le_self _ (mul_nonneg hσ hu.1)

/-- Change of variables on a layer large enough to contain all lost points. -/
theorem loss_rescaling {K σ : ℝ} (hK : 0 ≤ K) (hKA : A / c ≤ K)
    (hσ : σ ∈ Ioc 0 ε) (hδ : δ ≤ R - σ * K) :
    (∫ v in δ..R, loss (g := g) (J := J) σ v) / σ ^ 2 =
      ∫ u in (0)..K, rescaledLoss (g := g) (J := J) R σ u := by
  have hr : R - σ * K ≤ R := sub_le_self _ (mul_nonneg hσ.1.le hK)
  have hw : R - σ * K ≤ R - A * σ / c := by
    have := mul_le_mul_of_nonneg_left hKA hσ.1.le
    nlinarith [show σ * (A / c) = A * σ / c by ring]
  have hi := (h.loss_cont hR hz (Ioc_subset_Icc_self hσ)).intervalIntegrable_of_Icc
    (μ := volume) hR.1.le
  have hi1 := hi.mono_set (by rw [uIcc_of_le hδ, uIcc_of_le hR.1.le]; exact Icc_subset_Icc_right hr)
  have hi2 := hi.mono_set (by rw [uIcc_of_le hr, uIcc_of_le hR.1.le]; exact Icc_subset_Icc_left hδ)
  have hz1 : (∫ v in δ..(R - σ * K), loss (g := g) (J := J) σ v) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with v hv
    rw [uIoc_of_le hδ] at hv
    exact h.loss_zero hR hz (Ioc_subset_Icc_self hσ) ⟨hv.1.le, hv.2.trans hr⟩ (hv.2.trans hw)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hz1, zero_add]
  have hc := intervalIntegral.mul_integral_comp_sub_mul (f := loss (g := g) (J := J) σ) σ R
    (a := 0) (b := K)
  simp only [mul_zero, sub_zero] at hc
  rw [← hc]
  unfold rescaledLoss
  rw [intervalIntegral.integral_div]
  rw [pow_two, mul_div_mul_left _ _ hσ.1.ne']

omit h hR hz in
/-- Area of the limiting triangle. The factor `1/2` is explicit here. -/
theorem integral_affine_hinge {a d K : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (hK : a / d ≤ K) :
    (∫ u in (0)..K, max 0 (a - d * u)) = a ^ 2 / (2 * d) := by
  have har : 0 ≤ a / d := div_nonneg ha hd.le
  have hc : Continuous (fun u : ℝ => max 0 (a - d * u)) := by fun_prop
  have hleft : (∫ u in (0)..(a / d), max 0 (a - d * u)) =
      ∫ u in (0)..(a / d), a - d * u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le har] at hu
    change max 0 (a - d * u) = a - d * u
    rw [max_eq_right]
    have := (le_div_iff₀ hd).mp hu.2
    nlinarith
  have hright : (∫ u in (a / d)..K, max 0 (a - d * u)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with u hu
    rw [uIoc_of_le hK] at hu
    apply max_eq_left
    have := (div_le_iff₀ hd).mp hu.1.le
    nlinarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (a / d)) (hc.intervalIntegrable (a / d) K), hleft, hright, add_zero,
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_id.const_mul d),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), smul_eq_mul]
  field_simp
  ring

/-- The normalized contact correction converges to the moving-contact
 coefficient. Only this POINTWISE proof shrinks its neighborhood with `R-δ`.
 The preceding uniform bounds use the original, common `ε`. -/
theorem loss_integral_limit :
    Tendsto (fun σ => (∫ v in δ..R, loss (g := g) (J := J) σ v) / σ ^ 2)
      (𝓝[>] 0) (𝓝 (contactCoefficient (g := g) (J := J) R)) := by
  let K := A / c + 1
  have hK : 0 < K := add_pos_of_nonneg_of_pos
    (div_nonneg h.speed_nonneg h.transverse_pos.le) zero_lt_one
  have hKA : A / c ≤ K := by dsimp [K]; linarith
  have hsmall : ∀ᶠ σ : ℝ in 𝓝[>] 0, σ ∈ Ioc 0 ε ∧ δ ≤ R - σ * K := by
    filter_upwards [eventually_right h.epsilon_pos,
      eventually_right (div_pos (sub_pos.mpr hR.1) hK)] with σ hσ hσK
    refine ⟨hσ, ?_⟩
    have := (le_div_iff₀ hK).mp hσK.2
    linarith
  have hl : Tendsto (fun σ => ∫ u in (0)..K, rescaledLoss (g := g) (J := J) R σ u)
      (𝓝[>] 0) (𝓝 (∫ u in (0)..K,
        J 0 R * max 0 (-(deriv (fun s => g s R) 0 - u * deriv (g 0) R)))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M * A)
    · filter_upwards [hsmall] with σ hσ
      have hc : ContinuousOn (rescaledLoss (g := g) (J := J) R σ) (Icc 0 K) := by
        apply ContinuousOn.div_const
        exact (h.loss_cont hR hz (Ioc_subset_Icc_self hσ.1)).comp
          (by fun_prop) (fun _ hu => rescaled_mem hσ.1.1.le hσ.2 hu)
      exact (hc.intervalIntegrable_of_Icc hK.le).def'.aestronglyMeasurable
    · filter_upwards [hsmall] with σ hσ
      filter_upwards with u hu
      rw [uIoc_of_le hK.le] at hu
      have hb := h.loss_bound hR hz (Ioc_subset_Icc_self hσ.1)
        (rescaled_mem hσ.1.1.le hσ.2 (Ioc_subset_Icc_self hu))
      rw [rescaledLoss, Real.norm_eq_abs, abs_div, abs_of_pos hσ.1.1]
      exact (div_le_iff₀ hσ.1.1).mpr hb
    · exact intervalIntegrable_const
    · filter_upwards with u _hu
      exact h.rescaledLoss_limit hR hz u
  have hb := h.contact_derivative_bounds hR hz
  have hd : 0 < -deriv (g 0) R := lt_of_lt_of_le h.transverse_pos (by linarith [hb.2.2])
  have har : (-deriv (fun s => g s R) 0) / (-deriv (g 0) R) ≤ K := by
    apply le_trans _ hKA
    calc
      _ ≤ A / (-deriv (g 0) R) := div_le_div_of_nonneg_right (by linarith [hb.1]) hd.le
      _ ≤ A / c := div_le_div_of_nonneg_left h.speed_nonneg h.transverse_pos
        (by linarith [hb.2.2])
  have he : (∫ u in (0)..K,
        J 0 R * max 0 (-(deriv (fun s => g s R) 0 - u * deriv (g 0) R))) =
      contactCoefficient (g := g) (J := J) R := by
    rw [intervalIntegral.integral_const_mul]
    have hfun (u : ℝ) : -(deriv (fun s => g s R) 0 - u * deriv (g 0) R) =
        -deriv (fun s => g s R) 0 - (-deriv (g 0) R) * u := by ring
    simp_rw [hfun]
    rw [integral_affine_hinge (neg_nonneg.mpr hb.2.1) hd har]
    unfold contactCoefficient
    ring
  rw [he] at hl
  apply hl.congr'
  filter_upwards [hsmall] with σ hσ
  exact (h.loss_rescaling hR hz hK.le hKA hσ.1 hσ.2).symm

/-- The contact coefficient itself has the same fibre-independent bound. -/
theorem contactCoefficient_bound :
    |contactCoefficient (g := g) (J := J) R| ≤ M * A ^ 2 / c := by
  apply le_of_tendsto (h.loss_integral_limit hR hz).abs
  filter_upwards [eventually_right h.epsilon_pos] with σ hσ
  exact h.loss_integral_bound hR hz hσ

end Hypotheses

/-- The canonical old endpoint. It is used only in the strictly active regime. -/
def oldRoot (g : ℝ → ℝ → ℝ) (δ V : ℝ) : ℝ := sSup (active g δ V)

/-- Constant coefficient; zero in BOTH non-active regimes. -/
def F0 (g J : ℝ → ℝ → ℝ) (δ V : ℝ) : ℝ :=
  if 0 < g 0 δ then ∫ v in δ..oldRoot g δ V, J 0 v * g 0 v else 0

/-- Linear coefficient of the full product; zero at cutoff contact. -/
def F1 (g J : ℝ → ℝ → ℝ) (δ V : ℝ) : ℝ :=
  if 0 < g 0 δ then ∫ v in δ..oldRoot g δ V, productD1 g J 0 v else 0

/-- Quadratic COEFFICIENT, not the second derivative. In particular the
 contact term is divided by `2 * (-∂v g)`, not just `-∂v g`. The interior-root
 formula is deliberately NOT used at exact cutoff contact. -/
def F2 (g J : ℝ → ℝ → ℝ) (δ V : ℝ) : ℝ :=
  if 0 < g 0 δ then
    (1 / 2 * ∫ v in δ..oldRoot g δ V, productD2 g J 0 v) +
      Hypotheses.contactCoefficient (g := g) (J := J) (oldRoot g δ V)
  else 0

/-- Explicit uniform domination constant; independent of `g 0 δ` and `R-δ`. -/
def remainderBound (δ V c A M B : ℝ) : ℝ := 2 * B * (V - δ) + 2 * (M * A ^ 2 / c)

/-- Compatibility with the closed-set-integral convention in the contract. -/
theorem fibre_eq_setIntegral (g J : ℝ → ℝ → ℝ) {δ V : ℝ} (hδV : δ ≤ V) (σ : ℝ) :
    fibre g J δ V σ = ∫ v in Icc δ V, J σ v * max 0 (g σ v) := by
  rw [fibre, intervalIntegral.integral_of_le hδV, integral_Icc_eq_integral_Ioc]

/-- All three coefficients are exactly zero at contact or in the inactive regime. -/
theorem coefficients_zero (hg : g 0 δ ≤ 0) :
    F0 g J δ V = 0 ∧ F1 g J δ V = 0 ∧ F2 g J δ V = 0 := by
  simp [F0, F1, F2, not_lt.mpr hg]

namespace Hypotheses
variable (h : Hypotheses g J δ V ε c A M B)
include h

/-- The complete three-regime classification. -/
theorem three_regimes :
    (g 0 δ < 0 ∧ ∀ σ ∈ Icc 0 ε, fibre g J δ V σ = 0) ∨
    (g 0 δ = 0 ∧ ∀ σ ∈ Icc 0 ε, fibre g J δ V σ = 0) ∨
    (0 < g 0 δ ∧ ∃! R : ℝ, R ∈ Ioo δ V ∧ g 0 R = 0) := by
  rcases lt_trichotomy (g 0 δ) 0 with hi | hc | ha
  · exact Or.inl ⟨hi, fun _ hs => h.fibre_zero hi.le hs⟩
  · exact Or.inr (Or.inl ⟨hc, fun _ hs => h.fibre_zero hc.le hs⟩)
  · exact Or.inr (Or.inr ⟨ha, h.exists_unique_root ha⟩)

/-- In the active regime the canonical endpoint is the IVT root. -/
theorem oldRoot_eq {R : ℝ} (hR : R ∈ Ioo δ V) (hz : g 0 R = 0) :
    oldRoot g δ V = R := by
  rw [oldRoot, h.active_eq hR hz, csSup_Icc hR.1.le]

/-- Explicit coefficient formulas at any interior old root. -/
theorem coefficients_of_root {R : ℝ} (hR : R ∈ Ioo δ V) (hz : g 0 R = 0) :
    F0 g J δ V = (∫ v in δ..R, J 0 v * g 0 v) ∧
    F1 g J δ V = (∫ v in δ..R, deriv (fun s => J s v * g s v) 0) ∧
    F2 g J δ V = (1 / 2 * ∫ v in δ..R,
      deriv (fun s => deriv (fun t => J t v * g t v) s) 0) +
        J 0 R * (deriv (fun s => g s R) 0) ^ 2 / (2 * (-deriv (g 0) R)) := by
  have ha : 0 < g 0 δ := by
    have := h.strictAnti (left_mem_Icc.mpr h.cutoff_lt.le) (Ioo_subset_Icc_self hR) hR.1
    linarith
  simp [F0, F1, F2, ha, h.oldRoot_eq hR hz, productD1, productD2, contactCoefficient]

private theorem normalized_split {R σ : ℝ} (hR : R ∈ Ioo δ V) (hz : g 0 R = 0)
    (hσ : σ ∈ Ioc 0 ε) :
    (fibre g J δ V σ - (F0 g J δ V + F1 g J δ V * σ + F2 g J δ V * σ ^ 2)) / σ ^ 2 =
      (fixed (g := g) (J := J) (δ := δ) R σ -
        fixedPolynomial (g := g) (J := J) (δ := δ) R σ) / σ ^ 2 +
      ((∫ v in δ..R, loss (g := g) (J := J) σ v) / σ ^ 2 -
        contactCoefficient (g := g) (J := J) R) := by
  obtain ⟨h0, h1, h2⟩ := h.coefficients_of_root hR hz
  rw [h.fibre_eq_fixed_add_loss hR hz (Ioc_subset_Icc_self hσ), h0, h1, h2]
  unfold fixedPolynomial contactCoefficient productD2 productD1
  field_simp [hσ.1.ne']
  ring

/-- The normalized remainder tends to zero from the right, fibre by fibre.
 The exact-cutoff-contact case is pointwise zero, not an a.e. exception. -/
theorem remainder_limit :
    Tendsto (fun σ => (fibre g J δ V σ -
      (F0 g J δ V + F1 g J δ V * σ + F2 g J δ V * σ ^ 2)) / σ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  by_cases ha : 0 < g 0 δ
  · obtain ⟨R, ⟨hR, hz⟩, _⟩ := h.exists_unique_root ha
    have hl := (h.fixed_remainder_limit hR hz).add
      ((h.loss_integral_limit hR hz).sub_const (contactCoefficient (g := g) (J := J) R))
    simp only [sub_self, add_zero] at hl
    apply hl.congr'
    filter_upwards [eventually_right h.epsilon_pos] with σ hσ
    exact (h.normalized_split hR hz hσ).symm
  · obtain ⟨h0, h1, h2⟩ := coefficients_zero (J := J) (V := V) (le_of_not_gt ha)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_right h.epsilon_pos] with σ hσ
    simp [h.fibre_zero (le_of_not_gt ha) (Ioc_subset_Icc_self hσ), h0, h1, h2]

/-- The abstract monotone non-opening fibre theorem: genuine right little-o,
 with the explicitly defined piecewise coefficients above. -/
theorem right_quadratic_jet :
    (fun σ => fibre g J δ V σ -
      (F0 g J δ V + F1 g J δ V * σ + F2 g J δ V * σ ^ 2)) =o[𝓝[>] 0]
        (fun σ => σ ^ 2) := by
  apply (isLittleO_iff_tendsto' ?_).mpr h.remainder_limit
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact fun hz => False.elim ((pow_ne_zero 2 (ne_of_gt hσ)) hz)

/-- Domination on ONE COMMON right neighborhood. No minimum active height or
 minimum root-to-cutoff distance is assumed. This does NOT assert uniform
 little-o, which the regressions show to be false. -/
theorem normalized_remainder_bound {σ : ℝ} (hσ : σ ∈ Ioc 0 ε) :
    |fibre g J δ V σ - (F0 g J δ V + F1 g J δ V * σ + F2 g J δ V * σ ^ 2)| / σ ^ 2 ≤
      remainderBound δ V c A M B := by
  rw [← abs_of_nonneg (sq_nonneg σ), ← abs_div, abs_of_nonneg (sq_nonneg σ)]
  by_cases ha : 0 < g 0 δ
  · obtain ⟨R, ⟨hR, hz⟩, _⟩ := h.exists_unique_root ha
    rw [h.normalized_split hR hz hσ]
    calc
      _ ≤ |(fixed (g := g) (J := J) (δ := δ) R σ -
          fixedPolynomial (g := g) (J := J) (δ := δ) R σ) / σ ^ 2| +
          (|(∫ v in δ..R, loss (g := g) (J := J) σ v) / σ ^ 2| +
            |contactCoefficient (g := g) (J := J) R|) :=
        (abs_add _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ ≤ 2 * B * (V - δ) + (M * A ^ 2 / c + M * A ^ 2 / c) :=
        add_le_add (h.fixed_remainder_bound hR hz hσ)
          (add_le_add (h.loss_integral_bound hR hz hσ) (h.contactCoefficient_bound hR hz))
      _ = _ := by unfold remainderBound; ring
  · obtain ⟨h0, h1, h2⟩ := coefficients_zero (J := J) (V := V) (le_of_not_gt ha)
    simp only [h.fibre_zero (le_of_not_gt ha) (Ioc_subset_Icc_self hσ), h0, h1, h2,
      zero_mul, add_zero, sub_zero, zero_div, abs_zero]
    unfold remainderBound
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) h.second_nonneg)
      (sub_nonneg.mpr h.cutoff_lt.le))
      (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg h.weight_nonneg (sq_nonneg A))
        h.transverse_pos.le))

end Hypotheses
end MonotoneHinge
end BoundaryDraft
