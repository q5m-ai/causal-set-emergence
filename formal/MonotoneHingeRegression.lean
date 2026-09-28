import BoundaryDraft.MonotoneHingeIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Synthetic regressions for the monotone non-opening fibre theorem

These test the abstract analytic theorem, not the geometric jet still open in
#61. In particular the approaching-contact family has a common normalized bound
but does not have uniform little-o. The variable-weight regression differentiates
`J * g`, retaining both product-rule terms and the second-derivative factor two.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval ContDiff

noncomputable section
namespace BoundaryDraft.MonotoneHinge.Regression

/-- Affine test gap with cutoff `δ`. -/
def affineGap (q a d δ σ v : ℝ) : ℝ := q - a * σ - d * (v - δ)

/-- Constant test weight. -/
def unitWeight (_σ _v : ℝ) : ℝ := 1

theorem affine_sigma_deriv (q a d δ σ v : ℝ) :
    HasDerivAt (fun s => affineGap q a d δ s v) (-a) σ := by
  simpa [affineGap] using (((hasDerivAt_id σ).const_mul a).const_sub q).sub_const (d * (v - δ))

@[simp] theorem affine_productD1 (q a d δ σ v : ℝ) :
    productD1 (affineGap q a d δ) unitWeight σ v = -a := by
  simp only [productD1, unitWeight, one_mul]
  exact (affine_sigma_deriv q a d δ σ v).deriv

@[simp] theorem affine_productD2 (q a d δ σ v : ℝ) :
    productD2 (affineGap q a d δ) unitWeight σ v = 0 := by
  simp [productD2]

/-- One family of primitive inputs covers positive, zero, and negative `q`.
 No lower bound on positive `q` occurs anywhere. -/
theorem affine_hypotheses {q a d δ V ε : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hδV : δ < V) (hε : 0 < ε) (hq : q < d * (V - δ)) :
    Hypotheses (affineGap q a d δ) unitWeight δ V ε d a 1 0 where
  cutoff_lt := hδV
  epsilon_pos := hε
  transverse_pos := hd
  speed_nonneg := ha
  weight_nonneg := by norm_num
  second_nonneg := le_rfl
  null_continuous := by unfold affineGap; fun_prop
  null_decrease := by intros; dsimp [affineGap]; nlinarith
  clearance := by dsimp [affineGap]; linarith
  nonopening := by
    intro σ hσ v _hv
    dsimp [affineGap]
    constructor <;> nlinarith [mul_nonneg ha hσ.1]
  gap_continuous := by intros; unfold affineGap; fun_prop
  weight_continuous := by intros; exact continuousOn_const
  gap_differentiable := by intros; unfold affineGap; fun_prop
  weight_continuousAt := by intros; exact continuousAt_const
  product_deriv := by
    intro v _hv σ _hσ
    simpa only [unitWeight, one_mul, affine_productD1] using affine_sigma_deriv q a d δ σ v
  product_deriv2 := by
    intro v _hv σ _hσ
    simpa only [affine_productD1, affine_productD2] using hasDerivAt_const σ (-a)
  first_continuous := by
    change ContinuousOn (fun v => productD1 (affineGap q a d δ) unitWeight 0 v) _
    simp only [affine_productD1]
    exact continuousOn_const
  second_continuous := by
    change ContinuousOn (fun v => productD2 (affineGap q a d δ) unitWeight 0 v) _
    simp only [affine_productD2]
    exact continuousOn_const
  weight_bound := by intros; norm_num [unitWeight]
  second_bound := by intros; simp

/-- Direct evaluation of the actual affine hinge, also beyond closure of the
 perturbed active interval. -/
theorem affine_fibre {q a d δ V σ : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hδV : δ < V) (hq : q < d * (V - δ)) (hσ : 0 ≤ σ) :
    fibre (affineGap q a d δ) unitWeight δ V σ = (max 0 (q - a * σ)) ^ 2 / (2 * d) := by
  by_cases hpos : 0 ≤ q - a * σ
  · unfold fibre
    simp only [unitWeight, one_mul, affineGap]
    rw [intervalIntegral.integral_comp_sub_right
      (fun u => max 0 (q - a * σ - d * u)) δ, sub_self]
    rw [Hypotheses.integral_affine_hinge hpos hd, max_eq_right hpos]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg ha hσ]
  · have hneg := le_of_lt (lt_of_not_ge hpos)
    rw [max_eq_left hneg]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
    unfold fibre
    apply intervalIntegral.integral_zero_ae
    filter_upwards with v hv
    rw [uIoc_of_le hδV.le] at hv
    have hg : affineGap q a d δ σ v ≤ 0 := by
      dsimp [affineGap]
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hv.1.le)]
    simp [unitWeight, max_eq_left hg]

private theorem affine_integral (q a d δ σ R : ℝ) :
    (∫ v in δ..R, affineGap q a d δ σ v) =
      (q - a * σ + d * δ) * (R - δ) - d * (R ^ 2 - δ ^ 2) / 2 := by
  calc
    _ = ∫ v in δ..R, (q - a * σ + d * δ) - d * v := by
      apply intervalIntegral.integral_congr
      intro v _hv
      dsimp [affineGap]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_id.const_mul d),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
      simp only [smul_eq_mul]
      ring

/-- Exact interior coefficients; the boundary contribution is `a²/(2d)`,
 NOT the second derivative `a²/d`. -/
theorem affine_coefficients {q a d δ V : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hδV : δ < V) (hq : q < d * (V - δ)) (hpos : 0 < q) :
    F0 (affineGap q a d δ) unitWeight δ V = q ^ 2 / (2 * d) ∧
    F1 (affineGap q a d δ) unitWeight δ V = -a * q / d ∧
    F2 (affineGap q a d δ) unitWeight δ V = a ^ 2 / (2 * d) := by
  have h := affine_hypotheses ha hd hδV zero_lt_one hq
  have hR : δ + q / d ∈ Ioo δ V := by
    constructor
    · linarith [div_pos hpos hd]
    · have := (div_lt_iff₀ hd).mpr (show q < (V - δ) * d by nlinarith)
      linarith
  have hz : affineGap q a d δ 0 (δ + q / d) = 0 := by
    unfold affineGap
    field_simp
    ring
  have hr := h.oldRoot_eq hR hz
  have hgp : 0 < affineGap q a d δ 0 δ := by simpa [affineGap] using hpos
  have hdv : deriv (affineGap q a d δ 0) (δ + q / d) = -d := by
    have ht := (((hasDerivAt_id (δ + q / d)).sub_const δ).const_mul d).const_sub q
    change deriv (fun v => q - a * 0 - d * (v - δ)) (δ + q / d) = -d
    simpa using ht.deriv
  simp only [F0, F1, F2, if_pos hgp, hr, unitWeight, one_mul, affine_productD1,
    affine_productD2, intervalIntegral.integral_zero, mul_zero,
    Hypotheses.contactCoefficient, (affine_sigma_deriv q a d δ 0 (δ + q / d)).deriv,
    hdv, neg_neg, neg_sq, zero_add, intervalIntegral.integral_const, smul_eq_mul]
  rw [affine_integral]
  constructor
  · field_simp
    ring
  constructor
  · ring
  · trivial

/-- Interior regression applies the actual general little-o theorem. -/
theorem affine_interior_jet {q a d δ V : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hδV : δ < V) (hq : q < d * (V - δ)) (hpos : 0 < q) :
    (fun σ => fibre (affineGap q a d δ) unitWeight δ V σ -
      (q ^ 2 / (2 * d) + (-a * q / d) * σ + (a ^ 2 / (2 * d)) * σ ^ 2)) =o[𝓝[>] 0]
        (fun σ => σ ^ 2) := by
  obtain ⟨h0, h1, h2⟩ := affine_coefficients ha hd hδV hq hpos
  simpa only [h0, h1, h2] using
    (affine_hypotheses ha hd hδV zero_lt_one hq).right_quadratic_jet

/-- Exact cutoff contact: fibre AND all coefficients vanish on the right. -/
theorem exact_contact {a d δ V : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (hδV : δ < V) :
    (∀ σ, 0 ≤ σ → fibre (affineGap 0 a d δ) unitWeight δ V σ = 0) ∧
    F0 (affineGap 0 a d δ) unitWeight δ V = 0 ∧
    F1 (affineGap 0 a d δ) unitWeight δ V = 0 ∧
    F2 (affineGap 0 a d δ) unitWeight δ V = 0 := by
  refine ⟨?_, coefficients_zero (by simp [affineGap])⟩
  intro σ hσ
  have h := affine_hypotheses ha hd hδV (ε := σ + 1) (by linarith)
    (mul_pos hd (sub_pos.mpr hδV))
  exact h.fibre_zero (by simp [affineGap]) ⟨hσ, by linarith⟩

/-- Inactive regression, with no regularity needed on an empty active set. -/
theorem inactive {q a d δ V : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (hδV : δ < V) (hq : q < 0) :
    (∀ σ, 0 ≤ σ → fibre (affineGap q a d δ) unitWeight δ V σ = 0) ∧
    F0 (affineGap q a d δ) unitWeight δ V = 0 ∧
    F1 (affineGap q a d δ) unitWeight δ V = 0 ∧
    F2 (affineGap q a d δ) unitWeight δ V = 0 := by
  refine ⟨?_, coefficients_zero (by simpa [affineGap] using hq.le)⟩
  intro σ hσ
  have h := affine_hypotheses ha hd hδV (ε := σ + 1) (by linarith)
    (hq.trans (mul_pos hd (sub_pos.mpr hδV)))
  exact h.fibre_zero (by simpa [affineGap] using hq.le) ⟨hσ, by linarith⟩

/-- The normalized remainder of the approaching-contact family. -/
def familyRemainder (q σ : ℝ) : ℝ :=
  |fibre (affineGap q 1 1 0) unitWeight 0 2 σ -
    (F0 (affineGap q 1 1 0) unitWeight 0 2 +
      F1 (affineGap q 1 1 0) unitWeight 0 2 * σ +
      F2 (affineGap q 1 1 0) unitWeight 0 2 * σ ^ 2)| / σ ^ 2

/-- Common constants and common radius, all the way to `q = 0`. -/
theorem family_uniform_bound {q σ : ℝ} (hq : q ∈ Icc 0 1) (hσ : σ ∈ Ioc 0 1) :
    familyRemainder q σ ≤ 2 := by
  have h := affine_hypotheses (q := q) (a := 1) (d := 1) (δ := 0) (V := 2)
    (ε := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith [hq.2])
  simpa [familyRemainder, remainderBound] using h.normalized_remainder_bound hσ

/-- Along `q = σ/2`, with `q` approaching zero, the normalized error stays
 exactly `1/8`, despite the common bound above. -/
theorem family_diagonal {σ : ℝ} (hσ : σ ∈ Ioc 0 1) :
    familyRemainder (σ / 2) σ = 1 / 8 := by
  have hq : 0 < σ / 2 := by linarith [hσ.1]
  have hclear : σ / 2 < 1 * (2 - 0) := by linarith [hσ.2]
  obtain ⟨h0, h1, h2⟩ := affine_coefficients (a := 1) (d := 1) (δ := 0) (V := 2)
    (by norm_num) (by norm_num) (by norm_num) hclear hq
  unfold familyRemainder
  rw [h0, h1, h2, affine_fibre (by norm_num) (by norm_num) (by norm_num) hclear hσ.1.le]
  rw [max_eq_left (by linarith [hσ.1] : σ / 2 - 1 * σ ≤ 0)]
  have he : (0 : ℝ) ^ 2 / (2 * 1) -
      ((σ / 2) ^ 2 / (2 * 1) + (-1 * (σ / 2) / 1) * σ + (1 ^ 2 / (2 * 1)) * σ ^ 2) =
      -(σ ^ 2 / 8) := by ring
  rw [he, abs_neg, abs_of_nonneg (by positivity)]
  field_simp [hσ.1.ne']
  ring

/-- Uniform little-o would imply this eventual `1/16` estimate, which is false. -/
theorem not_uniform_little_o :
    ¬ ∀ᶠ σ : ℝ in 𝓝[>] 0, ∀ q ∈ Ioo (0 : ℝ) 1, familyRemainder q σ ≤ 1 / 16 := by
  intro he
  obtain ⟨σ, hσ, hb⟩ := ((eventually_right zero_lt_one).and he).exists
  have hq : σ / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have := hb (σ / 2) hq
  rw [family_diagonal hσ] at this
  norm_num at this

/-- The diagonal family really approaches cutoff contact from the active side. -/
theorem family_parameter_limit :
    Tendsto (fun σ : ℝ => σ / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hi : Tendsto (fun σ : ℝ => σ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hi.div_const (2 : ℝ)
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    change 0 < σ / 2
    exact div_pos hσ (by norm_num)

/-! ## Nonconstant smooth weight: all product-rule contributions survive -/

/-- Varies in BOTH coordinates, and has a nonzero second parameter derivative. -/
def smoothWeight (σ v : ℝ) : ℝ := (1 + σ + σ ^ 2) * (1 + v)

/-- The variable weight is jointly smooth, not just separately continuous. -/
theorem smooth_weight_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothWeight p.1 p.2) := by
  exact ((contDiff_const.add contDiff_fst).add (contDiff_fst.pow 2)).mul
    (contDiff_const.add contDiff_snd)

private theorem weight_sigma_deriv (σ v : ℝ) :
    HasDerivAt (fun s => smoothWeight s v) ((1 + 2 * σ) * (1 + v)) σ := by
  convert (((hasDerivAt_const σ 1).add (hasDerivAt_id σ)).add
    ((hasDerivAt_id σ).pow 2)).mul_const (1 + v) using 1
  simp only [id_eq]
  ring

@[simp] theorem smooth_productD1 (σ v : ℝ) :
    productD1 (affineGap 1 1 1 0) smoothWeight σ v = -(1 + v) * (v + 2 * v * σ + 3 * σ ^ 2) := by
  unfold productD1
  rw [((weight_sigma_deriv σ v).mul (affine_sigma_deriv 1 1 1 0 σ v)).deriv]
  dsimp [smoothWeight, affineGap]
  ring

private theorem smooth_deriv2 (σ v : ℝ) :
    HasDerivAt (fun s => productD1 (affineGap 1 1 1 0) smoothWeight s v)
      (-(1 + v) * (2 * v + 6 * σ)) σ := by
  simp_rw [smooth_productD1]
  convert (((hasDerivAt_const σ v).add ((hasDerivAt_id σ).const_mul (2 * v))).add
    (((hasDerivAt_id σ).pow 2).const_mul 3)).const_mul (-(1 + v)) using 1
  simp only [id_eq]
  ring

@[simp] theorem smooth_productD2 (σ v : ℝ) :
    productD2 (affineGap 1 1 1 0) smoothWeight σ v = -(1 + v) * (2 * v + 6 * σ) :=
  (smooth_deriv2 σ v).deriv

private theorem smooth_active {v : ℝ} (hv : v ∈ active (affineGap 1 1 1 0) 0 2) :
    v ∈ Icc (0 : ℝ) 1 := by
  have hv0 := hv.1.1
  have hv1 := hv.2
  dsimp [affineGap] at hv1
  exact ⟨hv0, by linarith⟩

/-- All primitive assumptions, with numerical uniform constants on the entire
 common rectangle. The second product derivative bound is not a Taylor premise. -/
theorem smooth_hypotheses :
    Hypotheses (affineGap 1 1 1 0) smoothWeight 0 2 1 1 1 6 16 := by
  have hb := affine_hypotheses (q := 1) (a := 1) (d := 1) (δ := 0) (V := 2) (ε := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine {
    cutoff_lt := hb.cutoff_lt
    epsilon_pos := hb.epsilon_pos
    transverse_pos := hb.transverse_pos
    speed_nonneg := hb.speed_nonneg
    weight_nonneg := by norm_num
    second_nonneg := by norm_num
    null_continuous := hb.null_continuous
    null_decrease := hb.null_decrease
    clearance := hb.clearance
    nonopening := hb.nonopening
    gap_continuous := hb.gap_continuous
    gap_differentiable := hb.gap_differentiable
    weight_continuous := ?_
    weight_continuousAt := ?_
    product_deriv := ?_
    product_deriv2 := ?_
    first_continuous := ?_
    second_continuous := ?_
    weight_bound := ?_
    second_bound := ?_ }
  · intros; unfold smoothWeight; fun_prop
  · intros; unfold smoothWeight; fun_prop
  · intro v _hv σ _hσ
    exact ((weight_sigma_deriv σ v).mul (affine_sigma_deriv 1 1 1 0 σ v)).differentiableAt.hasDerivAt
  · intro v _hv σ _hσ
    rw [smooth_productD2]
    exact smooth_deriv2 σ v
  · change ContinuousOn (fun v => productD1 (affineGap 1 1 1 0) smoothWeight 0 v) _
    simp only [smooth_productD1]
    fun_prop
  · change ContinuousOn (fun v => productD2 (affineGap 1 1 1 0) smoothWeight 0 v) _
    simp only [smooth_productD2]
    fun_prop
  · intro σ hσ v hv
    have hv := smooth_active hv
    have hs0 : 0 ≤ 1 + σ + σ ^ 2 := by nlinarith [hσ.1, sq_nonneg σ]
    have hs3 : 1 + σ + σ ^ 2 ≤ 3 := by nlinarith [hσ.1, hσ.2]
    have hv0 : 0 ≤ 1 + v := by linarith [hv.1]
    have hv2 : 1 + v ≤ 2 := by linarith [hv.2]
    unfold smoothWeight
    rw [abs_of_nonneg (mul_nonneg hs0 hv0)]
    nlinarith [mul_le_mul hs3 hv2 hv0 (by norm_num : (0 : ℝ) ≤ 3)]
  · intro σ hσ v hv
    have hv := smooth_active hv
    have hv0 : 0 ≤ 1 + v := by linarith [hv.1]
    have hv2 : 1 + v ≤ 2 := by linarith [hv.2]
    have hs0 : 0 ≤ 2 * v + 6 * σ := by linarith [hσ.1, hv.1]
    have hs8 : 2 * v + 6 * σ ≤ 8 := by linarith [hσ.2, hv.2]
    rw [smooth_productD2, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hv0 hs0)]
    nlinarith [mul_le_mul hv2 hs8 hs0 (by norm_num : (0 : ℝ) ≤ 2)]

/-- This is not a disguised constant-weight test. -/
theorem smooth_weight_nonconstant : smoothWeight 0 0 ≠ smoothWeight 0 1 ∧
    smoothWeight 0 0 ≠ smoothWeight 1 0 := by norm_num [smoothWeight]

/-- Missing `Jσ*gσ` or `Jσσ*g`, or using the second derivative instead
 of half of it, changes the explicitly checked coefficient `1/6`. -/
theorem smooth_coefficients :
    F0 (affineGap 1 1 1 0) smoothWeight 0 2 = 2 / 3 ∧
    F1 (affineGap 1 1 1 0) smoothWeight 0 2 = -5 / 6 ∧
    F2 (affineGap 1 1 1 0) smoothWeight 0 2 = 1 / 6 := by
  have hR : (1 : ℝ) ∈ Ioo 0 2 := by constructor <;> norm_num
  have hz : affineGap 1 1 1 0 0 1 = 0 := by norm_num [affineGap]
  have hr := smooth_hypotheses.oldRoot_eq hR hz
  have hp : 0 < affineGap 1 1 1 0 0 0 := by norm_num [affineGap]
  have h0 : (∫ v in (0 : ℝ)..1, smoothWeight 0 v * affineGap 1 1 1 0 0 v) = 2 / 3 := by
    calc
      _ = ∫ v in (0 : ℝ)..1, 1 - v ^ 2 := by
        apply intervalIntegral.integral_congr
        intro v _hv
        dsimp [smoothWeight, affineGap]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2)]
        norm_num
  have h1 : (∫ v in (0 : ℝ)..1, productD1 (affineGap 1 1 1 0) smoothWeight 0 v) = -5 / 6 := by
    calc
      _ = ∫ v in (0 : ℝ)..1, -v - v ^ 2 := by
        apply intervalIntegral.integral_congr
        intro v _hv
        rw [smooth_productD1]
        ring
      _ = _ := by
        have hi : IntervalIntegrable (fun v : ℝ => -v) volume 0 1 :=
          continuous_id.neg.intervalIntegrable 0 1
        rw [intervalIntegral.integral_sub hi (intervalIntegral.intervalIntegrable_pow 2),
          intervalIntegral.integral_neg (f := fun v : ℝ => v), integral_id, integral_pow]
        norm_num
  have h2 : (∫ v in (0 : ℝ)..1, productD2 (affineGap 1 1 1 0) smoothWeight 0 v) = -5 / 3 := by
    calc
      _ = ∫ v in (0 : ℝ)..1, -2 * v - 2 * v ^ 2 := by
        apply intervalIntegral.integral_congr
        intro v _hv
        rw [smooth_productD2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_id.const_mul (-2))
          ((intervalIntegral.intervalIntegrable_pow 2).const_mul 2),
          intervalIntegral.integral_const_mul (-2) (fun v : ℝ => v),
          intervalIntegral.integral_const_mul 2 (fun v : ℝ => v ^ 2), integral_id, integral_pow]
        norm_num
  have hdv : deriv (affineGap 1 1 1 0 0) 1 = -1 := by
    change deriv (fun v : ℝ => 1 - 1 * 0 - 1 * (v - 0)) 1 = -1
    simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).deriv
  simp only [F0, F1, F2, if_pos hp, hr, h0, h1, h2, Hypotheses.contactCoefficient,
    hdv, (affine_sigma_deriv 1 1 1 0 0 1).deriv]
  norm_num [smoothWeight]

/-- Nonconstant-weight regression invokes the general little-o conclusion. -/
theorem smooth_jet :
    (fun σ => fibre (affineGap 1 1 1 0) smoothWeight 0 2 σ -
      (2 / 3 + (-5 / 6) * σ + (1 / 6) * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  obtain ⟨h0, h1, h2⟩ := smooth_coefficients
  simpa only [h0, h1, h2] using smooth_hypotheses.right_quadratic_jet

end BoundaryDraft.MonotoneHinge.Regression
