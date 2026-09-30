import BoundaryDraft.DimensionMellin
import BoundaryDraft.AnalyticCore
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Vertical reduction and signed tail integration

These general analytic lemmas keep the finite-height vertical reduction
independent of its tail representation. Slice moment hypotheses are explicit
here; specialization to an actual dimension-dependent cone slice must prove
them, rather than putting normalization into a kernel definition.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The finite-height action reduction, with independent point/pair coefficients. -/
def verticalActionReduction (a β : ℝ) (F : ℝ → ℝ) (H : ℝ) : ℝ :=
  a * H - β * ∫ t : ℝ in Ioc 0 H, (H - t) * F t

/-- A tail integral, not the definition of the physical vertical reduction. -/
def verticalTailReduction (β : ℝ) (F : ℝ → ℝ) (H : ℝ) : ℝ :=
  -β * ∫ t : ℝ in Ioi H, (t - H) * F t

private def triangleWeight (n : ℕ) (F : ℝ → ℝ) (t H : ℝ) : ℝ :=
  (Ioo 0 t).indicator (fun H => H ^ n * (t - H) * F t) H

private theorem integrable_triangleWeight (n : ℕ) (F : ℝ → ℝ) (t : ℝ) :
    Integrable (triangleWeight n F t) := by
  unfold triangleWeight
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact (show Continuous (fun H : ℝ => H ^ n * (t - H) * F t) by fun_prop).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

private theorem integral_triangleWeight (n : ℕ) (F : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ H : ℝ, triangleWeight n F t H) =
      (t ^ (n + 2) / (((n : ℝ) + 1) * (n + 2))) * F t := by
  unfold triangleWeight
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht]
  have he (H : ℝ) : H ^ n * (t - H) * F t = (t * H ^ n - H ^ (n + 1)) * F t := by ring
  simp_rw [he]
  have hi₁ : IntervalIntegrable (fun x : ℝ => t * x ^ n) volume 0 t :=
    (show Continuous (fun x : ℝ => t * x ^ n) by fun_prop).intervalIntegrable 0 t
  have hi₂ : IntervalIntegrable (fun x : ℝ => x ^ (n + 1)) volume 0 t :=
    (show Continuous (fun x : ℝ => x ^ (n + 1)) by fun_prop).intervalIntegrable 0 t
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero,
    Nat.cast_add, Nat.cast_one]
  congr 1
  rw [show n + 1 + 1 = n + 2 by omega, pow_succ]
  field_simp
  ring

private theorem triangleWeight_norm (n : ℕ) (F : ℝ → ℝ) (t H : ℝ) :
    ‖triangleWeight n F t H‖ = triangleWeight n (fun t => ‖F t‖) t H := by
  by_cases hH : H ∈ Ioo 0 t
  · simp only [triangleWeight, indicator_of_mem hH, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hH.1.le n), abs_of_pos (sub_pos.mpr hH.2)]
  · simp [triangleWeight, indicator_of_not_mem hH]

private theorem measurable_triangleWeight (n : ℕ) (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (fun p : ℝ × ℝ => triangleWeight n F p.1 p.2) := by
  change Measurable ({p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator
    (fun p : ℝ × ℝ => p.2 ^ n * (p.1 - p.2) * F p.1))
  exact ((measurable_snd.pow_const n).mul (measurable_fst.sub measurable_snd) |>.mul
    (hF.comp measurable_fst)).indicator
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst))

private theorem integrable_triangleWeight_prod (n : ℕ) (F : ℝ → ℝ) (hF : Measurable F)
    (hi : IntegrableOn (fun t : ℝ => t ^ (n + 2) * F t) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ => triangleWeight n F p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (measurable_triangleWeight n F hF).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (integrable_triangleWeight n F), ?_⟩
  apply (hi.norm.div_const (((n : ℝ) + 1) * (n + 2))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp_rw [triangleWeight_norm]
  rw [integral_triangleWeight n (fun t => ‖F t‖) ht.le, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le _)]
  ring

private theorem integral_triangleWeight_column (n : ℕ) (F : ℝ → ℝ) {H : ℝ} (hH : 0 < H) :
    (∫ t : ℝ in Ioi 0, triangleWeight n F t H) =
      H ^ n * ∫ t : ℝ in Ioi H, (t - H) * F t := by
  have he : (fun t : ℝ => triangleWeight n F t H) =
      (Ioi H).indicator (fun t => H ^ n * (t - H) * F t) := by
    funext t
    by_cases ht : H < t <;> simp [triangleWeight, hH, ht]
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hH.le]
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

private theorem integral_triangleWeight_columns (n : ℕ) (F : ℝ → ℝ) :
    (fun H : ℝ => ∫ t : ℝ in Ioi 0, triangleWeight n F t H) =
      (Ioi 0).indicator (fun H => H ^ n * ∫ t : ℝ in Ioi H, (t - H) * F t) := by
  funext H
  by_cases hH : 0 < H
  · rw [indicator_of_mem (show H ∈ Ioi (0 : ℝ) from hH),
      integral_triangleWeight_column n F hH]
  · rw [indicator_of_not_mem (show H ∉ Ioi (0 : ℝ) from hH)]
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun t => by simp [triangleWeight, hH]

/-- A slice's absolutely integrable `(n+2)`-moment controls the entire signed
`n`-moment of its tail reduction. Absolute Fubini is proved before swapping. -/
theorem integrableOn_verticalTailReduction_moment (n : ℕ) (β : ℝ) (F : ℝ → ℝ)
    (hF : Measurable F)
    (hi : IntegrableOn (fun t : ℝ => t ^ (n + 2) * F t) (Ioi 0)) :
    IntegrableOn (fun H : ℝ => H ^ n * verticalTailReduction β F H) (Ioi 0) := by
  have hp := (integrable_triangleWeight_prod n F hF hi).integral_prod_right
  rw [integral_triangleWeight_columns n F,
    integrable_indicator_iff measurableSet_Ioi] at hp
  apply (hp.const_mul (-β)).congr
  exact Eventually.of_forall fun H => by simp only [verticalTailReduction]; ring

/-- General signed tail-moment formula, derived from the actual double integral. -/
theorem integral_verticalTailReduction_moment (n : ℕ) (β : ℝ) (F : ℝ → ℝ)
    (hF : Measurable F)
    (hi : IntegrableOn (fun t : ℝ => t ^ (n + 2) * F t) (Ioi 0)) :
    (∫ H : ℝ in Ioi 0, H ^ n * verticalTailReduction β F H) =
      -β / (((n : ℝ) + 1) * (n + 2)) * ∫ t : ℝ in Ioi 0, t ^ (n + 2) * F t := by
  have hs := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
    (f := fun t H : ℝ => triangleWeight n F t H) (integrable_triangleWeight_prod n F hF hi)
  rw [integral_triangleWeight_columns n F, integral_indicator measurableSet_Ioi] at hs
  have hr : (∫ t : ℝ in Ioi 0, ∫ H : ℝ, triangleWeight n F t H) =
      (1 / (((n : ℝ) + 1) * (n + 2))) * ∫ t : ℝ in Ioi 0, t ^ (n + 2) * F t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [integral_triangleWeight n F ht.le]
    ring
  rw [hr] at hs
  calc
    _ = -β * ∫ H : ℝ in Ioi 0, H ^ n * ∫ t : ℝ in Ioi H, (t - H) * F t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro H _
      simp only [verticalTailReduction]
      ring
    _ = _ := by rw [← hs]; ring

/-- The tail representation follows from both independently evaluated lower
slice moments. No divergent pieces are separately integrated. -/
theorem verticalActionReduction_eq_tail (a β : ℝ) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi 0))
    (htF : IntegrableOn (fun t : ℝ => t * F t) (Ioi 0))
    (h₀ : β * ∫ t : ℝ in Ioi 0, F t = a)
    (h₁ : (∫ t : ℝ in Ioi 0, t * F t) = 0) {H : ℝ} (hH : 0 ≤ H) :
    verticalActionReduction a β F H = verticalTailReduction β F H := by
  have hi : IntegrableOn (fun t : ℝ => (t - H) * F t) (Ioi 0) := by
    simpa only [sub_mul, mul_assoc] using htF.sub (hF.const_mul H)
  have hs := setIntegral_union (Ioc_disjoint_Ioi_same : Disjoint (Ioc 0 H) (Ioi H))
    measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self)
    (hi.mono_set (Ioi_subset_Ioi hH))
  rw [Ioc_union_Ioi_eq_Ioi hH] at hs
  have hfull : (∫ t : ℝ in Ioi 0, (t - H) * F t) =
      -H * ∫ t : ℝ in Ioi 0, F t := by
    simp_rw [sub_mul]
    rw [integral_sub htF (hF.const_mul H), integral_const_mul, h₁]
    ring
  rw [hfull] at hs
  have he : (∫ t : ℝ in Ioc 0 H, (H - t) * F t) =
      -(∫ t : ℝ in Ioc 0 H, (t - H) * F t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only
    ring
  unfold verticalActionReduction verticalTailReduction
  rw [he, ← h₀]
  nlinarith [congrArg (fun x : ℝ => β * x) hs]

/-- Unit mass is a consequence of the evaluated second slice moment, not part
of the definition of either reduction. -/
theorem integral_verticalActionReduction (a β : ℝ) (F : ℝ → ℝ)
    (hF : Measurable F) (hi₀ : IntegrableOn F (Ioi 0))
    (hi₁ : IntegrableOn (fun t : ℝ => t * F t) (Ioi 0))
    (hi₂ : IntegrableOn (fun t : ℝ => t ^ 2 * F t) (Ioi 0))
    (h₀ : β * ∫ t : ℝ in Ioi 0, F t = a)
    (h₁ : (∫ t : ℝ in Ioi 0, t * F t) = 0)
    (h₂ : -β * ∫ t : ℝ in Ioi 0, t ^ 2 * F t = 2) :
    IntegrableOn (verticalActionReduction a β F) (Ioi 0) ∧
      (∫ H : ℝ in Ioi 0, verticalActionReduction a β F H) = 1 := by
  have he (H : ℝ) (hH : H ∈ Ioi 0) := verticalActionReduction_eq_tail a β F hi₀ hi₁ h₀ h₁ hH.le
  constructor
  · have hi := integrableOn_verticalTailReduction_moment 0 β F hF hi₂
    simp only [pow_zero, one_mul] at hi
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    exact (he H hH).symm
  · calc
      _ = ∫ H : ℝ in Ioi 0, verticalTailReduction β F H :=
        setIntegral_congr_fun measurableSet_Ioi he
      _ = 1 := by
        have hm := integral_verticalTailReduction_moment 0 β F hF hi₂
        simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, one_mul] at hm
        rw [hm]
        nlinarith [h₂]

/-- Source-only normal cutoff after the complete vertical partner reduction.
The integration is not restricted in the partner variable of the action. -/
def regulatedVerticalReduction (G χ : ℝ → ℝ) (κ k : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, χ s * (k * G (k * (κ * s)))

/-- Exact rescaling of the regulated observable, retaining the signed kernel. -/
theorem regulatedVerticalReduction_rescale (G χ : ℝ → ℝ) {κ k : ℝ}
    (hκ : 0 < κ) (hk : 0 < k) :
    regulatedVerticalReduction G χ κ k =
      κ⁻¹ * ∫ u : ℝ in Ioi 0, G u * χ ((k⁻¹ * u) / κ) := by
  let f : ℝ → ℝ := fun u => G u * χ (u / (k * κ))
  have hs := integral_comp_mul_left_Ioi f 0 (mul_pos hk hκ)
  simp only [mul_zero, smul_eq_mul] at hs
  have he (s : ℝ) : f ((k * κ) * s) = χ s * G (k * (κ * s)) := by
    dsimp [f]
    rw [mul_div_cancel_left₀ _ (mul_ne_zero hk.ne' hκ.ne')]
    ring
  simp_rw [he] at hs
  calc
    _ = k * ∫ s : ℝ in Ioi 0, χ s * G (k * (κ * s)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp only [regulatedVerticalReduction]
      ring
    _ = k * ((k * κ)⁻¹ * ∫ u : ℝ in Ioi 0, f u) := by rw [hs]
    _ = κ⁻¹ * ∫ u : ℝ in Ioi 0, G u * χ ((k⁻¹ * u) / κ) := by
      have hfactor : k * (k * κ)⁻¹ = κ⁻¹ := by field_simp
      rw [← mul_assoc, hfactor]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp [f]
      congr 2
      field_simp

/-- Signed concentration produces the inverse slope from an independently
proved mass; positivity of `G` is neither used nor assumed. -/
theorem regulatedVerticalReduction_limit (G χ : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hmass : (∫ u : ℝ in Ioi 0, G u) = 1) (hχ : Continuous χ)
    (C : ℝ) (hbound : ∀ s, ‖χ s‖ ≤ C) (hχ₀ : χ 0 = 1) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (regulatedVerticalReduction G χ κ) atTop (𝓝 (1 / κ)) := by
  have hl := signed_rescaling_limit (volume.restrict (Ioi 0)) G (fun x => χ (x / κ))
    hG (hχ.comp (continuous_id.div_const κ)) C (fun x => hbound _)
  simp only [hmass, one_mul, zero_div, hχ₀] at hl
  have hi := (hl.comp tendsto_inv_atTop_zero).const_mul κ⁻¹
  simp only [mul_one, one_div] at hi ⊢
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
  exact (regulatedVerticalReduction_rescale G χ hκ hk).symm

/-- The physical density scale is a derived positive power in every dimension. -/
theorem regulatedVerticalReduction_density_limit (d : ℕ) (hd : 0 < d)
    (G χ : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hmass : (∫ u : ℝ in Ioi 0, G u) = 1) (hχ : Continuous χ)
    (C : ℝ) (hbound : ∀ s, ‖χ s‖ ≤ C) (hχ₀ : χ 0 = 1) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ρ : ℝ => regulatedVerticalReduction G χ κ (ρ ^ (1 / (d : ℝ))))
      atTop (𝓝 (1 / κ)) :=
  (regulatedVerticalReduction_limit G χ hG hmass hχ C hbound hχ₀ hκ).comp
    (tendsto_rpow_atTop (div_pos (by norm_num) (Nat.cast_pos.mpr hd)))

/-- A fixed compact normal cutoff really removes the exterior source integral;
it does not truncate the partner integral inside `G`. -/
theorem regulatedVerticalReduction_cutoff (G χ : ℝ → ℝ) (κ k a : ℝ)
    (hcut : ∀ s, a < s → χ s = 0) :
    regulatedVerticalReduction G χ κ k =
      ∫ s : ℝ in Ioc 0 a, χ s * (k * G (k * (κ * s))) := by
  unfold regulatedVerticalReduction
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  by_cases hs : s ∈ Ioc 0 a
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs.1), indicator_of_mem hs]
  · rw [indicator_of_not_mem hs]
    by_cases hs₀ : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs₀, hcut s (lt_of_not_ge (fun ha => hs ⟨hs₀, ha⟩)), zero_mul]
    · rw [indicator_of_not_mem hs₀]

/-- Tangential signed weights enter only through their integral. This scalar
conclusion still needs the independent spacetime reduction to describe an action. -/
theorem regulatedVerticalReduction_weighted_density_limit (d : ℕ) (hd : 0 < d)
    (G χ : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hmass : (∫ u : ℝ in Ioi 0, G u) = 1) (hχ : Continuous χ)
    (C W : ℝ) (hbound : ∀ s, ‖χ s‖ ≤ C) (hχ₀ : χ 0 = 1) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ρ : ℝ => W * regulatedVerticalReduction G χ κ (ρ ^ (1 / (d : ℝ))))
      atTop (𝓝 (W / κ)) := by
  simpa only [mul_one_div] using
    (regulatedVerticalReduction_density_limit d hd G χ hG hmass hχ C hbound hχ₀ hκ).const_mul W

/-- A fixed-observable Lipschitz error bound after signed mass cancellation.
The first absolute moment is required; a second moment is not assumed. -/
theorem regulatedVerticalReduction_error (G B : ℝ → ℝ)
    (hG : IntegrableOn G (Ioi 0)) (hmass : (∫ u : ℝ in Ioi 0, G u) = 1)
    (hG₁ : IntegrableOn (fun u : ℝ => u * |G u|) (Ioi 0)) (hB : Measurable B)
    (C L : ℝ) (hbound : ∀ r, 0 ≤ r → ‖B r‖ ≤ C)
    (hLip : ∀ r, 0 ≤ r → ‖B r - B 0‖ ≤ L * r)
    {κ k : ℝ} (hκ : 0 < κ) (hk : 0 < k) :
    ‖regulatedVerticalReduction G B κ k - κ⁻¹ * B 0‖ ≤
      (L * k⁻¹ / κ ^ 2) * ∫ u : ℝ in Ioi 0, u * |G u| := by
  have hi : IntegrableOn (fun u : ℝ => G u * B (k⁻¹ * u / κ)) (Ioi 0) := by
    apply (hG.norm.mul_const C).mono'
      (hG.aestronglyMeasurable.mul
        (hB.comp ((measurable_const.mul measurable_id).div_const κ)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change ‖G u * B (k⁻¹ * u / κ)‖ ≤ ‖G u‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hbound _ (div_nonneg (mul_nonneg (inv_nonneg.mpr hk.le) hu.le) hκ.le)) (norm_nonneg _)
  have he : regulatedVerticalReduction G B κ k - κ⁻¹ * B 0 =
      κ⁻¹ * ∫ u : ℝ in Ioi 0, G u * (B (k⁻¹ * u / κ) - B 0) := by
    rw [regulatedVerticalReduction_rescale G B hκ hk]
    simp_rw [mul_sub]
    rw [integral_sub hi (hG.mul_const (B 0)), integral_mul_const, hmass]
    ring
  have hest : ‖∫ u : ℝ in Ioi 0, G u * (B (k⁻¹ * u / κ) - B 0)‖ ≤
      (L * k⁻¹ / κ) * ∫ u : ℝ in Ioi 0, u * |G u| := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hG₁.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Real.norm_eq_abs (G u)]
    calc
      _ ≤ |G u| * (L * (k⁻¹ * u / κ)) :=
        mul_le_mul_of_nonneg_left
          (hLip _ (div_nonneg (mul_nonneg (inv_nonneg.mpr hk.le) hu.le) hκ.le)) (abs_nonneg _)
      _ = _ := by ring
  rw [he, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ)]
  convert mul_le_mul_of_nonneg_left hest (inv_nonneg.mpr hκ.le) using 1
  ring

end BoundaryDraft
