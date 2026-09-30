import BoundaryDraft.DimensionNormalizedKernel

/-!
# Absolute tails of the actual dimension-dependent reduced kernel

The finite-height action reduction is not redefined as a tail. Its independently
proved zeroth and first slice moments justify the tail representation. The
positive even-dimensional spatial leading coefficient then gives a negative
cubic reduced tail, with an absolute fifth-order remainder. The even second
absolute moment diverges, and its signed truncated integral tends to negative
infinity. Odd-dimensional absolute moments follow from the proved absolute
slice moments and Fubini.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft

private theorem reduced_integrable_inv_pow (n : ℕ) {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun t : ℝ => 1 / t ^ (n + 2)) (Ioi H) := by
  have hn : -((n + 2 : ℕ) : ℝ) < -1 := by
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  apply (integrableOn_Ioi_rpow_of_lt hn hH).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.rpow_neg (hH.trans ht).le, Real.rpow_natCast, one_div]

private theorem reduced_integral_inv_pow (n : ℕ) {H : ℝ} (hH : 0 < H) :
    (∫ t : ℝ in Ioi H, 1 / t ^ (n + 2)) = 1 / (((n : ℝ) + 1) * H ^ (n + 1)) := by
  have hn : -((n + 2 : ℕ) : ℝ) < -1 := by
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  calc
    _ = ∫ t : ℝ in Ioi H, t ^ (-((n + 2 : ℕ) : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Real.rpow_neg (hH.trans ht).le, Real.rpow_natCast, one_div]
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hn hH,
        show -((n + 2 : ℕ) : ℝ) + 1 = -((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hH.le, Real.rpow_natCast]
      rw [neg_div_neg_eq]
      simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev, one_mul]

private theorem reduced_weight_inv_pow (n : ℕ) (H : ℝ) {t : ℝ} (ht : 0 < t) :
    (t - H) / t ^ (n + 3) = 1 / t ^ (n + 2) - H * (1 / t ^ ((n + 1) + 2)) := by
  have he : n + 3 = (n + 2) + 1 := by omega
  rw [he, show (n + 1) + 2 = (n + 2) + 1 by omega, pow_succ]
  field_simp

/-- Absolute convergence of the model weighted power tail. -/
theorem integrableOn_vertical_power_tail (n : ℕ) {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun t : ℝ => (t - H) / t ^ (n + 3)) (Ioi H) := by
  apply ((reduced_integrable_inv_pow n hH).sub
    ((reduced_integrable_inv_pow (n + 1) hH).const_mul H)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (reduced_weight_inv_pow n H (hH.trans ht)).symm

/-- Exact model integral. At `n=2,4` the constants are `1/12,1/30`. -/
theorem integral_vertical_power_tail (n : ℕ) {H : ℝ} (hH : 0 < H) :
    (∫ t : ℝ in Ioi H, (t - H) / t ^ (n + 3)) =
      1 / (((n : ℝ) + 1) * (n + 2) * H ^ (n + 1)) := by
  calc
    _ = ∫ t : ℝ in Ioi H, 1 / t ^ (n + 2) - H * (1 / t ^ ((n + 1) + 2)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => reduced_weight_inv_pow n H (hH.trans ht))
    _ = _ := by
      rw [integral_sub (reduced_integrable_inv_pow n hH)
        ((reduced_integrable_inv_pow (n + 1) hH).const_mul H), integral_const_mul,
        reduced_integral_inv_pow n hH, reduced_integral_inv_pow (n + 1) hH]
      push_cast
      rw [pow_succ H (n + 1)]
      field_simp
      ring

/-- Integrating the actual error, rather than differentiating an asymptotic
remainder, gives the cubic leading term and a fifth-order absolute bound. -/
theorem verticalTailReduction_cubic_remainder (β : ℝ) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Ioi 0))
    (htF : IntegrableOn (fun t : ℝ => t * F t) (Ioi 0)) (D C : ℝ)
    (hrem : ∀ t : ℝ, 0 < t → |F t - D / t ^ 5| ≤ C / t ^ 7)
    {H : ℝ} (hH : 0 < H) :
    |verticalTailReduction β F H + β * D / (12 * H ^ 3)| ≤
      |β| * C / (30 * H ^ 5) := by
  have hi : IntegrableOn (fun t : ℝ => (t - H) * F t) (Ioi H) := by
    have hi₀ : IntegrableOn (fun t : ℝ => (t - H) * F t) (Ioi 0) := by
      simpa only [sub_mul] using htF.sub (hF.const_mul H)
    exact hi₀.mono_set (Ioi_subset_Ioi hH.le)
  have hid : IntegrableOn (fun t : ℝ => (t - H) * (D / t ^ 5)) (Ioi H) := by
    apply ((integrableOn_vertical_power_tail 2 hH).const_mul D).congr
    exact Eventually.of_forall (fun t => by dsimp only; norm_num only; ring)
  have hir : IntegrableOn (fun t : ℝ => (t - H) * (F t - D / t ^ 5)) (Ioi H) := by
    simpa only [mul_sub] using hi.sub hid
  have hmodel : (∫ t : ℝ in Ioi H, (t - H) * (D / t ^ 5)) = D / (12 * H ^ 3) := by
    calc
      _ = D * ∫ t : ℝ in Ioi H, (t - H) / t ^ 5 := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp only
        ring
      _ = _ := by
        have he := integral_vertical_power_tail 2 hH
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd, one_mul, OfNat.ofNat] at he
        rw [he]
        ring
  have he : verticalTailReduction β F H + β * D / (12 * H ^ 3) =
      -β * ∫ t : ℝ in Ioi H, (t - H) * (F t - D / t ^ 5) := by
    simp only [verticalTailReduction, mul_sub]
    rw [integral_sub hi hid, hmodel]
    ring
  have herror : |∫ t : ℝ in Ioi H, (t - H) * (F t - D / t ^ 5)| ≤ C / (30 * H ^ 5) := by
    calc
      _ ≤ ∫ t : ℝ in Ioi H, ‖(t - H) * (F t - D / t ^ 5)‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi H)) (fun t => (t - H) * (F t - D / t ^ 5))
      _ ≤ ∫ t : ℝ in Ioi H, C * ((t - H) / t ^ 7) := by
        apply setIntegral_mono_on hir.norm
          ((integrableOn_vertical_power_tail 4 hH).const_mul C) measurableSet_Ioi
        intro t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.le)]
        exact (mul_le_mul_of_nonneg_left (hrem t (hH.trans ht))
          (sub_nonneg.mpr ht.le)).trans_eq (by ring)
      _ = C / (30 * H ^ 5) := by
        rw [integral_const_mul]
        have he₇ := integral_vertical_power_tail 4 hH
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd, one_mul, OfNat.ofNat] at he₇
        rw [he₇]
        ring
  rw [he, abs_mul, abs_neg]
  exact (mul_le_mul_of_nonneg_left herror (abs_nonneg β)).trans_eq (by ring)

/-- The positive spatial leading coefficient, including the physical sphere
factor and the actual interval-volume coefficient. -/
def dimensionConeEvenTailCoefficient (n : ℕ) : ℝ :=
  let d := 2 * n + 2
  (dimensionSphereArea d / 2) *
    (dimensionSliceTaylorCoeff (((d : ℝ) - 3) / 2) (n + 2) *
      ∫ σ : ℝ in Ioi 0, σ ^ (n + 2) *
        dimensionKernel d (dimensionIntervalCoefficient d * σ ^ ((d : ℝ) / 2)))

/-- Positive magnitude of the negative cubic reduced-kernel leading term. -/
def dimensionPlaneEvenTailCoefficient (n : ℕ) : ℝ :=
  dimensionPairCoefficient (2 * n + 2) * dimensionConeEvenTailCoefficient n / 12

theorem dimensionConeEvenTailCoefficient_pos (n : ℕ) :
    0 < dimensionConeEvenTailCoefficient n :=
  mul_pos (half_pos (dimensionSphereArea_pos (2 * n + 2) (by omega)))
    (dimensionSigmaSlice_even_leading_pos n (dimensionIntervalCoefficient_pos _ (by omega)))

theorem dimensionPlaneEvenTailCoefficient_pos (n : ℕ) :
    0 < dimensionPlaneEvenTailCoefficient n :=
  div_pos (mul_pos (dimensionPairCoefficient_pos _ (by omega))
    (dimensionConeEvenTailCoefficient_pos n)) (by norm_num)

private theorem reduced_cone_eq_sigma (d : ℕ) (t : ℝ) :
    dimensionConeSlice d t = dimensionSphereArea d / 2 *
      dimensionSigmaSlice d (dimensionIntervalCoefficient d) t := by
  unfold dimensionConeSlice dimensionPhysicalSlice dimensionSphereArea
  ring

/-- The checked sigma-slice estimate transfers to the actual physical slice. -/
theorem dimensionConeSlice_even_leading_remainder (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      |dimensionConeSlice (2 * n + 2) t - dimensionConeEvenTailCoefficient n / t ^ 5| ≤
        C / t ^ 7 := by
  have hc := dimensionIntervalCoefficient_pos (2 * n + 2) (by omega)
  have hS := half_pos (dimensionSphereArea_pos (2 * n + 2) (by omega))
  obtain ⟨C, hC, hb⟩ := dimensionSigmaSlice_even_leading_remainder n hc
  refine ⟨dimensionSphereArea (2 * n + 2) / 2 * C, mul_pos hS hC, ?_⟩
  intro t ht
  have he : dimensionConeSlice (2 * n + 2) t - dimensionConeEvenTailCoefficient n / t ^ 5 =
      (dimensionSphereArea (2 * n + 2) / 2) *
        (dimensionSigmaSlice (2 * n + 2) (dimensionIntervalCoefficient (2 * n + 2)) t -
          (dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (n + 2) *
            (∫ σ : ℝ in Ioi 0, σ ^ (n + 2) * dimensionKernel (2 * n + 2)
              (dimensionIntervalCoefficient (2 * n + 2) * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2)))) /
            t ^ 5) := by
    rw [reduced_cone_eq_sigma]
    unfold dimensionConeEvenTailCoefficient
    ring
  rw [he, abs_mul, abs_of_pos hS]
  exact (mul_le_mul_of_nonneg_left (hb t ht) hS.le).trans_eq (by ring)

/-- Actual even-dimensional reduced kernel: a strictly negative cubic leading
term and an absolute `O(H^-5)` remainder, with no analytic tail hypothesis. -/
theorem dimensionPlaneKernel_even_leading_remainder (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H →
      |dimensionPlaneKernel (2 * n + 2) H + dimensionPlaneEvenTailCoefficient n / H ^ 3| ≤
        C / H ^ 5 := by
  obtain ⟨C, hC, hrem⟩ := dimensionConeSlice_even_leading_remainder n
  have hβ := dimensionPairCoefficient_pos (2 * n + 2) (by omega)
  refine ⟨dimensionPairCoefficient (2 * n + 2) * C / 30,
    div_pos (mul_pos hβ hC) (by norm_num), ?_⟩
  intro H hH
  have hF : IntegrableOn (dimensionConeSlice (2 * n + 2)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      integrableOn_dimensionConeSlice_moment (2 * n + 2) 0 (by omega) (by omega)
  have htF : IntegrableOn (fun t : ℝ => t * dimensionConeSlice (2 * n + 2) t) (Ioi 0) := by
    simpa only [pow_one] using
      integrableOn_dimensionConeSlice_moment (2 * n + 2) 1 (by omega) (by omega)
  have hh := verticalTailReduction_cubic_remainder (dimensionPairCoefficient (2 * n + 2))
    hF htF (dimensionConeEvenTailCoefficient n) C hrem hH
  rw [← dimensionPlaneKernel_eq_tail (2 * n + 2) (by omega) hH.le, abs_of_pos hβ] at hh
  have he : dimensionPairCoefficient (2 * n + 2) * dimensionConeEvenTailCoefficient n /
      (12 * H ^ 3) = dimensionPlaneEvenTailCoefficient n / H ^ 3 := by
    unfold dimensionPlaneEvenTailCoefficient
    ring
  rw [he] at hh
  exact hh.trans_eq (by ring)

/-- All natural moments of the actual odd-dimensional reduced kernel are
absolutely integrable; absolute slice Fubini supplies each order separately. -/
theorem integrableOn_dimensionPlaneKernel_odd_moment (n k : ℕ) :
    IntegrableOn (fun H : ℝ => H ^ k * dimensionPlaneKernel (2 * n + 3) H) (Ioi 0) := by
  have hF : IntegrableOn (fun t : ℝ => t ^ (k + 2) * dimensionConeSlice (2 * n + 3) t) (Ioi 0) :=
    integrableOn_dimensionPhysicalSlice_odd_moment n (k + 2)
      (dimensionIntervalCoefficient_pos _ (by omega))
  apply (integrableOn_verticalTailReduction_moment k (dimensionPairCoefficient (2 * n + 3))
    (dimensionConeSlice (2 * n + 3)) (measurable_dimensionConeSlice _) hF).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  rw [dimensionPlaneKernel_eq_tail (2 * n + 3) (by omega) hH.le]

/-- Explicit absolute-value formulation of the odd-dimensional moment result. -/
theorem integrableOn_dimensionPlaneKernel_odd_abs_moment (n k : ℕ) :
    IntegrableOn (fun H : ℝ => H ^ k * |dimensionPlaneKernel (2 * n + 3) H|) (Ioi 0) := by
  apply (integrableOn_dimensionPlaneKernel_odd_moment n k).abs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  rw [abs_mul, abs_of_nonneg (pow_nonneg hH.le k)]

private theorem reduced_quadratic_upper_bound {G : ℝ → ℝ} {A C : ℝ}
    (hA : 0 < A) (hrem : ∀ H : ℝ, 0 < H → |G H + A / H ^ 3| ≤ C / H ^ 5) :
    ∃ R : ℝ, 0 < R ∧ ∀ H : ℝ, R ≤ H → H ^ 2 * G H ≤ -(A / 2) / H := by
  let R : ℝ := max 1 (2 * C / A)
  refine ⟨R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro H hH
  have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  have hHA : 2 * C / A ≤ H := (le_max_right _ _).trans hH
  have hlarge : 2 * C ≤ A * H ^ 2 := by
    have hh := (div_le_iff₀ hA).mp hHA
    have hsq : H ≤ H ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hA.le]
  have hab : G H + A / H ^ 3 ≤ C / H ^ 5 :=
    (le_abs_self _).trans (hrem H hH0)
  have hm := mul_le_mul_of_nonneg_right hab (pow_nonneg hH0.le 5)
  have he₁ : (G H + A / H ^ 3) * H ^ 5 = H ^ 5 * G H + A * H ^ 2 := by field_simp; ring
  have he₂ : (C / H ^ 5) * H ^ 5 = C := by field_simp
  rw [he₁, he₂] at hm
  apply (mul_le_mul_right (pow_pos hH0 3)).mp
  have he₃ : (H ^ 2 * G H) * H ^ 3 = H ^ 5 * G H := by ring
  have he₄ : (-(A / 2) / H) * H ^ 3 = -(A / 2) * H ^ 2 := by field_simp; ring
  rw [he₃, he₄]
  nlinarith

/-- The actual even-dimensional reduced kernel is strictly negative beyond
some finite height. -/
theorem dimensionPlaneKernel_even_eventually_neg (n : ℕ) :
    ∀ᶠ H : ℝ in atTop, dimensionPlaneKernel (2 * n + 2) H < 0 := by
  obtain ⟨C, _, hC⟩ := dimensionPlaneKernel_even_leading_remainder n
  have hA := dimensionPlaneEvenTailCoefficient_pos n
  obtain ⟨R, hR, hb⟩ := reduced_quadratic_upper_bound hA hC
  filter_upwards [eventually_ge_atTop R] with H hH
  have hH0 : 0 < H := hR.trans_le hH
  have hneg : H ^ 2 * dimensionPlaneKernel (2 * n + 2) H < 0 :=
    (hb H hH).trans_lt (div_neg_of_neg_of_pos (neg_neg_of_pos (half_pos hA)) hH0)
  by_contra hn
  have hp := mul_nonneg (sq_nonneg H) (le_of_not_gt hn)
  linarith

private theorem reduced_not_integrable_second_abs {G : ℝ → ℝ} {A C : ℝ}
    (hA : 0 < A) (hrem : ∀ H : ℝ, 0 < H → |G H + A / H ^ 3| ≤ C / H ^ 5) :
    ¬ IntegrableOn (fun H : ℝ => H ^ 2 * |G H|) (Ioi 0) := by
  intro hi
  obtain ⟨R, hR, hb⟩ := reduced_quadratic_upper_bound hA hrem
  have hg : IntegrableOn (fun H : ℝ => (A / 2) / H) (Ioi R) := by
    apply (hi.mono_set (Ioi_subset_Ioi hR.le)).mono'
      (measurable_const.div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    have hH0 : 0 < H := hR.trans hH
    rw [Real.norm_eq_abs, id_eq, abs_of_nonneg (div_nonneg (half_pos hA).le hH0.le)]
    have hh := hb H hH.le
    rw [neg_div] at hh
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs (G H)) (sq_nonneg H)]
  have hinv : IntegrableOn (fun H : ℝ => H ^ (-1 : ℝ)) (Ioi R) := by
    apply (hg.const_mul (A / 2)⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H _hH
    rw [Real.rpow_neg_one]
    simp only [div_eq_mul_inv]
    rw [← mul_assoc, inv_mul_cancel₀ (show A * (2 : ℝ)⁻¹ ≠ 0 by positivity), one_mul]
  have hh := (integrableOn_Ioi_rpow_iff hR).mp hinv
  linarith

/-- The actual even-dimensional reduced kernel has no second absolute height
moment. This is an obstruction, not a value obtained by continuation. -/
theorem not_integrableOn_dimensionPlaneKernel_even_abs_second (n : ℕ) :
    ¬ IntegrableOn (fun H : ℝ => H ^ 2 * |dimensionPlaneKernel (2 * n + 2) H|) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := dimensionPlaneKernel_even_leading_remainder n
  exact reduced_not_integrable_second_abs (dimensionPlaneEvenTailCoefficient_pos n) hC

/-- The ordinary signed second height moment is not Bochner integrable. -/
theorem not_integrableOn_dimensionPlaneKernel_even_second (n : ℕ) :
    ¬ IntegrableOn (fun H : ℝ => H ^ 2 * dimensionPlaneKernel (2 * n + 2) H) (Ioi 0) := by
  intro hi
  apply not_integrableOn_dimensionPlaneKernel_even_abs_second n
  apply hi.abs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  rw [abs_mul, abs_of_nonneg (pow_nonneg hH.le 2)]

private theorem reduced_integrable_moment_local {G : ℝ → ℝ}
    (hi : IntegrableOn G (Ioi 0)) (k : ℕ) (T : ℝ) :
    IntegrableOn (fun H : ℝ => H ^ k * G H) (Ioc 0 T) := by
  have hil := hi.mono_set (Ioc_subset_Ioi_self : Ioc 0 T ⊆ Ioi (0 : ℝ))
  apply (hil.norm.const_mul (|T| ^ k)).mono'
    ((continuous_id.pow k).aestronglyMeasurable.mul hil.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with H hH
  simp only [Pi.mul_apply, id_eq, norm_mul, Real.norm_eq_abs, abs_pow,
    abs_of_pos hH.1]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hH.1.le (hH.2.trans (le_abs_self T)) k) (abs_nonneg _)

/-- Local natural moments remain integrable even when the full moment diverges. -/
theorem integrableOn_dimensionPlaneKernel_moment_local (d : ℕ) (hd : 2 ≤ d)
    (k : ℕ) (T : ℝ) :
    IntegrableOn (fun H : ℝ => H ^ k * dimensionPlaneKernel d H) (Ioc 0 T) :=
  reduced_integrable_moment_local (integrableOn_dimensionPlaneKernel d hd) k T

private theorem reduced_truncated_second_tendsto_atBot {G : ℝ → ℝ}
    (hi : IntegrableOn G (Ioi 0)) {A C : ℝ} (hA : 0 < A)
    (hrem : ∀ H : ℝ, 0 < H → |G H + A / H ^ 3| ≤ C / H ^ 5) :
    Tendsto (fun T : ℝ => ∫ H : ℝ in Ioc 0 T, H ^ 2 * G H) atTop atBot := by
  obtain ⟨R, hR, hb⟩ := reduced_quadratic_upper_bound hA hrem
  let B : ℝ := ∫ H : ℝ in Ioc 0 R, H ^ 2 * G H
  have hlog : Tendsto (fun T : ℝ => Real.log (T / R)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop).atTop_div_const hR)
  have hlim : Tendsto (fun T : ℝ => B + (-(A / 2)) * Real.log (T / R)) atTop atBot :=
    tendsto_const_nhds.add_atBot (hlog.const_mul_atTop_of_neg (neg_neg_of_pos (half_pos hA)))
  apply tendsto_atBot_mono' atTop _ hlim
  filter_upwards [eventually_ge_atTop R] with T hT
  have hil := reduced_integrable_moment_local hi 2 T
  have hirt : IntegrableOn (fun H : ℝ => H ^ 2 * G H) (Ioc R T) :=
    hil.mono_set (Ioc_subset_Ioc_left hR.le)
  have hlogi : IntegrableOn (fun H : ℝ => -(A / 2) / H) (Ioc R T) := by
    apply (ContinuousOn.integrableOn_Icc
      (show ContinuousOn (fun H : ℝ => -(A / 2) / H) (Icc R T) from
        continuousOn_const.div continuousOn_id
          (fun H hH => ne_of_gt (hR.trans_le hH.1)))).mono_set Ioc_subset_Icc_self
  have hmono : (∫ H : ℝ in Ioc R T, H ^ 2 * G H) ≤
      ∫ H : ℝ in Ioc R T, -(A / 2) / H :=
    setIntegral_mono_on hirt hlogi measurableSet_Ioc (fun H hH => hb H hH.1.le)
  have heval : (∫ H : ℝ in Ioc R T, -(A / 2) / H) = -(A / 2) * Real.log (T / R) := by
    rw [← intervalIntegral.integral_of_le hT]
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul,
      integral_inv (by rw [uIcc_of_le hT]; intro h; exact (not_le_of_gt hR) h.1)]
    rfl
  have hsplit : (∫ H : ℝ in Ioc 0 T, H ^ 2 * G H) =
      B + ∫ H : ℝ in Ioc R T, H ^ 2 * G H := by
    rw [← Ioc_union_Ioc_eq_Ioc hR.le hT]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (reduced_integrable_moment_local hi 2 R) hirt
  rw [heval] at hmono
  rw [hsplit]
  exact add_le_add_left hmono B

/-- The signed truncated second moment tends to negative infinity. There is
therefore no conditionally convergent second height moment hiding behind the
failure of absolute integrability. -/
theorem tendsto_dimensionPlaneKernel_even_second_atBot (n : ℕ) :
    Tendsto (fun T : ℝ => ∫ H : ℝ in Ioc 0 T, H ^ 2 * dimensionPlaneKernel (2 * n + 2) H)
      atTop atBot := by
  obtain ⟨C, _, hC⟩ := dimensionPlaneKernel_even_leading_remainder n
  exact reduced_truncated_second_tendsto_atBot
    (integrableOn_dimensionPlaneKernel (2 * n + 2) (by omega))
    (dimensionPlaneEvenTailCoefficient_pos n) hC

end BoundaryDraft
