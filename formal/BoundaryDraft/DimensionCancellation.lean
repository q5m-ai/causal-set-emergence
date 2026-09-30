import BoundaryDraft.DimensionMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Conditional dimension-dependent signed cancellation

This proves analytic contract K in `notes/dimension-kernels.md` for the actual
`dimensionKernel`. The polynomial has degree at most `d / 2` (natural division),
but the little-o remainder has the REAL order `(d : ℝ) / 2`. In odd dimensions
this is a genuinely stronger, fractional-order hypothesis.

Boundedness on the positive half-line suffices; compact support is not needed.
The global remainder bound is derived, not assumed by the cancellation theorem.
No geometric admissibility, overlap regularity, or sample-wise limit is asserted.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The full jet, including the last vanishing natural moment. -/
def dimensionJet (d : ℕ) (b : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (dimensionFactorCount d), b j * s ^ j

/-- Normalize by the real half-dimension, not its integer part. -/
def dimensionRemainder (d : ℕ) (B : ℝ → ℝ) (b : ℕ → ℝ) (s : ℝ) : ℝ :=
  (B s - dimensionJet d b s) / s ^ ((d : ℝ) / 2)

theorem measurable_dimensionJet (d : ℕ) (b : ℕ → ℝ) :
    Measurable (dimensionJet d b) := by
  unfold dimensionJet
  fun_prop

theorem measurable_dimensionRemainder (d : ℕ) (B : ℝ → ℝ) (b : ℕ → ℝ)
    (hB : Measurable B) : Measurable (dimensionRemainder d B b) := by
  unfold dimensionRemainder
  exact (hB.sub (measurable_dimensionJet d b)).div (measurable_id.pow_const _)

theorem tendsto_dimensionRemainder (d : ℕ) (B : ℝ → ℝ) (b : ℕ → ℝ)
    (hjet : (fun s => B s - dimensionJet d b s) =o[𝓝[>] 0]
      (fun s => s ^ ((d : ℝ) / 2))) :
    Tendsto (dimensionRemainder d B b) (𝓝[>] 0) (𝓝 0) :=
  hjet.tendsto_div_nhds_zero

private theorem dimensionJet_order_le (d j : ℕ) (hj : j < dimensionFactorCount d) :
    (j : ℝ) ≤ (d : ℝ) / 2 := by
  have hn : 2 * j ≤ d := by
    unfold dimensionFactorCount at hj
    omega
  have hr : (2 : ℝ) * j ≤ d := by exact_mod_cast hn
  linarith

/-- Little-o controls the quotient near zero. Away from zero each jet exponent
is at most the real half-dimension, so boundedness of the weight suffices. -/
theorem dimensionRemainder_bounded (d : ℕ) (B : ℝ → ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (hjet : (fun s => B s - dimensionJet d b s) =o[𝓝[>] 0]
      (fun s => s ^ ((d : ℝ) / 2))) :
    ∃ D : ℝ, ∀ s, 0 < s → ‖dimensionRemainder d B b s‖ ≤ D := by
  have hlocal : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖dimensionRemainder d B b s‖ < 1 :=
    (tendsto_dimensionRemainder d B b hjet).norm.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hlocal
  change 0 < δ at hδ
  let q : ℝ := (d : ℝ) / 2
  let D := |C| / δ ^ q +
    ∑ j ∈ Finset.range (dimensionFactorCount d), |b j| * δ ^ ((j : ℝ) - q)
  refine ⟨max 1 D, fun s hs => ?_⟩
  by_cases hsδ : s < δ
  · exact (hsmall ⟨hs, hsδ⟩).le.trans (le_max_left _ _)
  have hδs : δ ≤ s := le_of_not_gt hsδ
  have hq : 0 ≤ q := div_nonneg (Nat.cast_nonneg d) (by norm_num)
  have hsq : 0 < s ^ q := Real.rpow_pos_of_pos hs _
  have hδq : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
  have he : dimensionRemainder d B b s = B s / s ^ q -
      ∑ j ∈ Finset.range (dimensionFactorCount d), b j * s ^ ((j : ℝ) - q) := by
    unfold dimensionRemainder dimensionJet
    rw [sub_div, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.rpow_sub hs, Real.rpow_natCast]
    ring
  have hB : |B s / s ^ q| ≤ |C| / δ ^ q := by
    rw [abs_div, abs_of_pos hsq]
    exact div_le_div₀ (abs_nonneg C) ((hbound s hs).trans (le_abs_self C)) hδq
      (Real.rpow_le_rpow hδ.le hδs hq)
  have hpoly : |∑ j ∈ Finset.range (dimensionFactorCount d),
      b j * s ^ ((j : ℝ) - q)| ≤
      ∑ j ∈ Finset.range (dimensionFactorCount d), |b j| * δ ^ ((j : ℝ) - q) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hδ hδs
        (sub_nonpos.mpr (dimensionJet_order_le d j (Finset.mem_range.mp hj))))
      (abs_nonneg _)
  rw [he, Real.norm_eq_abs]
  exact ((abs_sub _ _).trans (add_le_add hB hpoly)).trans (le_max_right _ _)

/-- Every natural-order moment is absolutely convergent, not merely totalized. -/
theorem integrableOn_dimensionKernel_transverse_moment (d j : ℕ) (hd : 0 < d) :
    IntegrableOn (fun s : ℝ => s ^ j * dimensionKernel d (s ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
  simpa only [Real.rpow_natCast] using integrableOn_dimensionKernel_rpow d
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg j))

/-- Absolute integrability for a bounded measurable weight and the signed kernel. -/
theorem integrableOn_dimensionKernel_transverse_mul_bounded (d : ℕ) (hd : 0 < d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) :
    IntegrableOn (fun s : ℝ => B s * dimensionKernel d (s ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
  have hi : IntegrableOn (fun s : ℝ => dimensionKernel d (s ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
    simpa using integrableOn_dimensionKernel_transverse_moment d 0 hd
  apply (hi.norm.const_mul C).mono'
    (hB.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound s hs) (norm_nonneg _)

theorem integrableOn_dimensionKernel_transverse_jet (d : ℕ) (hd : 0 < d)
    (b : ℕ → ℝ) :
    IntegrableOn (fun s : ℝ => dimensionJet d b s *
      dimensionKernel d (s ^ ((d : ℝ) / 2))) (Ioi 0) := by
  simp only [dimensionJet, Finset.sum_mul, mul_assoc]
  exact integrable_finset_sum _ fun j _ =>
    (integrableOn_dimensionKernel_transverse_moment d j hd).const_mul (b j)

/-- Exact cancellation of the whole polynomial on the whole positive half-line. -/
theorem integral_dimensionKernel_transverse_jet (d : ℕ) (hd : 0 < d) (b : ℕ → ℝ) :
    (∫ s : ℝ in Ioi 0, dimensionJet d b s *
      dimensionKernel d (s ^ ((d : ℝ) / 2))) = 0 := by
  simp only [dimensionJet, Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum _ (fun j _ =>
    (integrableOn_dimensionKernel_transverse_moment d j hd).const_mul (b j))]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul, integral_dimensionKernel_transverse_zero d j hd
    (Finset.mem_range.mp hj), mul_zero]

/-- Signed subtraction is justified by absolute integrability of both terms. -/
theorem integral_dimensionKernel_transverse_sub_jet (d : ℕ) (hd : 0 < d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b : ℕ → ℝ) :
    (∫ s : ℝ in Ioi 0, (B s - dimensionJet d b s) *
      dimensionKernel d (s ^ ((d : ℝ) / 2))) =
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel d (s ^ ((d : ℝ) / 2)) := by
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_dimensionKernel_transverse_mul_bounded d hd B hB C hbound)
    (integrableOn_dimensionKernel_transverse_jet d hd b),
    integral_dimensionKernel_transverse_jet d hd b, sub_zero]

/-- The original density-weighted integrand is absolutely integrable at every
positive density, without a jet or a compact-support assumption. -/
theorem integrableOn_dimensionKernel_density_mul_bounded (d : ℕ) (hd : 0 < d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => B s * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
  have hi : IntegrableOn (fun s : ℝ => dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
    simpa using integrableOn_dimensionKernel_density_rpow d
      (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
      (by norm_num : (-1 : ℝ) < 0) (mul_pos hc hρ)
  apply (hi.norm.const_mul C).mono'
    (hB.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound s hs) (norm_nonneg _)

theorem integrableOn_dimensionKernel_density_moment (d j : ℕ) (hd : 0 < d)
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => s ^ j * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
  simpa only [Real.rpow_natCast] using integrableOn_dimensionKernel_density_rpow d
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg j)) (mul_pos hc hρ)

theorem integral_dimensionKernel_density_moment_zero (d j : ℕ) (hd : 0 < d)
    (hj : j < dimensionFactorCount d) (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ s : ℝ in Ioi 0, s ^ j * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2))) = 0 := by
  simp_rw [← Real.rpow_natCast]
  rw [integral_dimensionKernel_density_rpow d
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg j)) (mul_pos hc hρ)]
  have he : ((j : ℝ) + 1) / ((d : ℝ) / 2) = 2 * (j + 1) / d := by ring
  rw [he, dimensionMellinFactor_root d _ j hd hj, mul_zero, mul_zero]

theorem integrableOn_dimensionKernel_density_jet (d : ℕ) (hd : 0 < d)
    (b : ℕ → ℝ) (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => dimensionJet d b s *
      dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2))) (Ioi 0) := by
  simp only [dimensionJet, Finset.sum_mul, mul_assoc]
  simp only [← mul_assoc c ρ]
  exact integrable_finset_sum _ fun j _ =>
    (integrableOn_dimensionKernel_density_moment d j hd c ρ hc hρ).const_mul (b j)

theorem integral_dimensionKernel_density_jet (d : ℕ) (hd : 0 < d)
    (b : ℕ → ℝ) (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ s : ℝ in Ioi 0, dimensionJet d b s *
      dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2))) = 0 := by
  simp only [dimensionJet, Finset.sum_mul, mul_assoc]
  simp only [← mul_assoc c ρ]
  rw [integral_finset_sum _ (fun j _ =>
    (integrableOn_dimensionKernel_density_moment d j hd c ρ hc hρ).const_mul (b j))]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul, integral_dimensionKernel_density_moment_zero d j hd
    (Finset.mem_range.mp hj) c ρ hc hρ, mul_zero]

/-- Exact polynomial subtraction at finite positive density. No little-o
estimate is used for this identity and no support is discarded. -/
theorem integral_dimensionKernel_density_sub_jet (d : ℕ) (hd : 0 < d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b : ℕ → ℝ)
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ s : ℝ in Ioi 0, (B s - dimensionJet d b s) *
      dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2))) =
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2)) := by
  simp_rw [sub_mul]
  rw [integral_sub
    (integrableOn_dimensionKernel_density_mul_bounded d hd B hB C hbound c ρ hc hρ)
    (integrableOn_dimensionKernel_density_jet d hd b c ρ hc hρ),
    integral_dimensionKernel_density_jet d hd b c ρ hc hρ, sub_zero]

/-- The fractional critical moment supplies the absolute dominator in odd as
well as even dimensions. -/
theorem integrableOn_dimensionKernel_transverse_remainder (d : ℕ) (hd : 0 < d)
    (R : ℝ → ℝ) (hR : Measurable R) (D : ℝ)
    (hbound : ∀ s, 0 < s → ‖R s‖ ≤ D) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => (z ^ ((d : ℝ) / 2) *
      dimensionKernel d (z ^ ((d : ℝ) / 2))) * R (ε * z)) (Ioi 0) := by
  have hq : 0 < (d : ℝ) / 2 := div_pos (Nat.cast_pos.mpr hd) (by norm_num)
  have hi := integrableOn_dimensionKernel_rpow d hq (by linarith : -1 < (d : ℝ) / 2)
  apply (hi.norm.mul_const D).mono'
    (hi.aestronglyMeasurable.mul
      (hR.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound _ (mul_pos hε hz)) (norm_nonneg _)

/-- Dominated convergence is used after the signed polynomial cancellation. -/
theorem dimensionKernel_transverse_remainder_limit (d : ℕ) (hd : 0 < d)
    (R : ℝ → ℝ) (hR : Measurable R) (hR0 : Tendsto R (𝓝[>] 0) (𝓝 0))
    (D : ℝ) (hbound : ∀ s, 0 < s → ‖R s‖ ≤ D) :
    Tendsto (fun ε : ℝ => ∫ z : ℝ in Ioi 0,
      (z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2))) * R (ε * z))
      (𝓝[>] 0) (𝓝 0) := by
  have hq : 0 < (d : ℝ) / 2 := div_pos (Nat.cast_pos.mpr hd) (by norm_num)
  have hi := integrableOn_dimensionKernel_rpow d hq (by linarith : -1 < (d : ℝ) / 2)
  have hlim : Tendsto (fun ε : ℝ => ∫ z : ℝ in Ioi 0,
      (z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2))) * R (ε * z))
      (𝓝[>] 0) (𝓝 (∫ _ : ℝ in Ioi 0, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2))‖ * D)
    · exact Eventually.of_forall fun ε => hi.aestronglyMeasurable.mul
        (hR.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _ (mul_pos hε hz)) (norm_nonneg _)
    · exact hi.norm.mul_const D
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have harg : Tendsto (fun ε : ℝ => ε * z) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.2
        refine ⟨?_, ?_⟩
        · have h : Tendsto (fun ε : ℝ => ε * z) (𝓝 0) (𝓝 (0 * z)) :=
            (continuous_id.mul continuous_const).tendsto 0
          simpa only [zero_mul] using h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact mul_pos (show 0 < ε from hε) hz
      simpa using (hR0.comp harg).const_mul
        (z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2)))
  simpa using hlim

theorem dimensionJet_mul (d : ℕ) (b : ℕ → ℝ) (ε s : ℝ) :
    dimensionJet d b (ε * s) = dimensionJet d (fun j => b j * ε ^ j) s := by
  simp only [dimensionJet, mul_pow, mul_assoc]

/-- Positive rescaling and full polynomial subtraction give this exact identity;
no remainder estimate or hidden integrability premise is required. -/
theorem integral_dimensionKernel_transverse_eq_remainder (d : ℕ) (hd : 0 < d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b : ℕ → ℝ) (k : ℝ) (hk : 0 < k) :
    (∫ s : ℝ in Ioi 0, B s * dimensionKernel d ((k * s) ^ ((d : ℝ) / 2))) =
      (k⁻¹ * (k⁻¹) ^ ((d : ℝ) / 2)) * ∫ z : ℝ in Ioi 0,
        (z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2))) *
          dimensionRemainder d B b (k⁻¹ * z) := by
  have hs := integral_comp_mul_left_Ioi
    (fun z => B (k⁻¹ * z) * dimensionKernel d (z ^ ((d : ℝ) / 2))) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  rw [hs, ← integral_dimensionKernel_transverse_sub_jet d hd (fun z => B (k⁻¹ * z))
    (hB.comp (measurable_const.mul measurable_id)) C
    (fun z hz => hbound _ (mul_pos (inv_pos.mpr hk) hz)) (fun j => b j * k⁻¹ ^ j)]
  have he : (∫ z : ℝ in Ioi 0,
      (B (k⁻¹ * z) - dimensionJet d (fun j => b j * k⁻¹ ^ j) z) *
        dimensionKernel d (z ^ ((d : ℝ) / 2))) =
      (k⁻¹) ^ ((d : ℝ) / 2) * ∫ z : ℝ in Ioi 0,
        (z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2))) *
          dimensionRemainder d B b (k⁻¹ * z) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    dsimp only
    rw [← dimensionJet_mul, dimensionRemainder, Real.mul_rpow (inv_pos.mpr hk).le hz.le]
    field_simp [(Real.rpow_pos_of_pos (inv_pos.mpr hk) ((d : ℝ) / 2)).ne',
      (Real.rpow_pos_of_pos hz ((d : ℝ) / 2)).ne']
    ring
  rw [he, mul_assoc]

private theorem dimensionKernel_density_prefactor (d : ℕ) (hd : 0 < d)
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (1 + 2 / (d : ℝ)) *
      (((c * ρ) ^ (2 / (d : ℝ)))⁻¹ *
        (((c * ρ) ^ (2 / (d : ℝ)))⁻¹) ^ ((d : ℝ) / 2)) =
      c ^ (-(1 + 2 / (d : ℝ))) := by
  have hbase : 0 < c * ρ := mul_pos hc hρ
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hpow : ((((c * ρ) ^ (2 / (d : ℝ)))⁻¹) ^ ((d : ℝ) / 2)) =
      (c * ρ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_neg hbase.le, ← Real.rpow_mul hbase.le]
    congr 1
    field_simp
    ring
  rw [hpow, ← Real.rpow_neg hbase.le, ← Real.rpow_add hbase]
  have hexp : -(2 / (d : ℝ)) + (-1) = -(1 + 2 / (d : ℝ)) := by ring
  rw [hexp, Real.mul_rpow hc.le hρ.le]
  calc
    _ = c ^ (-(1 + 2 / (d : ℝ))) *
        (ρ ^ (1 + 2 / (d : ℝ)) * ρ ^ (-(1 + 2 / (d : ℝ)))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hρ, add_neg_cancel, Real.rpow_zero, mul_one]

/-- The physical density normalization leaves exactly the constant
`c ^ (-(1 + 2 / d))`; all exponents, including odd half-dimensions, are real. -/
theorem dimensionKernel_transverse_normalized_rescaling (d : ℕ) (hd : 0 < d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b : ℕ → ℝ)
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (1 + 2 / (d : ℝ)) *
      (∫ s : ℝ in Ioi 0, B s * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2))) =
      c ^ (-(1 + 2 / (d : ℝ))) * ∫ z : ℝ in Ioi 0,
        (z ^ ((d : ℝ) / 2) * dimensionKernel d (z ^ ((d : ℝ) / 2))) *
          dimensionRemainder d B b ((c * ρ) ^ (-(2 / (d : ℝ))) * z) := by
  have hbase : 0 < c * ρ := mul_pos hc hρ
  have hk : 0 < (c * ρ) ^ (2 / (d : ℝ)) := Real.rpow_pos_of_pos hbase _
  have he : (∫ s : ℝ in Ioi 0, B s *
      dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2))) =
      ∫ s : ℝ in Ioi 0, B s *
        dimensionKernel d (((c * ρ) ^ (2 / (d : ℝ)) * s) ^ ((d : ℝ) / 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [dimensionKernel_density_scaling d hd c ρ s hc hρ hs.le]
  rw [he, integral_dimensionKernel_transverse_eq_remainder d hd B hB C hbound b _ hk,
    ← mul_assoc, dimensionKernel_density_prefactor d hd c ρ hc hρ,
    Real.rpow_neg hbase.le]

/-- The transverse width goes to zero through strictly positive values. -/
theorem tendsto_dimensionKernel_transverse_width (d : ℕ) (hd : 0 < d)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => (c * ρ) ^ (-(2 / (d : ℝ)))) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, ?_⟩
  · exact (tendsto_rpow_neg_atTop
      (div_pos (by norm_num) (Nat.cast_pos.mpr hd))).comp (tendsto_id.const_mul_atTop hc)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact Real.rpow_pos_of_pos (mul_pos hc hρ) _

/-- Analytic contract K for every integer dimension at least two. The only
analytic premises on the weight are measurability, boundedness on the positive
half-line, and a degree-`floor(d/2)` jet with little-o remainder of REAL order
`d/2`. In particular the odd-dimensional premise is not weakened to the integer
jet order. Compact support, global remainder bounds, and geometric conclusions
are not premises. -/
theorem dimensionKernel_transverse_cancellation (d : ℕ) (hd : 2 ≤ d)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b : ℕ → ℝ)
    (hjet : (fun s => B s - dimensionJet d b s) =o[𝓝[>] 0]
      (fun s => s ^ ((d : ℝ) / 2))) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / (d : ℝ)) *
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2)))
      atTop (𝓝 0) := by
  have hd0 : 0 < d := by omega
  obtain ⟨D, hD⟩ := dimensionRemainder_bounded d B b C hbound hjet
  have h := ((dimensionKernel_transverse_remainder_limit d hd0 (dimensionRemainder d B b)
    (measurable_dimensionRemainder d B b hB) (tendsto_dimensionRemainder d B b hjet)
    D hD).comp (tendsto_dimensionKernel_transverse_width d hd0 c hc)).const_mul
      (c ^ (-(1 + 2 / (d : ℝ))))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (dimensionKernel_transverse_normalized_rescaling d hd0 B hB C hbound b c ρ hc hρ).symm

end BoundaryDraft
