import BoundaryDraft.NullTransverseMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Conditional signed null-transverse cancellation

The analytic hypothesis is a right-hand quadratic jet with little-o remainder.
It is NOT a field of any geometric admissibility structure. Applying this result
to the actual translated-overlap density requires a separate geometric proof.

Boundedness on the positive half-line suffices; compact support is not needed.
In particular measurable compactly supported weights may jump at their positive
support cutoff. No continuity or differentiability away from zero is assumed.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The full polynomial is subtracted even outside the support of the weight.
The value at zero is zero by the convention for division by zero. -/
def quadraticRemainder (B : ℝ → ℝ) (b₀ b₁ b₂ s : ℝ) : ℝ :=
  (B s - (b₀ + b₁ * s + b₂ * s ^ 2)) / s ^ 2

theorem measurable_quadraticRemainder (B : ℝ → ℝ) (b₀ b₁ b₂ : ℝ)
    (hB : Measurable B) : Measurable (quadraticRemainder B b₀ b₁ b₂) := by
  unfold quadraticRemainder
  fun_prop

/-- The little-o hypothesis means precisely that the remainder quotient vanishes
from the right; the value of the original weight at zero is immaterial. -/
theorem tendsto_quadraticRemainder (B : ℝ → ℝ) (b₀ b₁ b₂ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2)) :
    Tendsto (quadraticRemainder B b₀ b₁ b₂) (𝓝[>] 0) (𝓝 0) :=
  hjet.tendsto_div_nhds_zero

/-- Local little-o control plus a bounded weight gives a GLOBAL bound on the
quotient. Away from zero the subtracted polynomial has at most quadratic growth. -/
theorem quadraticRemainder_bounded (B : ℝ → ℝ) (b₀ b₁ b₂ C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (hjet : (fun s => B s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2)) :
    ∃ D : ℝ, ∀ s, 0 < s → ‖quadraticRemainder B b₀ b₁ b₂ s‖ ≤ D := by
  have hlim := tendsto_quadraticRemainder B b₀ b₁ b₂ hjet
  have hlocal : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖quadraticRemainder B b₀ b₁ b₂ s‖ < 1 :=
    hlim.norm.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hlocal
  change 0 < δ at hδ
  let D := (|C| + |b₀|) / δ ^ 2 + |b₁| / δ + |b₂|
  refine ⟨max 1 D, fun s hs => ?_⟩
  by_cases hsδ : s < δ
  · exact (hsmall ⟨hs, hsδ⟩).le.trans (le_max_left _ _)
  have hδs : δ ≤ s := le_of_not_gt hsδ
  have he : quadraticRemainder B b₀ b₁ b₂ s = (B s - b₀) / s ^ 2 - b₁ / s - b₂ := by
    unfold quadraticRemainder
    field_simp
    ring
  have hnum : |B s - b₀| ≤ |C| + |b₀| :=
    (abs_sub _ _).trans (add_le_add_right ((hbound s hs).trans (le_abs_self C)) _)
  have hsq : δ ^ 2 ≤ s ^ 2 := by nlinarith
  have hfar : ‖quadraticRemainder B b₀ b₁ b₂ s‖ ≤ D := by
    rw [he, Real.norm_eq_abs]
    calc
      _ ≤ |(B s - b₀) / s ^ 2| + |b₁ / s| + |b₂| :=
        (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
      _ = |B s - b₀| / s ^ 2 + |b₁| / s + |b₂| := by
        rw [abs_div, abs_div, abs_of_nonneg (sq_nonneg s), abs_of_pos hs]
      _ ≤ (|C| + |b₀|) / δ ^ 2 + |b₁| / δ + |b₂| := by
        gcongr
      _ = D := rfl
  exact hfar.trans (le_max_right _ _)

/-- Absolute integrability of a bounded measurable weight times the signed
kernel. The bound and measurability, not the totalized integral, justify it. -/
theorem integrableOn_bdgKernel_transverse_mul_bounded (B : ℝ → ℝ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) :
    IntegrableOn (fun z => B z * bdgKernel (z ^ 2)) (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn (fun z => bdgKernel (z ^ 2)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_bdgKernel_transverse_moment 0
  apply (hi.norm.const_mul C).mono'
    (hB.mul (by unfold bdgKernel bdgPolynomial; fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg _)

theorem integrableOn_bdgKernel_transverse_quadratic (b₀ b₁ b₂ : ℝ) :
    IntegrableOn (fun z : ℝ => (b₀ + b₁ * z + b₂ * z ^ 2) * bdgKernel (z ^ 2))
      (Ioi 0) := by
  have h := (((integrableOn_bdgKernel_transverse_moment 0).const_mul b₀).add
    ((integrableOn_bdgKernel_transverse_moment 1).const_mul b₁)).add
    ((integrableOn_bdgKernel_transverse_moment 2).const_mul b₂)
  apply h.congr
  exact Eventually.of_forall fun z => by dsimp; ring

/-- Polynomial subtraction uses the whole positive half-line, not just the
support of the weight. All three terms are absolutely integrable. -/
theorem integral_bdgKernel_transverse_quadratic (b₀ b₁ b₂ : ℝ) :
    (∫ z : ℝ in Ioi 0, (b₀ + b₁ * z + b₂ * z ^ 2) * bdgKernel (z ^ 2)) = 0 := by
  have he (z : ℝ) : (b₀ + b₁ * z + b₂ * z ^ 2) * bdgKernel (z ^ 2) =
      b₀ * (z ^ 0 * bdgKernel (z ^ 2)) + b₁ * (z ^ 1 * bdgKernel (z ^ 2)) +
        b₂ * (z ^ 2 * bdgKernel (z ^ 2)) := by ring
  simp_rw [he]
  have hi : IntegrableOn (fun z : ℝ => b₀ * (z ^ 0 * bdgKernel (z ^ 2)) +
      b₁ * (z ^ 1 * bdgKernel (z ^ 2))) (Ioi 0) :=
    ((integrableOn_bdgKernel_transverse_moment 0).const_mul b₀).add
      ((integrableOn_bdgKernel_transverse_moment 1).const_mul b₁)
  rw [integral_add hi ((integrableOn_bdgKernel_transverse_moment 2).const_mul b₂),
    integral_add ((integrableOn_bdgKernel_transverse_moment 0).const_mul b₀)
      ((integrableOn_bdgKernel_transverse_moment 1).const_mul b₁)]
  simp [integral_const_mul, integral_bdgKernel_transverse_zero,
    integral_bdgKernel_transverse_one, integral_bdgKernel_transverse_two]

/-- Absolute integrability of the rescaled remainder with the explicit
integrable envelope `D * |z^2 * bdgKernel (z^2)|`. -/
theorem integrableOn_bdgKernel_transverse_remainder (R : ℝ → ℝ) (hR : Measurable R)
    (D : ℝ) (hbound : ∀ s, 0 < s → ‖R s‖ ≤ D) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => (z ^ 2 * bdgKernel (z ^ 2)) * R (ε * z)) (Ioi 0) := by
  apply ((integrableOn_bdgKernel_transverse_moment 2).norm.mul_const D).mono'
    ((integrableOn_bdgKernel_transverse_moment 2).aestronglyMeasurable.mul
      (hR.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  change ‖(z ^ 2 * bdgKernel (z ^ 2)) * R (ε * z)‖ ≤ ‖z ^ 2 * bdgKernel (z ^ 2)‖ * D
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound _ (mul_pos hε hz))
    (norm_nonneg (z ^ 2 * bdgKernel (z ^ 2)))

/-- Dominated convergence is applied only AFTER the signed cancellations. -/
theorem bdgKernel_transverse_remainder_limit (R : ℝ → ℝ) (hR : Measurable R)
    (hR0 : Tendsto R (𝓝[>] 0) (𝓝 0))
    (D : ℝ) (hbound : ∀ s, 0 < s → ‖R s‖ ≤ D) :
    Tendsto (fun ε : ℝ => ∫ z : ℝ in Ioi 0,
      (z ^ 2 * bdgKernel (z ^ 2)) * R (ε * z)) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ z : ℝ in Ioi 0,
      (z ^ 2 * bdgKernel (z ^ 2)) * R (ε * z)) (𝓝[>] 0)
      (𝓝 (∫ _ : ℝ in Ioi 0, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖z ^ 2 * bdgKernel (z ^ 2)‖ * D)
    · exact Eventually.of_forall fun ε =>
        (integrableOn_bdgKernel_transverse_moment 2).aestronglyMeasurable.mul
          (hR.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _ (mul_pos hε hz)) (norm_nonneg _)
    · exact (integrableOn_bdgKernel_transverse_moment 2).norm.mul_const D
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have harg : Tendsto (fun ε : ℝ => ε * z) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.2
        refine ⟨?_, ?_⟩
        · have h : Tendsto (fun ε : ℝ => ε * z) (𝓝 0) (𝓝 (0 * z)) :=
            (continuous_id.mul continuous_const).tendsto 0
          simpa only [zero_mul] using h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact mul_pos (show 0 < ε from hε) (show 0 < z from hz)
      simpa using (hR0.comp harg).const_mul (z ^ 2 * bdgKernel (z ^ 2))
  simpa using hlim

/-- The full polynomial can be subtracted inside the signed integral. -/
theorem integral_bdgKernel_transverse_sub_quadratic (B : ℝ → ℝ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (b₀ b₁ b₂ : ℝ) :
    (∫ z : ℝ in Ioi 0, (B z - (b₀ + b₁ * z + b₂ * z ^ 2)) * bdgKernel (z ^ 2)) =
      ∫ z : ℝ in Ioi 0, B z * bdgKernel (z ^ 2) := by
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_bdgKernel_transverse_mul_bounded B hB C hbound)
    (integrableOn_bdgKernel_transverse_quadratic b₀ b₁ b₂),
    integral_bdgKernel_transverse_quadratic, sub_zero]

/-- Absolute integrability at every positive scale. -/
theorem integrableOn_bdgKernel_transverse_scaled (B : ℝ → ℝ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun s => B s * bdgKernel ((k * s) ^ 2)) (Ioi (0 : ℝ)) := by
  have hi := integrableOn_bdgKernel_transverse_mul_bounded (fun z => B (k⁻¹ * z))
    (hB.comp (measurable_const.mul measurable_id)) C
    (fun z hz => hbound _ (mul_pos (inv_pos.mpr hk) hz))
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun z => B (k⁻¹ * z) * bdgKernel (z ^ 2)) 0 hk).2 (by simpa using hi)
  simpa only [inv_mul_cancel_left₀ hk.ne'] using hs

/-- Every polynomial term is absolutely integrable at positive scale, even
though the polynomial has no compact support. -/
theorem integrableOn_bdgKernel_transverse_scaled_moment (n : ℕ) (k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => s ^ n * bdgKernel ((k * s) ^ 2)) (Ioi 0) := by
  have hi : IntegrableOn (fun z : ℝ => (k⁻¹ * z) ^ n * bdgKernel (z ^ 2)) (Ioi 0) := by
    apply ((integrableOn_bdgKernel_transverse_moment n).const_mul (k⁻¹ ^ n)).congr
    exact Eventually.of_forall fun z => by dsimp; ring
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun z : ℝ => (k⁻¹ * z) ^ n * bdgKernel (z ^ 2)) 0 hk).2 (by simpa using hi)
  simpa only [inv_mul_cancel_left₀ hk.ne'] using hs

/-- The original finite-density integrand is absolutely integrable. -/
theorem integrableOn_bdgKernel_density_mul_bounded (B : ℝ → ℝ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => B s * bdgKernel (c * ρ * s ^ 2)) (Ioi 0) := by
  have h := integrableOn_bdgKernel_transverse_scaled B hB C hbound
    (Real.sqrt (c * ρ)) (Real.sqrt_pos.mpr (mul_pos hc hρ))
  simpa only [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le] using h

/-- Exact substitution and polynomial subtraction on the entire half-line.
No assumption about a remainder estimate is used for this identity. -/
theorem integral_bdgKernel_transverse_eq_remainder (B : ℝ → ℝ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (b₀ b₁ b₂ k : ℝ) (hk : 0 < k) :
    (∫ s : ℝ in Ioi 0, B s * bdgKernel ((k * s) ^ 2)) =
      k⁻¹ ^ 3 * ∫ z : ℝ in Ioi 0,
        (z ^ 2 * bdgKernel (z ^ 2)) * quadraticRemainder B b₀ b₁ b₂ (k⁻¹ * z) := by
  have hs := integral_comp_mul_left_Ioi (fun z => B (k⁻¹ * z) * bdgKernel (z ^ 2)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  rw [hs, ← integral_bdgKernel_transverse_sub_quadratic (fun z => B (k⁻¹ * z))
    (hB.comp (measurable_const.mul measurable_id)) C
    (fun z hz => hbound _ (mul_pos (inv_pos.mpr hk) hz)) b₀ (b₁ * k⁻¹) (b₂ * k⁻¹ ^ 2)]
  have he : (∫ z : ℝ in Ioi 0,
      (B (k⁻¹ * z) - (b₀ + b₁ * k⁻¹ * z + b₂ * k⁻¹ ^ 2 * z ^ 2)) * bdgKernel (z ^ 2)) =
      k⁻¹ ^ 2 * ∫ z : ℝ in Ioi 0,
        (z ^ 2 * bdgKernel (z ^ 2)) * quadraticRemainder B b₀ b₁ b₂ (k⁻¹ * z) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    dsimp [quadraticRemainder]
    field_simp [hk.ne', ne_of_gt (show 0 < z from hz)]
    ring
  rw [he]
  ring

/-- The physical normalization cancels all density-dependent scale factors.
The remaining constant depends only on the fixed positive interval coefficient. -/
theorem bdgKernel_transverse_normalized_rescaling (B : ℝ → ℝ)
    (hB : Measurable B) (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C)
    (b₀ b₁ b₂ c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (3 / 2 : ℝ) * (∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)) =
      (Real.sqrt c)⁻¹ ^ 3 * ∫ z : ℝ in Ioi 0, (z ^ 2 * bdgKernel (z ^ 2)) *
        quadraticRemainder B b₀ b₁ b₂ ((Real.sqrt (c * ρ))⁻¹ * z) := by
  have hk : 0 < Real.sqrt (c * ρ) := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have hp : ρ ^ (3 / 2 : ℝ) = Real.sqrt ρ ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have he (s : ℝ) : c * ρ * s ^ 2 = (Real.sqrt (c * ρ) * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he]
  rw [integral_bdgKernel_transverse_eq_remainder B hB C hbound b₀ b₁ b₂ _ hk, hp]
  rw [Real.sqrt_mul hc.le]
  field_simp
  ring

/-- The null-transverse width approaches zero through positive values. -/
theorem tendsto_bdgKernel_transverse_width (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => (Real.sqrt (c * ρ))⁻¹) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun ρ : ℝ => (c * ρ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop hc)
    simpa only [Real.sqrt_inv, Real.sqrt_zero] using h.sqrt
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hc hρ))

/-- Conditional cancellation for any bounded measurable weight with a right
quadratic jet. In particular this covers compactly supported weights with a
jump at a positive cutoff. It is not a theorem about a geometric overlap density,
a localization theorem, or a sample-wise convergence result. -/
theorem bdgKernel_transverse_cancellation (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b₀ b₁ b₂ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2)) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := quadraticRemainder_bounded B b₀ b₁ b₂ C hbound hjet
  have h := ((bdgKernel_transverse_remainder_limit (quadraticRemainder B b₀ b₁ b₂)
    (measurable_quadraticRemainder B b₀ b₁ b₂ hB)
    (tendsto_quadraticRemainder B b₀ b₁ b₂ hjet) D hD).comp
    (tendsto_bdgKernel_transverse_width c hc)).const_mul ((Real.sqrt c)⁻¹ ^ 3)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (bdgKernel_transverse_normalized_rescaling B hB C hbound b₀ b₁ b₂ c ρ hc hρ).symm

end BoundaryDraft
