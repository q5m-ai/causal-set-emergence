import BoundaryDraft.ShortRadialQuadraticLimit

/-!
# Fixed-cutoff polynomial cancellation

The actual truncated polynomial is compared with its uncut quadratic part.
The global cubic error bound includes the entire omitted tail. This lemma
supports absolute-overlap basis responses; it does not assume or produce a
geometric overlap expansion.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ShortCutoffPolynomial

/-- A polynomial with the same sharp proper-time cutoff as the short density. -/
def density (δ a b d e f σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then a + b * σ + d * σ ^ 2 + e * σ ^ 3 + f * σ ^ 4 else 0

theorem measurable_density (δ a b d e f : ℝ) : Measurable (density δ a b d e f) := by
  unfold density
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

theorem quadratic_bound {q s : ℝ} (hq : 0 < q) (hs : q ≤ s) (a b d : ℝ) :
    |a + b * s + d * s ^ 2| ≤ (|a| / q ^ 3 + |b| / q ^ 2 + |d| / q) * s ^ 3 := by
  have hs0 := hq.trans_le hs
  apply (div_le_iff₀ (pow_pos hs0 3)).mp
  have he : (a + b * s + d * s ^ 2) / s ^ 3 = a / s ^ 3 + b / s ^ 2 + d / s := by
    field_simp
    ring
  rw [← abs_of_pos (pow_pos hs0 3), ← abs_div, he]
  calc
    _ ≤ |a / s ^ 3| + |b / s ^ 2| + |d / s| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ = |a| / s ^ 3 + |b| / s ^ 2 + |d| / s := by
      rw [abs_div, abs_div, abs_div, abs_of_pos (pow_pos hs0 3),
        abs_of_nonneg (sq_nonneg s), abs_of_pos hs0]
    _ ≤ _ := by gcongr

/-- A global, rather than only near-origin, bound before taking absolute values
of the signed kernel. All constants depend on the fixed positive cutoff. -/
theorem cubic_bound {δ : ℝ} (hδ : 0 < δ) (a b d e f : ℝ) :
    ∃ C : ℝ, ∀ σ, 0 < σ →
      ‖density δ a b d e f σ - (a + b * σ + d * σ ^ 2)‖ ≤ C * σ ^ 3 := by
  let Cnear := |e| + |f| * δ ^ 2
  let Cfar := |a| / (δ ^ 2) ^ 3 + |b| / (δ ^ 2) ^ 2 + |d| / (δ ^ 2)
  refine ⟨max Cnear Cfar, fun σ hσ => ?_⟩
  by_cases hs : σ ≤ δ ^ 2
  · have he : density δ a b d e f σ - (a + b * σ + d * σ ^ 2) = e * σ ^ 3 + f * σ ^ 4 := by
      rw [density, if_pos ⟨hσ.le, hs⟩]
      ring
    rw [he, Real.norm_eq_abs]
    calc
      _ ≤ |e * σ ^ 3| + |f * σ ^ 4| := abs_add _ _
      _ = (|e| + |f| * σ) * σ ^ 3 := by
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos hσ 3), abs_of_pos (pow_pos hσ 4)]
        ring
      _ ≤ Cnear * σ ^ 3 := by dsimp [Cnear]; gcongr
      _ ≤ max Cnear Cfar * σ ^ 3 := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ.le _)
  · rw [density, if_neg (by simp [hs]), zero_sub, norm_neg, Real.norm_eq_abs]
    exact (quadratic_bound (sq_pos_of_pos hδ) (le_of_not_ge hs) a b d).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cnear Cfar) (pow_nonneg hσ.le _))

theorem integrable_density {δ c ρ : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ)
    (a b d e f : ℝ) :
    IntegrableOn (fun σ => density δ a b d e f σ * bdgKernel (c * ρ * σ ^ 2)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := cubic_bound hδ a b d e f
  have hm : Measurable (fun σ => density δ a b d e f σ - (a + b * σ + d * σ ^ 2)) :=
    (measurable_density δ a b d e f).sub (by fun_prop)
  have hiD := integrableOn_bdgKernel_mul_cubic_bound _ hm C hC hc hρ
  have hiP := integrableOn_bdgKernel_transverse_scaled_quadratic a b d
    (Real.sqrt (c * ρ)) (Real.sqrt_pos.mpr (mul_pos hc hρ))
  have he (σ : ℝ) : (Real.sqrt (c * ρ) * σ) ^ 2 = c * ρ * σ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he] at hiP
  apply (hiD.add hiP).congr
  exact Eventually.of_forall fun σ => by dsimp; ring

/-- The fully normalized truncated polynomial response vanishes. No uniformity
as the cutoff shrinks is asserted. -/
theorem normalized_limit {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (a b d e f : ℝ) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
      density δ a b d e f σ * bdgKernel (c * ρ * σ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := cubic_bound hδ a b d e f
  have hm : Measurable (fun σ => density δ a b d e f σ - (a + b * σ + d * σ ^ 2)) :=
    (measurable_density δ a b d e f).sub (by fun_prop)
  apply (bdgKernel_cubic_cancellation _ hm C hC c hc).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hiA := integrable_density hδ hc hρ a b d e f
  have hiP := integrableOn_bdgKernel_transverse_scaled_quadratic a b d
    (Real.sqrt (c * ρ)) (Real.sqrt_pos.mpr (mul_pos hc hρ))
  have hP := integral_bdgKernel_transverse_scaled_quadratic a b d
    (Real.sqrt (c * ρ)) (Real.sqrt_pos.mpr (mul_pos hc hρ))
  have he (σ : ℝ) : (Real.sqrt (c * ρ) * σ) ^ 2 = c * ρ * σ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he] at hiP hP
  simp_rw [sub_mul]
  rw [integral_sub hiA hiP, hP, sub_zero]

end ShortCutoffPolynomial
end BoundaryDraft
