import BoundaryDraft.DimensionKernel

/-!
# Mellin integrals of the dimension-dependent BDG kernels

The integral is defined independently of the algebraic product in
`DimensionKernel`. Absolute integrability and the Gamma recurrence identify
that product with the actual signed integral, for every positive real Mellin
parameter. No continuation across divergent moments is used.
-/

open MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Actual polynomial-exponential Mellin integral. -/
def polynomialMellin (p : Polynomial ℝ) (a : ℝ) : ℝ :=
  ∫ z : ℝ in Ioi 0, (Real.exp (-z) * z ^ (a - 1)) * p.eval z

private theorem mellin_monomial_integrand (n : ℕ) (c a z : ℝ) (hz : 0 < z) :
    (Real.exp (-z) * z ^ (a - 1)) * (monomial n c).eval z =
      c * (Real.exp (-z) * z ^ (a + n - 1)) := by
  rw [eval_monomial, ← Real.rpow_natCast]
  calc
    _ = c * (Real.exp (-z) * (z ^ (a - 1) * z ^ (n : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hz, show a - 1 + (n : ℝ) = a + n - 1 by ring]

/-- Absolute integrability, before any signed polynomial cancellation. -/
theorem integrableOn_polynomialMellin (p : Polynomial ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun z : ℝ => (Real.exp (-z) * z ^ (a - 1)) * p.eval z) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, mul_add] using hp.add hq
  | monomial n c =>
    have hn : 0 < a + n := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)
    apply ((Real.GammaIntegral_convergent hn).const_mul c).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (mellin_monomial_integrand n c a z hz).symm

theorem polynomialMellin_monomial (n : ℕ) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    polynomialMellin (monomial n c) a = c * Real.Gamma (a + n) := by
  unfold polynomialMellin
  have hn : 0 < a + n := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)
  rw [Real.Gamma_eq_integral hn, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun z hz => mellin_monomial_integrand n c a z hz)

theorem polynomialMellin_add (p q : Polynomial ℝ) {a : ℝ} (ha : 0 < a) :
    polynomialMellin (p + q) a = polynomialMellin p a + polynomialMellin q a := by
  simp only [polynomialMellin, eval_add, mul_add]
  exact integral_add (integrableOn_polynomialMellin p ha)
    (integrableOn_polynomialMellin q ha)

theorem polynomialMellin_sub (p q : Polynomial ℝ) {a : ℝ} (ha : 0 < a) :
    polynomialMellin (p - q) a = polynomialMellin p a - polynomialMellin q a := by
  simp only [polynomialMellin, eval_sub, mul_sub]
  exact integral_sub (integrableOn_polynomialMellin p ha)
    (integrableOn_polynomialMellin q ha)

theorem polynomialMellin_C_mul (c : ℝ) (p : Polynomial ℝ) (a : ℝ) :
    polynomialMellin (C c * p) a = c * polynomialMellin p a := by
  simp only [polynomialMellin, eval_mul, eval_C]
  simp_rw [mul_left_comm (Real.exp _ * _), integral_const_mul]

/-- Euler integration by parts proved on monomials and extended by linearity.
All integrals here are absolutely convergent; no boundary term is postulated. -/
theorem polynomialMellin_euler (p : Polynomial ℝ) {a : ℝ} (ha : 0 < a) :
    polynomialMellin (X * (derivative p - p)) a = -a * polynomialMellin p a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have he : X * (derivative (p + q) - (p + q)) =
        X * (derivative p - p) + X * (derivative q - q) := by
      rw [derivative_add]
      ring
    rw [he, polynomialMellin_add _ _ ha, polynomialMellin_add _ _ ha, hp, hq]
    ring
  | monomial n c =>
    rw [mul_sub, polynomialMellin_sub _ _ ha, X_mul_monomial,
      polynomialMellin_monomial _ _ ha]
    have he : X * derivative (monomial n c) = monomial n (c * n) := by
      cases n with
      | zero => simp
      | succ n => simp [derivative_monomial_succ, X_mul_monomial]
    rw [he, polynomialMellin_monomial _ _ ha, polynomialMellin_monomial _ _ ha]
    have hn : a + (↑(n + 1) : ℝ) = (a + n) + 1 := by push_cast; ring
    rw [hn, Real.Gamma_add_one (ne_of_gt
      (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)))]
    ring

/-- The independently defined recurrence has the claimed integrated multiplier. -/
theorem polynomialMellin_dimensionPolynomialStage (d m : ℕ) {a : ℝ} (ha : 0 < a) :
    polynomialMellin (dimensionPolynomialStage d m) a =
      Real.Gamma a * dimensionMellinFactor d m a := by
  induction m with
  | zero =>
    simpa [dimensionPolynomialStage, dimensionMellinFactor] using
      polynomialMellin_monomial 0 1 ha
  | succ m ih =>
    simp only [dimensionPolynomialStage]
    rw [polynomialMellin_add _ _ ha, mul_assoc, polynomialMellin_C_mul,
      polynomialMellin_euler _ ha, ih]
    simp only [dimensionMellinFactor, Finset.prod_range_succ, Nat.cast_add,
      Nat.cast_one]
    ring

/-- Absolute convergence for every dimension and positive Mellin parameter. -/
theorem integrableOn_dimensionKernel_mellin (d : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun z : ℝ => z ^ (a - 1) * dimensionKernel d z) (Ioi 0) := by
  simpa only [dimensionKernel, mul_left_comm, mul_assoc, mul_comm] using
    integrableOn_polynomialMellin (dimensionPolynomial d) ha

/-- General-dimensional Mellin identity for the actual signed kernel. -/
theorem integral_dimensionKernel_mellin (d : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ z : ℝ in Ioi 0, z ^ (a - 1) * dimensionKernel d z) =
      Real.Gamma a * dimensionMellinFactor d (dimensionFactorCount d) a := by
  convert polynomialMellin_dimensionPolynomialStage d (dimensionFactorCount d) ha using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z _
  simp only [dimensionKernel, dimensionPolynomial]
  ring

private theorem mellin_rpow_weight {q : ℝ} (hq : 0 < q) (j z : ℝ) (hz : 0 < z) :
    z ^ (q - 1) * (z ^ q) ^ ((j + 1) / q - 1) = z ^ j := by
  rw [← Real.rpow_mul hz.le, ← Real.rpow_add hz]
  congr 1
  field_simp

/-- A genuine positive power substitution preserves absolute convergence. -/
theorem integrableOn_dimensionKernel_rpow (d : ℕ) {q j : ℝ}
    (hq : 0 < q) (hj : -1 < j) :
    IntegrableOn (fun u : ℝ => u ^ j * dimensionKernel d (u ^ q)) (Ioi 0) := by
  have ha : 0 < (j + 1) / q := div_pos (by linarith) hq
  have hi := (integrableOn_Ioi_comp_rpow_iff'
    (fun z : ℝ => z ^ ((j + 1) / q - 1) * dimensionKernel d z) hq.ne').mpr
      (integrableOn_dimensionKernel_mellin d ha)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [smul_eq_mul, ← mul_assoc, mellin_rpow_weight hq j z hz]

/-- Integrated power substitution, not an algebraic definition of a moment. -/
theorem integral_dimensionKernel_rpow (d : ℕ) {q j : ℝ}
    (hq : 0 < q) (hj : -1 < j) :
    (∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (u ^ q)) =
      (1 / q) * Real.Gamma ((j + 1) / q) *
        dimensionMellinFactor d (dimensionFactorCount d) ((j + 1) / q) := by
  have ha : 0 < (j + 1) / q := div_pos (by linarith) hq
  have he := integral_dimensionKernel_mellin d ha
  rw [← integral_comp_rpow_Ioi_of_pos hq] at he
  have hs : (∫ u : ℝ in Ioi 0, (q * u ^ (q - 1)) •
      ((u ^ q) ^ ((j + 1) / q - 1) * dimensionKernel d (u ^ q))) =
      q * ∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (u ^ q) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [smul_eq_mul, mul_assoc, ← mul_assoc (u ^ (q - 1)),
      mellin_rpow_weight hq j u hu]
  rw [hs] at he
  have hq0 : q ≠ 0 := hq.ne'
  field_simp
  nlinarith [he]

/-- Every real transverse order above the integrability threshold is allowed,
including the fractional orders needed in odd dimensions. -/
theorem integral_dimensionKernel_transverse (d : ℕ) (hd : 0 < d) {j : ℝ}
    (hj : -1 < j) :
    (∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (u ^ ((d : ℝ) / 2))) =
      (2 / (d : ℝ)) * Real.Gamma (2 * (j + 1) / d) *
        ∏ i ∈ Finset.range (dimensionFactorCount d), (1 - (j + 1) / (i + 1)) := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [integral_dimensionKernel_rpow d (div_pos hd' (by norm_num)) hj]
  have he : (j + 1) / ((d : ℝ) / 2) = 2 * (j + 1) / d := by ring
  rw [he, dimensionMellinFactor_transverse d _ hd]
  ring

/-- The vanishing natural moments are actual convergent integrals. -/
theorem integral_dimensionKernel_transverse_zero (d k : ℕ) (hd : 0 < d)
    (hk : k < dimensionFactorCount d) :
    (∫ u : ℝ in Ioi 0, u ^ k * dimensionKernel d (u ^ ((d : ℝ) / 2))) = 0 := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  simp_rw [← Real.rpow_natCast]
  rw [integral_dimensionKernel_rpow d (div_pos hd' (by norm_num))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k))]
  have he : ((k : ℝ) + 1) / ((d : ℝ) / 2) = 2 * (k + 1) / d := by ring
  rw [he, dimensionMellinFactor_root d _ k hd hk, mul_zero]

/-- Positive spatial rescaling, including nonintegral moment orders. -/
theorem integral_dimensionKernel_scaled_rpow (d : ℕ) (q j k : ℝ) (hk : 0 < k) :
    (∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d ((k * u) ^ q)) =
      k ^ (-(j + 1)) * ∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (u ^ q) := by
  have hs := integral_comp_mul_left_Ioi
    (fun u : ℝ => u ^ j * dimensionKernel d (u ^ q)) 0 hk
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (∫ u : ℝ in Ioi 0, (k * u) ^ j * dimensionKernel d ((k * u) ^ q)) =
      k ^ j * ∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d ((k * u) ^ q) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.mul_rpow hk.le hu.le]
    ring
  rw [he] at hs
  have hp : k ^ (-j) * k ^ j = 1 := by
    rw [← Real.rpow_add hk, neg_add_cancel, Real.rpow_zero]
  calc
    _ = k ^ (-j) * (k ^ j * ∫ u : ℝ in Ioi 0,
        u ^ j * dimensionKernel d ((k * u) ^ q)) := by rw [← mul_assoc, hp, one_mul]
    _ = k ^ (-j) * (k⁻¹ * ∫ u : ℝ in Ioi 0,
        u ^ j * dimensionKernel d (u ^ q)) := by rw [hs]
    _ = _ := by
      rw [← Real.rpow_neg_one k, ← mul_assoc, ← Real.rpow_add hk]
      congr 2
      ring

theorem integrableOn_dimensionKernel_scaled_rpow (d : ℕ) {q j k : ℝ}
    (hq : 0 < q) (hj : -1 < j) (hk : 0 < k) :
    IntegrableOn (fun u : ℝ => u ^ j * dimensionKernel d ((k * u) ^ q)) (Ioi 0) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => u ^ j * dimensionKernel d (u ^ q)) 0 hk).mpr
      (by simpa using integrableOn_dimensionKernel_rpow d hq hj)
  apply (hi.const_mul (k ^ (-j))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.mul_rpow hk.le hu.le]
  have hp : k ^ (-j) * k ^ j = 1 := by
    rw [← Real.rpow_add hk, neg_add_cancel, Real.rpow_zero]
  rw [← mul_assoc, ← mul_assoc, hp, one_mul]

private theorem dimensionKernel_density_rpow (d : ℕ) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (u : ℝ) (hu : 0 ≤ u) :
    dimensionKernel d (c * u ^ q) = dimensionKernel d ((c ^ (1 / q) * u) ^ q) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hc.le _) hu, ← Real.rpow_mul hc.le,
    one_div_mul_cancel hq.ne', Real.rpow_one]

/-- Absolute convergence at arbitrary positive density/interval scale. -/
theorem integrableOn_dimensionKernel_density_rpow (d : ℕ) {q j c : ℝ}
    (hq : 0 < q) (hj : -1 < j) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ j * dimensionKernel d (c * u ^ q)) (Ioi 0) := by
  apply (integrableOn_dimensionKernel_scaled_rpow d hq hj
    (Real.rpow_pos_of_pos hc (1 / q))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [dimensionKernel_density_rpow d hq hc u hu.le]

/-- The full density power is derived by substitution in a convergent integral. -/
theorem integral_dimensionKernel_density_rpow (d : ℕ) {q j c : ℝ}
    (hq : 0 < q) (hj : -1 < j) (hc : 0 < c) :
    (∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (c * u ^ q)) =
      c ^ (-(j + 1) / q) * ((1 / q) * Real.Gamma ((j + 1) / q) *
        dimensionMellinFactor d (dimensionFactorCount d) ((j + 1) / q)) := by
  calc
    _ = ∫ u : ℝ in Ioi 0,
        u ^ j * dimensionKernel d ((c ^ (1 / q) * u) ^ q) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [dimensionKernel_density_rpow d hq hc u hu.le]
    _ = _ := by
      rw [integral_dimensionKernel_scaled_rpow d q j _ (Real.rpow_pos_of_pos hc _),
        integral_dimensionKernel_rpow d hq hj, ← Real.rpow_mul hc.le]
      congr 2
      ring

theorem dimensionPolynomialStage_eval_zero (d m : ℕ) :
    (dimensionPolynomialStage d m).eval 0 = 1 := by
  induction m with
  | zero => simp [dimensionPolynomialStage]
  | succ m ih => simpa [dimensionPolynomialStage] using ih

theorem dimensionKernel_zero (d : ℕ) : dimensionKernel d 0 = 1 := by
  simp [dimensionKernel, dimensionPolynomial, dimensionPolynomialStage_eval_zero]

theorem continuous_dimensionKernel (d : ℕ) : Continuous (dimensionKernel d) := by
  have hp (p : Polynomial ℝ) : Continuous (fun z => p.eval z) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [eval_add] using hp.add hq
    | monomial n c =>
      simpa only [eval_monomial] using continuous_const.mul (continuous_id.pow n)
  exact (hp (dimensionPolynomial d)).mul (continuous_id.neg.rexp)

/-- The endpoint value is nonzero: divergent ordinary moments are not assigned
analytic-continuation values. Lean's totalized integral is not a convergence proof. -/
theorem not_integrableOn_dimensionKernel_rpow (d : ℕ) {q j c : ℝ}
    (hq : 0 < q) (hj : j ≤ -1) :
    ¬ IntegrableOn (fun u : ℝ => u ^ j * dimensionKernel d (c * u ^ q)) (Ioi 0) := by
  intro hi
  have hc : ContinuousAt (fun u : ℝ => dimensionKernel d (c * u ^ q)) 0 :=
    (continuous_dimensionKernel d).continuousAt.comp
      (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hq.le)))
  have hl : Tendsto (fun u : ℝ => dimensionKernel d (c * u ^ q)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Real.zero_rpow hq.ne', mul_zero, dimensionKernel_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ u in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) < dimensionKernel d (c * u ^ q) :=
    (tendsto_order.mp hl).1 _ (by norm_num)
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  have hd : 0 < δ := hδ
  have hweight : IntegrableOn (fun u : ℝ => u ^ j) (Ioo 0 δ) := by
    have hi' := (hi.mono_set (Ioo_subset_Ioi_self : Ioo 0 δ ⊆ Ioi 0)).norm.const_mul 2
    apply hi'.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu.1 _),
      norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu.1 _),
      Real.norm_eq_abs, abs_of_pos (lt_trans (by norm_num) (hsmall hu))]
    have hku : 1 ≤ 2 * dimensionKernel d (c * u ^ q) := by
      linarith [show (1 / 2 : ℝ) < dimensionKernel d (c * u ^ q) from hsmall hu]
    nlinarith [mul_le_mul_of_nonneg_left hku (Real.rpow_nonneg hu.1.le j)]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hd).mp hweight
  linarith

/-- Within the convergent range these, and only these, are the transverse roots. -/
theorem integral_dimensionKernel_transverse_ne_zero_iff (d : ℕ) (hd : 0 < d)
    {j : ℝ} (hj : -1 < j) :
    (∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (u ^ ((d : ℝ) / 2))) ≠ 0 ↔
      ∀ k < dimensionFactorCount d, j ≠ (k : ℝ) := by
  rw [integral_dimensionKernel_transverse d hd hj]
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hΓ : Real.Gamma (2 * (j + 1) / d) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (mul_pos (by norm_num) (by linarith)) hd')).ne'
  rw [mul_ne_zero_iff, mul_ne_zero_iff]
  constructor
  · rintro ⟨_, hp⟩ k hk hji
    have h := Finset.prod_ne_zero_iff.mp hp k (Finset.mem_range.mpr hk)
    apply h
    rw [hji, div_self (by positivity : (k : ℝ) + 1 ≠ 0), sub_self]
  · intro h
    refine ⟨⟨div_ne_zero (by norm_num) hd'.ne', hΓ⟩, Finset.prod_ne_zero_iff.mpr ?_⟩
    intro k hk he
    apply h k (Finset.mem_range.mp hk)
    have he' : (j + 1) / ((k : ℝ) + 1) = 1 := by linarith
    have := (div_eq_one_iff_eq (by positivity : (k : ℝ) + 1 ≠ 0)).mp he'
    linarith

/-- The critical half-integral power genuinely survives in odd dimensions. -/
theorem integral_dimensionKernel_odd_critical_ne_zero (d : ℕ) (hd : 0 < d)
    (hodd : d % 2 = 1) :
    (∫ u : ℝ in Ioi 0,
      u ^ ((d : ℝ) / 2) * dimensionKernel d (u ^ ((d : ℝ) / 2))) ≠ 0 := by
  apply (integral_dimensionKernel_transverse_ne_zero_iff d hd
    (by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith)).mpr
  intro k _ he
  have he' : (d : ℝ) = (2 * k : ℕ) := by push_cast; linarith
  have he'' : d = 2 * k := by exact_mod_cast he'
  omega

end BoundaryDraft
