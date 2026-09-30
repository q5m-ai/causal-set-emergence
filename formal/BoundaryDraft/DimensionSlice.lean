import BoundaryDraft.DimensionMellin
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.Taylor

/-!
# The actual dimension-dependent spatial slice

The sphere-area factor divided by two is omitted. The slice is the finite
squared-proper-time integral from section 4 of `notes/dimension-kernels.md`,
not a definition in terms of a Mellin product.

Absolute finite-slice integrability and the small-height bound are proved
first. Odd-dimensional polynomial cancellation gives an exponential bound
and all natural absolute height moments. A Taylor expansion on the lower
half of the sigma interval, with separate absolute control of both tails,
gives the even-dimensional positive `t^-5` term and `O(t^-7)` remainder.
This proves absolute moments of orders zero through three in every supported
dimension and divergence of the even-dimensional fourth absolute moment.
The radial change of variables is proved separately. Evaluation of the signed
height moments and normalization of the action are not claimed here.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- The spatial slice in squared proper time, without the sphere-area factor. -/
def dimensionSigmaSlice (d : ℕ) (c t : ℝ) : ℝ :=
  ∫ σ : ℝ in Ioc 0 (t ^ 2),
    (t ^ 2 - σ) ^ (((d : ℝ) - 3) / 2) *
      dimensionKernel d (c * σ ^ ((d : ℝ) / 2))

private theorem slice_polynomial_continuous (p : Polynomial ℝ) :
    Continuous (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using
      (continuous_const.mul (continuous_id.pow n) : Continuous (fun x : ℝ => c * x ^ n))

private theorem slice_kernel_continuous (d : ℕ) (c : ℝ) :
    Continuous (fun σ : ℝ => dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) := by
  unfold dimensionKernel
  have h : Continuous (fun σ : ℝ => c * σ ^ ((d : ℝ) / 2)) :=
    continuous_const.mul (Real.continuous_rpow_const (by positivity))
  exact ((slice_polynomial_continuous (dimensionPolynomial d)).comp h).mul (Real.continuous_exp.comp h.neg)

/-- The endpoint singularity in dimension two is integrable as well. -/
theorem integrableOn_dimensionSigmaSlice_integrand (d : ℕ) (hd : 2 ≤ d)
    (c t : ℝ) :
    IntegrableOn (fun σ : ℝ =>
      (t ^ 2 - σ) ^ (((d : ℝ) - 3) / 2) *
        dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) (Ioc 0 (t ^ 2)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : IntervalIntegrable
      (fun σ : ℝ => σ ^ (((d : ℝ) - 3) / 2)) volume 0 (t ^ 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hsub := hpow.comp_sub_left (t ^ 2)
  simp only [sub_zero, sub_self] at hsub
  exact (hsub.symm.mul_continuousOn (slice_kernel_continuous d c).continuousOn).1

@[simp] theorem dimensionSigmaSlice_zero (d : ℕ) (c : ℝ) :
    dimensionSigmaSlice d c 0 = 0 := by
  simp [dimensionSigmaSlice]

/-- Absolute natural transverse moments at an arbitrary positive coefficient.
This is used to dominate tails, before using the signed moment zeros. -/
theorem integrableOn_dimensionSliceProfile_moment (d k : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun σ : ℝ => σ ^ k * dimensionKernel d (c * σ ^ ((d : ℝ) / 2)))
      (Ioi 0) := by
  simpa only [Real.rpow_natCast] using integrableOn_dimensionKernel_density_rpow d
    (q := (d : ℝ) / 2) (j := (k : ℝ))
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k)) hc

/-- The natural transverse cancellations persist at every positive coefficient. -/
theorem integral_dimensionSliceProfile_moment_zero (d k : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) (hk : k < dimensionFactorCount d) :
    (∫ σ : ℝ in Ioi 0, σ ^ k * dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) = 0 := by
  simp_rw [← Real.rpow_natCast]
  rw [integral_dimensionKernel_density_rpow d
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k)) hc]
  rw [show ((k : ℝ) + 1) / ((d : ℝ) / 2) = 2 * (k + 1) / d by ring,
    dimensionMellinFactor_root d _ k hd hk, mul_zero, mul_zero]

private theorem slice_power_integral {a α : ℝ} (ha : 0 ≤ a) (hα : -1 < α) :
    (∫ σ : ℝ in Ioc 0 a, (a - σ) ^ α) = a ^ (α + 1) / (α + 1) := by
  rw [← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_comp_sub_left (fun σ : ℝ => σ ^ α) a, sub_self, sub_zero,
    integral_rpow (Or.inl hα), Real.zero_rpow (by linarith : α + 1 ≠ 0), sub_zero]

/-- Global measurability includes the singular two-dimensional endpoint. -/
theorem measurable_dimensionSigmaSlice (d : ℕ) (c : ℝ) :
    Measurable (dimensionSigmaSlice d c) := by
  let f : ℝ → ℝ → ℝ := fun t σ =>
    if 0 < σ ∧ σ ≤ t ^ 2 then
      (t ^ 2 - σ) ^ (((d : ℝ) - 3) / 2) *
        dimensionKernel d (c * σ ^ ((d : ℝ) / 2)) else 0
  have hm : Measurable (Function.uncurry f) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.pow_const (2 : ℕ))))
    · exact (((measurable_fst.pow_const (2 : ℕ)).sub measurable_snd).pow_const _).mul
        ((slice_kernel_continuous d c).measurable.comp measurable_snd)
    · exact measurable_const
  have he : dimensionSigmaSlice d c = fun t => ∫ σ : ℝ, f t σ := by
    funext t
    rw [dimensionSigmaSlice, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext σ
    simp only [indicator, mem_Ioc, f]
  rw [he]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- A bound on every compact positive-height interval. In particular, the
slice is `O(t^(d-1))` at zero in every dimension at least two. -/
theorem dimensionSigmaSlice_local_bound (d : ℕ) (hd : 2 ≤ d) (c T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      |dimensionSigmaSlice d c t| ≤ C * t ^ (d - 1) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let α : ℝ := ((d : ℝ) - 3) / 2
  have hα : -1 < α := by dsimp [α]; linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (T ^ 2)) (slice_kernel_continuous d c).continuousOn
  let D : ℝ := |B| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D / (α + 1), div_pos hD (by linarith), ?_⟩
  intro t ht
  have hpow : IntervalIntegrable (fun σ : ℝ => σ ^ α) volume 0 (t ^ 2) :=
    intervalIntegral.intervalIntegrable_rpow' hα
  have hsub := hpow.comp_sub_left (t ^ 2)
  simp only [sub_zero, sub_self] at hsub
  have hi : IntegrableOn (fun σ : ℝ => (t ^ 2 - σ) ^ α) (Ioc 0 (t ^ 2)) := hsub.symm.1
  have hp : (t ^ 2) ^ (α + 1) = t ^ (d - 1) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.1]
    have he : (2 : ℝ) * (α + 1) = ((d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      dsimp [α]
      ring
    norm_num only [Nat.cast_ofNat]
    rw [he, Real.rpow_natCast]
  calc
    |dimensionSigmaSlice d c t| ≤
        ∫ σ : ℝ in Ioc 0 (t ^ 2),
          ‖(t ^ 2 - σ) ^ α * dimensionKernel d (c * σ ^ ((d : ℝ) / 2))‖ :=
      by
        change ‖∫ σ : ℝ in Ioc 0 (t ^ 2),
          (t ^ 2 - σ) ^ α * dimensionKernel d (c * σ ^ ((d : ℝ) / 2))‖ ≤ _
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ σ : ℝ in Ioc 0 (t ^ 2), D * (t ^ 2 - σ) ^ α := by
      apply setIntegral_mono_on (integrableOn_dimensionSigmaSlice_integrand d hd c t).norm
        (hi.const_mul D) measurableSet_Ioc
      intro σ hσ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hσ.2) _)]
      have hK : |dimensionKernel d (c * σ ^ ((d : ℝ) / 2))| ≤ D := by
        refine (hB σ ⟨hσ.1.le, hσ.2.trans ?_⟩).trans ?_
        · exact pow_le_pow_left₀ ht.1 ht.2 2
        · exact (le_abs_self B).trans (by dsimp [D]; linarith)
      nlinarith [Real.rpow_nonneg (sub_nonneg.mpr hσ.2) α]
    _ = D / (α + 1) * t ^ (d - 1) := by
      rw [integral_const_mul, slice_power_integral (sq_nonneg t) hα, hp]
      ring

/-- Every natural absolute height moment is locally integrable, including at
zero. This statement alone makes no claim about the tail at infinity. -/
theorem integrableOn_dimensionSigmaSlice_moment_local (d : ℕ) (hd : 2 ≤ d)
    (c T : ℝ) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionSigmaSlice d c t) (Ioc 0 T) := by
  obtain ⟨C, _, hC⟩ := dimensionSigmaSlice_local_bound d hd c T
  have hi : IntegrableOn (fun t : ℝ => C * t ^ (k + (d - 1))) (Ioc 0 T) :=
    ((continuous_const.mul (continuous_id.pow _)).intervalIntegrable 0 T).1
  refine hi.mono'
    ((measurable_id.pow_const k).mul (measurable_dimensionSigmaSlice d c)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht.1.le k), pow_add]
  nlinarith [mul_le_mul_of_nonneg_left (hC t ⟨ht.1.le, ht.2⟩) (pow_nonneg ht.1.le k)]

private theorem slice_sub_pow_expand (a σ : ℝ) (n : ℕ) :
    (a - σ) ^ n = ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ k * a ^ (n - k) * (n.choose k : ℝ)) * σ ^ k := by
  rw [show a - σ = -σ + a by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_pow]
  ring

private theorem slice_polynomial_moments (d n : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) (hn : n < dimensionFactorCount d) (a : ℝ) :
    IntegrableOn (fun σ : ℝ => (a - σ) ^ n *
      dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) (Ioi 0) ∧
    (∫ σ : ℝ in Ioi 0, (a - σ) ^ n *
      dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) = 0 := by
  let A : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * a ^ (n - k) * (n.choose k : ℝ)
  have he (σ : ℝ) : (a - σ) ^ n * dimensionKernel d (c * σ ^ ((d : ℝ) / 2)) =
      ∑ k ∈ Finset.range (n + 1), A k *
        (σ ^ k * dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) := by
    rw [slice_sub_pow_expand, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_assoc _ _ _
  simp_rw [he]
  have hi (k : ℕ) (_hk : k ∈ Finset.range (n + 1)) :
      IntegrableOn (fun σ : ℝ => A k *
        (σ ^ k * dimensionKernel d (c * σ ^ ((d : ℝ) / 2)))) (Ioi 0) :=
    (integrableOn_dimensionSliceProfile_moment d k hd hc).const_mul (A k)
  refine ⟨integrable_finset_sum _ hi, ?_⟩
  rw [integral_finset_sum _ hi]
  apply Finset.sum_eq_zero
  intro k hk
  rw [integral_const_mul, integral_dimensionSliceProfile_moment_zero d k hd hc
    (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hn), mul_zero]

/-- In odd dimensions the whole polynomial part cancels. This is an equality
between convergent integrals of the actual kernel, not a formal Mellin rule. -/
theorem dimensionSigmaSlice_odd_eq_tail (n : ℕ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    dimensionSigmaSlice (2 * n + 3) c t =
      -(∫ σ : ℝ in Ioi (t ^ 2), (t ^ 2 - σ) ^ n *
        dimensionKernel (2 * n + 3) (c * σ ^ (((2 * n + 3 : ℕ) : ℝ) / 2))) := by
  have he : (((2 * n + 3 : ℕ) : ℝ) - 3) / 2 = (n : ℝ) := by push_cast; ring
  simp only [dimensionSigmaSlice, he, Real.rpow_natCast]
  obtain ⟨hi, hz⟩ := slice_polynomial_moments (2 * n + 3) n (by omega) hc
    (by unfold dimensionFactorCount; omega) (t ^ 2)
  have hu := setIntegral_union (f := fun σ : ℝ => (t ^ 2 - σ) ^ n *
      dimensionKernel (2 * n + 3) (c * σ ^ (((2 * n + 3 : ℕ) : ℝ) / 2)))
    (s := Ioc 0 (t ^ 2)) (t := Ioi (t ^ 2))
    (by apply disjoint_left.mpr; intro σ hσ hσ'; exact (not_lt_of_ge hσ.2) hσ')
    measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self)
    (hi.mono_set (Ioi_subset_Ioi (sq_nonneg t)))
  rw [Ioc_union_Ioi_eq_Ioi (sq_nonneg t), hz] at hu
  linarith

private theorem slice_integrable_polynomial_exp_rpow (p : Polynomial ℝ) (k : ℕ)
    {q b : ℝ} (hq : 1 ≤ q) (hb : 0 < b) (c : ℝ) :
    IntegrableOn (fun σ : ℝ => σ ^ k * p.eval (c * σ ^ q) *
      Real.exp (-b * σ ^ q)) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    simpa only [Polynomial.eval_add, mul_add, add_mul] using hp.add hr
  | monomial m A =>
    have hs : -1 < (k : ℝ) + q * m := by
      have hq' : 0 ≤ q := le_trans zero_le_one hq
      have : 0 ≤ (k : ℝ) + q * m := by positivity
      linarith
    apply ((integrableOn_rpow_mul_exp_neg_mul_rpow hs hq hb).const_mul (A * c ^ m)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    rw [Polynomial.eval_monomial, mul_pow, ← Real.rpow_natCast σ k,
      ← Real.rpow_natCast (σ ^ q) m, ← Real.rpow_mul hσ.le,
      Real.rpow_add hσ]
    ring

/-- Exponentially weighted absolute profile moments. Half of the exponential
is reserved for the tail estimate, while the polynomial remains integrable. -/
theorem integrableOn_dimensionSliceProfile_exp_moment (d k : ℕ) (hd : 2 ≤ d)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun σ : ℝ => σ ^ k *
      (Real.exp (c / 2 * σ ^ ((d : ℝ) / 2)) *
        |dimensionKernel d (c * σ ^ ((d : ℝ) / 2))|)) (Ioi 0) := by
  have hq : 1 ≤ (d : ℝ) / 2 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hi := (slice_integrable_polynomial_exp_rpow (dimensionPolynomial d) k hq
    (half_pos hc) c).abs
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hσ.le k),
    abs_of_pos (Real.exp_pos _), dimensionKernel, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(c / 2) * σ ^ ((d : ℝ) / 2)) =
      Real.exp (c / 2 * σ ^ ((d : ℝ) / 2)) * Real.exp (-(c * σ ^ ((d : ℝ) / 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- Odd-dimensional slices have an absolute exponential bound after the
finite polynomial cancellation. All polynomial factors have been absorbed
into half of the original exponential. -/
theorem dimensionSigmaSlice_odd_exp_bound (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |dimensionSigmaSlice (2 * n + 3) c t| ≤
        C * Real.exp (-(c / 2) * t ^ (2 * n + 3)) := by
  let d := 2 * n + 3
  let q : ℝ := (d : ℝ) / 2
  let g : ℝ → ℝ := fun σ => σ ^ n *
    (Real.exp (c / 2 * σ ^ q) * |dimensionKernel d (c * σ ^ q)|)
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hg : IntegrableOn g (Ioi 0) := integrableOn_dimensionSliceProfile_exp_moment d n hd hc
  have hg0 : ∀ σ ∈ Ioi (0 : ℝ), 0 ≤ g σ := by
    intro σ hσ
    have hσ' : 0 ≤ σ := hσ.le
    dsimp [g]
    positivity
  let B : ℝ := ∫ σ : ℝ in Ioi 0, g σ
  have hB : 0 ≤ B := setIntegral_nonneg measurableSet_Ioi hg0
  refine ⟨B + 1, by linarith, ?_⟩
  intro t ht
  have hp : (t ^ 2) ^ q = t ^ d := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
    have he : (↑(2 : ℕ) : ℝ) * q = (d : ℝ) := by dsimp [q]; ring
    rw [he, Real.rpow_natCast]
  have hm : Real.exp (c / 2 * t ^ d) * |dimensionSigmaSlice d c t| ≤ B := by
    obtain ⟨hi, _⟩ := slice_polynomial_moments d n (by omega) hc
      (by dsimp [d]; unfold dimensionFactorCount; omega) (t ^ 2)
    have hit := hi.mono_set (Ioi_subset_Ioi (sq_nonneg t))
    have hgt := hg.mono_set (Ioi_subset_Ioi (sq_nonneg t))
    calc
      _ ≤ Real.exp (c / 2 * t ^ d) *
          ∫ σ : ℝ in Ioi (t ^ 2),
            ‖(t ^ 2 - σ) ^ n * dimensionKernel d (c * σ ^ q)‖ := by
        rw [dimensionSigmaSlice_odd_eq_tail n hc t, abs_neg]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        change ‖∫ σ : ℝ in Ioi (t ^ 2),
          (t ^ 2 - σ) ^ n * dimensionKernel d (c * σ ^ q)‖ ≤ _
        exact norm_integral_le_integral_norm _
      _ = ∫ σ : ℝ in Ioi (t ^ 2), Real.exp (c / 2 * t ^ d) *
          ‖(t ^ 2 - σ) ^ n * dimensionKernel d (c * σ ^ q)‖ :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ σ : ℝ in Ioi (t ^ 2), g σ := by
        apply setIntegral_mono_on (hit.norm.const_mul _) hgt measurableSet_Ioi
        intro σ hσ
        have hσ0 : 0 ≤ σ := (sq_nonneg t).trans hσ.le
        have hs : |t ^ 2 - σ| ≤ σ := by
          rw [abs_of_nonpos (sub_nonpos.mpr hσ.le)]
          nlinarith [sq_nonneg t]
        have hep : Real.exp (c / 2 * t ^ d) ≤ Real.exp (c / 2 * σ ^ q) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (half_pos hc).le
          rw [← hp]
          exact Real.rpow_le_rpow (sq_nonneg t) hσ.le hq
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        change _ ≤ σ ^ n * (Real.exp (c / 2 * σ ^ q) * |dimensionKernel d (c * σ ^ q)|)
        calc
          _ ≤ Real.exp (c / 2 * σ ^ q) *
              (σ ^ n * |dimensionKernel d (c * σ ^ q)|) := by
            exact mul_le_mul hep
              (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hs n) (abs_nonneg _))
              (by positivity) (Real.exp_nonneg _)
          _ = _ := by ring
      _ ≤ B := setIntegral_mono_set hg
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ; exact hg0 σ hσ)
        (Eventually.of_forall (Ioi_subset_Ioi (sq_nonneg t)))
  have hbound : |dimensionSigmaSlice d c t| ≤ B * Real.exp (-(c / 2) * t ^ d) := by
    have he : Real.exp (-(c / 2) * t ^ d) = (Real.exp (c / 2 * t ^ d))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [he, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hm)
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))

/-- Every natural height moment of the actual odd-dimensional slice is
absolutely integrable. The exponential estimate, not signed Fubini, supplies
the global dominator. -/
theorem integrableOn_dimensionSigmaSlice_odd_moment (n k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionSigmaSlice (2 * n + 3) c t) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := dimensionSigmaSlice_odd_exp_bound n hc
  have hi : IntegrableOn (fun t : ℝ => C *
      (t ^ k * Real.exp (-(c / 2) * t ^ (2 * n + 3)))) (Ioi 0) := by
    simpa only [Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := ((2 * n + 3 : ℕ) : ℝ))
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k))
        (by exact_mod_cast (show 1 ≤ 2 * n + 3 by omega)) (half_pos hc)).const_mul C
  refine hi.mono'
    ((measurable_id.pow_const k).mul (measurable_dimensionSigmaSlice _ c)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht.le k)]
  calc
    _ ≤ t ^ k * (C * Real.exp (-(c / 2) * t ^ (2 * n + 3))) :=
      mul_le_mul_of_nonneg_left (hC t ht.le) (pow_nonneg ht.le k)
    _ = _ := by ring

/-- Explicit absolute-value form for consumers of odd-dimensional slices. -/
theorem integrableOn_dimensionSigmaSlice_odd_abs_moment (n k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * |dimensionSigmaSlice (2 * n + 3) c t|) (Ioi 0) := by
  apply (integrableOn_dimensionSigmaSlice_odd_moment n k hc).abs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le k)]

private theorem slice_tendsto_polynomial_exp_rpow (p : Polynomial ℝ) (k : ℕ)
    {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    Tendsto (fun σ : ℝ => σ ^ k * p.eval (c * σ ^ q) * Real.exp (-c * σ ^ q))
      atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    simpa only [Polynomial.eval_add, mul_add, add_mul, add_zero] using hp.add hr
  | monomial m A =>
    have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((k : ℝ) / q + m) c hc).comp (tendsto_rpow_atTop hq)).const_mul (A * c ^ m)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
    dsimp only [Function.comp_def]
    rw [Polynomial.eval_monomial, mul_pow, ← Real.rpow_natCast σ k,
      ← Real.rpow_natCast (σ ^ q) m, ← Real.rpow_mul hσ.le,
      ← Real.rpow_mul hσ.le]
    have he : q * ((k : ℝ) / q + m) = (k : ℝ) + q * m := by field_simp; ring
    rw [he, Real.rpow_add hσ]
    ring

private theorem slice_bound_of_continuous_tendsto {f : ℝ → ℝ} (hf : Continuous f)
    (ht : Tendsto f atTop (𝓝 0)) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → |f x| ≤ C := by
  have hh : ∀ᶠ x : ℝ in atTop, ‖f x‖ < 1 := by
    exact (tendsto_order.mp ht.norm).2 1 (by norm_num)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hh
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) R) hf.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro x hx
  by_cases hxR : x ≤ R
  · exact (hB x ⟨hx, hxR⟩).trans ((le_abs_self B).trans (by linarith))
  · exact (hR x (le_of_not_ge hxR)).le.trans (by linarith [abs_nonneg B])

/-- Uniform inverse-power control of the actual profile; this also controls
its contribution next to the integrable spatial endpoint singularity. -/
theorem dimensionSliceProfile_power_bound (d k : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 ≤ σ →
      σ ^ k * |dimensionKernel d (c * σ ^ ((d : ℝ) / 2))| ≤ C := by
  have ht : Tendsto (fun σ : ℝ => σ ^ k * dimensionKernel d (c * σ ^ ((d : ℝ) / 2)))
      atTop (𝓝 0) := by
    simpa only [dimensionKernel, mul_assoc, neg_mul] using
      slice_tendsto_polynomial_exp_rpow (dimensionPolynomial d) k
        (div_pos (Nat.cast_pos.mpr hd) (by norm_num)) hc
  obtain ⟨C, hC, hbound⟩ := slice_bound_of_continuous_tendsto
    ((continuous_id.pow k).mul (slice_kernel_continuous d c)) ht
  refine ⟨C, hC, ?_⟩
  intro σ hσ
  simpa only [id_eq, abs_mul, abs_of_nonneg (pow_nonneg hσ k)] using hbound σ hσ

/-- The ordinary Taylor coefficient of the spatial weight at zero. -/
def dimensionSliceTaylorCoeff (α : ℝ) (k : ℕ) : ℝ :=
  taylorCoeffWithin (fun u : ℝ => (1 - u) ^ α) k (Icc 0 (1 / 2)) 0

private def sliceTaylorPoly (α : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, dimensionSliceTaylorCoeff α k * u ^ k

private theorem slice_taylor_bound (α : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Icc (0 : ℝ) (1 / 2),
      |(1 - u) ^ α - sliceTaylorPoly α N u| ≤ C * u ^ N := by
  cases N with
  | zero => omega
  | succ n =>
    have hf : ContDiffOn ℝ (n + 1) (fun u : ℝ => (1 - u) ^ α) (Icc 0 (1 / 2)) :=
      (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
        (fun u hu => by change 1 - u ≠ 0; linarith [hu.2])
    obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (by norm_num : (0 : ℝ) ≤ 1 / 2) hf
    refine ⟨|C| + 1, by positivity, ?_⟩
    intro u hu
    have he : taylorWithinEval (fun u : ℝ => (1 - u) ^ α) n (Icc 0 (1 / 2)) 0 u =
        sliceTaylorPoly α (n + 1) u := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k _
      simp only [dimensionSliceTaylorCoeff, taylorCoeffWithin, sub_zero, smul_eq_mul]
      ring
    have hh := hC u hu
    rw [he, sub_zero, Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self C).trans (by linarith)) (pow_nonneg hu.1 _))

private theorem slice_taylorPoly_integrable {f : ℝ → ℝ}
    (hi : ∀ k : ℕ, IntegrableOn (fun σ : ℝ => σ ^ k * f σ) (Ioi 0))
    (α a : ℝ) (N : ℕ) :
    IntegrableOn (fun σ : ℝ => sliceTaylorPoly α N (σ / a) * f σ) (Ioi 0) := by
  unfold sliceTaylorPoly
  simp only [Finset.sum_mul, div_pow]
  have he (k : ℕ) (σ : ℝ) : dimensionSliceTaylorCoeff α k * (σ ^ k / a ^ k) * f σ =
      (dimensionSliceTaylorCoeff α k / a ^ k) * (σ ^ k * f σ) := by ring
  simp_rw [he]
  exact integrable_finset_sum _ (fun k _ => (hi k).const_mul _)

private theorem slice_taylorPoly_integral {f : ℝ → ℝ}
    (hi : ∀ k : ℕ, IntegrableOn (fun σ : ℝ => σ ^ k * f σ) (Ioi 0))
    (α a : ℝ) (N : ℕ) :
    (∫ σ : ℝ in Ioi 0, sliceTaylorPoly α N (σ / a) * f σ) =
      ∑ k ∈ Finset.range N, dimensionSliceTaylorCoeff α k / a ^ k *
        ∫ σ : ℝ in Ioi 0, σ ^ k * f σ := by
  unfold sliceTaylorPoly
  simp only [Finset.sum_mul, div_pow]
  have he (k : ℕ) (σ : ℝ) : dimensionSliceTaylorCoeff α k * (σ ^ k / a ^ k) * f σ =
      (dimensionSliceTaylorCoeff α k / a ^ k) * (σ ^ k * f σ) := by ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun k _ => (hi k).const_mul _)]
  simp only [integral_const_mul]

private theorem slice_taylorPoly_tail_bound (α : ℝ) (N : ℕ) {a σ : ℝ}
    (ha : 0 < a) (hσ : a / 2 ≤ σ) :
    |sliceTaylorPoly α N (σ / a)| ≤
      ((∑ k ∈ Finset.range N, |dimensionSliceTaylorCoeff α k| * (2 : ℝ) ^ (N - k)) /
        a ^ N) * σ ^ N := by
  have hσ0 : 0 ≤ σ := (half_pos ha).le.trans hσ
  have hkbound (k : ℕ) (hk : k ∈ Finset.range N) :
      a ^ N * (σ / a) ^ k ≤ (2 : ℝ) ^ (N - k) * σ ^ N := by
    have hkN : k ≤ N := (Finset.mem_range.mp hk).le
    have ha0 : a ≠ 0 := ha.ne'
    calc
      _ = a ^ (N - k) * σ ^ k := by
        rw [div_pow, ← Nat.sub_add_cancel hkN, pow_add]
        field_simp
        ring
      _ ≤ (2 * σ) ^ (N - k) * σ ^ k :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ ha.le (by linarith) _) (pow_nonneg hσ0 k)
      _ = _ := by rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hkN]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos ha N)).mpr
  calc
    |sliceTaylorPoly α N (σ / a)| * a ^ N ≤
        (∑ k ∈ Finset.range N, |dimensionSliceTaylorCoeff α k * (σ / a) ^ k|) * a ^ N :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg ha.le N)
    _ = ∑ k ∈ Finset.range N, |dimensionSliceTaylorCoeff α k| * (a ^ N * (σ / a) ^ k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg (pow_nonneg (div_nonneg hσ0 ha.le) k)]
      ring
    _ ≤ ∑ k ∈ Finset.range N,
        |dimensionSliceTaylorCoeff α k| * ((2 : ℝ) ^ (N - k) * σ ^ N) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hkbound k hk) (abs_nonneg _)
    _ = (∑ k ∈ Finset.range N, |dimensionSliceTaylorCoeff α k| * (2 : ℝ) ^ (N - k)) * σ ^ N := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem slice_convolution_taylor_bound {f : ℝ → ℝ}
    (hf : Continuous f)
    (hi : ∀ k : ℕ, IntegrableOn (fun σ : ℝ => σ ^ k * f σ) (Ioi 0))
    (hb : ∀ k : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ σ : ℝ, 0 ≤ σ → σ ^ k * |f σ| ≤ B)
    {α : ℝ} (hα : -1 < α) (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a →
      |(∫ σ : ℝ in Ioc 0 a, (a - σ) ^ α * f σ) -
        a ^ α * (∑ k ∈ Finset.range N, dimensionSliceTaylorCoeff α k / a ^ k *
          ∫ σ : ℝ in Ioi 0, σ ^ k * f σ)| ≤ C * (a ^ α / a ^ N) := by
  obtain ⟨T, hT, hTaylor⟩ := slice_taylor_bound α N hN
  obtain ⟨B, hB, hProfile⟩ := hb (N + 1)
  let g : ℝ → ℝ := fun σ => σ ^ N * |f σ|
  have hg : IntegrableOn g (Ioi 0) := by
    apply (hi N).abs.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    rw [abs_mul, abs_of_nonneg (pow_nonneg hσ.le N)]
  have hg0 (σ : ℝ) (hσ : 0 ≤ σ) : 0 ≤ g σ := mul_nonneg (pow_nonneg hσ N) (abs_nonneg _)
  let M : ℝ := ∫ σ : ℝ in Ioi 0, g σ
  have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi (fun σ hσ => hg0 σ hσ.le)
  have hMoment (U : Set ℝ) (hU : U ⊆ Ioi (0 : ℝ)) : (∫ σ : ℝ in U, g σ) ≤ M :=
    setIntegral_mono_set hg
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ; exact hg0 σ hσ.le)
      (Eventually.of_forall hU)
  let S : ℝ := ∑ k ∈ Finset.range N, |dimensionSliceTaylorCoeff α k| * (2 : ℝ) ^ (N - k)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => by positivity)
  let E : ℝ := B * (2 : ℝ) ^ (N + 1) / (α + 1)
  have hE : 0 < E := div_pos (mul_pos hB (by positivity)) (by linarith)
  refine ⟨T * M + E + S * M + 1, by positivity, ?_⟩
  intro a ha
  let w : ℝ → ℝ := fun σ => (a - σ) ^ α
  let p : ℝ → ℝ := fun σ => a ^ α * sliceTaylorPoly α N (σ / a)
  let L := Ioc (0 : ℝ) (a / 2)
  let H := Ioc (a / 2) a
  let U := Ioi (a / 2)
  let A : ℝ := a ^ α / a ^ N
  have hA : 0 ≤ A := div_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg ha.le N)
  have hL : L ⊆ Ioi (0 : ℝ) := Ioc_subset_Ioi_self
  have hU : U ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (half_pos ha).le
  have hLa : L ⊆ Ioc (0 : ℝ) a := Ioc_subset_Ioc_right (by linarith)
  have hHa : H ⊆ Ioc (0 : ℝ) a := Ioc_subset_Ioc_left (half_pos ha).le
  have hpow : IntervalIntegrable (fun σ : ℝ => σ ^ α) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' hα
  have hw := hpow.comp_sub_left a
  simp only [sub_zero, sub_self] at hw
  have hwi : IntegrableOn w (Ioc 0 a) := hw.symm.1
  have hwfi : IntegrableOn (fun σ => w σ * f σ) (Ioc 0 a) :=
    (hw.symm.mul_continuousOn hf.continuousOn).1
  have hpi : IntegrableOn (fun σ => p σ * f σ) (Ioi 0) := by
    simpa only [p, mul_assoc] using (slice_taylorPoly_integrable hi α a N).const_mul (a ^ α)
  have hrem : IntegrableOn (fun σ => (w σ - p σ) * f σ) L := by
    simpa only [sub_mul] using (hwfi.mono_set hLa).sub (hpi.mono_set hL)
  have hlow : |∫ σ : ℝ in L, (w σ - p σ) * f σ| ≤ (T * M) * A := by
    calc
      _ ≤ ∫ σ : ℝ in L, ‖(w σ - p σ) * f σ‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict L) (fun σ => (w σ - p σ) * f σ)
      _ ≤ ∫ σ : ℝ in L, (T * A) * g σ := by
        apply setIntegral_mono_on hrem.norm ((hg.mono_set hL).const_mul _) measurableSet_Ioc
        intro σ hσ
        have hσ0 : 0 ≤ σ := hσ.1.le
        have hu : σ / a ∈ Icc (0 : ℝ) (1 / 2) :=
          ⟨div_nonneg hσ0 ha.le, (div_le_iff₀ ha).mpr (by linarith [hσ.2])⟩
        have hw_eq : w σ = a ^ α * (1 - σ / a) ^ α := by
          rw [← Real.mul_rpow ha.le (by linarith [hu.2])]
          dsimp only [w]
          congr 1
          field_simp
        have hbnd : |w σ - p σ| ≤ (T * A) * σ ^ N := by
          rw [hw_eq]
          dsimp only [p]
          rw [← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le _)]
          calc
            _ ≤ a ^ α * (T * (σ / a) ^ N) :=
              mul_le_mul_of_nonneg_left (hTaylor _ hu) (Real.rpow_nonneg ha.le _)
            _ = _ := by dsimp [A]; rw [div_pow]; ring
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)).trans_eq (by dsimp [g]; ring)
      _ = (T * A) * ∫ σ : ℝ in L, g σ := integral_const_mul _ _
      _ ≤ (T * A) * M := mul_le_mul_of_nonneg_left (hMoment L hL) (mul_nonneg hT.le hA)
      _ = _ := by ring
  have hhigh : |∫ σ : ℝ in H, w σ * f σ| ≤ E * A := by
    let D : ℝ := B * (2 : ℝ) ^ (N + 1) / a ^ (N + 1)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hbound (σ : ℝ) (hσ : σ ∈ H) : |f σ| ≤ D := by
      have hσ0 : 0 ≤ σ := (half_pos ha).le.trans hσ.1.le
      apply (le_div_iff₀ (pow_pos ha (N + 1))).mpr
      calc
        |f σ| * a ^ (N + 1) ≤ |f σ| * (2 * σ) ^ (N + 1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ ha.le (by linarith [hσ.1]) _) (abs_nonneg _)
        _ = (2 : ℝ) ^ (N + 1) * (σ ^ (N + 1) * |f σ|) := by rw [mul_pow]; ring
        _ ≤ (2 : ℝ) ^ (N + 1) * B :=
          mul_le_mul_of_nonneg_left (hProfile σ hσ0) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∫ σ : ℝ in H, ‖w σ * f σ‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict H) (fun σ => w σ * f σ)
      _ ≤ ∫ σ : ℝ in H, D * w σ := by
        apply setIntegral_mono_on (hwfi.mono_set hHa).norm
          ((hwi.mono_set hHa).const_mul D) measurableSet_Ioc
        intro σ hσ
        have hw0 : 0 ≤ w σ := Real.rpow_nonneg (sub_nonneg.mpr hσ.2) _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
        exact (mul_le_mul_of_nonneg_left (hbound σ hσ) hw0).trans_eq (mul_comm _ _)
      _ = D * ∫ σ : ℝ in H, w σ := integral_const_mul _ _
      _ ≤ D * ∫ σ : ℝ in Ioc 0 a, w σ := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply setIntegral_mono_set hwi _ (Eventually.of_forall hHa)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
        exact Real.rpow_nonneg (sub_nonneg.mpr hσ.2) _
      _ = E * A := by
        rw [show (∫ σ : ℝ in Ioc 0 a, w σ) = a ^ (α + 1) / (α + 1) from
          slice_power_integral ha.le hα, Real.rpow_add ha, Real.rpow_one]
        dsimp [D, E, A]
        simp only [pow_succ]
        field_simp [ha.ne', show α + 1 ≠ 0 by linarith]
        ring
  have hpoly : |∫ σ : ℝ in U, p σ * f σ| ≤ (S * M) * A := by
    calc
      _ ≤ ∫ σ : ℝ in U, ‖p σ * f σ‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict U) (fun σ => p σ * f σ)
      _ ≤ ∫ σ : ℝ in U, (S * A) * g σ := by
        apply setIntegral_mono_on (hpi.mono_set hU).norm
          ((hg.mono_set hU).const_mul _) measurableSet_Ioi
        intro σ hσ
        rw [Real.norm_eq_abs, abs_mul]
        dsimp only [p]
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le _)]
        have hbnd := slice_taylorPoly_tail_bound α N ha hσ.le
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg ha.le _)) (abs_nonneg _)).trans_eq
            (by dsimp [S, A, g]; ring)
      _ = (S * A) * ∫ σ : ℝ in U, g σ := integral_const_mul _ _
      _ ≤ (S * A) * M := mul_le_mul_of_nonneg_left (hMoment U hU) (mul_nonneg hS hA)
      _ = _ := by ring
  have hsplit : (∫ σ : ℝ in Ioc 0 a, w σ * f σ) =
      (∫ σ : ℝ in L, w σ * f σ) + ∫ σ : ℝ in H, w σ * f σ := by
    have hu : L ∪ H = Ioc 0 a := Ioc_union_Ioc_eq_Ioc (half_pos ha).le (by linarith)
    rw [← hu]
    exact setIntegral_union
      (by apply disjoint_left.mpr; intro σ hσ hσ'; exact (not_lt_of_ge hσ.2) hσ'.1)
      measurableSet_Ioc (hwfi.mono_set hLa) (hwfi.mono_set hHa)
  have hpsplit : (∫ σ : ℝ in Ioi 0, p σ * f σ) =
      (∫ σ : ℝ in L, p σ * f σ) + ∫ σ : ℝ in U, p σ * f σ := by
    have hu : L ∪ U = Ioi 0 := Ioc_union_Ioi_eq_Ioi (half_pos ha).le
    rw [← hu]
    exact setIntegral_union
      (by apply disjoint_left.mpr; intro σ hσ hσ'; exact (not_lt_of_ge hσ.2) hσ')
      measurableSet_Ioi (hpi.mono_set hL) (hpi.mono_set hU)
  have hpint : (∫ σ : ℝ in Ioi 0, p σ * f σ) =
      a ^ α * (∑ k ∈ Finset.range N, dimensionSliceTaylorCoeff α k / a ^ k *
        ∫ σ : ℝ in Ioi 0, σ ^ k * f σ) := by
    simp only [p, mul_assoc, integral_const_mul, slice_taylorPoly_integral hi]
  have heq : (∫ σ : ℝ in Ioc 0 a, w σ * f σ) -
      (∫ σ : ℝ in Ioi 0, p σ * f σ) =
      (∫ σ : ℝ in L, (w σ - p σ) * f σ) +
        (∫ σ : ℝ in H, w σ * f σ) - ∫ σ : ℝ in U, p σ * f σ := by
    simp only [sub_mul]
    rw [integral_sub (hwfi.mono_set hLa) (hpi.mono_set hL), hsplit, hpsplit]
    ring
  rw [← hpint]
  change |(∫ σ : ℝ in Ioc 0 a, w σ * f σ) - (∫ σ : ℝ in Ioi 0, p σ * f σ)| ≤ _
  rw [heq]
  calc
    _ ≤ |(∫ σ : ℝ in L, (w σ - p σ) * f σ) + (∫ σ : ℝ in H, w σ * f σ)| +
        |∫ σ : ℝ in U, p σ * f σ| := abs_sub _ _
    _ ≤ (|∫ σ : ℝ in L, (w σ - p σ) * f σ| + |∫ σ : ℝ in H, w σ * f σ|) +
        |∫ σ : ℝ in U, p σ * f σ| := add_le_add_right (abs_add _ _) _
    _ ≤ _ := by
      change _ ≤ (T * M + E + S * M + 1) * A
      nlinarith [hlow, hhigh, hpoly]

/-- A finite Taylor expansion of the actual slice, with a proved absolute
remainder. The split at half the squared height retains the two-dimensional
endpoint singularity; no divergent double integral is interchanged. -/
theorem dimensionSigmaSlice_taylor_bound (d : ℕ) (hd : 2 ≤ d)
    {c : ℝ} (hc : 0 < c) (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      |dimensionSigmaSlice d c t -
        (t ^ 2) ^ (((d : ℝ) - 3) / 2) *
          (∑ k ∈ Finset.range N,
            dimensionSliceTaylorCoeff (((d : ℝ) - 3) / 2) k / (t ^ 2) ^ k *
              ∫ σ : ℝ in Ioi 0, σ ^ k * dimensionKernel d (c * σ ^ ((d : ℝ) / 2)))| ≤
        C * ((t ^ 2) ^ (((d : ℝ) - 3) / 2) / (t ^ 2) ^ N) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC, hb⟩ := slice_convolution_taylor_bound (slice_kernel_continuous d c)
    (fun k => integrableOn_dimensionSliceProfile_moment d k (by omega) hc)
    (fun k => dimensionSliceProfile_power_bound d k (by omega) hc)
    (show -1 < ((d : ℝ) - 3) / 2 by linarith) N hN
  exact ⟨C, hC, fun t ht => hb (t ^ 2) (sq_pos_of_pos ht)⟩

private theorem slice_sq_weight_power {t α : ℝ} (ht : 0 < t) (N k : ℕ)
    (he : 2 * (α - (N : ℝ)) = -(k : ℝ)) :
    (t ^ 2) ^ α / (t ^ 2) ^ N = 1 / t ^ k := by
  rw [← Real.rpow_sub_natCast (ne_of_gt (sq_pos_of_pos ht)),
    ← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.rpow_neg ht.le, Real.rpow_natCast, one_div]

/-- Even-dimensional absolute `t^-5` control, after all vanishing transverse
moments are cancelled. The constant does not depend on height. -/
theorem dimensionSigmaSlice_even_tail_bound (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      |dimensionSigmaSlice (2 * n + 2) c t| ≤ C / t ^ 5 := by
  obtain ⟨C, hC, hb⟩ := dimensionSigmaSlice_taylor_bound (2 * n + 2) (by omega) hc
    (n + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hz : (∑ k ∈ Finset.range (n + 2),
      dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) k / (t ^ 2) ^ k *
        ∫ σ : ℝ in Ioi 0, σ ^ k *
          dimensionKernel (2 * n + 2) (c * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_dimensionSliceProfile_moment_zero (2 * n + 2) k (by omega) hc
      (by unfold dimensionFactorCount; have := Finset.mem_range.mp hk; omega), mul_zero]
  have he := slice_sq_weight_power ht (n + 2) 5
    (α := (((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (by push_cast; ring)
  simpa only [hz, mul_zero, sub_zero, he, mul_one_div] using hb t ht

/-- The even-dimensional leading term and `O(t^-7)` error. The coefficient is
an actual Taylor coefficient times an absolutely convergent transverse
moment; its further Gamma/binomial evaluation is separate from this estimate. -/
theorem dimensionSigmaSlice_even_leading_remainder (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      |dimensionSigmaSlice (2 * n + 2) c t -
        (dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (n + 2) *
          (∫ σ : ℝ in Ioi 0, σ ^ (n + 2) *
            dimensionKernel (2 * n + 2) (c * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2)))) /
          t ^ 5| ≤ C / t ^ 7 := by
  obtain ⟨C, hC, hb⟩ := dimensionSigmaSlice_taylor_bound (2 * n + 2) (by omega) hc
    ((n + 2) + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hz : (∑ k ∈ Finset.range (n + 2),
      dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) k / (t ^ 2) ^ k *
        ∫ σ : ℝ in Ioi 0, σ ^ k *
          dimensionKernel (2 * n + 2) (c * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_dimensionSliceProfile_moment_zero (2 * n + 2) k (by omega) hc
      (by unfold dimensionFactorCount; have := Finset.mem_range.mp hk; omega), mul_zero]
  have he5 := slice_sq_weight_power ht (n + 2) 5
    (α := (((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (by push_cast; ring)
  have he7 := slice_sq_weight_power ht ((n + 2) + 1) 7
    (α := (((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (by push_cast; ring)
  have hh := hb t ht
  rw [Finset.sum_range_succ, hz, zero_add, he7, mul_one_div] at hh
  convert hh using 1
  congr 2
  rw [show (t ^ 2) ^ ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) *
      (dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (n + 2) / (t ^ 2) ^ (n + 2) *
        (∫ σ : ℝ in Ioi 0, σ ^ (n + 2) * dimensionKernel (2 * n + 2)
          (c * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2)))) =
      ((t ^ 2) ^ ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) / (t ^ 2) ^ (n + 2)) *
        (dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (n + 2) *
          (∫ σ : ℝ in Ioi 0, σ ^ (n + 2) * dimensionKernel (2 * n + 2)
            (c * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2)))) by ring, he5]
  ring

/-- The four required absolute height moments are integrable in every even
dimension, including dimension two. -/
theorem integrableOn_dimensionSigmaSlice_even_moment (n k : ℕ) (hk : k ≤ 3)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionSigmaSlice (2 * n + 2) c t) (Ioi 0) := by
  obtain ⟨C, hC, hbound⟩ := dimensionSigmaSlice_even_tail_bound n hc
  have hi : IntegrableOn (fun t : ℝ => C / t ^ 2) (Ioi 1) := by
    have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul C
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    rw [show (-2 : ℝ) = -(↑(2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0,
      Real.rpow_natCast, div_eq_mul_inv]
  have hit : IntegrableOn (fun t : ℝ => t ^ k * dimensionSigmaSlice (2 * n + 2) c t) (Ioi 1) := by
    apply hi.mono'
      ((measurable_id.pow_const k).mul (measurable_dimensionSigmaSlice _ c)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_mul, id_eq, abs_of_nonneg (pow_nonneg ht0.le k)]
    calc
      _ ≤ t ^ 3 * |dimensionSigmaSlice (2 * n + 2) c t| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht.le hk) (abs_nonneg _)
      _ ≤ t ^ 3 * (C / t ^ 5) := mul_le_mul_of_nonneg_left (hbound t ht0) (pow_nonneg ht0.le 3)
      _ = _ := by field_simp; ring
  have hil := integrableOn_dimensionSigmaSlice_moment_local (2 * n + 2) (by omega) c 1 k
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using hil.union hit

/-- Orders zero through three are absolutely integrable before any evaluation
of signed slice moments, in every supported dimension. -/
theorem integrableOn_dimensionSigmaSlice_moment (d k : ℕ) (hd : 2 ≤ d) (hk : k ≤ 3)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionSigmaSlice d c t) (Ioi 0) := by
  rcases Nat.even_or_odd d with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · cases n with
    | zero => omega
    | succ n =>
      rw [show (n + 1) + (n + 1) = 2 * n + 2 by omega]
      exact integrableOn_dimensionSigmaSlice_even_moment n k hk hc
  · cases n with
    | zero => omega
    | succ n =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
      exact integrableOn_dimensionSigmaSlice_odd_moment n k hc

/-- Explicit absolute-value form of the all-dimensional moment theorem. -/
theorem integrableOn_dimensionSigmaSlice_abs_moment (d k : ℕ) (hd : 2 ≤ d) (hk : k ≤ 3)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * |dimensionSigmaSlice d c t|) (Ioi 0) := by
  apply (integrableOn_dimensionSigmaSlice_moment d k hd hk hc).abs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le k)]

private theorem slice_iteratedDeriv_weight (α : ℝ) (k : ℕ) :
    ∀ u ∈ Icc (0 : ℝ) (1 / 2),
      iteratedDerivWithin k (fun v : ℝ => (1 - v) ^ α) (Icc 0 (1 / 2)) u =
        ((-1 : ℝ) ^ k * ∏ i ∈ Finset.range k, (α - (i : ℝ))) * (1 - u) ^ (α - k) := by
  induction k with
  | zero => intro u _; simp
  | succ k ih =>
    intro u hu
    have hne : 1 - u ≠ 0 := by linarith [hu.2]
    have hder := (((hasDerivAt_id u).const_sub 1).rpow_const
      (p := α - (k : ℝ)) (Or.inl hne)).const_mul
        ((-1 : ℝ) ^ k * ∏ i ∈ Finset.range k, (α - (i : ℝ)))
    have hd := (hder.hasDerivWithinAt.congr ih (ih u hu)).derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 2) u hu)
    rw [iteratedDerivWithin_succ, hd, Finset.prod_range_succ, pow_succ]
    push_cast
    rw [show α - ((k : ℝ) + 1) = α - (k : ℝ) - 1 by ring]
    simp only [id_eq]
    ring

/-- Explicit finite-product evaluation of the spatial Taylor coefficient. -/
theorem dimensionSliceTaylorCoeff_eq (α : ℝ) (k : ℕ) :
    dimensionSliceTaylorCoeff α k =
      ((k.factorial : ℝ)⁻¹ * (-1 : ℝ) ^ k) *
        ∏ i ∈ Finset.range k, (α - (i : ℝ)) := by
  rw [dimensionSliceTaylorCoeff, taylorCoeffWithin,
    slice_iteratedDeriv_weight α k 0 (by norm_num)]
  simp only [sub_zero, Real.one_rpow, mul_one, smul_eq_mul]
  ring

/-- The even-dimensional first surviving Taylor coefficient has the sign
that cancels the sign of the first surviving transverse moment. -/
theorem dimensionSliceTaylorCoeff_even_sign (n : ℕ) :
    0 < (-1 : ℝ) ^ (n + 2) *
      dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (n + 2) := by
  let α : ℝ := (((2 * n + 2 : ℕ) : ℝ) - 3) / 2
  have he : α = (n : ℝ) - 1 / 2 := by dsimp [α]; push_cast; ring
  have hprod : 0 < ∏ i ∈ Finset.range n, (α - (i : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast (Finset.mem_range.mp hi)
    rw [he]
    linarith
  have hprod' : 0 < ∏ i ∈ Finset.range (n + 2), (α - (i : ℝ)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    have h1 : α - (n : ℝ) = -(1 / 2) := by rw [he]; ring
    have h2 : α - ((n + 1 : ℕ) : ℝ) = -(3 / 2) := by rw [he]; push_cast; ring
    rw [h1, h2]
    nlinarith
  have hs : (-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2) = 1 := by
    rw [← mul_pow]
    norm_num
  change 0 < (-1 : ℝ) ^ (n + 2) * dimensionSliceTaylorCoeff α (n + 2)
  rw [dimensionSliceTaylorCoeff_eq]
  have hf : 0 < ((n + 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  calc
    0 < ((n + 2).factorial : ℝ)⁻¹ * (∏ i ∈ Finset.range (n + 2), (α - (i : ℝ))) :=
      mul_pos (inv_pos.mpr hf) hprod'
    _ = _ := by
      symm
      calc
        _ = ((n + 2).factorial : ℝ)⁻¹ *
            ((-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2)) *
              (∏ i ∈ Finset.range (n + 2), (α - (i : ℝ))) := by ring
        _ = _ := by rw [hs, mul_one]

/-- The first uncancelled scaled transverse moment has sign `(-1)^m`.
Its sign is proved from the integrated Mellin identity, not postulated. -/
theorem dimensionSliceProfile_first_moment_sign (d : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) :
    0 < (-1 : ℝ) ^ dimensionFactorCount d *
      (∫ σ : ℝ in Ioi 0, σ ^ dimensionFactorCount d *
        dimensionKernel d (c * σ ^ ((d : ℝ) / 2))) := by
  let m := dimensionFactorCount d
  have hq : 0 < (d : ℝ) / 2 := div_pos (Nat.cast_pos.mpr hd) (by norm_num)
  have ha : 0 < ((m : ℝ) + 1) / ((d : ℝ) / 2) := div_pos (by positivity) hq
  have hfactor : 0 < (-1 : ℝ) ^ m *
      dimensionMellinFactor d m (((m : ℝ) + 1) / ((d : ℝ) / 2)) := by
    rw [show ((m : ℝ) + 1) / ((d : ℝ) / 2) = 2 * (m + 1) / d by ring,
      dimensionMellinFactor_transverse d m hd (m : ℝ),
      show (-1 : ℝ) ^ m = ∏ _i ∈ Finset.range m, (-1 : ℝ) by simp,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro i hi
    have hi' : (i : ℝ) < m := by exact_mod_cast Finset.mem_range.mp hi
    have hr : 1 < ((m : ℝ) + 1) / ((i : ℝ) + 1) :=
      (lt_div_iff₀ (by positivity)).mpr (by linarith)
    nlinarith
  change 0 < (-1 : ℝ) ^ m * _
  simp_rw [← Real.rpow_natCast]
  rw [integral_dimensionKernel_density_rpow d hq
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg m)) hc]
  simp only [Real.rpow_natCast]
  have hpos : 0 < c ^ (-((m : ℝ) + 1) / ((d : ℝ) / 2)) *
      (1 / ((d : ℝ) / 2)) * Real.Gamma (((m : ℝ) + 1) / ((d : ℝ) / 2)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hc _) (one_div_pos.mpr hq)) (Real.Gamma_pos_of_pos ha)
  convert mul_pos hpos hfactor using 1
  ring

/-- Strict positivity of the actual even-dimensional leading coefficient. -/
theorem dimensionSigmaSlice_even_leading_pos (n : ℕ) {c : ℝ} (hc : 0 < c) :
    0 < dimensionSliceTaylorCoeff ((((2 * n + 2 : ℕ) : ℝ) - 3) / 2) (n + 2) *
      (∫ σ : ℝ in Ioi 0, σ ^ (n + 2) *
        dimensionKernel (2 * n + 2) (c * σ ^ (((2 * n + 2 : ℕ) : ℝ) / 2))) := by
  have hcoeff := dimensionSliceTaylorCoeff_even_sign n
  have hm := dimensionSliceProfile_first_moment_sign (2 * n + 2) (by omega) hc
  rw [show dimensionFactorCount (2 * n + 2) = n + 2 by unfold dimensionFactorCount; omega] at hm
  have hs : (-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2) = 1 := by
    rw [← mul_pow]
    norm_num
  have hh := mul_pos hcoeff hm
  have he (A B : ℝ) : ((-1 : ℝ) ^ (n + 2) * A) * ((-1 : ℝ) ^ (n + 2) * B) = A * B := by
    calc
      _ = ((-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2)) * (A * B) := by ring
      _ = _ := by rw [hs, one_mul]
  rwa [he] at hh

private theorem slice_not_integrable_fourth_of_remainder {F : ℝ → ℝ} {D C : ℝ}
    (hD : 0 < D) (hrem : ∀ t : ℝ, 0 < t → |F t - D / t ^ 5| ≤ C / t ^ 7) :
    ¬ IntegrableOn (fun t : ℝ => t ^ 4 * |F t|) (Ioi 0) := by
  intro hi
  let R : ℝ := max 1 (2 * C / D)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlower (t : ℝ) (ht : R < t) : (D / 2) / t ≤ t ^ 4 * |F t| := by
    have ht1 : 1 ≤ t := (le_max_left _ _).trans ht.le
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have htD : 2 * C / D ≤ t := (le_max_right _ _).trans ht.le
    have hlarge : 2 * C ≤ D * t ^ 2 := by
      have hh := (div_le_iff₀ hD).mp htD
      have hs : t ≤ t ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs hD.le]
    have hh := (abs_sub_le_iff.mp (hrem t ht0)).2
    have hab : D / t ^ 5 ≤ |F t| + C / t ^ 7 := by linarith [le_abs_self (F t)]
    have hm := mul_le_mul_of_nonneg_right hab (pow_nonneg ht0.le 7)
    have he1 : (D / t ^ 5) * t ^ 7 = D * t ^ 2 := by field_simp; ring
    have he2 : (|F t| + C / t ^ 7) * t ^ 7 = t ^ 7 * |F t| + C := by field_simp; ring
    rw [he1, he2] at hm
    apply (mul_le_mul_right (pow_pos ht0 3)).mp
    have he3 : ((D / 2) / t) * t ^ 3 = (D / 2) * t ^ 2 := by field_simp; ring
    have he4 : (t ^ 4 * |F t|) * t ^ 3 = t ^ 7 * |F t| := by ring
    rw [he3, he4]
    nlinarith
  have hg : IntegrableOn (fun t : ℝ => (D / 2) / t) (Ioi R) := by
    apply (hi.mono_set (Ioi_subset_Ioi hR.le)).mono'
      (measurable_const.div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hR.trans ht
    rw [Real.norm_eq_abs, id_eq, abs_of_nonneg (div_nonneg (half_pos hD).le ht0.le)]
    exact hlower t ht
  have hinv : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioi R) := by
    apply (hg.const_mul (D / 2)⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
    rw [Real.rpow_neg_one]
    simp only [div_eq_mul_inv]
    rw [← mul_assoc, inv_mul_cancel₀ (show D * (2 : ℝ)⁻¹ ≠ 0 by positivity), one_mul]
  have hh := (integrableOn_Ioi_rpow_iff hR).mp hinv
  linarith

/-- The even-dimensional fourth absolute height moment really diverges.
The positive leading coefficient is derived above, rather than assumed. -/
theorem not_integrableOn_dimensionSigmaSlice_even_abs_fourth (n : ℕ)
    {c : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun t : ℝ => t ^ 4 * |dimensionSigmaSlice (2 * n + 2) c t|) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := dimensionSigmaSlice_even_leading_remainder n hc
  exact slice_not_integrable_fourth_of_remainder (dimensionSigmaSlice_even_leading_pos n hc) hC

/-- The signed fourth moment is not a Bochner-integrable integral either. -/
theorem not_integrableOn_dimensionSigmaSlice_even_fourth (n : ℕ)
    {c : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun t : ℝ => t ^ 4 * dimensionSigmaSlice (2 * n + 2) c t) (Ioi 0) := by
  intro hi
  apply not_integrableOn_dimensionSigmaSlice_even_abs_fourth n hc
  apply hi.abs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le 4)]

/-- Absolute integrability of the finite radial spatial integral. -/
theorem integrableOn_dimensionSigmaSlice_radial (d : ℕ) (c t : ℝ) :
    IntegrableOn (fun r : ℝ => r ^ (d - 2) *
      dimensionKernel d (c * (t ^ 2 - r ^ 2) ^ ((d : ℝ) / 2))) (Ioc 0 t) := by
  have hσ : Continuous (fun r : ℝ => t ^ 2 - r ^ 2) :=
    continuous_const.sub (continuous_id.pow 2)
  exact (((continuous_id.pow (d - 2)).mul
    ((slice_kernel_continuous d c).comp hσ)).intervalIntegrable 0 t).1

/-- Exact radial change of variables for the complete spatial slice.
Multiplication by the sphere-area factor divided by two recovers the usual
spatial polar integral. This includes the singular sigma weight in dimension
two; no endpoint is deleted except a Lebesgue-null singleton. -/
theorem dimensionSigmaSlice_eq_radial (d : ℕ) (hd : 2 ≤ d) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    dimensionSigmaSlice d c t = 2 *
      ∫ r : ℝ in Ioc 0 t, r ^ (d - 2) *
        dimensionKernel d (c * (t ^ 2 - r ^ 2) ^ ((d : ℝ) / 2)) := by
  let α : ℝ := ((d : ℝ) - 3) / 2
  let f : ℝ → ℝ := fun u => u ^ α * dimensionKernel d (c * (t ^ 2 - u) ^ ((d : ℝ) / 2))
  let g : ℝ → ℝ := (Ioc 0 (t ^ 2)).indicator f
  let h : ℝ → ℝ := fun r => r ^ (d - 2) *
    dimensionKernel d (c * (t ^ 2 - r ^ 2) ^ ((d : ℝ) / 2))
  have hreflect : dimensionSigmaSlice d c t = ∫ u : ℝ in Ioc 0 (t ^ 2), f u := by
    have he := intervalIntegral.integral_comp_sub_left
      (fun σ : ℝ => (t ^ 2 - σ) ^ α * dimensionKernel d (c * σ ^ ((d : ℝ) / 2)))
      (a := 0) (b := t ^ 2) (t ^ 2)
    simp only [sub_self, sub_zero, sub_sub_cancel,
      intervalIntegral.integral_of_le (sq_nonneg t)] at he
    exact he.symm
  have hg : (∫ u : ℝ in Ioi 0, g u) = ∫ u : ℝ in Ioc 0 (t ^ 2), f u := by
    rw [show g = (Ioc 0 (t ^ 2)).indicator f from rfl,
      setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hsub := integral_comp_rpow_Ioi_of_pos (g := g) (by norm_num : (0 : ℝ) < 2)
  have hsquare (r : ℝ) : r ^ (2 : ℝ) = r ^ 2 := Real.rpow_natCast r 2
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hsquare, smul_eq_mul] at hsub
  have hpoint (r : ℝ) (hr : 0 < r) : (2 * r) * g (r ^ 2) =
      2 * (Ioc 0 t).indicator h r := by
    by_cases hrt : r ≤ t
    · have hr2 : r ^ 2 ∈ Ioc 0 (t ^ 2) := ⟨sq_pos_of_pos hr, (sq_le_sq₀ hr.le ht).mpr hrt⟩
      change (2 * r) * (Ioc 0 (t ^ 2)).indicator f (r ^ 2) = _
      rw [indicator_of_mem hr2, indicator_of_mem (show r ∈ Ioc 0 t from ⟨hr, hrt⟩)]
      have hpower : r * (r ^ 2) ^ α = r ^ (d - 2) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
        norm_num only [Nat.cast_ofNat]
        calc
          _ = r ^ (1 : ℝ) * r ^ ((2 : ℝ) * α) := by rw [Real.rpow_one]
          _ = r ^ (1 + 2 * α) := (Real.rpow_add hr _ _).symm
          _ = _ := by
            have he : 1 + 2 * α = ((d - 2 : ℕ) : ℝ) := by
              rw [Nat.cast_sub hd, Nat.cast_ofNat]
              dsimp [α]
              ring
            rw [he, Real.rpow_natCast]
      change (2 * r) * ((r ^ 2) ^ α * dimensionKernel d (c * (t ^ 2 - r ^ 2) ^ ((d : ℝ) / 2))) =
        2 * (r ^ (d - 2) * dimensionKernel d (c * (t ^ 2 - r ^ 2) ^ ((d : ℝ) / 2)))
      rw [← mul_assoc, mul_assoc 2 r, hpower, mul_assoc]
    · have hr2 : r ^ 2 ∉ Ioc 0 (t ^ 2) := fun hmem => hrt ((sq_le_sq₀ hr.le ht).mp hmem.2)
      change (2 * r) * (Ioc 0 (t ^ 2)).indicator f (r ^ 2) = _
      rw [indicator_of_not_mem hr2,
        indicator_of_not_mem (show r ∉ Ioc 0 t from fun hmem => hrt hmem.2), mul_zero, mul_zero]
  calc
    dimensionSigmaSlice d c t = ∫ u : ℝ in Ioc 0 (t ^ 2), f u := hreflect
    _ = ∫ u : ℝ in Ioi 0, g u := hg.symm
    _ = ∫ r : ℝ in Ioi 0, (2 * r) * g (r ^ 2) := hsub.symm
    _ = ∫ r : ℝ in Ioi 0, 2 * (Ioc 0 t).indicator h r :=
      setIntegral_congr_fun measurableSet_Ioi (fun r hr => hpoint r hr)
    _ = 2 * ∫ r : ℝ in Ioc 0 t, h r := by
      rw [integral_const_mul, setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr Ioc_subset_Ioi_self]

end BoundaryDraft
