import BoundaryDraft.DimensionSlice
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.Convex

/-!
# Mellin integration of the actual spatial slice

The slice is the finite squared-proper-time integral in `DimensionSlice`.
The initial-strip calculation uses absolutely convergent double integrals.
The independently proved endpoint bounds then give holomorphy, and the identity
principle extends the actual Mellin integral to the entire parity-dependent
convergence domain. The odd Gamma quotient is simplified before continuation;
the even denominator is handled by the entire reciprocal Gamma function.

The physical sphere factor is restored by `dimensionPhysicalSlice`. Its moments
of orders zero through three are evaluated unconditionally, with a zero third
moment in even dimensions and a strictly negative one in odd dimensions. Action
coefficient normalization and the vertical-reduction mass theorem are separate
consumers of these evaluated integrals.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology

noncomputable section
namespace BoundaryDraft

private theorem integral_weighted_comp_mul (f : ℝ → ℝ) (r : ℝ)
    {u : ℝ} (hu : 0 < u) :
    (∫ w : ℝ in Ioi 0, w ^ r * f (u * w)) =
      u ^ (-(r + 1)) * ∫ w : ℝ in Ioi 0, w ^ r * f w := by
  have hs := integral_comp_mul_left_Ioi (fun w : ℝ => w ^ r * f w) 0 hu
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (∫ w : ℝ in Ioi 0, (u * w) ^ r * f (u * w)) =
      u ^ r * ∫ w : ℝ in Ioi 0, w ^ r * f (u * w) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    dsimp only
    rw [Real.mul_rpow hu.le hw.le, mul_assoc]
  rw [he] at hs
  have hp : u ^ (-r) * u ^ r = 1 := by
    rw [← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
  calc
    _ = u ^ (-r) * (u ^ r * ∫ w : ℝ in Ioi 0, w ^ r * f (u * w)) := by
      rw [← mul_assoc, hp, one_mul]
    _ = u ^ (-r) * (u⁻¹ * ∫ w : ℝ in Ioi 0, w ^ r * f w) := by rw [hs]
    _ = _ := by
      rw [← Real.rpow_neg_one u, ← mul_assoc, ← Real.rpow_add hu]
      congr 2
      ring

private theorem integrable_weighted_comp_mul {f : ℝ → ℝ} {r : ℝ}
    (hf : IntegrableOn (fun w : ℝ => w ^ r * f w) (Ioi 0))
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun w : ℝ => w ^ r * f (u * w)) (Ioi 0) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff
    (fun w : ℝ => w ^ r * f w) 0 hu).mpr (by simpa using hf)
  apply (hi.const_mul (u ^ (-r))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [Real.mul_rpow hu.le hw.le]
  have hp : u ^ (-r) * u ^ r = 1 := by
    rw [← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
  rw [← mul_assoc, ← mul_assoc, hp, one_mul]

private theorem beta_integrand_ofReal (a b u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1) =
      ((u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu.1,
    Complex.ofReal_cpow (sub_nonneg.mpr hu.2)]
  push_cast
  rfl

private theorem integrable_beta_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * (1 - u) ^ (b - 1)) (Ioo 0 1) := by
  have hi := ((Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ)) ha hb).1.re)
  apply (IntegrableOn.mono_set hi Ioo_subset_Ioc_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [beta_integrand_ofReal a b u ⟨hu.1.le, hu.2.le⟩]
  rfl

private theorem integral_beta_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u : ℝ in Ioo 0 1, u ^ (a - 1) * (1 - u) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have he : Complex.betaIntegral (a : ℂ) (b : ℂ) =
      (((∫ u : ℝ in Ioo 0 1, u ^ (a - 1) * (1 - u) ^ (b - 1)) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioo
      (fun u hu => beta_integrand_ofReal a b u ⟨hu.1.le, hu.2.le⟩)
  have hg := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (a : ℂ)) (t := (b : ℂ)) ha hb
  rw [he, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at hg
  have hr := Complex.ofReal_injective hg
  exact (eq_div_iff (ne_of_gt (Real.Gamma_pos_of_pos (add_pos ha hb)))).mpr
    (by simpa only [mul_comm] using hr.symm)

private theorem integrable_mellin_slice_product {f : ℝ → ℝ}
    (hm : Measurable f) {p r : ℝ} (hp : -1 < p) (hr : r < 0)
    (hf : IntegrableOn (fun w : ℝ => w ^ r * f w) (Ioi 0)) :
    Integrable (fun x : ℝ × ℝ =>
      (1 - x.1) ^ p * (x.2 ^ r * f (x.1 * x.2)))
      ((volume.restrict (Ioo 0 1)).prod (volume.restrict (Ioi 0))) := by
  have hm' : Measurable (fun x : ℝ × ℝ =>
      (1 - x.1) ^ p * (x.2 ^ r * f (x.1 * x.2))) :=
    ((measurable_const.sub measurable_fst).pow_const p).mul
      ((measurable_snd.pow_const r).mul (hm.comp (measurable_fst.mul measurable_snd)))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (integrable_weighted_comp_mul hf hu.1).const_mul _
  · have hb := (integrable_beta_rpow (a := -r) (b := p + 1)
      (by linarith) (by linarith)).mul_const
        (∫ w : ℝ in Ioi 0, w ^ r * ‖f w‖)
    apply hb.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hw : ∀ w ∈ Ioi (0 : ℝ),
        ‖(1 - u) ^ p * (w ^ r * f (u * w))‖ =
          (1 - u) ^ p * (w ^ r * ‖f (u * w)‖) := by
      intro w hw
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) _),
        abs_of_pos (Real.rpow_pos_of_pos hw _)]
    rw [setIntegral_congr_fun measurableSet_Ioi hw, integral_const_mul,
      integral_weighted_comp_mul (fun w => ‖f w‖) r hu.1]
    simp only [add_sub_cancel_right]
    rw [show -r - 1 = -(r + 1) by ring]
    ring

private theorem integral_mellin_slice_product {f : ℝ → ℝ}
    (hm : Measurable f) {p r : ℝ} (hp : -1 < p) (hr : r < 0)
    (hf : IntegrableOn (fun w : ℝ => w ^ r * f w) (Ioi 0)) :
    (∫ w : ℝ in Ioi 0, ∫ u : ℝ in Ioo 0 1,
      (1 - u) ^ p * (w ^ r * f (u * w))) =
        (Real.Gamma (-r) * Real.Gamma (p + 1) / Real.Gamma (p + 1 - r)) *
          ∫ w : ℝ in Ioi 0, w ^ r * f w := by
  rw [← integral_integral_swap (integrable_mellin_slice_product hm hp hr hf)]
  calc
    _ = ∫ u : ℝ in Ioo 0 1,
        (u ^ (-r - 1) * (1 - u) ^ p) * ∫ w : ℝ in Ioi 0, w ^ r * f w := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [integral_const_mul, integral_weighted_comp_mul f r hu.1]
      rw [show -r - 1 = -(r + 1) by ring]
      ring
    _ = _ := by
      rw [integral_mul_const]
      have hb := integral_beta_rpow (a := -r) (b := p + 1) (by linarith) (by linarith)
      simp only [add_sub_cancel_right] at hb
      rw [hb, show -r + (p + 1) = p + 1 - r by ring]

private theorem slice_fibre_rescale (f : ℝ → ℝ) (p : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ σ : ℝ in Ioc 0 w, (w - σ) ^ p * f σ) =
      w ^ (p + 1) * ∫ u : ℝ in Ioo 0 1, (1 - u) ^ p * f (w * u) := by
  have hs := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun σ : ℝ => (w - σ) ^ p * f σ) hw.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hw.le] at hs
  have he : (∫ u : ℝ in Ioo 0 1, (w - w * u) ^ p * f (w * u)) =
      w ^ p * ∫ u : ℝ in Ioo 0 1, (1 - u) ^ p * f (w * u) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp only
    rw [show w - w * u = w * (1 - u) by ring,
      Real.mul_rpow hw.le (sub_pos.mpr hu.2).le, mul_assoc]
  calc
    _ = w * ∫ u : ℝ in Ioo 0 1, (w - w * u) ^ p * f (w * u) := by
      rw [hs, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
    _ = _ := by
      rw [he, Real.rpow_add hw, Real.rpow_one]
      ring

private theorem weighted_slice_fibre_rescale (f : ℝ → ℝ) (p a : ℝ)
    {w : ℝ} (hw : 0 < w) :
    w ^ (a - 1) * (∫ σ : ℝ in Ioc 0 w, (w - σ) ^ p * f σ) =
      ∫ u : ℝ in Ioo 0 1, (1 - u) ^ p * (w ^ (a + p) * f (u * w)) := by
  rw [slice_fibre_rescale f p hw, ← mul_assoc, ← Real.rpow_add hw,
    show a - 1 + (p + 1) = a + p by ring, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  dsimp only
  rw [mul_comm u w]
  ring

private theorem mellin_square_weight (s t : ℝ) (ht : 0 < t) :
    t ^ ((2 : ℝ) - 1) * (t ^ (2 : ℝ)) ^ (s / 2 - 1) = t ^ (s - 1) := by
  rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  ring

private theorem mellin_square_convolution {f : ℝ → ℝ} (hm : Measurable f)
    {p s : ℝ} (hp : -1 < p) (hr : s / 2 + p < 0)
    (hf : IntegrableOn (fun w : ℝ => w ^ (s / 2 + p) * f w) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) *
      ∫ σ : ℝ in Ioc 0 (t ^ 2), (t ^ 2 - σ) ^ p * f σ) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) *
      ∫ σ : ℝ in Ioc 0 (t ^ 2), (t ^ 2 - σ) ^ p * f σ) =
      (1 / 2 : ℝ) *
        (Real.Gamma (-(s / 2 + p)) * Real.Gamma (p + 1) /
          Real.Gamma (1 - s / 2)) *
        ∫ w : ℝ in Ioi 0, w ^ (s / 2 + p) * f w := by
  let g : ℝ → ℝ := fun w => w ^ (s / 2 - 1) *
    ∫ σ : ℝ in Ioc 0 w, (w - σ) ^ p * f σ
  have hi : IntegrableOn g (Ioi 0) := by
    apply (integrable_mellin_slice_product hm hp hr hf).integral_prod_right.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact (weighted_slice_fibre_rescale f p (s / 2) hw).symm
  have hv : (∫ w : ℝ in Ioi 0, g w) =
      (Real.Gamma (-(s / 2 + p)) * Real.Gamma (p + 1) /
        Real.Gamma (1 - s / 2)) *
        ∫ w : ℝ in Ioi 0, w ^ (s / 2 + p) * f w := by
    calc
      _ = ∫ w : ℝ in Ioi 0, ∫ u : ℝ in Ioo 0 1,
          (1 - u) ^ p * (w ^ (s / 2 + p) * f (u * w)) :=
        setIntegral_congr_fun measurableSet_Ioi
          (fun w hw => weighted_slice_fibre_rescale f p (s / 2) hw)
      _ = _ := by
        rw [integral_mellin_slice_product hm hp hr hf,
          show p + 1 - (s / 2 + p) = 1 - s / 2 by ring]
  have he (t : ℝ) (ht : 0 < t) :
      t ^ ((2 : ℝ) - 1) * g (t ^ (2 : ℝ)) =
        t ^ (s - 1) * ∫ σ : ℝ in Ioc 0 (t ^ 2), (t ^ 2 - σ) ^ p * f σ := by
    dsimp only [g]
    rw [← mul_assoc, mellin_square_weight s t ht, Real.rpow_two]
  constructor
  · apply ((integrableOn_Ioi_comp_rpow_iff' g (by norm_num : (2 : ℝ) ≠ 0)).mpr hi).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact he t ht
  · have hs := integral_comp_rpow_Ioi_of_pos (g := g) (by norm_num : (0 : ℝ) < 2)
    have he' : (∫ t : ℝ in Ioi 0, ((2 : ℝ) * t ^ ((2 : ℝ) - 1)) • g (t ^ (2 : ℝ))) =
        2 * ∫ t : ℝ in Ioi 0, t ^ (s - 1) *
          ∫ σ : ℝ in Ioc 0 (t ^ 2), (t ^ 2 - σ) ^ p * f σ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, mul_assoc, he t ht]
    rw [he', hv] at hs
    linarith

/-- Absolute convergence of the actual integrated slice in the initial strip.
This precedes the use of any signed transverse cancellation or tail estimate. -/
theorem integrableOn_dimensionSigmaSlice_mellin_initial (d : ℕ) (hd : 2 ≤ d)
    {c s : ℝ} (hc : 0 < c) (hlo : 1 - (d : ℝ) < s) (hhi : s < 3 - (d : ℝ)) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * dimensionSigmaSlice d c t) (Ioi 0) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact (mellin_square_convolution
    ((continuous_dimensionKernel d).measurable.comp
      (measurable_const.mul (measurable_id.pow_const ((d : ℝ) / 2))))
    (p := ((d : ℝ) - 3) / 2) (s := s) (by linarith) (by linarith)
    (integrableOn_dimensionKernel_density_rpow d (by linarith) (by linarith) hc)).1

/-- The unsimplified Beta/Mellin identity, obtained by absolute Fubini for the
independently defined finite spatial slice. All Gamma arguments in this formula
are positive on this strip. -/
theorem integral_dimensionSigmaSlice_mellin_initial_beta (d : ℕ) (hd : 2 ≤ d)
    {c s : ℝ} (hc : 0 < c) (hlo : 1 - (d : ℝ) < s) (hhi : s < 3 - (d : ℝ)) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice d c t) =
      (1 / (d : ℝ)) * c ^ (-(s + d - 1) / d) *
        Real.Gamma ((s + d - 1) / d) *
        Real.Gamma ((3 - d - s) / 2) * Real.Gamma (((d : ℝ) - 1) / 2) /
        Real.Gamma (1 - s / 2) *
        dimensionMellinFactor d (dimensionFactorCount d) ((s + d - 1) / d) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h := (mellin_square_convolution
    ((continuous_dimensionKernel d).measurable.comp
      (measurable_const.mul (measurable_id.pow_const ((d : ℝ) / 2))))
    (p := ((d : ℝ) - 3) / 2) (s := s) (by linarith) (by linarith)
    (integrableOn_dimensionKernel_density_rpow d (by linarith) (by linarith) hc)).2
  dsimp only [Function.comp_def, id_eq] at h
  rw [integral_dimensionKernel_density_rpow d (by linarith) (by linarith) hc] at h
  have h1 : (s / 2 + ((d : ℝ) - 3) / 2 + 1) / ((d : ℝ) / 2) =
      (s + d - 1) / d := by ring
  have h2 : -(s / 2 + ((d : ℝ) - 3) / 2 + 1) / ((d : ℝ) / 2) =
      -(s + d - 1) / d := by ring
  rw [h1, h2, show -(s / 2 + ((d : ℝ) - 3) / 2) = (3 - d - s) / 2 by ring,
    show ((d : ℝ) - 3) / 2 + 1 = ((d : ℝ) - 1) / 2 by ring] at h
  change (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice d c t) = _ at h
  rw [h]
  ring

private theorem gamma_mul_descending_product (m : ℕ) {x : ℝ} (hx : x < 1) :
    Real.Gamma (1 - x) * (∏ i ∈ Finset.range m, (1 - x / (i + 1))) =
      Real.Gamma ((m : ℝ) + 1 - x) / (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    have hp : 0 < (m : ℝ) + 1 - x := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [Nat.cast_succ, show (m : ℝ) + 1 + 1 - x = ((m : ℝ) + 1 - x) + 1 by ring,
      Real.Gamma_add_one hp.ne', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm' : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Simplification of the apparent Beta poles is performed inside the genuine
initial convergence strip, where the Gamma recurrence has no zero argument. -/
theorem integral_dimensionSigmaSlice_mellin_initial (d : ℕ) (hd : 2 ≤ d)
    {c s : ℝ} (hc : 0 < c) (hlo : 1 - (d : ℝ) < s) (hhi : s < 3 - (d : ℝ)) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice d c t) =
      Real.Gamma (((d : ℝ) - 1) / 2) / ((d : ℝ) * (dimensionFactorCount d).factorial) *
        c ^ (-(s + d - 1) / d) * Real.Gamma ((s + d - 1) / d) *
        Real.Gamma ((dimensionFactorCount d : ℝ) + 1 - (s + d - 1) / 2) /
        Real.Gamma (1 - s / 2) := by
  have hd0 : 0 < d := by omega
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd0)
  have hm : dimensionMellinFactor d (dimensionFactorCount d) ((s + d - 1) / d) =
      ∏ i ∈ Finset.range (dimensionFactorCount d), (1 - ((s + d - 1) / 2) / (i + 1)) := by
    unfold dimensionMellinFactor
    apply Finset.prod_congr rfl
    intro i _
    have hi : (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hg := gamma_mul_descending_product (dimensionFactorCount d)
    (x := (s + d - 1) / 2) (by linarith)
  rw [show 1 - (s + (d : ℝ) - 1) / 2 = (3 - d - s) / 2 by ring] at hg
  rw [integral_dimensionSigmaSlice_mellin_initial_beta d hd hc hlo hhi, hm]
  calc
    _ = ((1 / (d : ℝ)) * c ^ (-(s + d - 1) / d) * Real.Gamma ((s + d - 1) / d) *
        Real.Gamma (((d : ℝ) - 1) / 2) / Real.Gamma (1 - s / 2)) *
        (Real.Gamma ((3 - d - s) / 2) *
          ∏ i ∈ Finset.range (dimensionFactorCount d), (1 - ((s + d - 1) / 2) / (i + 1))) := by ring
    _ = _ := by rw [hg]; ring

/-- The physical spatial slice, including exactly half the sphere-area factor.
Its definition retains the independently defined finite slice integral. -/
def dimensionPhysicalSlice (d : ℕ) (c t : ℝ) : ℝ :=
  Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2) *
    dimensionSigmaSlice d c t

/-- The real initial-strip Mellin identity for the normalized physical slice. -/
theorem integral_dimensionPhysicalSlice_mellin_initial (d : ℕ) (hd : 2 ≤ d)
    {c s : ℝ} (hc : 0 < c) (hlo : 1 - (d : ℝ) < s) (hhi : s < 3 - (d : ℝ)) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionPhysicalSlice d c t) =
      Real.pi ^ (((d : ℝ) - 1) / 2) / ((d : ℝ) * (dimensionFactorCount d).factorial) *
        c ^ (-(s + d - 1) / d) * Real.Gamma ((s + d - 1) / d) *
        Real.Gamma ((dimensionFactorCount d : ℝ) + 1 - (s + d - 1) / 2) /
        Real.Gamma (1 - s / 2) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : Real.Gamma (((d : ℝ) - 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  calc
    _ = (Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2)) *
        ∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice d c t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only [dimensionPhysicalSlice]
      ring
    _ = _ := by
      rw [integral_dimensionSigmaSlice_mellin_initial d hd hc hlo hhi]
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        _ = (Real.Gamma (((d : ℝ) - 1) / 2) *
            (Real.Gamma (((d : ℝ) - 1) / 2))⁻¹) *
            (Real.pi ^ (((d : ℝ) - 1) / 2) *
              ((dimensionFactorCount d).factorial : ℝ)⁻¹ * (d : ℝ)⁻¹ *
              c ^ (-(s + d - 1) / d) * Real.Gamma ((s + d - 1) / d) *
              Real.Gamma ((dimensionFactorCount d : ℝ) + 1 - (s + d - 1) / 2) *
              (Real.Gamma (1 - s / 2))⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hg, one_mul]; ring

private theorem mellin_ofReal (f : ℝ → ℝ) (s : ℝ) :
    mellin (fun t => (f t : ℂ)) (s : ℂ) =
      (((∫ t : ℝ in Ioi 0, t ^ (s - 1) * f t) : ℝ) : ℂ) := by
  rw [mellin, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
  push_cast
  rfl

private theorem sigma_slice_locally_integrable (d : ℕ) (hd : 2 ≤ d) (c : ℝ) :
    LocallyIntegrableOn (fun t => (dimensionSigmaSlice d c t : ℂ)) (Ioi 0) := by
  intro t ht
  refine ⟨Ioc 0 (t + 1), nhdsWithin_le_nhds (Ioc_mem_nhds ht (by linarith)), ?_⟩
  simpa only [pow_zero, one_mul] using
    (integrableOn_dimensionSigmaSlice_moment_local d hd c (t + 1) 0).ofReal

private theorem sigma_slice_origin_bound (d : ℕ) (hd : 2 ≤ d) (c : ℝ) :
    (fun t => (dimensionSigmaSlice d c t : ℂ)) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(1 - (d : ℝ)))) := by
  obtain ⟨C, _, hC⟩ := dimensionSigmaSlice_local_bound d hd c 1
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht1
  have he : -(1 - (d : ℝ)) = ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  rw [Complex.norm_real, Real.norm_eq_abs, he, Real.rpow_natCast,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (show 0 ≤ t from ht.le) (d - 1))]
  exact hC t ⟨ht.le, ht1.le⟩

private theorem sigma_slice_odd_exp_bound (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (fun t => (dimensionSigmaSlice (2 * n + 3) c t : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-(c / 2) * t)) := by
  obtain ⟨C, hC0, hC⟩ := dimensionSigmaSlice_odd_exp_bound n hc
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hC t (le_trans zero_le_one ht)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC0.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (le_self_pow₀ ht (by omega : 2 * n + 3 ≠ 0))
    (by linarith)

private theorem differentiableAt_Gamma_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have h := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at h
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private theorem identity_from_real_interval {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {a b x : ℝ} (hax : a < x) (hxb : x < b) (hxU : (x : ℂ) ∈ U)
    (he : ∀ y ∈ Ioo a b, f (y : ℂ) = g (y : ℂ)) : EqOn f g U := by
  have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr
        (Eventually.of_forall fun t ht => Complex.ofReal_injective.ne_iff.mpr ht)
  apply (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hU) hconn hxU
  apply ht.frequently
  apply (Eventually.filter_mono nhdsWithin_le_nhds _).frequently
  filter_upwards [eventually_gt_nhds hax, eventually_lt_nhds hxb] with y hay hyb
  exact he y ⟨hay, hyb⟩

private theorem sigma_slice_odd_initial (n : ℕ) {c s : ℝ} (hc : 0 < c)
    (hlo : 1 - ((2 * n + 3 : ℕ) : ℝ) < s)
    (hhi : s < 3 - ((2 * n + 3 : ℕ) : ℝ)) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice (2 * n + 3) c t) =
      Real.Gamma (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
        Real.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2) := by
  rw [integral_dimensionSigmaSlice_mellin_initial (2 * n + 3) (by omega) hc hlo hhi]
  have hm : dimensionFactorCount (2 * n + 3) = n + 2 := by
    unfold dimensionFactorCount
    omega
  rw [hm]
  have he : (((2 * n + 3 : ℕ) : ℝ) - 1) / 2 = (n : ℝ) + 1 := by push_cast; ring
  have he' : ((n + 2 : ℕ) : ℝ) + 1 - (s + (2 * n + 3 : ℕ) - 1) / 2 =
      (1 - s / 2) + 1 := by push_cast; ring
  have hs : 0 < 1 - s / 2 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at hhi
    linarith
  have hg := (Real.Gamma_pos_of_pos hs).ne'
  rw [he, he', Real.Gamma_add_one hs.ne']
  rw [← mul_assoc, mul_div_cancel_right₀ _ hg]

private def sigmaSliceOddMellin (n : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  ((Real.Gamma (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) : ℝ) : ℂ) *
    (c : ℂ) ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
    Complex.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2)

private theorem sigmaSliceOddMellin_ofReal (n : ℕ) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    sigmaSliceOddMellin n c (s : ℂ) =
      ((Real.Gamma (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
        Real.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2) : ℝ) : ℂ) := by
  unfold sigmaSliceOddMellin
  rw [show -( (s : ℂ) + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) =
      ((-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
    show ((s : ℂ) + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) =
      (((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hc.le, Complex.Gamma_ofReal]
  push_cast
  rfl

private theorem differentiableOn_sigmaSliceOddMellin (n : ℕ) {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (sigmaSliceOddMellin n c)
      {s : ℂ | 1 - ((2 * n + 3 : ℕ) : ℝ) < s.re} := by
  intro s hs
  have hd : (0 : ℝ) < (2 * n + 3 : ℕ) := by positivity
  have ha : 0 < ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) : ℂ).re := by
    have he : ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) : ℂ).re =
        (s.re + ((2 * n + 3 : ℕ) : ℝ) - 1) / (2 * n + 3 : ℕ) := by
      simp only [Complex.div_natCast_re, Complex.add_re, Complex.sub_re,
        Complex.natCast_re, Complex.one_re]
    rw [he]
    exact div_pos (by change 1 - ((2 * n + 3 : ℕ) : ℝ) < s.re at hs; linarith) hd
  have hG := (differentiableAt_Gamma_pos ha).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (z + (2 * n + 3 : ℕ) - 1) /
      (2 * n + 3 : ℕ)) s by fun_prop)
  have hP : DifferentiableAt ℂ (fun z : ℂ => (c : ℂ) ^
      (-(z + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ))) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  exact (((differentiableAt_const _).mul hP).mul hG |>.mul
    (show DifferentiableAt ℂ (fun z : ℂ => 1 - z / 2) s by fun_prop)).differentiableWithinAt

/-- Odd-dimensional continuation is an identity of absolutely convergent Mellin
integrals on the full half-plane. The Gamma quotient has already been replaced
by its polynomial value, so no Gamma pole is evaluated. -/
theorem hasMellin_dimensionSigmaSlice_odd (n : ℕ) {c : ℝ} (hc : 0 < c)
    {s : ℂ} (hs : 1 - ((2 * n + 3 : ℕ) : ℝ) < s.re) :
    HasMellin (fun t => (dimensionSigmaSlice (2 * n + 3) c t : ℂ)) s
      (((Real.Gamma (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) : ℝ) : ℂ) *
        (c : ℂ) ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
        Complex.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2)) := by
  have hloc := sigma_slice_locally_integrable (2 * n + 3) (by omega) c
  have htop := sigma_slice_odd_exp_bound n hc
  have hbot := sigma_slice_origin_bound (2 * n + 3) (by omega) c
  refine ⟨mellinConvergent_of_isBigO_rpow_exp (half_pos hc) hloc htop hbot hs, ?_⟩
  let U : Set ℂ := {z : ℂ | 1 - ((2 * n + 3 : ℕ) : ℝ) < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hf : DifferentiableOn ℂ (mellin (fun t =>
      (dimensionSigmaSlice (2 * n + 3) c t : ℂ))) U := by
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow_exp (half_pos hc) hloc htop hbot hz).differentiableWithinAt
  have he := identity_from_real_interval hU hconn hf
    (differentiableOn_sigmaSliceOddMellin n hc)
    (a := 1 - ((2 * n + 3 : ℕ) : ℝ)) (b := 3 - ((2 * n + 3 : ℕ) : ℝ))
    (x := 2 - ((2 * n + 3 : ℕ) : ℝ)) (by linarith) (by linarith)
    (by dsimp [U]; linarith) ?_
  · exact he hs
  · intro y hy
    rw [mellin_ofReal, sigma_slice_odd_initial n hc hy.1 hy.2,
      sigmaSliceOddMellin_ofReal n hc]

/-- All real Mellin orders of the actual odd slice above its origin threshold,
including every natural moment. This is not the unsimplified Gamma quotient. -/
theorem integral_dimensionSigmaSlice_mellin_odd (n : ℕ) {c s : ℝ} (hc : 0 < c)
    (hs : 1 - ((2 * n + 3 : ℕ) : ℝ) < s) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice (2 * n + 3) c t) =
      Real.Gamma (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
        Real.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2) := by
  have h := (hasMellin_dimensionSigmaSlice_odd n hc (s := (s : ℂ)) hs).2
  change mellin _ _ = sigmaSliceOddMellin n c (s : ℂ) at h
  rw [mellin_ofReal, sigmaSliceOddMellin_ofReal n hc] at h
  exact Complex.ofReal_injective h

/-- Factoring the sphere coefficient out of any actual weighted slice integral. -/
theorem integral_dimensionPhysicalSlice_weight (d : ℕ) (c : ℝ) (w : ℝ → ℝ) :
    (∫ t : ℝ in Ioi 0, w t * dimensionPhysicalSlice d c t) =
      Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2) *
        ∫ t : ℝ in Ioi 0, w t * dimensionSigmaSlice d c t := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [dimensionPhysicalSlice]
  ring

/-- The full real Mellin identity for the physical odd-dimensional slice. -/
theorem integral_dimensionPhysicalSlice_mellin_odd (n : ℕ) {c s : ℝ} (hc : 0 < c)
    (hs : 1 - ((2 * n + 3 : ℕ) : ℝ) < s) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionPhysicalSlice (2 * n + 3) c t) =
      Real.pi ^ (n + 1 : ℕ) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
        Real.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2) := by
  rw [integral_dimensionPhysicalSlice_weight,
    integral_dimensionSigmaSlice_mellin_odd n hc hs]
  have he : (((2 * n + 3 : ℕ) : ℝ) - 1) / 2 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hg : Real.Gamma (n + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [he, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (Real.Gamma (n + 1) * (Real.Gamma (n + 1))⁻¹) *
        (Real.pi ^ (n + 1) * ((n + 2).factorial : ℝ)⁻¹ * ((2 * n + 3 : ℕ) : ℝ)⁻¹ *
          c ^ (-(s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) *
          Real.Gamma ((s + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ)) * (1 - s / 2)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hg, one_mul]; ring

/-- Absolute natural moments of the physical odd slice, independent of their
signed evaluation. -/
theorem integrableOn_dimensionPhysicalSlice_odd_moment (n k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionPhysicalSlice (2 * n + 3) c t) (Ioi 0) := by
  apply ((integrableOn_dimensionSigmaSlice_odd_moment n k hc).const_mul
    (Real.pi ^ ((((2 * n + 3 : ℕ) : ℝ) - 1) / 2) /
      Real.Gamma ((((2 * n + 3 : ℕ) : ℝ) - 1) / 2))).congr
  exact Eventually.of_forall fun t => by dsimp only [dimensionPhysicalSlice]; ring

/-- Every natural odd-dimensional slice moment follows from the convergent
Mellin identity; the fourth and higher moments are allowed as well. -/
theorem integral_dimensionPhysicalSlice_odd_moment (n k : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ k * dimensionPhysicalSlice (2 * n + 3) c t) =
      Real.pi ^ (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-1 - (k : ℝ) / (2 * n + 3 : ℕ)) *
        Real.Gamma (1 + (k : ℝ) / (2 * n + 3 : ℕ)) * (1 - ((k : ℝ) + 1) / 2) := by
  have hd : (0 : ℝ) < (2 * n + 3 : ℕ) := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := integral_dimensionPhysicalSlice_mellin_odd n (s := (k : ℝ) + 1) hc
    (by have : (3 : ℝ) ≤ (2 * n + 3 : ℕ) := by exact_mod_cast (show 3 ≤ 2 * n + 3 by omega)
        linarith)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h]
  have h1 : ((k : ℝ) + 1 + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) =
      1 + (k : ℝ) / (2 * n + 3 : ℕ) := by field_simp; ring
  have h2 : -((k : ℝ) + 1 + (2 * n + 3 : ℕ) - 1) / (2 * n + 3 : ℕ) =
      -1 - (k : ℝ) / (2 * n + 3 : ℕ) := by field_simp; ring
  rw [h1, h2]

/-- The first odd slice moment vanishes, unlike the first height moment of the
vertical reduction. -/
theorem integral_dimensionPhysicalSlice_odd_J1 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t * dimensionPhysicalSlice (2 * n + 3) c t) = 0 := by
  simpa using integral_dimensionPhysicalSlice_odd_moment n 1 hc

/-- The third odd slice moment is nonzero and negative. -/
theorem integral_dimensionPhysicalSlice_odd_J3 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ 3 * dimensionPhysicalSlice (2 * n + 3) c t) =
      -(Real.pi ^ (n + 1) / (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ))) *
        c ^ (-1 - (3 : ℝ) / (2 * n + 3 : ℕ)) * Real.Gamma (1 + 3 / (2 * n + 3 : ℕ)) := by
  rw [integral_dimensionPhysicalSlice_odd_moment n 3 hc]
  norm_num

/-- Odd-dimensional zeroth slice moment at every positive interval coefficient. -/
theorem integral_dimensionPhysicalSlice_odd_J0 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, dimensionPhysicalSlice (2 * n + 3) c t) =
      Real.pi ^ (n + 1) /
        (2 * ((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ) * c) := by
  have h := integral_dimensionPhysicalSlice_odd_moment n 0 hc
  norm_num only [pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero, sub_zero,
    Real.Gamma_one, mul_one, zero_add, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  rw [h, Real.rpow_neg_one]
  ring

/-- Odd-dimensional second slice moment, with its physical sphere factor. -/
theorem integral_dimensionPhysicalSlice_odd_J2 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionPhysicalSlice (2 * n + 3) c t) =
      -(Real.pi ^ (n + 1) /
        (2 * ((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ))) *
        c ^ (-1 - (2 : ℝ) / (2 * n + 3 : ℕ)) * Real.Gamma (1 + 2 / (2 * n + 3 : ℕ)) := by
  rw [integral_dimensionPhysicalSlice_odd_moment n 2 hc]
  norm_num only [Nat.cast_ofNat, show (1 : ℝ) - (2 + 1) / 2 = -(1 / 2) by norm_num]
  ring

private def sigmaSliceEvenMellin (n : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  ((Real.Gamma ((n : ℝ) + 1 / 2) /
      (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) : ℝ) : ℂ) *
    (c : ℂ) ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
    Complex.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
    Complex.Gamma ((5 - s) / 2) * (Complex.Gamma (1 - s / 2))⁻¹

private theorem sigmaSliceEvenMellin_ofReal (n : ℕ) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    sigmaSliceEvenMellin n c (s : ℂ) =
      ((Real.Gamma ((n : ℝ) + 1 / 2) /
          (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((5 - s) / 2) / Real.Gamma (1 - s / 2) : ℝ) : ℂ) := by
  unfold sigmaSliceEvenMellin
  rw [show -((s : ℂ) + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) =
      ((-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
    show ((s : ℂ) + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) =
      (((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
    show (5 - (s : ℂ)) / 2 = (((5 - s) / 2 : ℝ) : ℂ) by push_cast; rfl,
    show 1 - (s : ℂ) / 2 = ((1 - s / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hc.le, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  rfl

private theorem sigma_slice_even_initial (n : ℕ) {c s : ℝ} (hc : 0 < c)
    (hlo : 1 - ((2 * n + 2 : ℕ) : ℝ) < s)
    (hhi : s < 3 - ((2 * n + 2 : ℕ) : ℝ)) :
    mellin (fun t => (dimensionSigmaSlice (2 * n + 2) c t : ℂ)) (s : ℂ) =
      sigmaSliceEvenMellin n c (s : ℂ) := by
  rw [mellin_ofReal, integral_dimensionSigmaSlice_mellin_initial (2 * n + 2)
    (by omega) hc hlo hhi, sigmaSliceEvenMellin_ofReal n hc]
  congr 1
  have hm : dimensionFactorCount (2 * n + 2) = n + 2 := by
    unfold dimensionFactorCount
    omega
  have he : (((2 * n + 2 : ℕ) : ℝ) - 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  have he' : ((n + 2 : ℕ) : ℝ) + 1 - (s + (2 * n + 2 : ℕ) - 1) / 2 =
      (5 - s) / 2 := by push_cast; ring
  rw [hm, he, he']

private theorem differentiableOn_sigmaSliceEvenMellin (n : ℕ) {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (sigmaSliceEvenMellin n c)
      {s : ℂ | 1 - ((2 * n + 2 : ℕ) : ℝ) < s.re ∧ s.re < 5} := by
  intro s hs
  have hd : (0 : ℝ) < (2 * n + 2 : ℕ) := by positivity
  have ha : 0 < ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) : ℂ).re := by
    simp only [Complex.div_natCast_re, Complex.add_re, Complex.sub_re,
      Complex.natCast_re, Complex.one_re]
    exact div_pos (by linarith [hs.1]) hd
  have hb : 0 < ((5 - s) / 2).re := by
    norm_num [Complex.div_ofNat_re, Complex.sub_re]
    linarith [hs.2]
  have hG := (differentiableAt_Gamma_pos ha).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (z + (2 * n + 2 : ℕ) - 1) /
      (2 * n + 2 : ℕ)) s by fun_prop)
  have hB := (differentiableAt_Gamma_pos hb).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (5 - z) / 2) s by fun_prop)
  have hP : DifferentiableAt ℂ (fun z : ℂ => (c : ℂ) ^
      (-(z + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ))) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  have hI := Complex.differentiable_one_div_Gamma.differentiableAt.comp s
    (show DifferentiableAt ℂ (fun z : ℂ => 1 - z / 2) s by fun_prop)
  exact (((((differentiableAt_const _).mul hP).mul hG).mul hB).mul hI).differentiableWithinAt

/-- Once the independently proved even tail estimate is supplied, continuation
identifies the absolutely convergent Mellin integral throughout the even strip.
The only analytic input here is the endpoint bound, not a moment identity. -/
theorem hasMellin_dimensionSigmaSlice_even_of_isBigO (n : ℕ) {c : ℝ} (hc : 0 < c)
    (htop : (fun t => (dimensionSigmaSlice (2 * n + 2) c t : ℂ)) =O[atTop]
      (fun t : ℝ => t ^ (-(5 : ℝ))))
    {s : ℂ} (hlo : 1 - ((2 * n + 2 : ℕ) : ℝ) < s.re) (hhi : s.re < 5) :
    HasMellin (fun t => (dimensionSigmaSlice (2 * n + 2) c t : ℂ)) s
      (((Real.Gamma ((n : ℝ) + 1 / 2) /
          (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) : ℝ) : ℂ) *
        (c : ℂ) ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Complex.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Complex.Gamma ((5 - s) / 2) * (Complex.Gamma (1 - s / 2))⁻¹) := by
  have hloc := sigma_slice_locally_integrable (2 * n + 2) (by omega) c
  have hbot := sigma_slice_origin_bound (2 * n + 2) (by omega) c
  refine ⟨mellinConvergent_of_isBigO_rpow hloc htop hhi hbot hlo, ?_⟩
  let U : Set ℂ := {z : ℂ | 1 - ((2 * n + 2 : ℕ) : ℝ) < z.re ∧ z.re < 5}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hconn : IsPreconnected U :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have hf : DifferentiableOn ℂ (mellin (fun t =>
      (dimensionSigmaSlice (2 * n + 2) c t : ℂ))) U := by
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow hloc htop hz.2 hbot hz.1).differentiableWithinAt
  have he := identity_from_real_interval hU hconn hf
    (differentiableOn_sigmaSliceEvenMellin n hc)
    (a := 1 - ((2 * n + 2 : ℕ) : ℝ)) (b := 3 - ((2 * n + 2 : ℕ) : ℝ))
    (x := 2 - ((2 * n + 2 : ℕ) : ℝ)) (by linarith) (by linarith)
    (by dsimp [U]; constructor <;> push_cast <;> linarith [Nat.cast_nonneg (α := ℝ) n])
    (fun y hy => sigma_slice_even_initial n hc hy.1 hy.2)
  exact he ⟨hlo, hhi⟩

private theorem sigma_slice_even_bound (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (fun t => (dimensionSigmaSlice (2 * n + 2) c t : ℂ)) =O[atTop]
      (fun t : ℝ => t ^ (-(5 : ℝ))) := by
  obtain ⟨C, _, hC⟩ := dimensionSigmaSlice_even_tail_bound n hc
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht (-(5 : ℝ))), Real.rpow_neg ht.le]
  rw [show t ^ (5 : ℝ) = t ^ (5 : ℕ) from Real.rpow_natCast t 5]
  exact (hC t ht).trans_eq (div_eq_mul_inv C (t ^ 5))

/-- The genuine complex Mellin identity of the actual even slice on its entire
strip of absolute convergence. The endpoint estimates are proved in
`DimensionSlice`, not hypotheses of this theorem. -/
theorem hasMellin_dimensionSigmaSlice_even (n : ℕ) {c : ℝ} (hc : 0 < c)
    {s : ℂ} (hlo : 1 - ((2 * n + 2 : ℕ) : ℝ) < s.re) (hhi : s.re < 5) :
    HasMellin (fun t => (dimensionSigmaSlice (2 * n + 2) c t : ℂ)) s
      (((Real.Gamma ((n : ℝ) + 1 / 2) /
          (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) : ℝ) : ℂ) *
        (c : ℂ) ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Complex.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Complex.Gamma ((5 - s) / 2) * (Complex.Gamma (1 - s / 2))⁻¹) :=
  hasMellin_dimensionSigmaSlice_even_of_isBigO n hc (sigma_slice_even_bound n hc) hlo hhi

/-- The actual real even-slice Mellin integral; reciprocal Gamma is harmless
at its zeros, since the numerator Gamma has positive argument in this strip. -/
theorem integral_dimensionSigmaSlice_mellin_even (n : ℕ) {c s : ℝ} (hc : 0 < c)
    (hlo : 1 - ((2 * n + 2 : ℕ) : ℝ) < s) (hhi : s < 5) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionSigmaSlice (2 * n + 2) c t) =
      Real.Gamma ((n : ℝ) + 1 / 2) /
        (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((5 - s) / 2) / Real.Gamma (1 - s / 2) := by
  have h := (hasMellin_dimensionSigmaSlice_even n hc (s := (s : ℂ)) hlo hhi).2
  change mellin _ _ = sigmaSliceEvenMellin n c (s : ℂ) at h
  rw [mellin_ofReal, sigmaSliceEvenMellin_ofReal n hc] at h
  exact Complex.ofReal_injective h

/-- The physical even-dimensional Mellin identity, with its genuine sphere
factor and its full strip of absolute convergence. -/
theorem integral_dimensionPhysicalSlice_mellin_even (n : ℕ) {c s : ℝ} (hc : 0 < c)
    (hlo : 1 - ((2 * n + 2 : ℕ) : ℝ) < s) (hhi : s < 5) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * dimensionPhysicalSlice (2 * n + 2) c t) =
      Real.pi ^ ((n : ℝ) + 1 / 2) /
        (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((5 - s) / 2) / Real.Gamma (1 - s / 2) := by
  rw [integral_dimensionPhysicalSlice_weight,
    integral_dimensionSigmaSlice_mellin_even n hc hlo hhi]
  have he : (((2 * n + 2 : ℕ) : ℝ) - 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  have hg : Real.Gamma ((n : ℝ) + 1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (Real.Gamma ((n : ℝ) + 1 / 2) * (Real.Gamma ((n : ℝ) + 1 / 2))⁻¹) *
        (Real.pi ^ ((n : ℝ) + 1 / 2) * ((n + 2).factorial : ℝ)⁻¹ * ((2 * n + 2 : ℕ) : ℝ)⁻¹ *
          c ^ (-(s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
          Real.Gamma ((s + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ)) *
          Real.Gamma ((5 - s) / 2) * (Real.Gamma (1 - s / 2))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hg, one_mul]; ring

/-- Absolute moments of orders zero through three, for every physical slice. -/
theorem integrableOn_dimensionPhysicalSlice_moment (d k : ℕ) (hd : 2 ≤ d) (hk : k ≤ 3)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionPhysicalSlice d c t) (Ioi 0) := by
  apply ((integrableOn_dimensionSigmaSlice_moment d k hd hk hc).const_mul
    (Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2))).congr
  exact Eventually.of_forall fun t => by dsimp only [dimensionPhysicalSlice]; ring

/-- Evaluation of all four convergent natural moments in even dimensions. -/
theorem integral_dimensionPhysicalSlice_even_moment (n k : ℕ) (hk : k ≤ 3)
    {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ k * dimensionPhysicalSlice (2 * n + 2) c t) =
      Real.pi ^ ((n : ℝ) + 1 / 2) /
        (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) *
        c ^ (-1 - (k : ℝ) / (2 * n + 2 : ℕ)) *
        Real.Gamma (1 + (k : ℝ) / (2 * n + 2 : ℕ)) *
        Real.Gamma ((4 - (k : ℝ)) / 2) / Real.Gamma ((1 - (k : ℝ)) / 2) := by
  have hd : (0 : ℝ) < (2 * n + 2 : ℕ) := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have h := integral_dimensionPhysicalSlice_mellin_even n (s := (k : ℝ) + 1) hc
    (by have : (2 : ℝ) ≤ (2 * n + 2 : ℕ) := by exact_mod_cast (show 2 ≤ 2 * n + 2 by omega)
        linarith) (by linarith)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h]
  have h1 : ((k : ℝ) + 1 + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) =
      1 + (k : ℝ) / (2 * n + 2 : ℕ) := by field_simp; ring
  have h2 : -((k : ℝ) + 1 + (2 * n + 2 : ℕ) - 1) / (2 * n + 2 : ℕ) =
      -1 - (k : ℝ) / (2 * n + 2 : ℕ) := by field_simp; ring
  rw [h1, h2, show (5 - ((k : ℝ) + 1)) / 2 = (4 - (k : ℝ)) / 2 by ring,
    show 1 - ((k : ℝ) + 1) / 2 = (1 - (k : ℝ)) / 2 by ring]

/-- Zeroth even slice moment, including dimension two. -/
theorem integral_dimensionPhysicalSlice_even_J0 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, dimensionPhysicalSlice (2 * n + 2) c t) =
      Real.pi ^ n / (((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ) * c) := by
  have h := integral_dimensionPhysicalSlice_even_moment n 0 (by omega) hc
  norm_num only [pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero, sub_zero,
    Real.Gamma_one, mul_one, zero_add,
    show (4 : ℝ) / 2 = 2 by norm_num, Real.Gamma_two, Real.Gamma_one_half_eq] at h
  rw [h, Real.rpow_neg_one, Real.rpow_add Real.pi_pos, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow]
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- The first even slice moment is zero. The denominator is the entire
reciprocal Gamma factor obtained in the continuation, not a divergent integral. -/
theorem integral_dimensionPhysicalSlice_even_J1 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t * dimensionPhysicalSlice (2 * n + 2) c t) = 0 := by
  simpa using integral_dimensionPhysicalSlice_even_moment n 1 (by omega) hc

private theorem gamma_neg_half : Real.Gamma (-(1 / 2)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := -(1 / 2)) (by norm_num)
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.Gamma_one_half_eq] at h
  linarith

/-- Second even slice moment with its nonzero signed value. -/
theorem integral_dimensionPhysicalSlice_even_J2 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionPhysicalSlice (2 * n + 2) c t) =
      -(Real.pi ^ n / (2 * ((2 * n + 2 : ℕ) : ℝ) * ((n + 2).factorial : ℝ))) *
        c ^ (-1 - (2 : ℝ) / (2 * n + 2 : ℕ)) * Real.Gamma (1 + 2 / (2 * n + 2 : ℕ)) := by
  rw [integral_dimensionPhysicalSlice_even_moment n 2 (by omega) hc]
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 2) / 2 = 1 by norm_num,
    show ((1 : ℝ) - 2) / 2 = -(1 / 2) by norm_num, Real.Gamma_one, mul_one, gamma_neg_half]
  rw [Real.rpow_add Real.pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- The third even slice moment vanishes; it does not vanish in odd dimensions. -/
theorem integral_dimensionPhysicalSlice_even_J3 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ 3 * dimensionPhysicalSlice (2 * n + 2) c t) = 0 := by
  have h := integral_dimensionPhysicalSlice_even_moment n 3 (by omega) hc
  have hg : Real.Gamma (-1) = 0 := by simpa using Real.Gamma_neg_nat_eq_zero 1
  norm_num only [Nat.cast_ofNat, show ((1 : ℝ) - 3) / 2 = -1 by norm_num,
    hg, div_zero] at h
  exact h

/-- Every supported dimension has a zero first spatial-slice moment. -/
theorem integral_dimensionPhysicalSlice_J1 (d : ℕ) (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t * dimensionPhysicalSlice d c t) = 0 := by
  rcases Nat.even_or_odd d with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · cases n with
    | zero => omega
    | succ n =>
      rw [show (n + 1) + (n + 1) = 2 * n + 2 by omega]
      exact integral_dimensionPhysicalSlice_even_J1 n hc
  · cases n with
    | zero => omega
    | succ n =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
      exact integral_dimensionPhysicalSlice_odd_J1 n hc

/-- The parity obstruction is a strict inequality for the actual integral. -/
theorem integral_dimensionPhysicalSlice_odd_J3_neg (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ 3 * dimensionPhysicalSlice (2 * n + 3) c t) < 0 := by
  rw [integral_dimensionPhysicalSlice_odd_J3 n hc]
  have hA : 0 < Real.pi ^ (n + 1) /
      (((2 * n + 3 : ℕ) : ℝ) * ((n + 2).factorial : ℝ)) := by positivity
  have hP := Real.rpow_pos_of_pos hc (-1 - (3 : ℝ) / (2 * n + 3 : ℕ))
  have hG : 0 < Real.Gamma (1 + (3 : ℝ) / (2 * n + 3 : ℕ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hA) hP) hG

end BoundaryDraft
