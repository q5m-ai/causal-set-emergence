import BoundaryDraft.DimensionLorentz
import BoundaryDraft.DimensionSpacetime
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Actual Alexandrov interval volume in every integer physical dimension ≥ 2

First integrate Euclidean balls of radius `min t (H-t)` in the rest frame.
The published Gamma coefficient is then identified using the already proved
sphere normalization. The explicit Lorentz frame transports arbitrary timelike
endpoints. Null intervals are handled separately, never by a singular boost.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft

variable {n : ℕ}

theorem dimensionCausalInterval_subset_compact (x y : DimensionSpacetime n) :
    dimensionCausalInterval x y ⊆ Icc x.1 y.1 ×ˢ Metric.closedBall x.2 (y.1 - x.1) := by
  intro z hz
  have h₁ : ‖z.2 - x.2‖ ≤ z.1 - x.1 := hz.1
  have h₂ : ‖y.2 - z.2‖ ≤ y.1 - z.1 := hz.2
  have ht : x.1 ≤ z.1 ∧ z.1 ≤ y.1 := by
    constructor <;> nlinarith [norm_nonneg (z.2 - x.2), norm_nonneg (y.2 - z.2)]
  exact ⟨ht, by rw [Metric.mem_closedBall, dist_eq_norm]; linarith [ht.2]⟩

theorem volume_dimensionCausalInterval_lt_top (x y : DimensionSpacetime n) :
    volume (dimensionCausalInterval x y) < ∞ :=
  lt_of_le_of_lt (measure_mono (dimensionCausalInterval_subset_compact x y))
    (isCompact_Icc.prod (isCompact_closedBall _ _)).measure_lt_top

private theorem dimensionBall_integral_one (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R) :
    (∫ _z : DimensionSpatial n in Metric.closedBall 0 R, (1 : ℝ)) =
      dimensionRadialFactor n / n * R ^ n := by
  rw [integral_dimensionSpatial_radial n hn R hR (fun _ => 1)]
  simp only [mul_one, integral_pow, Nat.sub_add_cancel hn,
    zero_pow (by omega : n ≠ 0), sub_zero]
  have hc : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  rw [hc]
  ring

private theorem integral_min_pow (n : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∫ t in (0 : ℝ)..H, min t (H - t) ^ n) =
      2 * (H / 2) ^ (n + 1) / (n + 1) := by
  have hc : Continuous (fun t : ℝ => min t (H - t) ^ n) :=
    (continuous_id.min (continuous_const.sub continuous_id)).pow n
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (H / 2)) (hc.intervalIntegrable (H / 2) H)]
  have hfirst : (∫ t in (0 : ℝ)..H / 2, min t (H - t) ^ n) =
      ∫ t in (0 : ℝ)..H / 2, t ^ n := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ H / 2)] at ht
    dsimp only
    rw [min_eq_left (by linarith [ht.2])]
  have hlast : (∫ t in (H / 2)..H, min t (H - t) ^ n) =
      ∫ t in (0 : ℝ)..H / 2, t ^ n := by
    calc
      _ = ∫ t in (H / 2)..H, (H - t) ^ n := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : H / 2 ≤ H)] at ht
        dsimp only
        rw [min_eq_right (by linarith [ht.1])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) H]
        congr 1 <;> ring
  rw [hfirst, hlast, integral_pow]
  simp only [zero_pow (by omega : n + 1 ≠ 0), sub_zero]
  ring

/-- Rest-frame volume, computed from the actual product measure. -/
theorem volume_dimensionStandardInterval_real (n : ℕ) (hn : 0 < n) (H : ℝ) (hH : 0 ≤ H) :
    (volume (dimensionCausalInterval (0 : DimensionSpacetime n) (H, 0))).toReal =
      dimensionIntervalCoefficient (n + 1) * H ^ (n + 1) := by
  let I := dimensionCausalInterval (0 : DimensionSpacetime n) (H, 0)
  have hm : MeasurableSet I := measurableSet_dimensionCausalInterval _ _
  have hi : IntegrableOn (fun _ : DimensionSpacetime n => (1 : ℝ)) I :=
    (continuous_const.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_closedBall (0 : DimensionSpatial n) H))).mono_set
        (by simpa only [Prod.fst_zero, Prod.snd_zero, sub_zero] using
          dimensionCausalInterval_subset_compact (0 : DimensionSpacetime n) (H, 0))
  have hprod := (integrable_indicator_iff hm).mpr hi
  rw [Measure.volume_eq_prod] at hprod
  have hv : (volume I).toReal = ∫ p in I, (1 : ℝ) := by simp [Measure.real]
  rw [hv, ← integral_indicator hm, Measure.volume_eq_prod, integral_prod _ hprod]
  have hf (t : ℝ) : (∫ z : DimensionSpatial n, I.indicator (fun _ => (1 : ℝ)) (t, z)) =
      (Icc 0 H).indicator (fun t => dimensionRadialFactor n / n * min t (H - t) ^ n) t := by
    by_cases ht : t ∈ Icc 0 H
    · have he (z : DimensionSpatial n) : I.indicator (fun _ => (1 : ℝ)) (t, z) =
          (Metric.closedBall 0 (min t (H - t))).indicator (fun _ => (1 : ℝ)) z := by
        simp only [I, dimensionCausalInterval, dimensionCausalFuture, indicator,
          mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, zero_sub, norm_neg,
          Metric.mem_closedBall, dist_zero_right, le_min_iff]
      simp_rw [he]
      rw [indicator_of_mem ht, integral_indicator measurableSet_closedBall]
      exact dimensionBall_integral_one n hn _ (le_min ht.1 (sub_nonneg.mpr ht.2))
    · rw [indicator_of_not_mem ht]
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun z => by
        apply indicator_of_not_mem
        intro hz
        have h₁ : ‖z‖ ≤ t := by simpa [I, dimensionCausalInterval, dimensionCausalFuture] using hz.1
        have h₂ : ‖z‖ ≤ H - t := by simpa [I, dimensionCausalInterval, dimensionCausalFuture] using hz.2
        exact ht ⟨(norm_nonneg _).trans h₁, by nlinarith [norm_nonneg z]⟩
  simp_rw [hf]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hH, intervalIntegral.integral_const_mul,
    integral_min_pow n H hH, dimensionRadialFactor_eq_sphere n hn,
    dimensionIntervalCoefficient_eq_sphere (n + 1) (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, div_pow, pow_succ]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

theorem volume_dimensionStandardInterval (n : ℕ) (hn : 0 < n) (H : ℝ) (hH : 0 ≤ H) :
    volume (dimensionCausalInterval (0 : DimensionSpacetime n) (H, 0)) =
      ENNReal.ofReal (dimensionIntervalCoefficient (n + 1) * H ^ (n + 1)) := by
  rw [← volume_dimensionStandardInterval_real n hn H hH,
    ENNReal.ofReal_toReal (volume_dimensionCausalInterval_lt_top _ _).ne]

/-- Arbitrary future timelike endpoints, with the affine Jacobian proved in
`DimensionLorentz`. The half-dimensional real power includes odd dimensions. -/
theorem volume_dimensionCausalInterval_timelike (hn : 0 < n) (x y : DimensionSpacetime n)
    (hxy : y ∈ dimensionChronologicalFuture x) :
    volume (dimensionCausalInterval x y) = ENNReal.ofReal
      (dimensionIntervalCoefficient (n + 1) * dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
  let H := Real.sqrt (dimensionIntervalSq x y)
  have hs := dimensionIntervalSq_pos hxy
  have hH : 0 < H := Real.sqrt_pos.mpr hs
  have ht : 0 < (y - x).1 := (norm_nonneg _).trans_lt hxy
  have hd : dimensionMinkowski n (y - x) (y - x) = H ^ 2 := by
    rw [← dimensionIntervalSq_eq_minkowski, Real.sq_sqrt hs.le]
  obtain ⟨F, hF0, hFH⟩ := exists_dimensionRestFrame (y - x) H hH ht hd
  let G : DimensionPoincareEquiv n := { F with translation := x }
  have hG0 : G 0 = x := by simp [G, DimensionPoincareEquiv.apply_eq]
  have hGH : G (H, 0) = y := by
    have hh : F.linear (H, 0) = y - x := by
      simpa only [DimensionPoincareEquiv.apply_eq, hF0, add_zero] using hFH
    simp [G, DimensionPoincareEquiv.apply_eq, hh]
  rw [← hG0, ← hGH, ← G.interval_image, G.volume_image,
    volume_dimensionStandardInterval n hn H hH.le]
  rw [hG0, hGH]
  congr 2
  dsimp only [H]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  congr 1
  ring

/-- Closed causal pairs, including null and diagonal pairs. The null branch
uses zero volume directly and does not assert a null rest frame. -/
theorem volume_dimensionCausalInterval (hn : 0 < n) (x y : DimensionSpacetime n)
    (hxy : y ∈ dimensionCausalFuture x) :
    volume (dimensionCausalInterval x y) = ENNReal.ofReal
      (dimensionIntervalCoefficient (n + 1) * dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
  by_cases hs : dimensionIntervalSq x y = 0
  · rw [volume_dimensionCausalInterval_null hn x y hs, hs, Real.zero_rpow (by positivity), mul_zero,
      ENNReal.ofReal_zero]
  · apply volume_dimensionCausalInterval_timelike hn x y
    change ‖y.2 - x.2‖ < y.1 - x.1
    apply lt_of_le_of_ne hxy
    intro he
    exact hs (by simp [dimensionIntervalSq, he])

theorem dimensionRestrictedIntervalVolume_eq_properTime (hn : 0 < n)
    {M : Set (DimensionSpacetime n)} (hM : DimensionCausallyConvex M)
    {x y : DimensionSpacetime n} (hx : x ∈ M) (hy : y ∈ M) (hxy : y ∈ dimensionCausalFuture x) :
    dimensionRestrictedIntervalVolume M x y = ENNReal.ofReal
      (dimensionIntervalCoefficient (n + 1) * dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
  rw [dimensionRestrictedIntervalVolume_eq hM hx hy, volume_dimensionCausalInterval hn x y hxy]

end BoundaryDraft
