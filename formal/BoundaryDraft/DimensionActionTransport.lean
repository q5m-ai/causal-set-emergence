import BoundaryDraft.DimensionIntervalVolume
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Finite-density transport of the actual dimension-indexed weighted action

Both endpoints and the first-endpoint weight are transported. Future partners
remain the entire region, including null and diagonal pairs. These are exact
finite-density identities, not boundary limits or Poisson expectations.
-/

open MeasureTheory Set
open scoped Pointwise ENNReal
noncomputable section
namespace BoundaryDraft

variable {n : ℕ}

namespace DimensionPoincareEquiv

theorem image_future_inter (F : DimensionPoincareEquiv n) (M : Set (DimensionSpacetime n))
    (x : DimensionSpacetime n) :
    F '' (M ∩ dimensionCausalFuture x) = F '' M ∩ dimensionCausalFuture (F x) := by
  ext z
  obtain ⟨y, rfl⟩ := F.toHomeomorph.surjective z
  simp only [F.toHomeomorph.injective.mem_set_image, mem_inter_iff, F.causalFuture_map]

/-- Lorentz covariance with a signed first-endpoint weight. -/
theorem weightedAction_image (F : DimensionPoincareEquiv n) (a β c ρ : ℝ)
    (M : Set (DimensionSpacetime n)) (w : DimensionSpacetime n → ℝ) :
    dimensionWeightedAction n a β c ρ (F '' M) (fun p => w (F.symm p)) =
      dimensionWeightedAction n a β c ρ M w := by
  unfold dimensionWeightedAction
  rw [F.integral_image, F.integral_image]
  simp only [F.symm_apply_apply]
  congr 3
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← F.image_future_inter, F.integral_image]
  simp only [dimensionBilocalKernel, F.intervalSq_map]

end DimensionPoincareEquiv

theorem dimensionIntervalSq_smul (s : ℝ) (x y : DimensionSpacetime n) :
    dimensionIntervalSq (s • x) (s • y) = s ^ 2 * dimensionIntervalSq x y := by
  rw [dimensionIntervalSq_eq_minkowski, ← smul_sub,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    ← dimensionIntervalSq_eq_minkowski]
  ring

/-- Positive scaling preserves the closed order, not just chronology. -/
theorem dimensionCausalFuture_smul {s : ℝ} (hs : 0 < s) (x y : DimensionSpacetime n) :
    s • y ∈ dimensionCausalFuture (s • x) ↔ y ∈ dimensionCausalFuture x := by
  simp only [dimensionCausalFuture, mem_setOf_eq, Prod.smul_fst, Prod.smul_snd,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs, smul_eq_mul, ← mul_sub,
    mul_le_mul_left hs]

def dimensionDilateRegion (s : ℝ) (M : Set (DimensionSpacetime n)) : Set (DimensionSpacetime n) :=
  (fun x => s • x) '' M

theorem dimensionSpacetime_finrank (n : ℕ) : Module.finrank ℝ (DimensionSpacetime n) = n + 1 := by
  simp [DimensionSpacetime, DimensionSpatial, Module.finrank_prod, Nat.add_comm]

theorem volume_dimensionDilateRegion {s : ℝ} (hs : 0 < s) (M : Set (DimensionSpacetime n)) :
    volume (dimensionDilateRegion s M) = ENNReal.ofReal (s ^ (n + 1)) * volume M := by
  simpa only [dimensionSpacetime_finrank] using Measure.addHaar_smul_of_nonneg volume hs.le M

theorem integral_dimensionDilateRegion {s : ℝ} (hs : 0 < s) (M : Set (DimensionSpacetime n))
    (f : DimensionSpacetime n → ℝ) :
    (∫ y in dimensionDilateRegion s M, f y) = s ^ (n + 1) * ∫ x in M, f (s • x) := by
  have h := Measure.setIntegral_comp_smul_of_pos volume f M hs
  rw [dimensionSpacetime_finrank, smul_eq_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'), one_mul]
  rfl

theorem dimensionDilateRegion_future_inter {s : ℝ} (hs : 0 < s)
    (M : Set (DimensionSpacetime n)) (x : DimensionSpacetime n) :
    dimensionDilateRegion s (M ∩ dimensionCausalFuture x) =
      dimensionDilateRegion s M ∩ dimensionCausalFuture (s • x) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (dimensionCausalFuture_smul hs x y).mpr hc⟩
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    exact ⟨y, ⟨hy, (dimensionCausalFuture_smul hs x y).mp hc⟩, rfl⟩

theorem dimensionBilocalKernel_smul {s : ℝ} (hs : 0 < s) (c ρ : ℝ)
    (x y : DimensionSpacetime n) (hxy : y ∈ dimensionCausalFuture x) :
    dimensionBilocalKernel n c ρ (s • x) (s • y) =
      dimensionBilocalKernel n c (ρ * s ^ (n + 1)) x y := by
  have hp : (s ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2) = s ^ (n + 1) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (((n + 1 : ℕ) : ℝ) / 2) = ((n + 1 : ℕ) : ℝ) by ring,
      Real.rpow_natCast]
  unfold dimensionBilocalKernel
  rw [dimensionIntervalSq_smul, Real.mul_rpow (sq_nonneg s) (dimensionIntervalSq_nonneg hxy), hp]
  congr 1
  ring

/-- Both endpoint Jacobians appear, even with a signed source weight. -/
theorem dimensionWeighted_bilocal_dilate {s : ℝ} (hs : 0 < s) (c ρ : ℝ)
    (M : Set (DimensionSpacetime n)) (hM : MeasurableSet M) (w : DimensionSpacetime n → ℝ) :
    (∫ x in dimensionDilateRegion s M, w (s⁻¹ • x) *
      ∫ y in dimensionDilateRegion s M ∩ dimensionCausalFuture x, dimensionBilocalKernel n c ρ x y) =
      (s ^ (n + 1)) ^ 2 * ∫ x in M, w x *
        ∫ y in M ∩ dimensionCausalFuture x, dimensionBilocalKernel n c (ρ * s ^ (n + 1)) x y := by
  rw [integral_dimensionDilateRegion hs]
  simp_rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul,
    ← dimensionDilateRegion_future_inter hs, integral_dimensionDilateRegion hs]
  have he (x : DimensionSpacetime n) :
      (∫ y in M ∩ dimensionCausalFuture x, dimensionBilocalKernel n c ρ (s • x) (s • y)) =
        ∫ y in M ∩ dimensionCausalFuture x, dimensionBilocalKernel n c (ρ * s ^ (n + 1)) x y := by
    apply setIntegral_congr_fun (hM.inter (measurableSet_dimensionCausalFuture x))
    intro y hy
    exact dimensionBilocalKernel_smul hs c ρ x y hy.2
  simp_rw [he, ← mul_assoc, mul_comm _ (s ^ (n + 1)), mul_assoc, integral_const_mul]
  ring

/-- Exact positive-dilation law in physical dimension `n+1 ≥ 2`. No density
limit, rate, regulator removal, or random-process covariance is inferred. -/
theorem dimensionWeightedAction_dilate (hn : 0 < n) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (a β c : ℝ) (M : Set (DimensionSpacetime n)) (hM : MeasurableSet M)
    (w : DimensionSpacetime n → ℝ) :
    dimensionWeightedAction n a β c ρ (dimensionDilateRegion s M) (fun p => w (s⁻¹ • p)) =
      s ^ (n - 1) * dimensionWeightedAction n a β c (ρ * s ^ (n + 1)) M w := by
  have hd : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (ρ * s ^ (n + 1)) ^ (2 / ((n + 1 : ℕ) : ℝ)) =
      ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) * s ^ 2 := by
    rw [Real.mul_rpow hρ.le (pow_nonneg hs.le _), ← Real.rpow_natCast s (n + 1),
      ← Real.rpow_mul hs.le, mul_div_cancel₀ 2 hd, Real.rpow_two]
  have hsdeg : s ^ (n - 1) * s ^ 2 = s ^ (n + 1) := by
    rw [← pow_add, show n - 1 + 2 = n + 1 by omega]
  unfold dimensionWeightedAction
  rw [integral_dimensionDilateRegion hs, dimensionWeighted_bilocal_dilate hs c ρ M hM w, hp]
  simp only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  calc
    _ = (s ^ (n - 1) * s ^ 2) * ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) *
        (a * (∫ x in M, w x) - β * (ρ * s ^ (n + 1)) * ∫ x in M,
          w x * ∫ y in M ∩ dimensionCausalFuture x,
            dimensionBilocalKernel n c (ρ * s ^ (n + 1)) x y) := by rw [hsdeg]; ring
    _ = _ := by ring

end BoundaryDraft
