import BoundaryDraft.DimensionIntervalCompatibility

/-! Exact Lorentz and positive-dilation transport, without a limit premise. -/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft

-- Expanded, dimension-general signed observable: both endpoint integrals and
-- the weight are transformed, with no truncation of the partner domain.
example (n : ℕ) (F : DimensionPoincareEquiv n) (a β c ρ : ℝ)
    (M : Set (DimensionSpacetime n)) (w : DimensionSpacetime n → ℝ) :
    ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) *
      (a * (∫ x in F '' M, -w (F.symm x)) - β * ρ * ∫ x in F '' M,
        -w (F.symm x) * ∫ y in F '' M ∩ dimensionCausalFuture x,
          dimensionBilocalKernel n c ρ x y) =
      dimensionWeightedAction n a β c ρ M (fun x => -w x) :=
  F.weightedAction_image a β c ρ M (fun x => -w x)

example (n : ℕ) (F : DimensionPoincareEquiv n) (x y : DimensionSpacetime n) :
    F y ∈ dimensionCausalFuture (F x) ↔ y ∈ dimensionCausalFuture x := F.causalFuture_map x y

example (n : ℕ) (F : DimensionPoincareEquiv n) : |LinearMap.det F.linear.toLinearMap| = 1 :=
  F.abs_det_linear

-- Concrete spatial parity. It preserves future direction while reversing
-- spatial orientation in odd spatial dimension. No determinant premise.
private def parityLinear (n : ℕ) : DimensionSpacetime n ≃ₗ[ℝ] DimensionSpacetime n where
  toFun x := (x.1, -x.2)
  invFun x := (x.1, -x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [add_comm]
  map_smul' c x := by simp

private def parity (n : ℕ) : DimensionPoincareEquiv n where
  linear := parityLinear n
  translation := 0
  preserves_inner x y := by simp [parityLinear, dimensionMinkowski_apply]
  future_time := by norm_num [parityLinear]

example (M : Set (DimensionSpacetime 3)) :
    volume ((fun x : DimensionSpacetime 3 => (x.1, -x.2)) '' M) = volume M := by
  simpa only [DimensionPoincareEquiv.apply_eq, parity, parityLinear, LinearEquiv.coe_mk,
    add_zero] using (parity 3).volume_image M

example (n : ℕ) (hn : 0 < n) (s ρ : ℝ) (hs : 0 < s) (hρ : 0 < ρ)
    (a β c : ℝ) (M : Set (DimensionSpacetime n)) (hM : MeasurableSet M)
    (w : DimensionSpacetime n → ℝ) :
    dimensionWeightedAction n a β c ρ ((fun x => s • x) '' M) (fun x => w (s⁻¹ • x)) =
      s ^ (n - 1) * dimensionWeightedAction n a β c (ρ * s ^ (n + 1)) M w :=
  dimensionWeightedAction_dilate hn hs hρ a β c M hM w

-- In 2D the area factor is one, not a positive power of s.
example (ρ : ℝ) (hρ : 0 < ρ) (M : Set (DimensionSpacetime 1)) (hM : MeasurableSet M)
    (w : DimensionSpacetime 1 → ℝ) :
    dimensionWeightedAction 1 2 4 (1 / 2) ρ (dimensionDilateRegion 2 M) (fun x => w ((1 / 2 : ℝ) • x)) =
      dimensionWeightedAction 1 2 4 (1 / 2) (ρ * 4) M w := by
  have h := dimensionWeightedAction_dilate (by omega : 0 < 1)
    (by norm_num : (0 : ℝ) < 2) hρ 2 4 (1 / 2) M hM w
  norm_num at h
  exact h

-- Reciprocal scale in odd dimension: density changes by 1/8, area by 1/2.
example (ρ : ℝ) (hρ : 0 < ρ) (M : Set (DimensionSpacetime 2)) (hM : MeasurableSet M)
    (w : DimensionSpacetime 2 → ℝ) :
    dimensionWeightedAction 2 (dimensionPointCoefficient 3) (dimensionPairCoefficient 3) (Real.pi / 12)
      ρ (dimensionDilateRegion (1 / 2) M) (fun x => w ((2 : ℝ) • x)) =
      (1 / 2 : ℝ) * dimensionWeightedAction 2 (dimensionPointCoefficient 3) (dimensionPairCoefficient 3)
        (Real.pi / 12) (ρ / 8) M w := by
  have h := dimensionWeightedAction_dilate (by omega : 0 < 2)
    (by norm_num : (0 : ℝ) < 1 / 2) hρ (dimensionPointCoefficient 3)
      (dimensionPairCoefficient 3) (Real.pi / 12) M hM w
  norm_num at h
  simpa only [div_eq_mul_inv, one_mul] using h

-- 4D unchanged area factor and both endpoint Jacobians, at non-unit scale.
example (M : Set (DimensionSpacetime 3)) : volume (dimensionDilateRegion 2 M) = 16 * volume M := by
  have h := volume_dimensionDilateRegion (by norm_num : (0 : ℝ) < 2) M
  norm_num at h
  exact h

example (ρ : ℝ) (hρ : 0 < ρ) (M : Set (DimensionSpacetime 3)) (hM : MeasurableSet M) :
    dimensionWeightedAction 3 (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) ρ
      (dimensionDilateRegion 2 M) (fun _ => 1) =
      4 * dimensionWeightedAction 3 (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) (ρ * 16)
        M (fun _ => 1) := by
  have h := dimensionWeightedAction_dilate (by omega : 0 < 3)
    (by norm_num : (0 : ℝ) < 2) hρ (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) M hM (fun _ => 1)
  norm_num at h
  exact h

end BoundaryDraft
