import BoundaryDraft.DimensionCausalInterval
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lorentz transport in arbitrary finite dimension

Metric preservation and future orientation are the only geometric inputs.
Absolute determinant one and product-volume preservation are conclusions.
An explicit Householder reflection supplies a rest frame for every future
 timelike displacement. Neither a volume nor a transport law is a premise.
-/

open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace BoundaryDraft

variable {n : ℕ}

/-- The Minkowski bilinear form on the actual Euclidean product coordinates. -/
def dimensionMinkowski (n : ℕ) : LinearMap.BilinForm ℝ (DimensionSpacetime n) :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.1 - ⟪x.2, y.2⟫_ℝ)
    (by intros; simp [inner_add_left]; ring)
    (by intros; simp [inner_smul_left]; ring)
    (by intros; simp [inner_add_right]; ring)
    (by intros; simp [inner_smul_right]; ring)

theorem dimensionMinkowski_apply (x y : DimensionSpacetime n) :
    dimensionMinkowski n x y = x.1 * y.1 - ⟪x.2, y.2⟫_ℝ := rfl

theorem dimensionMinkowski_symm (x y : DimensionSpacetime n) :
    dimensionMinkowski n x y = dimensionMinkowski n y x := by
  simp only [dimensionMinkowski_apply, real_inner_comm y.2 x.2, mul_comm]

theorem dimensionIntervalSq_eq_minkowski (x y : DimensionSpacetime n) :
    dimensionIntervalSq x y = dimensionMinkowski n (y - x) (y - x) := by
  simp only [dimensionMinkowski_apply, Prod.fst_sub, Prod.snd_sub,
    real_inner_self_eq_norm_sq, dimensionIntervalSq, pow_two]

theorem dimensionMinkowski_nondegenerate (n : ℕ) : (dimensionMinkowski n).Nondegenerate := by
  intro x hx
  have ht := hx (1, 0)
  have hs := hx (0, x.2)
  simp only [dimensionMinkowski_apply, mul_one, inner_zero_right, sub_zero] at ht
  simp only [dimensionMinkowski_apply, mul_zero, zero_sub, neg_eq_zero,
    inner_self_eq_zero] at hs
  exact Prod.ext ht hs

/-- Metric preservation forces absolute determinant one, independently of the
choice of basis and allowing spatial orientation reversal. -/
theorem dimensionMinkowski_abs_det (L : DimensionSpacetime n →ₗ[ℝ] DimensionSpacetime n)
    (hL : ∀ x y, dimensionMinkowski n (L x) (L y) = dimensionMinkowski n x y) :
    |LinearMap.det L| = 1 := by
  classical
  let b := Module.Free.chooseBasis ℝ (DimensionSpacetime n)
  have he : (dimensionMinkowski n).comp L L = dimensionMinkowski n := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hL x y
  have hm := congrArg (fun B => (BilinForm.toMatrix b B).det) he
  dsimp only at hm
  rw [BilinForm.toMatrix_comp b b, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix] at hm
  have hj := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (dimensionMinkowski_nondegenerate n)
  have hs : LinearMap.det L ^ 2 = 1 := by
    apply (mul_right_cancel₀ hj)
    nlinarith [hm]
  nlinarith [sq_abs (LinearMap.det L), abs_nonneg (LinearMap.det L)]

theorem dimensionMinkowski_measurePreserving
    (L : DimensionSpacetime n →ₗ[ℝ] DimensionSpacetime n)
    (hL : ∀ x y, dimensionMinkowski n (L x) (L y) = dimensionMinkowski n x y) :
    MeasurePreserving L := by
  have hd := dimensionMinkowski_abs_det L hL
  refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
  have hn : LinearMap.det L ≠ 0 := by intro h; simp [h] at hd
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hn, abs_inv, hd]
  simp

/-- The Cauchy--Schwarz time-orientation step is separate from metric preservation. -/
theorem dimension_time_nonneg_of_inner_nonneg {v d : DimensionSpacetime n}
    (hv : 0 ≤ dimensionMinkowski n v v) (hd0 : 0 < d.1)
    (hd : 0 < dimensionMinkowski n d d) (hvd : 0 ≤ dimensionMinkowski n v d) :
    0 ≤ v.1 := by
  simp only [dimensionMinkowski_apply, real_inner_self_eq_norm_sq] at hv hd hvd
  by_contra h
  have hv0 : v.1 < 0 := lt_of_not_ge h
  have hvnorm : ‖v.2‖ ≤ -v.1 := by nlinarith [norm_nonneg v.2]
  have hdnorm : ‖d.2‖ < d.1 := by nlinarith [norm_nonneg d.2]
  have hcs := (neg_le_abs ⟪v.2, d.2⟫_ℝ).trans (abs_real_inner_le_norm v.2 d.2)
  have hmul := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hvnorm (norm_nonneg d.2))
    (mul_lt_mul_of_pos_left hdnorm (neg_pos.mpr hv0))
  nlinarith

theorem dimensionCausalFuture_iff_sub (x y : DimensionSpacetime n) :
    y ∈ dimensionCausalFuture x ↔ y - x ∈ dimensionCausalFuture 0 := by
  simp [dimensionCausalFuture]

theorem dimensionCausalFuture_zero_iff (v : DimensionSpacetime n) :
    v ∈ dimensionCausalFuture 0 ↔ 0 ≤ v.1 ∧ 0 ≤ dimensionMinkowski n v v := by
  simp only [dimensionCausalFuture, mem_setOf_eq, Prod.fst_zero, Prod.snd_zero,
    sub_zero, dimensionMinkowski_apply, real_inner_self_eq_norm_sq]
  constructor
  · intro h
    exact ⟨(norm_nonneg _).trans h, by nlinarith [norm_nonneg v.2]⟩
  · rintro ⟨ht, hq⟩
    nlinarith [norm_nonneg v.2]

/-- Affine, future-oriented Lorentz map. No Jacobian or action premise. -/
structure DimensionPoincareEquiv (n : ℕ) where
  linear : DimensionSpacetime n ≃ₗ[ℝ] DimensionSpacetime n
  translation : DimensionSpacetime n
  preserves_inner : ∀ x y, dimensionMinkowski n (linear x) (linear y) = dimensionMinkowski n x y
  future_time : 0 < (linear (1, 0)).1

namespace DimensionPoincareEquiv

def toHomeomorph (F : DimensionPoincareEquiv n) : DimensionSpacetime n ≃ₜ DimensionSpacetime n :=
  F.linear.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addRight F.translation)

instance : CoeFun (DimensionPoincareEquiv n) (fun _ => DimensionSpacetime n → DimensionSpacetime n) :=
  ⟨fun F => F.toHomeomorph⟩

theorem apply_eq (F : DimensionPoincareEquiv n) (x : DimensionSpacetime n) :
    F x = F.linear x + F.translation := rfl

theorem map_sub (F : DimensionPoincareEquiv n) (x y : DimensionSpacetime n) :
    F y - F x = F.linear (y - x) := by
  simp only [apply_eq, _root_.map_sub]
  abel

@[simp] theorem intervalSq_map (F : DimensionPoincareEquiv n) (x y : DimensionSpacetime n) :
    dimensionIntervalSq (F x) (F y) = dimensionIntervalSq x y := by
  rw [dimensionIntervalSq_eq_minkowski, F.map_sub, F.preserves_inner,
    ← dimensionIntervalSq_eq_minkowski]

private theorem inverse_future_time (F : DimensionPoincareEquiv n) :
    0 < (F.linear.symm (1, 0)).1 := by
  have h := F.preserves_inner (F.linear.symm (1, 0)) (1, 0)
  simp only [F.linear.apply_symm_apply, dimensionMinkowski_apply, one_mul, mul_one,
    inner_zero_left, inner_zero_right, sub_zero] at h
  exact h ▸ F.future_time

def symm (F : DimensionPoincareEquiv n) : DimensionPoincareEquiv n where
  linear := F.linear.symm
  translation := -F.linear.symm F.translation
  preserves_inner := by
    intro x y
    simpa using (F.preserves_inner (F.linear.symm x) (F.linear.symm y)).symm
  future_time := F.inverse_future_time

@[simp] theorem symm_apply_apply (F : DimensionPoincareEquiv n) (x : DimensionSpacetime n) :
    F.symm (F x) = x := by simp [apply_eq, symm]

@[simp] theorem apply_symm_apply (F : DimensionPoincareEquiv n) (x : DimensionSpacetime n) :
    F (F.symm x) = x := by simp [apply_eq, symm]

private theorem future_linear (F : DimensionPoincareEquiv n) {v : DimensionSpacetime n}
    (hv : v ∈ dimensionCausalFuture 0) : F.linear v ∈ dimensionCausalFuture 0 := by
  rw [dimensionCausalFuture_zero_iff] at hv ⊢
  have hd : dimensionMinkowski n (F.linear (1, 0)) (F.linear (1, 0)) = 1 := by
    rw [F.preserves_inner]; simp [dimensionMinkowski_apply]
  refine ⟨dimension_time_nonneg_of_inner_nonneg (F.preserves_inner v v ▸ hv.2)
    F.future_time (by rw [hd]; norm_num) ?_, F.preserves_inner v v ▸ hv.2⟩
  simpa only [F.preserves_inner, dimensionMinkowski_apply, mul_one, inner_zero_right,
    sub_zero] using hv.1

/-- Includes every null pair and the diagonal. -/
@[simp] theorem causalFuture_map (F : DimensionPoincareEquiv n) (x y : DimensionSpacetime n) :
    F y ∈ dimensionCausalFuture (F x) ↔ y ∈ dimensionCausalFuture x := by
  rw [dimensionCausalFuture_iff_sub (F x) (F y), F.map_sub, dimensionCausalFuture_iff_sub x y]
  constructor
  · intro h
    simpa [symm] using F.symm.future_linear h
  · exact F.future_linear

theorem abs_det_linear (F : DimensionPoincareEquiv n) : |LinearMap.det F.linear.toLinearMap| = 1 :=
  dimensionMinkowski_abs_det F.linear.toLinearMap F.preserves_inner

theorem measurePreserving (F : DimensionPoincareEquiv n) : MeasurePreserving F :=
  (measurePreserving_add_right volume F.translation).comp
    (dimensionMinkowski_measurePreserving F.linear.toLinearMap F.preserves_inner)

theorem volume_image (F : DimensionPoincareEquiv n) (M : Set (DimensionSpacetime n)) :
    volume (F '' M) = volume M := by
  have h := F.measurePreserving.measure_preimage_emb F.toHomeomorph.measurableEmbedding (F '' M)
  rw [F.toHomeomorph.injective.preimage_image] at h
  exact h.symm

theorem integral_image (F : DimensionPoincareEquiv n) (M : Set (DimensionSpacetime n))
    (f : DimensionSpacetime n → ℝ) : (∫ y in F '' M, f y) = ∫ x in M, f (F x) :=
  F.measurePreserving.setIntegral_image_emb F.toHomeomorph.measurableEmbedding f M

theorem interval_image (F : DimensionPoincareEquiv n) (x y : DimensionSpacetime n) :
    F '' dimensionCausalInterval x y = dimensionCausalInterval (F x) (F y) := by
  ext z
  obtain ⟨w, rfl⟩ := F.toHomeomorph.surjective z
  simp only [F.toHomeomorph.injective.mem_set_image, dimensionCausalInterval,
    mem_setOf_eq, F.causalFuture_map]

end DimensionPoincareEquiv

/-- Explicit rank-one Lorentz reflection in a non-null vector. -/
def dimensionLorentzReflection (v : DimensionSpacetime n) :
    DimensionSpacetime n →ₗ[ℝ] DimensionSpacetime n :=
  LinearMap.id - (2 / dimensionMinkowski n v v) • (dimensionMinkowski n v).smulRight v

theorem dimensionLorentzReflection_apply (v y : DimensionSpacetime n) :
    dimensionLorentzReflection v y = y - (2 * dimensionMinkowski n y v /
      dimensionMinkowski n v v) • v := by
  simp only [dimensionLorentzReflection, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, dimensionMinkowski_symm v y]
  congr 2
  ring

theorem dimensionLorentzReflection_inner (v y z : DimensionSpacetime n)
    (hv : dimensionMinkowski n v v ≠ 0) :
    dimensionMinkowski n (dimensionLorentzReflection v y) (dimensionLorentzReflection v z) =
      dimensionMinkowski n y z := by
  simp only [dimensionLorentzReflection_apply, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    dimensionMinkowski_symm v z]
  field_simp only [hv]
  ring

theorem dimensionLorentzReflection_involutive (v : DimensionSpacetime n)
    (hv : dimensionMinkowski n v v ≠ 0) : Function.Involutive (dimensionLorentzReflection v) := by
  intro y
  rw [dimensionLorentzReflection_apply, dimensionLorentzReflection_apply,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
  have he : 2 * (dimensionMinkowski n y v -
      2 * dimensionMinkowski n y v / dimensionMinkowski n v v * dimensionMinkowski n v v) /
        dimensionMinkowski n v v = -(2 * dimensionMinkowski n y v / dimensionMinkowski n v v) := by
    field_simp only [hv]
    ring
  rw [he, neg_smul]
  abel

/-- Every positive-duration timelike displacement admits an actual
future-preserving, volume-preserving rest frame. -/
theorem exists_dimensionRestFrame (d : DimensionSpacetime n) (H : ℝ)
    (hH : 0 < H) (hd0 : 0 < d.1) (hdH : dimensionMinkowski n d d = H ^ 2) :
    ∃ F : DimensionPoincareEquiv n, F.translation = 0 ∧ F (H, 0) = d := by
  by_cases he : d = (H, 0)
  · subst d
    exact ⟨⟨LinearEquiv.refl ℝ _, 0, fun _ _ => rfl, by norm_num⟩, rfl, by
      simp [DimensionPoincareEquiv.apply_eq]⟩
  · let v : DimensionSpacetime n := d - (H, 0)
    have hd_ge : H ≤ d.1 := by
      simp only [dimensionMinkowski_apply, real_inner_self_eq_norm_sq] at hdH
      nlinarith [sq_nonneg ‖d.2‖]
    have hd_ne : d.1 ≠ H := by
      intro ht
      apply he
      have hs : d.2 = 0 := by
        simp only [dimensionMinkowski_apply, real_inner_self_eq_norm_sq, ht] at hdH
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg d.2])
      exact Prod.ext ht hs
    have hvv : dimensionMinkowski n v v = 2 * H * (H - d.1) := by
      dsimp only [v]
      simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hdH,
        dimensionMinkowski_apply, inner_zero_right, inner_zero_left, sub_zero]
      ring
    have hv : dimensionMinkowski n v v ≠ 0 := by
      rw [hvv]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hH.ne') (sub_ne_zero.mpr hd_ne.symm)
    let L := LinearEquiv.ofInvolutive (dimensionLorentzReflection v)
      (dimensionLorentzReflection_involutive v hv)
    have haxis : L (H, 0) = d := by
      change dimensionLorentzReflection v (H, 0) = d
      rw [dimensionLorentzReflection_apply, hvv]
      have hev : dimensionMinkowski n (H, 0) v = H * (d.1 - H) := by
        simp [v, dimensionMinkowski_apply]
      rw [hev]
      have hc : 2 * (H * (d.1 - H)) / (2 * H * (H - d.1)) = -1 := by
        apply (div_eq_iff (hvv ▸ hv)).mpr
        ring
      rw [hc, neg_one_smul, sub_neg_eq_add]
      dsimp [v]
      abel
    have htime : 0 < (L (1, 0)).1 := by
      have hh : (H, (0 : DimensionSpatial n)) = H • (1, 0) := by simp
      rw [hh, map_smul] at haxis
      have ht := congrArg Prod.fst haxis
      change H * (L (1, 0)).1 = d.1 at ht
      nlinarith
    exact ⟨⟨L, 0, (fun y z => dimensionLorentzReflection_inner v y z hv), htime⟩, rfl, by
      simpa [DimensionPoincareEquiv.apply_eq] using haxis⟩

end BoundaryDraft
