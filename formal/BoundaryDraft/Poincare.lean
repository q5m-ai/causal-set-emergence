import BoundaryDraft.ExpectationBridge

/-!
# Affine, time-oriented Lorentz transport

Only algebraic metric preservation and the orientation of the time axis are
inputs. In particular, determinant one is NOT a hypothesis: spatial orientation
reversal is allowed. Product Lebesgue and causal-region transport are derived.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

/-- An affine Lorentz equivalence, including translations and either spatial
orientation. Time orientation is specified on just one future timelike vector. -/
structure PoincareEquiv where
  linear : Spacetime ≃ₗ[ℝ] Spacetime
  translation : Spacetime
  preserves_inner : ∀ x y, minkowskiInner (linear x) (linear y) = minkowskiInner x y
  future_time : 0 < linear (timeAxis 1) 0

namespace PoincareEquiv

/-- The underlying affine homeomorphism. -/
def toHomeomorph (F : PoincareEquiv) : Spacetime ≃ₜ Spacetime :=
  F.linear.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addRight F.translation)

instance : CoeFun PoincareEquiv (fun _ => Spacetime → Spacetime) :=
  ⟨fun F => F.toHomeomorph⟩

theorem apply_eq (F : PoincareEquiv) (x : Spacetime) :
    F x = F.linear x + F.translation := rfl

theorem map_sub (F : PoincareEquiv) (x y : Spacetime) :
    F y - F x = F.linear (y - x) := by
  simp only [apply_eq, _root_.map_sub]
  abel

/-- All endpoint interval squares, not just timelike ones, are preserved. -/
@[simp] theorem intervalSq_map (F : PoincareEquiv) (x y : Spacetime) :
    intervalSq (F x) (F y) = intervalSq x y := by
  rw [intervalSq_eq_minkowski_sub, F.map_sub, F.preserves_inner,
    ← intervalSq_eq_minkowski_sub]

private theorem inner_axis (x : Spacetime) :
    minkowskiInner x (timeAxis 1) = x 0 := by simp [minkowskiInner]

private theorem inverse_future_time (F : PoincareEquiv) :
    0 < F.linear.symm (timeAxis 1) 0 := by
  have h := F.preserves_inner (F.linear.symm (timeAxis 1)) (timeAxis 1)
  rw [F.linear.apply_symm_apply, minkowskiInner_symm, inner_axis, inner_axis] at h
  exact h ▸ F.future_time

/-- Inverse affine transport, with its time orientation derived. -/
def symm (F : PoincareEquiv) : PoincareEquiv where
  linear := F.linear.symm
  translation := -F.linear.symm F.translation
  preserves_inner := by
    intro x y
    simpa using (F.preserves_inner (F.linear.symm x) (F.linear.symm y)).symm
  future_time := F.inverse_future_time

@[simp] theorem symm_apply_apply (F : PoincareEquiv) (x : Spacetime) :
    F.symm (F x) = x := by simp [apply_eq, symm]

@[simp] theorem apply_symm_apply (F : PoincareEquiv) (x : Spacetime) :
    F (F.symm x) = x := by simp [apply_eq, symm]

private theorem future_linear (F : PoincareEquiv) {v : Spacetime}
    (hv : v ∈ causalFuture 0) : F.linear v ∈ causalFuture 0 := by
  have hvq : 0 ≤ minkowskiInner v v := by
    rw [minkowskiInner_self]
    exact sub_nonneg.mpr hv.2
  have hd : minkowskiInner (F.linear (timeAxis 1)) (F.linear (timeAxis 1)) = 1 := by
    rw [F.preserves_inner]
    simp [minkowskiInner]
  have ht := time_nonneg_of_minkowskiInner_nonneg
    (F.preserves_inner v v ▸ hvq) F.future_time (by rw [hd]; norm_num)
    (show 0 ≤ minkowskiInner (F.linear v) (F.linear (timeAxis 1)) by
      rw [F.preserves_inner, inner_axis]; exact hv.1)
  constructor
  · exact ht
  · have hq : 0 ≤ intervalSq 0 (F.linear v) := by
      rw [← minkowskiInner_self, F.preserves_inner]; exact hvq
    exact sub_nonneg.mp hq

private theorem causal_iff_sub (x y : Spacetime) :
    y ∈ causalFuture x ↔ y - x ∈ causalFuture 0 := by
  simp [causalFuture, spatialSeparationSq, sub_nonneg]

/-- The closed causal relation, including null pairs and the diagonal. -/
@[simp] theorem causalFuture_map (F : PoincareEquiv) (x y : Spacetime) :
    F y ∈ causalFuture (F x) ↔ y ∈ causalFuture x := by
  rw [causal_iff_sub (F x) (F y), F.map_sub, causal_iff_sub x y]
  constructor
  · intro h
    simpa [symm] using F.symm.future_linear h
  · exact F.future_linear

/-- Absolute determinant one is a consequence of metric preservation.
The matrix identity is `Lᵀ J L = J` in the original product coordinates. -/
theorem abs_det_linear (F : PoincareEquiv) :
    |LinearMap.det F.linear.toLinearMap| = 1 := by
  classical
  let L := LinearMap.toMatrix' F.linear.toLinearMap
  let J : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]
  have hJ (x y : Spacetime) :
      minkowskiInner x y = ∑ i : Fin 4, x i * J i i * y i := by
    simp [minkowskiInner, J, Fin.sum_univ_succ]
    ring
  have hmatrix : L.transpose * J * L = J := by
    ext i j
    have h := F.preserves_inner (Pi.single i 1) (Pi.single j 1)
    have hr : minkowskiInner (Pi.single i 1) (Pi.single j 1) = J i j := by
      rw [hJ]
      by_cases hij : i = j
      · subst j; simp [Pi.single_apply, J, Matrix.diagonal_apply]
      · simp [Pi.single_apply, J, Matrix.diagonal_apply, hij, Ne.symm hij]
    rw [hr, hJ] at h
    have he (k : Fin 4) : (Pi.single k (1 : ℝ) : Spacetime) =
        fun l => if l = k then 1 else 0 := by ext l; simp [Pi.single_apply]
    simpa [L, LinearMap.toMatrix'_apply, Matrix.mul_apply, Matrix.transpose_apply,
      he, J, Fin.sum_univ_succ] using h
  have hdetJ : J.det = -1 := by norm_num [J, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hd := congrArg Matrix.det hmatrix
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetJ] at hd
  have hs : L.det ^ 2 = 1 := by nlinarith [hd]
  dsimp only [L] at hs
  rw [LinearMap.det_toMatrix'] at hs
  nlinarith [sq_abs (LinearMap.det F.linear.toLinearMap), abs_nonneg
    (LinearMap.det F.linear.toLinearMap)]

/-- Lebesgue preservation is derived from the determinant and translation. -/
theorem measurePreserving (F : PoincareEquiv) : MeasurePreserving F := by
  have hlinear : MeasurePreserving F.linear := by
    refine ⟨F.linear.toContinuousLinearEquiv.continuous.measurable, ?_⟩
    have hn : LinearMap.det F.linear.toLinearMap ≠ 0 := by
      intro h
      simpa [h] using F.abs_det_linear
    rw [show (F.linear : Spacetime → Spacetime) = F.linear.toLinearMap by rfl,
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hn, abs_inv, F.abs_det_linear]
    simp
  exact (measurePreserving_add_right volume F.translation).comp hlinear

/-- Volume preservation on arbitrary sets, not just measurable regions. -/
theorem volume_image (F : PoincareEquiv) (M : Set Spacetime) :
    volume (F '' M) = volume M := by
  have h := F.measurePreserving.measure_preimage_emb
    F.toHomeomorph.measurableEmbedding (F '' M)
  rw [F.toHomeomorph.injective.preimage_image] at h
  exact h.symm

/-- Signed integral transport on any set, via a measurable equivalence.
No positivity of the observable or unproved Fubini interchange is used. -/
theorem integral_image (F : PoincareEquiv) (M : Set Spacetime) (f : Spacetime → ℝ) :
    (∫ y in F '' M, f y) = ∫ x in M, f (F x) :=
  F.measurePreserving.setIntegral_image_emb F.toHomeomorph.measurableEmbedding f M

end PoincareEquiv

/-- A continuous coordinate change on finite-dimensional spacetime maps a
bounded set into a bounded set, by compactness of its closure. -/
theorem isBounded_image_spacetime {M : Set Spacetime} (hM : Bornology.IsBounded M)
    {f : Spacetime → Spacetime} (hf : Continuous f) : Bornology.IsBounded (f '' M) :=
  (hM.isCompact_closure.image hf).isBounded.subset (image_mono subset_closure)

/-- Geometric causal convexity transports through a causal homeomorphism. -/
theorem CausallyConvex.image {M : Set Spacetime} (hM : CausallyConvex M)
    (F : Spacetime ≃ₜ Spacetime)
    (hc : ∀ x y, F y ∈ causalFuture (F x) ↔ y ∈ causalFuture x) :
    CausallyConvex (F '' M) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
  refine ⟨F.symm z, hM x hx y hy ?_, F.apply_symm_apply z⟩
  constructor
  · exact (hc x (F.symm z)).mp (by simpa using hz.1)
  · exact (hc (F.symm z) y).mp (by simpa using hz.2)

/-- The original region class is preserved without extra hypotheses. -/
theorem BoundedCausalRegion.poincare_image {M : Set Spacetime}
    (hM : BoundedCausalRegion M) (F : PoincareEquiv) : BoundedCausalRegion (F '' M) :=
  ⟨F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hM.measurable,
    isBounded_image_spacetime hM.bounded F.toHomeomorph.continuous,
    hM.causallyConvex.image F.toHomeomorph F.causalFuture_map⟩

end BoundaryDraft
