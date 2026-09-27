import BoundaryDraft.Poincare
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Covariance and positive-dilation scaling of the unchanged BDG mean

Both proofs substitute in each of the actual two endpoint integrals. They do
not use a boundary limit or redefine the action. The expectation results then
use the existing exact bridge, not a new covariance law for random processes.
-/

open MeasureTheory Set
open scoped BigOperators Pointwise

noncomputable section
namespace BoundaryDraft

/-- Every future-point kernel is absolutely integrable on a bounded region. -/
theorem integrableOn_bdg_future_of_bounded {M : Set Spacetime}
    (hM : Bornology.IsBounded M) (ρ : ℝ) (x : Spacetime) :
    IntegrableOn (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2))
      (M ∩ causalFuture x) := by
  have hc : Continuous (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) := by
    unfold bdgKernel bdgPolynomial
    have := continuous_intervalSq
    fun_prop
  exact (hc.continuousOn.integrableOn_compact hM.isCompact_closure).mono_set
    (fun _ hy => subset_closure hy.1)

/-- The outer integral is absolutely integrable too. This follows from compact
bilocal domination and Fubini, with the causal indicator kept intact. -/
theorem integrableOn_bdg_outer {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) :
    IntegrableOn (fun x => ∫ y in M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) M := by
  classical
  let S : Set (Spacetime × Spacetime) :=
    {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ causalFuture p.1}
  let K : Spacetime × Spacetime → ℝ := S.indicator
    (fun p => bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
  have hS : MeasurableSet S :=
    (hm.preimage measurable_fst).inter
      ((hm.preimage measurable_snd).inter measurableSet_causalRelation)
  have hK : Integrable K (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hS).mpr (integrableOn_bilocal_bdg hb ρ)
  apply (integrable_indicator_iff hm).mp
  apply hK.integral_prod_left.congr
  filter_upwards [] with x
  by_cases hx : x ∈ M
  · rw [indicator_of_mem hx, ← integral_indicator
      (hm.inter (isClosed_causalFuture x).measurableSet)]
    congr 1
    ext y
    simp only [K, Set.indicator_apply]
    simp [S, hx]
  · simp [K, S, Set.indicator, hx]

namespace PoincareEquiv

/-- Image of the whole future integration slice, including its null boundary. -/
theorem image_future_inter (F : PoincareEquiv) (M : Set Spacetime) (x : Spacetime) :
    F '' (M ∩ causalFuture x) = F '' M ∩ causalFuture (F x) := by
  ext z
  obtain ⟨y, rfl⟩ := F.toHomeomorph.surjective z
  simp only [F.toHomeomorph.injective.mem_set_image, mem_inter_iff, F.causalFuture_map]

/-- Exact finite-density covariance of the original bilocal definition.
The measurable-equivalence substitution actually holds for every set/density;
physical bounded causally convex regions are handled below. -/
theorem continuumMean_image (F : PoincareEquiv) (ρ : ℝ) (M : Set Spacetime) :
    continuumMean ρ (F '' M) = continuumMean ρ M := by
  unfold continuumMean
  rw [F.integral_image, F.integral_image]
  congr 3
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← F.image_future_inter, F.integral_image]
  simp only [F.intervalSq_map]

/-- The finite-density expected-action identity is transferred through the
separately proved bridge. No coupling of Poisson laws is asserted. -/
theorem expectedBDGAction_image (F : PoincareEquiv) {M : Set Spacetime}
    (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (F '' M) = expectedBDGAction ρ M := by
  rw [(hM.poincare_image F).expectedBDGAction_eq hρ, hM.expectedBDGAction_eq hρ,
    F.continuumMean_image]

end PoincareEquiv

/-- Positive dilation means the set image under simultaneous scaling of all
four coordinates, not scaling only the spatial section or its height. -/
def dilateRegion (s : ℝ) (M : Set Spacetime) : Set Spacetime :=
  (fun x : Spacetime => s • x) '' M

@[simp] theorem dilateRegion_eq_smul (s : ℝ) (M : Set Spacetime) :
    dilateRegion s M = s • M := rfl

/-- Endpoint squared intervals have degree two under dilation. -/
theorem intervalSq_smul (s : ℝ) (x y : Spacetime) :
    intervalSq (s • x) (s • y) = s ^ 2 * intervalSq x y := by
  rw [intervalSq_eq_minkowski_sub, ← smul_sub,
    minkowskiInner_smul_left, minkowskiInner_smul_right, ← intervalSq_eq_minkowski_sub]
  ring

/-- Positive dilations preserve and reflect the entire closed causal order. -/
theorem causalFuture_smul {s : ℝ} (hs : 0 < s) (x y : Spacetime) :
    s • y ∈ causalFuture (s • x) ↔ y ∈ causalFuture x := by
  have hc (a b : Spacetime) : b ∈ causalFuture a ↔
      a 0 ≤ b 0 ∧ 0 ≤ intervalSq a b := by
    simp [causalFuture, intervalSq, sub_nonneg]
  rw [hc, hc, intervalSq_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_le_mul_left hs,
    mul_nonneg_iff_of_pos_left (sq_pos_of_pos hs)]

/-- A convenient actual homeomorphism, with inverse scaling by `s⁻¹`. -/
def dilationHomeomorph (s : ℝ) (hs : 0 < s) : Spacetime ≃ₜ Spacetime :=
  Homeomorph.smul (Units.mk0 s hs.ne')

@[simp] theorem dilationHomeomorph_apply (s : ℝ) (hs : 0 < s) (x : Spacetime) :
    dilationHomeomorph s hs x = s • x := rfl

@[simp] theorem dilationHomeomorph_symm_apply (s : ℝ) (hs : 0 < s) (x : Spacetime) :
    (dilationHomeomorph s hs).symm x = s⁻¹ • x := rfl

theorem BoundedCausalRegion.dilate {M : Set Spacetime} (hM : BoundedCausalRegion M)
    {s : ℝ} (hs : 0 < s) : BoundedCausalRegion (dilateRegion s M) := by
  let F := dilationHomeomorph s hs
  exact ⟨F.measurableEmbedding.measurableSet_image.mpr hM.measurable,
    isBounded_image_spacetime hM.bounded F.continuous,
    hM.causallyConvex.image F (causalFuture_smul hs)⟩

/-- Extended-real volume scales by the fourth power, on every set. -/
theorem volume_dilateRegion {s : ℝ} (hs : 0 < s) (M : Set Spacetime) :
    volume (dilateRegion s M) = ENNReal.ofReal (s ^ 4) * volume M := by
  simpa [Spacetime] using Measure.addHaar_smul_of_nonneg volume hs.le M

/-- The Jacobian factor is the fourth power for the original product measure.
This signed set-integral substitution is valid also for zero-volume sets. -/
theorem integral_dilateRegion {s : ℝ} (hs : 0 < s) (M : Set Spacetime)
    (f : Spacetime → ℝ) :
    (∫ y in dilateRegion s M, f y) = s ^ 4 * ∫ x in M, f (s • x) := by
  have h := Measure.setIntegral_comp_smul_of_pos volume f M hs
  have hdim : Module.finrank ℝ Spacetime = 4 := by simp [Spacetime]
  rw [hdim, smul_eq_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'), one_mul]
  rfl

/-- Dilation of each full causal future slice. -/
theorem dilateRegion_future_inter {s : ℝ} (hs : 0 < s)
    (M : Set Spacetime) (x : Spacetime) :
    dilateRegion s (M ∩ causalFuture x) =
      dilateRegion s M ∩ causalFuture (s • x) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (causalFuture_smul hs x y).mpr hc⟩
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    exact ⟨y, ⟨hy, (causalFuture_smul hs x y).mp hc⟩, rfl⟩

/-- Exact two-endpoint scaling, including both Jacobian factors. -/
theorem bilocal_integral_dilate {s : ℝ} (hs : 0 < s) (ρ : ℝ) (M : Set Spacetime) :
    (∫ x in dilateRegion s M, ∫ y in dilateRegion s M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
    s ^ 8 * ∫ x in M, ∫ y in M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * (ρ * s ^ 4) * intervalSq x y ^ 2) := by
  rw [integral_dilateRegion hs]
  simp_rw [← dilateRegion_future_inter hs, integral_dilateRegion hs, intervalSq_smul]
  have he (x y : Spacetime) :
      (Real.pi / 24) * ρ * (s ^ 2 * intervalSq x y) ^ 2 =
        (Real.pi / 24) * (ρ * s ^ 4) * intervalSq x y ^ 2 := by ring
  simp_rw [he, integral_const_mul]
  ring

/-- Independent positive-dilation law at finite positive density. -/
theorem continuumMean_dilate {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (M : Set Spacetime) :
    continuumMean ρ (dilateRegion s M) = s ^ 2 * continuumMean (ρ * s ^ 4) M := by
  unfold continuumMean
  rw [integral_dilateRegion hs, bilocal_integral_dilate hs]
  have hsqrt : Real.sqrt (ρ * s ^ 4) = Real.sqrt ρ * s ^ 2 := by
    rw [Real.sqrt_mul hρ.le, show s ^ 4 = (s ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg s)]
  rw [hsqrt]
  ring

/-- Dilation transfer to the independently defined Poisson expectation. -/
theorem expectedBDGAction_dilate {M : Set Spacetime} (hM : BoundedCausalRegion M)
    {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) :
    expectedBDGAction ρ (dilateRegion s M) =
      s ^ 2 * expectedBDGAction (ρ * s ^ 4) M := by
  rw [(hM.dilate hs).expectedBDGAction_eq hρ,
    hM.expectedBDGAction_eq (mul_pos hρ (pow_pos hs _)), continuumMean_dilate hs hρ]

end BoundaryDraft
