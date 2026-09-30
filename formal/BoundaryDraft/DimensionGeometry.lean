import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# Dimension-indexed graph-cap geometry for finite-density reduction

Space is genuinely Euclidean and spacetime carries the canonical product
Lebesgue measure. The hypotheses below are only geometric: bounded positive
support and a strictly Lipschitz positive part. No integral or limit is an
admissibility premise. The existing four-dimensional types are unchanged.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

abbrev DimensionSpatial (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev DimensionSpacetime (n : ℕ) := ℝ × DimensionSpatial n

/-- Closed future cone, retaining its vertex and null boundary. -/
def dimensionCausalFuture {n : ℕ} (x : DimensionSpacetime n) : Set (DimensionSpacetime n) :=
  {y | ‖y.2 - x.2‖ ≤ y.1 - x.1}

/-- Squared proper time, defined from the Euclidean spatial norm. -/
def dimensionIntervalSq {n : ℕ} (x y : DimensionSpacetime n) : ℝ :=
  (y.1 - x.1) ^ 2 - ‖y.2 - x.2‖ ^ 2

/-- The independently defined cap below a flat future plane. -/
def dimensionGraphCap {n : ℕ} (h : DimensionSpatial n → ℝ) : Set (DimensionSpacetime n) :=
  {p | -h p.2 < p.1 ∧ p.1 < 0}

structure DimensionGraphCapData {n : ℕ} (h : DimensionSpatial n → ℝ) : Prop where
  bounded_positive : Bornology.IsBounded {x | 0 < h x}
  lipschitz_positivePart : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧
    ∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * ‖y - x‖

theorem measurableSet_dimensionCausalFuture {n : ℕ} (x : DimensionSpacetime n) :
    MeasurableSet (dimensionCausalFuture x) :=
  (isClosed_le (continuous_snd.sub continuous_const).norm
    (continuous_fst.sub continuous_const)).measurableSet

theorem continuous_dimensionIntervalSq {n : ℕ} :
    Continuous (fun p : DimensionSpacetime n × DimensionSpacetime n =>
      dimensionIntervalSq p.1 p.2) := by
  unfold dimensionIntervalSq
  fun_prop

namespace DimensionGraphCapData

variable {n : ℕ} {h : DimensionSpatial n → ℝ} (hh : DimensionGraphCapData h)
include hh

theorem continuous_positivePart : Continuous (fun x => max 0 (h x)) := by
  obtain ⟨κ, hκ, _, hLip⟩ := hh.lipschitz_positivePart
  have hl : LipschitzWith ⟨κ, hκ⟩ (fun x => max 0 (h x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using hLip x y
  exact hl.continuous

theorem measurableSet_positive : MeasurableSet {x | 0 < h x} := by
  have he : {x | 0 < h x} = {x | 0 < max 0 (h x)} := by ext x; simp
  rw [he]
  exact (isOpen_lt continuous_const hh.continuous_positivePart).measurableSet

omit hh in
theorem cap_eq_positivePart : dimensionGraphCap h =
    {p : DimensionSpacetime n | -max 0 (h p.2) < p.1 ∧ p.1 < 0} := by
  ext p
  constructor
  · rintro ⟨hp, ht⟩
    have hpos : 0 < h p.2 := by linarith
    simpa only [mem_setOf_eq, max_eq_right hpos.le] using And.intro hp ht
  · rintro ⟨hp, ht⟩
    have hpos : 0 < h p.2 := by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn)] at hp
      linarith
    simpa only [dimensionGraphCap, mem_setOf_eq, max_eq_right hpos.le] using And.intro hp ht

theorem measurableSet_cap : MeasurableSet (dimensionGraphCap h) := by
  rw [cap_eq_positivePart]
  exact ((isOpen_lt (hh.continuous_positivePart.comp continuous_snd).neg continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).measurableSet

/-- One compact product dominates the entire cap before any signed Fubini. -/
theorem cap_subset_compact : ∃ K : Set (DimensionSpacetime n),
    IsCompact K ∧ dimensionGraphCap h ⊆ K := by
  obtain ⟨H, hH⟩ := (hh.bounded_positive.isCompact_closure.image
    hh.continuous_positivePart).isBounded.exists_norm_le
  refine ⟨Icc (-H) 0 ×ˢ closure {x | 0 < h x},
    isCompact_Icc.prod hh.bounded_positive.isCompact_closure, ?_⟩
  intro p hp
  have hpos : 0 < h p.2 := by have := hp.1; have := hp.2; linarith
  have ht := hH _ ⟨p.2, subset_closure hpos, rfl⟩
  dsimp only at ht
  rw [Real.norm_eq_abs, max_eq_right hpos.le, abs_of_pos hpos] at ht
  exact ⟨⟨by have := hp.1; linarith, hp.2.le⟩, subset_closure hpos⟩

theorem isBounded_cap : Bornology.IsBounded (dimensionGraphCap h) := by
  obtain ⟨K, hK, hsub⟩ := hh.cap_subset_compact
  exact hK.isBounded.subset hsub

theorem integrableOn_cap (f : DimensionSpacetime n → ℝ) (hf : Continuous f) :
    IntegrableOn f (dimensionGraphCap h) := by
  obtain ⟨K, hK, hsub⟩ := hh.cap_subset_compact
  exact (hf.continuousOn.integrableOn_compact hK).mono_set hsub

/-- This elementary future-set argument includes null displacements. -/
theorem complete_future (x : DimensionSpacetime n) (hx : x ∈ dimensionGraphCap h) :
    dimensionGraphCap h ∩ dimensionCausalFuture x =
      {y | y ∈ dimensionCausalFuture x ∧ y.1 < 0} := by
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hh.lipschitz_positivePart
  rw [cap_eq_positivePart] at hx ⊢
  ext y
  constructor
  · intro hy
    exact ⟨hy.2, hy.1.2⟩
  · rintro ⟨hxy, hy0⟩
    have hd : ‖y.2 - x.2‖ ≤ y.1 - x.1 := hxy
    have ht : 0 ≤ y.1 - x.1 := (norm_nonneg _).trans hd
    have hl := (abs_le.mp (hLip x.2 y.2)).2
    have hk := mul_le_mul_of_nonneg_left hd hκ
    have hk' := mul_le_of_le_one_left ht hκ1.le
    exact ⟨⟨by have := hx.1; linarith, hy0⟩, hxy⟩

end DimensionGraphCapData

/-- Continuous nonnegative compactly supported Lipschitz regulators supply
actual examples without changing any existing geometric admissibility class. -/
theorem dimensionGraphCapData_of_nonnegative {n : ℕ} (h : DimensionSpatial n → ℝ)
    (hs : HasCompactSupport h) (hn : ∀ x, 0 ≤ h x) (κ : ℝ)
    (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hLip : ∀ x y, |h x - h y| ≤ κ * ‖y - x‖) :
    DimensionGraphCapData h := by
  refine ⟨hs.isCompact.isBounded.subset ?_, κ, hκ, hκ1, ?_⟩
  · intro x hx
    exact subset_closure (show x ∈ Function.support h from ne_of_gt hx)
  · intro x y
    simpa only [max_eq_right (hn x), max_eq_right (hn y)] using hLip x y

end BoundaryDraft
