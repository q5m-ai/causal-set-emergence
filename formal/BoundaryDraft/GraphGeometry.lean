import BoundaryDraft.Specification
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Admissible spacelike graph caps

`GraphCapData` contains only the bounded-support and strict Euclidean
positive-part Lipschitz assumptions used by the exact action reduction.
`GraphCapRegularity` records the separate C³/regular-boundary assumptions for
future collar work. In particular it imposes no condition on the differential
at positive height. Neither structure assumes any integral identity or limit.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

/-- Euclidean spatial distance, compatible with `spatialSeparationSq`. -/
def spatialDistance (x y : Spatial) : ℝ :=
  ‖((WithLp.equiv 2 _).symm (y - x) : EuclideanSpace ℝ (Fin 3))‖

theorem spatialDistance_nonneg (x y : Spatial) : 0 ≤ spatialDistance x y :=
  norm_nonneg _

theorem spatialDistance_sq (x y : Spatial) :
    spatialDistance x y ^ 2 = ∑ i : Fin 3, (y i - x i) ^ 2 := by
  simp [spatialDistance, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]

theorem spatialDistance_symm (x y : Spatial) :
    spatialDistance x y = spatialDistance y x := by
  apply (sq_eq_sq₀ (spatialDistance_nonneg _ _) (spatialDistance_nonneg _ _)).mp
  simp only [spatialDistance_sq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The reduction needs no smoothness of the raw profile outside its positive
set, and allows nonsmooth caps as well as all the regular caps below. -/
structure GraphCapData (h : Spatial → ℝ) : Prop where
  bounded_positive : Bornology.IsBounded {x | 0 < h x}
  lipschitz_positivePart : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ x y : Spatial,
    |max 0 (h x) - max 0 (h y)| ≤ κ * spatialDistance x y

/-- Additional assumptions reserved for a later regular-collar theorem.
C³ is required locally at the closed positive region in Euclidean coordinates.
The joint is the zero level *in that closure*, not unrelated exterior zeros.
Nonvanishing is required only there, never at positive-height critical points. -/
structure GraphCapRegularity (h : Spatial → ℝ) : Prop where
  smooth_near : ∀ x ∈ closure {x : EuclideanSpace ℝ (Fin 3) | 0 < h x},
    ContDiffAt ℝ 3 (fun y : EuclideanSpace ℝ (Fin 3) => h y) x
  boundary_zero : ∀ x ∈ frontier {x : Spatial | 0 < h x}, h x = 0
  regular_zero : ∀ x ∈ closure {x : EuclideanSpace ℝ (Fin 3) | 0 < h x},
    h x = 0 → fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => h y) x ≠ 0

/-- The draft's admissible class, with reduction and collar data separated. -/
structure AdmissibleGraphCap (h : Spatial → ℝ) : Prop
    extends GraphCapData h, GraphCapRegularity h

namespace GraphCapData

variable {h : Spatial → ℝ} (hh : GraphCapData h)
include hh

/-- Convert Euclidean control to continuity in the original coordinate topology. -/
theorem continuous_positivePart : Continuous (fun x => max 0 (h x)) := by
  obtain ⟨κ, hκ, _, hLip⟩ := hh.lipschitz_positivePart
  have hl : LipschitzWith ⟨κ, hκ⟩
      (fun x : EuclideanSpace ℝ (Fin 3) => max 0 (h x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |max 0 (h x) - max 0 (h y)| ≤ κ * ‖x - y‖
    have he := hLip x y
    change |max 0 (h x) - max 0 (h y)| ≤ κ * ‖y - x‖ at he
    simpa only [norm_sub_rev] using he
  exact hl.continuous.comp (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ))

theorem isOpen_positive : IsOpen {x | 0 < h x} := by
  have he : {x | 0 < h x} = {x | 0 < max 0 (h x)} := by
    ext x
    simp
  rw [he]
  exact isOpen_lt continuous_const hh.continuous_positivePart

theorem measurableSet_positive : MeasurableSet {x | 0 < h x} :=
  hh.isOpen_positive.measurableSet

theorem hasCompactSupport_positivePart : HasCompactSupport (fun x => max 0 (h x)) := by
  apply HasCompactSupport.intro hh.bounded_positive.isCompact_closure
  intro x hx
  exact max_eq_left (le_of_not_gt fun hp => hx (subset_closure hp))

omit hh in
/-- Strict cap membership only depends on the positive part of the profile. -/
theorem cap_eq_positivePart : graphCapRegion h =
    {p | -max 0 (h (spatialPart p)) < p 0 ∧ p 0 < 0} := by
  ext p
  change (-h (spatialPart p) < p 0 ∧ p 0 < 0) ↔ _
  constructor
  · rintro ⟨hp, ht⟩
    have hpos : 0 < h (spatialPart p) := by linarith
    simpa only [mem_setOf_eq, max_eq_right hpos.le] using And.intro hp ht
  · rintro ⟨hp, ht⟩
    have hpos : 0 < h (spatialPart p) := by
      by_cases hn : 0 < h (spatialPart p)
      · exact hn
      · rw [max_eq_left (le_of_not_gt hn)] at hp
        linarith
    simpa only [max_eq_right hpos.le] using And.intro hp ht

theorem isOpen_positivePart_epigraph :
    IsOpen {p : Spacetime | -max 0 (h (spatialPart p)) < p 0} := by
  have hc : Continuous spatialPart := by unfold spatialPart; fun_prop
  exact isOpen_lt (hh.continuous_positivePart.comp hc).neg (continuous_apply 0)

theorem isOpen_cap : IsOpen (graphCapRegion h) := by
  rw [cap_eq_positivePart]
  exact hh.isOpen_positivePart_epigraph.inter
    (isOpen_lt (continuous_apply 0) continuous_const)

theorem measurableSet_cap : MeasurableSet (graphCapRegion h) :=
  hh.isOpen_cap.measurableSet

/-- A compact coordinate box dominates the cap, including all vertical fibres. -/
theorem cap_subset_box : ∃ R : ℝ, graphCapRegion h ⊆
    Icc (fun _ => -R) (fun _ => R) := by
  obtain ⟨R, hR⟩ := hh.bounded_positive.exists_norm_le
  obtain ⟨H, hH⟩ := (hh.bounded_positive.isCompact_closure.image
    hh.continuous_positivePart).isBounded.exists_norm_le
  refine ⟨max R H, ?_⟩
  intro p hp
  have hpos : 0 < h (spatialPart p) := by have := hp.1; have := hp.2; linarith
  have hs := hR _ hpos
  have ht := hH _ ⟨spatialPart p, subset_closure hpos, rfl⟩
  change ‖max 0 (h (spatialPart p))‖ ≤ H at ht
  rw [Real.norm_eq_abs, max_eq_right hpos.le, abs_of_pos hpos] at ht
  have hH0 : 0 < max R H := lt_of_lt_of_le (hpos.trans_le ht) (le_max_right _ _)
  constructor <;> intro i
  · refine Fin.cases ?_ (fun j => ?_) i
    · have := hp.1
      change -max R H ≤ p 0
      linarith [le_max_right R H]
    · have hj := norm_le_pi_norm (spatialPart p) j
      rw [Real.norm_eq_abs] at hj
      exact (neg_le_neg (le_max_left R H)).trans
        ((neg_le_neg hs).trans (abs_le.mp hj).1)
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact hp.2.le.trans hH0.le
    · have hj := norm_le_pi_norm (spatialPart p) j
      rw [Real.norm_eq_abs] at hj
      exact (abs_le.mp hj).2.trans (hs.trans (le_max_left _ _))

theorem isBounded_cap : Bornology.IsBounded (graphCapRegion h) := by
  obtain ⟨R, hR⟩ := hh.cap_subset_box
  exact (isCompact_Icc : IsCompact (Icc (fun _ : Fin 4 => -R) (fun _ => R))).isBounded.subset hR

end GraphCapData

/-- The zero level in the closed positive region is exactly its boundary. -/
theorem AdmissibleGraphCap.frontier_eq (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    frontier {x | 0 < h x} = closure {x | 0 < h x} ∩ {x | h x = 0} := by
  rw [hh.toGraphCapData.isOpen_positive.frontier_eq]
  ext x
  constructor
  · rintro ⟨hc, hn⟩
    exact ⟨hc, hh.boundary_zero x (by
      rw [hh.toGraphCapData.isOpen_positive.frontier_eq]
      exact ⟨hc, hn⟩)⟩
  · rintro ⟨hc, hz⟩
    exact ⟨hc, by change ¬0 < h x; rw [show h x = 0 from hz]; exact lt_irrefl _⟩

/-- The squared causal inequality controls the Euclidean spatial distance. -/
theorem spatialDistance_le_of_causalFuture (x y : Spacetime) (hxy : y ∈ causalFuture x) :
    spatialDistance (spatialPart x) (spatialPart y) ≤ y 0 - x 0 := by
  apply (sq_le_sq₀ (spatialDistance_nonneg _ _) (sub_nonneg.mpr hxy.1)).mp
  simpa only [spatialDistance_sq, spatialPart, spatialSeparationSq] using hxy.2

/-- The positive-part epigraph is a future set, including null displacements. -/
theorem positivePart_epigraph_future (h : Spatial → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hLip : ∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * spatialDistance x y)
    (x y : Spacetime) (hx : -max 0 (h (spatialPart x)) < x 0)
    (hxy : y ∈ causalFuture x) : -max 0 (h (spatialPart y)) < y 0 := by
  have hd := spatialDistance_le_of_causalFuture x y hxy
  have hl := (abs_le.mp (hLip (spatialPart x) (spatialPart y))).2
  have hk := mul_le_mul_of_nonneg_left hd hκ
  have hk' := mul_le_of_le_one_left (sub_nonneg.mpr hxy.1) hκ1
  linarith

/-- Exact complete cone slice. The vertex and null surface are not removed. -/
theorem graphCap_complete_future (h : Spatial → ℝ) (hh : GraphCapData h)
    (x : Spacetime) (hx : x ∈ graphCapRegion h) :
    graphCapRegion h ∩ causalFuture x = {y | y ∈ causalFuture x ∧ y 0 < 0} := by
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hh.lipschitz_positivePart
  rw [GraphCapData.cap_eq_positivePart] at hx ⊢
  ext y
  exact ⟨fun hy => ⟨hy.2, hy.1.2⟩, fun ⟨hxy, hy0⟩ =>
    ⟨⟨positivePart_epigraph_future h κ hκ hκ1.le hLip x y hx.1 hxy, hy0⟩, hxy⟩⟩

theorem graphCap_causallyConvex (h : Spatial → ℝ) (hh : GraphCapData h)
    (x y z : Spacetime) (hx : x ∈ graphCapRegion h) (hz : z ∈ graphCapRegion h)
    (hxy : y ∈ causalFuture x) (hyz : z ∈ causalFuture y) :
    y ∈ graphCapRegion h := by
  have hy : y ∈ {y | y ∈ causalFuture x ∧ y 0 < 0} :=
    ⟨hxy, lt_of_le_of_lt hyz.1 hz.2⟩
  rw [← graphCap_complete_future h hh x hx] at hy
  exact hy.1

end BoundaryDraft
