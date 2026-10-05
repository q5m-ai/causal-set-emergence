import BoundaryDraft.TwoDLine

/-! # Derived finite interval decomposition with the complete regular frontier

The construction is geometric, retaining every interval and every endpoint.
It asserts no bilocal additivity and makes no assumption on interior gradients.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDComponents

/-- A bounded open real set has an entire interval through each of its points,
with BOTH endpoints in its frontier. No connectedness assumption is made. -/
theorem exists_interval {U : Set ℝ} (ho : IsOpen U) (hb : Bornology.IsBounded U)
    {x : ℝ} (hx : x ∈ U) :
    ∃ a b : ℝ, a ∈ frontier U ∧ b ∈ frontier U ∧ a < x ∧ x < b ∧ Ioo a b ⊆ U := by
  classical
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hb
  have hxR : -R < x ∧ x < R := by
    have := hR hx
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using this
  have hR0 : 0 < R := by linarith [hxR.1, hxR.2]
  have hn (y : ℝ) (hy : y = -R ∨ y = R) : y ∉ U := by
    intro hyU
    have hyR := hR hyU
    rcases hy with rfl | rfl <;> simp [Metric.mem_ball, Real.dist_eq, abs_of_pos hR0] at hyR
  obtain ⟨a, ha, hmax⟩ := (isCompact_Icc.inter_right ho.isClosed_compl).exists_isGreatest
    (show (Icc (-R) x ∩ Uᶜ).Nonempty from ⟨-R, ⟨⟨le_rfl, hxR.1.le⟩, hn _ (Or.inl rfl)⟩⟩)
  obtain ⟨b, hb', hmin⟩ := (isCompact_Icc.inter_right ho.isClosed_compl).exists_isLeast
    (show (Icc x R ∩ Uᶜ).Nonempty from ⟨R, ⟨⟨hxR.2.le, le_rfl⟩, hn _ (Or.inr rfl)⟩⟩)
  have hax : a < x := lt_of_le_of_ne ha.1.2 (fun he => ha.2 (he.symm ▸ hx))
  have hxb : x < b := lt_of_le_of_ne hb'.1.1 (fun he => hb'.2 (he ▸ hx))
  have hab : a < b := hax.trans hxb
  have hsub : Ioo a b ⊆ U := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact hyU
    exfalso
    by_cases hyx : y ≤ x
    · have := hmax (show y ∈ Icc (-R) x ∩ Uᶜ from ⟨⟨ha.1.1.trans hy.1.le, hyx⟩, hyU⟩)
      linarith [hy.1]
    · have := hmin (show y ∈ Icc x R ∩ Uᶜ from ⟨⟨(not_le.mp hyx).le, hy.2.le.trans hb'.1.2⟩, hyU⟩)
      linarith [hy.2]
  have hcl : Icc a b ⊆ closure U := by
    rw [← closure_Ioo hab.ne]
    exact closure_mono hsub
  refine ⟨a, b, ?_, ?_, hax, hxb, hsub⟩ <;> rw [ho.frontier_eq]
  · exact ⟨hcl ⟨le_rfl, hab.le⟩, ha.2⟩
  · exact ⟨hcl ⟨hab.le, le_rfl⟩, hb'.2⟩

/-- Finite, pairwise disjoint interval decomposition with the complete frontier.
This is a geometric decomposition, NOT bilocal action additivity. -/
theorem finite_intervals {U : Set ℝ} (ho : IsOpen U) (hb : Bornology.IsBounded U)
    (hj : (frontier U).Finite) :
    ∃ P : Finset (ℝ × ℝ),
      (∀ p ∈ P, p.1 < p.2 ∧ p.1 ∈ frontier U ∧ p.2 ∈ frontier U) ∧
      U = ⋃ p ∈ P, Ioo p.1 p.2 ∧
      (P : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2) ∧
      frontier U = ⋃ p ∈ P, ({p.1, p.2} : Set ℝ) := by
  classical
  let P := (hj.toFinset.product hj.toFinset).filter
    (fun p : ℝ × ℝ => p.1 < p.2 ∧ Ioo p.1 p.2 ⊆ U)
  have hmem (p : ℝ × ℝ) : p ∈ P ↔
      p.1 ∈ frontier U ∧ p.2 ∈ frontier U ∧ p.1 < p.2 ∧ Ioo p.1 p.2 ⊆ U := by
    rcases p with ⟨a, b⟩
    simp [P, and_assoc]
  have hends (p : ℝ × ℝ) (hp : p ∈ P) : p.1 ∉ U ∧ p.2 ∉ U := by
    have h := hmem p |>.mp hp
    rw [ho.frontier_eq] at h
    exact ⟨h.1.2, h.2.1.2⟩
  have he : U = ⋃ p ∈ P, Ioo p.1 p.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, b, ha, hb, hax, hxb, hs⟩ := exists_interval ho hb hx
      exact mem_iUnion₂.mpr ⟨(a, b), (hmem _).mpr ⟨ha, hb, hax.trans hxb, hs⟩, hax, hxb⟩
    · intro hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
      exact (hmem p |>.mp hp).2.2.2 hxp
  refine ⟨P, fun p hp => ⟨(hmem p |>.mp hp).2.2.1, (hmem p |>.mp hp).1,
    (hmem p |>.mp hp).2.1⟩, he, ?_, ?_⟩
  · intro p hp q hq hpq
    apply disjoint_left.mpr
    intro y hyp hyq
    have hl : p.1 = q.1 := by
      rcases lt_trichotomy p.1 q.1 with hl | he | hr
      · exact False.elim ((hends q hq).1 ((hmem p |>.mp hp).2.2.2 ⟨hl, hyq.1.trans hyp.2⟩))
      · exact he
      · exact False.elim ((hends p hp).1 ((hmem q |>.mp hq).2.2.2 ⟨hr, hyp.1.trans hyq.2⟩))
    have hr : p.2 = q.2 := by
      rcases lt_trichotomy p.2 q.2 with hl | he | hr
      · exact False.elim ((hends p hp).2 ((hmem q |>.mp hq).2.2.2 ⟨hyq.1.trans hyp.2, hl⟩))
      · exact he
      · exact False.elim ((hends q hq).2 ((hmem p |>.mp hp).2.2.2 ⟨hyp.1.trans hyq.2, hr⟩))
    exact hpq (Prod.ext hl hr)
  · ext x
    constructor
    · intro hx
      have hxc := frontier_subset_closure hx
      rw [he, Finset.closure_biUnion] at hxc
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxc
      have hab := (hmem p |>.mp hp).2.2.1
      rw [closure_Ioo hab.ne] at hxp
      have hn : x ∉ U := by rw [ho.frontier_eq] at hx; exact hx.2
      have hend : x = p.1 ∨ x = p.2 := by
        by_cases ha : x = p.1
        · exact Or.inl ha
        · right
          by_cases hb' : x = p.2
          · exact hb'
          exact False.elim (hn ((hmem p |>.mp hp).2.2.2
            ⟨lt_of_le_of_ne hxp.1 (Ne.symm ha), lt_of_le_of_ne hxp.2 hb'⟩))
      exact mem_iUnion₂.mpr ⟨p, hp, by simpa using hend⟩
    · intro hx
      obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp hx
      rcases hx with rfl | hx
      · exact (hmem p |>.mp hp).1
      · have hx : x = p.2 := hx
        rw [hx]
        exact (hmem p |>.mp hp).2.1

end TwoDComponents

def twoDPositiveLine (h : TwoDSpace → ℝ) : Set ℝ := twoDLine '' {x | 0 < h x}

theorem mem_twoDPositiveLine (h : TwoDSpace → ℝ) (s : ℝ) :
    s ∈ twoDPositiveLine h ↔ 0 < h (twoDLine.symm s) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [twoDLine.symm_apply_apply] using hx
  · intro hx
    exact ⟨twoDLine.symm s, hx, twoDLine.apply_symm_apply s⟩

/-- Complete finite interval geometry, not a componentwise action contract. -/
structure TwoDIntervalFamily (h : TwoDSpace → ℝ) where
  intervals : Finset (ℝ × ℝ)
  ordered : ∀ p ∈ intervals, p.1 < p.2
  ends : ∀ p ∈ intervals,
    p.1 ∈ twoDLine '' dimensionTwoSpatialJoint h ∧ p.2 ∈ twoDLine '' dimensionTwoSpatialJoint h
  positive : twoDPositiveLine h = ⋃ p ∈ intervals, Ioo p.1 p.2
  disjoint : (intervals : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2)
  all_endpoints : twoDLine '' dimensionTwoSpatialJoint h = ⋃ p ∈ intervals, ({p.1, p.2} : Set ℝ)

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem frontier_positiveLine : frontier (twoDPositiveLine h) = twoDLine '' dimensionTwoSpatialJoint h := by
  rw [hf.joint_eq_frontier]
  exact (twoDLine.toHomeomorph.image_frontier _).symm

/-- Derived solely from the unchanged smooth contract; empty families and
arbitrarily many disconnected components are allowed. -/
theorem exists_intervalFamily : Nonempty (TwoDIntervalFamily h) := by
  have ho : IsOpen (twoDPositiveLine h) := twoDLine.toHomeomorph.isOpenMap _ hf.isOpen_positive
  have hb : Bornology.IsBounded (twoDPositiveLine h) :=
    twoDLine.isometry.lipschitz.isBounded_image hf.bounded_positive
  have hj : (frontier (twoDPositiveLine h)).Finite := by
    rw [hf.frontier_positiveLine]
    exact hf.joint_finite.image twoDLine
  obtain ⟨P, hP, he, hd, hj⟩ := TwoDComponents.finite_intervals ho hb hj
  rw [hf.frontier_positiveLine] at hP hj
  exact ⟨⟨P, fun p hp => (hP p hp).1, fun p hp => (hP p hp).2, he, hd, hj⟩⟩

end SmoothTwoD
end BoundaryDraft
