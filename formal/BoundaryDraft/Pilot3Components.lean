import BoundaryDraft.Pilot3Geometry

/-!
# All-component and irrelevant-exterior controls

These are set-level identities. They do NOT assert additivity of the bilocal
action, which retains cross-component pairs, nor infer smoothness of a raw
maximum on arbitrary overlaps.
-/

open Set
noncomputable section
namespace BoundaryDraft

theorem pilot3Region_max (h₁ h₂ f : Pilot3Space → ℝ) :
    pilot3Region (fun x => max (h₁ x) (h₂ x)) f = pilot3Region h₁ f ∪ pilot3Region h₂ f := by
  ext p
  change (_ < _ ∧ _ < _) ↔ (_ < _ ∧ _ < _) ∨ (_ < _ ∧ _ < _)
  dsimp only
  by_cases hh : h₁ p.2 ≤ h₂ p.2
  · rw [max_eq_right hh]
    constructor
    · exact Or.inr
    · rintro (hp | hp)
      · exact ⟨by have := hp.1; linarith, hp.2⟩
      · exact hp
  · rw [max_eq_left (le_of_not_ge hh)]
    constructor
    · exact Or.inl
    · rintro (hp | hp)
      · exact hp
      · exact ⟨by have := hp.1; linarith, hp.2⟩

theorem pilot3ClosedPositive_max (h₁ h₂ : Pilot3Space → ℝ) :
    pilot3ClosedPositive (fun x => max (h₁ x) (h₂ x)) =
      pilot3ClosedPositive h₁ ∪ pilot3ClosedPositive h₂ := by
  simp only [pilot3ClosedPositive, lt_max_iff, setOf_or, closure_union]

/-- Both whole joints of separated components are retained, not one sheet. -/
theorem pilot3SpatialJoint_max {h₁ h₂ : Pilot3Space → ℝ}
    (hh₁ : Pilot3RegularHeight h₁) (hh₂ : Pilot3RegularHeight h₂)
    (hd : Disjoint (pilot3ClosedPositive h₁) (pilot3ClosedPositive h₂)) :
    pilot3SpatialJoint (fun x => max (h₁ x) (h₂ x)) =
      pilot3SpatialJoint h₁ ∪ pilot3SpatialJoint h₂ := by
  have hdis := Set.disjoint_left.mp hd
  have hother₁ (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h₁) : h₂ x ≤ 0 := by
    by_contra hn
    exact hdis hx (subset_closure (show x ∈ {x | 0 < h₂ x} from lt_of_not_ge hn))
  have hother₂ (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h₂) : h₁ x ≤ 0 := by
    by_contra hn
    exact hdis (subset_closure (show x ∈ {x | 0 < h₁ x} from lt_of_not_ge hn)) hx
  ext x
  simp only [pilot3SpatialJoint, pilot3ClosedPositive_max, mem_inter_iff, mem_union, mem_setOf_eq]
  constructor
  · rintro ⟨hx | hx, hz⟩
    · exact Or.inl ⟨hx, le_antisymm ((le_max_left _ _).trans hz.le)
        (hh₁.nonneg_on_closedPositive x hx)⟩
    · exact Or.inr ⟨hx, le_antisymm ((le_max_right _ _).trans hz.le)
        (hh₂.nonneg_on_closedPositive x hx)⟩
  · rintro (⟨hx, hz⟩ | ⟨hx, hz⟩)
    · exact ⟨Or.inl hx, by rw [hz, max_eq_left (hother₁ x hx)]⟩
    · exact ⟨Or.inr hx, by rw [hz, max_eq_right (hother₂ x hx)]⟩

/-- The region is insensitive to ALL raw nonpositive exterior values. -/
theorem pilot3Region_eq_of_positivePart_eq {h k f : Pilot3Space → ℝ}
    (he : ∀ x, max 0 (h x) = max 0 (k x)) : pilot3Region h f = pilot3Region k f := by
  rw [pilot3Region_eq_envelopes, pilot3Region_eq_envelopes]
  simp_rw [he]

/-- Raw exterior zeros outside the closed positive set never create a joint. -/
theorem pilot3SpatialJoint_excludes_exterior {h : Pilot3Space → ℝ} {x : Pilot3Space}
    (hx : x ∉ pilot3ClosedPositive h) : x ∉ pilot3SpatialJoint h := fun hJ => hx hJ.1

end BoundaryDraft
