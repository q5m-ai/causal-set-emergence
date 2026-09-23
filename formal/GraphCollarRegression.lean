import BoundaryDraft

/-!
Independent contracts for the compact-joint/noncritical-band prerequisite of
issue #19. These do not assert a coarea identity or a general limit theorem.
-/

open BoundaryDraft MeasureTheory Set
noncomputable section

-- Restate the band contract without using the closed-positive-set abbreviation.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin 3),
      x ∈ closure {y : EuclideanSpace ℝ (Fin 3) | 0 < h y} →
      0 ≤ h x → h x ≤ δ →
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => h y) x ≠ 0 := by
  obtain ⟨δ, hδ, hband⟩ := hh.exists_noncritical_band
  exact ⟨δ, hδ, fun x hx _ hs => hband x hx hs⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    IsCompact (closure {x : EuclideanSpace ℝ (Fin 3) | 0 < h x} ∩ {x | h x = 0}) :=
  hh.isCompact_joint

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ graphJoint h) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U ∧ x ∈ U ∧
      ContDiffOn ℝ 3 (fun y : EuclideanSpace ℝ (Fin 3) => h y) U ∧
      ∀ y ∈ U, fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => h z) y ≠ 0 :=
  hh.exists_regular_neighborhood x hx.1 (hh.regular_zero x hx.1 hx.2)

-- A raw zero level can be huge without being part of the joint.
example : graphJoint (fun _ : Spatial => (0 : ℝ)) = ∅ := by
  simp [graphJoint, graphClosedPositive]

-- No stronger hypotheses are imposed on the original unequal-axis family.
example : ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ closure {y : EuclideanSpace ℝ (Fin 3) |
      0 < ellipsoidProfile (1 / 4) ![1, 2, 3] y},
      ellipsoidProfile (1 / 4) ![1, 2, 3] x ≤ δ →
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        ellipsoidProfile (1 / 4) ![1, 2, 3] y) x ≠ 0 := by
  apply (ellipsoid_admissible _ _ (by norm_num) ?_).exists_noncritical_band
  intro i
  fin_cases i <;> norm_num
