import BoundaryDraft

/-!
A nonempty cap with an irrelevant exterior zero half-space. Its raw height
jumps at x₀ = 2, but its causal envelope is the original ellipsoid envelope.
All original admissibility fields are proved; none is weakened or added.
-/

open BoundaryDraft Set Filter
open scoped Topology

noncomputable section
namespace TwoFaceExteriorRegression

def unitHeight : Spatial → ℝ := ellipsoidProfile (1 / 4) (fun _ => 1)

def exteriorHeight (x : Spatial) : ℝ := if x 0 < 2 then unitHeight x else 0

theorem unit_admissible : AdmissibleGraphCap unitHeight :=
  ellipsoid_admissible _ _ (by norm_num) (fun _ => by norm_num)

theorem positivePart_eq (x : Spatial) : max 0 (exteriorHeight x) = max 0 (unitHeight x) := by
  by_cases hx : x 0 < 2
  · simp [exteriorHeight, hx]
  · have hn : unitHeight x ≤ 0 := by
      apply le_of_not_gt
      intro hp
      have hb := (ellipsoid_positive_subset_box (1 / 4) (fun _ => 1)
        (by norm_num) (fun _ => by norm_num) hp).2 0
      exact hx (lt_of_le_of_lt hb (by norm_num))
    simp [exteriorHeight, hx, max_eq_left hn]

theorem positive_iff (x : Spatial) : 0 < exteriorHeight x ↔ 0 < unitHeight x := by
  have he := positivePart_eq x
  have hh : 0 < max 0 (exteriorHeight x) ↔ 0 < max 0 (unitHeight x) := by rw [he]
  simpa using hh

theorem positive_eq : {x : Spatial | 0 < exteriorHeight x} = {x | 0 < unitHeight x} := by
  ext x
  exact positive_iff x

theorem closedPositive_eq : graphClosedPositive exteriorHeight = graphClosedPositive unitHeight := by
  unfold graphClosedPositive
  apply congrArg closure
  ext x
  exact positive_iff x

theorem closed_x0 {x : Spatial} (hx : x ∈ closure {y : Spatial | 0 < unitHeight y}) : x 0 ≤ 1 := by
  have hb : {y : Spatial | 0 < unitHeight y} ⊆ {y | y 0 ≤ 1} := by
    intro y hy
    exact (ellipsoid_positive_subset_box (1 / 4) (fun _ => 1)
      (by norm_num) (fun _ => by norm_num) hy).2 0
  exact closure_minimal hb (isClosed_le (continuous_apply 0) continuous_const) hx

theorem euclidean_closed_x0 {x : JointSpace} (hx : x ∈ graphClosedPositive unitHeight) : x 0 ≤ 1 := by
  have hb : {y : JointSpace | 0 < unitHeight y} ⊆ {y | y 0 ≤ 1} := by
    intro y hy
    exact (ellipsoid_positive_subset_box (1 / 4) (fun _ => 1)
      (by norm_num) (fun _ => by norm_num) hy).2 0
  exact closure_minimal hb (isClosed_le
    ((continuous_apply 0).comp (PiLp.continuous_equiv 2 _)) continuous_const) hx

theorem height_germ {x : JointSpace} (hx : x ∈ graphClosedPositive unitHeight) :
    (fun y : JointSpace => exteriorHeight y) =ᶠ[𝓝 x] (fun y => unitHeight y) := by
  have ho : IsOpen {y : JointSpace | y 0 < 2} := isOpen_lt
    ((continuous_apply 0).comp (PiLp.continuous_equiv 2 _)) continuous_const
  filter_upwards [ho.mem_nhds (lt_of_le_of_lt (euclidean_closed_x0 hx) (by norm_num))] with y hy
  exact if_pos hy

theorem exterior_admissible : AdmissibleGraphCap exteriorHeight where
  bounded_positive := by rw [positive_eq]; exact unit_admissible.bounded_positive
  lipschitz_positivePart := by
    obtain ⟨κ, hk, hk1, hl⟩ := unit_admissible.lipschitz_positivePart
    exact ⟨κ, hk, hk1, fun x y => by simpa only [positivePart_eq] using hl x y⟩
  smooth_near := by
    intro x hx
    change x ∈ graphClosedPositive exteriorHeight at hx
    rw [closedPositive_eq] at hx
    exact (unit_admissible.smooth_near x hx).congr_of_eventuallyEq (height_germ hx)
  boundary_zero := by
    intro x hx
    rw [positive_eq] at hx
    have hl : x 0 < 2 := lt_of_le_of_lt (closed_x0 (frontier_subset_closure hx)) (by norm_num)
    simpa only [exteriorHeight, if_pos hl] using unit_admissible.boundary_zero x hx
  regular_zero := by
    intro x hx hz
    change x ∈ graphClosedPositive exteriorHeight at hx
    rw [closedPositive_eq] at hx
    rw [(height_germ hx).fderiv_eq]
    have he : exteriorHeight x = unitHeight x := (height_germ hx).self_of_nhds
    exact unit_admissible.regular_zero x hx (he.symm.trans hz)

-- Nonempty geometry and the original expectation bridge hold despite that
-- exterior behavior. The future face need not be planar either.
example : ∃ c : ℝ, 0 < c ∧ AdmissibleTwoFace exteriorHeight (twoFaceSine c) ∧
    (twoFaceRegion exteriorHeight (twoFaceSine c)).Nonempty ∧
    BoundedCausalRegion (twoFaceRegion exteriorHeight (twoFaceSine c)) ∧
    ∀ ρ : ℝ, 0 < ρ → expectedBDGAction ρ (twoFaceRegion exteriorHeight (twoFaceSine c)) =
      continuumMean ρ (twoFaceRegion exteriorHeight (twoFaceSine c)) := by
  obtain ⟨c, hc, hf⟩ := exterior_admissible.exists_twoFace_sine
  refine ⟨c, hc, hf, ?_, hf.boundedCausalRegion, fun _ hρ => hf.expectedBDGAction_eq hρ⟩
  exact ⟨Fin.cons (-1 / 8) 0, by
    norm_num [twoFaceRegion, spatialPart_cons, twoFaceSine, exteriorHeight, unitHeight, ellipsoidProfile]⟩

-- An entire exterior half-space is zero, not an unrecorded boundary stratum.
example {f : Spatial → ℝ} (hf : AdmissibleTwoFace exteriorHeight f)
    (x : JointSpace) (hx : 2 ≤ x 0) :
    exteriorHeight x = 0 ∧ twoFaceLift f x ∉ closure (twoFaceRegion exteriorHeight f) ∧
    twoFaceLift f x ∉ twoFaceJoint exteriorHeight f := by
  have hn : x ∉ graphClosedPositive exteriorHeight := by
    rw [closedPositive_eq]
    intro hm
    have := euclidean_closed_x0 hm
    linarith
  refine ⟨if_neg (not_lt_of_ge hx), ?_, ?_⟩
  · intro hp
    exact hn ((hf.mem_closure_region _).mp hp).1
  · intro hp
    exact hn ((mem_twoFaceLift_image f (graphJoint exteriorHeight) _).mp hp).1.1

-- Exact compatibility is preserved through the positive-part envelope even
-- where the two raw heights disagree.
example (f : Spatial → ℝ) : twoFaceRegion exteriorHeight f = twoFaceRegion unitHeight f := by
  rw [twoFaceRegion_eq_envelopes, twoFaceRegion_eq_envelopes]
  simp only [positivePart_eq]

end TwoFaceExteriorRegression
