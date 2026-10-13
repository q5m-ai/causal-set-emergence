import BoundaryDraft.CompactTorus
import BoundaryDraft.DimensionIntervalVolume

/-!
# Causal lifting in a thin cubic quotient slab

The covering space is used only to prove statements about the actual quotient
order. Thinness is a fixed geometric bound, not a density-dependent cutoff.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft
namespace CompactTorus

variable (L : ℝ)

/-- The Euclidean covering projection, with the existing quotient as codomain. -/
def cover (v : DimensionSpatial 3) : Space L := project L v

@[simp] theorem cover_zero : cover L 0 = 0 := rfl
@[simp] theorem cover_add (u v : DimensionSpatial 3) :
    cover L (u + v) = cover L u + cover L v := rfl
@[simp] theorem cover_sub (u v : DimensionSpatial 3) :
    cover L (u - v) = cover L u - cover L v := rfl

variable [Fact (0 < L)]

/-- A centered representative in each actual circle quotient. -/
def circleLift (q : AddCircle L) : ℝ := (AddCircle.equivIco L (-L / 2) q).val

@[simp] theorem circleLift_project (q : AddCircle L) :
    (circleLift L q : AddCircle L) = q :=
  (AddCircle.equivIco L (-L / 2)).symm_apply_apply q

theorem circleLift_mem (q : AddCircle L) : circleLift L q ∈ Ico (-L / 2) (L / 2) := by
  have h := (AddCircle.equivIco L (-L / 2) q).property
  convert h using 1
  ring

theorem abs_circleLift (q : AddCircle L) : |circleLift L q| = ‖q‖ := by
  have h := (AddCircle.norm_coe_eq_abs_iff L (ne_of_gt (Fact.out : 0 < L))
    (x := circleLift L q)).mpr (by
      rw [abs_of_pos (Fact.out : 0 < L)]
      exact abs_le.mpr ⟨by linarith [(circleLift_mem L q).1], (circleLift_mem L q).2.le⟩)
  rw [circleLift_project] at h
  exact h.symm

/-- A minimum-length Euclidean representative, not a same-chart condition. -/
def centeredLift (q : Space L) : DimensionSpatial 3 :=
  ![circleLift L q.1, circleLift L q.2.1, circleLift L q.2.2]

@[simp] theorem cover_centeredLift (q : Space L) : cover L (centeredLift L q) = q := by
  simp [cover, project, centeredLift]

theorem norm_centeredLift (q : Space L) :
    ‖centeredLift L q‖ = (spatialDistance L).distance 0 q := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, distance_eq]
  change Real.sqrt (|circleLift L q.1| ^ 2 + |circleLift L q.2.1| ^ 2 +
    |circleLift L q.2.2| ^ 2) = _
  simp only [abs_circleLift, Prod.fst_zero, Prod.snd_zero, dist_zero_left]

omit [Fact (0 < L)] in
theorem distance_sub (p q : Space L) :
    (spatialDistance L).distance 0 (q - p) = (spatialDistance L).distance p q := by
  simp only [distance_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
    dist_zero_left, dist_eq_norm, zero_sub, norm_neg]
  rw [norm_sub_rev q.1 p.1, norm_sub_rev q.2.1 p.2.1, norm_sub_rev q.2.2 p.2.2]

omit [Fact (0 < L)] in
theorem distance_cover_le (u v : DimensionSpatial 3) :
    (spatialDistance L).distance (cover L u) (cover L v) ≤ ‖v - u‖ := by
  rw [← distance_sub, ← cover_sub, distance_eq, EuclideanSpace.norm_eq]
  simp only [cover, project, Fin.sum_univ_three, Prod.fst_zero, Prod.snd_zero,
    dist_zero_left]
  apply Real.sqrt_le_sqrt
  gcongr
  all_goals exact QuotientAddGroup.norm_mk_le_norm

/-- Two lifts inside the same ball of radius strictly less than half a period
cannot represent the same quotient point. This also controls intermediate
points of an entire interval, not only its endpoints. -/
theorem cover_injective_ball {a : DimensionSpatial 3} {R : ℝ} (hR : 2 * R < L) :
    InjOn (cover L) (Metric.closedBall a R) := by
  intro u hu v hv he
  have hu' : ‖u - a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hv' : ‖v - a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hi (i : Fin 3) : u i ∈ Ico (a i - L / 2) (a i - L / 2 + L) ∧
      v i ∈ Ico (a i - L / 2) (a i - L / 2 + L) := by
    have h₁ := (PiLp.norm_apply_le (u - a) i).trans hu'
    have h₂ := (PiLp.norm_apply_le (v - a) i).trans hv'
    simp only [PiLp.sub_apply, Real.norm_eq_abs, abs_le] at h₁ h₂
    constructor <;> constructor <;> linarith
  apply PiLp.ext
  intro i
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (hi i).1 (hi i).2).mp
  fin_cases i
  · exact congrArg Prod.fst he
  · exact congrArg (fun p : Space L => p.2.1) he
  · exact congrArg (fun p : Space L => p.2.2) he

/-- All causal targets have a lift attaining the quotient distance. -/
theorem exists_causal_lift (a : DimensionSpatial 3) (q : Space L) {τ : ℝ}
    (h : (spatialDistance L).distance (cover L a) q ≤ τ) :
    ∃ b : DimensionSpatial 3, cover L b = q ∧ ‖b - a‖ ≤ τ := by
  refine ⟨a + centeredLift L (q - cover L a), ?_, ?_⟩
  · simp
  · rw [add_sub_cancel_left, norm_centeredLift, distance_sub]
    exact h

/-- Thinness supplies uniqueness for every causal lift, including null pairs. -/
theorem existsUnique_causal_lift (a : DimensionSpatial 3) (q : Space L) {τ : ℝ}
    (hτ : 2 * τ < L) (h : (spatialDistance L).distance (cover L a) q ≤ τ) :
    ∃! b : DimensionSpatial 3, cover L b = q ∧ ‖b - a‖ ≤ τ := by
  obtain ⟨b, hb, hba⟩ := exists_causal_lift L a q h
  refine ⟨b, ⟨hb, hba⟩, fun c hc => ?_⟩
  exact cover_injective_ball L hτ
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hc.2)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hba) (hc.1.trans hb.symm)

/-- Covering projection on spacetime; no bounded coordinate region is substituted
for the quotient slab. -/
def spacetimeCover (x : DimensionSpacetime 3) : ℝ × Space L := (x.1, cover L x.2)

omit [Fact (0 < L)] in
theorem causal_project {x y : DimensionSpacetime 3} (h : y ∈ dimensionCausalFuture x) :
    Ultrastatic.Rel (spatialDistance L) (spacetimeCover L x) (spacetimeCover L y) :=
  (distance_cover_le L x.2 y.2).trans h

/-- The whole quotient interval is exactly the projection of its lifted diamond.
For the reverse inclusion the two causal legs are lifted and their endpoint
lifts are identified by the strict period bound. -/
theorem interval_image {x y : DimensionSpacetime 3} (hτ : 2 * (y.1 - x.1) < L)
    (hxy : y ∈ dimensionCausalFuture x) :
    spacetimeCover L '' dimensionCausalInterval x y =
      Ultrastatic.closedInterval (spatialDistance L) (spacetimeCover L x) (spacetimeCover L y) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨causal_project L hz.1, causal_project L hz.2⟩
  · intro z hz
    obtain ⟨b, hb, hxb⟩ := exists_causal_lift L x.2 z.2 hz.1
    change ‖b - x.2‖ ≤ z.1 - x.1 at hxb
    have hby : (spatialDistance L).distance (cover L b) (cover L y.2) ≤ y.1 - z.1 := by
      simpa only [hb] using hz.2
    obtain ⟨c, hc, hbc⟩ := exists_causal_lift L b (cover L y.2) hby
    have hxc : ‖c - x.2‖ ≤ y.1 - x.1 := by
      calc
        ‖c - x.2‖ = ‖(c - b) + (b - x.2)‖ := by congr 1; abel
        _ ≤ ‖c - b‖ + ‖b - x.2‖ := norm_add_le _ _
        _ ≤ y.1 - x.1 := by linarith
    have hcy : c = y.2 := cover_injective_ball L hτ
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hxc)
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hxy) hc
    refine ⟨(z.1, b), ⟨hxb, ?_⟩, Prod.ext rfl hb⟩
    simpa only [hcy] using hbc

/-- The projection is injective on every point of the entire diamond. -/
theorem interval_injective {x y : DimensionSpacetime 3} (hτ : 2 * (y.1 - x.1) < L) :
    InjOn (spacetimeCover L) (dimensionCausalInterval x y) := by
  intro u hu v hv he
  have hcu := (dimensionCausalInterval_subset_compact x y hu).2
  have hcv := (dimensionCausalInterval_subset_compact x y hv).2
  exact Prod.ext (congrArg (fun p : ℝ × Space L => p.1) he)
    (cover_injective_ball L hτ hcu hcv (congrArg Prod.snd he))

omit [Fact (0 < L)] in
/-- The required lift bound follows from membership in the fixed open slab. -/
theorem slab_time_gap {T : ℝ} (hT : 2 * T < L) {x y : ℝ × Space L}
    (hx : x ∈ slab L T) (hy : y ∈ slab L T) : 2 * (y.1 - x.1) < L := by
  have h₁ := hx.1.1
  have h₂ := hy.1.2
  linarith

end CompactTorus
end BoundaryDraft
