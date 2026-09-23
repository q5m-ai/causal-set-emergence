import BoundaryDraft.EllipsoidGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Geometry of the null-plane-truncated diamond

This file works directly with the strict inequalities in `nullCapRegion`.
It proves that the cap is open, bounded, and causally convex, and that the
future of each cap point is the complete Minkowski interval up to the strict
future-tip boundary.  No admissibility structure or geometric hypothesis is
introduced.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

/-- Causal past, expressed using the existing causal-future relation. -/
def causalPast (q : Spacetime) : Set Spacetime := {x | q ∈ causalFuture x}

/-- Chronological past, expressed using the existing chronological-future relation. -/
def chronologicalPast (q : Spacetime) : Set Spacetime :=
  {x | q ∈ chronologicalFuture x}

/-- The closed Alexandrov interval.  Its null boundary will later be removed
under the integral by an explicit null-set proof. -/
def causalInterval (x q : Spacetime) : Set Spacetime := causalFuture x ∩ causalPast q

/-- Event on the time axis. -/
def timeAxis (T : ℝ) : Spacetime := fun i => if i = 0 then T else 0

@[simp] theorem timeAxis_zero (T : ℝ) : timeAxis T 0 = T := by
  simp [timeAxis]

@[simp] theorem timeAxis_succ (T : ℝ) (i : Fin 3) : timeAxis T i.succ = 0 := by
  simp [timeAxis, Fin.succ_ne_zero]

@[simp] theorem pastTip_eq_neg_timeAxis (T : ℝ) : pastTip T = -timeAxis T := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [pastTip, timeAxis]

/-- The Euclidean spatial square is continuous in both endpoints. -/
theorem continuous_spatialSeparationSq :
    Continuous (Function.uncurry spatialSeparationSq) := by
  unfold Function.uncurry spatialSeparationSq
  fun_prop

/-- Proper-time square is continuous in both endpoints. -/
theorem continuous_intervalSq : Continuous (Function.uncurry intervalSq) := by
  unfold Function.uncurry intervalSq
  exact (((continuous_apply 0).comp continuous_snd).sub
      ((continuous_apply 0).comp continuous_fst)).pow 2 |>.sub
    continuous_spatialSeparationSq

/-- The causal future is closed and hence measurable. -/
theorem isClosed_causalFuture (x : Spacetime) : IsClosed (causalFuture x) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const (continuous_apply 0)
  · change IsClosed {y | spatialSeparationSq x y ≤ (y 0 - x 0) ^ 2}
    apply isClosed_le
    · exact continuous_spatialSeparationSq.comp
        (continuous_const.prodMk continuous_id)
    · fun_prop

/-- The chronological future is open and hence measurable. -/
theorem isOpen_chronologicalFuture (x : Spacetime) : IsOpen (chronologicalFuture x) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_apply 0)
  · change IsOpen {y | spatialSeparationSq x y < (y 0 - x 0) ^ 2}
    apply isOpen_lt
    · exact continuous_spatialSeparationSq.comp
        (continuous_const.prodMk continuous_id)
    · fun_prop

/-- The null cap is an honest open, measurable subset of the original
four-dimensional coordinate space. -/
theorem isOpen_nullCapRegion (T a : ℝ) : IsOpen (nullCapRegion T a) := by
  have hq : IsOpen {x : Spacetime | (0 : Spacetime) ∈ chronologicalFuture x} := by
    unfold chronologicalFuture
    exact (isOpen_lt (continuous_apply 0) continuous_const).inter
      (isOpen_lt
        (continuous_spatialSeparationSq.comp (continuous_id.prodMk continuous_const))
        ((continuous_const.sub (continuous_apply 0)).pow 2))
  have hp : IsOpen {x : Spacetime | -a < x 0 - x 1} :=
    isOpen_lt continuous_const ((continuous_apply 0).sub (continuous_apply 1))
  simpa only [nullCapRegion, mem_inter_iff, mem_setOf_eq] using
    (isOpen_chronologicalFuture (pastTip T)).inter (hq.inter hp)

theorem measurableSet_nullCapRegion (T a : ℝ) : MeasurableSet (nullCapRegion T a) :=
  (isOpen_nullCapRegion T a).measurableSet

/-- Every cap point lies in a fixed compact coordinate box. -/
theorem nullCapRegion_subset_box (T a : ℝ) (hT : 0 < T) :
    nullCapRegion T a ⊆ Icc (fun _ => -T) (fun _ => T) := by
  intro x hx
  have hpt := hx.1
  have hq := hx.2.1
  have ht_lower : -T < x 0 := by
    simpa [chronologicalFuture, pastTip] using hpt.1
  have ht_upper : x 0 < 0 := by
    simpa [chronologicalFuture] using hq.1
  have hsum : (∑ i : Fin 3, x i.succ ^ 2) < x 0 ^ 2 := by
    simpa [chronologicalFuture, spatialSeparationSq] using hq.2
  have hcoord (i : Fin 3) : |x i.succ| < T := by
    have hi0 : x i.succ ^ 2 ≤ ∑ j : Fin 3, x j.succ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j.succ)) (Finset.mem_univ i)
    have hxT : x 0 ^ 2 ≤ T ^ 2 := by
      rw [show x 0 ^ 2 = (-x 0) ^ 2 by ring]
      exact (sq_le_sq₀ (by linarith : 0 ≤ -x 0) hT.le).mpr
        (by linarith : -x 0 ≤ T)
    have hi : x i.succ ^ 2 < T ^ 2 :=
      lt_of_le_of_lt hi0 (lt_of_lt_of_le hsum hxT)
    exact (sq_lt_sq₀ (abs_nonneg _) hT.le).mp (by simpa only [sq_abs] using hi)
  constructor <;> intro i
  · refine Fin.cases (le_of_lt ht_lower) (fun j => (abs_lt.mp (hcoord j)).1.le) i
  · refine Fin.cases (by linarith : x 0 ≤ T) (fun j => (abs_lt.mp (hcoord j)).2.le) i

/-- Boundedness is derived from the original strict diamond inequalities. -/
theorem isBounded_nullCapRegion (T a : ℝ) (hT : 0 < T) :
    Bornology.IsBounded (nullCapRegion T a) :=
  (isCompact_Icc : IsCompact (Icc (fun _ : Fin 4 => -T) (fun _ => T))).isBounded.subset
    (nullCapRegion_subset_box T a hT)

/-- Continuous functions are absolutely integrable on the bounded null cap. -/
theorem integrableOn_nullCapRegion (T a : ℝ) (hT : 0 < T)
    (f : Spacetime → ℝ) (hf : Continuous f) :
    IntegrableOn f (nullCapRegion T a) :=
  hf.integrableOn_Icc.mono_set (nullCapRegion_subset_box T a hT)

private theorem spatialDistance_lt_of_chronologicalFuture (x y : Spacetime)
    (hxy : y ∈ chronologicalFuture x) :
    spatialDistance (spatialPart x) (spatialPart y) < y 0 - x 0 := by
  apply (sq_lt_sq₀ (spatialDistance_nonneg _ _) (sub_pos.mpr hxy.1).le).mp
  simpa only [spatialDistance_sq, spatialPart, spatialSeparationSq] using hxy.2

private theorem spatialDistance_triangle (x y z : Spatial) :
    spatialDistance x z ≤ spatialDistance x y + spatialDistance y z := by
  let X : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm x
  let Y : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm y
  let Z : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm z
  simpa [spatialDistance, X, Y, Z, dist_eq_norm, map_sub, add_comm] using
    dist_triangle Z Y X

private theorem spatialSeparationSq_eq_distance_sq (x y : Spacetime) :
    spatialSeparationSq x y = spatialDistance (spatialPart x) (spatialPart y) ^ 2 := by
  simpa [spatialSeparationSq, spatialPart] using
    (spatialDistance_sq (spatialPart x) (spatialPart y)).symm

/-- Causal transitivity for the concrete coordinate relation. -/
theorem causalFuture_trans {x y z : Spacetime}
    (hxy : y ∈ causalFuture x) (hyz : z ∈ causalFuture y) :
    z ∈ causalFuture x := by
  have hdxy := spatialDistance_le_of_causalFuture x y hxy
  have hdyz := spatialDistance_le_of_causalFuture y z hyz
  have htri := spatialDistance_triangle (spatialPart x) (spatialPart y) (spatialPart z)
  have htime : 0 ≤ z 0 - x 0 := by linarith [hxy.1, hyz.1]
  constructor
  · linarith [hxy.1, hyz.1]
  · rw [spatialSeparationSq_eq_distance_sq]
    exact (sq_le_sq₀ (spatialDistance_nonneg _ _) htime).mpr
      (htri.trans (by linarith [hdxy, hdyz]))

/-- A chronological step followed by a causal step remains chronological. -/
theorem chronologicalFuture_causal_trans {x y z : Spacetime}
    (hxy : y ∈ chronologicalFuture x) (hyz : z ∈ causalFuture y) :
    z ∈ chronologicalFuture x := by
  have hdxy := spatialDistance_lt_of_chronologicalFuture x y hxy
  have hdyz := spatialDistance_le_of_causalFuture y z hyz
  have htri := spatialDistance_triangle (spatialPart x) (spatialPart y) (spatialPart z)
  have hdist : spatialDistance (spatialPart x) (spatialPart z) < z 0 - x 0 := by
    exact lt_of_le_of_lt htri (by linarith [hdxy, hdyz])
  have htime : 0 ≤ z 0 - x 0 :=
    (spatialDistance_nonneg _ _).trans (le_of_lt hdist)
  constructor
  · exact sub_pos.mp (lt_of_le_of_lt (spatialDistance_nonneg _ _) hdist)
  · rw [spatialSeparationSq_eq_distance_sq]
    exact (sq_lt_sq₀ (spatialDistance_nonneg _ _) htime).mpr hdist

/-- A causal step followed by a chronological step remains chronological. -/
theorem causal_chronologicalFuture_trans {x y z : Spacetime}
    (hxy : y ∈ causalFuture x) (hyz : z ∈ chronologicalFuture y) :
    z ∈ chronologicalFuture x := by
  have hyx : spatialDistance (spatialPart y) (spatialPart x) ≤ y 0 - x 0 := by
    simpa only [spatialDistance_symm] using spatialDistance_le_of_causalFuture x y hxy
  have hzy := spatialDistance_lt_of_chronologicalFuture y z hyz
  have hzy' : spatialDistance (spatialPart z) (spatialPart y) < z 0 - y 0 := by
    simpa only [spatialDistance_symm] using hzy
  have htri := spatialDistance_triangle (spatialPart z) (spatialPart y) (spatialPart x)
  have hdist : spatialDistance (spatialPart x) (spatialPart z) < z 0 - x 0 := by
    rw [spatialDistance_symm]
    exact lt_of_le_of_lt htri (by linarith [hyx, hzy'])
  have htime : 0 ≤ z 0 - x 0 :=
    (spatialDistance_nonneg _ _).trans (le_of_lt hdist)
  constructor
  · exact sub_pos.mp (lt_of_le_of_lt (spatialDistance_nonneg _ _) hdist)
  · rw [spatialSeparationSq_eq_distance_sq]
    exact (sq_lt_sq₀ (spatialDistance_nonneg _ _) htime).mpr hdist

/-- The future side of `t-z=-a` is preserved by every causal displacement. -/
theorem nullPlane_future {a : ℝ} {x y : Spacetime}
    (hx : -a < x 0 - x 1) (hxy : y ∈ causalFuture x) :
    -a < y 0 - y 1 := by
  have hzsq : (y 1 - x 1) ^ 2 ≤ spatialSeparationSq x y := by
    unfold spatialSeparationSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (y j.succ - x j.succ))
      (Finset.mem_univ (0 : Fin 3))
  have hz : y 1 - x 1 ≤ y 0 - x 0 := by
    have habs : |y 1 - x 1| ≤ y 0 - x 0 := by
      apply (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hxy.1)).mp
      rw [sq_abs]
      exact hzsq.trans hxy.2
    exact (le_abs_self _).trans habs
  linarith

/-- Exact future-slice description with all strict/open conventions retained.
The past-tip cone and null-plane inequalities are automatic in the future of
`x`; only the strict past of the future tip remains. -/
theorem nullCap_complete_future (T a : ℝ) (x : Spacetime)
    (hx : x ∈ nullCapRegion T a) :
    nullCapRegion T a ∩ causalFuture x =
      causalFuture x ∩ chronologicalPast 0 := by
  ext y
  constructor
  · intro hy
    exact ⟨hy.2, hy.1.2.1⟩
  · rintro ⟨hxy, hyq⟩
    exact ⟨⟨chronologicalFuture_causal_trans hx.1 hxy, hyq,
      nullPlane_future hx.2.2 hxy⟩, hxy⟩

/-- The strict null cap is causally convex. -/
theorem nullCap_causallyConvex (T a : ℝ) {x y z : Spacetime}
    (hx : x ∈ nullCapRegion T a) (hz : z ∈ nullCapRegion T a)
    (hxy : y ∈ causalFuture x) (hyz : z ∈ causalFuture y) :
    y ∈ nullCapRegion T a := by
  have hyq : 0 ∈ chronologicalFuture y :=
    causal_chronologicalFuture_trans hyz hz.2.1
  have hy : y ∈ causalFuture x ∩ chronologicalPast 0 := ⟨hxy, hyq⟩
  rw [← nullCap_complete_future T a x hx] at hy
  exact hy.1

end BoundaryDraft
