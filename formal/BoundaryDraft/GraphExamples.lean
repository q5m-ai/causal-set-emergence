import BoundaryDraft.EllipsoidJoint
import BoundaryDraft.SpacetimeIntegration

/-!
# Admissible examples

The original ellipsoids are admitted under their original axis hypotheses.
Damping their height by `u ↦ u - u²` gives a smooth, genuinely nonquadratic
profile with the same regular joint and with interior critical points intact.
No coarea or surface-integral result is used here.
-/

open Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

/-- Full admissibility of the existing ellipsoid, not just its reduction data. -/
theorem ellipsoid_admissible (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    AdmissibleGraphCap (ellipsoidProfile a b) where
  toGraphCapData := ellipsoid_graphCapData a b ha hb
  smooth_near := fun x _ => ((contDiff_ellipsoidProfile a b).of_le (by norm_num)).contDiffAt
  boundary_zero := fun _ hx =>
    (frontier_lt_subset_eq continuous_const (continuous_ellipsoidProfile a b) hx).symm
  regular_zero := by
    intro x _ hx
    apply ellipsoid_joint_regular a b ha (fun i => by linarith [hb i]) x
    rw [ellipsoidJoint_eq_zero a b ha]
    exact hx

/-- A quartic graph height, not a quadratic ellipsoid profile. -/
def dampedEllipsoidProfile (a : ℝ) (b : Fin 3 → ℝ) (x : Spatial) : ℝ :=
  ellipsoidProfile a b x - ellipsoidProfile a b x ^ 2

private theorem damped_pos_iff (u : ℝ) (hu : u < 1) :
    0 < u - u ^ 2 ↔ 0 < u := by
  rw [show u - u ^ 2 = u * (1 - u) by ring,
    mul_pos_iff_of_pos_right (sub_pos.mpr hu)]

private theorem damped_positivePart (u : ℝ) (hu : u ≤ 1 / 2) :
    max 0 (u - u ^ 2) = max 0 u - (max 0 u) ^ 2 := by
  by_cases hp : 0 < u
  · rw [max_eq_right hp.le, max_eq_right ((damped_pos_iff u (by linarith)).mpr hp).le]
  · rw [max_eq_left (le_of_not_gt hp), max_eq_left (by nlinarith)]
    norm_num

private theorem damped_lipschitz (u v : ℝ)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    |(u - u ^ 2) - (v - v ^ 2)| ≤ |u - v| := by
  rw [show (u - u ^ 2) - (v - v ^ 2) = (u - v) * (1 - (u + v)) by ring, abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem dampedEllipsoid_positive (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (ha' : a ≤ 1 / 2) :
    {x | 0 < dampedEllipsoidProfile a b x} = {x | 0 < ellipsoidProfile a b x} := by
  ext x
  exact damped_pos_iff _ (lt_of_le_of_lt (ellipsoidProfile_le a b ha.le x) (by linarith))

theorem continuous_dampedEllipsoidProfile (a : ℝ) (b : Fin 3 → ℝ) :
    Continuous (dampedEllipsoidProfile a b) :=
  (continuous_ellipsoidProfile a b).sub ((continuous_ellipsoidProfile a b).pow 2)

theorem dampedEllipsoid_graphCapData (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (ha' : a ≤ 1 / 2) (hb : ∀ i, 2 * a < b i) :
    GraphCapData (dampedEllipsoidProfile a b) where
  bounded_positive := by
    rw [dampedEllipsoid_positive a b ha ha']
    exact (ellipsoid_graphCapData a b ha hb).bounded_positive
  lipschitz_positivePart := by
    obtain ⟨κ, hκ, hκ1, hLip⟩ := ellipsoid_positivePart_lipschitz a b ha hb
    refine ⟨κ, hκ, hκ1, fun x y => ?_⟩
    have hx := (ellipsoidProfile_le a b ha.le x).trans ha'
    have hy := (ellipsoidProfile_le a b ha.le y).trans ha'
    rw [dampedEllipsoidProfile, dampedEllipsoidProfile,
      damped_positivePart _ hx, damped_positivePart _ hy]
    exact (damped_lipschitz _ _ (le_max_left _ _) (max_le (by norm_num) hx)
      (le_max_left _ _) (max_le (by norm_num) hy)).trans (hLip x y)

/-- Damping preserves regularity at height zero without excluding critical
points in the interior. The differential is the original one at the joint. -/
theorem dampedEllipsoid_admissible (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (ha' : a ≤ 1 / 2) (hb : ∀ i, 2 * a < b i) :
    AdmissibleGraphCap (dampedEllipsoidProfile a b) where
  toGraphCapData := dampedEllipsoid_graphCapData a b ha ha' hb
  smooth_near := by
    intro x _
    exact (((contDiff_ellipsoidProfile a b).sub
      ((contDiff_ellipsoidProfile a b).pow 2)).of_le (by norm_num)).contDiffAt
  boundary_zero := fun _ hx =>
    (frontier_lt_subset_eq continuous_const (continuous_dampedEllipsoidProfile a b) hx).symm
  regular_zero := by
    intro x _ hx
    have he : ellipsoidProfile a b x = 0 := by
      have hu := (ellipsoidProfile_le a b ha.le x).trans ha'
      change ellipsoidProfile a b x - ellipsoidProfile a b x ^ 2 = 0 at hx
      have hf : ellipsoidProfile a b x * (1 - ellipsoidProfile a b x) = 0 := by nlinarith [hx]
      exact (mul_eq_zero.mp hf).resolve_right (by linarith)
    have hd := (hasGradientAt_ellipsoidProfile a b x).hasFDerivAt
    have hg := hd.sub ((hasDerivAt_pow 2 (ellipsoidProfile a b x)).comp_hasFDerivAt x hd)
    have heq : fderiv ℝ (fun y : JointSpace => dampedEllipsoidProfile a b y) x =
        fderiv ℝ (fun y : JointSpace => ellipsoidProfile a b y) x := by
      calc
        _ = _ := hg.fderiv
        _ = _ := by rw [hd.fderiv]; simp [he]
    rw [heq]
    apply ellipsoid_joint_regular a b ha (fun i => by linarith [hb i]) x
    rw [ellipsoidJoint_eq_zero a b ha]
    exact he

/-- The new theorem applies to the quartic family at every positive density. -/
theorem dampedEllipsoid_graphReduction (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (ha' : a ≤ 1 / 2) (hb : ∀ i, 2 * a < b i) :
    GraphReductionGoal (dampedEllipsoidProfile a b) :=
  (dampedEllipsoid_admissible a b ha ha' hb).graphReduction

end BoundaryDraft
