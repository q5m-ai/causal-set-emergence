import BoundaryDraft.GraphGeometry
import Mathlib.Data.Fintype.Lattice

/-!
# Geometry of the concrete ellipsoidal graph cap

The spatial distance here is Euclidean, not the supremum norm on `Spatial`.
The positive part of the profile has a global Lipschitz constant strictly
below one. Consequently the future slice has no missing lateral boundary.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace BoundaryDraft

/-- Radius after dividing each coordinate by its ellipsoid axis. -/
def ellipsoidRadius (b : Fin 3 → ℝ) (x : Spatial) : ℝ :=
  ‖((WithLp.equiv 2 _).symm (fun i => x i / b i) : EuclideanSpace ℝ (Fin 3))‖

theorem ellipsoidRadius_sq (b : Fin 3 → ℝ) (x : Spatial) :
    ellipsoidRadius b x ^ 2 = ∑ i : Fin 3, (x i / b i) ^ 2 := by
  simp [ellipsoidRadius, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, div_pow]

theorem continuous_ellipsoidProfile (a : ℝ) (b : Fin 3 → ℝ) :
    Continuous (ellipsoidProfile a b) := by
  unfold ellipsoidProfile
  fun_prop

/-- Positivity is exactly the open ellipsoid, not a separately assumed domain. -/
theorem ellipsoidProfile_pos_iff (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (x : Spatial) :
    0 < ellipsoidProfile a b x ↔ ∑ i : Fin 3, (x i / b i) ^ 2 < 1 := by
  unfold ellipsoidProfile
  rw [mul_pos_iff_of_pos_left ha, sub_pos]

theorem measurableSet_ellipsoid_positive (a : ℝ) (b : Fin 3 → ℝ) :
    MeasurableSet {x | 0 < ellipsoidProfile a b x} :=
  isOpen_lt continuous_const (continuous_ellipsoidProfile a b) |>.measurableSet

theorem ellipsoidProfile_le (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 ≤ a)
    (x : Spatial) : ellipsoidProfile a b x ≤ a := by
  have hs : 0 ≤ ∑ i : Fin 3, (x i / b i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  dsimp [ellipsoidProfile]
  nlinarith

/-- A closed coordinate box contains the positive set; in particular it is bounded. -/
theorem ellipsoid_positive_subset_box (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) :
    {x | 0 < ellipsoidProfile a b x} ⊆ Icc (-b) b := by
  intro x hx
  have hs := (ellipsoidProfile_pos_iff a b ha x).mp hx
  constructor <;> intro i
  all_goals
    have hi : (x i / b i) ^ 2 < 1 :=
      lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (x j / b j))
        (Finset.mem_univ i)) hs
    have hi' : |x i / b i| < 1 := (sq_lt_one_iff_abs_lt_one _).mp hi
    rw [abs_div, abs_of_pos (hb i), div_lt_one (hb i)] at hi'
  · exact (abs_lt.mp hi').1.le
  · exact (abs_lt.mp hi').2.le

theorem isBounded_ellipsoid_positive (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) : Bornology.IsBounded {x | 0 < ellipsoidProfile a b x} :=
  (isCompact_Icc : IsCompact (Icc (-b) b)).isBounded.subset
    (ellipsoid_positive_subset_box a b ha hb)

/-- The zero extension has compact support, including its boundary. The raw
quadratic profile itself is not compactly supported or globally Lipschitz. -/
theorem hasCompactSupport_ellipsoid_positivePart (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 0 < b i) :
    HasCompactSupport (fun x => max 0 (ellipsoidProfile a b x)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-b) b))
  intro x hx
  exact max_eq_left (le_of_not_gt fun hp => hx (ellipsoid_positive_subset_box a b ha hb hp))

private theorem truncated_square_lipschitz {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |max 0 (1 - r ^ 2) - max 0 (1 - s ^ 2)| ≤ 2 * |r - s| := by
  wlog hrs : r ≤ s generalizing r s
  · simpa only [abs_sub_comm] using this hs hr (le_of_not_ge hrs)
  rw [abs_of_nonpos (sub_nonpos.mpr hrs)]
  have hsq : r ^ 2 ≤ s ^ 2 := sq_le_sq₀ hr hs |>.mpr hrs
  have hm : max 0 (1 - s ^ 2) ≤ max 0 (1 - r ^ 2) := max_le_max_left _ (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hm)]
  by_cases hs1 : s ≤ 1
  · rw [max_eq_right (by nlinarith : 0 ≤ 1 - r ^ 2),
      max_eq_right (by nlinarith : 0 ≤ 1 - s ^ 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (by linarith : 0 ≤ 2 - (r + s))]
  · rw [max_eq_left (by nlinarith : 1 - s ^ 2 ≤ 0)]
    by_cases hr1 : r ≤ 1
    · rw [max_eq_right (by nlinarith : 0 ≤ 1 - r ^ 2)]
      nlinarith [sq_nonneg (r - 1)]
    · rw [max_eq_left (by nlinarith : 1 - r ^ 2 ≤ 0)]
      linarith

private theorem ellipsoidRadius_sub_le (b : Fin 3 → ℝ) (m : ℝ)
    (hm : 0 < m) (hb : ∀ i, m ≤ b i) (x y : Spatial) :
    |ellipsoidRadius b x - ellipsoidRadius b y| ≤ spatialDistance x y / m := by
  let X : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm (fun i => x i / b i)
  let Y : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm (fun i => y i / b i)
  apply (abs_norm_sub_norm_le X Y).trans
  have hnorm : ‖X - Y‖ ^ 2 = ∑ i : Fin 3, ((x i - y i) / b i) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, X, Y, ← sub_div, div_pow]
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (spatialDistance_nonneg _ _) hm.le)).mp
  rw [hnorm, div_pow, spatialDistance_sq, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [div_pow, show (x i - y i) ^ 2 = (y i - x i) ^ 2 by ring]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hm)
    ((sq_le_sq₀ hm.le (hm.le.trans (hb i))).mpr (hb i))

/-- Global Euclidean Lipschitz control of the *positive part*, including pairs
with one or both points outside the ellipsoid. -/
theorem ellipsoid_positivePart_lipschitz (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ x y : Spatial,
      |max 0 (ellipsoidProfile a b x) - max 0 (ellipsoidProfile a b y)| ≤
        κ * spatialDistance x y := by
  obtain ⟨i, hi⟩ := Finite.exists_min b
  have hm : 0 < b i := lt_trans (by linarith) (hb i)
  refine ⟨2 * a / b i, by positivity, (div_lt_one hm).mpr (hb i), ?_⟩
  intro x y
  have hx : max 0 (ellipsoidProfile a b x) = a * max 0 (1 - ellipsoidRadius b x ^ 2) := by
    rw [ellipsoidProfile, ← ellipsoidRadius_sq, mul_max_of_nonneg _ _ ha.le, mul_zero]
  have hy : max 0 (ellipsoidProfile a b y) = a * max 0 (1 - ellipsoidRadius b y ^ 2) := by
    rw [ellipsoidProfile, ← ellipsoidRadius_sq, mul_max_of_nonneg _ _ ha.le, mul_zero]
  rw [hx, hy, ← mul_sub, abs_mul, abs_of_pos ha]
  calc
    _ ≤ a * (2 * |ellipsoidRadius b x - ellipsoidRadius b y|) :=
      mul_le_mul_of_nonneg_left (truncated_square_lipschitz (norm_nonneg _) (norm_nonneg _)) ha.le
    _ ≤ a * (2 * (spatialDistance x y / b i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ellipsoidRadius_sub_le b (b i) hm hi x y) (by norm_num)) ha.le
    _ = _ := by ring

/-- Ellipsoids satisfy exactly the general reduction assumptions. -/
theorem ellipsoid_graphCapData (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    GraphCapData (ellipsoidProfile a b) where
  bounded_positive := isBounded_ellipsoid_positive a b ha (fun i => by linarith [hb i])
  lipschitz_positivePart := ellipsoid_positivePart_lipschitz a b ha hb

/-- Every future point below the planar boundary belongs to the graph cap.
The set equality retains null-related points and the cone vertex exactly. -/
theorem ellipsoid_complete_future (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i)
    (x : Spacetime) (hx : x ∈ graphCapRegion (ellipsoidProfile a b)) :
    graphCapRegion (ellipsoidProfile a b) ∩ causalFuture x =
      {y | y ∈ causalFuture x ∧ y 0 < 0} :=
  graphCap_complete_future _ (ellipsoid_graphCapData a b ha hb) x hx

/-- Causal convexity: every event causally between two cap events is in the cap. -/
theorem ellipsoid_causallyConvex (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i)
    (x y z : Spacetime) (hx : x ∈ graphCapRegion (ellipsoidProfile a b))
    (hz : z ∈ graphCapRegion (ellipsoidProfile a b))
    (hxy : y ∈ causalFuture x) (hyz : z ∈ causalFuture y) :
    y ∈ graphCapRegion (ellipsoidProfile a b) :=
  graphCap_causallyConvex _ (ellipsoid_graphCapData a b ha hb) x y z hx hz hxy hyz

end BoundaryDraft
