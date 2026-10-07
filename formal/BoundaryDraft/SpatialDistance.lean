import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Continuous spatial distances, independent of a presentation metric

The topology may be presented by a chord or a maximum metric. The distance
used by the causal order is explicit and must satisfy the metric laws. This
keeps the round-sphere and Euclidean-product distances distinct from those
presentation metrics. There is no volume or probabilistic input here.
-/

open Set
noncomputable section
namespace BoundaryDraft

structure SpatialDistance (X : Type*) [TopologicalSpace X] where
  distance : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ distance x y
  self : ∀ x, distance x x = 0
  comm : ∀ x y, distance x y = distance y x
  triangle : ∀ x y z, distance x z ≤ distance x y + distance y z
  eq_of_zero : ∀ x y, distance x y = 0 → x = y
  continuous : Continuous (fun p : X × X => distance p.1 p.2)

namespace SpatialDistance
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Use a genuine metric when it is already the intended spatial distance. -/
def ofMetric (X : Type*) [MetricSpace X] : SpatialDistance X where
  distance := dist
  nonneg := fun _ _ => dist_nonneg
  self := dist_self
  comm := dist_comm
  triangle := dist_triangle
  eq_of_zero := fun _ _ => dist_eq_zero.mp
  continuous := continuous_dist

/-- The two-dimensional Euclidean norm triangle inequality in scalar form. -/
theorem sqrt_sq_add_sq_triangle (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  have h := norm_add_le ((WithLp.equiv 2 (ℝ × ℝ)).symm (a, b))
    ((WithLp.equiv 2 (ℝ × ℝ)).symm (c, d))
  simpa only [WithLp.prod_norm_eq_of_L2, WithLp.add_fst, WithLp.add_snd,
    Real.norm_eq_abs, sq_abs] using h

/-- Euclidean product distance, NOT the default maximum product metric. -/
def prod (D : SpatialDistance X) (E : SpatialDistance Y) : SpatialDistance (X × Y) where
  distance x y := Real.sqrt (D.distance x.1 y.1 ^ 2 + E.distance x.2 y.2 ^ 2)
  nonneg _ _ := Real.sqrt_nonneg _
  self x := by simp [D.self, E.self]
  comm x y := by rw [D.comm x.1 y.1, E.comm x.2 y.2]
  triangle x y z := by
    apply (Real.sqrt_le_sqrt (add_le_add
      (pow_le_pow_left₀ (D.nonneg _ _) (D.triangle _ _ _) 2)
      (pow_le_pow_left₀ (E.nonneg _ _) (E.triangle _ _ _) 2))).trans
    exact sqrt_sq_add_sq_triangle _ _ _ _
  eq_of_zero x y h := by
    have hs : D.distance x.1 y.1 ^ 2 + E.distance x.2 y.2 ^ 2 = 0 :=
      (Real.sqrt_eq_zero (add_nonneg (sq_nonneg _) (sq_nonneg _))).mp h
    exact Prod.ext (D.eq_of_zero _ _ (by nlinarith [sq_nonneg (E.distance x.2 y.2)]))
      (E.eq_of_zero _ _ (by nlinarith [sq_nonneg (D.distance x.1 y.1)]))
  continuous := (Real.continuous_sqrt.comp
    (((D.continuous.comp (continuous_fst.fst.prodMk continuous_snd.fst)).pow 2).add
      ((E.continuous.comp (continuous_fst.snd.prodMk continuous_snd.snd)).pow 2)))

@[simp] theorem prod_distance (D : SpatialDistance X) (E : SpatialDistance Y) (x y : X × Y) :
    (D.prod E).distance x y =
      Real.sqrt (D.distance x.1 y.1 ^ 2 + E.distance x.2 y.2 ^ 2) := rfl

end SpatialDistance
end BoundaryDraft
