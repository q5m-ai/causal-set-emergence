import BoundaryDraft.SpatialDistance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The round sphere's actual angular distance

The unit sphere retains its usual Borel topology, but its causal distance is
`arccos` of the inner product, not the ambient chord distance. The triangle
inequality is proved here: the pinned mathlib's angle triangle declaration is
only a `proof_wanted` placeholder and is not used.
-/

open Set Metric InnerProductGeometry
open scoped RealInnerProductSpace
noncomputable section
namespace BoundaryDraft

abbrev RoundSphere := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace RoundSphere

@[simp] theorem norm_coe (x : RoundSphere) : ‖x.val‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.property

theorem coe_ne_zero (x : RoundSphere) : x.val ≠ 0 := by
  intro h
  simpa [h] using norm_coe x

/-- Great-circle angular distance, in radians, on the unit round sphere. -/
def distance (x y : RoundSphere) : ℝ := angle x.val y.val

theorem distance_eq_arccos (x y : RoundSphere) :
    distance x y = Real.arccos ⟪x.val, y.val⟫ := by
  simp [distance, angle]

@[simp] theorem cos_distance (x y : RoundSphere) :
    Real.cos (distance x y) = ⟪x.val, y.val⟫ := by
  simp [distance, cos_angle]

theorem normal_component_norm (x y : RoundSphere) :
    ‖x.val - Real.cos (distance x y) • y.val‖ = Real.sin (distance x y) := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (show 0 ≤ Real.sin (distance x y) from sin_angle_nonneg _ _)).mp
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_coe, norm_coe, inner_smul_right, ← cos_distance]
  nlinarith [Real.sin_sq_add_cos_sq (distance x y)]

theorem distance_triangle (x y z : RoundSphere) :
    distance x z ≤ distance x y + distance y z := by
  by_cases h : Real.pi ≤ distance x y + distance y z
  · exact (angle_le_pi _ _).trans h
  have hs : distance x y + distance y z ≤ Real.pi := (lt_of_not_ge h).le
  apply (Real.strictAntiOn_cos.le_iff_le
    (show distance x y + distance y z ∈ Icc 0 Real.pi from
      ⟨add_nonneg (angle_nonneg _ _) (angle_nonneg _ _), hs⟩)
    (show distance x z ∈ Icc 0 Real.pi from ⟨angle_nonneg _ _, angle_le_pi _ _⟩)).mp
  have hc := (abs_le.mp (abs_real_inner_le_norm
    (x.val - Real.cos (distance x y) • y.val)
    (z.val - Real.cos (distance z y) • y.val))).1
  rw [normal_component_norm, normal_component_norm] at hc
  have hyz : distance z y = distance y z := angle_comm _ _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_coe, one_pow, ← cos_distance, hyz] at hc
  rw [Real.cos_add]
  nlinarith

theorem eq_of_distance_zero {x y : RoundSphere} (h : distance x y = 0) : x = y := by
  have hc : ⟪x.val, y.val⟫ = 1 := by rw [← cos_distance, h, Real.cos_zero]
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hn := norm_sub_sq_real x.val y.val
  simp only [norm_coe, one_pow, hc] at hn
  nlinarith [norm_nonneg (x.val - y.val)]

/-- Continuous angular metric laws, without changing the sphere's topology. -/
def spatialDistance : SpatialDistance RoundSphere where
  distance := distance
  nonneg _ _ := angle_nonneg _ _
  self x := angle_self (coe_ne_zero x)
  comm _ _ := angle_comm _ _
  triangle := distance_triangle
  eq_of_zero _ _ := eq_of_distance_zero
  continuous := by
    simp only [funext₂ distance_eq_arccos]
    exact Real.continuous_arccos.comp
      ((continuous_subtype_val.comp continuous_fst).inner
        (continuous_subtype_val.comp continuous_snd))

/-- Antipodes are at distance pi, rather than chord distance two. -/
theorem distance_antipode (x : RoundSphere) :
    distance x ⟨-x.val, by simpa only [mem_sphere_zero_iff_norm, norm_neg] using x.property⟩ =
      Real.pi := angle_self_neg_of_nonzero (coe_ne_zero x)

end RoundSphere
end BoundaryDraft
