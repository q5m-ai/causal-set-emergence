import BoundaryDraft.ThinTorusIntegration

/-!
# Independent geometry of the cubic ultrastatic slab

The quotient covering coordinates carry the constant (+---) metric. The
coordinate Levi-Civita and curvature contractions below are computed from that
metric, independently of the action or its phase coefficients. They are invariant
under every covering translation, so their value does not depend on a lift.
This is a concrete flat covering-coordinate calculation, not a general curved
manifold curvature API.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace BoundaryDraft
namespace CompactTorus

variable (L : ℝ) [Fact (0 < L)]

def pastFace (T : ℝ) : Set (ℝ × Space L) := {-T / 2} ×ˢ univ
def futureFace (T : ℝ) : Set (ℝ × Space L) := {T / 2} ×ˢ univ

omit [Fact (0 < L)] in
theorem frontier_slab {T : ℝ} (hT : 0 < T) :
    frontier (slab L T) = pastFace L T ∪ futureFace L T := by
  rw [slab, Ultrastatic.slab, frontier_prod_univ_eq, frontier_Ioo (by linarith : -T / 2 < T / 2)]
  ext p
  simp [pastFace, futureFace, or_and_right]

omit [Fact (0 < L)] in
theorem joint_empty {T : ℝ} (hT : 0 < T) : pastFace L T ∩ futureFace L T = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  rintro x ⟨hx, hy⟩
  have hx' : x.1 = -T / 2 := hx.1
  have hy' : x.1 = T / 2 := hy.1
  linarith

theorem compact_faces (T : ℝ) : IsCompact (pastFace L T) ∧ IsCompact (futureFace L T) :=
  ⟨isCompact_singleton.prod isCompact_univ, isCompact_singleton.prod isCompact_univ⟩

theorem compact_closure (T : ℝ) : IsCompact (closure (slab L T)) :=
  Ultrastatic.isCompact_closure_slab T

/-- The actual quotient spatial distance agrees with the Euclidean metric on
small covering neighborhoods. No supremum-metric replacement is used. -/
theorem locally_euclidean (a : DimensionSpatial 3) {u v : DimensionSpatial 3}
    (hu : ‖u - a‖ < L / 4) (hv : ‖v - a‖ < L / 4) :
    (spatialDistance L).distance (cover L u) (cover L v) = ‖v - u‖ := by
  apply distance_cover_on_cube L u v
  have hn : ‖v - u‖ < L / 2 := by
    calc
      ‖v - u‖ = ‖(v - a) + (a - u)‖ := by congr 1; abel
      _ ≤ ‖v - a‖ + ‖a - u‖ := norm_add_le _ _
      _ < L / 2 := by rw [norm_sub_rev a u]; linarith
  intro i
  have hi := (PiLp.norm_apply_le (v - u) i).trans_lt hn
  simp only [PiLp.sub_apply, Real.norm_eq_abs, abs_lt] at hi
  constructor <;> linarith

/-- Constant Lorentz metric in every affine covering chart. Its inverse has the
same entries. Deck transformations are translations, not additional boundaries. -/
def chartMetric (_z : Spacetime) (i j : Fin 4) : ℝ :=
  if i = j then if i = 0 then 1 else -1 else 0

theorem chartMetric_inverse (z : Spacetime) (i j : Fin 4) :
    (∑ k : Fin 4, chartMetric z i k * chartMetric z k j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [chartMetric, Fin.sum_univ_four]

theorem chartMetric_translation (z b : Spacetime) : chartMetric (z + b) = chartMetric z := rfl

/-- The two complete faces are smooth constant-time graphs in every covering chart. -/
theorem face_graphs_smooth (T : ℝ) :
    ContDiff ℝ ⊤ (fun _ : DimensionSpatial 3 => -T / 2) ∧
    ContDiff ℝ ⊤ (fun _ : DimensionSpatial 3 => T / 2) :=
  ⟨contDiff_const, contDiff_const⟩

theorem chartMetric_quadratic (p z : Spacetime) :
    (∑ i : Fin 4, ∑ j : Fin 4, chartMetric p i j * z i * z j) =
      z 0 ^ 2 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := by
  norm_num [chartMetric, Fin.sum_univ_four,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  ring

/-- Levi-Civita coefficients calculated from the metric and its inverse. -/
def chartConnection (z : Spacetime) (i j k : Fin 4) : ℝ :=
  (1 / 2) * ∑ m : Fin 4, chartMetric z i m *
    (fderiv ℝ (fun p => chartMetric p m k) z (Pi.single j 1) +
      fderiv ℝ (fun p => chartMetric p m j) z (Pi.single k 1) -
      fderiv ℝ (fun p => chartMetric p j k) z (Pi.single m 1))

@[simp] theorem chartConnection_zero (z : Spacetime) (i j k : Fin 4) : chartConnection z i j k = 0 := by
  simp [chartConnection, chartMetric]

/-- Curvature of the calculated connection (the zero result is sign independent). -/
def chartCurvature (z : Spacetime) (i j k l : Fin 4) : ℝ :=
  fderiv ℝ (fun p => chartConnection p i l j) z (Pi.single k 1) -
    fderiv ℝ (fun p => chartConnection p i k j) z (Pi.single l 1) +
    ∑ m : Fin 4, (chartConnection z i k m * chartConnection z m l j -
      chartConnection z i l m * chartConnection z m k j)

@[simp] theorem chartCurvature_zero (z : Spacetime) (i j k l : Fin 4) : chartCurvature z i j k l = 0 := by
  simp [chartCurvature]

/-- Metric contraction of the independently calculated Ricci tensor. -/
def chartScalar (z : Spacetime) : ℝ :=
  ∑ j : Fin 4, ∑ l : Fin 4, chartMetric z j l * ∑ i : Fin 4, chartCurvature z i j i l

@[simp] theorem chartScalar_zero (z : Spacetime) : chartScalar z = 0 := by simp [chartScalar]

/-- Scalar on the actual quotient, evaluated in covering coordinates. The next
lemma makes the representative choice irrelevant, including every seam. -/
def scalarCurvature (x : ℝ × Space L) : ℝ :=
  chartScalar (fun i => if h : i = 0 then x.1 else centeredLift L x.2 ⟨i.val - 1, by omega⟩)

theorem scalarCurvature_eq_chart (x : ℝ × Space L) (z : Spacetime) :
    scalarCurvature L x = chartScalar z := by simp [scalarCurvature]

@[simp] theorem scalarCurvature_zero (x : ℝ × Space L) : scalarCurvature L x = 0 := by
  simp [scalarCurvature]

/-- Constant-time tangent vectors are strictly spacelike for the same metric. -/
theorem face_spacelike (v : DimensionSpatial 3) (hv : v ≠ 0) :
    dimensionMinkowski 3 (0, v) (0, v) < 0 := by
  change (0 : ℝ) * 0 - @inner ℝ (DimensionSpatial 3) _ v v < 0
  rw [mul_zero, zero_sub, real_inner_self_eq_norm_sq]
  exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))

/-- Independent bulk target: curvature contraction, not an action coefficient. -/
theorem bulk_target_zero (T : ℝ) : (1 / 2 : ℝ) * ∫ x, scalarCurvature L x ∂slabVolume L T = 0 := by
  simp

omit [Fact (0 < L)] in
/-- Empty joint gives zero for any induced measure and any angle weight; no
zero-angle limit or boundary-measure normalization is needed. -/
theorem joint_target_zero {T : ℝ} (hT : 0 < T)
    (μ : Measure (ℝ × Space L)) (weight : (ℝ × Space L) → ℝ) :
    (∫ x in pastFace L T ∩ futureFace L T, weight x ∂μ) = 0 := by
  rw [joint_empty L hT]
  simp

end CompactTorus
end BoundaryDraft
