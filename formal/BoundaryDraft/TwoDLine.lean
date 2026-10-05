import BoundaryDraft.TwoDCoordinates
import BoundaryDraft.TwoDMetric

/-! # Isometric real coordinate and BOTH unit spatial directions -/

open MeasureTheory Set
open scoped Topology Pointwise
noncomputable section
namespace BoundaryDraft

def twoDLine : TwoDSpace ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)
  norm_map' x := by
    simp [EuclideanSpace.norm_eq, LinearEquiv.funUnique, LinearEquiv.trans_apply,
      Real.sqrt_sq_eq_abs, norm_nonneg]

@[simp] theorem twoDLine_apply (x : TwoDSpace) : twoDLine x = x 0 := rfl

@[simp] theorem twoDLine_symm_apply (t : ℝ) (i : Fin 1) : twoDLine.symm t i = t := rfl

theorem twoD_norm_eq (x : TwoDSpace) : ‖x‖ = |x 0| := (twoDLine.norm_map x).symm

theorem twoD_inner_eq (x y : TwoDSpace) : inner (𝕜 := ℝ) x y = x 0 * y 0 := by
  rw [← twoDLine.inner_map_map]
  simp [RCLike.inner_apply, mul_comm]

theorem twoDLine_measurePreserving : MeasurePreserving twoDLine volume volume :=
  twoDLine.measurePreserving

def twoDRight : TwoDDirection := ⟨twoDLine.symm 1, by simp [Metric.mem_sphere, dist_zero_right]⟩
def twoDLeft : TwoDDirection := ⟨twoDLine.symm (-1), by simp [Metric.mem_sphere, dist_zero_right]⟩

theorem twoDRight_ne_left : twoDRight ≠ twoDLeft := by
  intro he
  have he := congrArg (fun ω : TwoDDirection => twoDLine ω.val) he
  norm_num [twoDRight, twoDLeft] at he

/-- There are exactly two directions, not a chosen hemisphere. -/
theorem twoDDirection_cases (ω : TwoDDirection) : ω = twoDRight ∨ ω = twoDLeft := by
  have hn : |ω.val 0| = 1 := by
    rw [← twoD_norm_eq]
    exact mem_sphere_zero_iff_norm.mp ω.property
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with hp | hm
  · left
    apply Subtype.ext
    apply twoDLine.injective
    simpa [twoDRight] using hp
  · right
    apply Subtype.ext
    apply twoDLine.injective
    simpa [twoDLeft] using hm

private theorem volume_line_image (s : Set ℝ) (hs : MeasurableSet s) :
    volume (twoDLine.symm '' s) = volume s := by
  have he : twoDLine.symm '' s = twoDLine ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa only [mem_preimage, twoDLine.apply_symm_apply] using ht
    · intro hx
      exact ⟨twoDLine x, hx, twoDLine.symm_apply_apply x⟩
  rw [he, ← Measure.map_apply twoDLine.continuous.measurable hs, twoDLine.measurePreserving.map_eq]

/-- Each of the two atoms has unit mass in the actual polar measure. -/
theorem twoDDirectionMeasure_right : twoDDirectionMeasure {twoDRight} = 1 := by
  rw [twoDDirectionMeasure, Measure.toSphere_apply' volume (measurableSet_singleton _),
    image_singleton, smul_singleton]
  have he : (fun t : ℝ => t • twoDRight.val) = twoDLine.symm := by
    funext t
    apply twoDLine.injective
    simp [twoDRight]
  rw [he, volume_line_image _ measurableSet_Ioo]
  norm_num [TwoDSpace, DimensionSpatial, Real.volume_Ioo]

theorem twoDDirectionMeasure_left : twoDDirectionMeasure {twoDLeft} = 1 := by
  rw [twoDDirectionMeasure, Measure.toSphere_apply' volume (measurableSet_singleton _),
    image_singleton, smul_singleton]
  have he : (fun t : ℝ => t • twoDLeft.val) '' Ioo (0 : ℝ) 1 =
      twoDLine.symm '' Ioo (-1 : ℝ) 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      apply twoDLine.injective
      simp [twoDLeft]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      apply twoDLine.injective
      simp [twoDLeft]
  rw [he, volume_line_image _ measurableSet_Ioo]
  norm_num [TwoDSpace, DimensionSpatial, Real.volume_Ioo]

/-- Exact two-atom identity for ANY observable, including nonradial ones. -/
theorem twoDDirectionMeasure_eq_dirac :
    twoDDirectionMeasure = Measure.dirac twoDRight + Measure.dirac twoDLeft := by
  have hu : (univ : Set TwoDDirection) = {twoDRight, twoDLeft} := by
    ext ω
    simp only [mem_univ, mem_insert_iff, mem_singleton_iff, true_iff]
    exact twoDDirection_cases ω
  haveI : Finite TwoDDirection := finite_univ_iff.mp (by
    rw [hu]
    exact (finite_singleton twoDLeft).insert twoDRight)
  apply Measure.ext_of_singleton
  intro ω
  rcases twoDDirection_cases ω with rfl | rfl
  · simp [twoDDirectionMeasure_right, Measure.add_apply, indicator,
      twoDRight_ne_left, twoDRight_ne_left.symm]
  · simp [twoDDirectionMeasure_left, Measure.add_apply, indicator,
      twoDRight_ne_left, twoDRight_ne_left.symm]

end BoundaryDraft
