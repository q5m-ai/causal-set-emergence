import BoundaryDraft.Pilot3Metric

/-!
# Finite canonical candidate area and actual one-dimensional Gram algebra

These results prove finiteness and integrability independently of the action.
The pointwise chart derivative and reparameterization factors below are not a
proof of the variable-density Hausdorff area formula or global collar coarea.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- Exact line normalization, on every set, including nonmeasurable sets. -/
theorem pilot3_line_normalization (v : Pilot3Space) (s : Set ℝ) :
    (μH[1] : Measure Pilot3Space) ((fun r => r • v) '' s) = ‖v‖₊ • volume s := by
  simpa only [hausdorffMeasure_real] using hausdorffMeasure_smul_right_image v s

theorem pilot3AreaDensity_nonneg (h f : Pilot3Space → ℝ) (x : Pilot3Space) :
    0 ≤ pilot3AreaDensity h f x := Real.sqrt_nonneg _

theorem pilot3AreaDensity_le_one (h f : Pilot3Space → ℝ) (x : Pilot3Space) :
    pilot3AreaDensity h f x ≤ 1 := by
  have := Real.sqrt_le_sqrt (show 1 - ‖pilot3TangentialGradient h f x‖ ^ 2 ≤ 1 by
    linarith [sq_nonneg ‖pilot3TangentialGradient h f x‖])
  simpa only [Real.sqrt_one] using this

theorem pilot3ProjectedArea_le (h f : Pilot3Space → ℝ) :
    pilot3ProjectedArea h f ≤ pilot3SurfaceMeasure h := by
  calc
    _ ≤ (pilot3SurfaceMeasure h).withDensity (fun _ => 1) :=
      withDensity_mono (Eventually.of_forall fun x => by
        simpa using ENNReal.ofReal_le_ofReal (pilot3AreaDensity_le_one h f x))
    _ = _ := by simp

theorem pilot3ProjectedArea_restrict_joint (h f : Pilot3Space → ℝ)
    (hJ : MeasurableSet (pilot3SpatialJoint h)) :
    (pilot3ProjectedArea h f).restrict (pilot3SpatialJoint h) = pilot3ProjectedArea h f := by
  rw [pilot3ProjectedArea, restrict_withDensity hJ, pilot3SurfaceMeasure,
    Measure.restrict_restrict_of_subset (Subset.refl (pilot3SpatialJoint h))]

@[simp] theorem pilot3AreaDensity_planar (h : Pilot3Space → ℝ) (x : Pilot3Space) :
    pilot3AreaDensity h (fun _ => 0) x = 1 := by
  simp [pilot3AreaDensity, pilot3TangentialGradient]

@[simp] theorem pilot3ProjectedArea_planar (h : Pilot3Space → ℝ) :
    pilot3ProjectedArea h (fun _ => 0) = pilot3SurfaceMeasure h := by simp [pilot3ProjectedArea]

private theorem plane_gram_identity (q n v : Pilot3Space) :
    ‖v‖ ^ 2 * (‖q‖ ^ 2 * ‖n‖ ^ 2 - inner (𝕜 := ℝ) q n ^ 2) =
      ‖n‖ ^ 2 * inner (𝕜 := ℝ) q v ^ 2 -
        2 * inner (𝕜 := ℝ) n v * inner (𝕜 := ℝ) q n * inner (𝕜 := ℝ) q v +
          ‖q‖ ^ 2 * inner (𝕜 := ℝ) n v ^ 2 := by
  simp [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct, Fin.sum_univ_succ]
  ring

/-- In the spatial plane the joint tangent is one-dimensional. Its actual
induced line element has the Lorentzian factor, not sqrt(1+|b|²). -/
theorem pilot3Graph_gram (q n v : Pilot3Space) (hn : ‖n‖ = 1)
    (hv : inner (𝕜 := ℝ) n v = 0) :
    pilot3GramDensity (pilot3GraphTangent q v) =
      Real.sqrt (1 - ‖q - inner (𝕜 := ℝ) q n • n‖ ^ 2) * ‖v‖ := by
  have hi := plane_gram_identity q n v
  simp only [hn, one_pow, mul_one, one_mul, hv, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, sub_zero, add_zero] at hi
  rw [pilot3GramDensity, pilot3GraphTangent, dimensionMinkowski_apply,
    real_inner_self_eq_norm_sq, pilot3_tangential_norm_sq q n hn]
  have he : -(inner (𝕜 := ℝ) q v * inner (𝕜 := ℝ) q v - ‖v‖ ^ 2) =
      (1 - (‖q‖ ^ 2 - inner (𝕜 := ℝ) q n ^ 2)) * ‖v‖ ^ 2 := by nlinarith [hi]
  rw [he, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem finite_projectedArea : IsFiniteMeasure (pilot3ProjectedArea h f) := by
  letI := hf.toPilot3RegularHeight.finite_surfaceMeasure
  exact isFiniteMeasure_of_le (pilot3SurfaceMeasure h) (pilot3ProjectedArea_le h f)

theorem finite_jointArea : IsFiniteMeasure (pilot3JointArea h f) := by
  letI := hf.finite_projectedArea
  exact Measure.isFiniteMeasure_map _ _

theorem measurableEmbedding_lift : MeasurableEmbedding (pilot3Lift f) := by
  apply (hf.continuous_future.prodMk continuous_id).measurableEmbedding
  intro x y he
  exact congrArg Prod.snd he

/-- Transport of observables to the ACTUAL spacetime joint. This is the
pushforward definition, not an assertion of the missing chart area formula. -/
theorem integral_jointArea (w : Pilot3Spacetime → ℝ) :
    (∫ p, w p ∂pilot3JointArea h f) = ∫ x, w (pilot3Lift f x) ∂pilot3ProjectedArea h f :=
  hf.measurableEmbedding_lift.integral_map w

theorem boundaryIntegral_eq_joint : pilot3BoundaryIntegral h f =
    ∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f :=
  (hf.integral_jointArea (fun p => pilot3Weight h f p.2)).symm

theorem integrable_weight : Integrable (pilot3Weight h f) (pilot3ProjectedArea h f) := by
  letI := hf.finite_projectedArea
  have hi := hf.continuousOn_weight.integrableOn_compact
    (μ := pilot3ProjectedArea h f) hf.toPilot3RegularHeight.isCompact_joint
  simpa only [IntegrableOn, pilot3ProjectedArea_restrict_joint h f
    hf.toPilot3RegularHeight.measurableSet_joint] using hi

theorem integrable_areaDensity : Integrable (pilot3AreaDensity h f) (pilot3SurfaceMeasure h) := by
  letI := hf.toPilot3RegularHeight.finite_surfaceMeasure
  have hi := hf.continuousOn_areaDensity.integrableOn_compact
    (μ := pilot3SurfaceMeasure h) hf.toPilot3RegularHeight.isCompact_joint
  simpa only [IntegrableOn, pilot3SurfaceMeasure,
    Measure.restrict_restrict_of_subset (Subset.refl (pilot3SpatialJoint h))] using hi

/-- Compactness also gives a positive angle margin for each fixed member,
including the empty-joint case without assuming a minimum is attained. -/
theorem exists_angle_margin : ∃ ε : ℝ, 0 < ε ∧
    ∀ x ∈ pilot3SpatialJoint h, 1 + ε ≤ pilot3Cosh h f x := by
  obtain ⟨ε, hε, hb⟩ := hf.toPilot3RegularHeight.isCompact_joint.exists_forall_le'
    (hf.continuousOn_cosh.sub continuousOn_const) (fun x hx => sub_pos.mpr (hf.cosh_gt_one x hx))
  exact ⟨ε, hε, fun x hx => by have := hb x hx; linarith⟩

theorem gramDensity (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h)
    (v : Pilot3Space) (hv : fderiv ℝ h x v = 0) :
    pilot3GramDensity (fderiv ℝ f x v, v) = pilot3AreaDensity h f x * ‖v‖ := by
  have hn := hf.toPilot3RegularHeight.inward_norm x hx
  have hvn : inner (𝕜 := ℝ) (pilot3Inward h x) v = 0 := by
    rw [pilot3_differential_eq_inner] at hv
    simp [pilot3Inward, inner_smul_left, hv]
  rw [pilot3_differential_eq_inner]
  exact pilot3Graph_gram _ _ _ hn hvn

/-- Actual derivative of any differentiable level parameterization. This
checks the geometric factor needed by a subsequent area-formula proof. -/
theorem hasDerivAt_lift {X : ℝ → Pilot3Space} {v : Pilot3Space} {u : ℝ}
    (hX : HasDerivAt X v u) (hx : X u ∈ pilot3ClosedPositive h) :
    HasDerivAt (fun t => pilot3Lift f (X t)) (fderiv ℝ f (X u) v, v) u := by
  exact (((hf.future_smoothAt _ hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt u hX).prodMk hX

theorem chart_gramDensity {X : ℝ → Pilot3Space} {v : Pilot3Space} {u : ℝ}
    (hX : HasDerivAt X v u) (hx : X u ∈ pilot3SpatialJoint h)
    (hlevel : (fun t => h (X t)) =ᶠ[𝓝 u] (fun _ => 0)) :
    pilot3GramDensity (deriv (fun t => pilot3Lift f (X t)) u) =
      pilot3AreaDensity h f (X u) * ‖v‖ := by
  have hd := ((hf.toPilot3RegularHeight.smoothAt _ hx.1).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt u hX
  have hz := (hd.congr_of_eventuallyEq hlevel.symm).unique (hasDerivAt_const u (0 : ℝ))
  rw [(hf.hasDerivAt_lift hX hx.1).deriv]
  exact hf.gramDensity _ hx v hz

end SmoothPilot3

/-- Exact planar weight under the SAME smooth pilot, with no new action limit. -/
theorem pilot3Weight_planar {h : Pilot3Space → ℝ} (hh : SmoothPilot3 h (fun _ => 0))
    (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    pilot3Weight h (fun _ => 0) x = 1 / ‖pilot3Gradient h x‖ := by
  have hk := hh.toPilot3RegularHeight.gradient_pos x hx
  obtain ⟨κ, η, _, hη, hb, hslope⟩ := hh.exists_slope_bounds
  have hk1 : ‖pilot3Gradient h x‖ < 1 := by have := (hslope x hx.1).1; linarith
  have hd : 0 < 1 - ‖pilot3Gradient h x‖ ^ 2 := by nlinarith
  have hs := Real.sqrt_pos.mpr hd
  have hs2 := Real.sq_sqrt hd.le
  have hC : pilot3Cosh h (fun _ => 0) x = 1 / Real.sqrt (1 - ‖pilot3Gradient h x‖ ^ 2) := by
    change dimensionMinkowski 2 (pilot3UnitNormal _) (pilot3UnitNormal _) = _
    rw [pilot3UnitNormal_inner, hh.gradient_past x hx.1]
    simp
  have hd2 : (1 / Real.sqrt (1 - ‖pilot3Gradient h x‖ ^ 2)) ^ 2 - 1 =
      (‖pilot3Gradient h x‖ / Real.sqrt (1 - ‖pilot3Gradient h x‖ ^ 2)) ^ 2 := by field_simp
  rw [pilot3Weight, hC, hd2, Real.sqrt_sq (div_pos hk hs).le]
  field_simp

theorem pilot3BoundaryIntegral_planar {h : Pilot3Space → ℝ} (hh : SmoothPilot3 h (fun _ => 0)) :
    pilot3BoundaryIntegral h (fun _ => 0) =
      ∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h := by
  unfold pilot3BoundaryIntegral
  rw [pilot3ProjectedArea_planar]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hh.toPilot3RegularHeight.measurableSet_joint] with x hx
  exact pilot3Weight_planar hh x hx

end BoundaryDraft
