import BoundaryDraft.Pilot3Surface

/-!
# Pilot3Space expression of the independently defined three-dimensional target

The coefficient identification is purely geometric. It neither defines the
joint area using the action nor assumes a limit for the short contribution.
All square roots and divisions use the positive branches derived from the
unchanged `SmoothPilot3` conditions. The one-dimensional Hausdorff measure retains normalization one.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 800000
namespace BoundaryDraft
namespace SmoothPilot3

variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

private theorem aemeasurable_coefficientAreaDensity :
    AEMeasurable (fun x => ENNReal.ofReal (pilot3AreaDensity h f x)) (pilot3SurfaceMeasure h) :=
  hf.integrable_areaDensity.aestronglyMeasurable.aemeasurable.ennreal_ofReal

/-- The angle weight times Lorentzian area density, expressed in the original
spatial coordinates. No action or analytic limiting assumption enters this identity. -/
theorem weight_mul_areaDensity (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    pilot3Weight h f x * pilot3AreaDensity h f x =
      (1 - ‖pilot3Gradient f x‖ ^ 2 +
        inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x)) /
          ‖pilot3Gradient h x‖ := by
  let p := pilot3Gradient f x
  let g := pilot3Gradient h x
  let k := ‖g‖
  let a := pilot3AreaDensity h f x
  let C := pilot3Cosh h f x
  let d := Real.sqrt (1 - ‖p - g‖ ^ 2) * Real.sqrt (1 - ‖p‖ ^ 2)
  let N := 1 - ‖p‖ ^ 2 + inner (𝕜 := ℝ) p g
  have hk : 0 < k := hf.toPilot3RegularHeight.gradient_pos x hx
  have ha : 0 < a := hf.areaDensity_pos x hx
  have hC : 1 < C := hf.cosh_gt_one x hx
  have hp : ‖p‖ < 1 := (hf.face_slopes_lt_one x hx.1).1
  have hpg : ‖p - g‖ < 1 := by
    simpa only [hf.gradient_past x hx.1] using (hf.face_slopes_lt_one x hx.1).2
  have hd₁ : 0 < 1 - ‖p - g‖ ^ 2 := by nlinarith [norm_nonneg (p - g)]
  have hd₂ : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hd : 0 < d := mul_pos (Real.sqrt_pos.mpr hd₁) (Real.sqrt_pos.mpr hd₂)
  have hd_sq : d ^ 2 = (1 - ‖p - g‖ ^ 2) * (1 - ‖p‖ ^ 2) := by
    dsimp [d]
    rw [mul_pow, Real.sq_sqrt hd₁.le, Real.sq_sqrt hd₂.le]
  have hC_eq : C = N / d := by
    change dimensionMinkowski 2 (pilot3UnitNormal _) (pilot3UnitNormal _) = _
    rw [pilot3UnitNormal_inner, hf.gradient_past x hx.1]
    dsimp only [N, d, p, g]
    rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm
      (pilot3Gradient h x) (pilot3Gradient f x)]
    ring
  have ht : ‖pilot3TangentialGradient h f x‖ ^ 2 =
      ‖p‖ ^ 2 - (k⁻¹ * inner (𝕜 := ℝ) p g) ^ 2 := by
    rw [pilot3TangentialGradient, pilot3_tangential_norm_sq _ _
      (hf.toPilot3RegularHeight.inward_norm x hx)]
    simp only [pilot3Inward, inner_smul_right]
    rfl
  have ha_sq : a ^ 2 = 1 - ‖p‖ ^ 2 + (k⁻¹ * inner (𝕜 := ℝ) p g) ^ 2 := by
    have hrad : 0 ≤ 1 - ‖pilot3TangentialGradient h f x‖ ^ 2 :=
      (Real.sqrt_pos.mp ha).le
    dsimp only [a, pilot3AreaDensity]
    rw [Real.sq_sqrt hrad, ht]
    ring
  have hnorm : ‖p - g‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner (𝕜 := ℝ) p g + k ^ 2 :=
    norm_sub_sq_real p g
  have hdet : N ^ 2 - d ^ 2 = (k * a) ^ 2 := by
    rw [mul_pow k a, ha_sq, hd_sq, hnorm]
    dsimp only [N]
    field_simp [hk.ne']
    ring
  have hCd : C * d = N := (eq_div_iff hd.ne').mp hC_eq
  have hs : 0 < Real.sqrt (C ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hs_sq := Real.sq_sqrt (show 0 ≤ C ^ 2 - 1 by nlinarith)
  have hroot : d * Real.sqrt (C ^ 2 - 1) = k * a := by
    apply (sq_eq_sq₀ (mul_pos hd hs).le (mul_pos hk ha).le).mp
    rw [mul_pow d (Real.sqrt (C ^ 2 - 1)), hs_sq]
    nlinarith only [hdet, congrArg (fun t : ℝ => t ^ 2) hCd]
  change C / Real.sqrt (C ^ 2 - 1) * a = N / k
  apply (eq_div_iff hk.ne').mpr
  field_simp [hs.ne']
  nlinarith only [congrArg (fun t : ℝ => C * t) hroot,
    congrArg (fun t : ℝ => t * Real.sqrt (C ^ 2 - 1)) hCd]

/-- Finiteness precedes the target conversion. The spatial integrand is not
assigned the totalized nonintegrable integral value. -/
theorem integrable_boundaryCoefficient :
    Integrable (fun x =>
      (1 - ‖pilot3Gradient f x‖ ^ 2 +
        inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x)) /
          ‖pilot3Gradient h x‖) (pilot3SurfaceMeasure h) := by
  have hi := (integrable_withDensity_iff_integrable_smul₀'
    hf.aemeasurable_coefficientAreaDensity
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hf.integrable_weight
  apply hi.congr
  filter_upwards [ae_restrict_mem hf.toPilot3RegularHeight.measurableSet_joint] with x hx
  rw [ENNReal.toReal_ofReal (pilot3AreaDensity_nonneg h f x), smul_eq_mul, mul_comm]
  exact hf.weight_mul_areaDensity x hx

/-- The original induced-area angle integral equals the spatial coefficient,
without redefining either the target or the admissibility class. -/
theorem boundaryIntegral_eq_spatialCoefficient :
    pilot3BoundaryIntegral h f =
      ∫ x, (1 - ‖pilot3Gradient f x‖ ^ 2 +
        inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x)) /
          ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h := by
  unfold pilot3BoundaryIntegral pilot3ProjectedArea
  rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable_coefficientAreaDensity
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hf.toPilot3RegularHeight.measurableSet_joint] with x hx
  rw [ENNReal.toReal_ofReal (pilot3AreaDensity_nonneg h f x), smul_eq_mul, mul_comm]
  exact hf.weight_mul_areaDensity x hx

end SmoothPilot3
end BoundaryDraft
