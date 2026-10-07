import BoundaryDraft.TwoDDivergence
import BoundaryDraft.TwoDShortExpansion

/-! # Genuine two-atom angular average of the actual absolute 2D polynomial -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

theorem integral_twoDDirection (G : TwoDDirection → ℝ) :
    (∫ ω, G ω ∂twoDDirectionMeasure) = G twoDRight + G twoDLeft := by
  rw [twoDDirectionMeasure_eq_dirac, integral_add_measure integrable_dirac integrable_dirac,
    integral_dirac, integral_dirac]

theorem twoDAbsoluteShortPolynomial_line (h f : TwoDSpace → ℝ) (s r : ℝ) :
    twoDAbsoluteShortPolynomial h f (s, twoDLine.symm r) =
      volume.real (twoDRegion h f) - s * volume.real {x | 0 < h x} +
      (∫ x in {x | 0 < h x}, twoDGradient f x 0) * r +
      (1 / 2 : ℝ) * (r ^ 2 * (∫ x in {x | 0 < h x}, twoDFutureHessian f x) +
        ∫ x, (s - twoDGradient f x 0 * r) ^ 2 / ‖twoDGradient h x‖ ∂dimensionTwoJointMeasure h) := by
  have hline : twoDLine.symm r = r • twoDLine.symm 1 := by
    rw [← map_smul]; simp
  have hess (x : TwoDSpace) :
      fderiv ℝ (fderiv ℝ f) x (twoDLine.symm r) (twoDLine.symm r) = r ^ 2 * twoDFutureHessian f x := by
    rw [hline]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, twoDFutureHessian]
    ring
  simp only [twoDAbsoluteShortPolynomial, twoD_inner_eq, twoDLine_symm_apply, hess,
    integral_mul_const, integral_const_mul]

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- Both directions have unit mass. Odd and mixed terms cancel only after
the complete signed two-atom sum. The bulk Hessian and all endpoints remain. -/
theorem integral_directions_absoluteShortPolynomial (s r : ℝ) :
    (∫ ω : TwoDDirection, twoDAbsoluteShortPolynomial h f (s, r • ω.val) ∂twoDDirectionMeasure) =
      2 * volume.real (twoDRegion h f) - 2 * s * volume.real {x | 0 < h x} +
        twoDShortTimeCoefficient h * s ^ 2 + twoDShortSpaceCoefficient h f * r ^ 2 := by
  have he : (∫ x, (s - twoDGradient f x 0 * r) ^ 2 / ‖twoDGradient h x‖ ∂dimensionTwoJointMeasure h) +
      (∫ x, (s - twoDGradient f x 0 * (-r)) ^ 2 / ‖twoDGradient h x‖ ∂dimensionTwoJointMeasure h) =
      2 * s ^ 2 * twoDShortTimeCoefficient h +
        2 * r ^ 2 * (∫ x, twoDGradient f x 0 ^ 2 / ‖twoDGradient h x‖ ∂dimensionTwoJointMeasure h) := by
    rw [← integral_add (hf.endpoint_integral _).1 (hf.endpoint_integral _).1]
    calc
      _ = ∫ x, (2 * s ^ 2) * (1 / ‖twoDGradient h x‖) +
          (2 * r ^ 2) * (twoDGradient f x 0 ^ 2 / ‖twoDGradient h x‖) ∂dimensionTwoJointMeasure h := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_add ((hf.endpoint_integral _).1.const_mul _) ((hf.endpoint_integral _).1.const_mul _),
          integral_const_mul, integral_const_mul]
        rfl
  rw [integral_twoDDirection]
  change twoDAbsoluteShortPolynomial h f (s, r • twoDLine.symm 1) +
    twoDAbsoluteShortPolynomial h f (s, r • twoDLine.symm (-1)) = _
  rw [← map_smul, ← map_smul]
  simp only [smul_eq_mul, mul_one, mul_neg_one, twoDAbsoluteShortPolynomial_line]
  dsimp only [twoDShortSpaceCoefficient]
  nlinarith [he]

end SmoothTwoD
end BoundaryDraft
