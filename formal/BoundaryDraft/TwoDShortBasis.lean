import BoundaryDraft.TwoDShortAngular
import BoundaryDraft.TwoDShortRemainder
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! # Genuine 2D logarithmic short-polynomial density -/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDShortBasis

/-- The actual two-direction polynomial multiplied by the 2D null Jacobian. -/
def fibre (V A T S σ v : ℝ) : ℝ :=
  (1 / (2 * v)) * (2 * V - 2 * A * ((v + σ / v) / 2) +
    T * ((v + σ / v) / 2) ^ 2 + S * ((v - σ / v) / 2) ^ 2)

def primitive (V A T S σ v : ℝ) : ℝ :=
  V * Real.log v - (A / 2) * (v - σ / v) +
    ((T + S) / 16) * (v ^ 2 - σ ^ 2 / v ^ 2) + ((T - S) * σ / 4) * Real.log v

theorem hasDerivAt_primitive (V A T S σ v : ℝ) (hv : v ≠ 0) :
    HasDerivAt (primitive V A T S σ) (fibre V A T S σ v) v := by
  have hl := Real.hasDerivAt_log hv
  have hlin := ((hasDerivAt_id v).sub ((hasDerivAt_const v σ).div (hasDerivAt_id v) hv)).const_mul (A / 2)
  have hsq := (((hasDerivAt_id v).pow 2).sub
    ((hasDerivAt_const v (σ ^ 2)).div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv))).const_mul ((T + S) / 16)
  convert (((hl.const_mul V).sub hlin).add hsq).add (hl.const_mul ((T - S) * σ / 4)) using 1
  dsimp only [fibre, id_eq]
  field_simp
  ring

theorem primitive_sqrt (V A T S : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    primitive V A T S σ (Real.sqrt σ) =
      (V / 2) * Real.log σ + ((T - S) / 8) * σ * Real.log σ := by
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hlog : Real.log (Real.sqrt σ) = Real.log σ / 2 := Real.log_sqrt hσ.le
  have hdiv : σ / Real.sqrt σ = Real.sqrt σ := by
    apply (div_eq_iff hs.ne').mpr
    exact (Real.mul_self_sqrt hσ.le).symm
  rw [primitive, hlog, hdiv, Real.sq_sqrt hσ.le, sub_self, mul_zero, sub_zero]
  field_simp [hσ.ne']
  ring

/-- Log sectors and the remaining exact polynomial terms, before any kernel
response is taken. The interval is bounded away from the singular vertex. -/
theorem integral_fibre (V A T S : ℝ) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hσδ : σ ≤ δ ^ 2) :
    (∫ v in Real.sqrt σ..δ, fibre V A T S σ v) =
      V * Real.log δ - A * δ / 2 + (T + S) * δ ^ 2 / 16 +
      (A / (2 * δ) + (T - S) * Real.log δ / 4) * σ -
      (V / 2) * Real.log σ - ((T - S) / 8) * σ * Real.log σ -
      (T + S) / (16 * δ ^ 2) * σ ^ 2 := by
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hsδ : Real.sqrt σ ≤ δ := (Real.sqrt_le_iff).mpr ⟨hδ.le, hσδ⟩
  have hn {v : ℝ} (hv : v ∈ uIcc (Real.sqrt σ) δ) : v ≠ 0 := by
    rw [uIcc_of_le hsδ] at hv
    exact (hs.trans_le hv.1).ne'
  have hi : IntervalIntegrable (fibre V A T S σ) volume (Real.sqrt σ) δ := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    have hv0 := hn hv
    have hv2 : 2 * v ≠ 0 := mul_ne_zero (by norm_num) hv0
    exact (show ContinuousAt (fibre V A T S σ) v by unfold fibre; fun_prop (disch := assumption)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => hasDerivAt_primitive V A T S σ v (hn hv)) hi,
    primitive_sqrt V A T S hσ, primitive]
  field_simp [hδ.ne']
  ring

end TwoDShortBasis

/-- Angular integration is ordinary integration against the two unit atoms. -/
def twoDShortPolynomialDensity (h f : TwoDSpace → ℝ) (δ σ : ℝ) : ℝ :=
  ∫ v in Real.sqrt σ..δ, twoDNullJacobian σ v *
    (∫ ω : TwoDDirection, twoDAbsoluteShortPolynomial h f (TwoDShortRemainder.point ω v σ)
      ∂twoDDirectionMeasure)

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- The logarithmic coefficient is the independently fixed normal-angle
boundary integral, as proved by whole-region FTC and complete endpoint counting. -/
theorem shortPolynomialDensity_eq {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hσδ : σ ≤ δ ^ 2) :
    twoDShortPolynomialDensity h f δ σ =
      volume.real (twoDRegion h f) * Real.log δ - volume.real {x | 0 < h x} * δ / 2 +
      (twoDShortTimeCoefficient h + twoDShortSpaceCoefficient h f) * δ ^ 2 / 16 +
      (volume.real {x | 0 < h x} / (2 * δ) + twoDBoundaryIntegral h f * Real.log δ / 4) * σ -
      (volume.real (twoDRegion h f) / 2) * Real.log σ -
      (twoDBoundaryIntegral h f / 8) * σ * Real.log σ -
      (twoDShortTimeCoefficient h + twoDShortSpaceCoefficient h f) / (16 * δ ^ 2) * σ ^ 2 := by
  have he (v : ℝ) : twoDNullJacobian σ v *
      (∫ ω : TwoDDirection, twoDAbsoluteShortPolynomial h f (TwoDShortRemainder.point ω v σ)
        ∂twoDDirectionMeasure) = TwoDShortBasis.fibre (volume.real (twoDRegion h f))
          (volume.real {x | 0 < h x}) (twoDShortTimeCoefficient h) (twoDShortSpaceCoefficient h f) σ v := by
    simp only [TwoDShortRemainder.point]
    rw [hf.integral_directions_absoluteShortPolynomial]
    unfold twoDNullJacobian TwoDShortBasis.fibre
    ring
  simp only [twoDShortPolynomialDensity, he]
  rw [TwoDShortBasis.integral_fibre _ _ _ _ hδ hσ hσδ, hf.short_coefficients_eq_boundaryIntegral]

end SmoothTwoD
end BoundaryDraft
