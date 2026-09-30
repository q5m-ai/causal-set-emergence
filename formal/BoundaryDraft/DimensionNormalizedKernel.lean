import BoundaryDraft.DimensionActionConstants
import BoundaryDraft.DimensionSliceMellin
import BoundaryDraft.DimensionReduction

/-!
# Normalization of the actual dimension-dependent vertical kernel

The slice and action coefficients were defined independently. Their proved
moments, not extra hypotheses or kernel fields, now imply absolute integrability,
unit mass, and the parity-dependent first height moment.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Actual density-one spatial slice with the published interval coefficient. -/
def dimensionConeSlice (d : ℕ) (t : ℝ) : ℝ :=
  dimensionPhysicalSlice d (dimensionIntervalCoefficient d) t

/-- The original finite-height vertical action reduction, not a mass definition. -/
def dimensionPlaneKernel (d : ℕ) (H : ℝ) : ℝ :=
  verticalActionReduction (dimensionPointCoefficient d) (dimensionPairCoefficient d)
    (dimensionConeSlice d) H

theorem measurable_dimensionConeSlice (d : ℕ) : Measurable (dimensionConeSlice d) := by
  exact measurable_const.mul (measurable_dimensionSigmaSlice d (dimensionIntervalCoefficient d))

theorem integrableOn_dimensionConeSlice_moment (d k : ℕ) (hd : 2 ≤ d) (hk : k ≤ 3) :
    IntegrableOn (fun t : ℝ => t ^ k * dimensionConeSlice d t) (Ioi 0) :=
  integrableOn_dimensionPhysicalSlice_moment d k hd hk (dimensionIntervalCoefficient_pos d hd)

private theorem dimensionConeSlice_even_J0 (n : ℕ) :
    dimensionPairCoefficient (2 * n + 2) *
      (∫ t : ℝ in Ioi 0, dimensionConeSlice (2 * n + 2) t) =
        dimensionPointCoefficient (2 * n + 2) := by
  simp only [dimensionConeSlice]
  rw [integral_dimensionPhysicalSlice_even_J0 n
    (dimensionIntervalCoefficient_pos _ (by omega))]
  have h := dimensionPairCoefficient_even_normalization (2 * n + 2) (by omega) (by omega)
  rw [show (((2 * n + 2 : ℕ) : ℝ) - 2) / 2 = (n : ℝ) by push_cast; ring,
    Real.rpow_natCast,
    show ((2 * n + 2 : ℕ) : ℝ) / 2 + 2 = ((n + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial] at h
  exact h

private theorem dimensionConeSlice_odd_J0 (n : ℕ) :
    dimensionPairCoefficient (2 * n + 3) *
      (∫ t : ℝ in Ioi 0, dimensionConeSlice (2 * n + 3) t) =
        dimensionPointCoefficient (2 * n + 3) := by
  simp only [dimensionConeSlice]
  rw [integral_dimensionPhysicalSlice_odd_J0 n
    (dimensionIntervalCoefficient_pos _ (by omega))]
  have h := dimensionPairCoefficient_odd_normalization (2 * n + 3) (by omega) (by omega)
  rw [show (((2 * n + 3 : ℕ) : ℝ) - 1) / 2 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast,
    show (((2 * n + 3 : ℕ) : ℝ) + 3) / 2 = ((n + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial] at h
  exact h

/-- Zeroth slice normalization is now a theorem of the actual kernel/action. -/
theorem dimensionConeSlice_J0 (d : ℕ) (hd : 2 ≤ d) :
    dimensionPairCoefficient d * (∫ t : ℝ in Ioi 0, dimensionConeSlice d t) =
      dimensionPointCoefficient d := by
  rcases Nat.even_or_odd d with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · cases n with
    | zero => omega
    | succ n =>
      rw [show (n + 1) + (n + 1) = 2 * n + 2 by omega]
      exact dimensionConeSlice_even_J0 n
  · cases n with
    | zero => omega
    | succ n =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
      exact dimensionConeSlice_odd_J0 n

theorem dimensionConeSlice_J1 (d : ℕ) (hd : 2 ≤ d) :
    (∫ t : ℝ in Ioi 0, t * dimensionConeSlice d t) = 0 :=
  integral_dimensionPhysicalSlice_J1 d hd (dimensionIntervalCoefficient_pos d hd)

private theorem dimensionConeSlice_even_J2_ratio (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionConeSlice (2 * n + 2) t) =
      -(∫ t : ℝ in Ioi 0, dimensionConeSlice (2 * n + 2) t) / 2 *
        dimensionIntervalCoefficient (2 * n + 2) ^ (-(2 / ((2 * n + 2 : ℕ) : ℝ))) *
          Real.Gamma (1 + 2 / ((2 * n + 2 : ℕ) : ℝ)) := by
  have hc := dimensionIntervalCoefficient_pos (2 * n + 2) (by omega)
  simp only [dimensionConeSlice]
  rw [integral_dimensionPhysicalSlice_even_J2 n hc, integral_dimensionPhysicalSlice_even_J0 n hc,
    show (-1 : ℝ) - 2 / ((2 * n + 2 : ℕ) : ℝ) =
      -1 + -(2 / ((2 * n + 2 : ℕ) : ℝ)) by ring,
    Real.rpow_add hc, Real.rpow_neg_one]
  ring

private theorem dimensionConeSlice_odd_J2_ratio (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionConeSlice (2 * n + 3) t) =
      -(∫ t : ℝ in Ioi 0, dimensionConeSlice (2 * n + 3) t) *
        dimensionIntervalCoefficient (2 * n + 3) ^ (-(2 / ((2 * n + 3 : ℕ) : ℝ))) *
          Real.Gamma (1 + 2 / ((2 * n + 3 : ℕ) : ℝ)) := by
  have hc := dimensionIntervalCoefficient_pos (2 * n + 3) (by omega)
  simp only [dimensionConeSlice]
  rw [integral_dimensionPhysicalSlice_odd_J2 n hc, integral_dimensionPhysicalSlice_odd_J0 n hc,
    show (-1 : ℝ) - 2 / ((2 * n + 3 : ℕ) : ℝ) =
      -1 + -(2 / ((2 * n + 3 : ℕ) : ℝ)) by ring,
    Real.rpow_add hc, Real.rpow_neg_one]
  ring

private theorem dimensionConeSlice_even_J2 (n : ℕ) :
    -dimensionPairCoefficient (2 * n + 2) *
      (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionConeSlice (2 * n + 2) t) = 2 := by
  rw [dimensionConeSlice_even_J2_ratio]
  have h := dimensionPointCoefficient_rescale (2 * n + 2) (by omega)
  rw [if_pos (by omega : (2 * n + 2) % 2 = 0)] at h
  calc
    _ = ((dimensionPairCoefficient (2 * n + 2) *
        (∫ t : ℝ in Ioi 0, dimensionConeSlice (2 * n + 2) t)) *
        dimensionIntervalCoefficient (2 * n + 2) ^ (-(2 / ((2 * n + 2 : ℕ) : ℝ))) *
          Real.Gamma (1 + 2 / ((2 * n + 2 : ℕ) : ℝ))) / 2 := by ring
    _ = 2 := by rw [dimensionConeSlice_even_J0, h]; norm_num

private theorem dimensionConeSlice_odd_J2 (n : ℕ) :
    -dimensionPairCoefficient (2 * n + 3) *
      (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionConeSlice (2 * n + 3) t) = 2 := by
  rw [dimensionConeSlice_odd_J2_ratio]
  have h := dimensionPointCoefficient_rescale (2 * n + 3) (by omega)
  rw [if_neg (by omega : (2 * n + 3) % 2 ≠ 0)] at h
  calc
    _ = (dimensionPairCoefficient (2 * n + 3) *
        (∫ t : ℝ in Ioi 0, dimensionConeSlice (2 * n + 3) t)) *
        dimensionIntervalCoefficient (2 * n + 3) ^ (-(2 / ((2 * n + 3 : ℕ) : ℝ))) *
          Real.Gamma (1 + 2 / ((2 * n + 3 : ℕ) : ℝ)) := by ring
    _ = 2 := by rw [dimensionConeSlice_odd_J0, h]

/-- The nonzero second slice moment supplies, rather than assumes, unit mass. -/
theorem dimensionConeSlice_J2 (d : ℕ) (hd : 2 ≤ d) :
    -dimensionPairCoefficient d * (∫ t : ℝ in Ioi 0, t ^ 2 * dimensionConeSlice d t) = 2 := by
  rcases Nat.even_or_odd d with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · cases n with
    | zero => omega
    | succ n =>
      rw [show (n + 1) + (n + 1) = 2 * n + 2 by omega]
      exact dimensionConeSlice_even_J2 n
  · cases n with
    | zero => omega
    | succ n =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
      exact dimensionConeSlice_odd_J2 n

theorem dimensionPlaneKernel_eq_tail (d : ℕ) (hd : 2 ≤ d) {H : ℝ} (hH : 0 ≤ H) :
    dimensionPlaneKernel d H = verticalTailReduction (dimensionPairCoefficient d) (dimensionConeSlice d) H := by
  apply verticalActionReduction_eq_tail _ _ _
  · simpa using integrableOn_dimensionConeSlice_moment d 0 hd (by omega)
  · simpa using integrableOn_dimensionConeSlice_moment d 1 hd (by omega)
  · exact dimensionConeSlice_J0 d hd
  · exact dimensionConeSlice_J1 d hd
  · exact hH

private theorem dimensionPlaneKernel_integrable_mass (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (dimensionPlaneKernel d) (Ioi 0) ∧
      (∫ H : ℝ in Ioi 0, dimensionPlaneKernel d H) = 1 := by
  apply integral_verticalActionReduction _ _ _ (measurable_dimensionConeSlice d)
  · simpa using integrableOn_dimensionConeSlice_moment d 0 hd (by omega)
  · simpa using integrableOn_dimensionConeSlice_moment d 1 hd (by omega)
  · exact integrableOn_dimensionConeSlice_moment d 2 hd (by omega)
  · exact dimensionConeSlice_J0 d hd
  · exact dimensionConeSlice_J1 d hd
  · exact dimensionConeSlice_J2 d hd

/-- Absolute integrability of the actual reduced kernel in every dimension. -/
theorem integrableOn_dimensionPlaneKernel (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (dimensionPlaneKernel d) (Ioi 0) :=
  (dimensionPlaneKernel_integrable_mass d hd).1

/-- Unconditional mass-one theorem with the published action normalization. -/
theorem integral_dimensionPlaneKernel (d : ℕ) (hd : 2 ≤ d) :
    (∫ H : ℝ in Ioi 0, dimensionPlaneKernel d H) = 1 :=
  (dimensionPlaneKernel_integrable_mass d hd).2

/-- First height moment is absolutely integrable before its sign is evaluated. -/
theorem integrableOn_dimensionPlaneKernel_first_moment (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (fun H : ℝ => H * dimensionPlaneKernel d H) (Ioi 0) := by
  have hi := integrableOn_verticalTailReduction_moment 1 (dimensionPairCoefficient d)
    (dimensionConeSlice d) (measurable_dimensionConeSlice d)
      (integrableOn_dimensionConeSlice_moment d 3 hd (by omega))
  simp only [pow_one] at hi
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  rw [dimensionPlaneKernel_eq_tail d hd hH.le]

theorem integrableOn_dimensionPlaneKernel_first_abs_moment (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (fun H : ℝ => H * |dimensionPlaneKernel d H|) (Ioi 0) := by
  apply (integrableOn_dimensionPlaneKernel_first_moment d hd).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hH]

theorem integral_dimensionPlaneKernel_first_moment (d : ℕ) (hd : 2 ≤ d) :
    (∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel d H) =
      -dimensionPairCoefficient d / 6 * ∫ t : ℝ in Ioi 0, t ^ 3 * dimensionConeSlice d t := by
  calc
    _ = ∫ H : ℝ in Ioi 0,
        H * verticalTailReduction (dimensionPairCoefficient d) (dimensionConeSlice d) H := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro H hH
      dsimp only
      rw [dimensionPlaneKernel_eq_tail d hd hH.le]
    _ = _ := by
      have h := integral_verticalTailReduction_moment 1 (dimensionPairCoefficient d)
        (dimensionConeSlice d) (measurable_dimensionConeSlice d)
          (integrableOn_dimensionConeSlice_moment d 3 hd (by omega))
      norm_num at h
      exact h

/-- Even dimensions retain the checked 4D first-height-moment cancellation. -/
theorem integral_dimensionPlaneKernel_even_first (n : ℕ) :
    (∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel (2 * n + 2) H) = 0 := by
  rw [integral_dimensionPlaneKernel_first_moment _ (by omega)]
  simp only [dimensionConeSlice]
  rw [integral_dimensionPhysicalSlice_even_J3 n (dimensionIntervalCoefficient_pos _ (by omega)),
    mul_zero]

/-- Odd dimensions do not have the 4D zero first moment. -/
theorem integral_dimensionPlaneKernel_odd_first_pos (n : ℕ) :
    0 < ∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel (2 * n + 3) H := by
  rw [integral_dimensionPlaneKernel_first_moment _ (by omega)]
  exact mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr (dimensionPairCoefficient_pos _ (by omega)))
      (by norm_num))
    (integral_dimensionPhysicalSlice_odd_J3_neg n (dimensionIntervalCoefficient_pos _ (by omega)))

/-- The scalar regulated limit has no normalization premise left. Its use for
an action still goes through the independently proved finite spacetime reduction. -/
theorem dimensionPlaneKernel_regulated_limit (d : ℕ) (hd : 2 ≤ d)
    (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hbound : ∀ s, ‖χ s‖ ≤ C)
    (hχ₀ : χ 0 = 1) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ρ : ℝ => regulatedVerticalReduction (dimensionPlaneKernel d) χ κ
      (ρ ^ (1 / (d : ℝ)))) atTop (𝓝 (1 / κ)) :=
  regulatedVerticalReduction_density_limit d (by omega) _ χ
    (integrableOn_dimensionPlaneKernel d hd) (integral_dimensionPlaneKernel d hd)
    hχ C hbound hχ₀ hκ

/-- Fixed-cutoff rate with the actual first absolute height moment. There is
no uniform zero-angle or regulator-removal assertion. -/
theorem dimensionPlaneKernel_regulated_error (d : ℕ) (hd : 2 ≤ d)
    (B : ℝ → ℝ) (hB : Measurable B) (C L : ℝ)
    (hbound : ∀ r, 0 ≤ r → ‖B r‖ ≤ C)
    (hLip : ∀ r, 0 ≤ r → ‖B r - B 0‖ ≤ L * r)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    ‖regulatedVerticalReduction (dimensionPlaneKernel d) B κ (ρ ^ (1 / (d : ℝ))) -
        κ⁻¹ * B 0‖ ≤
      (L * (ρ ^ (1 / (d : ℝ)))⁻¹ / κ ^ 2) *
        ∫ u : ℝ in Ioi 0, u * |dimensionPlaneKernel d u| :=
  regulatedVerticalReduction_error _ B (integrableOn_dimensionPlaneKernel d hd)
    (integral_dimensionPlaneKernel d hd) (integrableOn_dimensionPlaneKernel_first_abs_moment d hd)
    hB C L hbound hLip hκ (Real.rpow_pos_of_pos hρ _)

end BoundaryDraft
