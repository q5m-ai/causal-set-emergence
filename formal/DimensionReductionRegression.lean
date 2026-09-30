import BoundaryDraft.DimensionReduction

/-! Signed Fubini/normalization regressions on an independent elementary slice.
This toy slice is not asserted to be a physical one-dimensional action. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

private def testSlice (t : ℝ) : ℝ := 2 * dimensionKernel 1 t

example (t : ℝ) : testSlice t = (2 - t) * Real.exp (-t) := by
  norm_num [testSlice, dimensionKernel, dimensionPolynomial, dimensionFactorCount,
    dimensionPolynomialStage, Polynomial.derivative_mul]
  ring

private theorem testSlice_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * testSlice t) (Ioi 0) := by
  have hi := (integrableOn_dimensionKernel_mellin 1
    (by positivity : 0 < (n : ℝ) + 1)).const_mul 2
  simp only [add_sub_cancel_right, Real.rpow_natCast] at hi
  apply hi.congr
  exact Eventually.of_forall fun t => by unfold testSlice; ring

private theorem testSlice_moment (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ n * testSlice t) = (1 - (n : ℝ)) * (n.factorial : ℝ) := by
  have hi := integral_dimensionKernel_mellin 1
    (by positivity : 0 < (n : ℝ) + 1)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial,
    dimensionMellinFactor, dimensionFactorCount] at hi
  norm_num [Finset.prod_range_succ] at hi
  calc
    _ = 2 * ∫ t : ℝ in Ioi 0, t ^ n * dimensionKernel 1 t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only [testSlice]
      ring
    _ = _ := by rw [hi]; ring

private theorem testSlice_mass :
    IntegrableOn (verticalActionReduction 1 1 testSlice) (Ioi 0) ∧
      (∫ H : ℝ in Ioi 0, verticalActionReduction 1 1 testSlice H) = 1 := by
  apply integral_verticalActionReduction 1 1 testSlice
    (by unfold testSlice; exact measurable_const.mul (continuous_dimensionKernel 1).measurable)
  · simpa using testSlice_integrable 0
  · simpa using testSlice_integrable 1
  · exact testSlice_integrable 2
  · simpa using testSlice_moment 0
  · simpa using testSlice_moment 1
  · have h := testSlice_moment 2
    norm_num at h ⊢
    linarith

-- The original finite reduction acquires unit mass from verified slice moments.
example : (∫ H : ℝ in Ioi 0, verticalActionReduction 1 1 testSlice H) = 1 :=
  testSlice_mass.2

-- The tail lemma retains the signed first moment; it does not impose zero.
example : (∫ H : ℝ in Ioi 0, H * verticalTailReduction 1 testSlice H) = 2 := by
  have h := integral_verticalTailReduction_moment 1 1 testSlice
    (by unfold testSlice; exact measurable_const.mul (continuous_dimensionKernel 1).measurable)
    (testSlice_integrable 3)
  norm_num [testSlice_moment, Nat.factorial] at h
  exact h

-- Source weights may have either sign. No positivity premise is introduced.
example (χ : ℝ → ℝ) (hχ : Continuous χ) (C W : ℝ)
    (hb : ∀ s, ‖χ s‖ ≤ C) (hχ₀ : χ 0 = 1) :
    Tendsto (fun ρ : ℝ => W *
      regulatedVerticalReduction (verticalActionReduction 1 1 testSlice) χ (1 / 2)
        (ρ ^ (1 / 5 : ℝ))) atTop (𝓝 (2 * W)) := by
  convert regulatedVerticalReduction_weighted_density_limit 5 (by norm_num)
    (verticalActionReduction 1 1 testSlice) χ testSlice_mass.1 testSlice_mass.2 hχ C W hb hχ₀
      (by norm_num : (0 : ℝ) < 1 / 2) using 1
  norm_num
  ring

example (G χ : ℝ → ℝ) (κ k a : ℝ) (hc : ∀ s, a < s → χ s = 0) :
    regulatedVerticalReduction G χ κ k =
      ∫ s : ℝ in Ioc 0 a, χ s * (k * G (k * (κ * s))) :=
  regulatedVerticalReduction_cutoff G χ κ k a hc
