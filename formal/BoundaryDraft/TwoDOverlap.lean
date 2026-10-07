import BoundaryDraft.TwoDGeometry

/-!
# Actual 2D translated overlap and its complete causal time fibre

This is a finite-density geometric input, not a signed disintegration or an
asymptotic theorem. In particular no componentwise additivity is assumed.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- The actual overlap of the WHOLE spacetime region with its translate. -/
def twoDOverlap (h f : TwoDSpace → ℝ) (t : ℝ) (r : TwoDSpace) : ℝ :=
  (volume (twoDRegion h f ∩
    (fun p : TwoDSpacetime => (p.1 + t, p.2 + r)) ⁻¹' twoDRegion h f)).toReal

/-- Both time intervals and every endpoint partner are present on the left.
The combined causal budget, not an assumed additivity rule, gives the right. -/
theorem SmoothTwoD.causal_time_fibre {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    (x r : TwoDSpace) (t : ℝ) (ht : ‖r‖ ≤ t) :
    {s : ℝ | (s, x) ∈ twoDRegion h f ∧ (s + t, x + r) ∈ twoDRegion h f} =
      Ioo (f x - max 0 (h x)) (f (x + r) - t) := by
  obtain ⟨κ, η, hκ, hη, hb, hl, hu⟩ := hf.slope_budget
  have hn : ‖(x + r) - x‖ = ‖r‖ := by simp
  have hu' : f (x + r) - f x ≤ η * ‖r‖ := by
    have he := (abs_le.mp (hu (x + r) x)).2
    rw [norm_sub_rev, hn] at he
    exact he
  have hl' : (f (x + r) - max 0 (h (x + r))) - (f x - max 0 (h x)) ≤
      (κ + η) * ‖r‖ := by
    have hh := (abs_le.mp (hl (x + r) x)).1
    rw [norm_sub_rev, hn] at hh
    nlinarith
  have htu : f (x + r) - t ≤ f x := by
    have := mul_le_mul_of_nonneg_left ht hη
    have := mul_le_of_le_one_left ((norm_nonneg _).trans ht) (show η ≤ 1 by linarith)
    linarith
  have htl : f (x + r) - max 0 (h (x + r)) ≤ f x - max 0 (h x) + t := by
    have := mul_le_mul_of_nonneg_left ht (add_nonneg hκ hη)
    have := mul_le_of_le_one_left ((norm_nonneg _).trans ht) hb.le
    linarith
  rw [twoDRegion_eq_envelopes]
  ext s
  simp only [mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨hs, _⟩, ⟨_, hy⟩⟩
    exact ⟨hs, by linarith⟩
  · rintro ⟨hs, hy⟩
    exact ⟨⟨hs, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Direct dimension-TWO polynomial, not a 3D/4D moment extrapolation. -/
theorem twoDKernel_eq (z : ℝ) :
    dimensionKernel 2 z = (1 - 2 * z + z ^ 2 / 2) * Real.exp (-z) := by
  unfold dimensionKernel
  congr 1
  norm_num [dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    Polynomial.derivative_mul]
  ring

end BoundaryDraft
