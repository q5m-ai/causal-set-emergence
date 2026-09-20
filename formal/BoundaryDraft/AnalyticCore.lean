import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A checked analytic component, not the full boundary conjecture

The signed-kernel limit below is the dominated-convergence step after an exact
geometric reduction. Integrability, normalization of the specific BDG kernel,
and the reduction from the four-dimensional action are NOT proved here.

No positivity assumption on the kernel is made.
-/

open MeasureTheory Filter
open scoped Topology

namespace BoundaryDraft

/-- A bounded continuous profile can be passed through an integrable signed
kernel under rescaling. The measure can in particular be volume restricted
to the positive half-line. -/
theorem signed_rescaling_limit
    (μ : Measure ℝ) (G B : ℝ → ℝ)
    (hG : Integrable G μ) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ x, ‖B x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ u, G u * B (ε * u) ∂μ)
      (𝓝 0) (𝓝 ((∫ u, G u ∂μ) * B 0)) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ u, G u * B (ε * u) ∂μ)
      (𝓝 0) (𝓝 (∫ u, G u * B 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u => ‖G u‖ * C)
    · exact Filter.Eventually.of_forall fun ε =>
        hG.aestronglyMeasurable.mul
          (hB.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro ε
      apply Filter.Eventually.of_forall
      intro u
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound (ε * u)) (norm_nonneg (G u))
    · exact hG.norm.mul_const C
    · apply Filter.Eventually.of_forall
      intro u
      have harg : Tendsto (fun ε : ℝ => ε * u) (𝓝 0) (𝓝 0) := by
        simpa only [id_eq, zero_mul] using
          ((continuous_id : Continuous (fun ε : ℝ => ε)).mul
            (continuous_const : Continuous (fun _ : ℝ => u))).tendsto (0 : ℝ)
      exact tendsto_const_nhds.mul ((hB.tendsto 0).comp harg)
  simpa only [integral_mul_const] using hlim

/-- Unit mass specializes the limit to the profile's boundary value. The mass
identity is an explicit hypothesis, not an assumed theorem about the BDG kernel. -/
theorem signed_rescaling_limit_unit_mass
    (μ : Measure ℝ) (G B : ℝ → ℝ)
    (hG : Integrable G μ) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ x, ‖B x‖ ≤ C)
    (hmass : ∫ u, G u ∂μ = 1) :
    Tendsto (fun ε : ℝ => ∫ u, G u * B (ε * u) ∂μ)
      (𝓝 0) (𝓝 (B 0)) := by
  simpa only [hmass, one_mul] using
    signed_rescaling_limit μ G B hG hB C hbound

end BoundaryDraft
