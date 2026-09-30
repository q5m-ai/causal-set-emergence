import BoundaryDraft.DimensionNormalizedKernel
import BoundaryDraft.DimensionReducedTail
import BoundaryDraft.DimensionRodrigues

/-! Actual integral normalization, parity, divergence, and endpoint regressions.
No slice moments, mass identities, or tail estimates are assumed here. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology

-- Expand the independently defined finite reduction and actual sigma slice.
example (d : ℕ) (hd : 2 ≤ d) :
    (∫ H : ℝ in Ioi 0,
      dimensionPointCoefficient d * H - dimensionPairCoefficient d *
        ∫ t : ℝ in Ioc 0 H, (H - t) *
          (Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2) *
            ∫ σ : ℝ in Ioc 0 (t ^ 2),
              (t ^ 2 - σ) ^ (((d : ℝ) - 3) / 2) *
                dimensionKernel d (dimensionIntervalCoefficient d * σ ^ ((d : ℝ) / 2)))) = 1 :=
  integral_dimensionPlaneKernel d hd

example (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (dimensionPlaneKernel d) (Ioi 0) ∧
      IntegrableOn (fun H : ℝ => H * |dimensionPlaneKernel d H|) (Ioi 0) :=
  ⟨integrableOn_dimensionPlaneKernel d hd, integrableOn_dimensionPlaneKernel_first_abs_moment d hd⟩

example : (∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel 2 H) = 0 := by
  simpa using integral_dimensionPlaneKernel_even_first 0

example : (∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel 4 H) = 0 := by
  simpa using integral_dimensionPlaneKernel_even_first 1

example : 0 < ∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel 3 H := by
  simpa using integral_dimensionPlaneKernel_odd_first_pos 0

example : 0 < ∫ H : ℝ in Ioi 0, H * dimensionPlaneKernel 5 H := by
  simpa using integral_dimensionPlaneKernel_odd_first_pos 1

-- Even second moments cannot be interpreted using a totalized integral value.
example (n : ℕ) :
    ¬ IntegrableOn (fun H : ℝ => H ^ 2 * |dimensionPlaneKernel (2 * n + 2) H|) (Ioi 0) :=
  not_integrableOn_dimensionPlaneKernel_even_abs_second n

example (n : ℕ) :
    Tendsto (fun R : ℝ => ∫ H : ℝ in Ioc 0 R, H ^ 2 * dimensionPlaneKernel (2 * n + 2) H)
      atTop atBot :=
  tendsto_dimensionPlaneKernel_even_second_atBot n

example (n k : ℕ) :
    IntegrableOn (fun H : ℝ => H ^ k * |dimensionPlaneKernel (2 * n + 3) H|) (Ioi 0) :=
  integrableOn_dimensionPlaneKernel_odd_abs_moment n k

example (n : ℕ) :
    0 < dimensionPlaneEvenTailCoefficient n ∧
      ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H →
        |dimensionPlaneKernel (2 * n + 2) H + dimensionPlaneEvenTailCoefficient n / H ^ 3| ≤
          C / H ^ 5 :=
  ⟨dimensionPlaneEvenTailCoefficient_pos n, dimensionPlaneKernel_even_leading_remainder n⟩

-- The endpoint singularity in dimension two is genuinely integrable.
example (c t : ℝ) :
    IntegrableOn (fun σ : ℝ => (t ^ 2 - σ) ^ (-(1 / 2) : ℝ) * dimensionKernel 2 (c * σ))
      (Ioc 0 (t ^ 2)) := by
  have h := integrableOn_dimensionSigmaSlice_integrand 2 (by norm_num) c t
  norm_num at h
  exact h

-- Fractional odd-dimensional powers are differentiated only on the positive domain.
example (c σ : ℝ) (hσ : 0 < σ) :
    iteratedDeriv 2 (fun s : ℝ => s ^ 2 * Real.exp (-(c * s ^ (3 / 2 : ℝ)))) σ =
      2 * dimensionKernel 3 (c * σ ^ (3 / 2 : ℝ)) := by
  simpa [dimensionFactorCount, Nat.factorial] using dimensionKernel_rodrigues 3 c hσ

example (c : ℝ) :
    Tendsto (iteratedDeriv 1 (fun s : ℝ => s ^ 2 * Real.exp (-(c * s ^ (3 / 2 : ℝ)))))
      (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_iteratedDeriv_pow_exp_zero 3 2 1 (by norm_num) (by norm_num) c

-- No positivity of the kernel or second-moment assumption in this rate.
example (d : ℕ) (hd : 2 ≤ d) (B : ℝ → ℝ) (hB : Measurable B) (C L : ℝ)
    (hb : ∀ r, 0 ≤ r → ‖B r‖ ≤ C) (hL : ∀ r, 0 ≤ r → ‖B r - B 0‖ ≤ L * r)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    ‖regulatedVerticalReduction (dimensionPlaneKernel d) B κ (ρ ^ (1 / (d : ℝ))) - κ⁻¹ * B 0‖ ≤
      (L * (ρ ^ (1 / (d : ℝ)))⁻¹ / κ ^ 2) *
        ∫ u : ℝ in Ioi 0, u * |dimensionPlaneKernel d u| :=
  dimensionPlaneKernel_regulated_error d hd B hB C L hb hL hκ hρ
