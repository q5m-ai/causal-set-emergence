import BoundaryDraft.DimensionCancellation

/-! Independently expanded cancellation contracts. The right-hand jet remains
an analytic hypothesis, never a geometric admissibility field. -/

open MeasureTheory Set Filter Asymptotics BoundaryDraft
open scoped Topology

-- Independently expanded all-dimensional contract, without a quotient-bound premise.
example (d : ℕ) (hd : 2 ≤ d) (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b : ℕ → ℝ)
    (hjet : (fun s => B s - ∑ j ∈ Finset.range (d / 2 + 1), b j * s ^ j)
      =o[𝓝[>] 0] (fun s => s ^ ((d : ℝ) / 2))) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / (d : ℝ)) *
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel d (c * ρ * s ^ ((d : ℝ) / 2)))
      atTop (𝓝 0) := by
  exact dimensionKernel_transverse_cancellation d hd B hB C hbound b hjet c hc

-- The odd-dimensional jet really uses the fractional critical power.
example (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b₀ b₁ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s)) =o[𝓝[>] 0]
      (fun s => s ^ (3 / 2 : ℝ))) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (5 / 3 : ℝ) *
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel 3 (c * ρ * s ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have h := dimensionKernel_transverse_cancellation 3 (by norm_num) B hB C hbound
    (fun j => if j = 0 then b₀ else b₁) (by
      simpa [dimensionJet, dimensionFactorCount, Finset.sum_range_succ] using hjet) c hc
  norm_num at h ⊢
  exact h

example (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b₀ b₁ b₂ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ (5 / 2 : ℝ))) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (7 / 5 : ℝ) *
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel 5 (c * ρ * s ^ (5 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have h := dimensionKernel_transverse_cancellation 5 (by norm_num) B hB C hbound
    (fun j => if j = 0 then b₀ else if j = 1 then b₁ else b₂) (by
      simpa [dimensionJet, dimensionFactorCount, Finset.sum_range_succ] using hjet) c hc
  norm_num at h ⊢
  exact h

-- Recover the original four-dimensional powers and independently defined BDG kernel.
example (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b₀ b₁ b₂ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2)) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)) atTop (𝓝 0) := by
  have h := dimensionKernel_transverse_cancellation 4 (by norm_num) B hB C hbound
    (fun j => if j = 0 then b₀ else if j = 1 then b₁ else b₂) (by
      norm_num [dimensionJet, dimensionFactorCount, Finset.sum_range_succ]
      exact hjet) c hc
  norm_num [dimensionKernel_four, Real.rpow_natCast] at h ⊢
  exact h

-- Dimension two is included without any special endpoint convention.
example (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b₀ b₁ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s)) =o[𝓝[>] 0] (fun s => s))
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ 2 *
      ∫ s : ℝ in Ioi 0, B s * dimensionKernel 2 (c * ρ * s)) atTop (𝓝 0) := by
  have h := dimensionKernel_transverse_cancellation 2 (by norm_num) B hB C hbound
    (fun j => if j = 0 then b₀ else b₁) (by
      simpa [dimensionJet, dimensionFactorCount, Finset.sum_range_succ] using hjet) c hc
  norm_num [Real.rpow_natCast] at h ⊢
  exact h
