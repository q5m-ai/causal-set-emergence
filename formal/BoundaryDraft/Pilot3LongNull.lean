import BoundaryDraft.Pilot3LongFibre
import BoundaryDraft.TwoFaceLongNull
import BoundaryDraft.DimensionCancellation

/-!
# Unconditional signed long cancellation for every smooth 3D pilot

The actual geometric fibres are averaged on a proved compact active source
set. Pointwise quadratic little-o is combined with the checked UNIFORM bound,
not promoted to a uniform little-o. Three probes establish coefficient
integrability without root selection. The resulting linear jet has a uniform
quadratic error, sufficient for the unchanged dimension-three cancellation.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
namespace SmoothPilot3

set_option maxHeartbeats 1000000

variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

/-- The averaged actual density has a quadratic Peano jet. This is stronger
than needed in 3D, and follows DOMINATED averaging, not uniform fibre little-o. -/
theorem longDensity_right_quadratic_jet {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 b2 : ℝ, (fun σ => pilot3LongDensity h f δ σ - (b0 + b1 * σ + b2 * σ ^ 2))
      =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, hesq, hc, hA, hM, hB, hall⟩ :=
    Pilot3LongGeometry.exists_hypotheses hf hδ
  let F := fun (p : Pilot3LongFibre.Parameter) σ => MonotoneHinge.fibre
    (pilot3RayGap h f p.2 p.1.val) pilot3NullJacobian δ V σ
  let C0 := fun p : Pilot3LongFibre.Parameter => MonotoneHinge.F0
    (pilot3RayGap h f p.2 p.1.val) pilot3NullJacobian δ V
  let C1 := fun p : Pilot3LongFibre.Parameter => MonotoneHinge.F1
    (pilot3RayGap h f p.2 p.1.val) pilot3NullJacobian δ V
  let C2 := fun p : Pilot3LongFibre.Parameter => MonotoneHinge.F2
    (pilot3RayGap h f p.2 p.1.val) pilot3NullJacobian δ V
  let D := MonotoneHinge.remainderBound δ V c A M B
  have hD0 : 0 ≤ D := by
    dsimp [D, MonotoneHinge.remainderBound]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (sub_nonneg.mpr hV.le))
      (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hM (sq_nonneg A)) hc.le))
  have hj (p : Pilot3LongFibre.Parameter) :
      (fun σ => F p σ - (C0 p + C1 p * σ + C2 p * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) :=
    (hall p.2 p.1).right_quadratic_jet
  have hb (p : Pilot3LongFibre.Parameter) (σ : ℝ) (hσ : σ ∈ Ioc 0 ε) :
      |F p σ - (C0 p + C1 p * σ + C2 p * σ ^ 2)| / σ ^ 2 ≤ D :=
    (hall p.2 p.1).normalized_remainder_bound hσ
  have hFi (σ : ℝ) (hσ : σ ∈ Ioc 0 ε) : Measurable (fun p => F p σ) ∧
      Integrable (fun p => F p σ) (pilot3CircleMeasure.prod volume) :=
    Pilot3LongFibre.measurable_integrable_fibre hf hδ hV.le hσ.1.le (hσ.2.trans_lt hesq)
  have hm := AveragedQuadraticJet.measurable_coefficients_of_right_jet
    F C0 C1 C2 hε (fun σ hσ => (hFi σ hσ).1) hj
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  have hmargin : 0 < (1 - κ - η) * δ / 2 := by
    have hpos : 0 < 1 - κ - η := by linarith [C.budget]
    positivity
  let S := pilot3HeightTube h ((1 - κ - η) * δ / 2)
  have hS : IsCompact S := hf.isCompact_heightTube _
  let P : Set Pilot3LongFibre.Parameter := univ ×ˢ S
  have hPm : MeasurableSet P := MeasurableSet.univ.prod hS.measurableSet
  have hPf : (pilot3CircleMeasure.prod volume) P < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_lt_top _ _) hS.measure_lt_top
  let μ := (pilot3CircleMeasure.prod volume).restrict P
  haveI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hPf⟩
  have hinactive (p : Pilot3LongFibre.Parameter) (hp : p ∉ P) : pilot3RayGap h f p.2 p.1.val 0 δ ≤ 0 := by
    apply le_of_not_gt
    intro hg
    have hx := (C.old_endpoint_margin hδ le_rfl p.2 p.1.val
      (mem_sphere_zero_iff_norm.mp p.1.property) hg.le).1
    exact hp ⟨mem_univ _, pilot3_mem_heightTube hmargin hx⟩
  have hFzero (σ : ℝ) (hσ : σ ∈ Ioc 0 ε) (p : Pilot3LongFibre.Parameter) (hp : p ∉ P) : F p σ = 0 :=
    (hall p.2 p.1).fibre_zero (hinactive p hp) (Ioc_subset_Icc_self hσ)
  have hDi : Integrable (fun _p : Pilot3LongFibre.Parameter => D) μ := integrable_const D
  obtain ⟨hC0, hC1, hC2⟩ := TwoFaceLongNull.integrable_coefficients_of_three_probes
    F C0 C1 C2 (fun _ => D) hε (fun σ hσ => (hFi σ hσ).2.integrableOn) hm hDi hb
  have havg := AveragedQuadraticJet.averaged_right_quadratic_jet F C0 C1 C2
    (fun _ => D) hε hj hb (fun _ => hD0) hDi (fun σ hσ => (hFi σ hσ).1)
    hm.1 hm.2.1 hm.2.2 hC0 hC1 hC2
  refine ⟨∫ p, C0 p ∂μ, ∫ p, C1 p ∂μ, ∫ p, C2 p ∂μ, ?_⟩
  apply havg.congr' _ EventuallyEq.rfl
  filter_upwards [MonotoneHinge.eventually_right hε] with σ hσ
  rw [Pilot3LongFibre.density_eq_parameterFibre hf hδ hV hσ.1.le (hσ.2.trans_lt hesq)
    (fun x ω => (hall x ω).clearance.le)]
  have he : (∫ p, F p σ ∂μ) = ∫ p, F p σ ∂(pilot3CircleMeasure.prod volume) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hFzero σ hσ)
  rw [he]

/-- Uniform quadratic error for the averaged LINEAR jet, at every fixed
positive cutoff. No assertion of uniform quadratic fibre little-o is made. -/
theorem longDensity_linear_quadratic_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ σ ∈ Ioc 0 ε,
      |pilot3LongDensity h f δ σ - (b0 + b1 * σ)| ≤ C * σ ^ 2 := by
  obtain ⟨b0, b1, b2, hj⟩ := hf.longDensity_right_quadratic_jet hδ
  have hb : (fun σ => pilot3LongDensity h f δ σ - (b0 + b1 * σ)) =O[𝓝[>] 0] (fun σ => σ ^ 2) := by
    apply (hj.isBigO.add (isBigO_const_mul_self b2 (fun σ : ℝ => σ ^ 2) (𝓝[>] 0))).congr_left
    intro σ
    ring
  obtain ⟨C, hC, hb⟩ := hb.exists_pos
  obtain ⟨ε, hε, he⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hb.bound
  refine ⟨b0, b1, C, ε, hC, hε, fun σ hσ => ?_⟩
  simpa only [mem_setOf_eq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg σ)] using he hσ

omit hf in
private theorem sq_littleO_threeHalves :
    (fun σ : ℝ => σ ^ 2) =o[𝓝[>] 0] (fun σ : ℝ => σ ^ (3 / 2 : ℝ)) := by
  have ht : Tendsto (fun σ : ℝ => σ ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 2 : ℝ))).continuousAt
      (x := (0 : ℝ))
    simpa using hc.tendsto.mono_left inf_le_left
  apply (isLittleO_iff_tendsto' ?_).mpr
  · apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [← Real.rpow_natCast σ 2, ← Real.rpow_sub hσ]
    norm_num
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact fun hz => False.elim ((Real.rpow_pos_of_pos hσ (3 / 2 : ℝ)).ne' hz)

/-- Precisely the real-order remainder required by the unchanged analytic
cancellation theorem in odd physical dimension three. -/
theorem longDensity_right_linear_jet {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 : ℝ, (fun σ => pilot3LongDensity h f δ σ - (b0 + b1 * σ))
      =o[𝓝[>] 0] (fun σ => σ ^ (3 / 2 : ℝ)) := by
  obtain ⟨b0, b1, C, ε, _, hε, hb⟩ := hf.longDensity_linear_quadratic_bound hδ
  refine ⟨b0, b1, ?_⟩
  have hO : (fun σ => pilot3LongDensity h f δ σ - (b0 + b1 * σ)) =O[𝓝[>] 0] (fun σ => σ ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [MonotoneHinge.eventually_right hε] with σ hσ
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg σ)] using hb σ hσ
  exact hO.trans_isLittleO sq_littleO_threeHalves

/-- The complete signed kernel integral vanishes at its physical normalization,
only after deriving actual measurability, boundedness and the real-order jet. -/
theorem tendsto_longDensity {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, pilot3LongDensity h f δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  obtain ⟨b0, b1, hj⟩ := hf.longDensity_right_linear_jet hδ
  obtain ⟨C, _, hb⟩ := hf.bounded_longDensity hδ
  let b : ℕ → ℝ := fun j => if j = 0 then b0 else b1
  have he (σ : ℝ) : dimensionJet 3 b σ = b0 + b1 * σ := by
    simp [dimensionJet, dimensionFactorCount, Finset.sum_range_succ, b]
  have hjet : (fun σ => pilot3LongDensity h f δ σ - dimensionJet 3 b σ) =o[𝓝[>] 0]
      (fun σ => σ ^ ((3 : ℝ) / 2)) := by simpa only [he] using hj
  exact dimensionKernel_transverse_cancellation 3 (by norm_num) _ (hf.measurable_longDensity δ) C
    (fun σ _ => by simpa only [Real.norm_eq_abs] using hb σ) b hjet _
    (dimensionIntervalCoefficient_pos 3 (by norm_num))

/-- Unconditional actual normalized signed long limit for EVERY fixed positive
cutoff. The sibling short producer can choose its cutoff independently. -/
theorem tendsto_longAction {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => pilot3LongAction ρ δ h f) atTop (𝓝 0) := by
  have hl := (hf.tendsto_longDensity hδ).const_mul (-(dimensionPairCoefficient 3))
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  rw [hf.longAction_eq_density hδ ρ]
  have he : (∫ σ : ℝ, dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
      pilot3LongDensity h f δ σ) = ∫ σ : ℝ in Ioi 0,
      pilot3LongDensity h f δ σ * dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) := by
    rw [← integral_Ici_eq_integral_Ioi]
    have hz : ∀ σ, σ ∉ Ici (0 : ℝ) →
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) * pilot3LongDensity h f δ σ = 0 := by
      intro σ hσ
      simp [pilot3LongDensity, longDensityENN_negative δ (lt_of_not_ge hσ)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    congr 1
    ext σ
    ring
  rw [he, Real.rpow_add hρ, Real.rpow_one]
  ring

end SmoothPilot3
end BoundaryDraft
