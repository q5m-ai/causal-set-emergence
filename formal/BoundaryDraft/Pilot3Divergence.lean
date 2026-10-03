import BoundaryDraft.Pilot3Ramp

/-!
# Spatial divergence on the whole smooth pilot region

The proof uses compactly supported whole-space integration by parts followed
by the proved canonical collar coarea. The field need only be C1 near the
closed positive region; no behavior outside it, connectedness, or absence of
positive-height critical points is imposed. The outward sign is explicit.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

def pilot3Divergence (V : Pilot3Space → Pilot3Space) (x : Pilot3Space) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ V x (EuclideanSpace.basisFun (Fin 2) ℝ i) i

def pilot3Laplacian (f : Pilot3Space → ℝ) : Pilot3Space → ℝ := pilot3Divergence (pilot3Gradient f)

theorem contDiffAt_pilot3Gradient {f : Pilot3Space → ℝ} {x : Pilot3Space} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (pilot3Gradient f) x :=
  (InnerProductSpace.toDual ℝ Pilot3Space).symm.contDiff.contDiffAt.comp x (hf.fderiv_right (by simp))

theorem continuousAt_pilot3Divergence {V : Pilot3Space → Pilot3Space} {x : Pilot3Space}
    (hV : ContDiffAt ℝ 1 V x) : ContinuousAt (pilot3Divergence V) x := by
  apply tendsto_finset_sum
  intro i _
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).continuous.continuousAt.comp
    ((ContinuousLinearMap.apply ℝ Pilot3Space (EuclideanSpace.basisFun (Fin 2) ℝ i)).continuous.continuousAt.comp
      (hV.fderiv_right (m := 0) (by norm_num)).continuousAt)

theorem integral_pilot3Divergence_eq_zero {V : Pilot3Space → Pilot3Space}
    (hV : ContDiff ℝ 1 V) (hS : HasCompactSupport V) : (∫ x, pilot3Divergence V x) = 0 := by
  have hi (v : Pilot3Space) : Integrable (fun x => fderiv ℝ V x v) :=
    ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport (hS.fderiv_apply ℝ v)
  have hz (v : Pilot3Space) : (∫ x, fderiv ℝ V x v) = 0 := by
    have he := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := volume) (f := fun _ : Pilot3Space => (1 : ℝ)) (g := V) (v := v)
      (by simp) (by simpa using hi v) (by simpa using hV.continuous.integrable_of_hasCompactSupport hS)
      (differentiable_const 1) (hV.differentiable (by norm_num))
    simpa using he
  have hic (i : Fin 2) : Integrable (fun x => fderiv ℝ V x (EuclideanSpace.basisFun (Fin 2) ℝ i) i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).integrable_comp (hi _)
  unfold pilot3Divergence
  rw [integral_finset_sum _ (fun i _ => hic i)]
  apply Finset.sum_eq_zero
  intro i _
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).integral_comp_comm (hi (EuclideanSpace.basisFun (Fin 2) ℝ i))
  simpa only [hz, map_zero] using he

def pilot3RampField (h : Pilot3Space → ℝ) (V : Pilot3Space → Pilot3Space) (ε : ℝ) (x : Pilot3Space) : Pilot3Space :=
  pilot3HeightRamp (h x / ε) • V x

namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} {V : Pilot3Space → Pilot3Space} (hh : Pilot3RegularHeight h)
  (hV : ∀ x ∈ pilot3ClosedPositive h, ContDiffAt ℝ 1 V x)
include hh hV

theorem integrableOn_divergence : IntegrableOn (pilot3Divergence V) {x | 0 < h x} :=
  ((show ContinuousOn (pilot3Divergence V) (pilot3ClosedPositive h) from
    fun x hx => (continuousAt_pilot3Divergence (hV x hx)).continuousWithinAt).integrableOn_compact
      hh.isCompact_closedPositive).mono_set subset_closure

theorem continuousOn_flux : ContinuousOn (fun x => inner (𝕜 := ℝ) (V x) (pilot3Gradient h x)) (pilot3ClosedPositive h) :=
  (show ContinuousOn V (pilot3ClosedPositive h) from fun x hx => (hV x hx).continuousAt.continuousWithinAt).inner hh.continuousOn_gradient

theorem integrable_surface_flux : Integrable (fun x => inner (𝕜 := ℝ) (V x) (pilot3Gradient h x) /
    ‖pilot3Gradient h x‖) (pilot3SurfaceMeasure h) := by
  obtain ⟨A⟩ := hh.exists_collarAtlas
  exact A.integrable_level_weight_div hh _ (hh.continuousOn_flux hV) 0 ⟨le_rfl, A.width_pos.le⟩

omit hh hV in
private theorem rampField_zero (ε : ℝ) (hε : 0 < ε) (x : Pilot3Space) (hx : x ∉ pilot3ClosedPositive h) :
    pilot3RampField h V ε x = 0 := by
  have hn : h x ≤ 0 := le_of_not_gt (fun hp => hx (subset_closure hp))
  rw [pilot3RampField, pilot3HeightRamp_zero ((div_nonpos_of_nonpos_of_nonneg hn hε.le).trans (by norm_num)), zero_smul]

private theorem contDiff_rampField (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ 1 (pilot3RampField h V ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ pilot3ClosedPositive h
  · exact ((contDiff_pilot3HeightRamp.contDiffAt.comp x ((hh.smoothAt x hx).div_const ε)).of_le (by simp)).smul (hV x hx)
  · have he : pilot3RampField h V ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact rampField_zero ε hε y hy
    exact contDiffAt_const.congr_of_eventuallyEq he

omit hV in
private theorem hasCompactSupport_rampField (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (pilot3RampField h V ε) := by
  apply hh.isCompact_closedPositive.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (rampField_zero ε hε x hn)

private theorem divergence_rampField (ε : ℝ) (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    pilot3Divergence (pilot3RampField h V ε) x =
      pilot3HeightRamp (h x / ε) * pilot3Divergence V x + (deriv pilot3HeightRamp (h x / ε) / ε) *
        inner (𝕜 := ℝ) (V x) (pilot3Gradient h x) := by
  have hg := (hh.smoothAt x hx).differentiableAt (by simp)
  have hv := (hV x hx).differentiableAt (by norm_num)
  have hr := (contDiff_pilot3HeightRamp.differentiable (by simp) (h x / ε)).hasDerivAt
  have hdiv : HasFDerivAt (fun y => h y / ε) (ε⁻¹ • fderiv ℝ h x) x := by
    simpa only [div_eq_mul_inv] using hg.hasFDerivAt.mul_const ε⁻¹
  have hd := (hr.comp_hasFDerivAt x hdiv).smul hv.hasFDerivAt
  change HasFDerivAt (pilot3RampField h V ε) _ x at hd
  have hb (i : Fin 2) : fderiv ℝ h x (EuclideanSpace.basisFun (Fin 2) ℝ i) = pilot3Gradient h x i := by
    rw [pilot3_differential_eq_inner]
    simp [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.basisFun_apply]
  simp only [pilot3Divergence, hd.fderiv, Function.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [hb, PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

private theorem integral_divergence_ramp_closedPositive (ε : ℝ) (hε : 0 < ε) :
    (∫ x in pilot3ClosedPositive h, pilot3Divergence (pilot3RampField h V ε) x) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_pilot3Divergence_eq_zero (hh.contDiff_rampField hV ε hε) (hh.hasCompactSupport_rampField ε hε)
  · intro x hx
    have he : pilot3RampField h V ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact rampField_zero ε hε y hy
    simp only [pilot3Divergence, he.fderiv_eq, fderiv_const, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, PiLp.zero_apply, Finset.sum_const_zero]

private theorem continuousOn_ramp_divergence (ε : ℝ) :
    ContinuousOn (fun x => pilot3HeightRamp (h x / ε) * pilot3Divergence V x) (pilot3ClosedPositive h) :=
  (contDiff_pilot3HeightRamp.continuous.comp_continuousOn (hh.continuousOn_closedPositive.div_const ε)).mul
    (fun x hx => (continuousAt_pilot3Divergence (hV x hx)).continuousWithinAt)

private theorem continuousOn_ramp_flux (ε : ℝ) : ContinuousOn (fun x =>
    (deriv pilot3HeightRamp (h x / ε) / ε) * inner (𝕜 := ℝ) (V x) (pilot3Gradient h x)) (pilot3ClosedPositive h) :=
  ((continuous_deriv_pilot3HeightRamp.comp_continuousOn (hh.continuousOn_closedPositive.div_const ε)).div_const ε).mul
    (hh.continuousOn_flux hV)

private theorem integral_ramp_flux_eq_height (A : Pilot3CollarAtlas h) (ε : ℝ) (hε : 0 < ε) (hεA : ε < A.width) :
    (∫ x in pilot3ClosedPositive h, (deriv pilot3HeightRamp (h x / ε) / ε) * inner (𝕜 := ℝ) (V x) (pilot3Gradient h x)) =
      ∫ t in Icc 0 A.width, (deriv pilot3HeightRamp (t / ε) / ε) *
        pilot3WeightedHeightDensity h (fun x => inner (𝕜 := ℝ) (V x) (pilot3Gradient h x)) t := by
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hh.isCompact_closedPositive.isClosed.measurableSet
    (show pilot3ClosedCollar h A.width ⊆ pilot3ClosedPositive h from inter_subset_left)]
  · exact A.integral_closedCollar_weighted hh _ (hh.continuousOn_flux hV)
      _ ((continuous_deriv_pilot3HeightRamp.comp (continuous_id.div_const ε)).div_const ε).continuousOn
  · intro x hx
    have hxt : A.width < h x := lt_of_not_ge (fun hle => hx.2 ⟨hx.1, hle⟩)
    rw [deriv_pilot3HeightRamp_zero_of_gt ((one_lt_div hε).mpr (hεA.trans hxt)), zero_div, zero_mul]

/-- Exact finite-cutoff balance; all split integrands are absolutely integrable. -/
theorem ramp_balance (A : Pilot3CollarAtlas h) (ε : ℝ) (hε : 0 < ε) (hεA : ε < A.width) :
    (∫ x in {x | 0 < h x}, pilot3HeightRamp (h x / ε) * pilot3Divergence V x) =
      -(∫ t in Icc 0 A.width, (deriv pilot3HeightRamp (t / ε) / ε) *
        pilot3WeightedHeightDensity h (fun x => inner (𝕜 := ℝ) (V x) (pilot3Gradient h x)) t) := by
  rw [setIntegral_congr_set hh.ae_positive_eq_closedPositive]
  have he := hh.integral_divergence_ramp_closedPositive hV ε hε
  rw [setIntegral_congr_fun hh.isCompact_closedPositive.isClosed.measurableSet
    (fun x hx => hh.divergence_rampField hV ε x hx), integral_add
      ((hh.continuousOn_ramp_divergence hV ε).integrableOn_compact hh.isCompact_closedPositive)
      ((hh.continuousOn_ramp_flux hV ε).integrableOn_compact hh.isCompact_closedPositive),
    hh.integral_ramp_flux_eq_height hV A ε hε hεA] at he
  linarith

private theorem tendsto_integral_ramp_divergence :
    Tendsto (fun ε : ℝ => ∫ x in {x | 0 < h x}, pilot3HeightRamp (h x / ε) * pilot3Divergence V x)
      (𝓝[>] 0) (𝓝 (∫ x in {x | 0 < h x}, pilot3Divergence V x)) := by
  have hm : MeasurableSet {x | 0 < h x} := hh.isOpen_positive.measurableSet
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖pilot3Divergence V x‖)
  · exact Eventually.of_forall (fun ε =>
      ((hh.continuousOn_ramp_divergence hV ε).mono subset_closure).aestronglyMeasurable hm)
  · exact Eventually.of_forall (fun ε => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_pilot3HeightRamp_le _) (norm_nonneg _)).trans_eq (one_mul _)))
  · exact (hh.integrableOn_divergence hV).norm
  · filter_upwards [ae_restrict_mem hm] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hx)] with ε hε hεx
    rw [pilot3HeightRamp_one ((one_le_div hε).mpr hεx.le), one_mul]

/-- Spatial divergence with outward normal minus the increasing-height unit
normal. The measure is canonical Hausdorff ONE-measure, normalization one. -/
theorem spatial_divergence : (∫ x in {x | 0 < h x}, pilot3Divergence V x) =
    -(∫ x, inner (𝕜 := ℝ) (V x) (pilot3Gradient h x) / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) := by
  obtain ⟨A⟩ := hh.exists_collarAtlas
  have hr := (pilot3_tendsto_ramp_density A.width_pos _
    (A.continuousOn_weightedHeightDensity hh _ (hh.continuousOn_flux hV))).neg
  simp only [pilot3WeightedHeightDensity_zero] at hr
  have he : Tendsto (fun ε : ℝ => ∫ x in {x | 0 < h x}, pilot3HeightRamp (h x / ε) * pilot3Divergence V x)
      (𝓝[>] 0) (𝓝 (-(∫ x, inner (𝕜 := ℝ) (V x) (pilot3Gradient h x) / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h))) := by
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds A.width_pos)] with ε hε hεA
    exact (hh.ramp_balance hV A ε hε hεA).symm
  exact tendsto_nhds_unique (hh.tendsto_integral_ramp_divergence hV) he

end Pilot3RegularHeight
namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem integrableOn_laplacian : IntegrableOn (pilot3Laplacian f) {x | 0 < h x} :=
  hf.toPilot3RegularHeight.integrableOn_divergence
    (fun x hx => (contDiffAt_pilot3Gradient (hf.future_smoothAt x hx)).of_le (by simp))

theorem integrable_surface_flux : Integrable (fun x => inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x) /
    ‖pilot3Gradient h x‖) (pilot3SurfaceMeasure h) :=
  hf.toPilot3RegularHeight.integrable_surface_flux
    (fun x hx => (contDiffAt_pilot3Gradient (hf.future_smoothAt x hx)).of_le (by simp))

theorem spatial_divergence : (∫ x in {x | 0 < h x}, pilot3Laplacian f x) =
    -(∫ x, inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x) / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) :=
  hf.toPilot3RegularHeight.spatial_divergence
    (fun x hx => (contDiffAt_pilot3Gradient (hf.future_smoothAt x hx)).of_le (by simp))

end SmoothPilot3
end BoundaryDraft
