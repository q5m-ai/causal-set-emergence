import BoundaryDraft.GraphWeightedCoarea
import BoundaryDraft.TwoFaceAngle
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Spatial divergence for the original admissible two-face class

The cutoff argument uses whole-space integration by parts (one-dimensional
FTC and Fubini), not an assumed smooth-boundary Stokes theorem. The collar
flux uses the canonical normalized Hausdorff surface measure.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

set_option maxHeartbeats 800000

/-- Euclidean divergence in the fixed orthonormal spatial basis. -/
def graphDivergence (V : JointSpace → JointSpace) (x : JointSpace) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ V x (EuclideanSpace.basisFun (Fin 3) ℝ i) i

/-- The trace of the actual derivative of the Euclidean gradient. -/
def graphLaplacian (f : Spatial → ℝ) : JointSpace → ℝ :=
  graphDivergence (graphGradient f)

private theorem contDiffAt_graphGradient {f : Spatial → ℝ} {x : JointSpace}
    (hf : ContDiffAt ℝ 3 (fun y : JointSpace => f y) x) :
    ContDiffAt ℝ 2 (graphGradient f) x :=
  (InnerProductSpace.toDual ℝ JointSpace).symm.contDiff.contDiffAt.comp x
    (hf.fderiv_right (by norm_num))

private theorem continuousAt_graphDivergence {V : JointSpace → JointSpace} {x : JointSpace}
    (hV : ContDiffAt ℝ 1 V x) : ContinuousAt (graphDivergence V) x := by
  apply tendsto_finset_sum
  intro i _
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp
    ((ContinuousLinearMap.apply ℝ JointSpace (EuclideanSpace.basisFun (Fin 3) ℝ i)).continuous.continuousAt.comp
      (hV.fderiv_right (m := 0) (by norm_num)).continuousAt)

/-- Whole-space divergence integrates to zero for compactly supported C¹
fields. This is obtained by applying the checked linewise integration by
parts theorem in each of the three coordinate directions. -/
theorem integral_graphDivergence_eq_zero {V : JointSpace → JointSpace}
    (hV : ContDiff ℝ 1 V) (hS : HasCompactSupport V) :
    (∫ x, graphDivergence V x) = 0 := by
  have hi (v : JointSpace) : Integrable (fun x => fderiv ℝ V x v) :=
    ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hS.fderiv_apply ℝ v)
  have hz (v : JointSpace) : (∫ x, fderiv ℝ V x v) = 0 := by
    have he := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := volume) (f := fun _ : JointSpace => (1 : ℝ)) (g := V) (v := v)
      (by simp)
      (by simpa using hi v)
      (by simpa using hV.continuous.integrable_of_hasCompactSupport hS)
      (differentiable_const 1) (hV.differentiable (by norm_num))
    simpa using he
  have hic (i : Fin 3) : Integrable (fun x =>
      fderiv ℝ V x (EuclideanSpace.basisFun (Fin 3) ℝ i) i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).integrable_comp (hi _)
  unfold graphDivergence
  rw [integral_finset_sum _ (fun i _ => hic i)]
  apply Finset.sum_eq_zero
  intro i _
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).integral_comp_comm
    (hi (EuclideanSpace.basisFun (Fin 3) ℝ i))
  simpa only [hz, map_zero] using he

/-- A fixed smooth height ramp, zero below one half and one above one. -/
def graphHeightRamp (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

private theorem contDiff_graphHeightRamp : ContDiff ℝ 3 graphHeightRamp :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem graphHeightRamp_zero {t : ℝ} (ht : t ≤ 1 / 2) : graphHeightRamp t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem graphHeightRamp_one {t : ℝ} (ht : 1 ≤ t) : graphHeightRamp t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem norm_graphHeightRamp_le (t : ℝ) : ‖graphHeightRamp t‖ ≤ 1 := by
  unfold graphHeightRamp
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

private theorem deriv_graphHeightRamp_zero {t : ℝ} (ht : t < 1 / 2) :
    deriv graphHeightRamp t = 0 := by
  have he : graphHeightRamp =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [gt_mem_nhds ht] with u hu
    exact graphHeightRamp_zero hu.le
  rw [he.deriv_eq, deriv_const]

private theorem deriv_graphHeightRamp_zero_of_gt {t : ℝ} (ht : 1 < t) :
    deriv graphHeightRamp t = 0 := by
  have he : graphHeightRamp =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [lt_mem_nhds ht] with u hu
    exact graphHeightRamp_one hu.le
  rw [he.deriv_eq, deriv_const]

/-- No global extension of either raw profile is assumed. The height ramp
kills all values outside the positive region. -/
def graphRampField (h f : Spatial → ℝ) (ε : ℝ) (x : JointSpace) : JointSpace :=
  graphHeightRamp (h x / ε) • graphGradient f x

private theorem continuous_deriv_graphHeightRamp : Continuous (deriv graphHeightRamp) :=
  contDiff_graphHeightRamp.continuous_deriv (by norm_num)

private theorem integral_deriv_graphHeightRamp :
    (∫ t in Icc (0 : ℝ) 1, deriv graphHeightRamp t) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (contDiff_graphHeightRamp.differentiable (by norm_num) t).hasDerivAt)
    (continuous_deriv_graphHeightRamp.intervalIntegrable 0 1)]
  rw [graphHeightRamp_one le_rfl, graphHeightRamp_zero (by norm_num)]
  norm_num

private theorem integral_ramp_density_rescale {δ ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
    (B : ℝ → ℝ) :
    (∫ t in Icc 0 δ, (deriv graphHeightRamp (t / ε) / ε) * B t) =
      ∫ u in Icc (0 : ℝ) 1, deriv graphHeightRamp u * B (ε * u) := by
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Icc
    (Icc_subset_Icc_right hεδ.le) (fun t ht => ?_)]
  swap
  · have htε : ε < t := lt_of_not_ge (fun ht' => ht.2 ⟨ht.1.1, ht'⟩)
    rw [deriv_graphHeightRamp_zero_of_gt ((one_lt_div hε).mpr htε), zero_div, zero_mul]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hε.le,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he := intervalIntegral.smul_integral_comp_mul_left
    (fun t => (deriv graphHeightRamp (t / ε) / ε) * B t) ε (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at he
  rw [← he, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [mul_div_cancel_left₀ _ hε.ne', smul_eq_mul]
  field_simp

private theorem tendsto_ramp_density {δ : ℝ} (hδ : 0 < δ)
    (B : ℝ → ℝ) (hB : ContinuousOn B (Icc 0 δ)) :
    Tendsto (fun ε : ℝ => ∫ t in Icc 0 δ,
      (deriv graphHeightRamp (t / ε) / ε) * B t) (𝓝[>] 0) (𝓝 (B 0)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hδ)] with ε hε hεδ
    exact ⟨hε, hεδ⟩
  have harg (ε : ℝ) (hε : 0 < ε ∧ ε < δ) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ε * u ∈ Icc 0 δ :=
    ⟨mul_nonneg hε.1.le hu.1,
      (mul_le_mul_of_nonneg_left hu.2 hε.1.le).trans (by simpa using hε.2.le)⟩
  have hB0 : ContinuousWithinAt B (Ici 0) 0 :=
    (continuousWithinAt_Icc_iff_Ici hδ).mp (hB 0 ⟨le_rfl, hδ.le⟩)
  have hlim : Tendsto (fun ε : ℝ =>
      ∫ u in Icc (0 : ℝ) 1, deriv graphHeightRamp u * B (ε * u))
      (𝓝[>] 0) (𝓝 (∫ u in Icc (0 : ℝ) 1, deriv graphHeightRamp u * B 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u => ‖deriv graphHeightRamp u‖ * C)
    · filter_upwards [hsmall] with ε hε
      exact (continuous_deriv_graphHeightRamp.continuousOn.mul
        (hB.comp (continuous_const.mul continuous_id).continuousOn (harg ε hε))).aestronglyMeasurable
          measurableSet_Icc
    · filter_upwards [hsmall] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ (harg ε hε u hu)) (norm_nonneg _)
    · exact (continuous_deriv_graphHeightRamp.norm.mul continuous_const).integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have ha : Tendsto (fun ε : ℝ => ε * u) (𝓝[>] 0) (𝓝[≥] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · simpa only [id_eq, zero_mul] using
            (((continuous_id : Continuous (fun ε : ℝ => ε)).mul
              (continuous_const : Continuous (fun _ : ℝ => u))).tendsto (0 : ℝ)).mono_left
              (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact mul_nonneg hε.le hu.1
      exact tendsto_const_nhds.mul (hB0.tendsto.comp ha)
  have hlim' : Tendsto (fun ε : ℝ =>
      ∫ u in Icc (0 : ℝ) 1, deriv graphHeightRamp u * B (ε * u)) (𝓝[>] 0) (𝓝 (B 0)) := by
    simpa only [integral_mul_const, integral_deriv_graphHeightRamp, one_mul] using hlim
  apply hlim'.congr'
  filter_upwards [hsmall] with ε hε
  exact (integral_ramp_density_rescale hε.1 hε.2 B).symm

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem continuousOn_graphLaplacian : ContinuousOn (graphLaplacian f) (graphClosedPositive h) := by
  intro x hx
  exact (continuousAt_graphDivergence
    ((contDiffAt_graphGradient (hf.smooth_future x hx)).of_le (by norm_num))).continuousWithinAt

theorem integrableOn_graphLaplacian : IntegrableOn (graphLaplacian f) {x : JointSpace | 0 < h x} :=
  (hf.continuousOn_graphLaplacian.integrableOn_compact
    hf.toGraphCapData.isCompact_closedPositive).mono_set subset_closure

theorem continuousOn_graphFlux :
    ContinuousOn (fun x => inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x))
      (graphClosedPositive h) :=
  (continuousOn_graphGradient_of_smooth hf.smooth_future).inner
    (continuousOn_graphGradient_of_smooth hf.smooth_near)

theorem integrable_graphSurface_flux :
    Integrable (fun x => inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
      ‖graphGradient h x‖) (graphSurfaceMeasure h) := by
  obtain ⟨A⟩ := hf.toAdmissibleGraphCap.exists_controlledCollarAtlas
  simpa only [graphLevelMeasure_zero] using A.integrable_graphLevel_weight_div
    hf.toAdmissibleGraphCap _ hf.continuousOn_graphFlux 0 ⟨le_rfl, A.width_pos.le⟩

omit hf in
private theorem graphRampField_zero (ε : ℝ) (hε : 0 < ε) (x : JointSpace)
    (hx : x ∉ graphClosedPositive h) : graphRampField h f ε x = 0 := by
  have hn : h x ≤ 0 := le_of_not_gt (fun hp => hx (subset_closure hp))
  rw [graphRampField, graphHeightRamp_zero ((div_nonpos_of_nonpos_of_nonneg hn hε.le).trans
    (by norm_num)), zero_smul]

private theorem contDiff_graphRampField (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (graphRampField h f ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ graphClosedPositive h
  · exact ((contDiff_graphHeightRamp.contDiffAt.comp x
      ((hf.smooth_near x hx).div_const ε)).of_le (by norm_num)).smul
        ((contDiffAt_graphGradient (hf.smooth_future x hx)).of_le (by norm_num))
  · have he : graphRampField h f ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact graphRampField_zero ε hε y hy
    exact contDiffAt_const.congr_of_eventuallyEq he

private theorem hasCompactSupport_graphRampField (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (graphRampField h f ε) := by
  apply hf.toGraphCapData.isCompact_closedPositive.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (graphRampField_zero ε hε x hn)

private theorem divergence_graphRampField (ε : ℝ) (x : JointSpace)
    (hx : x ∈ graphClosedPositive h) :
    graphDivergence (graphRampField h f ε) x =
      graphHeightRamp (h x / ε) * graphLaplacian f x +
        (deriv graphHeightRamp (h x / ε) / ε) *
          inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) := by
  have hh := (hf.smooth_near x hx).differentiableAt (by norm_num)
  have hg := (contDiffAt_graphGradient (hf.smooth_future x hx)).differentiableAt (by norm_num)
  have hr := (contDiff_graphHeightRamp.differentiable (by norm_num) (h x / ε)).hasDerivAt
  have hdiv : HasFDerivAt (fun y : JointSpace => h y / ε)
      (ε⁻¹ • fderiv ℝ (fun y : JointSpace => h y) x) x := by
    simpa only [div_eq_mul_inv] using hh.hasFDerivAt.mul_const ε⁻¹
  have hd := (hr.comp_hasFDerivAt x hdiv).smul hg.hasFDerivAt
  change HasFDerivAt (graphRampField h f ε) _ x at hd
  have hb (i : Fin 3) : fderiv ℝ (fun y : JointSpace => h y) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) = graphGradient h x i := by
    rw [graph_differential_eq_inner]
    simp [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.basisFun_apply]
  simp only [graphLaplacian, graphDivergence, hd.fderiv, Function.comp_apply,
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [hb, PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

private theorem ae_positive_eq_closedPositive :
    {x : JointSpace | 0 < h x} =ᶠ[ae volume] graphClosedPositive h := by
  have hz := hf.toAdmissibleGraphCap.volume_graphLevel_eq_zero 0
    (fun x hx => hf.regular_zero x hx.1 hx.2)
  have hn : ∀ᵐ x : JointSpace, x ∉ graphLevel h 0 := by
    simpa only [ae_iff, not_not] using hz
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · exact fun hp => (subset_closure (s := {y : JointSpace | 0 < h y}) hp)
  · intro hxc
    exact lt_of_le_of_ne (hf.toAdmissibleGraphCap.nonneg_on_closedPositive x hxc)
      (fun he => hx ⟨hxc, he.symm⟩)

private theorem integral_graphDivergence_ramp_closedPositive (ε : ℝ) (hε : 0 < ε) :
    (∫ x in graphClosedPositive h, graphDivergence (graphRampField h f ε) x) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_graphDivergence_eq_zero (hf.contDiff_graphRampField ε hε)
      (hf.hasCompactSupport_graphRampField ε hε)
  · intro x hx
    have he : graphRampField h f ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact graphRampField_zero ε hε y hy
    simp only [graphDivergence, he.fderiv_eq, fderiv_const, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, PiLp.zero_apply, Finset.sum_const_zero]

private theorem continuousOn_ramp_laplacian (ε : ℝ) :
    ContinuousOn (fun x : JointSpace => graphHeightRamp (h x / ε) * graphLaplacian f x)
      (graphClosedPositive h) :=
  (contDiff_graphHeightRamp.continuous.comp_continuousOn
    (hf.toAdmissibleGraphCap.continuousOn_closedPositive.div_const ε)).mul
      hf.continuousOn_graphLaplacian

private theorem continuousOn_ramp_flux (ε : ℝ) :
    ContinuousOn (fun x : JointSpace => (deriv graphHeightRamp (h x / ε) / ε) *
      inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x)) (graphClosedPositive h) :=
  ((continuous_deriv_graphHeightRamp.comp_continuousOn
    (hf.toAdmissibleGraphCap.continuousOn_closedPositive.div_const ε)).div_const ε).mul
      hf.continuousOn_graphFlux

private theorem integral_ramp_flux_eq_height (A : ControlledCollarAtlas h)
    (ε : ℝ) (hε : 0 < ε) (hεA : ε < A.width) :
    (∫ x in graphClosedPositive h, (deriv graphHeightRamp (h x / ε) / ε) *
      inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x)) =
      ∫ t in Icc 0 A.width, (deriv graphHeightRamp (t / ε) / ε) *
        graphWeightedHeightDensity h
          (fun x => inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x)) t := by
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero
    hf.toGraphCapData.isCompact_closedPositive.isClosed.measurableSet
    (show graphClosedCollar h A.width ⊆ graphClosedPositive h from inter_subset_left)]
  · exact A.integral_closedCollar_weighted hf.toAdmissibleGraphCap _ hf.continuousOn_graphFlux
      _ ((continuous_deriv_graphHeightRamp.comp (continuous_id.div_const ε)).div_const ε).continuousOn
  · intro x hx
    have hxt : A.width < h x := lt_of_not_ge (fun hle => hx.2 ⟨hx.1, hle⟩)
    rw [deriv_graphHeightRamp_zero_of_gt ((one_lt_div hε).mpr (hεA.trans hxt)),
      zero_div, zero_mul]

/-- The finite-cutoff identity, with all terms absolutely integrable before
splitting the integral. No boundary identity is an input. -/
theorem graph_ramp_balance (A : ControlledCollarAtlas h)
    (ε : ℝ) (hε : 0 < ε) (hεA : ε < A.width) :
    (∫ x in {x : JointSpace | 0 < h x}, graphHeightRamp (h x / ε) * graphLaplacian f x) =
      -(∫ t in Icc 0 A.width, (deriv graphHeightRamp (t / ε) / ε) *
        graphWeightedHeightDensity h
          (fun x => inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x)) t) := by
  rw [setIntegral_congr_set hf.ae_positive_eq_closedPositive]
  have he := hf.integral_graphDivergence_ramp_closedPositive ε hε
  rw [setIntegral_congr_fun hf.toGraphCapData.isCompact_closedPositive.isClosed.measurableSet
    (fun x hx => hf.divergence_graphRampField ε x hx),
    integral_add
      ((hf.continuousOn_ramp_laplacian ε).integrableOn_compact hf.toGraphCapData.isCompact_closedPositive)
      ((hf.continuousOn_ramp_flux ε).integrableOn_compact hf.toGraphCapData.isCompact_closedPositive),
    hf.integral_ramp_flux_eq_height A ε hε hεA] at he
  linarith

private theorem tendsto_integral_ramp_laplacian :
    Tendsto (fun ε : ℝ => ∫ x in {x : JointSpace | 0 < h x},
      graphHeightRamp (h x / ε) * graphLaplacian f x) (𝓝[>] 0)
      (𝓝 (∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x)) := by
  have hm : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖graphLaplacian f x‖)
  · exact Eventually.of_forall (fun ε =>
      ((hf.continuousOn_ramp_laplacian ε).mono subset_closure).aestronglyMeasurable hm)
  · exact Eventually.of_forall (fun ε => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_graphHeightRamp_le _) (norm_nonneg _)).trans_eq
        (one_mul _)))
  · exact hf.integrableOn_graphLaplacian.norm
  · filter_upwards [ae_restrict_mem hm] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds hx)] with ε hε hεx
    rw [graphHeightRamp_one ((one_le_div hε).mpr hεx.le), one_mul]

/-- S19 with weight one, on the actual original admissible two-face class.
The outward normal is minus the increasing-height normal. The surface measure
is the existing normalized Hausdorff measure, and positive-height critical
points are permitted. -/
theorem spatial_divergence :
    (∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) =
      -(∫ x, inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h) := by
  obtain ⟨A⟩ := hf.toAdmissibleGraphCap.exists_controlledCollarAtlas
  have hr := (tendsto_ramp_density A.width_pos _
    (A.continuousOn_graphWeightedHeightDensity hf.toAdmissibleGraphCap _ hf.continuousOn_graphFlux)).neg
  simp only [graphWeightedHeightDensity_zero] at hr
  have he : Tendsto (fun ε : ℝ => ∫ x in {x : JointSpace | 0 < h x},
      graphHeightRamp (h x / ε) * graphLaplacian f x) (𝓝[>] 0)
      (𝓝 (-(∫ x, inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h))) := by
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds A.width_pos)] with ε hε hεA
    exact (hf.graph_ramp_balance A ε hε hεA).symm
  exact tendsto_nhds_unique hf.tendsto_integral_ramp_laplacian he

end AdmissibleTwoFace
end BoundaryDraft
