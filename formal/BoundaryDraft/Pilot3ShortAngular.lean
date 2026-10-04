import BoundaryDraft.Pilot3CircleMoments
import BoundaryDraft.Pilot3Divergence
import BoundaryDraft.Pilot3Coefficient

/-!
# Angular terms in the absolute three-dimensional overlap two-jet

All circle moments are computed from the actual two-dimensional polar measure.
The spatial polynomial includes the future linear and Hessian terms and the
mixed and spatial surface terms. The absolute polynomial below also retains
the volume, moving time slice and time-quadratic surface contribution.
-/


open MeasureTheory Set Metric
open scoped BigOperators Topology InnerProductSpace

noncomputable section
namespace BoundaryDraft

set_option maxHeartbeats 800000

/-- Spatial and mixed terms in the absolute origin two-jet. No planar
comparison or planar analytic theorem is used. -/
def pilot3SpatialShortPolynomial (h f : Pilot3Space → ℝ) (z : ℝ × Pilot3Space) : ℝ :=
  (∫ x in {x : Pilot3Space | 0 < h x},
      inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) +
    (1 / 2 : ℝ) * (∫ x in {x : Pilot3Space | 0 < h x},
      fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x z.2 z.2) +
    (1 / 2 : ℝ) * (∫ x,
      (inner (𝕜 := ℝ) (pilot3Gradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) /
          ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)

/-- The coefficient left after full angular averaging. -/
def pilot3ShortSpaceCoefficient (h f : Pilot3Space → ℝ) : ℝ :=
  (Real.pi / 2) *
    ((∫ x in {x : Pilot3Space | 0 < h x}, pilot3Laplacian f x) +
      ∫ x, ‖pilot3Gradient f x‖ ^ 2 / ‖pilot3Gradient h x‖
        ∂pilot3SurfaceMeasure h)

/-- The time-square coefficient comes from the canonical joint itself. -/
def pilot3ShortTimeCoefficient (h : Pilot3Space → ℝ) : ℝ :=
  Real.pi * ∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h

/-- The moving time slice of the complete overlap. -/
def pilot3ShortLinearCoefficient (h : Pilot3Space → ℝ) : ℝ :=
  -(2 * Real.pi) * volume.real {x | 0 < h x}

/-- The absolute origin polynomial retains the actual volume and all time
terms. This definition does not compare the region with a planar cap. -/
def pilot3AbsoluteShortPolynomial (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime) : ℝ :=
  volume.real (pilot3Region h f) - z.1 * volume.real {x | 0 < h x} +
    (1 / 2 : ℝ) * z.1 ^ 2 *
      (∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) +
    pilot3SpatialShortPolynomial h f z

namespace SmoothPilot3

variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

private theorem continuousOn_futureHessian :
    ContinuousOn (fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)))
      (pilot3ClosedPositive h) := by
  intro x hx
  exact (((hf.future_smoothAt x hx).fderiv_right (m := 2)
    (WithTop.coe_le_coe.mpr le_top)).fderiv_right
    (m := 1) (by norm_num)).continuousAt.continuousWithinAt

private theorem integrableOn_positive_of_continuousOn
    {g : Pilot3Space → ℝ} (hg : ContinuousOn g (pilot3ClosedPositive h)) :
    IntegrableOn g {x : Pilot3Space | 0 < h x} :=
  (hg.integrableOn_compact hf.toPilot3RegularHeight.isCompact_closedPositive).mono_set subset_closure

/-- Absolute integrability of the source linear observable. -/
theorem integrableOn_shortLinear (v : Pilot3Space) :
    IntegrableOn (fun x : Pilot3Space => inner (𝕜 := ℝ) (pilot3Gradient f x) v)
      {x : Pilot3Space | 0 < h x} := by
  apply hf.integrableOn_positive_of_continuousOn
  exact (continuousOn_pilot3Gradient hf.future_smoothAt).inner continuousOn_const

/-- Absolute integrability of every source Hessian component. -/
theorem integrableOn_shortHessian (u v : Pilot3Space) :
    IntegrableOn (fun x : Pilot3Space =>
      fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x u v)
      {x : Pilot3Space | 0 < h x} := by
  apply hf.integrableOn_positive_of_continuousOn
  exact (hf.continuousOn_futureHessian.clm_apply continuousOn_const).clm_apply continuousOn_const

/-- A continuous weight divided by the regular joint slope is absolutely
integrable against the canonical surface measure. -/
theorem integrable_graphSurface_weight_div (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) :
    Integrable (fun x => w x / ‖pilot3Gradient h x‖) (pilot3SurfaceMeasure h) := by
  obtain ⟨A⟩ := hf.toPilot3RegularHeight.exists_collarAtlas
  simpa only [pilot3LevelMeasure_zero] using A.integrable_level_weight_div
    hf.toPilot3RegularHeight w hw 0 ⟨le_rfl, A.width_pos.le⟩

/-- Absolute integrability of a slope-weighted future-gradient component. -/
theorem integrable_graphSurface_inner_div (v : Pilot3Space) :
    Integrable (fun x => inner (𝕜 := ℝ) (pilot3Gradient f x) v /
      ‖pilot3Gradient h x‖) (pilot3SurfaceMeasure h) := by
  apply hf.integrable_graphSurface_weight_div
  exact (continuousOn_pilot3Gradient hf.future_smoothAt).inner continuousOn_const

/-- Absolute integrability of a slope-weighted product of future-gradient
components. -/
theorem integrable_graphSurface_inner_mul_div (u v : Pilot3Space) :
    Integrable (fun x =>
      (inner (𝕜 := ℝ) (pilot3Gradient f x) u *
        inner (𝕜 := ℝ) (pilot3Gradient f x) v) / ‖pilot3Gradient h x‖)
      (pilot3SurfaceMeasure h) := by
  apply hf.integrable_graphSurface_weight_div
  exact ((continuousOn_pilot3Gradient hf.future_smoothAt).inner continuousOn_const).mul
    ((continuousOn_pilot3Gradient hf.future_smoothAt).inner continuousOn_const)

/-- The squared future slope divided by the joint slope is absolutely
integrable. -/
theorem integrable_graphSurface_norm_sq_div :
    Integrable (fun x => ‖pilot3Gradient f x‖ ^ 2 / ‖pilot3Gradient h x‖)
      (pilot3SurfaceMeasure h) := by
  apply hf.integrable_graphSurface_weight_div
  exact (continuousOn_pilot3Gradient hf.future_smoothAt).norm.pow 2

/-- The trace of the actual second Fréchet derivative agrees with the
Laplacian defined as the divergence of the Euclidean gradient. -/
theorem sum_futureHessian_basis_eq_pilot3Laplacian (x : Pilot3Space)
    (hx : x ∈ pilot3ClosedPositive h) :
    (∑ i : Fin 2,
      fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = pilot3Laplacian f x := by
  have hD : HasFDerivAt (fun y : Pilot3Space => fderiv ℝ (fun z : Pilot3Space => f z) y)
      (fderiv ℝ (fderiv ℝ (fun z : Pilot3Space => f z)) x) x :=
    (((hf.future_smoothAt x hx).fderiv_right (m := 2)
      (WithTop.coe_le_coe.mpr le_top)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hG : HasFDerivAt (pilot3Gradient f)
      ((InnerProductSpace.toDual ℝ Pilot3Space).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (fun z : Pilot3Space => f z)) x)) x := by
    simpa only [pilot3Gradient, gradient] using
      (InnerProductSpace.toDual ℝ Pilot3Space).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
        x hD
  simp only [pilot3Laplacian, pilot3Divergence, hG.fderiv,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  let e := EuclideanSpace.basisFun (Fin 2) ℝ i
  let L := fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x e
  have hr := congrArg (fun A : Pilot3Space →L[ℝ] ℝ => A e)
    ((InnerProductSpace.toDual ℝ Pilot3Space).apply_symm_apply L)
  simpa only [e, L, InnerProductSpace.toDual_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right, map_one, one_mul, RCLike.conj_to_real] using hr.symm
private theorem integrable_shortProduct_of_continuousOn
    {g : Pilot3Space × Pilot3Circle → ℝ}
    (hg : ContinuousOn g (pilot3ClosedPositive h ×ˢ (univ : Set Pilot3Circle))) :
    Integrable g ((volume.restrict {x : Pilot3Space | 0 < h x}).prod pilot3CircleMeasure) := by
  have hi : IntegrableOn g
      ({x : Pilot3Space | 0 < h x} ×ˢ (univ : Set Pilot3Circle))
      ((volume : Measure Pilot3Space).prod pilot3CircleMeasure) :=
    (hg.integrableOn_compact
      (hf.toPilot3RegularHeight.isCompact_closedPositive.prod isCompact_univ)).mono_set
        (prod_mono subset_closure (Subset.refl univ))
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  simpa using hi

private theorem integrable_surfaceProduct_of_continuousOn
    {g : Pilot3Space × Pilot3Circle → ℝ}
    (hg : ContinuousOn g (pilot3SpatialJoint h ×ˢ (univ : Set Pilot3Circle))) :
    Integrable g ((pilot3SurfaceMeasure h).prod pilot3CircleMeasure) := by
  letI := hf.toPilot3RegularHeight.finite_surfaceMeasure
  have hi : IntegrableOn g (pilot3SpatialJoint h ×ˢ (univ : Set Pilot3Circle))
      ((pilot3SurfaceMeasure h).prod pilot3CircleMeasure) :=
    hg.integrableOn_compact
      (hf.toPilot3RegularHeight.isCompact_joint.prod isCompact_univ)
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  have ha : ∀ᵐ x ∂pilot3SurfaceMeasure h, x ∈ pilot3SpatialJoint h :=
    ae_restrict_mem hf.toPilot3RegularHeight.measurableSet_joint
  rw [Measure.restrict_eq_self_of_ae_mem ha, Measure.restrict_univ] at hi
  exact hi

/-- Joint absolute integrability of the source linear angular term, before
interchanging its spatial and circle integrals. -/
theorem integrable_shortLinear_angular (r : ℝ) :
    Integrable (fun p : Pilot3Space × Pilot3Circle =>
      inner (𝕜 := ℝ) (pilot3Gradient f p.1) (r • p.2.val))
      ((volume.restrict {x : Pilot3Space | 0 < h x}).prod pilot3CircleMeasure) := by
  apply hf.integrable_shortProduct_of_continuousOn
  have hp : ContinuousOn (fun p : Pilot3Space × Pilot3Circle => pilot3Gradient f p.1)
      (pilot3ClosedPositive h ×ˢ (univ : Set Pilot3Circle)) :=
    (continuousOn_pilot3Gradient hf.future_smoothAt).comp
      continuous_fst.continuousOn (fun _ hp => hp.1)
  exact hp.inner (continuous_const.smul
    (continuous_subtype_val.comp continuous_snd)).continuousOn

/-- Joint absolute integrability of the source Hessian angular term, before
Fubini. -/
theorem integrable_shortHessian_angular (r : ℝ) :
    Integrable (fun p : Pilot3Space × Pilot3Circle =>
      fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) p.1
        (r • p.2.val) (r • p.2.val))
      ((volume.restrict {x : Pilot3Space | 0 < h x}).prod pilot3CircleMeasure) := by
  apply hf.integrable_shortProduct_of_continuousOn
  have hH : ContinuousOn (fun p : Pilot3Space × Pilot3Circle =>
      fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) p.1)
      (pilot3ClosedPositive h ×ˢ (univ : Set Pilot3Circle)) :=
    hf.continuousOn_futureHessian.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hv : Continuous (fun p : Pilot3Space × Pilot3Circle => r • p.2.val) :=
    continuous_const.smul (continuous_subtype_val.comp continuous_snd)
  exact (hH.clm_apply hv.continuousOn).clm_apply hv.continuousOn

/-- Joint absolute integrability of the complete surface angular term,
including the mixed time-directional contribution, before Fubini. -/
theorem integrable_shortSurface_angular (s r : ℝ) :
    Integrable (fun p : Pilot3Space × Pilot3Circle =>
      (inner (𝕜 := ℝ) (pilot3Gradient f p.1) (r • p.2.val) ^ 2 -
        2 * s * inner (𝕜 := ℝ) (pilot3Gradient f p.1) (r • p.2.val)) /
          ‖pilot3Gradient h p.1‖)
      ((pilot3SurfaceMeasure h).prod pilot3CircleMeasure) := by
  apply hf.integrable_surfaceProduct_of_continuousOn
  have hp : ContinuousOn (fun p : Pilot3Space × Pilot3Circle => pilot3Gradient f p.1)
      (pilot3SpatialJoint h ×ˢ (univ : Set Pilot3Circle)) :=
    ((continuousOn_pilot3Gradient hf.future_smoothAt).mono inter_subset_left).comp
      continuous_fst.continuousOn (fun _ hp => hp.1)
  have hg : ContinuousOn (fun p : Pilot3Space × Pilot3Circle => ‖pilot3Gradient h p.1‖)
      (pilot3SpatialJoint h ×ˢ (univ : Set Pilot3Circle)) :=
    (((continuousOn_pilot3Gradient hf.toPilot3RegularHeight.smoothAt).mono inter_subset_left).comp
      continuous_fst.continuousOn (fun _ hp => hp.1)).norm
  have hv : Continuous (fun p : Pilot3Space × Pilot3Circle => r • p.2.val) :=
    continuous_const.smul (continuous_subtype_val.comp continuous_snd)
  apply (((hp.inner hv.continuousOn).pow 2).sub
    ((continuousOn_const.mul continuousOn_const).mul (hp.inner hv.continuousOn))).div hg
  intro p hpJ
  exact (hf.toPilot3RegularHeight.gradient_pos p.1 hpJ.1).ne'

/-- The complete source-linear contribution has zero full-circle average. -/
theorem integral_pilot3Circle_shortLinear (r : ℝ) :
    (∫ ω : Pilot3Circle,
      (∫ x in {x : Pilot3Space | 0 < h x},
        inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val))
      ∂pilot3CircleMeasure) = 0 := by
  have hi := hf.integrable_shortLinear_angular r
  rw [← integral_integral_swap hi]
  have hm : MeasurableSet {x : Pilot3Space | 0 < h x} :=
    hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  calc
    (∫ x in {x : Pilot3Space | 0 < h x},
        ∫ ω : Pilot3Circle,
          inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)
          ∂pilot3CircleMeasure) =
        ∫ _x in {x : Pilot3Space | 0 < h x}, (0 : ℝ) := by
      apply setIntegral_congr_fun hm
      intro x _
      simp_rw [inner_smul_right]
      rw [integral_const_mul, integral_pilot3Circle_inner, mul_zero]
    _ = 0 := by simp

/-- The source Hessian contribution averages to its actual Euclidean trace.
The trace-to-Laplacian bridge is pointwise and uses only the original C³
hypothesis. -/
theorem integral_pilot3Circle_shortHessian (r : ℝ) :
    (∫ ω : Pilot3Circle,
      (∫ x in {x : Pilot3Space | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x
          (r • ω.val) (r • ω.val))
      ∂pilot3CircleMeasure) =
      (Real.pi) * r ^ 2 *
        (∫ x in {x : Pilot3Space | 0 < h x}, pilot3Laplacian f x) := by
  have hi := hf.integrable_shortHessian_angular r
  rw [← integral_integral_swap hi]
  have hm : MeasurableSet {x : Pilot3Space | 0 < h x} :=
    hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  calc
    (∫ x in {x : Pilot3Space | 0 < h x},
        ∫ ω : Pilot3Circle,
          fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x
            (r • ω.val) (r • ω.val) ∂pilot3CircleMeasure) =
        ∫ x in {x : Pilot3Space | 0 < h x},
          ((Real.pi) * r ^ 2) * pilot3Laplacian f x := by
      apply setIntegral_congr_fun hm
      intro x hx
      let H := fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x
      calc
        (∫ ω : Pilot3Circle, H (r • ω.val) (r • ω.val)
            ∂pilot3CircleMeasure) =
            r ^ 2 * (∫ ω : Pilot3Circle, H ω.val ω.val ∂pilot3CircleMeasure) := by
          simp_rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with ω
          ring
        _ = r ^ 2 * ((Real.pi) * ∑ i : Fin 2,
            H (EuclideanSpace.basisFun (Fin 2) ℝ i)
              (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
          rw [integral_pilot3Circle_bilinear]
        _ = ((Real.pi) * r ^ 2) * pilot3Laplacian f x := by
          rw [hf.sum_futureHessian_basis_eq_pilot3Laplacian x (subset_closure hx)]
          ring
    _ = _ := by
      rw [integral_const_mul]

/-- The complete canonical-surface contribution has no mixed `s*r` average;
its quadratic part is the squared future slope. -/
theorem integral_pilot3Circle_shortSurface (s r : ℝ) :
    (∫ ω : Pilot3Circle,
      (∫ x,
        (inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val) ^ 2 -
          2 * s * inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)) /
            ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)
      ∂pilot3CircleMeasure) =
      (Real.pi) * r ^ 2 *
        (∫ x, ‖pilot3Gradient f x‖ ^ 2 / ‖pilot3Gradient h x‖
          ∂pilot3SurfaceMeasure h) := by
  letI := hf.toPilot3RegularHeight.finite_surfaceMeasure
  have hi := hf.integrable_shortSurface_angular s r
  rw [← integral_integral_swap hi]
  calc
    (∫ x, ∫ ω : Pilot3Circle,
        (inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val) ^ 2 -
          2 * s * inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)) /
            ‖pilot3Gradient h x‖ ∂pilot3CircleMeasure
        ∂pilot3SurfaceMeasure h) =
      ∫ x, ((Real.pi) * r ^ 2) *
        (‖pilot3Gradient f x‖ ^ 2 / ‖pilot3Gradient h x‖)
        ∂pilot3SurfaceMeasure h := by
      apply integral_congr_ae
      filter_upwards with x
      let p := pilot3Gradient f x
      let d := ‖pilot3Gradient h x‖
      have hsq := integrable_pilot3Circle_inner_mul p p
      have hlin := integrable_pilot3Circle_inner p
      calc
        (∫ ω : Pilot3Circle,
            (inner (𝕜 := ℝ) p (r • ω.val) ^ 2 -
              2 * s * inner (𝕜 := ℝ) p (r • ω.val)) / d
            ∂pilot3CircleMeasure) =
          ∫ ω : Pilot3Circle, d⁻¹ *
            (r ^ 2 * (inner (𝕜 := ℝ) p ω.val * inner (𝕜 := ℝ) p ω.val) -
              (2 * s * r) * inner (𝕜 := ℝ) p ω.val)
            ∂pilot3CircleMeasure := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [inner_smul_right]
          simp only [div_eq_mul_inv]
          ring
        _ = d⁻¹ * (r ^ 2 *
              (∫ ω : Pilot3Circle,
                inner (𝕜 := ℝ) p ω.val * inner (𝕜 := ℝ) p ω.val
                ∂pilot3CircleMeasure) -
            (2 * s * r) *
              (∫ ω : Pilot3Circle, inner (𝕜 := ℝ) p ω.val
                ∂pilot3CircleMeasure)) := by
          rw [integral_const_mul,
            integral_sub (hsq.const_mul _) (hlin.const_mul _),
            integral_const_mul, integral_const_mul]
        _ = ((Real.pi) * r ^ 2) * (‖p‖ ^ 2 / d) := by
          rw [integral_pilot3Circle_inner_mul, integral_pilot3Circle_inner,
            real_inner_self_eq_norm_sq]
          ring
    _ = _ := by
      rw [integral_const_mul]

/-- Absolute integrability of the angular polynomial follows from the three
joint absolute-integrability statements above, before its integral is split. -/
theorem integrable_pilot3Circle_pilot3SpatialShortPolynomial (s r : ℝ) :
    Integrable (fun ω : Pilot3Circle =>
      pilot3SpatialShortPolynomial h f (s, r • ω.val)) pilot3CircleMeasure := by
  letI := hf.toPilot3RegularHeight.finite_surfaceMeasure
  have hlin : Integrable (fun ω : Pilot3Circle =>
      ∫ x in {x : Pilot3Space | 0 < h x},
        inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)) pilot3CircleMeasure := by
    simpa using (hf.integrable_shortLinear_angular r).integral_prod_right
  have hhess : Integrable (fun ω : Pilot3Circle =>
      ∫ x in {x : Pilot3Space | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x
          (r • ω.val) (r • ω.val)) pilot3CircleMeasure := by
    simpa using (hf.integrable_shortHessian_angular r).integral_prod_right
  have hsurf : Integrable (fun ω : Pilot3Circle =>
      ∫ x,
        (inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val) ^ 2 -
          2 * s * inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)) /
            ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) pilot3CircleMeasure := by
    simpa using (hf.integrable_shortSurface_angular s r).integral_prod_right
  simpa only [pilot3SpatialShortPolynomial] using
    hlin.add (hhess.const_mul (1 / 2 : ℝ)) |>.add (hsurf.const_mul (1 / 2 : ℝ))

/-- Full angular averaging of the geometric short polynomial.  The answer is
independent of the time coordinate `s`. -/
theorem integral_pilot3Circle_pilot3SpatialShortPolynomial (s r : ℝ) :
    (∫ ω : Pilot3Circle, pilot3SpatialShortPolynomial h f (s, r • ω.val)
      ∂pilot3CircleMeasure) = pilot3ShortSpaceCoefficient h f * r ^ 2 := by
  letI := hf.toPilot3RegularHeight.finite_surfaceMeasure
  let A : Pilot3Circle → ℝ := fun ω =>
    ∫ x in {x : Pilot3Space | 0 < h x},
      inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)
  let B : Pilot3Circle → ℝ := fun ω =>
    ∫ x in {x : Pilot3Space | 0 < h x},
      fderiv ℝ (fderiv ℝ (fun y : Pilot3Space => f y)) x
        (r • ω.val) (r • ω.val)
  let C : Pilot3Circle → ℝ := fun ω =>
    ∫ x,
      (inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val) ^ 2 -
        2 * s * inner (𝕜 := ℝ) (pilot3Gradient f x) (r • ω.val)) /
          ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h
  let Bhalf : Pilot3Circle → ℝ := fun ω => (1 / 2 : ℝ) * B ω
  let Chalf : Pilot3Circle → ℝ := fun ω => (1 / 2 : ℝ) * C ω
  have hA : Integrable A pilot3CircleMeasure := by
    simpa [A] using (hf.integrable_shortLinear_angular r).integral_prod_right
  have hB : Integrable B pilot3CircleMeasure := by
    simpa [B] using (hf.integrable_shortHessian_angular r).integral_prod_right
  have hC : Integrable C pilot3CircleMeasure := by
    simpa [C] using (hf.integrable_shortSurface_angular s r).integral_prod_right
  have hBhalf : Integrable Bhalf pilot3CircleMeasure := by
    simpa [Bhalf, smul_eq_mul] using hB.const_mul (1 / 2 : ℝ)
  have hChalf : Integrable Chalf pilot3CircleMeasure := by
    simpa [Chalf, smul_eq_mul] using hC.const_mul (1 / 2 : ℝ)
  change (∫ ω : Pilot3Circle, (A ω + Bhalf ω) + Chalf ω
    ∂pilot3CircleMeasure) = _
  calc
    _ = (∫ ω : Pilot3Circle, A ω + Bhalf ω ∂pilot3CircleMeasure) +
        ∫ ω : Pilot3Circle, Chalf ω ∂pilot3CircleMeasure :=
      integral_add (hA.add hBhalf) hChalf
    _ = ((∫ ω : Pilot3Circle, A ω ∂pilot3CircleMeasure) +
          ∫ ω : Pilot3Circle, Bhalf ω ∂pilot3CircleMeasure) +
        ∫ ω : Pilot3Circle, Chalf ω ∂pilot3CircleMeasure := by
      rw [integral_add hA hBhalf]
    _ = (∫ ω : Pilot3Circle, A ω ∂pilot3CircleMeasure) +
        (1 / 2 : ℝ) * (∫ ω : Pilot3Circle, B ω ∂pilot3CircleMeasure) +
        (1 / 2 : ℝ) * (∫ ω : Pilot3Circle, C ω ∂pilot3CircleMeasure) := by
      dsimp only [Bhalf, Chalf]
      rw [integral_const_mul, integral_const_mul]
    _ = pilot3ShortSpaceCoefficient h f * r ^ 2 := by
      dsimp only [A, B, C]
      rw [hf.integral_pilot3Circle_shortLinear,
        hf.integral_pilot3Circle_shortHessian,
        hf.integral_pilot3Circle_shortSurface,
        pilot3ShortSpaceCoefficient]
      ring

/-- Absolute integrability of the entire origin polynomial on the circle. -/
theorem integrable_pilot3Circle_absoluteShortPolynomial (s r : ℝ) :
    Integrable (fun ω : Pilot3Circle => pilot3AbsoluteShortPolynomial h f (s, r • ω.val))
      pilot3CircleMeasure := by
  unfold pilot3AbsoluteShortPolynomial
  exact (integrable_const (volume.real (pilot3Region h f) - s * volume.real {x | 0 < h x} +
    (1 / 2 : ℝ) * s ^ 2 * ∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)).add
      (hf.integrable_pilot3Circle_pilot3SpatialShortPolynomial s r)

/-- All origin terms averaged with the actual circle measure. -/
theorem integral_pilot3Circle_absoluteShortPolynomial (s r : ℝ) :
    (∫ ω : Pilot3Circle, pilot3AbsoluteShortPolynomial h f (s, r • ω.val)
      ∂pilot3CircleMeasure) =
      2 * Real.pi * volume.real (pilot3Region h f) +
        pilot3ShortLinearCoefficient h * s + pilot3ShortTimeCoefficient h * s ^ 2 +
        pilot3ShortSpaceCoefficient h f * r ^ 2 := by
  simp only [pilot3AbsoluteShortPolynomial, Prod.fst]
  rw [integral_add (integrable_const (volume.real (pilot3Region h f) - s * volume.real {x | 0 < h x} +
    (1 / 2 : ℝ) * s ^ 2 * ∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h))
    (hf.integrable_pilot3Circle_pilot3SpatialShortPolynomial s r),
    integral_const, smul_eq_mul, pilot3Circle_mass,
    hf.integral_pilot3Circle_pilot3SpatialShortPolynomial]
  unfold pilot3ShortLinearCoefficient pilot3ShortTimeCoefficient
  ring

/-- The signed three-dimensional time/radial response is exactly the
independently fixed intrinsic target. Outward orientation is supplied by the
proved spatial divergence theorem; line normalization remains one. -/
theorem shortCoefficient_identification :
    (pilot3ShortTimeCoefficient h - 2 * pilot3ShortSpaceCoefficient h f) / Real.pi =
      pilot3BoundaryIntegral h f := by
  have hi := hf.integrable_graphSurface_weight_div (fun _ => 1) continuousOn_const
  have hg := hf.integrable_graphSurface_norm_sq_div
  have hp := hf.integrable_surface_flux
  rw [hf.boundaryIntegral_eq_spatialCoefficient]
  calc
    _ = (∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) +
        (∫ x, inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x) /
          ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) -
        ∫ x, ‖pilot3Gradient f x‖ ^ 2 / ‖pilot3Gradient h x‖
          ∂pilot3SurfaceMeasure h := by
      unfold pilot3ShortTimeCoefficient pilot3ShortSpaceCoefficient
      rw [hf.spatial_divergence]
      field_simp [Real.pi_ne_zero]
      ring
    _ = _ := by
      rw [← integral_add hi hp]
      have he := integral_sub (hi.add hp) hg
      simp only [Pi.add_apply, Pi.sub_apply] at he
      rw [← he]
      apply integral_congr_ae
      filter_upwards with x
      ring

end SmoothPilot3
end BoundaryDraft
