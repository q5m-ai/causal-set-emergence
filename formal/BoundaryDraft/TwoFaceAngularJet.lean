import BoundaryDraft.SphereQuadraticMoments
import BoundaryDraft.GraphDivergence
import BoundaryDraft.TwoFaceCoefficient

/-!
# Angular average of the two-face short polynomial

This file isolates the finite polynomial supplied by the geometric overlap
jet.  It proves its absolute integrability and smoothness, computes its full
sphere average from the checked spherical moments, and identifies the
resulting coefficient with the independently defined two-face boundary
correction.  No overlap expansion or short-displacement limit is asserted.
-/

open MeasureTheory Set Metric
open scoped BigOperators Topology InnerProductSpace

noncomputable section
namespace BoundaryDraft

set_option maxHeartbeats 800000

/-- The curved-minus-planar polynomial anticipated by the local overlap jet.
Its three terms are respectively the source linear term, the source Hessian
term, and the canonical joint-surface correction. -/
def twoFaceShortPolynomial (h f : Spatial → ℝ) (z : ℝ × JointSpace) : ℝ :=
  (∫ x in {x : JointSpace | 0 < h x},
      inner (𝕜 := ℝ) (graphGradient f x) z.2) +
    (1 / 2 : ℝ) * (∫ x in {x : JointSpace | 0 < h x},
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x z.2 z.2) +
    (1 / 2 : ℝ) * (∫ x,
      (inner (𝕜 := ℝ) (graphGradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2) /
          ‖graphGradient h x‖ ∂graphSurfaceMeasure h)

/-- The coefficient left after full angular averaging. -/
def twoFaceShortCoefficient (h f : Spatial → ℝ) : ℝ :=
  (2 * Real.pi / 3) *
    ((∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) +
      ∫ x, ‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖
        ∂graphSurfaceMeasure h)

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

private theorem continuousOn_futureHessian :
    ContinuousOn (fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)))
      (graphClosedPositive h) := by
  intro x hx
  exact (((hf.smooth_future x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).continuousAt.continuousWithinAt

private theorem integrableOn_positive_of_continuousOn
    {g : JointSpace → ℝ} (hg : ContinuousOn g (graphClosedPositive h)) :
    IntegrableOn g {x : JointSpace | 0 < h x} :=
  (hg.integrableOn_compact hf.toGraphCapData.isCompact_closedPositive).mono_set subset_closure

/-- Absolute integrability of the source linear observable. -/
theorem integrableOn_shortLinear (v : JointSpace) :
    IntegrableOn (fun x : JointSpace => inner (𝕜 := ℝ) (graphGradient f x) v)
      {x : JointSpace | 0 < h x} := by
  apply hf.integrableOn_positive_of_continuousOn
  exact (continuousOn_graphGradient_of_smooth hf.smooth_future).inner continuousOn_const

/-- Absolute integrability of every source Hessian component. -/
theorem integrableOn_shortHessian (u v : JointSpace) :
    IntegrableOn (fun x : JointSpace =>
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x u v)
      {x : JointSpace | 0 < h x} := by
  apply hf.integrableOn_positive_of_continuousOn
  exact (hf.continuousOn_futureHessian.clm_apply continuousOn_const).clm_apply continuousOn_const

/-- A continuous weight divided by the regular joint slope is absolutely
integrable against the canonical surface measure. -/
theorem integrable_graphSurface_weight_div (w : JointSpace → ℝ)
    (hw : ContinuousOn w (graphClosedPositive h)) :
    Integrable (fun x => w x / ‖graphGradient h x‖) (graphSurfaceMeasure h) := by
  obtain ⟨A⟩ := hf.toAdmissibleGraphCap.exists_controlledCollarAtlas
  simpa only [graphLevelMeasure_zero] using A.integrable_graphLevel_weight_div
    hf.toAdmissibleGraphCap w hw 0 ⟨le_rfl, A.width_pos.le⟩

/-- Absolute integrability of a slope-weighted future-gradient component. -/
theorem integrable_graphSurface_inner_div (v : JointSpace) :
    Integrable (fun x => inner (𝕜 := ℝ) (graphGradient f x) v /
      ‖graphGradient h x‖) (graphSurfaceMeasure h) := by
  apply hf.integrable_graphSurface_weight_div
  exact (continuousOn_graphGradient_of_smooth hf.smooth_future).inner continuousOn_const

/-- Absolute integrability of a slope-weighted product of future-gradient
components. -/
theorem integrable_graphSurface_inner_mul_div (u v : JointSpace) :
    Integrable (fun x =>
      (inner (𝕜 := ℝ) (graphGradient f x) u *
        inner (𝕜 := ℝ) (graphGradient f x) v) / ‖graphGradient h x‖)
      (graphSurfaceMeasure h) := by
  apply hf.integrable_graphSurface_weight_div
  exact ((continuousOn_graphGradient_of_smooth hf.smooth_future).inner continuousOn_const).mul
    ((continuousOn_graphGradient_of_smooth hf.smooth_future).inner continuousOn_const)

/-- The squared future slope divided by the joint slope is absolutely
integrable. -/
theorem integrable_graphSurface_norm_sq_div :
    Integrable (fun x => ‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖)
      (graphSurfaceMeasure h) := by
  apply hf.integrable_graphSurface_weight_div
  exact (continuousOn_graphGradient_of_smooth hf.smooth_future).norm.pow 2

/-- The trace of the actual second Fréchet derivative agrees with the
Laplacian defined as the divergence of the Euclidean gradient. -/
theorem sum_futureHessian_basis_eq_graphLaplacian (x : JointSpace)
    (hx : x ∈ graphClosedPositive h) :
    (∑ i : Fin 3,
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)) = graphLaplacian f x := by
  have hD : HasFDerivAt (fun y : JointSpace => fderiv ℝ (fun z : JointSpace => f z) y)
      (fderiv ℝ (fderiv ℝ (fun z : JointSpace => f z)) x) x :=
    (((hf.smooth_future x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hG : HasFDerivAt (graphGradient f)
      ((InnerProductSpace.toDual ℝ JointSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (fun z : JointSpace => f z)) x)) x := by
    simpa only [graphGradient, gradient] using
      (InnerProductSpace.toDual ℝ JointSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
        x hD
  simp only [graphLaplacian, graphDivergence, hG.fderiv,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  let e := EuclideanSpace.basisFun (Fin 3) ℝ i
  let L := fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x e
  have hr := congrArg (fun A : JointSpace →L[ℝ] ℝ => A e)
    ((InnerProductSpace.toDual ℝ JointSpace).apply_symm_apply L)
  simpa only [e, L, InnerProductSpace.toDual_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right, map_one, one_mul, RCLike.conj_to_real] using hr.symm

omit hf in
private theorem inner_eq_sum_basis (u v : JointSpace) :
    inner (𝕜 := ℝ) u v = ∑ i : Fin 3, v i *
      inner (𝕜 := ℝ) u (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real,
    EuclideanSpace.basisFun_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp [EuclideanSpace.single_apply]

omit hf in
private theorem bilinear_eq_sum_basis
    (B : JointSpace →L[ℝ] JointSpace →L[ℝ] ℝ) (u v : JointSpace) :
    B u v = ∑ i : Fin 3, ∑ j : Fin 3,
      (u i * v j) * B (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  conv_lhs =>
    rw [← e.toBasis.sum_repr u, ← e.toBasis.sum_repr v]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, EuclideanSpace.basisFun_repr, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [e]
  ring

private def twoFaceShortCoordinatePolynomial (h f : Spatial → ℝ)
    (z : ℝ × JointSpace) : ℝ :=
  (∑ i : Fin 3,
      (∫ x in {x : JointSpace | 0 < h x},
        inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i)) * z.2 i) +
    (1 / 2 : ℝ) * (∑ i : Fin 3, ∑ j : Fin 3,
      (∫ x in {x : JointSpace | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)) * (z.2 i * z.2 j)) +
    (1 / 2 : ℝ) *
      ((∑ i : Fin 3, ∑ j : Fin 3,
        (∫ x,
          (inner (𝕜 := ℝ) (graphGradient f x)
              (EuclideanSpace.basisFun (Fin 3) ℝ i) *
            inner (𝕜 := ℝ) (graphGradient f x)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)) /
                ‖graphGradient h x‖ ∂graphSurfaceMeasure h) * (z.2 i * z.2 j)) -
        2 * z.1 * (∑ i : Fin 3,
          (∫ x, inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ i) / ‖graphGradient h x‖
              ∂graphSurfaceMeasure h) * z.2 i))

private theorem integral_shortLinear_eq_coordinates (z : JointSpace) :
    (∫ x in {x : JointSpace | 0 < h x},
      inner (𝕜 := ℝ) (graphGradient f x) z) =
      ∑ i : Fin 3,
        (∫ x in {x : JointSpace | 0 < h x},
          inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ i)) * z i := by
  calc
    _ = ∫ x in {x : JointSpace | 0 < h x}, ∑ i : Fin 3,
        z i * inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
      apply integral_congr_ae
      filter_upwards with x
      exact inner_eq_sum_basis _ _
    _ = ∑ i : Fin 3, ∫ x in {x : JointSpace | 0 < h x},
        z i * inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
      integral_finset_sum _ (fun i _ =>
        (hf.integrableOn_shortLinear (EuclideanSpace.basisFun (Fin 3) ℝ i)).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
      ring

private theorem integral_shortHessian_eq_coordinates (z : JointSpace) :
    (∫ x in {x : JointSpace | 0 < h x},
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x z z) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∫ x in {x : JointSpace | 0 < h x},
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
            (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)) * (z i * z j) := by
  calc
    _ = ∫ x in {x : JointSpace | 0 < h x}, ∑ i : Fin 3, ∑ j : Fin 3,
        (z i * z j) *
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
            (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
      apply integral_congr_ae
      filter_upwards with x
      exact bilinear_eq_sum_basis _ _ _
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in {x : JointSpace | 0 < h x}, (z i * z j) *
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
            (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
        (hf.integrableOn_shortHessian (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum _ (fun j _ =>
        (hf.integrableOn_shortHessian (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)).const_mul _)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      ring

private theorem integral_graphSurface_inner_eq_coordinates (z : JointSpace) :
    (∫ x, inner (𝕜 := ℝ) (graphGradient f x) z / ‖graphGradient h x‖
      ∂graphSurfaceMeasure h) =
      ∑ i : Fin 3,
        (∫ x, inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) / ‖graphGradient h x‖
            ∂graphSurfaceMeasure h) * z i := by
  calc
    _ = ∫ x, ∑ i : Fin 3, z i *
        (inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) / ‖graphGradient h x‖)
        ∂graphSurfaceMeasure h := by
      apply integral_congr_ae
      filter_upwards with x
      rw [inner_eq_sum_basis]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin 3, ∫ x, z i *
        (inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) / ‖graphGradient h x‖)
        ∂graphSurfaceMeasure h :=
      integral_finset_sum _ (fun i _ =>
        (hf.integrable_graphSurface_inner_div
          (EuclideanSpace.basisFun (Fin 3) ℝ i)).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
      ring

private theorem integral_graphSurface_inner_sq_eq_coordinates (z : JointSpace) :
    (∫ x, inner (𝕜 := ℝ) (graphGradient f x) z ^ 2 / ‖graphGradient h x‖
      ∂graphSurfaceMeasure h) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∫ x,
          (inner (𝕜 := ℝ) (graphGradient f x)
              (EuclideanSpace.basisFun (Fin 3) ℝ i) *
            inner (𝕜 := ℝ) (graphGradient f x)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)) / ‖graphGradient h x‖
            ∂graphSurfaceMeasure h) * (z i * z j) := by
  calc
    _ = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, (z i * z j) *
        ((inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ i) *
          inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)) / ‖graphGradient h x‖)
        ∂graphSurfaceMeasure h := by
      apply integral_congr_ae
      filter_upwards with x
      rw [inner_eq_sum_basis]
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (z i * z j) *
        ((inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ i) *
          inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)) / ‖graphGradient h x‖)
        ∂graphSurfaceMeasure h := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
        (hf.integrable_graphSurface_inner_mul_div
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum _ (fun j _ =>
        (hf.integrable_graphSurface_inner_mul_div
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)).const_mul _)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      ring

private theorem twoFaceShortPolynomial_eq_coordinates (z : ℝ × JointSpace) :
    twoFaceShortPolynomial h f z = twoFaceShortCoordinatePolynomial h f z := by
  rw [twoFaceShortPolynomial, twoFaceShortCoordinatePolynomial,
    hf.integral_shortLinear_eq_coordinates, hf.integral_shortHessian_eq_coordinates]
  have hsq := hf.integrable_graphSurface_inner_mul_div z.2 z.2
  have hlin := (hf.integrable_graphSurface_inner_div z.2).const_mul (2 * z.1)
  rw [show (fun x : JointSpace =>
      (inner (𝕜 := ℝ) (graphGradient f x) z.2 ^ 2 -
        2 * z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2) /
          ‖graphGradient h x‖) =
      fun x => inner (𝕜 := ℝ) (graphGradient f x) z.2 ^ 2 /
          ‖graphGradient h x‖ -
        (2 * z.1) * (inner (𝕜 := ℝ) (graphGradient f x) z.2 /
          ‖graphGradient h x‖) by
      funext x
      ring,
    integral_sub (by simpa only [pow_two] using hsq) hlin,
    hf.integral_graphSurface_inner_sq_eq_coordinates,
    integral_const_mul, hf.integral_graphSurface_inner_eq_coordinates]

/-- The geometric jet polynomial is a genuine finite degree-two polynomial;
in particular it is smooth to every order in `(time, space)`. -/
theorem contDiff_twoFaceShortPolynomial :
    ContDiff ℝ ⊤ (twoFaceShortPolynomial h f) := by
  rw [show twoFaceShortPolynomial h f = twoFaceShortCoordinatePolynomial h f from
    funext hf.twoFaceShortPolynomial_eq_coordinates]
  unfold twoFaceShortCoordinatePolynomial
  have hc (i : Fin 3) : ContDiff ℝ ⊤ (fun z : ℝ × JointSpace => z.2 i) := by
    simpa only [Function.comp_apply] using
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.comp
        (contDiff_snd : ContDiff ℝ ⊤ (Prod.snd : ℝ × JointSpace → JointSpace)))
  have hlinear : ContDiff ℝ ⊤ (fun z : ℝ × JointSpace =>
      ∑ i : Fin 3,
        (∫ x in {x : JointSpace | 0 < h x},
          inner (𝕜 := ℝ) (graphGradient f x)
            (EuclideanSpace.basisFun (Fin 3) ℝ i)) * z.2 i) := by
    exact ContDiff.sum fun i _ => contDiff_const.mul (hc i)
  have hhessian : ContDiff ℝ ⊤ (fun z : ℝ × JointSpace =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∫ x in {x : JointSpace | 0 < h x},
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
            (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)) * (z.2 i * z.2 j)) := by
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul ((hc i).mul (hc j))
  have hsurfaceQuadratic : ContDiff ℝ ⊤ (fun z : ℝ × JointSpace =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∫ x,
          (inner (𝕜 := ℝ) (graphGradient f x)
              (EuclideanSpace.basisFun (Fin 3) ℝ i) *
            inner (𝕜 := ℝ) (graphGradient f x)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)) /
                ‖graphGradient h x‖ ∂graphSurfaceMeasure h) * (z.2 i * z.2 j)) := by
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul ((hc i).mul (hc j))
  have hsurfaceLinear : ContDiff ℝ ⊤ (fun z : ℝ × JointSpace =>
      ∑ i : Fin 3,
        (∫ x, inner (𝕜 := ℝ) (graphGradient f x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) / ‖graphGradient h x‖
            ∂graphSurfaceMeasure h) * z.2 i) := by
    exact ContDiff.sum fun i _ => contDiff_const.mul (hc i)
  exact (hlinear.add (contDiff_const.mul hhessian)).add
    (contDiff_const.mul (hsurfaceQuadratic.sub
      (((contDiff_const.mul contDiff_fst).mul hsurfaceLinear))))

/-- Continuity, recorded separately for downstream dominated-averaging code. -/
theorem continuous_twoFaceShortPolynomial : Continuous (twoFaceShortPolynomial h f) :=
  hf.contDiff_twoFaceShortPolynomial.continuous

private theorem integrable_shortProduct_of_continuousOn
    {g : JointSpace × OverlapSphere → ℝ}
    (hg : ContinuousOn g (graphClosedPositive h ×ˢ (univ : Set OverlapSphere))) :
    Integrable g ((volume.restrict {x : JointSpace | 0 < h x}).prod overlapSphereMeasure) := by
  have hi : IntegrableOn g
      ({x : JointSpace | 0 < h x} ×ˢ (univ : Set OverlapSphere))
      ((volume : Measure JointSpace).prod overlapSphereMeasure) :=
    (hg.integrableOn_compact
      (hf.toGraphCapData.isCompact_closedPositive.prod isCompact_univ)).mono_set
        (prod_mono subset_closure (Subset.refl univ))
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  simpa using hi

private theorem integrable_surfaceProduct_of_continuousOn
    {g : JointSpace × OverlapSphere → ℝ}
    (hg : ContinuousOn g (graphJoint h ×ˢ (univ : Set OverlapSphere))) :
    Integrable g ((graphSurfaceMeasure h).prod overlapSphereMeasure) := by
  letI := hf.toAdmissibleGraphCap.finite_graphSurfaceMeasure
  have hi : IntegrableOn g (graphJoint h ×ˢ (univ : Set OverlapSphere))
      ((graphSurfaceMeasure h).prod overlapSphereMeasure) :=
    hg.integrableOn_compact
      (hf.toAdmissibleGraphCap.isCompact_joint.prod isCompact_univ)
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  rw [Measure.restrict_eq_self_of_ae_mem (ae_graphJoint hf.toAdmissibleGraphCap),
    Measure.restrict_univ] at hi
  exact hi

/-- Joint absolute integrability of the source linear angular term, before
interchanging its spatial and sphere integrals. -/
theorem integrable_shortLinear_angular (r : ℝ) :
    Integrable (fun p : JointSpace × OverlapSphere =>
      inner (𝕜 := ℝ) (graphGradient f p.1) (r • p.2.val))
      ((volume.restrict {x : JointSpace | 0 < h x}).prod overlapSphereMeasure) := by
  apply hf.integrable_shortProduct_of_continuousOn
  have hp : ContinuousOn (fun p : JointSpace × OverlapSphere => graphGradient f p.1)
      (graphClosedPositive h ×ˢ (univ : Set OverlapSphere)) :=
    (continuousOn_graphGradient_of_smooth hf.smooth_future).comp
      continuous_fst.continuousOn (fun _ hp => hp.1)
  exact hp.inner (continuous_const.smul
    (continuous_subtype_val.comp continuous_snd)).continuousOn

/-- Joint absolute integrability of the source Hessian angular term, before
Fubini. -/
theorem integrable_shortHessian_angular (r : ℝ) :
    Integrable (fun p : JointSpace × OverlapSphere =>
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) p.1
        (r • p.2.val) (r • p.2.val))
      ((volume.restrict {x : JointSpace | 0 < h x}).prod overlapSphereMeasure) := by
  apply hf.integrable_shortProduct_of_continuousOn
  have hH : ContinuousOn (fun p : JointSpace × OverlapSphere =>
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) p.1)
      (graphClosedPositive h ×ˢ (univ : Set OverlapSphere)) :=
    hf.continuousOn_futureHessian.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hv : Continuous (fun p : JointSpace × OverlapSphere => r • p.2.val) :=
    continuous_const.smul (continuous_subtype_val.comp continuous_snd)
  exact (hH.clm_apply hv.continuousOn).clm_apply hv.continuousOn

/-- Joint absolute integrability of the complete surface angular term,
including the mixed time-directional contribution, before Fubini. -/
theorem integrable_shortSurface_angular (s r : ℝ) :
    Integrable (fun p : JointSpace × OverlapSphere =>
      (inner (𝕜 := ℝ) (graphGradient f p.1) (r • p.2.val) ^ 2 -
        2 * s * inner (𝕜 := ℝ) (graphGradient f p.1) (r • p.2.val)) /
          ‖graphGradient h p.1‖)
      ((graphSurfaceMeasure h).prod overlapSphereMeasure) := by
  apply hf.integrable_surfaceProduct_of_continuousOn
  have hp : ContinuousOn (fun p : JointSpace × OverlapSphere => graphGradient f p.1)
      (graphJoint h ×ˢ (univ : Set OverlapSphere)) :=
    ((continuousOn_graphGradient_of_smooth hf.smooth_future).mono inter_subset_left).comp
      continuous_fst.continuousOn (fun _ hp => hp.1)
  have hg : ContinuousOn (fun p : JointSpace × OverlapSphere => ‖graphGradient h p.1‖)
      (graphJoint h ×ˢ (univ : Set OverlapSphere)) :=
    (((continuousOn_graphGradient_of_smooth hf.smooth_near).mono inter_subset_left).comp
      continuous_fst.continuousOn (fun _ hp => hp.1)).norm
  have hv : Continuous (fun p : JointSpace × OverlapSphere => r • p.2.val) :=
    continuous_const.smul (continuous_subtype_val.comp continuous_snd)
  apply (((hp.inner hv.continuousOn).pow 2).sub
    ((continuousOn_const.mul continuousOn_const).mul (hp.inner hv.continuousOn))).div hg
  intro p hpJ
  exact (hf.toAdmissibleGraphCap.graphSlope_pos p.1 hpJ.1).ne'

/-- The complete source-linear contribution has zero full-sphere average. -/
theorem integral_overlapSphere_shortLinear (r : ℝ) :
    (∫ ω : OverlapSphere,
      (∫ x in {x : JointSpace | 0 < h x},
        inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val))
      ∂overlapSphereMeasure) = 0 := by
  have hi := hf.integrable_shortLinear_angular r
  rw [← integral_integral_swap hi]
  have hm : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  calc
    (∫ x in {x : JointSpace | 0 < h x},
        ∫ ω : OverlapSphere,
          inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)
          ∂overlapSphereMeasure) =
        ∫ _x in {x : JointSpace | 0 < h x}, (0 : ℝ) := by
      apply setIntegral_congr_fun hm
      intro x _
      simp_rw [inner_smul_right]
      rw [integral_const_mul, integral_overlapSphere_inner, mul_zero]
    _ = 0 := by simp

/-- The source Hessian contribution averages to its actual Euclidean trace.
The trace-to-Laplacian bridge is pointwise and uses only the original C³
hypothesis. -/
theorem integral_overlapSphere_shortHessian (r : ℝ) :
    (∫ ω : OverlapSphere,
      (∫ x in {x : JointSpace | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
          (r • ω.val) (r • ω.val))
      ∂overlapSphereMeasure) =
      (4 * Real.pi / 3) * r ^ 2 *
        (∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) := by
  have hi := hf.integrable_shortHessian_angular r
  rw [← integral_integral_swap hi]
  have hm : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  calc
    (∫ x in {x : JointSpace | 0 < h x},
        ∫ ω : OverlapSphere,
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
            (r • ω.val) (r • ω.val) ∂overlapSphereMeasure) =
        ∫ x in {x : JointSpace | 0 < h x},
          ((4 * Real.pi / 3) * r ^ 2) * graphLaplacian f x := by
      apply setIntegral_congr_fun hm
      intro x hx
      let H := fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
      calc
        (∫ ω : OverlapSphere, H (r • ω.val) (r • ω.val)
            ∂overlapSphereMeasure) =
            r ^ 2 * (∫ ω : OverlapSphere, H ω.val ω.val ∂overlapSphereMeasure) := by
          simp_rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with ω
          ring
        _ = r ^ 2 * ((4 * Real.pi / 3) * ∑ i : Fin 3,
            H (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
          rw [integral_overlapSphere_bilinear]
        _ = ((4 * Real.pi / 3) * r ^ 2) * graphLaplacian f x := by
          rw [hf.sum_futureHessian_basis_eq_graphLaplacian x (subset_closure hx)]
          ring
    _ = _ := by
      rw [integral_const_mul]

/-- The complete canonical-surface contribution has no mixed `s*r` average;
its quadratic part is the squared future slope. -/
theorem integral_overlapSphere_shortSurface (s r : ℝ) :
    (∫ ω : OverlapSphere,
      (∫ x,
        (inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val) ^ 2 -
          2 * s * inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)) /
            ‖graphGradient h x‖ ∂graphSurfaceMeasure h)
      ∂overlapSphereMeasure) =
      (4 * Real.pi / 3) * r ^ 2 *
        (∫ x, ‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h) := by
  letI := hf.toAdmissibleGraphCap.finite_graphSurfaceMeasure
  have hi := hf.integrable_shortSurface_angular s r
  rw [← integral_integral_swap hi]
  calc
    (∫ x, ∫ ω : OverlapSphere,
        (inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val) ^ 2 -
          2 * s * inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)) /
            ‖graphGradient h x‖ ∂overlapSphereMeasure
        ∂graphSurfaceMeasure h) =
      ∫ x, ((4 * Real.pi / 3) * r ^ 2) *
        (‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖)
        ∂graphSurfaceMeasure h := by
      apply integral_congr_ae
      filter_upwards with x
      let p := graphGradient f x
      let d := ‖graphGradient h x‖
      have hsq := integrable_overlapSphere_inner_mul p p
      have hlin := integrable_overlapSphere_inner p
      calc
        (∫ ω : OverlapSphere,
            (inner (𝕜 := ℝ) p (r • ω.val) ^ 2 -
              2 * s * inner (𝕜 := ℝ) p (r • ω.val)) / d
            ∂overlapSphereMeasure) =
          ∫ ω : OverlapSphere, d⁻¹ *
            (r ^ 2 * (inner (𝕜 := ℝ) p ω.val * inner (𝕜 := ℝ) p ω.val) -
              (2 * s * r) * inner (𝕜 := ℝ) p ω.val)
            ∂overlapSphereMeasure := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [inner_smul_right]
          simp only [div_eq_mul_inv]
          ring
        _ = d⁻¹ * (r ^ 2 *
              (∫ ω : OverlapSphere,
                inner (𝕜 := ℝ) p ω.val * inner (𝕜 := ℝ) p ω.val
                ∂overlapSphereMeasure) -
            (2 * s * r) *
              (∫ ω : OverlapSphere, inner (𝕜 := ℝ) p ω.val
                ∂overlapSphereMeasure)) := by
          rw [integral_const_mul,
            integral_sub (hsq.const_mul _) (hlin.const_mul _),
            integral_const_mul, integral_const_mul]
        _ = ((4 * Real.pi / 3) * r ^ 2) * (‖p‖ ^ 2 / d) := by
          rw [integral_overlapSphere_inner_mul, integral_overlapSphere_inner,
            real_inner_self_eq_norm_sq]
          ring
    _ = _ := by
      rw [integral_const_mul]

/-- Absolute integrability of the angular polynomial follows from the three
joint absolute-integrability statements above, before its integral is split. -/
theorem integrable_overlapSphere_twoFaceShortPolynomial (s r : ℝ) :
    Integrable (fun ω : OverlapSphere =>
      twoFaceShortPolynomial h f (s, r • ω.val)) overlapSphereMeasure := by
  letI := hf.toAdmissibleGraphCap.finite_graphSurfaceMeasure
  have hlin : Integrable (fun ω : OverlapSphere =>
      ∫ x in {x : JointSpace | 0 < h x},
        inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)) overlapSphereMeasure := by
    simpa using (hf.integrable_shortLinear_angular r).integral_prod_right
  have hhess : Integrable (fun ω : OverlapSphere =>
      ∫ x in {x : JointSpace | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
          (r • ω.val) (r • ω.val)) overlapSphereMeasure := by
    simpa using (hf.integrable_shortHessian_angular r).integral_prod_right
  have hsurf : Integrable (fun ω : OverlapSphere =>
      ∫ x,
        (inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val) ^ 2 -
          2 * s * inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)) /
            ‖graphGradient h x‖ ∂graphSurfaceMeasure h) overlapSphereMeasure := by
    simpa using (hf.integrable_shortSurface_angular s r).integral_prod_right
  simpa only [twoFaceShortPolynomial] using
    hlin.add (hhess.const_mul (1 / 2 : ℝ)) |>.add (hsurf.const_mul (1 / 2 : ℝ))

/-- Full angular averaging of the geometric short polynomial.  The answer is
independent of the time coordinate `s`. -/
theorem integral_overlapSphere_twoFaceShortPolynomial (s r : ℝ) :
    (∫ ω : OverlapSphere, twoFaceShortPolynomial h f (s, r • ω.val)
      ∂overlapSphereMeasure) = twoFaceShortCoefficient h f * r ^ 2 := by
  letI := hf.toAdmissibleGraphCap.finite_graphSurfaceMeasure
  let A : OverlapSphere → ℝ := fun ω =>
    ∫ x in {x : JointSpace | 0 < h x},
      inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)
  let B : OverlapSphere → ℝ := fun ω =>
    ∫ x in {x : JointSpace | 0 < h x},
      fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x
        (r • ω.val) (r • ω.val)
  let C : OverlapSphere → ℝ := fun ω =>
    ∫ x,
      (inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val) ^ 2 -
        2 * s * inner (𝕜 := ℝ) (graphGradient f x) (r • ω.val)) /
          ‖graphGradient h x‖ ∂graphSurfaceMeasure h
  let Bhalf : OverlapSphere → ℝ := fun ω => (1 / 2 : ℝ) * B ω
  let Chalf : OverlapSphere → ℝ := fun ω => (1 / 2 : ℝ) * C ω
  have hA : Integrable A overlapSphereMeasure := by
    simpa [A] using (hf.integrable_shortLinear_angular r).integral_prod_right
  have hB : Integrable B overlapSphereMeasure := by
    simpa [B] using (hf.integrable_shortHessian_angular r).integral_prod_right
  have hC : Integrable C overlapSphereMeasure := by
    simpa [C] using (hf.integrable_shortSurface_angular s r).integral_prod_right
  have hBhalf : Integrable Bhalf overlapSphereMeasure := by
    simpa [Bhalf, smul_eq_mul] using hB.const_mul (1 / 2 : ℝ)
  have hChalf : Integrable Chalf overlapSphereMeasure := by
    simpa [Chalf, smul_eq_mul] using hC.const_mul (1 / 2 : ℝ)
  change (∫ ω : OverlapSphere, (A ω + Bhalf ω) + Chalf ω
    ∂overlapSphereMeasure) = _
  calc
    _ = (∫ ω : OverlapSphere, A ω + Bhalf ω ∂overlapSphereMeasure) +
        ∫ ω : OverlapSphere, Chalf ω ∂overlapSphereMeasure :=
      integral_add (hA.add hBhalf) hChalf
    _ = ((∫ ω : OverlapSphere, A ω ∂overlapSphereMeasure) +
          ∫ ω : OverlapSphere, Bhalf ω ∂overlapSphereMeasure) +
        ∫ ω : OverlapSphere, Chalf ω ∂overlapSphereMeasure := by
      rw [integral_add hA hBhalf]
    _ = (∫ ω : OverlapSphere, A ω ∂overlapSphereMeasure) +
        (1 / 2 : ℝ) * (∫ ω : OverlapSphere, B ω ∂overlapSphereMeasure) +
        (1 / 2 : ℝ) * (∫ ω : OverlapSphere, C ω ∂overlapSphereMeasure) := by
      dsimp only [Bhalf, Chalf]
      rw [integral_const_mul, integral_const_mul]
    _ = twoFaceShortCoefficient h f * r ^ 2 := by
      dsimp only [A, B, C]
      rw [hf.integral_overlapSphere_shortLinear,
        hf.integral_overlapSphere_shortHessian,
        hf.integral_overlapSphere_shortSurface,
        twoFaceShortCoefficient]
      ring

/-- The normalized angular coefficient is exactly the independently defined
two-face target minus its planar counterpart.  This uses the proved spatial
divergence theorem and geometric coefficient identity, not either statement
as an assumption. -/
theorem twoFaceShortCoefficient_identification :
    (-3 / (2 * Real.pi)) * twoFaceShortCoefficient h f =
      twoFaceBoundaryIntegral h f - graphBoundaryIntegral h := by
  have hcorrection :
      (∫ x, (inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) -
        ‖graphGradient f x‖ ^ 2) / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h) =
      (∫ x, inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h) -
      ∫ x, ‖graphGradient f x‖ ^ 2 / ‖graphGradient h x‖
        ∂graphSurfaceMeasure h := by
    rw [← integral_sub hf.integrable_graphSurface_flux
      hf.integrable_graphSurface_norm_sq_div]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hf.boundaryIntegral_sub_planar, hcorrection,
    twoFaceShortCoefficient, hf.spatial_divergence]
  field_simp [ne_of_gt Real.pi_pos]
  ring

end AdmissibleTwoFace
end BoundaryDraft
