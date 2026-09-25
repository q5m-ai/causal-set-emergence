import BoundaryDraft.GraphChart
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Ambient transport in a regular height chart

The height-frame constraints are obtained by differentiating the chart's
inverse identities throughout its open target. The checked frame determinant
then gives the local ambient change of variables. No level-surface transport
or gluing statement is assumed or proved in this file.
-/

open MeasureTheory Set Filter
open scoped Topology Matrix
noncomputable section
namespace BoundaryDraft

private theorem joint_det_eq_frame (A : JointSpace →L[ℝ] JointSpace) :
    A.toLinearMap.det = Matrix.det
      ![(A (EuclideanSpace.basisFun (Fin 3) ℝ 0) : Spatial),
        (A (EuclideanSpace.basisFun (Fin 3) ℝ 1) : Spatial),
        (A (EuclideanSpace.basisFun (Fin 3) ℝ 2) : Spatial)] := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr]

namespace RegularHeightChart

variable {h : Spatial → ℝ} (c : RegularHeightChart h)

/-- Actual inverse derivative at each point of the open chart target. -/
theorem hasFDerivAt_symm (p : JointSpace) (hp : p ∈ c.chart.target) :
    HasFDerivAt c.chart.symm (fderiv ℝ c.chart.symm p) p :=
  (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)).differentiableAt
    (by norm_num) |>.hasFDerivAt

/-- The inverse chart has height equal to its first coordinate on its target. -/
theorem height_symm (p : JointSpace) (hp : p ∈ c.chart.target) :
    h (c.chart.symm p) = p 0 := by
  rw [← c.height, c.chart.right_inv hp]

/-- Differentiating the inverse identity yields the height-frame constraints
at every target point, rather than at just the chart center. -/
theorem height_fderiv_symm (p : JointSpace) (hp : p ∈ c.chart.target) (v : JointSpace) :
    fderiv ℝ (fun y : JointSpace => h y) (c.chart.symm p)
      (fderiv ℝ c.chart.symm p v) = v 0 := by
  have hf := (c.contDiff_height.contDiffAt
    (c.chart.open_source.mem_nhds (c.chart.map_target hp))).differentiableAt (by norm_num)
  have hd := hf.hasFDerivAt.comp p (c.hasFDerivAt_symm p hp)
  have he : (fun q => h (c.chart.symm q)) =ᶠ[𝓝 p] (fun q : JointSpace => q 0) :=
    mem_of_superset (c.chart.open_target.mem_nhds hp) (fun q hq => c.height_symm q hq)
  have hD := (hd.congr_of_eventuallyEq he.symm).unique
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).hasFDerivAt
  exact congrArg (fun L : JointSpace →L[ℝ] ℝ => L v) hD

/-- Both derivatives are mutual inverses on the chart target. In particular,
shrinking has not left an unproved invertibility condition at nearby points. -/
theorem fderiv_comp_symm (p : JointSpace) (hp : p ∈ c.chart.target) :
    (fderiv ℝ c.chart (c.chart.symm p)).comp (fderiv ℝ c.chart.symm p) =
      ContinuousLinearMap.id ℝ JointSpace := by
  have hf := (c.contDiff.contDiffAt
    (c.chart.open_source.mem_nhds (c.chart.map_target hp))).differentiableAt (by norm_num)
  have hd := hf.hasFDerivAt.comp p (c.hasFDerivAt_symm p hp)
  have he : (fun q => c.chart (c.chart.symm q)) =ᶠ[𝓝 p] id :=
    c.chart.eventually_right_inverse hp
  exact (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id p)

/-- The inverse Jacobian never vanishes on the controlled target. -/
theorem det_fderiv_symm_ne_zero (p : JointSpace) (hp : p ∈ c.chart.target) :
    (fderiv ℝ c.chart.symm p).toLinearMap.det ≠ 0 := by
  have hcomp := congrArg (fun A : JointSpace →L[ℝ] JointSpace => A.toLinearMap.det)
    (c.fderiv_comp_symm p hp)
  change ((fderiv ℝ c.chart (c.chart.symm p)).toLinearMap.comp
    (fderiv ℝ c.chart.symm p).toLinearMap).det = (LinearMap.id : JointSpace →ₗ[ℝ] JointSpace).det at hcomp
  rw [LinearMap.det_comp, LinearMap.det_id] at hcomp
  exact right_ne_zero_of_mul_eq_one hcomp

/-- Tangential Gram factor in the fixed Euclidean parameter coordinates. -/
def sliceJacobian (p : JointSpace) : ℝ :=
  graphAreaJacobian
    (fderiv ℝ c.chart.symm p (EuclideanSpace.basisFun (Fin 3) ℝ 1))
    (fderiv ℝ c.chart.symm p (EuclideanSpace.basisFun (Fin 3) ℝ 2))

/-- The actual ambient determinant is the slice Gram factor divided by the
actual gradient norm. This is a consequence of `graph_coarea_frame_jacobian`. -/
theorem abs_det_fderiv_symm (p : JointSpace) (hp : p ∈ c.chart.target) :
    |(fderiv ℝ c.chart.symm p).toLinearMap.det| =
      c.sliceJacobian p / ‖graphGradient h (c.chart.symm p)‖ := by
  rw [joint_det_eq_frame]
  apply graph_coarea_frame_jacobian
  · simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply] using
      c.height_fderiv_symm p hp (EuclideanSpace.basisFun (Fin 3) ℝ 0)
  · simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply] using
      c.height_fderiv_symm p hp (EuclideanSpace.basisFun (Fin 3) ℝ 1)
  · simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply] using
      c.height_fderiv_symm p hp (EuclideanSpace.basisFun (Fin 3) ℝ 2)

/-- Signed local ambient change of variables, for every measurable target
subset. No positivity or integrability assumption on the test function is
hidden; the separate equivalence below checks absolute integrability. -/
theorem integral_symm_image (s : Set JointSpace) (hs : MeasurableSet s)
    (hst : s ⊆ c.chart.target) (f : JointSpace → ℝ) :
    (∫ x in c.chart.symm '' s, f x) =
      ∫ p in s, (c.sliceJacobian p / ‖graphGradient h (c.chart.symm p)‖) * f (c.chart.symm p) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun p hp => (c.hasFDerivAt_symm p (hst hp)).hasFDerivWithinAt)
    (c.chart.symm.injOn.mono hst)]
  apply setIntegral_congr_fun hs
  intro p hp
  change |(fderiv ℝ c.chart.symm p).toLinearMap.det| * f (c.chart.symm p) = _
  rw [c.abs_det_fderiv_symm p (hst hp)]

/-- Absolute integrability is preserved with the proved local Jacobian. -/
theorem integrableOn_symm_image_iff (s : Set JointSpace) (hs : MeasurableSet s)
    (hst : s ⊆ c.chart.target) (f : JointSpace → ℝ) :
    IntegrableOn f (c.chart.symm '' s) ↔
      IntegrableOn (fun p => (c.sliceJacobian p / ‖graphGradient h (c.chart.symm p)‖) *
        f (c.chart.symm p)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun p hp => (c.hasFDerivAt_symm p (hst hp)).hasFDerivWithinAt)
    (c.chart.symm.injOn.mono hst)]
  apply integrableOn_congr_fun _ hs
  intro p hp
  change |(fderiv ℝ c.chart.symm p).toLinearMap.det| * f (c.chart.symm p) = _
  rw [c.abs_det_fderiv_symm p (hst hp)]

/-- Weighted ambient Jacobian, also the local reciprocal-gradient slice
factor. Its continuity only needs the proved neighborhood inverse regularity. -/
def weightedJacobian (w : JointSpace → ℝ) (p : JointSpace) : ℝ :=
  w (c.chart.symm p) * |(fderiv ℝ c.chart.symm p).toLinearMap.det|

theorem continuousOn_weightedJacobian (w : JointSpace → ℝ) (hw : Continuous w) :
    ContinuousOn (c.weightedJacobian w) c.chart.target := by
  have hD : ContinuousOn (fderiv ℝ c.chart.symm) c.chart.target := by
    intro p hp
    exact ((c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  exact (hw.comp_continuousOn c.chart.symm.continuousOn).mul
    ((ContinuousLinearMap.continuous_det.comp_continuousOn hD).abs)

/-- Within a regular chart, every nonnegative-height point belongs to the
closed positive region. At height zero this follows by approaching from
positive chart heights; unrelated exterior zeros are not silently included. -/
theorem symm_mem_closedPositive (p : JointSpace) (hp : p ∈ c.chart.target)
    (hpos : 0 ≤ p 0) : c.chart.symm p ∈ graphClosedPositive h := by
  let u : ℕ → JointSpace := fun n => p + (1 / ((n : ℝ) + 1)) •
    EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hu : Tendsto u atTop (𝓝 p) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (EuclideanSpace.basisFun (Fin 3) ℝ 0))
  apply mem_closure_of_tendsto ((c.chart.symm.continuousAt hp).tendsto.comp hu)
  filter_upwards [hu.eventually (c.chart.open_target.mem_nhds hp)] with n hn
  change 0 < h (c.chart.symm (u n))
  rw [c.height_symm _ hn]
  have he : u n 0 = p 0 + 1 / ((n : ℝ) + 1) := by
    simp [u, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
  rw [he]
  positivity

end RegularHeightChart
end BoundaryDraft
