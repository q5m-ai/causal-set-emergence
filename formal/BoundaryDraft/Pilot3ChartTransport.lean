import BoundaryDraft.Pilot3HeightCharts
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Actual planar coarea Jacobian and chart volume transport

The derivative constraints come from differentiating the constructed inverse.
The ambient determinant equals tangent speed divided by gradient norm. The
volume change of variables is then the ordinary same-dimension Jacobian law;
the separately proved Hausdorff curve formula supplies surface transport.
-/

open MeasureTheory Set Filter
open scoped Topology Matrix ContDiff
noncomputable section
namespace BoundaryDraft

private theorem pilot3_cofactor_resolution (g z v : Pilot3Space) :
    inner (𝕜 := ℝ) g z • v - inner (𝕜 := ℝ) g v • z =
      Matrix.det ![(z : Fin 2 → ℝ), (v : Fin 2 → ℝ)] •
        (WithLp.equiv 2 _).symm ![-g 1, g 0] := by
  ext i
  fin_cases i <;>
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- One-dimensional tangential speed, with normalization one. -/
theorem pilot3_coarea_frame_jacobian (h : Pilot3Space → ℝ) (x z v : Pilot3Space)
    (hz : fderiv ℝ h x z = 1) (hv : fderiv ℝ h x v = 0) :
    |Matrix.det ![(z : Fin 2 → ℝ), (v : Fin 2 → ℝ)]| = ‖v‖ / ‖pilot3Gradient h x‖ := by
  rw [pilot3_differential_eq_inner] at hz hv
  have he := pilot3_cofactor_resolution (pilot3Gradient h x) z v
  simp only [hz, hv, one_smul, zero_smul, sub_zero] at he
  have hn : pilot3Gradient h x ≠ 0 := by intro hg; simp [hg] at hz
  have hn' := norm_ne_zero_iff.mpr hn
  have hrot : ‖((WithLp.equiv 2 _).symm ![-(pilot3Gradient h x) 1, (pilot3Gradient h x) 0] : Pilot3Space)‖ =
      ‖pilot3Gradient h x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, add_comm]
  apply (eq_div_iff hn').mpr
  have he' := congrArg norm he
  rw [norm_smul, Real.norm_eq_abs, hrot] at he'
  exact he'.symm

theorem pilot3_det_eq_frame (A : Pilot3Space →L[ℝ] Pilot3Space) :
    A.toLinearMap.det = Matrix.det
      ![(A (EuclideanSpace.basisFun (Fin 2) ℝ 0) : Fin 2 → ℝ),
        (A (EuclideanSpace.basisFun (Fin 2) ℝ 1) : Fin 2 → ℝ)] := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr]

namespace Pilot3HeightChart
variable {h : Pilot3Space → ℝ} (c : Pilot3HeightChart h)

theorem hasFDerivAt_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    HasFDerivAt c.chart.symm (fderiv ℝ c.chart.symm p) p :=
  (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt

theorem height_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) : h (c.chart.symm p) = p 0 := by
  rw [← c.height, c.chart.right_inv hp]

theorem height_fderiv_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) (v : Pilot3Space) :
    fderiv ℝ h (c.chart.symm p) (fderiv ℝ c.chart.symm p v) = v 0 := by
  have hf := (c.contDiff_height.contDiffAt
    (c.chart.open_source.mem_nhds (c.chart.map_target hp))).differentiableAt (by simp)
  have hd := hf.hasFDerivAt.comp p (c.hasFDerivAt_symm p hp)
  have he : (fun q => h (c.chart.symm q)) =ᶠ[𝓝 p] (fun q : Pilot3Space => q 0) :=
    mem_of_superset (c.chart.open_target.mem_nhds hp) (fun q hq => c.height_symm q hq)
  have hD := (hd.congr_of_eventuallyEq he.symm).unique
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  exact congrArg (fun L : Pilot3Space →L[ℝ] ℝ => L v) hD

theorem fderiv_comp_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    (fderiv ℝ c.chart (c.chart.symm p)).comp (fderiv ℝ c.chart.symm p) =
      ContinuousLinearMap.id ℝ Pilot3Space := by
  have hf := (c.contDiff.contDiffAt
    (c.chart.open_source.mem_nhds (c.chart.map_target hp))).differentiableAt (by simp)
  have hd := hf.hasFDerivAt.comp p (c.hasFDerivAt_symm p hp)
  have he : (fun q => c.chart (c.chart.symm q)) =ᶠ[𝓝 p] id := c.chart.eventually_right_inverse hp
  exact (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id p)

theorem det_fderiv_symm_ne_zero (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    (fderiv ℝ c.chart.symm p).toLinearMap.det ≠ 0 := by
  have he := congrArg (fun A : Pilot3Space →L[ℝ] Pilot3Space => A.toLinearMap.det) (c.fderiv_comp_symm p hp)
  change ((fderiv ℝ c.chart (c.chart.symm p)).toLinearMap.comp
    (fderiv ℝ c.chart.symm p).toLinearMap).det = (LinearMap.id : Pilot3Space →ₗ[ℝ] Pilot3Space).det at he
  rw [LinearMap.det_comp, LinearMap.det_id] at he
  exact right_ne_zero_of_mul_eq_one he

def sliceJacobian (p : Pilot3Space) : ℝ := ‖fderiv ℝ c.chart.symm p (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖

theorem abs_det_fderiv_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    |(fderiv ℝ c.chart.symm p).toLinearMap.det| = c.sliceJacobian p / ‖pilot3Gradient h (c.chart.symm p)‖ := by
  rw [pilot3_det_eq_frame]
  apply pilot3_coarea_frame_jacobian
  · simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply] using
      c.height_fderiv_symm p hp (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  · simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply] using
      c.height_fderiv_symm p hp (EuclideanSpace.basisFun (Fin 2) ℝ 1)

theorem integral_symm_image (s : Set Pilot3Space) (hs : MeasurableSet s)
    (hst : s ⊆ c.chart.target) (F : Pilot3Space → ℝ) :
    (∫ x in c.chart.symm '' s, F x) =
      ∫ p in s, (c.sliceJacobian p / ‖pilot3Gradient h (c.chart.symm p)‖) * F (c.chart.symm p) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun p hp => (c.hasFDerivAt_symm p (hst hp)).hasFDerivWithinAt) (c.chart.symm.injOn.mono hst)]
  apply setIntegral_congr_fun hs
  intro p hp
  change |(fderiv ℝ c.chart.symm p).toLinearMap.det| * F (c.chart.symm p) = _
  rw [c.abs_det_fderiv_symm p (hst hp)]

theorem integrableOn_symm_image_iff (s : Set Pilot3Space) (hs : MeasurableSet s)
    (hst : s ⊆ c.chart.target) (F : Pilot3Space → ℝ) :
    IntegrableOn F (c.chart.symm '' s) ↔
      IntegrableOn (fun p => (c.sliceJacobian p / ‖pilot3Gradient h (c.chart.symm p)‖) * F (c.chart.symm p)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun p hp => (c.hasFDerivAt_symm p (hst hp)).hasFDerivWithinAt) (c.chart.symm.injOn.mono hst)]
  apply integrableOn_congr_fun _ hs
  intro p hp
  change |(fderiv ℝ c.chart.symm p).toLinearMap.det| * F (c.chart.symm p) = _
  rw [c.abs_det_fderiv_symm p (hst hp)]

def weightedJacobian (w : Pilot3Space → ℝ) (p : Pilot3Space) : ℝ :=
  w (c.chart.symm p) * |(fderiv ℝ c.chart.symm p).toLinearMap.det|

theorem continuousOn_weightedJacobian (w : Pilot3Space → ℝ) (hw : Continuous w) :
    ContinuousOn (c.weightedJacobian w) c.chart.target := by
  have hD : ContinuousOn (fderiv ℝ c.chart.symm) c.chart.target := fun p hp =>
    ((c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  exact (hw.comp_continuousOn c.chart.symm.continuousOn).mul
    ((ContinuousLinearMap.continuous_det.comp_continuousOn hD).abs)

theorem symm_mem_closedPositive (p : Pilot3Space) (hp : p ∈ c.chart.target) (hpos : 0 ≤ p 0) :
    c.chart.symm p ∈ pilot3ClosedPositive h := by
  let u : ℕ → Pilot3Space := fun n => p + (1 / ((n : ℝ) + 1)) • EuclideanSpace.basisFun (Fin 2) ℝ 0
  have hu : Tendsto u atTop (𝓝 p) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 0))
  apply mem_closure_of_tendsto ((c.chart.symm.continuousAt hp).tendsto.comp hu)
  filter_upwards [hu.eventually (c.chart.open_target.mem_nhds hp)] with n hn
  change 0 < h (c.chart.symm (u n))
  rw [c.height_symm _ hn]
  have he : u n 0 = p 0 + 1 / ((n : ℝ) + 1) := by
    simp [u, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
  rw [he]
  positivity

end Pilot3HeightChart
end BoundaryDraft
