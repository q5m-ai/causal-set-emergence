import BoundaryDraft

/-!
Independent theorem contracts for linear area and variable-Jacobian graph
area. These tests do not assert collar coarea, ellipsoid measure compatibility,
or the still-open general graph-cap limit.
-/

open BoundaryDraft MeasureTheory Set Filter Metric
open scoped ENNReal Topology
noncomputable section

-- No measurability or finiteness premise is required for the linear image.
example (L : SurfacePlane →L[ℝ] ℝ) (s : Set SurfacePlane) :
    ENNReal.ofReal (Real.pi / 4) * μH[2] (surfaceGraphDerivative L '' s) =
      ENNReal.ofReal (Real.sqrt (1 + ‖L‖ ^ 2)) * volume s :=
  normalizedHausdorffTwo_surfaceGraphDerivative_image L s

-- The horizontal plane has exactly the previously proved planar normalization.
example (s : Set SurfacePlane) :
    normalizedHausdorffTwo (surfaceGraphDerivative (0 : SurfacePlane →L[ℝ] ℝ) '' s) = volume s := by
  rw [normalizedHausdorffTwo_surfaceGraphDerivative_image]
  simp

-- Both base directions contribute to the slope; a supremum norm is wrong here.
example (s : Set SurfacePlane) :
    normalizedHausdorffTwo (surfaceGraphDerivative
      (InnerProductSpace.toDual ℝ SurfacePlane ((WithLp.equiv 2 _).symm ![3, 4])) '' s) =
        ENNReal.ofReal (Real.sqrt 26) * volume s := by
  rw [normalizedHausdorffTwo_surfaceGraphDerivative_image,
    (InnerProductSpace.toDual ℝ SurfacePlane).norm_map]
  norm_num [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

-- Infinite measure is retained, rather than hidden behind a finite-set premise.
example (L : SurfacePlane →L[ℝ] ℝ) :
    normalizedHausdorffTwo (range (surfaceGraphDerivative L)) = ∞ := by
  rw [← image_univ, normalizedHausdorffTwo_surfaceGraphDerivative_image]
  simp [ENNReal.mul_top, ENNReal.ofReal_ne_zero_iff,
    Real.sqrt_pos.2 (show 0 < 1 + ‖L‖ ^ 2 by positivity)]

-- The full pullback contract uses the actual Fréchet derivative.
example (g : SurfacePlane → ℝ) (hg : ContDiff ℝ 1 g) :
    surfaceGraphPullbackMeasure g =
      volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2))) :=
  surfaceGraphPullbackMeasure_eq_withDensity hg

-- Absolute continuity and local finiteness are conclusions, not supplied fields.
example (g : SurfacePlane → ℝ) (hg : ContDiff ℝ 1 g) :
    IsLocallyFiniteMeasure (surfaceGraphPullbackMeasure g) ∧
      surfaceGraphPullbackMeasure g ≪ volume :=
  ⟨surfaceGraphPullbackMeasure_locallyFinite hg, surfaceGraphPullbackMeasure_absolutelyContinuous hg⟩

-- Every-point density, not merely a formal appeal to density uniqueness.
example (g : SurfacePlane → ℝ) (hg : ContDiff ℝ 1 g) (x : SurfacePlane) :
    Tendsto (fun r => surfaceGraphPullbackMeasure g (closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)))) :=
  surfaceGraphPullbackMeasure_tendsto_closedBall_ratio hg.continuous univ isOpen_univ
    hg.contDiffOn x (mem_univ x)

-- Nonlinear paraboloid: a variable Jacobian, not a linear-only theorem.
example : surfaceGraphPullbackMeasure (fun x : SurfacePlane => x 0 ^ 2 + x 1 ^ 2) =
    volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt
      (1 + ‖fderiv ℝ (fun y : SurfacePlane => y 0 ^ 2 + y 1 ^ 2) x‖ ^ 2))) := by
  apply surfaceGraphPullbackMeasure_eq_withDensity
  have hi (i : Fin 2) : ContDiff ℝ 1 (fun x : SurfacePlane => x i) :=
    (contDiff_apply ℝ ℝ i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).contDiff
  exact ((hi 0).pow 2).add ((hi 1).pow 2)

-- Open-domain regularity suffices; no global C¹ hypothesis is present.
example (g : SurfacePlane → ℝ) (hg : Continuous g) (U : Set SurfacePlane)
    (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) :
    (surfaceGraphPullbackMeasure g).restrict U =
      (volume.restrict U).withDensity
        (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2))) :=
  surfaceGraphPullbackMeasure_restrict_eq_withDensity hg U hU hgU

-- A graph with a crease outside the regular domain: global C¹ is not needed.
example :
    (surfaceGraphPullbackMeasure (fun x : SurfacePlane => |x 0|)).restrict {x | 0 < x 0} =
      (volume.restrict {x : SurfacePlane | 0 < x 0}).withDensity
        (fun x => ENNReal.ofReal (Real.sqrt
          (1 + ‖fderiv ℝ (fun y : SurfacePlane => |y 0|) x‖ ^ 2))) := by
  have hp : ContDiff ℝ 1 (fun x : SurfacePlane => x 0) :=
    (contDiff_apply ℝ ℝ 0).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).contDiff
  apply surfaceGraphPullbackMeasure_restrict_eq_withDensity hp.continuous.abs _
    (isOpen_lt continuous_const hp.continuous)
  apply hp.contDiffOn.congr
  intro x hx
  exact abs_of_pos hx

-- Signed integral and absolute integrability identities are separately checked.
example (g : SurfacePlane → ℝ) (hg : ContDiff ℝ 1 g) (f : JointSpace → ℝ)
    (s : Set SurfacePlane) (hs : MeasurableSet s) :
    (∫ y in surfaceGraph g '' s, f y ∂normalizedHausdorffTwo) =
      ∫ x in s, Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) * f (surfaceGraph g x) :=
  integral_normalizedHausdorffTwo_surfaceGraph hg f s hs

example (g : SurfacePlane → ℝ) (hg : ContDiff ℝ 1 g) (f : JointSpace → ℝ)
    (s : Set SurfacePlane) (hs : MeasurableSet s) :
    IntegrableOn f (surfaceGraph g '' s) normalizedHausdorffTwo ↔
      IntegrableOn (fun x => Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) * f (surfaceGraph g x)) s :=
  integrable_normalizedHausdorffTwo_surfaceGraph_iff hg f s hs
