import BoundaryDraft.Pilot3Surface

/-! Standalone #79 contracts. The canonical candidate target and Gram algebra
are independent of the action. No short producer, coefficient identification,
Hausdorff chart area formula or coarea theorem is asserted by this regression. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

example (h f : Pilot3Space → ℝ) :
    pilot3BoundaryIntegral h f =
      ∫ x, pilot3Cosh h f x / Real.sqrt (pilot3Cosh h f x ^ 2 - 1)
        ∂((μH[1] : Measure Pilot3Space).restrict
          (closure {x | 0 < h x} ∩ {x | h x = 0})).withDensity
            (fun x => ENNReal.ofReal (Real.sqrt (1 -
              ‖pilot3Gradient f x - inner (𝕜 := ℝ) (pilot3Gradient f x)
                (‖pilot3Gradient h x‖⁻¹ • pilot3Gradient h x) •
                  (‖pilot3Gradient h x‖⁻¹ • pilot3Gradient h x)‖ ^ 2))) := rfl

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    IsFiniteMeasure (pilot3ProjectedArea h f) ∧ IsFiniteMeasure (pilot3JointArea h f) ∧
      Integrable (pilot3Weight h f) (pilot3ProjectedArea h f) :=
  ⟨hf.finite_projectedArea, hf.finite_jointArea, hf.integrable_weight⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    pilot3BoundaryIntegral h f = ∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f :=
  hf.boundaryIntegral_eq_joint

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (x : Pilot3Space)
    (hx : x ∈ pilot3SpatialJoint h) :
    1 < pilot3Cosh h f x ∧ 0 < pilot3Angle h f x ∧ 0 < pilot3AreaDensity h f x :=
  ⟨hf.cosh_gt_one x hx, (hf.angle_identities x hx).1, hf.areaDensity_pos x hx⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (x v : Pilot3Space)
    (hx : x ∈ pilot3SpatialJoint h) (hv : fderiv ℝ h x v = 0) :
    Real.sqrt (-dimensionMinkowski 2 (fderiv ℝ f x v, v) (fderiv ℝ f x v, v)) =
      pilot3AreaDensity h f x * ‖v‖ := hf.gramDensity x hx v hv

example (a : ℝ) (v : Pilot3Spacetime) :
    pilot3GramDensity (a • v) = |a| * pilot3GramDensity v := pilot3GramDensity_smul a v

-- Orientation-reversing tangent coordinates do not reverse area.
example (v : Pilot3Spacetime) : pilot3GramDensity ((-1 : ℝ) • v) = pilot3GramDensity v := by
  simpa using pilot3GramDensity_smul (-1) v

example {h : Pilot3Space → ℝ} (hh : SmoothPilot3 h (fun _ => 0)) :
    pilot3ProjectedArea h (fun _ => 0) = (μH[1] : Measure Pilot3Space).restrict (pilot3SpatialJoint h) ∧
    pilot3BoundaryIntegral h (fun _ => 0) =
      ∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h :=
  ⟨pilot3ProjectedArea_planar h, pilot3BoundaryIntegral_planar hh⟩

-- Goals are still propositions, not proofs of the requested asymptotics.
example : Pilot3DeterministicGoal ↔ ∀ h f, SmoothPilot3 h f →
    Tendsto (fun ρ => dimensionWeightedAction 2 (dimensionPointCoefficient 3)
      (dimensionPairCoefficient 3) (dimensionIntervalCoefficient 3) ρ (pilot3Region h f) (fun _ => 1))
      atTop (𝓝 (pilot3BoundaryIntegral h f)) := Iff.rfl

example : Pilot3ExpectedGoal ↔ Pilot3DeterministicGoal := pilot3ExpectedGoal_iff

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (F : Pilot3Spacetime → ℝ)
    (hF : Continuous F) : (∫ p in pilot3Region h f, F p) =
      ∫ x in {x | 0 < h x}, ∫ t in Ioo (f x - h x) (f x), F (t, x) := hf.integral_region F hF
