import BoundaryDraft.Pilot3Surface
import BoundaryDraft.Pilot3Tubes
import BoundaryDraft.Pilot3JointAtlas
import BoundaryDraft.Pilot3Divergence

/-! Standalone #79 contracts. The canonical intrinsic target, chart measures,
finite-atlas gluing, spatial coarea and divergence are independent of the action.
No short producer, coefficient identification or pilot action limit is asserted. -/

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

-- T5 is an exact signed spatial decomposition, not the short analytic limit.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (τ : ℝ) (b : Pilot3Space) (hc : ‖b‖ ≤ τ) :
    pilot3WeightedOverlap h f w (τ, b) =
      (∫ x in {x | 0 < h x}, w x * h x) -
      (∫ x in {x | 0 < h x}, w x * (τ - f (x + b) + f x)) +
      ∫ x in {x | 0 < h x}, w x * max 0 (τ - f (x + b) + f x - h x) :=
  hf.weightedOverlap_eq_bulk_add_correction w hw (τ, b) hc

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hc : ‖z.2‖ ≤ z.1) :
    pilot3WeightedOverlap h f w z =
      ∫ x in {x | 0 < h x}, w x * max 0 (h x - (z.1 - f (x + z.2) + f x)) :=
  hf.weightedOverlap_eq_shortGap w hw z hc

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (w₁ w₂ : Pilot3Space → ℝ)
    (hw₁ : ContinuousOn w₁ (pilot3ClosedPositive h)) (hw₂ : ContinuousOn w₂ (pilot3ClosedPositive h))
    (z : Pilot3Spacetime) :
    pilot3WeightedOverlap h f (fun x => w₁ x + w₂ x) z =
      pilot3WeightedOverlap h f w₁ z + pilot3WeightedOverlap h f w₂ z := hf.weightedOverlap_add w₁ w₂ hw₁ hw₂ z

-- The exact moving-collar set, with no boundary mass at contact.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hc : ‖z.2‖ ≤ z.1) :
    pilot3WeightedOverlap h f w z = pilot3WeightedOverlap h f w 0 -
      (∫ x in {x | 0 < h x}, w x * (z.1 - f (x + z.2) + f x)) +
      ∫ x in {x | 0 < h x ∧ h x < z.1 - f (x + z.2) + f x},
        w x * (z.1 - f (x + z.2) + f x - h x) := hf.weightedOverlap_eq_bulk_add_collar w hw z hc

-- The same short tube contains every component and the entire small segment.
example {h : Pilot3Space → ℝ} {ε : ℝ} {x b : Pilot3Space}
    (hx : x ∈ closure {x | 0 < h x}) (hb : ‖b‖ ≤ ε) {t : ℝ} (ht : t ∈ Icc 0 1) :
    x + t • b ∈ pilot3TranslationTube h ε := pilot3_segment_mem_translationTube hx hb ht

open scoped ContDiff

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) : ∃ ε : ℝ, ∃ U : Set Pilot3Space,
    0 < ε ∧ IsOpen U ∧ pilot3TranslationTube h ε ⊆ U ∧
      ContDiffOn ℝ ∞ h U ∧ ContDiffOn ℝ ∞ f U := hf.exists_smooth_translationTube

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) : ∃ ε : ℝ, 0 < ε ∧
    (∀ x ∈ pilot3TranslationTube h ε, ContDiffAt ℝ ∞ h x ∧ ContDiffAt ℝ ∞ f x) ∧
    ∀ n : ℕ, ∃ Bh Bf : ℝ, 0 ≤ Bh ∧ 0 ≤ Bf ∧
      ∀ x ∈ pilot3TranslationTube h ε,
        ‖iteratedFDeriv ℝ n h x‖ ≤ Bh ∧ ‖iteratedFDeriv ℝ n f x‖ ≤ Bf :=
  hf.exists_translationTube_derivative_bounds

-- This is equality of fixed measures on every Borel chart subset.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (c : Pilot3SliceChart h)
    (s : Set ℝ) (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain 0) :
    (pilot3JointArea h f).restrict (c.jointChart f '' s) =
      Measure.map (c.jointChart f) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (pilot3GramDensity (deriv (c.jointChart f) u)))) :=
  c.jointArea_chart hf s hs hsD

-- Positive-measure overlaps agree, without a disjointness premise.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (c d : Pilot3SliceChart h)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsD : s ⊆ c.sliceDomain 0) (htD : t ⊆ d.sliceDomain 0) :
    (Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))).restrict (d.jointChart f '' t) =
    (Measure.map (d.jointChart f) ((volume.restrict t).withDensity
      (fun u => ENNReal.ofReal (d.jointDensity f u)))).restrict (c.jointChart f '' s) :=
  c.jointArea_overlap hf d s t hs ht hsD htD

-- Both integrability statements accompany the signed, normalized coarea law.
example {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h) (A : Pilot3CollarAtlas h)
    (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun x => g (h x) * w x) {x | 0 < h x ∧ h x < A.width} ∧
    IntervalIntegrable (fun t => g t * pilot3WeightedHeightDensity h w t) volume 0 A.width ∧
    (∫ x in {x | 0 < h x ∧ h x < A.width}, g (h x) * w x) =
      ∫ t in (0 : ℝ)..A.width, g t * pilot3WeightedHeightDensity h w t :=
  ⟨A.integrableOn_openCollar_weighted hh w hw g hg,
    A.intervalIntegrable_weightedHeightDensity hh w hw g hg, A.integral_openCollar_weighted hh w hw g hg⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    IntegrableOn (pilot3Laplacian f) {x | 0 < h x} ∧
    Integrable (fun x => inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x) /
      ‖pilot3Gradient h x‖) (pilot3SurfaceMeasure h) ∧
    (∫ x in {x | 0 < h x}, pilot3Laplacian f x) =
      -(∫ x, inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x) /
        ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) :=
  ⟨hf.integrableOn_laplacian, hf.integrable_surface_flux, hf.spatial_divergence⟩

example {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) :
    Tendsto (pilot3WeightedHeightDensity h w) (𝓝[≥] 0)
      (𝓝 (∫ x, w x / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)) :=
  hh.tendsto_weightedHeightDensity_zero w hw
