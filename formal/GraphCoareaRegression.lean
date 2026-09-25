import BoundaryDraft

/-!
Independent collar coarea contracts: the original spatial product measure,
canonical density, absolute integrability and measurability, both endpoints,
signed weights with no global-continuity hypothesis, and original ellipsoids.
Quartic critical-point and active-overlap tests extend their existing files.
-/

open BoundaryDraft MeasureTheory Set
open scoped Topology ENNReal
noncomputable section

-- No coarea premise, positivity of the test weight, or global noncriticality.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 δ) →
      IntegrableOn (fun x : Spatial => f (h x)) {x | 0 < h x ∧ h x < δ} ∧
      IntervalIntegrable (fun t => f t * graphHeightDensity h t) volume 0 δ ∧
      (∫ x : Spatial in {x | 0 < h x ∧ h x < δ}, f (h x)) =
        ∫ t in (0 : ℝ)..δ, f t * graphHeightDensity h t := by
  obtain ⟨δ, hδ, _, hc⟩ := hh.exists_collar_coarea
  exact ⟨δ, hδ, hc⟩

-- Fubini's joint measurability and absolute integrability, before interchanging.
example (h : Spatial → ℝ) (A : ControlledCollarAtlas h) (i : Fin A.count)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    AEStronglyMeasurable (fun p : ℝ × SurfacePlane => A.localTerm i p.1 p.2 * f p.1)
      (volume.restrict (Icc 0 A.width ×ˢ (A.charts i).disk)) ∧
    IntegrableOn (fun p : ℝ × SurfacePlane => ‖A.localTerm i p.1 p.2 * f p.1‖)
      (Icc 0 A.width ×ˢ (A.charts i).disk) :=
  ⟨(A.integrableOn_localTerm_mul i f hf).aestronglyMeasurable,
    (A.integrableOn_localTerm_mul i f hf).norm⟩

-- Absolute rather than just signed integrals are meaningful on both sides.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (A : ControlledCollarAtlas h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    IntegrableOn (fun x : Spatial => ‖f (h x)‖) {x | 0 < h x ∧ h x < A.width} ∧
    IntegrableOn (fun t => ‖f t * graphHeightDensity h t‖) (Icc 0 A.width) ∧
    AEStronglyMeasurable (fun t => f t * graphHeightDensity h t)
      (volume.restrict (Icc 0 A.width)) :=
  ⟨(A.integrableOn_openCollar_profile hh f hf).norm,
    (A.integrableOn_mul_graphHeightDensity hh f hf).norm,
    (A.integrableOn_mul_graphHeightDensity hh f hf).aestronglyMeasurable⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (A : ControlledCollarAtlas h)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    (∫ x : Spatial in {x | 0 < h x ∧ h x < A.width}, ‖f (h x)‖) =
      ∫ t in (0 : ℝ)..A.width, ‖f t‖ * graphHeightDensity h t :=
  A.integral_openCollar_profile hh _ hf.norm

-- Nullity is derived separately from Hausdorff finiteness, not from coarea.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (A : ControlledCollarAtlas h) :
    volume (graphLevel h 0) = 0 ∧ volume {x : Spatial | h x = A.width} = 0 ∧
    {x : JointSpace | 0 < h x ∧ h x < A.width} =ᶠ[ae volume] graphClosedCollar h A.width := by
  have hr := fun x (hx : x ∈ graphLevel h A.width) => A.noncritical x ⟨hx.1, hx.2.le⟩
  exact ⟨hh.volume_graphLevel_eq_zero 0 (fun x hx => hh.regular_zero x hx.1 hx.2),
    hh.volume_spatial_level_eq_zero A.width A.width_pos hr,
    hh.ae_openCollar_eq_closedCollar A.width hr⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (A : ControlledCollarAtlas h)
    (f : Spatial → ℝ) :
    (∫ x in {x | 0 < h x ∧ h x < A.width}, f x) =
      ∫ x in {x | 0 < h x ∧ h x ≤ A.width}, f x :=
  hh.integral_collar_eq_closed_endpoint A.width A.width_pos
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩) f

-- The raw zero level can have infinite volume. The endpoint API correctly
-- removes only the joint inside the cap closure.
example : volume {x : JointSpace | (fun _ : Spatial => (0 : ℝ)) x = 0} = ∞ ∧
    volume (graphLevel (fun _ : Spatial => (0 : ℝ)) 0) = 0 := by
  simp [graphJoint, graphClosedPositive]

namespace GraphCoareaRegression

/-- Negative on the collar and discontinuous at its left endpoint as an
ambient function. Only continuity relative to the collar is required. -/
def signedCollarWeight (δ t : ℝ) : ℝ := if t ∈ Icc 0 δ then -(1 + t ^ 2) else 7

theorem continuousOn_signedCollarWeight (δ : ℝ) :
    ContinuousOn (signedCollarWeight δ) (Icc 0 δ) := by
  apply (show ContinuousOn (fun t : ℝ => -(1 + t ^ 2)) (Icc 0 δ) by fun_prop).congr
  intro t ht
  simp [signedCollarWeight, ht]

theorem signedCollarWeight_not_continuousAt (δ : ℝ) (hδ : 0 < δ) :
    ¬ ContinuousAt (signedCollarWeight δ) 0 := by
  intro hc
  have hl : Filter.Tendsto (signedCollarWeight δ) (𝓝[<] 0) (𝓝 7) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [signedCollarWeight, not_le_of_gt (show t < 0 from ht)]
  have he := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hl
  norm_num [signedCollarWeight, hδ.le] at he

theorem signed_collar_coarea (h : Spatial → ℝ) (hh : AdmissibleGraphCap h)
    (A : ControlledCollarAtlas h) :
    (∫ x : Spatial in {x | 0 < h x ∧ h x < A.width}, signedCollarWeight A.width (h x)) =
      ∫ t in (0 : ℝ)..A.width, signedCollarWeight A.width t * graphHeightDensity h t :=
  A.integral_openCollar_profile hh _ (continuousOn_signedCollarWeight A.width)

end GraphCoareaRegression

-- Original unequal-axis hypotheses, not stronger graph-cap hypotheses.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun x : Spatial => planeKernel ρ (ellipsoidProfile a b x))
        {x | 0 < ellipsoidProfile a b x ∧ ellipsoidProfile a b x < δ} ∧
      IntervalIntegrable (fun t => planeKernel ρ t * graphHeightDensity (ellipsoidProfile a b) t)
        volume 0 δ ∧
      (∫ x : Spatial in {x | 0 < ellipsoidProfile a b x ∧ ellipsoidProfile a b x < δ},
        planeKernel ρ (ellipsoidProfile a b x)) =
        ∫ t in (0 : ℝ)..δ, planeKernel ρ t * graphHeightDensity (ellipsoidProfile a b) t :=
  (ellipsoid_admissible a b ha hb).exists_planeKernel_collar_coarea

-- The finite-density action now uses canonical coarea only in the collar.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (A : ControlledCollarAtlas h)
    (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (graphCapRegion h) =
      (∫ t in (0 : ℝ)..A.width, planeKernel ρ t * graphHeightDensity h t) +
        ∫ x in {x | A.width ≤ h x}, planeKernel ρ (h x) :=
  A.continuumMean_eq_height_collar_add_remainder hh ρ hρ
