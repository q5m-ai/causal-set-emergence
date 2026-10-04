import BoundaryDraft.Pilot3SliceCharts

/-!
# Intrinsic Lorentzian joint area on every chart overlap

The canonical spatial one-measure is identified by the proved curve area law.
Its Lorentzian density is the actual tangent Gram factor of the lifted chart,
not Euclidean spacetime speed or an action coefficient. Restrictions agree as
measures on every Borel overlap, including overlaps of positive measure.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

theorem pilot3_withDensity_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {g : X → Y} (hg : MeasurableEmbedding g) (μ : Measure X) (w : Y → ℝ≥0∞) :
    (Measure.map g μ).withDensity w = Measure.map g (μ.withDensity (w ∘ g)) := by
  ext s hs
  rw [withDensity_apply _ hs, hg.restrict_map, hg.lintegral_map,
    Measure.map_apply hg.measurable hs, withDensity_apply _ (hg.measurable hs)]
  rfl

namespace Pilot3SliceChart
variable {h f : Pilot3Space → ℝ} (c : Pilot3SliceChart h)

def jointChart (f : Pilot3Space → ℝ) (u : ℝ) : Pilot3Spacetime := pilot3Lift f (c.slice 0 u)

def jointDensity (f : Pilot3Space → ℝ) (u : ℝ) : ℝ := pilot3GramDensity (deriv (c.jointChart f) u)

/-- The density is the Gram speed of the actual lifted chart derivative. -/
theorem jointDensity_eq (hf : SmoothPilot3 h f) (u : ℝ) (hu : u ∈ c.sliceDomain 0) :
    c.jointDensity f u = pilot3AreaDensity h f (c.slice 0 u) * pilot3CurveJacobian (c.scalarSlice 0) u := by
  have hlevel : (fun t => h (c.slice 0 t)) =ᶠ[𝓝 u] (fun _ => 0) :=
    mem_of_superset ((c.isOpen_sliceDomain 0).mem_nhds hu) (fun v hv => (c.slice_mem_joint v hv).2)
  change pilot3GramDensity (deriv (fun v => pilot3Lift f (c.slice 0 v)) u) = _
  rw [hf.chart_gramDensity (c.hasDerivAt_slice 0 u hu) (c.slice_mem_joint u hu) hlevel]
  congr 1
  exact (c.scalarSlice_jacobian 0 u hu).symm

theorem jointDensity_pos (hf : SmoothPilot3 h f) (u : ℝ) (hu : u ∈ c.sliceDomain 0) :
    0 < c.jointDensity f u := by
  rw [c.jointDensity_eq hf u hu]
  exact mul_pos (hf.areaDensity_pos _ (c.slice_mem_joint u hu)) (pilot3CurveJacobian_pos _ _)

theorem measurableEmbedding_jointChart (hf : SmoothPilot3 h f) : MeasurableEmbedding (c.jointChart f) :=
  hf.measurableEmbedding_lift.comp (c.measurableEmbedding_slice 0)

/-- The FIXED candidate joint measure has the intrinsic Lorentzian chart law. -/
theorem jointArea_chart (hf : SmoothPilot3 h f) (s : Set ℝ) (hs : MeasurableSet s)
    (hsD : s ⊆ c.sliceDomain 0) :
    (pilot3JointArea h f).restrict (c.jointChart f '' s) =
      Measure.map (c.jointChart f) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (c.jointDensity f u))) := by
  have him : MeasurableSet (c.slice 0 '' s) := (c.measurableEmbedding_slice 0).measurableSet_image.mpr hs
  have hpre : pilot3Lift f ⁻¹' (c.jointChart f '' s) = c.slice 0 '' s := by
    change pilot3Lift f ⁻¹' ((pilot3Lift f ∘ c.slice 0) '' s) = _
    rw [image_comp, hf.measurableEmbedding_lift.injective.preimage_image]
  have hsub : c.slice 0 '' s ⊆ pilot3SpatialJoint h := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_joint u (hsD hu)
  have hsp : (pilot3SurfaceMeasure h).restrict (c.slice 0 '' s) =
      Measure.map (c.slice 0) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (pilot3CurveJacobian (c.scalarSlice 0) u))) := by
    rw [pilot3SurfaceMeasure, Measure.restrict_restrict_of_subset hsub, c.hausdorff_slice_image 0 s hs]
  have hw : AEMeasurable (fun u => ENNReal.ofReal (pilot3AreaDensity h f (c.slice 0 u))) (volume.restrict s) := by
    have hc : ContinuousOn (fun u => pilot3AreaDensity h f (c.slice 0 u)) s :=
      hf.continuousOn_areaDensity.comp (c.continuous_slice 0).continuousOn (fun u hu => c.slice_mem_joint u (hsD hu))
    exact (hc.aestronglyMeasurable hs).aemeasurable.ennreal_ofReal
  rw [pilot3JointArea, hf.measurableEmbedding_lift.restrict_map, hpre, pilot3ProjectedArea,
    restrict_withDensity him, hsp, pilot3_withDensity_map (c.measurableEmbedding_slice 0)]
  simp only [Function.comp_def]
  rw [← withDensity_mul₀ (measurable_pilot3CurveJacobian (c.scalarSlice 0)).ennreal_ofReal.aemeasurable hw,
    Measure.map_map hf.measurableEmbedding_lift.measurable (c.measurableEmbedding_slice 0).measurable]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (pilot3CurveJacobian_pos (c.scalarSlice 0) u).le,
    c.jointDensity_eq hf u (hsD hu), mul_comm]

/-- Equality of restricted measures on EVERY measurable overlap, not merely
an equality of total areas or a pointwise Jacobian identity. -/
theorem jointArea_overlap (hf : SmoothPilot3 h f) (d : Pilot3SliceChart h) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hsD : s ⊆ c.sliceDomain 0) (htD : t ⊆ d.sliceDomain 0) :
    (Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))).restrict (d.jointChart f '' t) =
    (Measure.map (d.jointChart f) ((volume.restrict t).withDensity
      (fun u => ENNReal.ofReal (d.jointDensity f u)))).restrict (c.jointChart f '' s) := by
  rw [← c.jointArea_chart hf s hs hsD, ← d.jointArea_chart hf t ht htD, Measure.restrict_comm]
  exact (d.measurableEmbedding_jointChart hf).measurableSet_image.mpr ht

/-- The angular target remains the same fixed intrinsic measure, now with a
proved chart rule. No coefficient or asymptotic theorem is used. -/
theorem jointArea_chart_integral (hf : SmoothPilot3 h f) (s : Set ℝ) (hs : MeasurableSet s)
    (hsD : s ⊆ c.sliceDomain 0) (F : Pilot3Spacetime → ℝ) :
    (∫ p in c.jointChart f '' s, F p ∂pilot3JointArea h f) =
      ∫ u, F (c.jointChart f u) ∂((volume.restrict s).withDensity (fun u => ENNReal.ofReal (c.jointDensity f u))) := by
  rw [c.jointArea_chart hf s hs hsD, (c.measurableEmbedding_jointChart hf).integral_map]

end Pilot3SliceChart
end BoundaryDraft
