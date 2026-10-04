import BoundaryDraft.Pilot3AtlasRepresentation

/-!
# Finite-atlas gluing and atlas independence of the intrinsic joint measure

The local measures use actual lifted-curve Gram speed, then the constructed
partition weight. Their finite sum is the original canonical joint measure.
This handles positive-measure chart overlaps and proves atlas independence
as an equality of measures, not merely equality of one chosen observable.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Manifold
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

theorem SmoothPilot3.ae_jointArea_mem_joint {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∀ᵐ p ∂pilot3JointArea h f, p ∈ pilot3Joint h f := by
  rw [pilot3JointArea, hf.measurableEmbedding_lift.ae_map_iff]
  have he : ∀ᵐ x ∂pilot3ProjectedArea h f, x ∈ pilot3SpatialJoint h := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact ae_restrict_mem hf.toPilot3RegularHeight.measurableSet_joint
  filter_upwards [he] with x hx
  exact ⟨x, hx, rfl⟩

namespace Pilot3CollarAtlas
variable {h f : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

/-- Both factors are explicit: intrinsic curve speed and partition weight. -/
def localJointMeasure (f : Pilot3Space → ℝ) (i : Fin A.count) : Measure Pilot3Spacetime :=
  Measure.map ((A.charts i).jointChart f)
    (((volume.restrict (A.charts i).disk).withDensity
      (fun u => ENNReal.ofReal ((A.charts i).jointDensity f u))).withDensity
        (fun u => ENNReal.ofReal (A.weights i ((A.charts i).slice 0 u))))

theorem localJointMeasure_eq (hf : SmoothPilot3 h f) (i : Fin A.count) :
    A.localJointMeasure f i = (pilot3JointArea h f).withDensity (fun p => ENNReal.ofReal (A.weights i p.2)) := by
  let c := A.charts i
  have ht : (0 : ℝ) ∈ Icc (-c.width) c.width := ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩
  have hS : MeasurableSet (c.jointChart f '' c.disk) :=
    (c.measurableEmbedding_jointChart hf).measurableSet_image.mpr measurableSet_ball
  have hloc : (pilot3JointArea h f).withDensity (fun p => ENNReal.ofReal (A.weights i p.2)) =
      ((pilot3JointArea h f).restrict (c.jointChart f '' c.disk)).withDensity
        (fun p => ENNReal.ofReal (A.weights i p.2)) := by
    rw [← withDensity_indicator hS]
    apply withDensity_congr_ae
    filter_upwards [hf.ae_jointArea_mem_joint] with p hp
    by_cases hpS : p ∈ c.jointChart f '' c.disk
    · simp only [indicator_of_mem hpS]
    · rw [indicator_of_not_mem hpS]
      obtain ⟨x, hx, rfl⟩ := hp
      have hxP : x ∉ c.patch := by
        intro hxP
        obtain ⟨u, hu, he⟩ := c.mem_slice_image_of_mem_patch x hxP 0 hx.2
        exact hpS ⟨u, hu, congrArg (pilot3Lift f) he⟩
      change ENNReal.ofReal (A.weights i x) = 0
      rw [A.weight_eq_zero_of_not_mem_patch i x hxP, ENNReal.ofReal_zero]
  rw [hloc, c.jointArea_chart hf c.disk measurableSet_ball (c.disk_subset_sliceDomain 0 ht),
    pilot3_withDensity_map (c.measurableEmbedding_jointChart hf)]
  rfl

/-- Canonical finite gluing, derived for any constructed collar atlas. -/
theorem sum_localJointMeasure (hf : SmoothPilot3 h f) :
    (∑ i, A.localJointMeasure f i) = pilot3JointArea h f := by
  let W := fun i (p : Pilot3Spacetime) => ENNReal.ofReal (A.weights i p.2)
  have hW (i : Fin A.count) : Measurable (W i) :=
    ((A.weights i).contMDiff.continuous.measurable.comp measurable_snd).ennreal_ofReal
  have hsum : (∑ i, (pilot3JointArea h f).withDensity (W i)) =
      (pilot3JointArea h f).withDensity (∑ i, W i) := by
    simpa only [tsum_fintype, Measure.sum_fintype] using (withDensity_tsum (μ := pilot3JointArea h f) hW).symm
  calc
    _ = ∑ i, (pilot3JointArea h f).withDensity (W i) := Finset.sum_congr rfl (fun i _ => A.localJointMeasure_eq hf i)
    _ = (pilot3JointArea h f).withDensity (∑ i, W i) := hsum
    _ = (pilot3JointArea h f).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [hf.ae_jointArea_mem_joint] with p hp
      obtain ⟨x, hx, rfl⟩ := hp
      simp only [Finset.sum_apply, Pi.one_apply]
      change (∑ i, ENNReal.ofReal (A.weights i x)) = 1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => A.weights.nonneg i x),
        A.sum_weights x ⟨hx.1, hx.2.le.trans A.width_pos.le⟩, ENNReal.ofReal_one]
    _ = _ := withDensity_one

/-- Independence includes arbitrary refinements and positive-measure overlaps. -/
theorem jointAtlas_independent (hf : SmoothPilot3 h f) (B : Pilot3CollarAtlas h) :
    (∑ i, A.localJointMeasure f i) = ∑ j, B.localJointMeasure f j := by
  rw [A.sum_localJointMeasure hf, B.sum_localJointMeasure hf]

theorem localJointMeasure_le (hf : SmoothPilot3 h f) (i : Fin A.count) :
    A.localJointMeasure f i ≤ pilot3JointArea h f := by
  rw [A.localJointMeasure_eq hf i]
  calc
    _ ≤ (pilot3JointArea h f).withDensity (fun _ => 1) :=
      withDensity_mono (Eventually.of_forall fun p => by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (A.weights.le_one i p.2))
    _ = _ := by simp

theorem integral_jointArea_eq_sum (hf : SmoothPilot3 h f) (F : Pilot3Spacetime → ℝ)
    (hF : Integrable F (pilot3JointArea h f)) :
    (∫ p, F p ∂pilot3JointArea h f) = ∑ i, ∫ p, F p ∂A.localJointMeasure f i := by
  rw [← A.sum_localJointMeasure hf, integral_finset_sum_measure]
  intro i _
  exact hF.mono_measure (A.localJointMeasure_le hf i)

end Pilot3CollarAtlas
end BoundaryDraft
