import BoundaryDraft.ThinTorusLifts

/-!
# Geometric volume of the actual thin-torus interval

Centered fundamental cubes are used as measure-transport domains, not as the
region or as a same-chart restriction on either endpoint.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft
namespace CompactTorus

variable (L : ℝ) [Fact (0 < L)]

/-- Cartesian coordinates with their ordinary product Lebesgue measure. -/
def tripleCoordinates : DimensionSpatial 3 ≃ᵐ ℝ × ℝ × ℝ :=
  (EuclideanSpace.measurableEquiv (Fin 3)).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow))

omit [Fact (0 < L)] in
theorem tripleCoordinates_apply (v : DimensionSpatial 3) :
    tripleCoordinates v = (v 0, v 1, v 2) := rfl

theorem tripleCoordinates_volume : MeasurePreserving tripleCoordinates volume
    (volume.prod (volume.prod volume)) := by
  exact ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)))

/-- Half-open fundamental cube centered on an arbitrary lift. -/
def coverCube (a : DimensionSpatial 3) : Set (DimensionSpatial 3) :=
  {v | ∀ i, v i ∈ Ico (a i - L / 2) (a i - L / 2 + L)}

omit [Fact (0 < L)] in
theorem measurableSet_coverCube (a : DimensionSpatial 3) : MeasurableSet (coverCube L a) := by
  simp only [coverCube, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Ico.preimage (by fun_prop : Measurable (fun v : DimensionSpatial 3 => v i))

omit [Fact (0 < L)] in
theorem coverCube_coordinates (a : DimensionSpatial 3) : coverCube L a =
    tripleCoordinates ⁻¹' (Ico (a 0 - L / 2) (a 0 - L / 2 + L) ×ˢ
      (Ico (a 1 - L / 2) (a 1 - L / 2 + L) ×ˢ
        Ico (a 2 - L / 2) (a 2 - L / 2 + L))) := by
  ext v
  simp [coverCube, Fin.forall_fin_succ, tripleCoordinates_apply]

theorem coverCube_injective (a : DimensionSpatial 3) : InjOn (cover L) (coverCube L a) := by
  intro u hu v hv he
  apply PiLp.ext
  intro i
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (hu i) (hv i)).mp
  fin_cases i
  · exact congrArg Prod.fst he
  · exact congrArg (fun q : Space L => q.2.1) he
  · exact congrArg (fun q : Space L => q.2.2) he

omit [Fact (0 < L)] in
theorem closedBall_subset_coverCube (a : DimensionSpatial 3) {R : ℝ} (hR : 2 * R < L) :
    Metric.closedBall a R ⊆ coverCube L a := by
  intro v hv i
  have hv' : ‖v - a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hi := (PiLp.norm_apply_le (v - a) i).trans hv'
  simp only [PiLp.sub_apply, Real.norm_eq_abs, abs_le] at hi
  constructor <;> linarith

/-- Quotient volume is precisely Lebesgue volume on ANY fundamental cube. -/
theorem cover_measurePreserving (a : DimensionSpatial 3) :
    MeasurePreserving (cover L) (volume.restrict (coverCube L a)) (spatialVolume L) := by
  have hc (i : Fin 3) : MeasurePreserving (fun x : ℝ => (x : AddCircle L))
      (volume.restrict (Ico (a i - L / 2) (a i - L / 2 + L))) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    exact AddCircle.measurePreserving_mk L (a i - L / 2)
  have ht := tripleCoordinates_volume.restrict_preimage
    ((measurableSet_Ico.prod (measurableSet_Ico.prod measurableSet_Ico)) :
      MeasurableSet (Ico (a 0 - L / 2) (a 0 - L / 2 + L) ×ˢ
        (Ico (a 1 - L / 2) (a 1 - L / 2 + L) ×ˢ
          Ico (a 2 - L / 2) (a 2 - L / 2 + L))))
  rw [← coverCube_coordinates, ← Measure.prod_restrict, ← Measure.prod_restrict] at ht
  exact ((hc 0).prod ((hc 1).prod (hc 2))).comp ht

theorem spacetimeCover_measurePreserving (a : DimensionSpatial 3) :
    MeasurePreserving (spacetimeCover L)
      (volume.restrict (univ ×ˢ coverCube L a)) (volume.prod (spatialVolume L)) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod (cover_measurePreserving L a)

theorem interval_preimage_cube {x y : DimensionSpacetime 3}
    (hτ : 2 * (y.1 - x.1) < L) (hxy : y ∈ dimensionCausalFuture x) :
    spacetimeCover L ⁻¹' Ultrastatic.closedInterval (spatialDistance L)
      (spacetimeCover L x) (spacetimeCover L y) ∩ (univ ×ˢ coverCube L x.2) =
      dimensionCausalInterval x y := by
  have hs : dimensionCausalInterval x y ⊆ univ ×ˢ coverCube L x.2 := by
    intro z hz
    exact ⟨mem_univ _, closedBall_subset_coverCube L x.2 hτ
      (dimensionCausalInterval_subset_compact x y hz).2⟩
  rw [← interval_image L hτ hxy]
  apply Subset.antisymm
  · rintro z ⟨⟨v, hv, he⟩, hz⟩
    have heq : v = z := Prod.ext (congrArg (fun p : ℝ × Space L => p.1) he)
      (coverCube_injective L x.2 (hs hv).2 hz.2 (congrArg Prod.snd he))
    simpa only [heq] using hv
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, hs hz⟩

/-- Full ambient quotient diamond volume, including null and diagonal pairs. -/
theorem intervalVolume_lift {x y : DimensionSpacetime 3}
    (hτ : 2 * (y.1 - x.1) < L) (hxy : y ∈ dimensionCausalFuture x) :
    (volume.prod (spatialVolume L)) (Ultrastatic.closedInterval (spatialDistance L)
      (spacetimeCover L x) (spacetimeCover L y)) =
      ENNReal.ofReal (Real.pi / 24 * ((y.1 - x.1) ^ 2 - ‖y.2 - x.2‖ ^ 2) ^ 2) := by
  letI : BorelSpace (Space L) := inferInstance
  have hm : MeasurableSet (Ultrastatic.closedInterval (spatialDistance L)
      (spacetimeCover L x) (spacetimeCover L y)) :=
    (Ultrastatic.isClosed_interval (spatialDistance L) _ _).measurableSet
  rw [← (spacetimeCover_measurePreserving L x.2).measure_preimage hm.nullMeasurableSet,
    Measure.restrict_apply (hm.preimage (spacetimeCover_measurePreserving L x.2).measurable),
    interval_preimage_cube L hτ hxy, volume_dimensionCausalInterval (by decide : 0 < 3) x y hxy]
  norm_num [dimensionIntervalCoefficient_four, dimensionIntervalSq]

/-- The actual restricted exclusive interval in the quotient has the standard
four-dimensional volume. No interval-volume formula is an input. -/
theorem intervalVolume_thin {T : ℝ} (hT : 2 * T < L) {x y : ℝ × Space L}
    (hx : x ∈ slab L T) (hy : y ∈ slab L T) (hxy : (measuredOrder L).Rel x y) :
    slabVolume L T ((measuredOrder L).interval x y) = ENNReal.ofReal
      (Real.pi / 24 * ((y.1 - x.1) ^ 2 - (spatialDistance L).distance x.2 y.2 ^ 2) ^ 2) := by
  let a := centeredLift L x.2
  let b := a + centeredLift L (y.2 - x.2)
  have ha : cover L a = x.2 := cover_centeredLift L x.2
  have hb : cover L b = y.2 := by simp [b, ha]
  have hn : ‖b - a‖ = (spatialDistance L).distance x.2 y.2 := by
    rw [show b - a = centeredLift L (y.2 - x.2) by dsimp [b]; abel,
      norm_centeredLift, distance_sub]
  have hc : (y.1, b) ∈ dimensionCausalFuture (x.1, a) := by
    change ‖b - a‖ ≤ y.1 - x.1
    rw [hn]
    exact hxy
  rw [intervalVolume_ambient L hx hy]
  have h := intervalVolume_lift L (x := (x.1, a)) (y := (y.1, b))
    (slab_time_gap L hT hx hy) hc
  simpa only [spacetimeCover, ha, hb, Prod.eta, hn] using h

end CompactTorus
end BoundaryDraft
