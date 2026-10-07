import BoundaryDraft.RoundSphereDistance
import BoundaryDraft.UltrastaticMeasuredOrder
import BoundaryDraft.SphereSurface
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# The round unit sphere times a circle: an actual compact curved instance

The selected geometry in #133 has sphere radius one, circle circumference
20 and slab width 4. Its causal distance is the square root of the sum of
squared great-circle and shortest-circle distances, including the antipodal
cut locus. Its measure is round induced area times quotient length. No
curvature target or asymptotic estimate is defined by the action.
-/

open MeasureTheory Set Metric
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft
namespace SphereCircle

abbrev Space (L : ℝ) := RoundSphere × AddCircle L

/-- Round unit-sphere area, already identified with induced Hausdorff area by
`SphereSurface`; no chart seams, poles or antipodes are removed. -/
def sphereArea : Measure RoundSphere :=
  (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

theorem sphereArea_eq_induced : sphereArea =
    Measure.comap (Subtype.val : RoundSphere → EuclideanSpace ℝ (Fin 3)) normalizedHausdorffTwo :=
  normalizedHausdorffTwo_comap_sphere.symm

instance : IsFiniteMeasure sphereArea := by unfold sphereArea; infer_instance

instance : NoAtoms sphereArea := by
  letI : NoAtoms (Measure.hausdorffMeasure 2 : Measure JointSpace) :=
    Measure.noAtoms_hausdorff JointSpace (by norm_num)
  constructor
  intro x
  rw [sphereArea_eq_induced,
    (MeasurableEmbedding.subtype_coe (isClosed_sphere.measurableSet :
      MeasurableSet (Metric.sphere (0 : JointSpace) 1))).comap_apply]
  simp [normalizedHausdorffTwo]

theorem sphereArea_univ : sphereArea univ = ENNReal.ofReal (4 * Real.pi) := by
  have h : (sphereArea univ).toReal = 4 * Real.pi := jointSphere_area
  rw [← ENNReal.ofReal_toReal (measure_ne_top sphereArea univ), h]

/-- The actual ultrastatic spatial distance, NOT a chord/max surrogate. -/
def spatialDistance (L : ℝ) : SpatialDistance (Space L) :=
  RoundSphere.spatialDistance.prod (SpatialDistance.ofMetric (AddCircle L))

theorem distance_eq (L : ℝ) (x y : Space L) :
    (spatialDistance L).distance x y =
      Real.sqrt ((Real.arccos (inner (𝕜 := ℝ) x.1.val y.1.val)) ^ 2 + dist x.2 y.2 ^ 2) := by
  simp only [spatialDistance, SpatialDistance.prod_distance, RoundSphere.spatialDistance,
    SpatialDistance.ofMetric, RoundSphere.distance_eq_arccos]

variable (L : ℝ) [Fact (0 < L)]

/-- Geometric area times LENGTH, not probability-normalized volume. -/
def spatialVolume : Measure (Space L) := sphereArea.prod (volume : Measure (AddCircle L))

instance : IsFiniteMeasure (spatialVolume L) := by unfold spatialVolume; infer_instance
instance : NoAtoms (spatialVolume L) := by unfold spatialVolume; infer_instance

theorem spatialVolume_univ : spatialVolume L univ = ENNReal.ofReal (4 * Real.pi * L) := by
  rw [spatialVolume, ← univ_prod_univ, Measure.prod_prod, sphereArea_univ,
    AddCircle.measure_univ, ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi)]

omit [Fact (0 < L)] in
theorem standardBorel : StandardBorelSpace (ℝ × Space L) := by
  haveI : StandardBorelSpace RoundSphere := inferInstance
  haveI : StandardBorelSpace (AddCircle L) := inferInstance
  infer_instance

theorem compactSpace : CompactSpace (Space L) := inferInstance

abbrev measuredOrder : MeasuredOrder (ℝ × Space L) := Ultrastatic.measuredOrder (spatialDistance L)
abbrev slab (T : ℝ) : Set (ℝ × Space L) := Ultrastatic.slab T
abbrev slabVolume (T : ℝ) : Measure (ℝ × Space L) := Ultrastatic.slabVolume (spatialVolume L) T
abbrev probability (T ρ : ℝ) := Ultrastatic.probability (spatialVolume L) T ρ

theorem slabVolume_univ (T : ℝ) :
    slabVolume L T univ = ENNReal.ofReal (T * (4 * Real.pi * L)) := by
  rw [Ultrastatic.slabVolume_univ, spatialVolume_univ,
    ENNReal.ofReal_mul' (mul_nonneg (by positivity) (le_of_lt (Fact.out : 0 < L)))]

theorem slabVolume_pos {T : ℝ} (hT : 0 < T) : 0 < slabVolume L T univ := by
  rw [slabVolume_univ]
  exact ENNReal.ofReal_pos.mpr
    (mul_pos hT (mul_pos (by positivity) (Fact.out : 0 < L)))

omit [Fact (0 < L)] in
theorem interval_subset_slab {T : ℝ} {x y : ℝ × Space L}
    (hx : x ∈ slab L T) (hy : y ∈ slab L T) :
    Ultrastatic.closedInterval (spatialDistance L) x y ⊆ slab L T :=
  Ultrastatic.interval_subset_slab _ hx hy

theorem intervalVolume_ambient {T : ℝ} {x y : ℝ × Space L}
    (hx : x ∈ slab L T) (hy : y ∈ slab L T) :
    slabVolume L T ((measuredOrder L).interval x y) =
      (volume.prod (spatialVolume L)) (Ultrastatic.closedInterval (spatialDistance L) x y) :=
  Ultrastatic.intervalVolume_ambient _ _ hx hy

/-- The same generic probability theorem applies through the cut locus: no
unique-geodesic, thin-slab or smooth interval-volume premise is used. -/
theorem expectation_eq (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, MeasuredOrderBDG4.discreteAction (measuredOrder L) ρ c ∂probability L T ρ) =
      MeasuredOrderBDG4.action (measuredOrder L) (slabVolume L T) ρ :=
  Ultrastatic.expectation_eq _ _ _ hρ

end SphereCircle
end BoundaryDraft
