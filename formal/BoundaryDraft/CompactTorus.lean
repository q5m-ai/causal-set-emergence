import BoundaryDraft.UltrastaticMeasuredOrder
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# The cubic flat torus, with its quotient distance and geometric volume

The three factors are actual real quotients by integer multiples of L.
The causal distance is their Euclidean product, not the default product max
metric. Circle volume is mathlib's quotient of length on a fundamental interval;
it is not probability-normalized Haar measure. No thin-slab interval-volume
formula or asymptotic claim is made here.
-/

open MeasureTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft
namespace CompactTorus

abbrev Space (L : ℝ) := AddCircle L × AddCircle L × AddCircle L

/-- Cubic quotient distance with the Euclidean, rather than maximum, norm. -/
def spatialDistance (L : ℝ) : SpatialDistance (Space L) :=
  (SpatialDistance.ofMetric (AddCircle L)).prod
    ((SpatialDistance.ofMetric (AddCircle L)).prod (SpatialDistance.ofMetric (AddCircle L)))

theorem distance_eq (L : ℝ) (x y : Space L) :
    (spatialDistance L).distance x y =
      Real.sqrt (dist x.1 y.1 ^ 2 + dist x.2.1 y.2.1 ^ 2 + dist x.2.2 y.2.2 ^ 2) := by
  simp only [spatialDistance, SpatialDistance.prod_distance, SpatialDistance.ofMetric,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  congr 1
  ring

/-- Quotient projection from Cartesian lifts. Each factor is `R / L Z`. -/
def project (L : ℝ) (x : Fin 3 → ℝ) : Space L := (x 0, x 1, x 2)

theorem circle_distance_lifts (L x y : ℝ) :
    dist (x : AddCircle L) (y : AddCircle L) =
      |x - y - round (L⁻¹ * (x - y)) * L| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq]

/-- The nearest lattice lift formula uses the three independent nearest
integers, hence the actual minimum Euclidean quotient distance. -/
theorem distance_project (L : ℝ) (x y : Fin 3 → ℝ) :
    (spatialDistance L).distance (project L x) (project L y) =
      Real.sqrt (∑ i : Fin 3, (x i - y i - round (L⁻¹ * (x i - y i)) * L) ^ 2) := by
  rw [distance_eq]
  simp only [project, circle_distance_lifts, sq_abs, Fin.sum_univ_three]

variable (L : ℝ) [Fact (0 < L)]

/-- Product of quotient LENGTH measures, with total spatial volume L cubed. -/
def spatialVolume : Measure (Space L) :=
  (volume : Measure (AddCircle L)).prod
    ((volume : Measure (AddCircle L)).prod (volume : Measure (AddCircle L)))

/-- The declared volume is the pushforward of ordinary product length on a
fundamental cube. This fixes its geometric normalization independently of BDG. -/
theorem quotientVolume :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ =>
      ((p.1 : AddCircle L), (p.2.1 : AddCircle L), (p.2.2 : AddCircle L)))
      ((volume.restrict (Ioc 0 L)).prod
        ((volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioc 0 L)))) (spatialVolume L) := by
  have h := AddCircle.measurePreserving_mk L 0
  simp only [zero_add] at h
  exact h.prod (h.prod h)

instance : IsFiniteMeasure (spatialVolume L) := by unfold spatialVolume; infer_instance

instance circleVolume_noAtoms : NoAtoms (volume : Measure (AddCircle L)) := ⟨fun x => by
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  simp [min_eq_right (le_of_lt (Fact.out : 0 < L))]⟩

instance : NoAtoms (spatialVolume L) := by unfold spatialVolume; infer_instance

theorem spatialVolume_univ : spatialVolume L univ = ENNReal.ofReal (L ^ 3) := by
  simp only [spatialVolume, ← univ_prod_univ, Measure.prod_prod, AddCircle.measure_univ]
  rw [← ENNReal.ofReal_mul (le_of_lt (Fact.out : 0 < L)),
    ← ENNReal.ofReal_mul (le_of_lt (Fact.out : 0 < L))]
  congr 1
  ring

omit [Fact (0 < L)] in
/-- Explicit standard Borel verification for the ambient manifold point space. -/
theorem standardBorel : StandardBorelSpace (ℝ × Space L) := by
  haveI : StandardBorelSpace (AddCircle L) := inferInstance
  infer_instance

theorem compactSpace : CompactSpace (Space L) := inferInstance

abbrev measuredOrder : MeasuredOrder (ℝ × Space L) := Ultrastatic.measuredOrder (spatialDistance L)
abbrev slab (T : ℝ) : Set (ℝ × Space L) := Ultrastatic.slab T
abbrev slabVolume (T : ℝ) : Measure (ℝ × Space L) := Ultrastatic.slabVolume (spatialVolume L) T
abbrev probability (T ρ : ℝ) := Ultrastatic.probability (spatialVolume L) T ρ

theorem slabVolume_univ (T : ℝ) : slabVolume L T univ = ENNReal.ofReal (T * L ^ 3) := by
  rw [Ultrastatic.slabVolume_univ, spatialVolume_univ,
    ENNReal.ofReal_mul' (pow_nonneg (le_of_lt (Fact.out : 0 < L)) 3)]

theorem slabVolume_pos {T : ℝ} (hT : 0 < T) : 0 < slabVolume L T univ := by
  rw [slabVolume_univ]
  exact ENNReal.ofReal_pos.mpr (mul_pos hT (pow_pos (Fact.out : 0 < L) _))

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

/-- Applies in particular to the selected thin slab L=1, T=2/5. No small-width
hypothesis is needed for the finite-density bridge with actual intervals. -/
theorem expectation_eq (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, MeasuredOrderBDG4.discreteAction (measuredOrder L) ρ c ∂probability L T ρ) =
      MeasuredOrderBDG4.action (measuredOrder L) (slabVolume L T) ρ :=
  Ultrastatic.expectation_eq _ _ _ hρ

end CompactTorus
end BoundaryDraft
