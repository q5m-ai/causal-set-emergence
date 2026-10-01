import BoundaryDraft.DimensionGeometry
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Dimension-indexed order intervals

The order is the closed causal order, not chronology. The exclusive interval
removes only its two endpoints. Nullity is a measure theorem, never an order
hypothesis. `n` denotes spatial dimension; the physical range is `0 < n`.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft

variable {n : ℕ}

instance dimensionSpacetime_noAtoms (n : ℕ) :
    NoAtoms (volume : Measure (DimensionSpacetime n)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

instance dimensionSpacetime_isAddHaarMeasure (n : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (DimensionSpacetime n)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

def dimensionChronologicalFuture (x : DimensionSpacetime n) : Set (DimensionSpacetime n) :=
  {y | ‖y.2 - x.2‖ < y.1 - x.1}

/-- Closed, ambient order interval. -/
def dimensionCausalInterval (x y : DimensionSpacetime n) : Set (DimensionSpacetime n) :=
  {z | z ∈ dimensionCausalFuture x ∧ y ∈ dimensionCausalFuture z}

/-- Exclusive order interval, retaining null-related intermediate points. -/
def dimensionCausalIntervalInterior (x y : DimensionSpacetime n) : Set (DimensionSpacetime n) :=
  dimensionCausalInterval x y \ {x, y}

theorem dimensionCausalFuture_refl (x : DimensionSpacetime n) : x ∈ dimensionCausalFuture x := by
  simp [dimensionCausalFuture]

theorem dimensionCausalFuture_trans {x y z : DimensionSpacetime n}
    (hxy : y ∈ dimensionCausalFuture x) (hyz : z ∈ dimensionCausalFuture y) :
    z ∈ dimensionCausalFuture x := by
  calc
    ‖z.2 - x.2‖ = ‖(z.2 - y.2) + (y.2 - x.2)‖ := by congr 1; abel
    _ ≤ ‖z.2 - y.2‖ + ‖y.2 - x.2‖ := norm_add_le _ _
    _ ≤ z.1 - x.1 := by change ‖y.2 - x.2‖ ≤ _ at hxy; change ‖z.2 - y.2‖ ≤ _ at hyz; linarith

theorem dimensionCausalFuture_antisymm {x y : DimensionSpacetime n}
    (hxy : y ∈ dimensionCausalFuture x) (hyx : x ∈ dimensionCausalFuture y) : x = y := by
  change ‖y.2 - x.2‖ ≤ y.1 - x.1 at hxy
  change ‖x.2 - y.2‖ ≤ x.1 - y.1 at hyx
  have ht : x.1 = y.1 := by nlinarith [norm_nonneg (y.2 - x.2), norm_nonneg (x.2 - y.2)]
  have hs : y.2 = x.2 := sub_eq_zero.mp (norm_eq_zero.mp (by rw [ht] at hxy; simpa using hxy))
  exact Prod.ext ht hs.symm

/-- An order available to finite-configuration consumers, with no chronology
premise and without installing a conflicting product-order instance. -/
def dimensionCausalOrder (n : ℕ) : PartialOrder (DimensionSpacetime n) where
  le x y := y ∈ dimensionCausalFuture x
  le_refl := dimensionCausalFuture_refl
  le_trans _ _ _ := dimensionCausalFuture_trans
  le_antisymm _ _ := dimensionCausalFuture_antisymm

theorem dimensionIntervalSq_nonneg {x y : DimensionSpacetime n}
    (hxy : y ∈ dimensionCausalFuture x) : 0 ≤ dimensionIntervalSq x y := by
  change ‖y.2 - x.2‖ ≤ y.1 - x.1 at hxy
  unfold dimensionIntervalSq
  nlinarith [norm_nonneg (y.2 - x.2)]

theorem dimensionIntervalSq_pos {x y : DimensionSpacetime n}
    (hxy : y ∈ dimensionChronologicalFuture x) : 0 < dimensionIntervalSq x y := by
  change ‖y.2 - x.2‖ < y.1 - x.1 at hxy
  unfold dimensionIntervalSq
  nlinarith [norm_nonneg (y.2 - x.2)]

theorem measurableSet_dimensionCausalRelation :
    MeasurableSet {p : DimensionSpacetime n × DimensionSpacetime n |
      p.2 ∈ dimensionCausalFuture p.1} :=
  (isClosed_le (continuous_snd.snd.sub continuous_fst.snd).norm
    (continuous_snd.fst.sub continuous_fst.fst)).measurableSet

theorem measurableSet_dimensionCausalInterval_joint :
    MeasurableSet {p : (DimensionSpacetime n × DimensionSpacetime n) × DimensionSpacetime n |
      p.2 ∈ dimensionCausalInterval p.1.1 p.1.2} := by
  unfold dimensionCausalInterval dimensionCausalFuture
  exact ((isClosed_le (continuous_snd.snd.sub continuous_fst.fst.snd).norm
    (continuous_snd.fst.sub continuous_fst.fst.fst)).inter
      (isClosed_le (continuous_fst.snd.snd.sub continuous_snd.snd).norm
        (continuous_fst.snd.fst.sub continuous_snd.fst))).measurableSet

theorem measurableSet_dimensionCausalIntervalInterior_joint :
    MeasurableSet {p : (DimensionSpacetime n × DimensionSpacetime n) × DimensionSpacetime n |
      p.2 ∈ dimensionCausalIntervalInterior p.1.1 p.1.2} := by
  have h := (measurableSet_dimensionCausalInterval_joint (n := n)).diff
    ((isClosed_eq continuous_snd continuous_fst.fst).measurableSet.union
      (isClosed_eq continuous_snd continuous_fst.snd).measurableSet)
  simpa only [dimensionCausalIntervalInterior, mem_diff, mem_insert_iff,
    mem_singleton_iff, mem_union, mem_setOf_eq] using h

theorem measurableSet_dimensionCausalInterval (x y : DimensionSpacetime n) :
    MeasurableSet (dimensionCausalInterval x y) := by
  have h := (measurableSet_dimensionCausalInterval_joint (n := n)).preimage
    (measurable_const.prodMk measurable_id : Measurable (fun z : DimensionSpacetime n => ((x, y), z)))
  exact h

theorem measurableSet_dimensionCausalIntervalInterior (x y : DimensionSpacetime n) :
    MeasurableSet (dimensionCausalIntervalInterior x y) :=
  (measurableSet_dimensionCausalInterval x y).diff ((finite_singleton y).insert x).measurableSet

@[simp] theorem left_not_mem_dimensionCausalIntervalInterior (x y : DimensionSpacetime n) :
    x ∉ dimensionCausalIntervalInterior x y := by simp [dimensionCausalIntervalInterior]

@[simp] theorem right_not_mem_dimensionCausalIntervalInterior (x y : DimensionSpacetime n) :
    y ∉ dimensionCausalIntervalInterior x y := by simp [dimensionCausalIntervalInterior]

/-- Finite endpoint sets have zero ambient volume. -/
theorem volume_dimensionInterval_endpoints (x y : DimensionSpacetime n) :
    volume ({x, y} : Set (DimensionSpacetime n)) = 0 :=
  ((finite_singleton y).insert x).measure_zero volume

theorem volume_dimensionCausalIntervalInterior (x y : DimensionSpacetime n) :
    volume (dimensionCausalIntervalInterior x y) = volume (dimensionCausalInterval x y) :=
  measure_diff_null (volume_dimensionInterval_endpoints x y)

/-- The endpoint diagonal is null in the actual product measure. -/
theorem volume_dimensionDiagonal :
    volume {p : DimensionSpacetime n × DimensionSpacetime n | p.1 = p.2} = 0 := by
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null (isClosed_eq continuous_fst continuous_snd).measurableSet
  filter_upwards [] with x
  simp

/-- Fubini and spatial sphere nullity, including the two directions in 2D. -/
theorem volume_dimensionNullCone (hn : 0 < n) (x : DimensionSpacetime n) :
    volume {y : DimensionSpacetime n | dimensionIntervalSq x y = 0} = 0 := by
  letI : NeZero n := ⟨hn.ne'⟩
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null
    (isClosed_eq (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id))
      continuous_const).measurableSet
  filter_upwards [] with t
  have he : {z : DimensionSpatial n | dimensionIntervalSq x (t, z) = 0} =
      Metric.sphere x.2 |t - x.1| := by
    ext z
    simp only [mem_setOf_eq, dimensionIntervalSq, Metric.mem_sphere, dist_eq_norm]
    rw [sub_eq_zero, ← sq_abs (t - x.1)]
    exact ⟨fun h => (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp h.symm,
      fun h => by rw [h]⟩
  change volume {z : DimensionSpatial n | dimensionIntervalSq x (t, z) = 0} = 0
  rw [he, Measure.addHaar_sphere]

theorem volume_dimensionNullPairs (hn : 0 < n) :
    volume {p : DimensionSpacetime n × DimensionSpacetime n |
      dimensionIntervalSq p.1 p.2 = 0} = 0 := by
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null
    (isClosed_eq continuous_dimensionIntervalSq continuous_const).measurableSet
  exact Filter.Eventually.of_forall (volume_dimensionNullCone hn)

/-- A null interval lies on the cone of its first endpoint. This proves the
null interval's volume directly, without taking a singular rest-frame limit. -/
theorem dimensionCausalInterval_subset_nullCone {x y : DimensionSpacetime n}
    (hxy : dimensionIntervalSq x y = 0) :
    dimensionCausalInterval x y ⊆ {z | dimensionIntervalSq x z = 0} := by
  intro z hz
  have hzx : ‖z.2 - x.2‖ ≤ z.1 - x.1 := hz.1
  have hyz : ‖y.2 - z.2‖ ≤ y.1 - z.1 := hz.2
  have hyx := dimensionCausalFuture_trans hz.1 hz.2
  have ht : 0 ≤ y.1 - x.1 := (norm_nonneg _).trans hyx
  have he : ‖y.2 - x.2‖ = y.1 - x.1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) ht).mp
    have := sub_eq_zero.mp hxy
    exact this.symm
  have htri : ‖y.2 - x.2‖ ≤ ‖y.2 - z.2‖ + ‖z.2 - x.2‖ := by
    calc
      _ = ‖(y.2 - z.2) + (z.2 - x.2)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hz' : ‖z.2 - x.2‖ = z.1 - x.1 := by rw [he] at htri; linarith
  simp [dimensionIntervalSq, hz']

theorem volume_dimensionCausalInterval_null (hn : 0 < n) (x y : DimensionSpacetime n)
    (hxy : dimensionIntervalSq x y = 0) : volume (dimensionCausalInterval x y) = 0 :=
  measure_mono_null (dimensionCausalInterval_subset_nullCone hxy) (volume_dimensionNullCone hn x)

theorem dimensionCausalInterval_eq_empty {x y : DimensionSpacetime n}
    (hxy : y ∉ dimensionCausalFuture x) : dimensionCausalInterval x y = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  exact fun _ hz => hxy (dimensionCausalFuture_trans hz.1 hz.2)

/-- Ambient causal convexity is interval containment, not a volume formula. -/
def DimensionCausallyConvex (M : Set (DimensionSpacetime n)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, dimensionCausalInterval x y ⊆ M

/-- Defined for EVERY region. In a non-convex region this remains the relevant
interval volume; it is not replaced by a proper-time expression. -/
def dimensionRestrictedIntervalVolume (M : Set (DimensionSpacetime n))
    (x y : DimensionSpacetime n) : ℝ≥0∞ :=
  volume (dimensionCausalIntervalInterior x y ∩ M)

theorem dimensionRestrictedIntervalVolume_eq {M : Set (DimensionSpacetime n)}
    (hM : DimensionCausallyConvex M) {x y : DimensionSpacetime n} (hx : x ∈ M) (hy : y ∈ M) :
    dimensionRestrictedIntervalVolume M x y = volume (dimensionCausalInterval x y) := by
  rw [dimensionRestrictedIntervalVolume, inter_eq_left.mpr
    (fun _ hz => hM x hx y hy hz.1), volume_dimensionCausalIntervalInterior]

/-- Existing graph caps are non-vacuous examples of the geometric condition. -/
theorem DimensionGraphCapData.causallyConvex {h : DimensionSpatial n → ℝ}
    (hh : DimensionGraphCapData h) : DimensionCausallyConvex (dimensionGraphCap h) := by
  intro x hx y hy z hz
  have ht : z.1 < 0 := lt_of_le_of_lt (by
    have h := (norm_nonneg _).trans hz.2
    linarith) hy.2
  have hm : z ∈ dimensionGraphCap h ∩ dimensionCausalFuture x := by
    rw [hh.complete_future x hx]
    exact ⟨hz.1, ht⟩
  exact hm.1

/-- The interval-volume function is jointly measurable in its two endpoints. -/
theorem measurable_dimensionRestrictedIntervalVolume {M : Set (DimensionSpacetime n)}
    (hM : MeasurableSet M) :
    Measurable (fun p : DimensionSpacetime n × DimensionSpacetime n =>
      dimensionRestrictedIntervalVolume M p.1 p.2) := by
  have h := (measurableSet_dimensionCausalIntervalInterior_joint (n := n)).inter
    (hM.preimage measurable_snd)
  exact measurable_measure_prodMk_left h

/-- Null exclusive intervals and their restrictions are null for any region,
without a causal-convexity or measurability assumption on that region. -/
theorem dimensionRestrictedIntervalVolume_null (hn : 0 < n)
    (M : Set (DimensionSpacetime n)) (x y : DimensionSpacetime n)
    (hxy : dimensionIntervalSq x y = 0) : dimensionRestrictedIntervalVolume M x y = 0 :=
  measure_mono_null (fun _ hz => hz.1.1) (volume_dimensionCausalInterval_null hn x y hxy)

/-- Chronology is available almost everywhere for integration ONLY. It does
not replace the closed causal order in a finite configuration. -/
theorem ae_dimensionCausalFuture_chronological (hn : 0 < n) (x : DimensionSpacetime n) :
    ∀ᵐ y ∂volume, y ∈ dimensionCausalFuture x → y ∈ dimensionChronologicalFuture x ∧ x ≠ y := by
  have hnull : ∀ᵐ y ∂volume, dimensionIntervalSq x y ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using volume_dimensionNullCone hn x
  filter_upwards [hnull] with y hs hxy
  have hc : y ∈ dimensionChronologicalFuture x := by
    change ‖y.2 - x.2‖ < y.1 - x.1
    apply lt_of_le_of_ne hxy
    intro he
    exact hs (by simp [dimensionIntervalSq, he])
  exact ⟨hc, fun he => hs (by simp [dimensionIntervalSq, he])⟩

end BoundaryDraft
