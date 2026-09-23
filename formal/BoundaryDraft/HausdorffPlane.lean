import BoundaryDraft.PlanarIsodiametric
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Euclidean planar Hausdorff normalization

Arbitrarily small Besicovitch disk coverings with nearly minimal total area
prove `(π/4) μH[2] ≤ volume` in the Euclidean plane, including on nonmeasurable
sets. The sharp planar isodiametric inequality gives the reverse bound through
`Measure.le_hausdorffMeasure`. Thus the normalized measure equals Lebesgue
measure on every set, without a measurability or finiteness hypothesis.
-/

open MeasureTheory Set Filter Metric
open scoped Topology MeasureTheory ENNReal
noncomputable section
namespace BoundaryDraft

private theorem ediam_closedBall_le (x : SurfacePlane) (r : ℝ) :
    EMetric.diam (closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
  apply ediam_le_of_forall_dist_le
  intro y hy z hz
  calc
    dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
    _ ≤ 2 * r := by linarith [mem_closedBall.mp hy, mem_closedBall.mp hz]

private theorem ediam_closedBall_sq_le_area (x : SurfacePlane) (r : ℝ) :
    EMetric.diam (closedBall x r) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 / Real.pi) * volume (closedBall x r) := by
  have hπ : ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal Real.pi = 4 := by
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ Real.pi_ne_zero]
    norm_num
  calc
    _ ≤ (ENNReal.ofReal (2 * r)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow (ediam_closedBall_le x r) (by norm_num)
    _ = 4 * (ENNReal.ofReal r) ^ 2 := by
      rw [ENNReal.rpow_two, ENNReal.ofReal_mul (by norm_num)]
      norm_num [mul_pow]
    _ = _ := by
      rw [EuclideanSpace.volume_closedBall_fin_two, mul_comm ((ENNReal.ofReal r) ^ 2),
        ← mul_assoc, hπ]

/-- The sharp covering upper bound for the unnormalized diameter measure.
No Borel-set premise and no planar isodiametric premise is used. -/
theorem hausdorff_plane_le_scaled_volume (s : Set SurfacePlane) :
    (μH[2] : Measure SurfacePlane) s ≤ ENNReal.ofReal (4 / Real.pi) * volume s := by
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ (t : Set SurfacePlane) (r : SurfacePlane → ℝ),
      t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ Ioo 0 (c n)) ∧
      (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧
      (∑' x : t, volume (closedBall (x : SurfacePlane) (r x))) ≤ volume s + ENNReal.ofReal (c n) := by
    apply Besicovitch.exists_closedBall_covering_tsum_measure_le volume
      (ne_of_gt (ENNReal.ofReal_pos.mpr (hc n))) (fun _ => Ioo 0 (c n)) s
    intro x hx δ hδ
    refine ⟨min (c n) δ / 2, ?_⟩
    have hm : 0 < min (c n) δ := lt_min (hc n) hδ
    exact ⟨⟨half_pos hm, (half_lt_self hm).trans_le (min_le_left _ _)⟩,
      half_pos hm, (half_lt_self hm).trans_le (min_le_right _ _)⟩
  choose t r ht hts hr hcover hsum using hex
  letI (n : ℕ) : Countable (t n) := (ht n).to_subtype
  let disks (n : ℕ) (x : t n) : Set SurfacePlane := closedBall x (r n x)
  have hdiam : ∀ n (x : t n), EMetric.diam (disks n x) ≤ ENNReal.ofReal (2 * c n) := by
    intro n x
    exact (ediam_closedBall_le x (r n x)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hr n x x.property).2.le (by norm_num)))
  have hcover' : ∀ n, s ⊆ ⋃ x : t n, disks n x := by
    intro n
    simpa only [disks, iUnion_subtype] using hcover n
  have hsum' : ∀ n, (∑' x : t n, EMetric.diam (disks n x) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (4 / Real.pi) * (volume s + ENNReal.ofReal (c n)) := by
    intro n
    calc
      _ ≤ ∑' x : t n, ENNReal.ofReal (4 / Real.pi) * volume (disks n x) := by
        apply ENNReal.tsum_le_tsum
        intro x
        exact ediam_closedBall_sq_le_area x (r n x)
      _ = ENNReal.ofReal (4 / Real.pi) * ∑' x : t n, volume (disks n x) :=
        ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul_left' (hsum n) _
  have hsize : Tendsto (fun n => ENNReal.ofReal (2 * c n)) atTop (𝓝 0) := by
    simpa [c, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hc0.const_mul 2)
  have hbound : Tendsto
      (fun n => ENNReal.ofReal (4 / Real.pi) * (volume s + ENNReal.ofReal (c n)))
      atTop (𝓝 (ENNReal.ofReal (4 / Real.pi) * volume s)) := by
    have he : Tendsto (fun n => ENNReal.ofReal (c n)) atTop (𝓝 0) := by
      simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc0
    simpa only [add_zero] using ENNReal.Tendsto.const_mul
      (tendsto_const_nhds.add he) (Or.inr (ENNReal.ofReal_ne_top (r := 4 / Real.pi)))
  exact (Measure.hausdorffMeasure_le_liminf_tsum 2 s _ hsize disks
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover')).trans
      ((liminf_le_liminf (Eventually.of_forall hsum')).trans_eq hbound.liminf_eq)

/-- The covering direction of Euclidean planar normalization. -/
theorem normalized_hausdorff_plane_le_volume (s : Set SurfacePlane) :
    ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure SurfacePlane) s ≤ volume s := by
  have he : ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (4 / Real.pi) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    field_simp
  have hb := mul_le_mul_left' (hausdorff_plane_le_scaled_volume s) (ENNReal.ofReal (Real.pi / 4))
  simpa only [← mul_assoc, he, one_mul] using hb

/-- The isodiametric direction of Euclidean planar normalization. -/
theorem volume_le_normalized_hausdorff_plane (s : Set SurfacePlane) :
    volume s ≤ ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure SurfacePlane) s := by
  have he : ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (4 / Real.pi) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    field_simp
  have he' : ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal (Real.pi / 4) = 1 := by
    rwa [mul_comm]
  have hscaled : ENNReal.ofReal (4 / Real.pi) • (volume : Measure SurfacePlane) ≤ μH[2] := by
    apply Measure.le_hausdorffMeasure 2 _ 1 zero_lt_one
    intro t _
    have h := mul_le_mul_left' (volume_le_pi_div_four_mul_ediam_sq t)
      (ENNReal.ofReal (4 / Real.pi))
    simpa only [Measure.smul_apply, smul_eq_mul, ← mul_assoc, he', one_mul] using h
  have h := mul_le_mul_left' (Measure.le_iff'.mp hscaled s) (ENNReal.ofReal (Real.pi / 4))
  simpa only [Measure.smul_apply, smul_eq_mul, ← mul_assoc, he, one_mul] using h

/-- Normalization on every planar set, including nonmeasurable sets and sets
of infinite measure. -/
theorem normalized_hausdorff_plane_eq_volume_apply (s : Set SurfacePlane) :
    ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure SurfacePlane) s = volume s :=
  le_antisymm (normalized_hausdorff_plane_le_volume s) (volume_le_normalized_hausdorff_plane s)

/-- Normalized two-dimensional Hausdorff measure on the Euclidean plane is
Lebesgue measure. -/
theorem normalized_hausdorff_plane_eq_volume :
    ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure SurfacePlane) = volume := by
  ext s
  exact normalized_hausdorff_plane_eq_volume_apply s

/-- This explicitly justifies discarding Lebesgue-null remainders in the
covering construction, rather than assuming the two planar measures equal. -/
theorem hausdorff_plane_zero_of_volume_zero (s : Set SurfacePlane) (hs : volume s = 0) :
    (μH[2] : Measure SurfacePlane) s = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa only [hs, mul_zero] using hausdorff_plane_le_scaled_volume s

end BoundaryDraft
