import BoundaryDraft.TranslatedOverlap

/-!
# A separate global two-graph subclass

This sufficient coordinate model is not a replacement for `GraphCapData`:
its raw graph functions are globally Euclidean Lipschitz, whereas the existing
graph-cap API controls only the positive part of its height. No existing
profile or regularity hypothesis is changed here.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- The open region between two global graphs, without additional walls. -/
def twoGraphRegion (lower upper : Spatial → ℝ) : Set Spacetime :=
  {p | lower (spatialPart p) < p 0 ∧ p 0 < upper (spatialPart p)}

theorem measurableSet_twoGraphRegion {lower upper : Spatial → ℝ}
    (hl : Continuous lower) (hu : Continuous upper) :
    MeasurableSet (twoGraphRegion lower upper) := by
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  exact ((isOpen_lt (hl.comp hs) (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) (hu.comp hs))).measurableSet

/-- Pointwise vertical intersection. The general formula has both a minimum
and a maximum; the causal/Lipschitz hypotheses below remove them. -/
theorem translatedOverlap_twoGraph {lower upper : Spatial → ℝ}
    (hl : Continuous lower) (hu : Continuous upper)
    (hb : Bornology.IsBounded (twoGraphRegion lower upper)) (s : ℝ) (a : Spatial) :
    translatedOverlap (twoGraphRegion lower upper) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (min (upper x) (upper (x + a) - s) -
        max (lower x) (lower (x + a) - s)) := by
  let M := twoGraphRegion lower upper
  have hm : MeasurableSet M := measurableSet_twoGraphRegion hl hu
  have hi := (integrable_indicator_iff hm).mpr (integrable_overlap_fibre hm hb (Fin.cons s a))
  rw [translatedOverlap, ← integral_indicator hm, integral_spacetime_fibres _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun (x : Spatial) => by
    let l := max (lower x) (lower (x + a) - s)
    let u := min (upper x) (upper (x + a) - s)
    have he (t : ℝ) :
        M.indicator (fun p => M.indicator (fun _ => (1 : ℝ)) (p + Fin.cons s a)) (Fin.cons t x) =
          (Ioo l u).indicator (fun _ => (1 : ℝ)) t := by
      have hadd : (Fin.cons t x : Spacetime) + Fin.cons s a = Fin.cons (t + s) (x + a) := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      have ht : t ∈ Ioo l u ↔ Fin.cons t x ∈ M ∧ Fin.cons (t + s) (x + a) ∈ M := by
        simp only [M, twoGraphRegion, mem_setOf_eq, spatialPart_cons, Fin.cons_zero,
          mem_Ioo, l, u, max_lt_iff, lt_min_iff]
        constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
      by_cases ht' : t ∈ Ioo l u
      · obtain ⟨hx, hy⟩ := ht.mp ht'
        simp only [indicator_of_mem hx, hadd, indicator_of_mem hy, indicator_of_mem ht']
      · rw [indicator_of_not_mem ht']
        by_cases hx : Fin.cons t x ∈ M
        · rw [indicator_of_mem hx, hadd, indicator_of_not_mem (fun hy => ht' (ht.mpr ⟨hx, hy⟩))]
        · exact indicator_of_not_mem hx _
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, mul_one, Real.volume_real_Ioo]
    exact max_comm _ _

/-- Euclidean global strict Lipschitz control of a raw graph function. This
is intentionally separate from the positive-part graph-cap API. -/
def StrictGraphLipschitz (f : Spatial → ℝ) : Prop :=
  ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ x y, |f x - f y| ≤ κ * spatialDistance x y

theorem StrictGraphLipschitz.continuous {f : Spatial → ℝ} (hf : StrictGraphLipschitz f) :
    Continuous f := by
  obtain ⟨κ, hκ, _, hl⟩ := hf
  have h : LipschitzWith ⟨κ, hκ⟩ (fun x : EuclideanSpace ℝ (Fin 3) => f (WithLp.equiv 2 _ x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |f (WithLp.equiv 2 _ x) - f (WithLp.equiv 2 _ y)| ≤ κ * ‖x - y‖
    have he := hl (WithLp.equiv 2 _ x) (WithLp.equiv 2 _ y)
    change |f (WithLp.equiv 2 _ x) - f (WithLp.equiv 2 _ y)| ≤ κ * ‖y - x‖ at he
    simpa only [norm_sub_rev] using he
  exact h.continuous.comp (PiLp.continuous_equiv_symm 2 _)

private theorem graph_shift_le {f : Spatial → ℝ} (hf : StrictGraphLipschitz f)
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) (x : Spatial) :
    |f (x + a) - f x| ≤ s := by
  obtain ⟨κ, hκ, hk, hl⟩ := hf
  have hd := spatialDistance_le_of_causalFuture 0 (Fin.cons s a) hz
  have he : spatialDistance (x + a) x = spatialDistance (spatialPart 0) a := by
    apply (sq_eq_sq₀ (spatialDistance_nonneg _ _) (spatialDistance_nonneg _ _)).mp
    simp [spatialDistance_sq, spatialPart]
  have hds : spatialDistance (spatialPart 0) a ≤ s := by simpa using hd
  calc
    _ ≤ κ * spatialDistance (x + a) x := hl _ _
    _ ≤ spatialDistance (spatialPart 0) a := by
      rw [he]
      exact mul_le_of_le_one_left (spatialDistance_nonneg _ _) hk.le
    _ ≤ s := hds

/-- The advertised positive-part overlap formula at every future-causal
 displacement, including the vertex and null directions. -/
theorem translatedOverlap_twoGraph_causal {lower upper : Spatial → ℝ}
    (hl : StrictGraphLipschitz lower) (hu : StrictGraphLipschitz upper)
    (hb : Bornology.IsBounded (twoGraphRegion lower upper))
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoGraphRegion lower upper) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (upper (x + a) - s - lower x) := by
  rw [translatedOverlap_twoGraph hl.continuous hu.continuous hb]
  congr 1
  ext x
  have hlow := (abs_le.mp (graph_shift_le hl hz x)).2
  have hupp := (abs_le.mp (graph_shift_le hu hz x)).2
  rw [min_eq_right (by linarith : upper (x + a) - s ≤ upper x),
    max_eq_left (by linarith : lower (x + a) - s ≤ lower x)]

/-- The original graph cap uses a Lipschitz causal envelope, not its raw
profile. Thus compatibility does not strengthen the old API. -/
theorem GraphCapData.strictGraphLipschitz_lowerEnvelope {h : Spatial → ℝ} (hh : GraphCapData h) :
    StrictGraphLipschitz (fun x => -max 0 (h x)) := by
  obtain ⟨κ, hκ, hk, hl⟩ := hh.lipschitz_positivePart
  refine ⟨κ, hκ, hk, fun x y => ?_⟩
  simpa only [neg_sub_neg, abs_sub_comm] using hl x y

theorem strictGraphLipschitz_zero : StrictGraphLipschitz (fun _ : Spatial => (0 : ℝ)) := by
  refine ⟨0, le_rfl, zero_lt_one, ?_⟩
  intro x y
  simp

theorem twoGraphRegion_lowerEnvelope (h : Spatial → ℝ) :
    twoGraphRegion (fun x => -max 0 (h x)) (fun _ => 0) = graphCapRegion h := by
  ext p
  change (-max 0 (h (spatialPart p)) < p 0 ∧ p 0 < 0) ↔
    (-h (spatialPart p) < p 0 ∧ p 0 < 0)
  by_cases hp : 0 ≤ h (spatialPart p)
  · rw [max_eq_right hp]
  · rw [max_eq_left (le_of_not_ge hp)]
    constructor <;> intro hmem <;> exfalso <;> linarith [hmem.1, hmem.2]

/-- The entire old reduction-admissible class embeds through its envelope,
including raw profiles that are not globally Lipschitz. -/
theorem GraphCapData.translatedOverlap_causal {h : Spatial → ℝ} (hh : GraphCapData h)
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (graphCapRegion h) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (max 0 (h x) - s) := by
  have hb : Bornology.IsBounded (twoGraphRegion (fun x => -max 0 (h x)) (fun _ => 0)) := by
    rw [twoGraphRegion_lowerEnvelope]
    exact hh.isBounded_cap
  have he := translatedOverlap_twoGraph_causal hh.strictGraphLipschitz_lowerEnvelope
    strictGraphLipschitz_zero hb hz
  rw [twoGraphRegion_lowerEnvelope] at he
  convert he using 2
  ext x
  congr 1
  ring

end BoundaryDraft
