import BoundaryDraft.GraphAtlas

/-!
# Null levels and collar endpoints

Regular levels are volume-null by Hausdorff finiteness, independently of
coarea. The positive-level and upper-endpoint lemmas are selectively reused
from draft PR #29; no kernel limit or density-continuity results are imported.
The zero endpoint is removed only inside the closed positive region, so
unrelated exterior zeros need not be null.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- At a positive height, restricting to the closed positive region does not
remove any points of the actual level. This does not hold at height zero. -/
theorem graphLevel_eq_of_pos (h : Spatial → ℝ) (s : ℝ) (hs : 0 < s) :
    graphLevel h s = {x : JointSpace | h x = s} := by
  ext x
  constructor
  · exact And.right
  · intro hx
    exact ⟨subset_closure (show 0 < h x from hx ▸ hs), hx⟩

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- Finite two-dimensional Hausdorff measure makes each regular level null
for three-dimensional volume. This is derived independently of coarea. -/
theorem volume_graphLevel_eq_zero (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    volume (graphLevel h s) = 0 := by
  have hz : (μH[3] : Measure JointSpace) (graphLevel h s) = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (2 : ℝ) < 3) _).resolve_right
      (hh.hausdorff_level_lt_top s hreg).ne
  have hz' : (μH[Module.finrank ℝ JointSpace] : Measure JointSpace) (graphLevel h s) = 0 := by
    simpa only [JointSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] using hz
  exact (Measure.absolutelyContinuous_isAddHaarMeasure volume
    (μH[Module.finrank ℝ JointSpace] : Measure JointSpace)) hz'

/-- Nullity in the original coordinate-product spatial measure, not merely
in the Euclidean coordinate model. -/
theorem volume_spatial_level_eq_zero (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    volume {x : Spatial | h x = s} = 0 := by
  have he : (WithLp.equiv 2 (Fin 3 → ℝ)) '' graphLevel h s = {x : Spatial | h x = s} := by
    rw [graphLevel_eq_of_pos h s hs]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨(WithLp.equiv 2 _).symm x, hx, rfl⟩
  have hm : MeasurableSet {x : Spatial | h x = s} := by
    rw [← he]
    exact ((hh.isCompact_level s).image (PiLp.continuous_equiv 2 _)).isClosed.measurableSet
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).measure_preimage hm.nullMeasurableSet]
  change volume {x : JointSpace | h x = s} = 0
  rw [← graphLevel_eq_of_pos h s hs]
  exact hh.volume_graphLevel_eq_zero s hreg

/-- Strict and closed positive collar endpoints agree almost everywhere
when the endpoint level is regular. Unrelated exterior zeros are not removed. -/
theorem ae_collar_endpoint (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    {x : Spatial | 0 < h x ∧ h x < s} =ᶠ[ae volume] {x | 0 < h x ∧ h x ≤ s} := by
  have hn : ∀ᵐ x : Spatial, h x ≠ s := by
    apply ae_iff.2
    simpa only [not_not] using hh.volume_spatial_level_eq_zero s hs hreg
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · exact fun hy => ⟨hy.1, hy.2.le⟩
  · exact fun hy => ⟨hy.1, lt_of_le_of_ne hy.2 hx⟩

/-- Endpoint replacement in the original spatial integral follows from
proved nullity; it is not an assumed part of a coarea formula. -/
theorem integral_collar_eq_closed_endpoint (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0)
    (f : Spatial → ℝ) :
    (∫ x in {x | 0 < h x ∧ h x < s}, f x) = ∫ x in {x | 0 < h x ∧ h x ≤ s}, f x :=
  setIntegral_congr_set (hh.ae_collar_endpoint s hs hreg)

/-- Both endpoint levels are null in the Euclidean collar. No nullity claim
is made about the raw zero level outside the cap closure. -/
theorem ae_openCollar_eq_closedCollar (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    {x : JointSpace | 0 < h x ∧ h x < s} =ᶠ[ae volume] graphClosedCollar h s := by
  have hzero : volume (graphLevel h 0) = 0 :=
    hh.volume_graphLevel_eq_zero 0 (fun x hx => hh.regular_zero x hx.1 hx.2)
  have htop := hh.volume_graphLevel_eq_zero s hreg
  have hz : ∀ᵐ x : JointSpace, x ∉ graphLevel h 0 := by
    simpa only [ae_iff, not_not] using hzero
  have ht : ∀ᵐ x : JointSpace, x ∉ graphLevel h s := by
    simpa only [ae_iff, not_not] using htop
  filter_upwards [hz, ht] with x hx0 hxs
  apply propext
  constructor
  · exact fun hx => ⟨subset_closure hx.1, hx.2.le⟩
  · intro hx
    exact ⟨lt_of_le_of_ne (hh.nonneg_on_closedPositive x hx.1)
      (fun he => hx0 ⟨hx.1, he.symm⟩),
      lt_of_le_of_ne hx.2 (fun he => hxs ⟨hx.1, he⟩)⟩

/-- Endpoint removal and the measure-preserving Euclidean identification
return the integral to the original product Lebesgue spatial coordinates. -/
theorem integral_spatial_openCollar_eq_closedCollar (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0)
    (f : Spatial → ℝ) :
    (∫ x in {x | 0 < h x ∧ h x < s}, f x) =
      ∫ x in graphClosedCollar h s, f x := by
  let e := (WithLp.equiv 2 (Fin 3 → ℝ))
  have he : MeasurableEmbedding e := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.measurableEmbedding
  rw [← ((PiLp.volume_preserving_equiv (Fin 3)).restrict_preimage_emb he
    {x : Spatial | 0 < h x ∧ h x < s}).integral_comp he]
  exact setIntegral_congr_set (hh.ae_openCollar_eq_closedCollar s hreg)

/-- The same endpoint and coordinate transports preserve absolute
integrability, not only the values of totalized integrals. -/
theorem integrableOn_spatial_openCollar_iff (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0)
    (f : Spatial → ℝ) :
    IntegrableOn f {x | 0 < h x ∧ h x < s} ↔
      IntegrableOn (fun x : JointSpace => f x) (graphClosedCollar h s) := by
  let e := (WithLp.equiv 2 (Fin 3 → ℝ))
  have he : MeasurableEmbedding e := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.measurableEmbedding
  have hi : IntegrableOn (fun x : JointSpace => f x) {x | 0 < h x ∧ h x < s} ↔
      IntegrableOn f {x : Spatial | 0 < h x ∧ h x < s} :=
    ((PiLp.volume_preserving_equiv (Fin 3)).restrict_preimage_emb he
      {x : Spatial | 0 < h x ∧ h x < s}).integrable_comp_emb he
  rw [IntegrableOn, Measure.restrict_congr_set (hh.ae_openCollar_eq_closedCollar s hreg)] at hi
  exact hi.symm

end AdmissibleGraphCap
end BoundaryDraft
