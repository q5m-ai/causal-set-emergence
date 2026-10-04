import BoundaryDraft.Pilot3Coarea
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Null regular levels and strict-collar interfaces

One-dimensional Hausdorff finiteness implies planar volume-nullity without
coarea. Only zeros in the closed positive region are removed; arbitrary
exterior raw zero sets are never assumed null.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
include hh

theorem volume_level_eq_zero (t : ℝ) (hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0) :
    volume (pilot3Level h t) = 0 := by
  have hz : (μH[2] : Measure Pilot3Space) (pilot3Level h t) = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) _).resolve_right
      (hh.hausdorff_level_lt_top t hreg).ne
  have hz' : (μH[Module.finrank ℝ Pilot3Space] : Measure Pilot3Space) (pilot3Level h t) = 0 := by
    simpa only [Pilot3Space, DimensionSpatial, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] using hz
  exact (Measure.absolutelyContinuous_isAddHaarMeasure volume
    (μH[Module.finrank ℝ Pilot3Space] : Measure Pilot3Space)) hz'

theorem ae_positive_eq_closedPositive : {x : Pilot3Space | 0 < h x} =ᶠ[ae volume] pilot3ClosedPositive h := by
  have hz := hh.volume_level_eq_zero 0 (fun x hx => hh.regular_zero x hx.1 hx.2)
  have hn : ∀ᵐ x : Pilot3Space, x ∉ pilot3Level h 0 := by simpa only [ae_iff, not_not] using hz
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · exact fun hp => subset_closure hp
  · intro hxc
    exact lt_of_le_of_ne (hh.nonneg_on_closedPositive x hxc) (fun he => hx ⟨hxc, he.symm⟩)

theorem ae_openCollar_eq_closedCollar (t : ℝ) (hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0) :
    {x : Pilot3Space | 0 < h x ∧ h x < t} =ᶠ[ae volume] pilot3ClosedCollar h t := by
  have hzero := hh.volume_level_eq_zero 0 (fun x hx => hh.regular_zero x hx.1 hx.2)
  have htop := hh.volume_level_eq_zero t hreg
  have hz : ∀ᵐ x : Pilot3Space, x ∉ pilot3Level h 0 := by simpa only [ae_iff, not_not] using hzero
  have ht : ∀ᵐ x : Pilot3Space, x ∉ pilot3Level h t := by simpa only [ae_iff, not_not] using htop
  filter_upwards [hz, ht] with x hx0 hxt
  apply propext
  constructor
  · exact fun hx => ⟨subset_closure hx.1, hx.2.le⟩
  · intro hx
    exact ⟨lt_of_le_of_ne (hh.nonneg_on_closedPositive x hx.1) (fun he => hx0 ⟨hx.1, he.symm⟩),
      lt_of_le_of_ne hx.2 (fun he => hxt ⟨hx.1, he⟩)⟩

end Pilot3RegularHeight
namespace Pilot3CollarAtlas
variable {h : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

theorem integrableOn_openCollar_weighted (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntegrableOn (fun x => g (h x) * w x) {x | 0 < h x ∧ h x < A.width} := by
  rw [IntegrableOn, Measure.restrict_congr_set (hh.ae_openCollar_eq_closedCollar A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩))]
  exact A.integrableOn_closedCollar_weighted hh w hw g hg

theorem intervalIntegrable_weightedHeightDensity (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    IntervalIntegrable (fun t => g t * pilot3WeightedHeightDensity h w t) volume 0 A.width :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le A.width_pos.le).mpr
    (A.integrableOn_weightedHeightDensity_mul hh w hw g hg)

theorem integral_openCollar_weighted (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    (∫ x in {x | 0 < h x ∧ h x < A.width}, g (h x) * w x) =
      ∫ t in (0 : ℝ)..A.width, g t * pilot3WeightedHeightDensity h w t := by
  rw [setIntegral_congr_set (hh.ae_openCollar_eq_closedCollar A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩)), A.integral_closedCollar_weighted hh w hw g hg,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le A.width_pos.le]

end Pilot3CollarAtlas
end BoundaryDraft
