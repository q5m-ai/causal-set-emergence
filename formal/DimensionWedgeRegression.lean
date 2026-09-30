import BoundaryDraft.DimensionWedge

/-! Full-action regressions, including zero-dimensional tangential measure,
negative weights, and a concrete nonzero two-dimensional regulated limit. -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

-- A genuine Euclidean 3-4-5 check, not the supremum-norm value 4.
example : ‖dimensionWedgePoint 3
    ((WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => 4))‖ ^ 2 = 25 := by
  rw [norm_dimensionWedgePoint_sq]
  norm_num [PiLp.norm_sq_eq_of_L2]

-- The n = 0 case has a nonzero-dimensional normal space and unit tangent mass.
example (a β c : ℝ)
    (hG : IntegrableOn (dimensionVerticalKernel 1 a β c 1) (Ioi 0))
    (hmass : (∫ s : ℝ in Ioi 0, dimensionVerticalKernel 1 a β c 1 s) = 1)
    {κ H R : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial 1 → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction 1 a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator 0 κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * w (dimensionWedgePoint 0 (0 : DimensionSpatial 0)))) := by
  have hl := dimensionWeighted_wedge_limit_of_mass 0 a β c hG hmass hκ hκ1 hH w hw hsource
  change Tendsto _ _ (𝓝 (κ⁻¹ * dimensionWedgeTangentialProfile 0 w 0)) at hl
  simpa only [dimensionWedgeTangentialProfile_zero_dim] using hl

-- Negative weights keep the full partner integral unchanged.
example (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ : ℝ) :
    dimensionWeightedAction (n + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => -w p.2) =
      ∫ r : ℝ in Ioi 0, dimensionWedgeTangentialProfile n (fun x => -w x) r *
        dimensionVerticalKernel (n + 1) a β c ρ (κ * r) :=
  dimensionWeighted_wedge_eq_normalIntegral n hκ hκ1 hH (fun x => -w x) hw.neg
    (fun x hx => by change -w x = 0; rw [hsource x hx, neg_zero]) a β c ρ

-- Actual physical 2D action: no analytic premises and explicit coefficients.
example {κ H R : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial 1 → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction 1 2 4 (1 / 2) ρ
      (dimensionGraphCap (dimensionWedgeRegulator 0 κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * w (dimensionWedgePoint 0 (0 : DimensionSpatial 0)))) := by
  have hl := dimensionWeighted_wedge_limit 0 hκ hκ1 hH w hw hsource
  change Tendsto _ _ (𝓝 (κ⁻¹ * dimensionWedgeTangentialProfile 0 w 0)) at hl
  simpa only [Nat.reduceAdd, dimensionWedgeTangentialProfile_zero_dim, dimensionPointCoefficient_two,
    dimensionPairCoefficient_two, dimensionIntervalCoefficient_two] using hl

-- The physical odd-dimensional case also has no mass or integrability premise.
example {κ H R : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial 2 → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction 2
      (dimensionPointCoefficient 3) (dimensionPairCoefficient 3) (Real.pi / 12) ρ
      (dimensionGraphCap (dimensionWedgeRegulator 1 κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : DimensionSpatial 1, w (dimensionWedgePoint 0 z))) := by
  simpa only [Nat.reduceAdd, dimensionIntervalCoefficient_three] using
    dimensionWeighted_wedge_limit 1 hκ hκ1 hH w hw hsource

-- The physical four-dimensional specialization retains the standard constants.
example {κ H R : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial 3 → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction 3
      (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) ρ
      (dimensionGraphCap (dimensionWedgeRegulator 2 κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : DimensionSpatial 2, w (dimensionWedgePoint 0 z))) := by
  simpa only [Nat.reduceAdd, dimensionPointCoefficient_four, dimensionPairCoefficient_four,
    dimensionIntervalCoefficient_four] using
    dimensionWeighted_wedge_limit 2 hκ hκ1 hH w hw hsource

private def lineWeight (x : DimensionSpatial 1) : ℝ := max 0 (1 - ‖x‖)

-- A genuinely nonzero source: slope one-half gives coefficient two.
example :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction 1 2 4 (1 / 2) ρ
      (dimensionGraphCap (dimensionWedgeRegulator 0 (1 / 2) 1))
      (fun p => lineWeight p.2)) atTop (𝓝 2) := by
  have hw : Continuous lineWeight := by unfold lineWeight; fun_prop
  have hs : ∀ x : DimensionSpatial 1, (1 : ℝ) < ‖x‖ → lineWeight x = 0 := by
    intro x hx
    unfold lineWeight
    exact max_eq_left (by linarith)
  have hl := dimensionWeighted_wedge_limit 0
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : 2 * (1 / 2 : ℝ) * 1 ≤ 1) lineWeight hw hs
  change Tendsto _ _ (𝓝 ((1 / 2 : ℝ)⁻¹ * dimensionWedgeTangentialProfile 0 lineWeight 0)) at hl
  have hp : dimensionWedgePoint 0 (0 : DimensionSpatial 0) = (0 : DimensionSpatial 1) := by
    ext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp
  simpa [dimensionWedgeTangentialProfile_zero_dim, hp, lineWeight,
    dimensionPointCoefficient_two, dimensionPairCoefficient_two, dimensionIntervalCoefficient_two]
    using hl

end BoundaryDraft
