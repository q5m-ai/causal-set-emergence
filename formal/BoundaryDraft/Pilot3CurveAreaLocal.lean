import BoundaryDraft.Pilot3CurveArea
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Local curve area and signed integration

Only local C¹ regularity is used for the area law. Actual derivative densities
and restricted measures agree on every overlap; a countable open cover glues
the local representatives. This is the canonical spatial one-measure, not an
atlas-defined replacement.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

private theorem pilot3_exists_contDiff_extension {g : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (x : ℝ) (hx : x ∈ U) :
    ∃ (k : ℝ → ℝ) (r : ℝ), ContDiff ℝ 1 k ∧ 0 < r ∧ ball x r ⊆ U ∧ EqOn k g (ball x r) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let k : ℝ → ℝ := fun y => b y * g y
  have hsupp : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [b]; linarith)).trans hRU
  refine ⟨k, R / 4, ?_, by positivity, (ball_subset_ball (by linarith)).trans hRU, ?_⟩
  · apply contDiff_iff_contDiffAt.2
    intro y
    by_cases hy : y ∈ tsupport b
    · exact b.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hsupp hy)))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [not_mem_tsupport_iff_eventuallyEq.1 hy] with z hz
      change b z * g z = 0
      simp [hz]
  · intro y hy
    change b y * g y = g y
    rw [b.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]

theorem pilot3CurvePullback_restrict_congr {g k : ℝ → ℝ}
    (hg : Continuous g) (hk : Continuous k) (V : Set ℝ) (he : EqOn g k V) :
    (pilot3CurvePullback g).restrict V = (pilot3CurvePullback k).restrict V := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    pilot3CurvePullback_apply hg, pilot3CurvePullback_apply hk]
  congr 1
  apply image_congr
  intro x hx
  simp only [pilot3Curve, he hx.2]

theorem pilot3CurvePullback_restrict_eq_withDensity {g : ℝ → ℝ}
    (hg : Continuous g) (U : Set ℝ) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) :
    (pilot3CurvePullback g).restrict U =
      (volume.restrict U).withDensity (fun u => ENNReal.ofReal (pilot3CurveJacobian g u)) := by
  have hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      (pilot3CurvePullback g).restrict (ball x r) =
        (volume.withDensity (fun u => ENNReal.ofReal (pilot3CurveJacobian g u))).restrict (ball x r) := by
    intro x hx
    obtain ⟨k, r, hk, hr, hsub, he⟩ := pilot3_exists_contDiff_extension hU hgU x hx
    refine ⟨r, hr, hsub, ?_⟩
    rw [pilot3CurvePullback_restrict_congr hg hk.continuous _ he.symm,
      pilot3CurvePullback_eq_withDensity hk, restrict_withDensity measurableSet_ball,
      restrict_withDensity measurableSet_ball]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have he' : k =ᶠ[𝓝 y] g := mem_of_superset (isOpen_ball.mem_nhds hy) fun z hz => he hz
    simp only [pilot3CurveJacobian, he'.fderiv_eq]
  choose! r hr hsub heq using hlocal
  obtain ⟨t, htU, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (fun x hx => nhdsWithin_le_nhds (ball_mem_nhds x (hr x hx)))
  have hUnion : (⋃ x ∈ t, ball x (r x)) = U :=
    Subset.antisymm (iUnion₂_subset fun x hx => hsub x (htU hx)) hcover
  rw [← restrict_withDensity hU.measurableSet, ← hUnion]
  exact (Measure.restrict_biUnion_congr htc).2 fun x hx => heq x (htU hx)

/-- Intrinsic spatial curve area on every measurable subset of the local domain. -/
theorem pilot3_hausdorff_restrict_curve_image_of_contDiffOn {g : ℝ → ℝ}
    (hg : Continuous g) (U : Set ℝ) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U)
    (s : Set ℝ) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    (μH[1] : Measure Pilot3Space).restrict (pilot3Curve g '' s) =
      Measure.map (pilot3Curve g) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (pilot3CurveJacobian g u))) := by
  have he := pilot3CurvePullback_restrict_eq_withDensity hg U hU hgU
  rw [← restrict_withDensity hU.measurableSet] at he
  have he' := Measure.restrict_congr_mono hsU he
  rw [restrict_withDensity hs] at he'
  rw [← he']
  let hf := continuous_measurableEmbedding_pilot3Curve hg
  have hm := hf.restrict_map (pilot3CurvePullback g) (pilot3Curve g '' s)
  change (Measure.map (pilot3Curve g) (Measure.comap (pilot3Curve g) (μH[1] : Measure Pilot3Space))).restrict
    (pilot3Curve g '' s) = _ at hm
  rw [hf.map_comap, hf.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range _ _)] at hm
  exact hm

/-- Signed integration with the ACTUAL variable speed and canonical one-measure. -/
theorem pilot3_integral_curve_of_contDiffOn {g : ℝ → ℝ}
    (hg : Continuous g) (U : Set ℝ) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U)
    (F : Pilot3Space → ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    (∫ y in pilot3Curve g '' s, F y ∂(μH[1] : Measure Pilot3Space)) =
      ∫ u in s, pilot3CurveJacobian g u * F (pilot3Curve g u) := by
  rw [pilot3_hausdorff_restrict_curve_image_of_contDiffOn hg U hU hgU s hs hsU,
    (continuous_measurableEmbedding_pilot3Curve hg).integral_map,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_pilot3CurveJacobian g).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    rw [ENNReal.toReal_ofReal (pilot3CurveJacobian_pos g u).le, smul_eq_mul]

theorem pilot3_integrable_curve_iff_of_contDiffOn {g : ℝ → ℝ}
    (hg : Continuous g) (U : Set ℝ) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U)
    (F : Pilot3Space → ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    IntegrableOn F (pilot3Curve g '' s) (μH[1] : Measure Pilot3Space) ↔
      IntegrableOn (fun u => pilot3CurveJacobian g u * F (pilot3Curve g u)) s := by
  unfold IntegrableOn
  rw [pilot3_hausdorff_restrict_curve_image_of_contDiffOn hg U hU hgU s hs hsU,
    (continuous_measurableEmbedding_pilot3Curve hg).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (measurable_pilot3CurveJacobian g).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (pilot3CurveJacobian_pos g _).le, smul_eq_mul, Function.comp_apply]

end BoundaryDraft
