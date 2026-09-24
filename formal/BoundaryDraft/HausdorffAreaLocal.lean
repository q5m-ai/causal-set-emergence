import BoundaryDraft.HausdorffArea
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Localization of the graph area formula

C¹ regularity is needed only on the open parameter domain. Smooth cutoffs
extend each germ to a global C¹ graph; equality of restricted measures is
then glued over a countable cover. No regularity of the derivative outside
the chosen domain is required.
-/

open MeasureTheory Set Filter Metric Function
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- A C¹ function on an open set has a globally C¹ representative near each
point. The cutoff is zero before reaching any uncontrolled part of the domain. -/
theorem exists_contDiff_extension_near {g : SurfacePlane → ℝ} {U : Set SurfacePlane}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (x : SurfacePlane) (hx : x ∈ U) :
    ∃ (k : SurfacePlane → ℝ) (r : ℝ), ContDiff ℝ 1 k ∧ 0 < r ∧
      ball x r ⊆ U ∧ EqOn k g (ball x r) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let k : SurfacePlane → ℝ := fun y => b y * g y
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

/-- Equality of graph functions on an open patch gives equality of their area
measures and of the actual derivative densities on that patch. -/
theorem surfaceGraphPullbackMeasure_restrict_congr {g k : SurfacePlane → ℝ}
    (hg : Continuous g) (hk : Continuous k) (V : Set SurfacePlane)
    (he : EqOn g k V) :
    (surfaceGraphPullbackMeasure g).restrict V = (surfaceGraphPullbackMeasure k).restrict V := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    surfaceGraphPullbackMeasure_apply hg, surfaceGraphPullbackMeasure_apply hk]
  congr 2
  apply image_congr
  intro x hx
  simp only [surfaceGraph, he hx.2]

/-- Open-domain version of the variable-Jacobian pullback identity. Only
continuity, not differentiability, is required outside the open domain. -/
theorem surfaceGraphPullbackMeasure_restrict_eq_withDensity {g : SurfacePlane → ℝ}
    (hg : Continuous g) (U : Set SurfacePlane) (hU : IsOpen U)
    (hgU : ContDiffOn ℝ 1 g U) :
    (surfaceGraphPullbackMeasure g).restrict U =
      (volume.restrict U).withDensity (fun x => ENNReal.ofReal (surfaceGraphJacobian g x)) := by
  have hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      (surfaceGraphPullbackMeasure g).restrict (ball x r) =
        (volume.withDensity (fun y => ENNReal.ofReal (surfaceGraphJacobian g y))).restrict (ball x r) := by
    intro x hx
    obtain ⟨k, r, hk, hr, hsub, he⟩ := exists_contDiff_extension_near hU hgU x hx
    refine ⟨r, hr, hsub, ?_⟩
    rw [surfaceGraphPullbackMeasure_restrict_congr hg hk.continuous _ he.symm,
      surfaceGraphPullbackMeasure_eq_withDensity hk, restrict_withDensity measurableSet_ball,
      restrict_withDensity measurableSet_ball]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have he' : k =ᶠ[𝓝 y] g :=
      mem_of_superset (isOpen_ball.mem_nhds hy) fun z hz => he hz
    have hd : fderiv ℝ k y = fderiv ℝ g y := he'.fderiv_eq
    simp only [surfaceGraphJacobian, hd]
  choose! r hr hsub heq using hlocal
  obtain ⟨t, htU, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (fun x hx => nhdsWithin_le_nhds (ball_mem_nhds x (hr x hx)))
  have hUnion : (⋃ x ∈ t, ball x (r x)) = U := by
    exact Subset.antisymm (iUnion₂_subset fun x hx => hsub x (htU hx)) hcover
  rw [← restrict_withDensity hU.measurableSet, ← hUnion]
  exact (Measure.restrict_biUnion_congr htc).2 fun x hx => heq x (htU hx)

/-- The total derivative convention is measurable even outside its regular
set; the area formula still requires C¹ regularity on its domain. -/
theorem measurable_surfaceGraphJacobian (g : SurfacePlane → ℝ) :
    Measurable (surfaceGraphJacobian g) := by
  exact (measurable_const.add ((measurable_fderiv ℝ g).norm.pow_const 2)).sqrt

/-- Local graph area as a pushforward, for any measurable subset of the open
C¹ domain. -/
theorem normalizedHausdorffTwo_restrict_surfaceGraph_image_of_contDiffOn
    {g : SurfacePlane → ℝ} (hg : Continuous g) (U : Set SurfacePlane)
    (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) (s : Set SurfacePlane)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    normalizedHausdorffTwo.restrict (surfaceGraph g '' s) =
      Measure.map (surfaceGraph g)
        ((volume.restrict s).withDensity (fun x => ENNReal.ofReal (surfaceGraphJacobian g x))) := by
  have h := surfaceGraphPullbackMeasure_restrict_eq_withDensity hg U hU hgU
  rw [← restrict_withDensity hU.measurableSet] at h
  have h' := Measure.restrict_congr_mono hsU h
  rw [restrict_withDensity hs] at h'
  rw [← h']
  let hf := continuous_measurableEmbedding_surfaceGraph hg
  have hm := hf.restrict_map (surfaceGraphPullbackMeasure g) (surfaceGraph g '' s)
  rw [hf.injective.preimage_image] at hm
  change (Measure.map (surfaceGraph g) (Measure.comap (surfaceGraph g) normalizedHausdorffTwo)).restrict
    (surfaceGraph g '' s) = _ at hm
  rw [hf.map_comap, Measure.restrict_restrict_of_subset (image_subset_range _ _)] at hm
  exact hm

/-- Signed integration over a graph needs C¹ regularity only on the open
domain containing the measurable parameter set. -/
theorem integral_normalizedHausdorffTwo_surfaceGraph_of_contDiffOn
    {g : SurfacePlane → ℝ} (hg : Continuous g) (U : Set SurfacePlane)
    (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) (f : JointSpace → ℝ)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    (∫ y in surfaceGraph g '' s, f y ∂normalizedHausdorffTwo) =
      ∫ x in s, surfaceGraphJacobian g x * f (surfaceGraph g x) := by
  rw [normalizedHausdorffTwo_restrict_surfaceGraph_image_of_contDiffOn hg U hU hgU s hs hsU,
    (continuous_measurableEmbedding_surfaceGraph hg).integral_map,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_surfaceGraphJacobian g).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (surfaceGraphJacobian_pos g x).le, smul_eq_mul]

/-- Absolute integrability also localizes to the open C¹ domain. -/
theorem integrable_normalizedHausdorffTwo_surfaceGraph_iff_of_contDiffOn
    {g : SurfacePlane → ℝ} (hg : Continuous g) (U : Set SurfacePlane)
    (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) (f : JointSpace → ℝ)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    IntegrableOn f (surfaceGraph g '' s) normalizedHausdorffTwo ↔
      IntegrableOn (fun x => surfaceGraphJacobian g x * f (surfaceGraph g x)) s := by
  unfold IntegrableOn
  rw [normalizedHausdorffTwo_restrict_surfaceGraph_image_of_contDiffOn hg U hU hgU s hs hsU,
    (continuous_measurableEmbedding_surfaceGraph hg).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (measurable_surfaceGraphJacobian g).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (surfaceGraphJacobian_pos g _).le, smul_eq_mul,
    Function.comp_apply]

end BoundaryDraft
