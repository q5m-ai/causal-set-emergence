import BoundaryDraft

/-!
Independent checks of the actual two-face region, strata, causal overlap,
fixed-cutoff density, and unchanged probability law. No area or limit goal is
assumed. Planar, genuinely curved, critical-height, and empty cases are kept.
-/

open BoundaryDraft MeasureTheory Set
open scoped Topology

noncomputable section
namespace TwoFaceGeometryRegression

-- Restate the complete original goal, rather than merely checking its name.
example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) :
    IsOpen (twoFaceRegion h f) ∧ BoundedCausalRegion (twoFaceRegion h f) ∧
    IsCompact (twoFacePast h f) ∧ IsCompact (twoFaceFuture h f) ∧
    IsCompact (twoFaceJoint h f) ∧
    frontier (twoFaceRegion h f) = twoFacePast h f ∪ twoFaceFuture h f ∧
    twoFacePast h f ∩ twoFaceFuture h f = twoFaceJoint h f :=
  twoFaceRegionGoal h f hf

-- Ambient interval containment, including null-related intermediate points.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (p q r : Spacetime)
    (hp : f (spatialPart p) - h (spatialPart p) < p 0 ∧ p 0 < f (spatialPart p))
    (hr : f (spatialPart r) - h (spatialPart r) < r 0 ∧ r 0 < f (spatialPart r))
    (hpq : q ∈ causalFuture p) (hqr : r ∈ causalFuture q) :
    f (spatialPart q) - h (spatialPart q) < q 0 ∧ q 0 < f (spatialPart q) :=
  hf.causallyConvex_region p hp r hr ⟨hpq, hqr⟩

-- The closure uses the actual closed positive region, not all raw zeros.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (p : Spacetime) :
    p ∈ closure (twoFaceRegion h f) ↔
      (WithLp.equiv 2 _).symm (spatialPart p) ∈ closure {x : JointSpace | 0 < h x} ∧
      f (spatialPart p) - h (spatialPart p) ≤ p 0 ∧ p 0 ≤ f (spatialPart p) :=
  hf.mem_closure_region p

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    StrictGraphLipschitz (fun x => f x - max 0 (h x)) ∧ StrictGraphLipschitz f ∧
    twoGraphRegion (fun x => f x - max 0 (h x)) f = twoFaceRegion h f :=
  ⟨hf.strictGraphLipschitz_lower, hf.strictGraphLipschitz_upper,
    (twoFaceRegion_eq_twoGraphRegion h f).symm⟩

-- Macroscopic null displacement: t=2, spatial vector=(2,0,0).
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    intervalSq 0 ![2, 2, 0, 0] = 0 ∧
    translatedOverlap (twoFaceRegion h f) ![2, 2, 0, 0] =
      ∫ x : Spatial, max 0 (f (x + ![2, 0, 0]) - 2 - (f x - max 0 (h x))) := by
  constructor
  · norm_num [intervalSq, spatialSeparationSq, Fin.sum_univ_succ]
  · exact hf.translatedOverlap_causal (by
      change (![2, 2, 0, 0] : Spacetime) ∈ causalFuture 0
      norm_num [causalFuture, spatialSeparationSq, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three])

-- At the vertex the spatial fibre recovers the full height volume.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    translatedOverlap (twoFaceRegion h f) 0 = ∫ x : Spatial, max 0 (h x) := by
  have he := hf.translatedOverlap_causal (s := 0) (a := 0) (by simp [causalFuture, spatialSeparationSq])
  have hz : (Fin.cons 0 (0 : Spatial) : Spacetime) = 0 := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  simpa only [hz, add_zero, sub_zero, sub_sub_cancel,
    max_eq_right (le_max_left (0 : ℝ) _)] using he

-- Full signed kernel; neither its negative part nor either density factor is lost.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteBDGAction ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        (volume.real (twoFaceRegion h f) - ρ * ∫ z in causalFuture 0,
          bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
            ∫ x : Spatial, max 0 (f (x + spatialPart z) - z 0 - (f x - max 0 (h x)))) :=
  hf.expectedBDGAction_eq_graphOverlap hρ

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (longOverlapDensity (twoFaceRegion h f) δ) ∧
    HasCompactSupport (longOverlapDensity (twoFaceRegion h f) δ) ∧
    Integrable (longOverlapDensity (twoFaceRegion h f) δ) ∧
    (∀ σ, longOverlapDensityENN (twoFaceRegion h f) δ σ < ⊤) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |longOverlapDensity (twoFaceRegion h f) δ σ| ≤ C :=
  ⟨hf.measurable_longOverlapDensity δ, hf.hasCompactSupport_longOverlapDensity hδ,
    hf.integrable_longOverlapDensity hδ, hf.longOverlapDensityENN_lt_top hδ,
    hf.bounded_longOverlapDensity hδ⟩

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    Integrable (fun σ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) *
      longOverlapDensity (twoFaceRegion h f) δ σ) ∧
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ, bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) * longOverlapDensity (twoFaceRegion h f) δ σ := by
  refine ⟨hf.integrable_longOverlapDensity_weight hδ _ ?_, hf.integral_longOverlap_bdg hδ ρ⟩
  unfold bdgKernel bdgPolynomial
  fun_prop

-- EVERY original planar cap is retained, with the old exact finite-density value.
example {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (twoFaceRegion h (fun _ => 0)) =
      ∫ x in {x | 0 < h x}, planeKernel ρ (h x) := by
  rw [hh.twoFace_planar.expectedBDGAction_eq hρ, twoFaceRegion_planar]
  exact hh.graphReduction ρ hρ

example {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) {s : ℝ} {a : Spatial}
    (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoFaceRegion h (fun _ => 0)) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (max 0 (h x) - s) := by
  rw [hh.twoFace_planar.translatedOverlap_causal hz]
  congr 1
  ext x
  congr 1
  ring

-- The contract's nonempty future face remains genuinely curved on the region.
theorem curved_geometry : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c)).Nonempty ∧
    BoundedCausalRegion (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c)) ∧
    frontier (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c)) =
      twoFacePast (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∪
      twoFaceFuture (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 := by
  obtain ⟨c, hc, hf, _, hn⟩ := twoFace_curved_nonvacuity
  refine ⟨c, hc, hf, ?_, hf.boundedCausalRegion, hf.frontier_region, hn⟩
  exact ⟨Fin.cons (-1 / 8) 0, by
    norm_num [twoFaceRegion, spatialPart_cons, twoFaceSine, ellipsoidProfile]⟩

-- An independently checked positive-height critical point remains allowed,
-- even with a curved future face. No global nonvanishing field is introduced.
def quartic : Spatial → ℝ := dampedEllipsoidProfile (1 / 4) (fun _ => 1)

theorem quartic_critical : quartic 0 = 3 / 16 ∧
    fderiv ℝ (fun x : JointSpace => quartic x) 0 = 0 := by
  constructor
  · norm_num [quartic, dampedEllipsoidProfile, ellipsoidProfile]
  · have hd := (hasGradientAt_ellipsoidProfile (1 / 4) (fun _ => 1) 0).hasFDerivAt
    have hz : ellipsoidGradient (1 / 4) (fun _ => 1) 0 = 0 := by
      ext i
      simp [ellipsoidGradient]
    have hg := hd.sub ((hasDerivAt_pow 2 (ellipsoidProfile (1 / 4) (fun _ => 1) 0)).comp_hasFDerivAt 0 hd)
    calc
      _ = _ := hg.fderiv
      _ = 0 := by rw [hz]; simp

example : ∃ c : ℝ, 0 < c ∧ AdmissibleTwoFace quartic (twoFaceSine c) ∧
    BoundedCausalRegion (twoFaceRegion quartic (twoFaceSine c)) ∧
    (∀ ρ : ℝ, 0 < ρ → expectedBDGAction ρ (twoFaceRegion quartic (twoFaceSine c)) =
      continuumMean ρ (twoFaceRegion quartic (twoFaceSine c))) ∧
    quartic 0 = 3 / 16 ∧ fderiv ℝ (fun x : JointSpace => quartic x) 0 = 0 := by
  have hh : AdmissibleGraphCap quartic :=
    dampedEllipsoid_admissible _ _ (by norm_num) (by norm_num) (fun _ => by norm_num)
  obtain ⟨c, hc, hf⟩ := hh.exists_twoFace_sine
  exact ⟨c, hc, hf, hf.boundedCausalRegion, fun _ hρ => hf.expectedBDGAction_eq hρ, quartic_critical⟩

-- The all-zero height is genuinely admissible: regular-zero obligations are
-- vacuous on its empty closed positive set, despite a huge raw zero set.
theorem zero_admissible : AdmissibleTwoFace (fun _ => 0) (fun _ => 0) := by
  apply AdmissibleGraphCap.twoFace_planar
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · exact ⟨0, le_rfl, zero_lt_one, by simp⟩
  · intro x _
    exact contDiffAt_const
  · simp
  · simp

theorem zero_region : twoFaceRegion (fun _ => 0) (fun _ => 0) = ∅ := by
  ext p
  change (0 - 0 < p 0 ∧ p 0 < 0) ↔ False
  constructor
  · rintro ⟨hp, hn⟩
    linarith
  · exact False.elim

example : frontier (twoFaceRegion (fun _ => 0) (fun _ => 0)) = ∅ ∧
    twoFacePast (fun _ => 0) (fun _ => 0) = ∅ ∧
    twoFaceFuture (fun _ => 0) (fun _ => 0) = ∅ ∧
    twoFaceJoint (fun _ => 0) (fun _ => 0) = ∅ := by
  rw [zero_region]
  simp [twoFacePast, twoFaceFuture, twoFaceJoint, graphJoint, graphClosedPositive]

example {ρ : ℝ} (hρ : 0 < ρ) (δ σ : ℝ) :
    expectedBDGAction ρ (twoFaceRegion (fun _ => 0) (fun _ => 0)) = 0 ∧
    longOverlapDensity (twoFaceRegion (fun _ => 0) (fun _ => 0)) δ σ = 0 := by
  constructor
  · rw [zero_admissible.expectedBDGAction_eq hρ, zero_region]
    simp [continuumMean]
  · rw [zero_region]
    exact longOverlapDensity_zero_of_volume_zero (measure_empty) δ σ

-- An exterior zero is not an extra joint or frontier point, for ANY admissible
-- raw profile, irrespective of its behavior outside the closed positive set.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (x : JointSpace)
    (_hz : h x = 0) (hx : x ∉ graphClosedPositive h) :
    twoFaceLift f x ∉ closure (twoFaceRegion h f) ∧ twoFaceLift f x ∉ twoFaceJoint h f := by
  constructor
  · intro hp
    exact hx ((hf.mem_closure_region _).mp hp).1
  · intro hp
    exact hx ((mem_twoFaceLift_image f (graphJoint h) _).mp hp).1.1

end TwoFaceGeometryRegression
