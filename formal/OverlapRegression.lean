import BoundaryDraft

/-!
# Independent exact-overlap regressions

These restate the finite-density contract, calibrate the full signed kernel,
shear and null Jacobians, and identify the new expression with both existing
exact base-case reductions. No limit or density-regularity premise is added.
-/

open BoundaryDraft MeasureTheory Set
open scoped ENNReal Topology Classical

noncomputable section

-- The complete action and both density factors, at every positive density.
example {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (ρ : ℝ) (_hρ : 0 < ρ) :
    continuumMean ρ M = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real M - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          ∫ x, M.indicator (fun _ => (1 : ℝ)) x * M.indicator (fun _ => (1 : ℝ)) (x + z)) := by
  rw [continuumMean_eq_translatedOverlap hm hb]
  simp_rw [translatedOverlap_eq_indicator M hm]

-- Probability interpretation additionally requires causal convexity.
example {M : Set Spacetime} (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ M = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real M - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) * translatedOverlap M z) := by
  rw [hM.expectedBDGAction_eq hρ, continuumMean_eq_translatedOverlap hM.measurable hM.bounded]

-- This kernel has not been replaced by its absolute value or positive part.
example : bdgKernel 1 < 0 := by
  have he := Real.exp_pos (-1)
  norm_num [bdgKernel, bdgPolynomial]
  nlinarith

example : (displacementMatrix (Fin 4)).det = 1 := det_displacementMatrix _

example (x z : Spacetime) : x + z ∈ causalFuture x ↔ z ∈ causalFuture 0 :=
  add_mem_causalFuture_iff x z

-- Unscaled null coordinates: at (u,v)=(1,3), Q=3 and radial Jacobian=1/2.
example (ω : OverlapSphere) :
    intervalSq 0 (Fin.cons 2 (spatialPolar ω 1)) = 3 := by
  convert radialNull_intervalSq 1 3 ω using 1 <;> norm_num

example : |radialNullMatrix.det| * ((3-1)/2)^2 = (1 : ℝ)/2 := by
  norm_num [det_radialNullMatrix]

example : (properTimeRadialDerivative ![3,3]).det = (1 : ℝ)/6 := by
  rw [det_properTimeRadialDerivative]
  norm_num

example : overlapSphereMeasure.real univ = 4 * Real.pi := overlapSphere_mass

-- The null boundary and macroscopic future displacements are not excised.
example (ω : OverlapSphere) : Fin.cons 2 (spatialPolar ω 2) ∈ longFuture 1 := by
  rw [polar_mem_longFuture ω (by norm_num)]
  norm_num [longRadialDomain]

example (ω : OverlapSphere) : intervalSq 0 (Fin.cons 2 (spatialPolar ω 2)) = 0 := by
  convert radialNull_intervalSq 0 4 ω using 1 <;> norm_num

-- Empty and genuinely nonempty zero-volume regions are included.
example (z : Spacetime) : translatedOverlap ∅ z = 0 := translatedOverlap_empty z

example (p z : Spacetime) : translatedOverlap {p} z = 0 :=
  translatedOverlap_zero_of_volume_zero (measure_singleton p) z

example (p : Spacetime) (δ σ : ℝ) : longOverlapDensity {p} δ σ = 0 :=
  longOverlapDensity_zero_of_volume_zero (measure_singleton p) δ σ

-- The actual density is measurable, bounded, compactly supported and integrable.
example {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    {δ : ℝ} (hδ : 0 < δ) :
    Measurable (longOverlapDensity M δ) ∧ HasCompactSupport (longOverlapDensity M δ) ∧
      Integrable (longOverlapDensity M δ) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |longOverlapDensity M δ σ| ≤ C :=
  ⟨measurable_longOverlapDensity hm δ, hasCompactSupport_longOverlapDensity hb hδ,
    integrable_longOverlapDensity hm hb hδ, bounded_longOverlapDensity hm hb hδ⟩

example {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    Integrable (fun σ => bdgKernel ((Real.pi/24)*ρ*σ^2) * longOverlapDensity M δ σ) ∧
      (∫ z in longFuture δ, bdgKernel ((Real.pi/24)*ρ*intervalSq 0 z^2) * translatedOverlap M z) =
        ∫ σ, bdgKernel ((Real.pi/24)*ρ*σ^2) * longOverlapDensity M δ σ := by
  refine ⟨integrable_longOverlapDensity_weight hm hb hδ
    (fun σ => bdgKernel ((Real.pi/24)*ρ*σ^2)) ?_, integral_longOverlap_bdg hm hb hδ ρ⟩
  unfold bdgKernel bdgPolynomial
  fun_prop

-- Calibrate against the original unequal-axis ellipsoid finite-density formula.
example (ρ : ℝ) (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (graphCapRegion (ellipsoidProfile (1/4) ![1,2,3])) - ρ *
        ∫ z in causalFuture 0, bdgKernel ((Real.pi/24)*ρ*intervalSq 0 z^2) *
          translatedOverlap (graphCapRegion (ellipsoidProfile (1/4) ![1,2,3])) z) =
      ∫ x in {x | 0 < ellipsoidProfile (1/4) ![1,2,3] x},
        planeKernel ρ (ellipsoidProfile (1/4) ![1,2,3] x) := by
  have ha : (0 : ℝ) < 1/4 := by norm_num
  have hb : ∀ i : Fin 3, 2*(1/4 : ℝ) < (![1,2,3] : Spatial) i := by
    intro i
    fin_cases i <;> norm_num
  have hh := ellipsoid_graphCapData (1/4) ![1,2,3] ha hb
  rw [← continuumMean_eq_translatedOverlap hh.measurableSet_cap hh.isBounded_cap]
  exact ellipsoid_graphReduction _ _ ha hb ρ hρ

-- Independently calibrate the existing null-cap Gaussian cancellation at T=2,a=1.
example (ρ : ℝ) (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (nullCapRegion 2 1) - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi/24)*ρ*intervalSq 0 z^2) * translatedOverlap (nullCapRegion 2 1) z) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ x in nullCapRegion 2 1,
        Real.exp (-(Real.pi/24)*ρ*intervalSq x 0^2) := by
  rw [← continuumMean_eq_translatedOverlap (measurableSet_nullCapRegion 2 1)
    (isBounded_nullCapRegion 2 1 (by norm_num))]
  exact nullCap_continuumMean_eq_spacetimeGaussian 2 1 ρ (by norm_num) (by norm_num) hρ

-- Compatibility uses the original positive-part envelope, not a raw Lipschitz premise.
example {h : Spatial → ℝ} (hh : GraphCapData h) {s : ℝ} {a : Spatial}
    (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (graphCapRegion h) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (max 0 (h x) - s) := hh.translatedOverlap_causal hz

-- The separate two-graph subclass has precisely the advertised positive-part fibre.
example {lower upper : Spatial → ℝ} (hl : StrictGraphLipschitz lower)
    (hu : StrictGraphLipschitz upper) (hb : Bornology.IsBounded (twoGraphRegion lower upper))
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoGraphRegion lower upper) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (upper (x+a)-s-lower x) :=
  translatedOverlap_twoGraph_causal hl hu hb hz
