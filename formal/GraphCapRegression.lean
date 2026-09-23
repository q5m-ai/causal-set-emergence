import BoundaryDraft

/-!
# General graph-cap contract regressions

Restate the finite-density action independently of the goal alias. Check
complete slices with null points and the vertex, compact domination, the
original ellipsoid hypotheses, and a genuinely nonquadratic admissible cap
with a positive-height critical point. No collar or limit premise is used.
-/

open BoundaryDraft MeasureTheory Set
open scoped BigOperators

noncomputable section

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (graphCapRegion h) =
      ∫ x in {x | 0 < h x}, planeKernel ρ (h x) := hh.graphReduction ρ hρ

-- Smoothness and zero-level regularity are not used by the exact reduction.
example (h : Spatial → ℝ) (hh : GraphCapData h) : GraphReductionGoal h :=
  graphCap_graphReduction h hh

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    frontier {x | 0 < h x} = closure {x | 0 < h x} ∩ {x | h x = 0} :=
  hh.frontier_eq h

example (h : Spatial → ℝ) (hh : GraphCapData h) (ρ : ℝ) :
    IntegrableOn (fun x => planeKernel ρ (h x)) {x | 0 < h x} :=
  integrableOn_graphCap_profile h hh _ (continuous_planeKernel ρ)

example (h : Spatial → ℝ) (hh : GraphCapData h) (x : Spacetime)
    (hx : x ∈ graphCapRegion h) :
    graphCapRegion h ∩ causalFuture x = {y | y ∈ causalFuture x ∧ y 0 < 0} :=
  graphCap_complete_future h hh x hx

-- Even an equality in the causal quadratic inequality is retained.
example (h : Spatial → ℝ) (hh : GraphCapData h) (x y : Spacetime)
    (hx : x ∈ graphCapRegion h) (ht : x 0 ≤ y 0) (hy : y 0 < 0)
    (hnull : spatialSeparationSq x y = (y 0 - x 0) ^ 2) :
    y ∈ graphCapRegion h ∩ causalFuture x := by
  rw [graphCap_complete_future h hh x hx]
  exact ⟨⟨ht, hnull.le⟩, hy⟩

example (h : Spatial → ℝ) (hh : GraphCapData h) (x : Spacetime)
    (hx : x ∈ graphCapRegion h) : x ∈ graphCapRegion h ∩ causalFuture x := by
  rw [graphCap_complete_future h hh x hx]
  exact ⟨by simp [causalFuture, spatialSeparationSq], hx.2⟩

-- The original public concrete theorem and the general specialization agree.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    AdmissibleGraphCap (ellipsoidProfile a b) := ellipsoid_admissible a b ha hb

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    (ellipsoid_admissible a b ha hb).graphReduction = ellipsoid_graphReduction a b ha hb := rfl

namespace GraphCapRegression

def quarticProfile : Spatial → ℝ := dampedEllipsoidProfile (1 / 4) (fun _ => 1)

theorem quartic_admissible : AdmissibleGraphCap quarticProfile :=
  dampedEllipsoid_admissible _ _ (by norm_num) (by norm_num) (fun _ => by norm_num)

theorem quartic_reduction : GraphReductionGoal quarticProfile := quartic_admissible.graphReduction

-- The interior maximum is allowed to be a critical point, not removed.
theorem quartic_positive_critical :
    quarticProfile 0 = 3 / 16 ∧
      fderiv ℝ (fun x : JointSpace => quarticProfile x) 0 = 0 := by
  constructor
  · norm_num [quarticProfile, dampedEllipsoidProfile, ellipsoidProfile]
  · have hd := (hasGradientAt_ellipsoidProfile (1 / 4) (fun _ => 1) 0).hasFDerivAt
    have hz : ellipsoidGradient (1 / 4) (fun _ => 1) 0 = 0 := by
      ext i
      simp [ellipsoidGradient]
    have hg := hd.sub ((hasDerivAt_pow 2 (ellipsoidProfile (1 / 4) (fun _ => 1) 0)).comp_hasFDerivAt 0 hd)
    calc
      _ = _ := hg.fderiv
      _ = 0 := by rw [hz]; simp

-- A quadratic centered ellipsoid satisfies a linewise quadratic identity
-- which this quartic violates. This is not just a renamed ellipsoid example.
theorem quartic_not_ellipsoid (a : ℝ) (b : Fin 3 → ℝ) :
    quarticProfile ≠ ellipsoidProfile a b := by
  intro he
  have h0 := congrFun he 0
  have h1 := congrFun he ![1, 0, 0]
  have h2 := congrFun he ![2, 0, 0]
  have hquad : ellipsoidProfile a b ![2, 0, 0] =
      4 * ellipsoidProfile a b ![1, 0, 0] - 3 * ellipsoidProfile a b 0 := by
    simp [ellipsoidProfile, Fin.sum_univ_succ]
    ring
  rw [← h0, ← h1, ← h2] at hquad
  norm_num [quarticProfile, dampedEllipsoidProfile, ellipsoidProfile, Fin.sum_univ_succ] at hquad

-- A noncritical boundary band exists for the quartic, but necessarily stops
-- below its positive-height critical point. Thus this is not a hidden global
-- nonvanishing assumption.
theorem quartic_noncritical_band : ∃ δ : ℝ, 0 < δ ∧ δ < 3 / 16 ∧
    ∀ x ∈ graphClosedPositive quarticProfile, quarticProfile x ≤ δ →
      fderiv ℝ (fun y : JointSpace => quarticProfile y) x ≠ 0 := by
  obtain ⟨δ, hδ, hband⟩ := quartic_admissible.exists_noncritical_band
  refine ⟨δ, hδ, ?_, hband⟩
  by_contra hn
  have hx : (0 : JointSpace) ∈ graphClosedPositive quarticProfile := by
    apply subset_closure
    change 0 < quarticProfile 0
    rw [quartic_positive_critical.1]
    norm_num
  exact hband 0 hx (by simpa [quartic_positive_critical.1] using le_of_not_gt hn)
    quartic_positive_critical.2

end GraphCapRegression
