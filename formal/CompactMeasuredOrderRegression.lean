import BoundaryDraft.CompactTorus
import BoundaryDraft.SphereCircle
import BoundaryDraft.MeasuredOrderBDG4Compatibility
import Mathlib.Data.Real.Pi.Bounds

/-!
Independent compact-manifold contracts and negative controls. These regressions
use the actual quotient/angular distances, original law and finite order layers.
There is no continuum-limit assertion.
-/

open BoundaryDraft MeasureTheory Set Metric
open scoped ENNReal Classical
noncomputable section
namespace CompactMeasuredOrderRegression

local instance : Fact (0 < (20 : ℝ)) := ⟨by norm_num⟩

/-- Exactly one ordered pair, not a symmetric pair counted twice. -/
theorem two_point_link {X : Type*} [MeasurableSpace X] (O : MeasuredOrder X)
    (x y : X) (hxy : O.Rel x y) (hne : x ≠ y) : O.layer 0 (x ::ₘ y ::ₘ 0) = 1 := by
  have hyx : ¬ O.Rel y x := fun h => hne (O.order.le_antisymm _ _ hxy h)
  simp [MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum, MeasuredOrder.intervalCount,
    FiniteConfiguration.count_cons, MeasuredOrder.interval, hne, hne.symm, hxy, hyx]

/-- A three-chain has two links and one one-point interval. -/
theorem three_point_layers {X : Type*} [MeasurableSpace X] (O : MeasuredOrder X)
    (x y z : X) (hxy : O.Rel x y) (hyz : O.Rel y z)
    (h12 : x ≠ y) (h23 : y ≠ z) (h13 : x ≠ z) :
    O.layer 0 (x ::ₘ y ::ₘ z ::ₘ 0) = 2 ∧
    O.layer 1 (x ::ₘ y ::ₘ z ::ₘ 0) = 1 ∧
    O.layer 2 (x ::ₘ y ::ₘ z ::ₘ 0) = 0 ∧
    O.layer 3 (x ::ₘ y ::ₘ z ::ₘ 0) = 0 := by
  have hxz := O.order.le_trans _ _ _ hxy hyz
  have h21 : ¬ O.Rel y x := fun h => h12 (O.order.le_antisymm _ _ hxy h)
  have h32 : ¬ O.Rel z y := fun h => h23 (O.order.le_antisymm _ _ hyz h)
  have h31 : ¬ O.Rel z x := fun h => h13 (O.order.le_antisymm _ _ hxz h)
  simp [MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum, MeasuredOrder.intervalCount,
    FiniteConfiguration.count_cons, MeasuredOrder.interval, h12, h12.symm, h23, h23.symm,
    h13, h13.symm, hxy, hyz, hxz, h21, h32, h31]

-- Both actual ambient spaces are standard Borel, and their geometric volumes
-- are finite and atomless, not hypotheses supplied by the regression.
example : StandardBorelSpace (ℝ × CompactTorus.Space 1) := CompactTorus.standardBorel 1
example : StandardBorelSpace (ℝ × SphereCircle.Space 20) := SphereCircle.standardBorel 20
example : CompactSpace (CompactTorus.Space 1) := CompactTorus.compactSpace 1
example : CompactSpace (SphereCircle.Space 20) := SphereCircle.compactSpace 20
example : IsFiniteMeasure (CompactTorus.slabVolume 1 (2 / 5)) := inferInstance
example : NoAtoms (CompactTorus.slabVolume 1 (2 / 5)) := inferInstance
example : IsFiniteMeasure (SphereCircle.slabVolume 20 4) := inferInstance
example : NoAtoms (SphereCircle.slabVolume 20 4) := inferInstance

example : CompactTorus.slabVolume 1 (2 / 5) univ = ENNReal.ofReal (2 / 5) := by
  rw [CompactTorus.slabVolume_univ]; norm_num

example : SphereCircle.slabVolume 20 4 univ = ENNReal.ofReal (320 * Real.pi) := by
  rw [SphereCircle.slabVolume_univ]; congr 1; ring

example : 0 < CompactTorus.slabVolume 1 (2 / 5) univ :=
  CompactTorus.slabVolume_pos 1 (by norm_num)
example : 0 < SphereCircle.slabVolume 20 4 univ := SphereCircle.slabVolume_pos 20 (by norm_num)

-- Explicit positive-density contracts retain the actual restricted intervals.
example {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteDimensionAction (CompactTorus.measuredOrder 1) 4 ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • CompactTorus.slabVolume 1 (2 / 5))) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ((CompactTorus.slabVolume 1 (2 / 5) univ).toReal - ρ *
          ∫ x, ∫ y in {y | (CompactTorus.measuredOrder 1).Rel x y}, bdgKernel
            (ρ * (CompactTorus.slabVolume 1 (2 / 5)
              ((CompactTorus.measuredOrder 1).interval x y)).toReal)
            ∂CompactTorus.slabVolume 1 (2 / 5) ∂CompactTorus.slabVolume 1 (2 / 5)) := by
  rw [MeasuredOrderBDG4.expectation_eq _ _ hρ, MeasuredOrderBDG4.action_eq]

example {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteDimensionAction (SphereCircle.measuredOrder 20) 4 ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • SphereCircle.slabVolume 20 4)) =
      MeasuredOrderBDG4.action (SphereCircle.measuredOrder 20) (SphereCircle.slabVolume 20 4) ρ :=
  SphereCircle.expectation_eq 20 4 hρ

/-- Nontrivial finite-density law, including the actual geometric mass. -/
theorem torus_card_probability {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    CompactTorus.probability 1 (2 / 5) ρ {c | c.card = k} =
      ENNReal.ofReal (Real.exp (-(ρ * (2 / 5))) * (ρ * (2 / 5)) ^ k / k.factorial) := by
  rw [show {c : Multiset (ℝ × CompactTorus.Space 1) | c.card = k} =
    {c | FiniteConfiguration.count univ c = k} by simp,
    Ultrastatic.count_probability _ _ _ MeasurableSet.univ]
  change ENNReal.ofReal (ProbabilityTheory.poissonPMFReal _ k) = _
  simp only [ProbabilityTheory.poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ.le, Ultrastatic.slabVolume_univ, CompactTorus.spatialVolume_univ]
  norm_num

/-- A one-point sample has positive probability, so the instance is not a
zero-volume/empty-law specialization. -/
example {ρ : ℝ} (hρ : 0 < ρ) :
    0 < CompactTorus.probability 1 (2 / 5) ρ {c | c.card = 1} := by
  rw [torus_card_probability hρ]
  apply ENNReal.ofReal_pos.mpr
  positivity

/-- First and second factorial moments retain one and TWO intensity factors. -/
example (ρ : ℝ) :
    (∫⁻ c : Multiset (ℝ × SphereCircle.Space 20), (c.card : ℝ≥0∞)
      ∂SphereCircle.probability 20 4 ρ) = ENNReal.ofReal ρ * ENNReal.ofReal (320 * Real.pi) := by
  rw [FinitePoisson.lintegral_card, Measure.smul_apply, smul_eq_mul, SphereCircle.slabVolume_univ]
  congr 2
  ring

example (ρ : ℝ) :
    (∫⁻ c : Multiset (ℝ × SphereCircle.Space 20), ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞)
      ∂SphereCircle.probability 20 4 ρ) =
      (ENNReal.ofReal ρ * ENNReal.ofReal (320 * Real.pi)) ^ 2 := by
  rw [FinitePoisson.lintegral_pairCard]
  simp only [Measure.smul_apply, smul_eq_mul, SphereCircle.slabVolume_univ,
    show (4 : ℝ) * (4 * Real.pi * 20) = 320 * Real.pi by ring, pow_two]

example : Measurable (fun p : ℝ × ((ℝ × SphereCircle.Space 20) × (ℝ × SphereCircle.Space 20)) =>
    bdgKernel (p.1 * (SphereCircle.slabVolume 20 4
      ((SphereCircle.measuredOrder 20).interval p.2.1 p.2.2)).toReal)) :=
  MeasuredOrderBDG4.measurable_kernel _ _

example (ρ : ℝ) : Integrable (MeasuredOrderBDG4.discreteAction (SphereCircle.measuredOrder 20) ρ)
    (SphereCircle.probability 20 4 ρ) := MeasuredOrderBDG4.integrable_discreteAction _ _ _

example {x y : ℝ × SphereCircle.Space 20}
    (hx : x ∈ SphereCircle.slab 20 4) (hy : y ∈ SphereCircle.slab 20 4) :
    SphereCircle.slabVolume 20 4 ((SphereCircle.measuredOrder 20).interval x y) =
      (volume.prod (SphereCircle.spatialVolume 20))
        (Ultrastatic.closedInterval (SphereCircle.spatialDistance 20) x y) :=
  SphereCircle.intervalVolume_ambient _ hx hy

example : IsCompact (closure (CompactTorus.slab 1 (2 / 5))) :=
  Ultrastatic.isCompact_closure_slab _
example : IsCompact (closure (SphereCircle.slab 20 4)) := Ultrastatic.isCompact_closure_slab _

-- A null three-chain in the selected thin torus slab.
def torusPoint (r : ℝ) : ℝ × CompactTorus.Space 1 := (r, (r, 0, 0))

theorem torusPoint_distance {r s : ℝ} (h : |r - s| ≤ 1 / 2) :
    (CompactTorus.spatialDistance 1).distance (torusPoint r).2 (torusPoint s).2 = |r - s| := by
  have hd : dist (r : AddCircle (1 : ℝ)) (s : AddCircle (1 : ℝ)) = |r - s| := by
    rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
    apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
    simpa using h
  rw [CompactTorus.distance_eq]
  simp [torusPoint, hd, Real.sqrt_sq_eq_abs]

theorem torusPoint_rel {r s : ℝ} (h : |r - s| ≤ 1 / 2) (hrs : r ≤ s) :
    (CompactTorus.measuredOrder 1).Rel (torusPoint r) (torusPoint s) := by
  change (CompactTorus.spatialDistance 1).distance _ _ ≤ s - r
  rw [torusPoint_distance h, abs_of_nonpos (sub_nonpos.mpr hrs)]
  linarith

theorem torusPoint_ne {r s : ℝ} (h : r ≠ s) : torusPoint r ≠ torusPoint s :=
  fun e => h (congrArg Prod.fst e)

def torusChain := torusPoint (-1 / 10) ::ₘ torusPoint 0 ::ₘ torusPoint (1 / 10) ::ₘ 0

example : (CompactTorus.measuredOrder 1).layer 0
    (torusPoint (-1 / 10) ::ₘ torusPoint (1 / 10) ::ₘ 0) = 1 :=
  two_point_link _ _ _ (torusPoint_rel (by norm_num [abs_div]) (by norm_num))
    (torusPoint_ne (by norm_num))

example : ¬ (CompactTorus.measuredOrder 1).Rel (torusPoint (1 / 10)) (torusPoint (-1 / 10)) := by
  intro h
  have ht := Ultrastatic.time_le _ h
  norm_num [torusPoint] at ht

/-- Both selected endpoints are excluded, but the null-related midpoint is kept. -/
example : (CompactTorus.measuredOrder 1).intervalCount
    (torusPoint (-1 / 10)) (torusPoint (1 / 10)) torusChain = 1 := by
  have h12 := torusPoint_rel (r := -1 / 10) (s := 0) (by norm_num [abs_div]) (by norm_num)
  have h23 := torusPoint_rel (r := 0) (s := 1 / 10) (by norm_num [abs_div]) (by norm_num)
  have hm : torusPoint 0 ∈ (CompactTorus.measuredOrder 1).interval
      (torusPoint (-1 / 10)) (torusPoint (1 / 10)) :=
    ⟨⟨h12, h23⟩, by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨torusPoint_ne (by norm_num), torusPoint_ne (by norm_num)⟩⟩
  simp only [torusChain, MeasuredOrder.intervalCount, FiniteConfiguration.count_cons,
    FiniteConfiguration.count_zero, hm, MeasuredOrder.left_not_mem_interval,
    MeasuredOrder.right_not_mem_interval, if_true, if_false]

example {ρ : ℝ} (hρ : 0 < ρ) :
    MeasuredOrderBDG4.discreteAction (CompactTorus.measuredOrder 1) ρ torusChain =
      10 * bdgNormalization ρ := by
  obtain ⟨h0, h1, h2, h3⟩ := three_point_layers (CompactTorus.measuredOrder 1)
    (torusPoint (-1 / 10)) (torusPoint 0) (torusPoint (1 / 10))
    (torusPoint_rel (by norm_num [abs_div]) (by norm_num))
    (torusPoint_rel (by norm_num [abs_div]) (by norm_num))
    (torusPoint_ne (by norm_num)) (torusPoint_ne (by norm_num)) (torusPoint_ne (by norm_num))
  rw [MeasuredOrderBDG4.discreteAction_eq _ hρ]
  dsimp only [torusChain]
  rw [h0, h1, h2, h3]
  norm_num
  ring

/-- The third point is actually null-related, not an accidental timelike fixture. -/
example : (CompactTorus.spatialDistance 1).distance
    (torusPoint (-1 / 10)).2 (torusPoint (1 / 10)).2 =
      (torusPoint (1 / 10)).1 - (torusPoint (-1 / 10)).1 := by
  rw [torusPoint_distance (by norm_num [abs_div])]
  norm_num [torusPoint, abs_div]

example : ∀ x ∈ torusChain, x ∈ CompactTorus.slab 1 (2 / 5) := by
  simp [torusChain, torusPoint, CompactTorus.slab, Ultrastatic.slab]
  norm_num

/-- The source's and target's occurrences do not inflate their own interval. -/
example (c : Multiset (ℝ × CompactTorus.Space 1)) :
    (CompactTorus.measuredOrder 1).intervalCount (torusPoint 0) (torusPoint (1 / 10))
      (torusPoint 0 ::ₘ torusPoint (1 / 10) ::ₘ c) =
    (CompactTorus.measuredOrder 1).intervalCount (torusPoint 0) (torusPoint (1 / 10)) c :=
  MeasuredOrder.intervalCount_insert_endpoints _ _ _ _

/-- A seam-crossing displacement uses the SHORT quotient arc. -/
example : dist ((9 / 10 : ℝ) : AddCircle (1 : ℝ)) ((1 / 10 : ℝ) : AddCircle (1 : ℝ)) = 1 / 5 := by
  rw [CompactTorus.circle_distance_lifts]
  norm_num [round, Int.fract, Int.floor_eq_iff, abs_div]

/-- Two nonzero spatial components forbid the maximum-metric surrogate. -/
example : ¬ (CompactTorus.measuredOrder 1).Rel
    (0, (0, 0, 0)) (1 / 4, ((1 / 4 : ℝ), (1 / 4 : ℝ), 0)) := by
  have hd : dist (0 : AddCircle (1 : ℝ)) ((1 / 4 : ℝ) : AddCircle (1 : ℝ)) = 1 / 4 := by
    rw [dist_eq_norm, ← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_sub,
      (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr (by norm_num [abs_div])]
    norm_num [abs_div]
  change ¬ (CompactTorus.spatialDistance 1).distance _ _ ≤ _
  rw [CompactTorus.distance_eq]
  simp only [hd, dist_self, zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1 / 4) ^ 2 + (1 / 4) ^ 2)
  have hn := Real.sqrt_nonneg ((1 / 4 : ℝ) ^ 2 + (1 / 4) ^ 2)
  intro h
  nlinarith

-- The actual sphere antipode is present inside the selected width-four slab.
def north : RoundSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
def south : RoundSphere := ⟨-north.val, by simp [north]⟩

def focusPast : ℝ × SphereCircle.Space 20 := (-Real.pi / 2, north, 0)
def focusFuture : ℝ × SphereCircle.Space 20 := (Real.pi / 2, south, 0)

theorem focusing_distance :
    (SphereCircle.spatialDistance 20).distance focusPast.2 focusFuture.2 = Real.pi := by
  change Real.sqrt (RoundSphere.distance north south ^ 2 + dist (0 : AddCircle (20 : ℝ)) 0 ^ 2) = _
  rw [show RoundSphere.distance north south = Real.pi from RoundSphere.distance_antipode north]
  simp [Real.sqrt_sq Real.pi_pos.le]

example : focusPast ∈ SphereCircle.slab 20 4 ∧ focusFuture ∈ SphereCircle.slab 20 4 := by
  constructor <;> change _ ∈ Ioo (-4 / 2 : ℝ) (4 / 2) ×ˢ (univ : Set (SphereCircle.Space 20))
  all_goals simp only [mem_prod, mem_Ioo, mem_univ, and_true, focusPast, focusFuture]
  all_goals constructor <;> linarith [Real.pi_pos, Real.pi_lt_four]

theorem focusing_related : (SphereCircle.measuredOrder 20).Rel focusPast focusFuture := by
  change (SphereCircle.spatialDistance 20).distance focusPast.2 focusFuture.2 ≤ _
  rw [focusing_distance]
  dsimp [focusPast, focusFuture]
  linarith

/-- Chord distance would give two at the antipode; the actual value is pi. -/
example : (SphereCircle.spatialDistance 20).distance focusPast.2 focusFuture.2 ≠ 2 := by
  rw [focusing_distance]
  linarith [Real.pi_gt_three]

/-- Null antipodal pairs contribute one genuine ordered link. -/
example : (SphereCircle.measuredOrder 20).layer 0 (focusPast ::ₘ focusFuture ::ₘ 0) = 1 := by
  apply two_point_link _ _ _ focusing_related
  intro h
  have ht := congrArg Prod.fst h
  dsimp [focusPast, focusFuture] at ht
  linarith [Real.pi_pos]

-- Unchanged flat, conformal and dimensional baselines, including arbitrary multisets.
example {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset Spacetime) :
    MeasuredOrderBDG4.discreteAction MeasuredOrderBDG4.coordinateOrder ρ c = discreteBDGAction ρ c :=
  MeasuredOrderBDG4.coordinate_discreteAction hρ c

example (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) :
    MeasuredOrderBDG4.action MeasuredOrderBDG4.coordinateOrder ((conformalVolume Ω).restrict M) ρ =
      conformalAction Ω ρ M := MeasuredOrderBDG4.conformal_action Ω ρ M

example {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset (DimensionSpacetime 3)) :
    MeasuredOrderBDG4.discreteAction (dimensionMeasuredOrder 3) ρ c =
      discreteBDGAction ρ (c.map (dimensionSpacetimeCoordinates 3)) :=
  MeasuredOrderBDG4.dimension_discreteAction hρ c

end CompactMeasuredOrderRegression
