import BoundaryDraft.SpacetimeSprinkling

/-!
# Independent finite-Poisson contracts and edge cases

These tests exercise the constructed probability measure, not assumed
point-process properties. No action or continuum-mean identity is asserted.
-/

open MeasureTheory ProbabilityTheory Set BoundaryDraft
open BoundaryDraft.FiniteConfiguration
open scoped BigOperators ENNReal Classical

noncomputable section

namespace PoissonRegression

/-- A nonempty four-dimensional unit box with unit intensity, independently
of the graph-cap and null-cap geometric hypotheses. -/
def unitBoxSprinkling : FiniteSprinkling where
  region := Set.pi univ (fun _ : Fin 4 => Icc (0 : ℝ) 1)
  measurable_region := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  finite_volume := by rw [volume_pi_pi]; norm_num
  density := 1
  density_pos := by norm_num

theorem unitBox_intensity : unitBoxSprinkling.intensity univ = 1 := by
  rw [FiniteSprinkling.intensity_apply _ MeasurableSet.univ]
  change ENNReal.ofReal 1 * volume (univ ∩ Set.pi univ (fun _ : Fin 4 => Icc (0 : ℝ) 1)) = 1
  rw [univ_inter, volume_pi_pi]
  norm_num

example : unitBoxSprinkling.probability {c | c.card = 0} = ENNReal.ofReal (Real.exp (-1)) := by
  have h := FinitePoisson.count_zero_probability unitBoxSprinkling.intensity MeasurableSet.univ
  simpa only [count_univ, unitBox_intensity, ENNReal.toReal_one] using h

/-- Empty regions at any positive density are legal inputs. -/
def emptySprinkling (ρ : ℝ) (hρ : 0 < ρ) : FiniteSprinkling where
  region := ∅
  measurable_region := MeasurableSet.empty
  finite_volume := by simp
  density := ρ
  density_pos := hρ

example (ρ : ℝ) (hρ : 0 < ρ) : IsProbabilityMeasure (emptySprinkling ρ hρ).probability :=
  inferInstance

example (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ c ∂(emptySprinkling ρ hρ).probability, c = 0 :=
  FiniteSprinkling.ae_empty_of_volume_zero _ (by simp [emptySprinkling])

/-- The empty-subset count has all its mass at zero, even in a nonempty region. -/
example (S : FiniteSprinkling) : S.probability {c | count ∅ c = 0} = 1 := by simp

example (S : FiniteSprinkling) : S.probability {c | count ∅ c = 1} = 0 := by simp

/-- Exact marginal law on a measurable piece of the region. -/
example (S : FiniteSprinkling) (A : Set Spacetime) (hA : MeasurableSet A)
    (hAM : A ⊆ S.region) (k : ℕ) :
    S.probability {c | count A c = k} =
      ENNReal.ofReal (Real.exp (-(S.density * (volume A).toReal)) *
        (S.density * (volume A).toReal) ^ k / k.factorial) := by
  simpa only [inter_eq_left.2 hAM] using S.count_probability hA k

/-- Exact independence check for two disjoint pieces, without positive-volume
assumptions on either piece. -/
example (S : FiniteSprinkling) (A B : Set Spacetime)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (k l : ℕ) :
    S.probability {c | count A c = k ∧ count B c = l} =
      poissonPMF (S.intensity A).toNNReal k * poissonPMF (S.intensity B).toNNReal l :=
  FinitePoisson.joint_count_probability S.intensity hA hB hAB k l

example (A B : Set Spacetime) (hAB : Disjoint A B) (c : Multiset Spacetime) :
    count (A ∪ B) c = count A c + count B c := count_disjoint_union hAB c

/-- Enumeration changes neither the configuration nor its observables. -/
example {n : ℕ} (v : Fin n → Spacetime) (e : Equiv.Perm (Fin n)) (A : Set Spacetime) :
    count A (ofTuple (v ∘ e)) = count A (ofTuple v) := by rw [ofTuple_perm]

example {n : ℕ} (v : Fin n → Spacetime) (e : Equiv.Perm (Fin n))
    (F : Spacetime → Spacetime → Multiset Spacetime → ℝ) :
    pairSum F (ofTuple (v ∘ e)) = pairSum F (ofTuple v) := by rw [ofTuple_perm]

/-- Multiplicities are retained before the almost-sure simplicity theorem. -/
example (x : Spacetime) : count {x} (x ::ₘ x ::ₘ 0) = 2 := by simp

/-- Distinct occurrences, not distinct locations: two coincident occurrences
have two ordered pairs. Such configurations are null under spacetime volume. -/
example (x : Spacetime) : pairSum (fun _ _ _ => (1 : ℝ≥0∞)) (x ::ₘ x ::ₘ 0) = 2 := by simp

example (S : FiniteSprinkling) : ∀ᵐ c ∂S.probability, c.Nodup := S.ae_nodup

example (S : FiniteSprinkling) : ∀ᵐ c ∂S.probability, ∀ x ∈ c, x ∈ S.region := S.ae_supported

/-- The singleton has no self-pair. -/
example (x : Spacetime) : pairSum (fun _ _ _ => (1 : ℝ≥0∞)) {x} = 0 := by simp

/-- The second factorial moment must not accidentally include the diagonal. -/
example (S : FiniteSprinkling) :
    (∫⁻ c : Multiset Spacetime, ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞) ∂S.probability) =
      S.intensity univ * S.intensity univ := FinitePoisson.lintegral_pairCard S.intensity

/-- Signed integration keeps negative pair contributions. -/
example (S : FiniteSprinkling) :
    (∫ c, pairSum (fun _ _ _ => (-1 : ℝ)) c ∂S.probability) =
      -((S.intensity univ).toReal * (S.intensity univ).toReal) := by
  rw [FiniteSprinkling.probability,
    FinitePoisson.integral_pairSum S.intensity (fun _ => measurable_const) 1
      (by norm_num) (by intros; norm_num)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_ofReal']

/-- A real point strictly between two time-axis endpoints is counted once. -/
example : intervalCount (timeAxis 0) (timeAxis 2)
    (timeAxis 0 ::ₘ timeAxis 1 ::ₘ timeAxis 2 ::ₘ 0) = 1 := by
  have h10 : timeAxis 1 ≠ timeAxis 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have h12 : timeAxis 1 ≠ timeAxis 2 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hi : timeAxis 1 ∈ causalIntervalInterior (timeAxis 0) (timeAxis 2) := by
    norm_num [causalIntervalInterior, causalInterval, causalPast, causalFuture,
      spatialSeparationSq, h10, h12]
  rw [Multiset.cons_swap (timeAxis 1) (timeAxis 2), intervalCount_insert_endpoints]
  simp [intervalCount, hi]

/-- Null-related intermediate points are retained; an open chronological
interval would incorrectly make this particular finite count zero. -/
example : intervalCount (timeAxis 0) (timeAxis 2) {![1, 1, 0, 0]} = 1 := by
  have h0 : (![1, 1, 0, 0] : Spacetime) ≠ timeAxis 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have h2 : (![1, 1, 0, 0] : Spacetime) ≠ timeAxis 2 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hi : (![1, 1, 0, 0] : Spacetime) ∈ causalIntervalInterior (timeAxis 0) (timeAxis 2) := by
    simp only [causalIntervalInterior, mem_diff, mem_insert_iff, mem_singleton_iff,
      causalInterval, mem_inter_iff, causalPast, causalFuture, mem_setOf_eq,
      spatialSeparationSq, timeAxis_zero, timeAxis_succ]
    norm_num [Fin.sum_univ_three, h0, h2]
    rfl
  simp [intervalCount, hi]

/-- The two marked endpoints never enter the residual interior count. -/
example (x y : Spacetime) (c : Multiset Spacetime) :
    intervalCount x y (x ::ₘ y ::ₘ c) = intervalCount x y c := intervalCount_insert_endpoints x y c

/-- Endpoint-dependent counts really are jointly measurable. -/
example : JointMeasurable (fun p : Spacetime × Spacetime => intervalCount p.1 p.2) :=
  jointMeasurable_intervalCount

/-- Finite-volume intersection, not the unrestricted interval volume, is the
rate for a region that need not be causally convex. -/
example (S : FiniteSprinkling) (x y : Spacetime) (k : ℕ) :
    S.probability {c | intervalCount x y c = k} =
      ENNReal.ofReal (Real.exp (-(S.density *
        (volume (causalIntervalInterior x y ∩ S.region)).toReal)) *
        (S.density * (volume (causalIntervalInterior x y ∩ S.region)).toReal) ^ k / k.factorial) :=
  S.count_probability (measurableSet_causalIntervalInterior x y) k

example (k : ℕ) :
    Measurable (intervalPairSum (fun n => if n = k then (1 : ℕ) else 0)) :=
  measurable_intervalPairSum _

example (S : FiniteSprinkling) :
    Integrable (intervalPairSum (fun n => if n = 0 then (-2 : ℝ) else 1)) S.probability := by
  apply integrable_intervalPairSum S _ 2 (by norm_num)
  intro n
  split_ifs <;> norm_num

/-- Full residual-dependent two-point identity, not merely an unmarked
factorial moment. This is the downstream interval-layer integration contract. -/
example (S : FiniteSprinkling) (F : Spacetime → Spacetime → Multiset Spacetime → ℝ≥0∞)
    (hF : JointMeasurable (fun p : Spacetime × Spacetime => F p.1 p.2)) :
    (∫⁻ c, pairSum F c ∂S.probability) =
      ∫⁻ x, ∫⁻ y, ∫⁻ c, F x y c ∂S.probability ∂S.intensity ∂S.intensity :=
  FinitePoisson.lintegral_pairSum S.intensity hF

example (S : FiniteSprinkling) (k : ℕ) :
    (∫⁻ c, intervalPairSum (fun n => if n = k then (1 : ℝ≥0∞) else 0) c ∂S.probability) =
      ∫⁻ x, ∫⁻ y, if y ∈ causalFuture x ∧ x ≠ y then
        poissonPMF (S.intensity (causalIntervalInterior x y)).toNNReal k else 0
        ∂S.intensity ∂S.intensity := lintegral_intervalLayer S k

end PoissonRegression
