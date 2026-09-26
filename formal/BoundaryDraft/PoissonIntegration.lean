import BoundaryDraft.FinitePoisson

/-!
# Factorial moments and absolute integrability

Reduced Mecke is available for arbitrary nonnegative, jointly measurable
residual observables. The first two factorial moments also give explicit
absolute-integrability bounds for bounded signed point and pair observables.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

noncomputable section

namespace BoundaryDraft
namespace FiniteConfiguration

variable {α : Type*}

@[simp] theorem pointSum_const (c : Multiset α) (a : ℝ≥0∞) :
    pointSum (fun _ _ => a) c = c.card * a := by
  simp [pointSum, nsmul_eq_mul]

@[simp] theorem pairSum_one (c : Multiset α) :
    pairSum (fun _ _ _ => (1 : ℝ≥0∞)) c = (c.card * (c.card - 1) : ℕ) := by
  classical
  simp only [pairSum, pointSum_const, mul_one]
  unfold pointSum
  have h : (c.map fun x => ((c.erase x).card : ℝ≥0∞)) =
      c.map (fun _ => ((c.card - 1 : ℕ) : ℝ≥0∞)) :=
    Multiset.map_congr rfl fun x hx => by rw [Multiset.card_erase_of_mem hx, Nat.pred_eq_sub_one]
  rw [h]
  simp [nsmul_eq_mul]

theorem abs_pointSum_le (F : α → Multiset α → ℝ) (c : Multiset α) (C : ℝ)
    (hF : ∀ x ∈ c, |F x (c.erase x)| ≤ C) :
    |pointSum F c| ≤ c.card * C := by
  classical
  change ‖(c.map fun x => F x (c.erase x)).sum‖ ≤ _
  apply (norm_multiset_sum_le _).trans
  have h := Multiset.sum_le_card_nsmul ((c.map fun x => F x (c.erase x)).map norm) C
    (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hb
      exact hF x hx)
  simpa [nsmul_eq_mul] using h

theorem abs_pairSum_le (F : α → α → Multiset α → ℝ) (c : Multiset α) (C : ℝ)
    (hF : ∀ x y r, |F x y r| ≤ C) :
    |pairSum F c| ≤ (c.card * (c.card - 1) : ℕ) * C := by
  classical
  have h := abs_pointSum_le (fun x r => pointSum (F x) r) c ((c.card - 1 : ℕ) * C)
    (fun x hx => by
      have hh := abs_pointSum_le (F x) (c.erase x) C (fun y _ => hF x y _)
      simpa [Multiset.card_erase_of_mem hx, Nat.pred_eq_sub_one] using hh)
  simpa [pairSum, Nat.cast_mul, mul_assoc] using h

theorem pointSum_nonneg {F : α → Multiset α → ℝ} (hF : ∀ x c, 0 ≤ F x c)
    (c : Multiset α) : 0 ≤ pointSum F c := by
  classical
  apply Multiset.sum_nonneg
  intro a ha
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 ha
  exact hF x _

theorem pairSum_nonneg {F : α → α → Multiset α → ℝ} (hF : ∀ x y c, 0 ≤ F x y c)
    (c : Multiset α) : 0 ≤ pairSum F c :=
  pointSum_nonneg (fun x r => pointSum_nonneg (hF x) r) c

theorem pointSum_ofReal {F : α → Multiset α → ℝ} (hF : ∀ x c, 0 ≤ F x c)
    (c : Multiset α) :
    ENNReal.ofReal (pointSum F c) = pointSum (fun x r => ENNReal.ofReal (F x r)) c := by
  classical
  have h (s : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
      ENNReal.ofReal (s.map f).sum = (s.map fun x => ENNReal.ofReal (f x)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons x s ih =>
      have hs : 0 ≤ (s.map f).sum := Multiset.sum_nonneg (by
        intro a ha
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 ha
        exact hf y)
      simp only [Multiset.map_cons, Multiset.sum_cons, ENNReal.ofReal_add (hf x) hs, ih]
  exact h c _ (fun x => hF x _)

theorem pairSum_ofReal {F : α → α → Multiset α → ℝ} (hF : ∀ x y c, 0 ≤ F x y c)
    (c : Multiset α) :
    ENNReal.ofReal (pairSum F c) = pairSum (fun x y r => ENNReal.ofReal (F x y r)) c := by
  rw [pairSum, pointSum_ofReal (fun x r => pointSum_nonneg (hF x) r)]
  simp_rw [pointSum_ofReal (hF _)]
  rfl

theorem pointSum_sub (F G : α → Multiset α → ℝ) (c : Multiset α) :
    pointSum (fun x r => F x r - G x r) c = pointSum F c - pointSum G c := by
  simp [pointSum, Multiset.sum_map_sub]

theorem pairSum_sub (F G : α → α → Multiset α → ℝ) (c : Multiset α) :
    pairSum (fun x y r => F x y r - G x y r) c = pairSum F c - pairSum G c := by
  simp only [pairSum, pointSum_sub]

end FiniteConfiguration
namespace FinitePoisson

open FiniteConfiguration

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- First factorial moment, including null intensity. -/
theorem lintegral_card : (∫⁻ c : Multiset α, (c.card : ℝ≥0∞) ∂law μ) = μ univ := by
  simpa using lintegral_pointSum μ (F := fun _ _ => 1) (fun _ => measurable_const)

/-- Ordered distinct-occurrence factorial moment, not the square of the
number of points (the diagonal is excluded). -/
theorem lintegral_pairCard :
    (∫⁻ c : Multiset α, ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞) ∂law μ) = μ univ * μ univ := by
  simpa using lintegral_pairSum μ (F := fun _ _ _ => 1) (fun _ => measurable_const)

theorem integrable_card : Integrable (fun c : Multiset α => (c.card : ℝ)) (law μ) := by
  have hm : Measurable (fun c : Multiset α => c.card) := by
    simpa only [count_univ] using (show Measurable (fun c : Multiset α => count univ c) from
      measurable_count MeasurableSet.univ)
  refine ⟨((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, Nat.abs_cast, ENNReal.ofReal_natCast]
  rw [lintegral_card]
  exact measure_lt_top μ _

theorem integrable_pairCard :
    Integrable (fun c : Multiset α => ((c.card * (c.card - 1) : ℕ) : ℝ)) (law μ) := by
  have hm : Measurable (fun c : Multiset α => c.card) := by
    simpa only [count_univ] using (show Measurable (fun c : Multiset α => count univ c) from
      measurable_count MeasurableSet.univ)
  refine ⟨((measurable_of_countable (fun n : ℕ => ((n * (n - 1) : ℕ) : ℝ))).comp hm).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, Nat.abs_cast, ENNReal.ofReal_natCast]
  rw [lintegral_pairCard]
  exact ENNReal.mul_lt_top (measure_lt_top μ _) (measure_lt_top μ _)

/-- A bounded signed residual point observable has an integrable sum. -/
theorem integrable_pointSum {F : α → Multiset α → ℝ} (hF : JointMeasurable F)
    (C : ℝ) (hbound : ∀ x c, |F x c| ≤ C) : Integrable (pointSum F) (law μ) :=
  ((integrable_card μ).mul_const C).mono' (measurable_pointSum hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun c => abs_pointSum_le F c C (fun x _ => hbound x _))

/-- A bounded signed residual pair observable has an integrable sum. -/
theorem integrable_pairSum {F : α → α → Multiset α → ℝ}
    (hF : JointMeasurable (fun p : α × α => F p.1 p.2))
    (C : ℝ) (hbound : ∀ x y c, |F x y c| ≤ C) : Integrable (pairSum F) (law μ) :=
  ((integrable_pairCard μ).mul_const C).mono' (measurable_pairSum hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun c => abs_pairSum_le F c C hbound)

theorem integral_pointSum_nonneg {F : α → Multiset α → ℝ} (hF : JointMeasurable F)
    (hpos : ∀ x c, 0 ≤ F x c) :
    (∫ c, pointSum F c ∂law μ) = (∫⁻ x, ∫⁻ c, ENNReal.ofReal (F x c) ∂law μ ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (pointSum_nonneg hpos)) (measurable_pointSum hF).aestronglyMeasurable]
  simp_rw [pointSum_ofReal hpos]
  rw [lintegral_pointSum μ (fun n => (hF n).ennreal_ofReal)]

theorem integral_pairSum_nonneg {F : α → α → Multiset α → ℝ}
    (hF : JointMeasurable (fun p : α × α => F p.1 p.2)) (hpos : ∀ x y c, 0 ≤ F x y c) :
    (∫ c, pairSum F c ∂law μ) =
      (∫⁻ x, ∫⁻ y, ∫⁻ c, ENNReal.ofReal (F x y c) ∂law μ ∂μ ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (pairSum_nonneg hpos)) (measurable_pairSum hF).aestronglyMeasurable]
  simp_rw [pairSum_ofReal hpos]
  rw [lintegral_pairSum μ (fun n => (hF n).ennreal_ofReal)]

/-- Signed pair integration by positive and negative parts. Absolute
integrability is proved from the explicit bound, rather than hidden in the
totalised real integral. The nonnegative Mecke identity remains unbounded. -/
theorem integral_pairSum {F : α → α → Multiset α → ℝ}
    (hF : JointMeasurable (fun p : α × α => F p.1 p.2))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x y c, |F x y c| ≤ C) :
    (∫ c, pairSum F c ∂law μ) =
      (∫⁻ x, ∫⁻ y, ∫⁻ c, ENNReal.ofReal (F x y c) ∂law μ ∂μ ∂μ).toReal -
      (∫⁻ x, ∫⁻ y, ∫⁻ c, ENNReal.ofReal (-F x y c) ∂law μ ∂μ ∂μ).toReal := by
  let P := fun x y c => max (F x y c) 0
  let N := fun x y c => max (-F x y c) 0
  have hP : JointMeasurable (fun p : α × α => P p.1 p.2) := fun n => (hF n).max measurable_const
  have hN : JointMeasurable (fun p : α × α => N p.1 p.2) := fun n => (hF n).neg.max measurable_const
  have hp (x y c) : 0 ≤ P x y c := le_max_right _ _
  have hn (x y c) : 0 ≤ N x y c := le_max_right _ _
  have hbp (x y c) : |P x y c| ≤ C := by
    rw [abs_of_nonneg (hp x y c)]
    exact max_le ((le_abs_self _).trans (hbound x y c)) hC
  have hbn (x y c) : |N x y c| ≤ C := by
    rw [abs_of_nonneg (hn x y c)]
    exact max_le ((neg_le_abs _).trans (hbound x y c)) hC
  have he : F = fun x y c => P x y c - N x y c := by
    funext x y c
    exact (max_zero_sub_max_neg_zero_eq_self (F x y c)).symm
  conv_lhs => rw [he]
  simp_rw [pairSum_sub]
  rw [integral_sub (integrable_pairSum μ hP C hbp) (integrable_pairSum μ hN C hbn),
    integral_pairSum_nonneg μ hP hp, integral_pairSum_nonneg μ hN hn]
  have hr (r : ℝ) : ENNReal.ofReal (max r 0) = ENNReal.ofReal r :=
    ENNReal.ofReal_toReal ENNReal.ofReal_ne_top
  simp only [P, N, hr]

end FinitePoisson
end BoundaryDraft
