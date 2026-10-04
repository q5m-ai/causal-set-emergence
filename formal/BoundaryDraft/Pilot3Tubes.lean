import BoundaryDraft.Pilot3Overlap

/-!
# Derived compact perturbation tubes for the 3D long and short consumers

The long tube includes the whole OLD active set (gap ≥ 0), including contacts
and points where the perturbed gap is negative. Constants depend on the fixed
positive cutoff, never on density. The short translation tube covers small
segments from every point of the closed positive region, without convexity or
connectedness. Bounds are on the actual raw smooth germs, not the clipped
height. These are geometric controls, not a jet, coarea formula or limit.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Compact superlevel tube; for positive `a` it lies strictly inside `{h > 0}`. -/
def pilot3HeightTube (h : Pilot3Space → ℝ) (a : ℝ) : Set Pilot3Space :=
  pilot3ClosedPositive h ∩ {x | a ≤ max 0 (h x)}

/-- Closed spatial neighborhood, used for short raw-germ translations. -/
def pilot3TranslationTube (h : Pilot3Space → ℝ) (ε : ℝ) : Set Pilot3Space :=
  Metric.cthickening ε (pilot3ClosedPositive h)

/-- The merged notes' `z = (tau, b)`, with `v = tau + |b|` and proper-time square `σ`.
The identities with `v` require a unit direction and `0 ≤ σ ≤ v²`, proved below. -/
def pilot3RayDisplacement (ω : Pilot3Space) (σ v : ℝ) : Pilot3Spacetime :=
  ((v + σ / v) / 2, ((v - σ / v) / 2) • ω)

def pilot3RayGap (h f : Pilot3Space → ℝ) (x ω : Pilot3Space) (σ v : ℝ) : ℝ :=
  pilot3OverlapGap h f (pilot3RayDisplacement ω σ v) x

/-- A common nonzero proper-time-square interval for the old-active endpoints. -/
def pilot3PerturbationWidth (κ m δ : ℝ) : ℝ :=
  min (δ ^ 2 / 2) (m * δ ^ 2 / (2 * (1 + κ)))

theorem pilot3PerturbationWidth_pos {κ m δ : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) (hδ : 0 < δ) :
    0 < pilot3PerturbationWidth κ m δ := by unfold pilot3PerturbationWidth; positivity

theorem pilot3PerturbationWidth_lt_sq {κ m δ : ℝ} (hδ : 0 < δ) :
    pilot3PerturbationWidth κ m δ < δ ^ 2 :=
  (min_le_left _ _).trans_lt (by nlinarith [sq_pos_of_pos hδ])

theorem pilot3PerturbationWidth_loss {κ m δ : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) (hδ : 0 < δ) :
    κ * pilot3PerturbationWidth κ m δ / (2 * δ) ≤ m * δ / 4 := by
  have he := (le_div_iff₀ (show 0 < 2 * (1 + κ) by positivity)).mp
    (min_le_right (δ ^ 2 / 2) (m * δ ^ 2 / (2 * (1 + κ))))
  have hp := pilot3PerturbationWidth_pos hκ hm hδ
  apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
  change κ * pilot3PerturbationWidth κ m δ ≤ _
  change pilot3PerturbationWidth κ m δ * (2 * (1 + κ)) ≤ _ at he
  nlinarith

theorem pilot3_norm_ray_sub (x ω : Pilot3Space) (hω : ‖ω‖ = 1) (r s : ℝ) :
    ‖(x + r • ω) - (x + s • ω)‖ = |r - s| := by
  rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hω, mul_one, Real.norm_eq_abs]

theorem pilot3RayDisplacement_norm {ω : Pilot3Space} (hω : ‖ω‖ = 1)
    {σ v : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖(pilot3RayDisplacement ω σ v).2‖ = (v - σ / v) / 2 := by
  have hdiv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith [hσ.2])
  simp only [pilot3RayDisplacement, norm_smul, Real.norm_eq_abs, hω, mul_one,
    abs_of_nonneg (show 0 ≤ (v - σ / v) / 2 by linarith)]

theorem pilot3RayDisplacement_causal {ω : Pilot3Space} (hω : ‖ω‖ = 1)
    {σ v : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖(pilot3RayDisplacement ω σ v).2‖ ≤ (pilot3RayDisplacement ω σ v).1 := by
  rw [pilot3RayDisplacement_norm hω hv hσ]
  dsimp [pilot3RayDisplacement]
  linarith [div_nonneg hσ.1 hv.le]

theorem pilot3RayDisplacement_parameters {ω : Pilot3Space} (hω : ‖ω‖ = 1)
    {σ v : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    (pilot3RayDisplacement ω σ v).1 + ‖(pilot3RayDisplacement ω σ v).2‖ = v ∧
      (pilot3RayDisplacement ω σ v).1 ^ 2 - ‖(pilot3RayDisplacement ω σ v).2‖ ^ 2 = σ := by
  rw [pilot3RayDisplacement_norm hω hv hσ]
  dsimp [pilot3RayDisplacement]
  constructor
  · ring
  · field_simp
    ring

namespace Pilot3SlopeControl
variable {h f : Pilot3Space → ℝ} {κ η : ℝ} (C : Pilot3SlopeControl h f κ η)
include C

/-- L7's old-null source AND partner margins, with exact contact included. -/
theorem old_endpoint_margin {δ v : ℝ} (hδ : 0 < δ) (hv : δ ≤ v)
    (x ω : Pilot3Space) (hω : ‖ω‖ = 1) (hg : 0 ≤ pilot3RayGap h f x ω 0 v) :
    (1 - κ - η) * δ / 2 ≤ max 0 (h x) ∧
      (1 - κ - η) * δ / 2 ≤ max 0 (h (x + (v / 2) • ω)) := by
  have hb := C.gap_height_margins (pilot3RayDisplacement ω 0 v)
    (pilot3RayDisplacement_causal hω (hδ.trans_le hv) ⟨le_rfl, sq_nonneg v⟩) x hg
  simp only [pilot3RayDisplacement, zero_div, add_zero, sub_zero] at hb
  have hm : 0 < 1 - κ - η := by linarith [C.budget]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hv hm.le]

/-- No hypothesis on the NEW gap: old-active points stay in the positive
height tube even after perturbation has crossed their contact. -/
theorem perturbed_endpoint_margin {δ ε σ v : ℝ} (hδ : 0 < δ) (hv : δ ≤ v)
    (hσ : σ ∈ Icc 0 ε) (hε : κ * ε / (2 * δ) ≤ (1 - κ - η) * δ / 4)
    (x ω : Pilot3Space) (hω : ‖ω‖ = 1) (hg : 0 ≤ pilot3RayGap h f x ω 0 v) :
    (1 - κ - η) * δ / 4 ≤ max 0 (h (x + ((v - σ / v) / 2) • ω)) := by
  have hb := (C.old_endpoint_margin hδ hv x ω hω hg).2
  have hl := (abs_le.mp (C.height_lipschitz (x + (v / 2) • ω)
    (x + ((v - σ / v) / 2) • ω))).2
  rw [pilot3_norm_ray_sub x ω hω] at hl
  rw [show (v - σ / v) / 2 - v / 2 = -(σ / (2 * v)) by ring,
    abs_neg, abs_of_nonneg (div_nonneg hσ.1 (by linarith))] at hl
  have he : κ * (σ / (2 * v)) ≤ κ * ε / (2 * δ) := by
    have hκ := C.height_nonneg
    have hε0 := hσ.1.trans hσ.2
    rw [← mul_div_assoc]
    gcongr
    exact hσ.2
  linarith

/-- L7's strict null-length decrease, valid also at cutoff contacts and
spatial tangencies. This is a Lipschitz finite difference, not a hinge derivative. -/
theorem nullGap_decrease {v w : ℝ} (hvw : v ≤ w) (x θ : Pilot3Space) (hθ : ‖θ‖ = 1) :
    pilot3RayGap h f x θ 0 w ≤ pilot3RayGap h f x θ 0 v - (1 - η) / 2 * (w - v) := by
  have hl := (abs_le.mp (C.future_lipschitz (x + (w / 2) • θ) (x + (v / 2) • θ))).2
  rw [pilot3_norm_ray_sub x θ hθ, abs_of_nonpos (show v / 2 - w / 2 ≤ 0 by linarith)] at hl
  dsimp [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement]
  simp only [zero_div, add_zero, sub_zero]
  ring_nf at hl ⊢
  linarith

/-- Two-sided proper-time-square finite differences with the actual future
translated. The slope bound is uniform once `v` has a fixed positive lower bound. -/
theorem rayGap_sigma_bounds {σ τ v : ℝ} (hστ : σ ≤ τ) (hv : 0 < v)
    (x θ : Pilot3Space) (hθ : ‖θ‖ = 1) :
    -(1 + η) * (τ - σ) / (2 * v) ≤ pilot3RayGap h f x θ τ v - pilot3RayGap h f x θ σ v ∧
      pilot3RayGap h f x θ τ v - pilot3RayGap h f x θ σ v ≤ -(1 - η) * (τ - σ) / (2 * v) := by
  have hl := abs_le.mp (C.future_lipschitz
    (x + ((v - τ / v) / 2) • θ) (x + ((v - σ / v) / 2) • θ))
  rw [pilot3_norm_ray_sub x θ hθ,
    show (v - σ / v) / 2 - (v - τ / v) / 2 = (τ - σ) / (2 * v) by ring,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hστ) (by positivity))] at hl
  dsimp [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement]
  ring_nf at hl ⊢
  constructor <;> linarith [hl.1, hl.2]

/-- Every perturbed active point is old-active. This finite-difference
inequality needs no spatial transversality or differentiation of a hinge. -/
theorem rayGap_le_null {σ v : ℝ} (hσ : 0 ≤ σ) (hv : 0 < v)
    (x ω : Pilot3Space) (hω : ‖ω‖ = 1) :
    pilot3RayGap h f x ω σ v ≤ pilot3RayGap h f x ω 0 v - (1 - η) * σ / (2 * v) := by
  have hl := (abs_le.mp (C.future_lipschitz
    (x + ((v - σ / v) / 2) • ω) (x + (v / 2) • ω))).2
  rw [pilot3_norm_ray_sub x ω hω] at hl
  rw [show v / 2 - (v - σ / v) / 2 = σ / (2 * v) by ring,
    abs_of_nonneg (div_nonneg hσ (by positivity))] at hl
  dsimp [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement]
  simp only [zero_div, add_zero, sub_zero]
  ring_nf at hl ⊢
  linarith

/-- A nonpositive null cutoff gap kills the ENTIRE right fibre, including
exact cutoff contacts of positive parameter measure and exceptional directions. -/
theorem rayGap_nonpos_of_cutoff_nonpos {δ v σ : ℝ} (hδ : 0 < δ) (hv : δ ≤ v) (hσ : 0 ≤ σ)
    (x θ : Pilot3Space) (hθ : ‖θ‖ = 1) (hg : pilot3RayGap h f x θ 0 δ ≤ 0) :
    pilot3RayGap h f x θ σ v ≤ 0 := by
  have hη : 0 ≤ 1 - η := by linarith [C.height_nonneg, C.budget]
  have hv0 := hδ.trans_le hv
  have h0 := C.nullGap_decrease hv x θ hθ
  have h1 := C.rayGap_le_null hσ hv0 x θ hθ
  have hp : 0 ≤ (1 - η) / 2 * (v - δ) := mul_nonneg (by positivity) (sub_nonneg.mpr hv)
  have hq : 0 ≤ (1 - η) * σ / (2 * v) := by positivity
  linarith

end Pilot3SlopeControl

theorem pilot3HeightTube_positive {h : Pilot3Space → ℝ} {a : ℝ} (ha : 0 < a)
    {x : Pilot3Space} (hx : x ∈ pilot3HeightTube h a) : 0 < h x := by
  have hp := ha.trans_le hx.2
  simpa using hp

theorem pilot3_mem_heightTube {h : Pilot3Space → ℝ} {a : ℝ} (ha : 0 < a)
    {x : Pilot3Space} (hx : a ≤ max 0 (h x)) : x ∈ pilot3HeightTube h a := by
  have hp : 0 < h x := by simpa using ha.trans_le hx
  exact ⟨subset_closure hp, hx⟩

/-- Small translations and their full segments require no convexity of the
positive region; the fixed closed neighborhood contains them. -/
theorem pilot3_add_mem_translationTube {h : Pilot3Space → ℝ} {ε : ℝ}
    {x b : Pilot3Space} (hx : x ∈ pilot3ClosedPositive h) (hb : ‖b‖ ≤ ε) :
    x + b ∈ pilot3TranslationTube h ε := by
  apply Metric.mem_cthickening_of_dist_le (x + b) x ε _ hx
  simpa only [dist_eq_norm, add_sub_cancel_left] using hb

theorem pilot3_segment_mem_translationTube {h : Pilot3Space → ℝ} {ε : ℝ}
    {x b : Pilot3Space} (hx : x ∈ pilot3ClosedPositive h) (hb : ‖b‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Icc 0 1) : x + t • b ∈ pilot3TranslationTube h ε := by
  apply pilot3_add_mem_translationTube hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg b) ht.2).trans hb

open scoped ContDiff

private theorem bound_iteratedDeriv_on_compact {g : Pilot3Space → ℝ} {S : Set Pilot3Space}
    (hS : IsCompact S) (hs : ∀ x ∈ S, ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖iteratedFDeriv ℝ n g x‖ ≤ B := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n g) S := fun x hx =>
    ((hs x hx).iteratedFDeriv_right (m := 0)
      (by simp only [zero_add]; exact WithTop.coe_le_coe.mpr le_top)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  exact ⟨max 0 B, le_max_left _ _, fun x hx => (hB x hx).trans (le_max_right _ _)⟩

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem isCompact_heightTube (a : ℝ) : IsCompact (pilot3HeightTube h a) :=
  hf.toPilot3RegularHeight.isCompact_closedPositive.inter_right
    (isClosed_le continuous_const hf.continuous_positivePart)

theorem isCompact_translationTube (ε : ℝ) : IsCompact (pilot3TranslationTube h ε) :=
  hf.toPilot3RegularHeight.isCompact_closedPositive.cthickening

/-- Every finite derivative order of the actual future is uniformly bounded
on the compact superlevel tube. Positive-height critical points are retained. -/
theorem future_derivative_bounds (a : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ pilot3HeightTube h a, ‖iteratedFDeriv ℝ n f x‖ ≤ B :=
  bound_iteratedDeriv_on_compact (hf.isCompact_heightTube a) (fun x hx => hf.future_smoothAt x hx.1) n

/-- One common OPEN smooth neighborhood surrounds a fixed closed translation
tube. This uses the original smooth-neighborhood fields, not an incorrect
openness assertion about the set of smooth-order `ContDiffAt` points. -/
theorem exists_smooth_translationTube : ∃ ε : ℝ, ∃ U : Set Pilot3Space,
    0 < ε ∧ IsOpen U ∧ pilot3TranslationTube h ε ⊆ U ∧
      ContDiffOn ℝ ∞ h U ∧ ContDiffOn ℝ ∞ f U := by
  let U : Set Pilot3Space := {x | ∃ V : Set Pilot3Space,
    IsOpen V ∧ x ∈ V ∧ ContDiffOn ℝ ∞ h V ∧ ContDiffOn ℝ ∞ f V}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun x hx => by
    obtain ⟨V, hV, hxV, hh, hF⟩ := hx
    exact Filter.mem_of_superset (hV.mem_nhds hxV) (fun y hy => ⟨V, hV, hy, hh, hF⟩)
  have hKU : pilot3ClosedPositive h ⊆ U := by
    intro x hx
    obtain ⟨V, hV, hxV, hh⟩ := hf.smooth_near x hx
    obtain ⟨W, hW, hxW, hF⟩ := hf.smooth_future x hx
    exact ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, hh.mono inter_subset_left, hF.mono inter_subset_right⟩
  obtain ⟨ε, hε, he⟩ := hf.toPilot3RegularHeight.isCompact_closedPositive.exists_cthickening_subset_open hU hKU
  refine ⟨ε, U, hε, hU, he, ?_, ?_⟩
  · rintro x ⟨V, hV, hxV, hh, _⟩
    exact (hh.contDiffAt (hV.mem_nhds hxV)).contDiffWithinAt
  · rintro x ⟨V, hV, hxV, _, hF⟩
    exact (hF.contDiffAt (hV.mem_nhds hxV)).contDiffWithinAt

/-- Uniform bounds for both RAW germs, to every fixed finite derivative order,
on a single compact translation tube chosen independently of density. -/
theorem exists_translationTube_derivative_bounds : ∃ ε : ℝ, 0 < ε ∧
    (∀ x ∈ pilot3TranslationTube h ε, ContDiffAt ℝ ∞ h x ∧ ContDiffAt ℝ ∞ f x) ∧
    ∀ n : ℕ, ∃ Bh Bf : ℝ, 0 ≤ Bh ∧ 0 ≤ Bf ∧
      ∀ x ∈ pilot3TranslationTube h ε,
        ‖iteratedFDeriv ℝ n h x‖ ≤ Bh ∧ ‖iteratedFDeriv ℝ n f x‖ ≤ Bf := by
  obtain ⟨ε, U, hε, hU, he, hh, hF⟩ := hf.exists_smooth_translationTube
  have hs : ∀ x ∈ pilot3TranslationTube h ε, ContDiffAt ℝ ∞ h x ∧ ContDiffAt ℝ ∞ f x :=
    fun x hx => ⟨hh.contDiffAt (hU.mem_nhds (he hx)), hF.contDiffAt (hU.mem_nhds (he hx))⟩
  refine ⟨ε, hε, hs, fun n => ?_⟩
  obtain ⟨Bh, hh0, hhb⟩ := bound_iteratedDeriv_on_compact (hf.isCompact_translationTube ε) (fun x hx => (hs x hx).1) n
  obtain ⟨Bf, hf0, hfb⟩ := bound_iteratedDeriv_on_compact (hf.isCompact_translationTube ε) (fun x hx => (hs x hx).2) n
  exact ⟨Bh, Bf, hh0, hf0, fun x hx => ⟨hhb x hx, hfb x hx⟩⟩

/-- A uniform finite upper length for ALL active rays, including perturbed
ones and exact contacts. No spatial component or exceptional direction is removed. -/
theorem exists_long_length_bound : ∃ V : ℝ, 0 < V ∧
    ∀ (x θ : Pilot3Space) (v σ : ℝ), ‖θ‖ = 1 → 0 < v → 0 ≤ σ →
      0 ≤ pilot3RayGap h f x θ σ v → v ≤ V := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  have hm : 0 < 1 - κ - η := by linarith [C.budget]
  obtain ⟨H, hH⟩ := hf.toPilot3RegularHeight.isCompact_closedPositive.exists_bound_of_continuousOn
    hf.continuous_positivePart.continuousOn
  refine ⟨2 * (max 0 H + 1) / (1 - κ - η), by positivity, ?_⟩
  intro x θ v σ hθ hv hσ hg
  have hη : 0 ≤ 1 - η := by linarith [C.height_nonneg, C.budget]
  have hg0 : 0 ≤ pilot3RayGap h f x θ 0 v := by
    have hd := C.rayGap_le_null hσ hv x θ hθ
    have hp : 0 ≤ (1 - η) * σ / (2 * v) := by positivity
    linarith
  have hb := (C.old_endpoint_margin hv le_rfl x θ hθ hg0).1
  have hx := pilot3_mem_heightTube (by positivity : 0 < (1 - κ - η) * v / 2) hb
  have hh := hH x hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)] at hh
  apply (le_div_iff₀ hm).mpr
  nlinarith [le_max_right (0 : ℝ) H]

/-- The common-cutoff long interface, derived from unchanged hypotheses.
Source and old target have twice the perturbed tube's positive-height margin.
There is no assumption on the new gap, contact transversality or interior gradient. -/
theorem exists_long_perturbationTube (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ η ε : ℝ, Pilot3SlopeControl h f κ η ∧
      ε = pilot3PerturbationWidth κ (1 - κ - η) δ ∧ 0 < ε ∧ ε < δ ^ 2 ∧
      ∀ (x θ : Pilot3Space) (v σ : ℝ), ‖θ‖ = 1 → δ ≤ v → σ ∈ Icc 0 ε →
        0 ≤ pilot3RayGap h f x θ 0 v →
        x ∈ pilot3HeightTube h ((1 - κ - η) * δ / 2) ∧
        x + (v / 2) • θ ∈ pilot3HeightTube h ((1 - κ - η) * δ / 2) ∧
        x + ((v - σ / v) / 2) • θ ∈ pilot3HeightTube h ((1 - κ - η) * δ / 4) := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  have hm : 0 < 1 - κ - η := by linarith [C.budget]
  refine ⟨κ, η, pilot3PerturbationWidth κ (1 - κ - η) δ, C, rfl,
    pilot3PerturbationWidth_pos C.height_nonneg hm hδ, pilot3PerturbationWidth_lt_sq hδ, ?_⟩
  intro x θ v σ hθ hv hσ hg
  have hb := C.old_endpoint_margin hδ hv x θ hθ hg
  exact ⟨pilot3_mem_heightTube (by positivity) hb.1,
    pilot3_mem_heightTube (by positivity) hb.2,
    pilot3_mem_heightTube (by positivity) (C.perturbed_endpoint_margin hδ hv hσ
      (pilot3PerturbationWidth_loss C.height_nonneg hm hδ) x θ hθ hg)⟩

end SmoothPilot3
end BoundaryDraft
