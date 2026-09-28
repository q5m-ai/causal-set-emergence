import BoundaryDraft

/-!
Independent regressions for the PREPARATORY estimates and conditional assembly
of #61. No example below proves the missing averaged-density quadratic jet.
In particular the planar and curved regressions are gap estimates, not new
long-null limits. The signed normalization regression retains its jet premise.
-/

open BoundaryDraft MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace TwoFaceLongNullRegression

-- The old planar class has no extra height or critical-point assumptions.
example {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) :
    ∃ m : ℝ, 0 < m ∧ ∀ (x y : Spatial) (s : ℝ),
      spatialDistance x y ≤ s → 0 ≤ max 0 (h x) - s →
      m * s ≤ max 0 (h x) ∧ m * s ≤ max 0 (h y) := by
  simpa only [twoFaceGap, add_zero, sub_zero] using hh.twoFace_planar.exists_gap_height_margin

example (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere) (σ v : ℝ) :
    twoFaceRayGap h (fun _ => 0) x ω σ v = max 0 (h x) - (v + σ / v) / 2 := by
  simp [twoFaceRayGap, twoFaceGap]

-- Unequal-axis original cap; no hidden exclusion of interior critical points.
private def cap : Spatial → ℝ := ellipsoidProfile (1 / 4) ![1, 2, 3]

private theorem cap_admissible : AdmissibleGraphCap cap := by
  exact ellipsoid_admissible _ _ (by norm_num)
    (fun i => by fin_cases i <;> norm_num)

example : AdmissibleTwoFace cap (fun _ => 0) := cap_admissible.twoFace_planar

-- The null-ray contact occurs at the positive-height critical point in every
-- direction. The lemma does not discard these directions or assume dh ≠ 0.
example (ω : OverlapSphere) : twoFaceRayGap cap (fun _ => 0) 0 ω 0 (1 / 2) = 0 ∧
    fderiv ℝ (fun x : JointSpace => cap x) 0 = 0 := by
  constructor
  · norm_num [twoFaceRayGap, twoFaceGap, cap, ellipsoidProfile]
  · have hd := (hasGradientAt_ellipsoidProfile (1 / 4) ![1, 2, 3] 0).hasFDerivAt
    have hz : ellipsoidGradient (1 / 4) ![1, 2, 3] 0 = 0 := by
      ext i
      simp [ellipsoidGradient]
    change fderiv ℝ (fun x : JointSpace => ellipsoidProfile (1 / 4) ![1, 2, 3] x) 0 = _
    rw [hd.fderiv, hz]
    simp

-- A cutoff exactly at that translated contact has no opening on the right.
example (ω : OverlapSphere) {σ v : ℝ} (hσ : 0 ≤ σ) (hv : 1 / 2 ≤ v) :
    max 0 (twoFaceRayGap cap (fun _ => 0) 0 ω σ v) = 0 := by
  apply max_eq_left
  exact twoFaceRayGap_nonpos_of_cutoff (η := 0) (by norm_num) (by simp)
    cap 0 ω (by norm_num) hσ hv (by
      norm_num [twoFaceRayGap, twoFaceGap, cap, ellipsoidProfile])

-- A strictly smaller cutoff includes the contact's surrounding crossing layer.
-- Its LENGTH is controlled, not just its central level set's measure.
example (x : Spatial) (ω : OverlapSphere) {σ : ℝ} (hσ : 0 ≤ σ) :
    volume {v : ℝ | 1 / 4 ≤ v ∧ 0 < twoFaceRayGap cap (fun _ => 0) x ω 0 v ∧
      twoFaceRayGap cap (fun _ => 0) x ω σ v ≤ 0} ≤ ENNReal.ofReal (4 * σ) := by
  have he := volume_twoFaceRayGap_crossing (f := fun _ => 0) (η := 0) (by norm_num) (by norm_num)
    (by simp) cap x ω (δ := 1 / 4) (by norm_num) hσ
  convert he using 1
  congr 1
  ring

-- Nonempty genuinely curved future-face example, with its independent
-- nonaffinity witness retained and a uniform crossing-layer bound.
theorem curved_crossing_control : ∃ c η : ℝ, 0 < c ∧ 0 ≤ η ∧ η < 1 ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 ∧
    ∀ (x : Spatial) (ω : OverlapSphere) (δ σ : ℝ), 0 < δ → 0 ≤ σ →
      volume {v : ℝ | δ ≤ v ∧
        0 < twoFaceRayGap (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) x ω 0 v ∧
        twoFaceRayGap (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) x ω σ v ≤ 0} ≤
        ENNReal.ofReal ((1 + η) * σ / (δ * (1 - η))) := by
  obtain ⟨c, hc, hf, _, hcurve⟩ := twoFace_curved_nonvacuity
  obtain ⟨η, hη0, hη, hlip⟩ := hf.strictGraphLipschitz_upper
  exact ⟨c, η, hc, hη0, hη, hf, hcurve, fun x ω _ _ hδ hσ =>
    volume_twoFaceRayGap_crossing hη0 hη hlip _ x ω hδ hσ⟩

-- The expansion's constant is NOT assumed equal to the density's value at zero.
-- Nor are geometric measurability, boundedness or integrability left as premises.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ)
    (hjet : ∃ b₀ b₁ b₂ : ℝ,
      (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
        (b₀ + b₁ * σ + b₂ * σ ^ 2)) =o[𝓝[>] (0 : ℝ)] (fun σ => σ ^ 2)) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) :=
  hf.tendsto_normalized_longOverlap_of_quadratic_jet hδ hjet

-- The finite-density identities and integrability do NOT require a jet at all,
-- and the half-line replacement works for every real density.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    IntegrableOn (fun z => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) (longFuture δ) ∧
    IntegrableOn (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ *
      bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (Ioi 0) ∧
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ in Ioi 0, longOverlapDensity (twoFaceRegion h f) δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) :=
  ⟨hf.integrableOn_longOverlap_bdg δ ρ, hf.integrableOn_longOverlapDensity_bdg δ ρ hδ,
    hf.integral_longOverlap_bdg_Ioi hδ ρ⟩

-- The point value at the endpoint is irrelevant to the whole/half-line identity.
example (M : Set Spacetime) (δ : ℝ) :
    (∫ σ : ℝ, (if σ = 0 then 73 else -2) * longOverlapDensity M δ σ) =
      ∫ σ : ℝ in Ioi 0, (-2) * longOverlapDensity M δ σ := by
  rw [integral_longOverlapDensity_eq_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro σ hσ
  simp only [if_neg (ne_of_gt (show 0 < σ from hσ))]

end TwoFaceLongNullRegression
