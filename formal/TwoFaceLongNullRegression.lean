import BoundaryDraft

/-!
Independent regressions of the unconditional ACTUAL-density jet and fixed-cutoff
long-overlap cancellation. The separate component regressions retain the long
fibre/root and atomic-contact proofs; here short witnesses couple the same
examples to the final unconditional geometric theorems.
Neither cutoff removal nor a complete two-face action limit is asserted.
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
theorem cap_contact_critical (ω : OverlapSphere) :
    twoFaceRayGap cap (fun _ => 0) 0 ω 0 (1 / 2) = 0 ∧
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
theorem cap_contact_nonopening (ω : OverlapSphere) {σ v : ℝ}
    (hσ : 0 ≤ σ) (hv : 1 / 2 ≤ v) :
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
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) :=
  hf.tendsto_normalized_longOverlap hδ

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

/-- Restate all three unconditional targets, including the original coefficient
and both density factors in the negative signed action contribution. -/
def ActualLongCancellation (h f : Spatial → ℝ) (δ : ℝ) : Prop :=
  (∃ b0 b1 b2 : ℝ,
    (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
      (b0 + b1 * σ + b2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2)) ∧
  Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
    ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) ∧
  Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
    ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0)

theorem actual_from_admissible {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) : ActualLongCancellation h f δ :=
  ⟨hf.longOverlapDensity_right_quadratic_jet hδ, hf.tendsto_longOverlap hδ,
    hf.tendsto_normalized_longOverlap hδ⟩

-- Every original planar cap is admitted, without new raw-profile assumptions.
theorem original_planar {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    {δ : ℝ} (hδ : 0 < δ) : ActualLongCancellation h (fun _ => 0) δ :=
  actual_from_admissible hh.twoFace_planar hδ

-- The old unequal-axis cap's positive-height critical point is retained.
theorem unequal_axis_critical (ω : OverlapSphere) : cap 0 = 1 / 4 ∧
    fderiv ℝ (fun x : JointSpace => cap x) 0 = 0 ∧
    ActualLongCancellation cap (fun _ => 0) (1 / 4) :=
  ⟨by norm_num [cap, ellipsoidProfile], (cap_contact_critical ω).2,
    original_planar cap_admissible (by norm_num)⟩

-- Exact cutoff contact, not the interior-root coefficient formula at contact.
theorem exact_cutoff_contact : ActualLongCancellation cap (fun _ => 0) (1 / 2) ∧
    ∀ ω : OverlapSphere,
      twoFaceRayGap cap (fun _ => 0) 0 ω 0 (1 / 2) = 0 ∧
      ∀ σ v : ℝ, 0 ≤ σ → 1 / 2 ≤ v →
        max 0 (twoFaceRayGap cap (fun _ => 0) 0 ω σ v) = 0 :=
  ⟨original_planar cap_admissible (by norm_num), fun ω =>
    ⟨(cap_contact_critical ω).1, fun _ _ hσ hv => cap_contact_nonopening ω hσ hv⟩⟩

-- The averaged geometric theorem still holds in a fixed region with roots
-- approaching the cutoff. It does not assert uniform fibre little-o.
theorem approaching_cutoff : ActualLongCancellation cap (fun _ => 0) (1 / 4) ∧
    ∃ R : ℝ → ℝ,
      (∀ t ∈ Ioc 0 (1 / 4), ∀ ω : OverlapSphere, 1 / 4 < R t ∧
        twoFaceRayGap cap (fun _ => 0) ![Real.sqrt (1 / 2 - 2 * t), 0, 0]
          ω 0 (R t) = 0) ∧ Tendsto R (𝓝[>] 0) (𝓝 (1 / 4)) := by
  refine ⟨original_planar cap_admissible (by norm_num), fun t => 1 / 4 + t, ?_, ?_⟩
  · intro t ht ω
    have hs : 0 ≤ (1 : ℝ) / 2 - 2 * t := by linarith [ht.2]
    have hh : cap ![Real.sqrt (1 / 2 - 2 * t), 0, 0] = 1 / 8 + t / 2 := by
      norm_num [cap, ellipsoidProfile, Fin.sum_univ_succ, Real.sq_sqrt hs]
      ring
    refine ⟨by linarith [ht.1], ?_⟩
    simp only [twoFaceRayGap, twoFaceGap, hh, zero_div, add_zero, sub_zero,
      max_eq_right (show 0 ≤ (1 : ℝ) / 8 + t / 2 by linarith [ht.1])]
    ring
  · simpa using (tendsto_const_nhds (x := (1 : ℝ) / 4)).add
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))

-- Genuinely curved sine face, with its nonaffinity witness and EVERY fixed δ.
theorem curved_sine_future : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 ∧
    ∀ δ : ℝ, 0 < δ → ActualLongCancellation
      (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) δ := by
  obtain ⟨c, hc, hf, _, hcurve⟩ := twoFace_curved_nonvacuity
  exact ⟨c, hc, hf, hcurve, fun _ hδ => actual_from_admissible hf hδ⟩

-- The empty active tube causes no failure of a finite-measure argument.
theorem empty_region {δ : ℝ} (hδ : 0 < δ) :
    twoFaceRegion (fun _ => 0) (fun _ => 0) = ∅ ∧
    ActualLongCancellation (fun _ => 0) (fun _ => 0) δ := by
  have hh : AdmissibleGraphCap (fun _ => 0) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simp
    · exact ⟨0, le_rfl, zero_lt_one, by simp⟩
    · intro x _; exact contDiffAt_const
    · simp
    · simp
  refine ⟨?_, original_planar hh hδ⟩
  ext p
  change (0 - 0 < p 0 ∧ p 0 < 0) ↔ False
  constructor
  · rintro ⟨hp, hn⟩; linarith
  · exact False.elim

-- No nonempty or positive-volume premise is hidden in the geometric theorem.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (hz : volume (twoFaceRegion h f) = 0) {δ : ℝ} (hδ : 0 < δ) :
    (∀ σ, longOverlapDensity (twoFaceRegion h f) δ σ = 0) ∧
    ActualLongCancellation h f δ :=
  ⟨fun σ => longOverlapDensity_zero_of_volume_zero hz δ σ, actual_from_admissible hf hδ⟩

-- A nonempty zero-volume set also has the exact unchanged zero density.
example (δ σ : ℝ) : longOverlapDensity ({0} : Set Spacetime) δ σ = 0 :=
  longOverlapDensity_zero_of_volume_zero (measure_singleton 0) δ σ

-- The oriented/closed length convention removes only a null endpoint;
-- the density identity itself is pointwise, including σ = 0.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ V : ℝ}
    (hδ : 0 < δ) (hV : δ < V)
    (hclear : ∀ x ω, twoFaceRayGap h f x ω 0 V ≤ 0) :
    longOverlapDensity (twoFaceRegion h f) δ 0 =
      ∫ p : TwoFaceLongNull.Parameter, MonotoneHinge.fibre
        (twoFaceRayGap h f p.2 p.1) TwoFaceLongGeometry.weight δ V 0
        ∂(overlapSphereMeasure.prod volume) :=
  hf.longOverlapDensity_eq_parameterFibre hδ hV le_rfl (sq_pos_of_pos hδ) hclear

end TwoFaceLongNullRegression
