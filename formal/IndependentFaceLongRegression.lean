import BoundaryDraft.IndependentFaceLongNull
import BoundaryDraft.IndependentFaceExamples

/-!
Independent class-E long contracts. The steep capsule is not admitted by the
old coordinate class. Exact contacts are treated pointwise, not deleted, and
positive-height critical points remain. No short/full limit is inferred.
-/

open BoundaryDraft MeasureTheory Set Filter Asymptotics
open scoped Topology Interval
noncomputable section
namespace IndependentFaceLongRegression

/-- Independently expand the actual density, signed original kernel, interval
coefficient and both physical density factors. -/
def ActualLong (h f : Spatial → ℝ) (δ : ℝ) : Prop :=
  (∃ b0 b1 b2 : ℝ,
    (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
      (b0 + b1 * σ + b2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2)) ∧
  Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
    ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) ∧
  Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
    ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0)

theorem actual {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) : ActualLong h f δ :=
  ⟨hf.longOverlapDensity_right_quadratic_jet hδ, hf.tendsto_longOverlap hδ,
    hf.tendsto_normalized_longOverlap hδ⟩

/-- The steep witness has a retained interior critical point and cannot use
an original-class action theorem. Every fixed positive long cutoff is allowed. -/
theorem steep {δ : ℝ} (hδ : 0 < δ) :
    ¬AdmissibleTwoFace steepCapsuleHeight steepCapsuleFuture ∧
    steepCapsuleHeight 0 = 3 / 4 ∧
    fderiv ℝ (fun x : JointSpace => steepCapsuleHeight x) 0 = 0 ∧
    ActualLong steepCapsuleHeight steepCapsuleFuture δ :=
  ⟨steepCapsule_not_old_twoFace, steepCapsule_positive_critical.1,
    steepCapsule_positive_critical.2, actual steepCapsule_admissible hδ⟩

-- Original callers and old inclusion both remain usable, without new premises.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) :
    ActualLong h f δ := actual hf.toIndependentTwoFace hδ

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i)
    {δ : ℝ} (hδ : 0 < δ) : ActualLong (ellipsoidProfile a b) (fun _ => 0) δ :=
  actual (planarEllipsoid_independent a b ha hb) hδ

-- Empty closure imposes no global continuity on the raw future. The long
-- theorem must differentiate the causal envelope, not this arbitrary function.
example (f : Spatial → ℝ) {δ : ℝ} (hδ : 0 < δ) : ActualLong (fun _ => -1) f δ := by
  have hf : AdmissibleIndependentTwoFace (fun _ => -1) f := {
    bounded_positive := by norm_num
    smooth_near := fun _ _ => contDiffAt_const
    boundary_zero := by norm_num
    regular_zero := by norm_num
    smooth_future := by norm_num [graphClosedPositive]
    envelopes := ⟨fun _ => 0, fun _ => 0, ⟨0, le_rfl, zero_lt_one, by simp⟩,
      ⟨0, le_rfl, zero_lt_one, by simp⟩, by norm_num, by norm_num [graphClosedPositive]⟩ }
  exact actual hf hδ

/-- All contact regimes and the moving coefficient, with one common bound
before the spatial/directional quantifiers. No uniform little-o is asserted. -/
example {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ε c A M B : ℝ, δ < V ∧ 0 < ε ∧ ∀ (x : Spatial) (ω : OverlapSphere),
      let g := twoFaceRayGap h hf.upperEnvelope x ω
      let J := TwoFaceLongGeometry.weight
      ((g 0 δ < 0 ∧ ∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre g J δ V σ = 0) ∨
        (g 0 δ = 0 ∧ ∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre g J δ V σ = 0) ∨
        (0 < g 0 δ ∧ ∃! R : ℝ, R ∈ Ioo δ V ∧ g 0 R = 0)) ∧
      (∀ σ ∈ Ioc 0 ε,
        |MonotoneHinge.fibre g J δ V σ -
          (MonotoneHinge.F0 g J δ V + MonotoneHinge.F1 g J δ V * σ +
            MonotoneHinge.F2 g J δ V * σ ^ 2)| / σ ^ 2 ≤
              MonotoneHinge.remainderBound δ V c A M B) ∧
      (∀ R ∈ Ioo δ V, g 0 R = 0 →
        MonotoneHinge.F2 g J δ V =
          (1 / 2 * ∫ v in δ..R, deriv (fun s => deriv (fun t => J t v * g t v) s) 0) +
            J 0 R * (deriv (fun s => g s R) 0) ^ 2 / (2 * (-deriv (g 0) R))) := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, _, _, _, _, hall⟩ := hf.exists_long_hypotheses hδ
  exact ⟨V, ε, c, A, M, B, hV, hε, fun x ω =>
    ⟨(hall x ω).three_regimes, fun _ hσ => (hall x ω).normalized_remainder_bound hσ,
      fun _ hR hz => ((hall x ω).coefficients_of_root hR hz).2.2⟩⟩

-- E24 detects the invalid old shortcut: thickness 3/2, face constants 3/4.
example : TwoFaceLongGeometry.perturbationWidth (3 / 2) (1 / 4) (1 / 4) = 1 / 320 ∧
    (3 / 2 : ℝ) * (1 / 320) / (2 * (1 / 4)) ≤ (1 / 4) * (1 / 4) / 4 ∧
    (3 / 2 : ℝ) * ((1 / 4) * (1 / 4) ^ 2 / 2) / (2 * (1 / 4)) >
      (1 / 4) * (1 / 4) / 4 := by
  norm_num [TwoFaceLongGeometry.perturbationWidth]

-- The endpoint lemma has two independent margins, not one combined margin.
example {h u : Spatial → ℝ}
    (hu : ∀ x y, |u x - u y| ≤ (3 / 4 : ℝ) * spatialDistance x y)
    (hl : ∀ x y, |(u x - max 0 (h x)) - (u y - max 0 (h y))| ≤
      (3 / 4 : ℝ) * spatialDistance x y)
    (x y : Spatial) (s : ℝ) (hd : spatialDistance x y ≤ s)
    (hg : 0 ≤ twoFaceGap h u x y s) :
    s / 4 ≤ max 0 (h x) ∧ s / 4 ≤ max 0 (h y) := by
  convert LongEnvelopeData.gap_height_margins (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) hl hu x y s hd hg using 1 <;> ring_nf

-- The compact smooth tube includes OLD active points even with NEGATIVE new gap.
example {h u : Spatial → ℝ} (hh : RegularHeight h)
    (hH : ∀ x y, |max 0 (h x) - max 0 (h y)| ≤ (3 / 2 : ℝ) * spatialDistance x y)
    (hm : ∀ (x y : Spatial) (s : ℝ), spatialDistance x y ≤ s →
      0 ≤ twoFaceGap h u x y s →
      (1 / 4) * s ≤ max 0 (h x) ∧ (1 / 4) * s ≤ max 0 (h y))
    (x : Spatial) (ω : OverlapSphere) {σ v : ℝ}
    (hv : 1 / 4 ≤ v) (hσ : σ ∈ Icc 0 (1 / 320))
    (hold : 0 ≤ twoFaceRayGap h u x ω 0 v) :
    IsCompact (TwoFaceLongGeometry.tube h (1 / 64)) ∧
    (WithLp.equiv 2 _).symm (x + spatialPolar ω ((v - σ / v) / 2)) ∈
      TwoFaceLongGeometry.tube h (1 / 64) := by
  refine ⟨TwoFaceLongGeometry.compact_tube_of_regular hh _, ?_⟩
  apply TwoFaceLongGeometry.mem_tube_of_margin (by norm_num)
  convert TwoFaceLongGeometry.perturbed_endpoint_margin
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) < 1 / 4) hH hm (by norm_num) x ω hv hσ hold using 1
  norm_num

private def U : Spatial → ℝ := steepCapsule_admissible.upperEnvelope

private theorem height_ray (ω : OverlapSphere) (t : ℝ) :
    steepCapsuleHeight (spatialPolar ω t) = (3 / 4 : ℝ) * (1 - t ^ 2) := by
  have hn := mem_sphere_zero_iff_norm.mp ω.property
  change steepCapsuleHeight (t • ω.val) = _
  rw [steepCapsule_height, norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs]

private theorem upper_ray (ω : OverlapSphere) (t : ℝ) (ht : t ^ 2 < 1) :
    U (spatialPolar ω t) = (3 / 8 : ℝ) * (1 - t ^ 2) := by
  have hh : 0 < steepCapsuleHeight (spatialPolar ω t) := by
    rw [height_ray]
    exact mul_pos (by norm_num) (sub_pos.mpr ht)
  rw [U, steepCapsule_admissible.upper_eq _ (subset_closure hh), steepCapsule_future, height_ray]
  ring

/-- An exact rational cutoff contact for EVERY direction. Both endpoints lie
in the positive interior. The chosen envelope is not assumed equal globally
to a clipped quadratic: only the raw-germ agreement at these points is used. -/
theorem steep_contact (ω : OverlapSphere) :
    twoFaceRayGap steepCapsuleHeight U (spatialPolar ω (-1 / 3)) ω 0 (4 / 3) = 0 := by
  have he : spatialPolar ω (-1 / 3) + spatialPolar ω ((4 / 3 - 0 / (4 / 3)) / 2) =
      spatialPolar ω (1 / 3) := by
    ext i
    change (-1 / 3 : ℝ) * ω.val i + ((4 / 3 - 0 / (4 / 3)) / 2) * ω.val i =
      (1 / 3 : ℝ) * ω.val i
    ring
  simp only [twoFaceRayGap, twoFaceGap, he, height_ray,
    upper_ray ω (-1 / 3) (by norm_num), upper_ray ω (1 / 3) (by norm_num)]
  norm_num

/-- Exact contact has all three RIGHT coefficients zero and does not reopen.
The interior-root formula is deliberately not used at cutoff contact. -/
theorem contact_regime : ∃ V ε : ℝ, 4 / 3 < V ∧ 0 < ε ∧ ∀ ω : OverlapSphere,
    let g := twoFaceRayGap steepCapsuleHeight U (spatialPolar ω (-1 / 3)) ω
    MonotoneHinge.F0 g TwoFaceLongGeometry.weight (4 / 3) V = 0 ∧
    MonotoneHinge.F1 g TwoFaceLongGeometry.weight (4 / 3) V = 0 ∧
    MonotoneHinge.F2 g TwoFaceLongGeometry.weight (4 / 3) V = 0 ∧
    (∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre g TwoFaceLongGeometry.weight (4 / 3) V σ = 0) ∧
    (∀ σ : ℝ, 0 < σ → g σ (4 / 3) < 0) := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, _, _, _, _, hall⟩ :=
    steepCapsule_admissible.exists_long_hypotheses (δ := 4 / 3) (by norm_num)
  refine ⟨V, ε, hV, hε, fun ω => ?_⟩
  have hz := steep_contact ω
  obtain ⟨h0, h1, h2⟩ := MonotoneHinge.coefficients_zero
    (J := TwoFaceLongGeometry.weight) (V := V) hz.le
  refine ⟨h0, h1, h2, fun _ hσ => (hall _ ω).fibre_zero hz.le hσ, ?_⟩
  intro σ hσ
  obtain ⟨η, _, hη, hl⟩ := steepCapsule_admissible.strictGraphLipschitz_upper
  have ht := (twoFaceRayGap_transverse_bounds hl steepCapsuleHeight
    (spatialPolar ω (-1 / 3)) ω (by norm_num : (0 : ℝ) < 4 / 3) hσ.le).2
  have hn : -(1 - η) * (σ - 0) / (2 * (4 / 3)) < 0 := by
    apply div_neg_of_neg_of_pos _ (by norm_num)
    exact mul_neg_of_neg_of_pos (by linarith) (by simpa using hσ)
  dsimp only [U] at hz ⊢
  rw [hz] at ht
  linarith

-- Pointwise density identity, not a merely a.e. representative, at sigma=0.
example {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) :
    longOverlapDensity (twoFaceRegion h f) δ 0 =
      ∫ ω, (∫ x : Spatial, ∫ v in Ici δ,
        ((v - 0/v)^2 / (8*v)) * max 0 (twoFaceRayGap h hf.upperEnvelope x ω 0 v))
        ∂overlapSphereMeasure :=
  hf.longOverlapDensity_eq_gap_fibres hδ le_rfl (sq_pos_of_pos hδ)

-- Finite-density transport and both absolute-integrability obligations hold
-- independently of a jet, at every real density, with the original sign intact.
example {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
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

end IndependentFaceLongRegression
