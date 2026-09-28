import BoundaryDraft.WeightedGraphAction
import BoundaryDraft.KernelCollar
import BoundaryDraft.EllipsoidAngle

/-!
# Regulated tangent-wedge ingredients

The bounded tent regulator is specified geometrically, independently of the
answer. The scalar profile below is the reduced observable, not a replacement
for `continuumMean`. The four-dimensional endpoint-weighted reduction and limit
are checked here. The invariant joint-area assembly and uniform-family
interpretation are conventional proofs in `notes/regulated-tangent-wedge.md`,
not newly claimed end-to-end Lean joint-integral theorems.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Coordinate control uses Euclidean distance, even though a coordinate cube
will be used for the artificial regulator. -/
theorem abs_coord_sub_le_spatialDistance (x y : Spatial) (i : Fin 3) :
    |x i - y i| ≤ spatialDistance x y := by
  apply (sq_le_sq₀ (abs_nonneg _) (spatialDistance_nonneg _ _)).mp
  rw [sq_abs, spatialDistance_sq]
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (y j - x j))
    (Finset.mem_univ i)
  nlinarith

private theorem norm_sub_le_spatialDistance (x y : Spatial) :
    ‖x - y‖ ≤ spatialDistance x y := by
  apply (pi_norm_le_iff_of_nonneg (spatialDistance_nonneg _ _)).2
  intro i
  exact abs_coord_sub_le_spatialDistance x y i

/-- A bounded piecewise-spacelike cap agreeing with the wedge near the source
support. Its extra faces are regulators, not part of the proposed joint. -/
def wedgeRegulatorProfile (k H : ℝ) (x : Spatial) : ℝ :=
  min (k * x 0) (H - k * ‖x‖)

/-- Non-vacuous geometric admissibility for the exact reduction. Smoothness
at the artificial seams is neither asserted nor needed. -/
theorem wedgeRegulator_data {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (H : ℝ) :
    GraphCapData (wedgeRegulatorProfile k H) := by
  constructor
  · apply isBounded_iff_forall_norm_le.2
    refine ⟨H / k, ?_⟩
    intro x hx
    have hh : 0 < H - k * ‖x‖ := (lt_min_iff.mp hx).2
    apply (le_div_iff₀ hk).2
    nlinarith
  · refine ⟨k, hk.le, hk1, ?_⟩
    intro x y
    have hfirst : |k * x 0 - k * y 0| ≤ k * spatialDistance x y := by
      rw [← mul_sub, abs_mul, abs_of_pos hk]
      exact mul_le_mul_of_nonneg_left (abs_coord_sub_le_spatialDistance x y 0) hk.le
    have hsecond : |(H - k * ‖x‖) - (H - k * ‖y‖)| ≤ k * spatialDistance x y := by
      rw [show (H - k * ‖x‖) - (H - k * ‖y‖) = -(k * (‖x‖ - ‖y‖)) by ring,
        abs_neg, abs_mul, abs_of_pos hk]
      exact mul_le_mul_of_nonneg_left
        ((abs_norm_sub_norm_le x y).trans (norm_sub_le_spatialDistance x y)) hk.le
    have hp := (abs_min_sub_min_le_max (k * x 0) (H - k * ‖x‖)
      (k * y 0) (H - k * ‖y‖)).trans (max_le hfirst hsecond)
    have hm : |max 0 (wedgeRegulatorProfile k H x) -
        max 0 (wedgeRegulatorProfile k H y)| ≤
        |wedgeRegulatorProfile k H x - wedgeRegulatorProfile k H y| := by
      simpa only [max_comm] using
        (abs_max_sub_max_le_abs (wedgeRegulatorProfile k H x)
          (wedgeRegulatorProfile k H y) 0)
    exact hm.trans hp

/-- A cube of source points lies in the affine part of the regulator whenever
the independently specified height margin holds. -/
theorem wedgeRegulator_eq_affine {k H R : ℝ} (hk : 0 ≤ k)
    (hH : 2 * k * R ≤ H) {x : Spatial} (hx : ‖x‖ ≤ R) :
    wedgeRegulatorProfile k H x = k * x 0 := by
  apply min_eq_left
  have hcoord : x 0 ≤ R := (le_abs_self _).trans
    ((norm_le_pi_norm x 0).trans hx)
  have h1 := mul_le_mul_of_nonneg_left hcoord hk
  have h2 := mul_le_mul_of_nonneg_left hx hk
  linarith

/-- The explicit regulated action is covered by the checked weighted reduction
at every density, without a coefficient or limit premise. -/
theorem weighted_wedgeRegulator_reduction {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (H ρ : ℝ) (a : Spatial → ℝ) (ha : Continuous a) :
    weightedContinuumMean ρ (graphCapRegion (wedgeRegulatorProfile k H))
      (fun p => a (spatialPart p)) =
      ∫ x in {x | 0 < wedgeRegulatorProfile k H x},
        a x * planeKernel ρ (wedgeRegulatorProfile k H x) :=
  weighted_graphCap_reduction _ (wedgeRegulator_data hk hk1 H) a ha ρ

/-- The scalar expression obtained after integrating tangential coordinates
and substituting height `s = k*r`. It is not the definition of a region action. -/
def wedgeProfileMean (ρ k : ℝ) (B : ℝ → ℝ) : ℝ :=
  k⁻¹ * ∫ s in Ioi (0 : ℝ), planeKernel ρ s * B (s / k)

/-- Tangential integration in the independently chosen orthonormal joint
coordinates; no angle coefficient is built into this profile. -/
def wedgeTangentialProfile (a : Spatial → ℝ) (r : ℝ) : ℝ :=
  ∫ z : Fin 2 → ℝ, a (Fin.cons r z)

private theorem norm_tail_le_cons (r : ℝ) (z : Fin 2 → ℝ) :
    ‖z‖ ≤ ‖(Fin.cons r z : Spatial)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  simpa using norm_le_pi_norm (Fin.cons r z : Spatial) i.succ

/-- A fixed compact tangential domain dominates every normal slice. -/
theorem wedgeTangentialProfile_eq_compact (a : Spatial → ℝ) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → a x = 0) (r : ℝ) :
    wedgeTangentialProfile a r =
      ∫ z in Metric.closedBall (0 : Fin 2 → ℝ) R, a (Fin.cons r z) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hsource _ ((by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz :
    R < ‖z‖).trans_le (norm_tail_le_cons r z))

/-- Continuity of the profile is derived from the test weight, not a new
analytic assumption about a geometric overlap. -/
theorem continuous_wedgeTangentialProfile (a : Spatial → ℝ) (ha : Continuous a)
    (R : ℝ) (hsource : ∀ x, R < ‖x‖ → a x = 0) :
    Continuous (wedgeTangentialProfile a) := by
  simp_rw [show wedgeTangentialProfile a = fun r =>
      ∫ z in Metric.closedBall (0 : Fin 2 → ℝ) R, a (Fin.cons r z) from
    funext (wedgeTangentialProfile_eq_compact a R hsource)]
  apply continuous_parametric_integral_of_continuous _ (isCompact_closedBall 0 R)
  apply ha.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

theorem hasCompactSupport_wedgeTangentialProfile (a : Spatial → ℝ) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → a x = 0) : HasCompactSupport (wedgeTangentialProfile a) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
  intro r hr
  have hr' : R < ‖r‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hr
  change (∫ z : Fin 2 → ℝ, a (Fin.cons r z)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  exact hsource _ (hr'.trans_le (by simpa using norm_le_pi_norm (Fin.cons r z : Spatial) 0))

private theorem integral_spatial_first (f : Spatial → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ r : ℝ, ∫ z : Fin 2 → ℝ, f (Fin.cons r z) := by
  let E : (ℝ × (Fin 2 → ℝ)) ≃ᵐ Spatial :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have hE : MeasurePreserving E :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _
  have hi := (hE.integrable_comp_emb E.measurableEmbedding).mpr hf
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  rw [← hE.integral_comp' f, Measure.volume_eq_prod, integral_prod _ hi]
  simp [E, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

/-- Actual four-dimensional regulated action to the scalar profile. The support
and margin hypotheses are geometric and independent of the desired answer.
All causal partners remain in the cap's complete future slices. -/
theorem weighted_wedgeRegulator_eq_profile {k H R : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hH : 2 * k * R ≤ H) (ρ : ℝ) (a : Spatial → ℝ) (ha : Continuous a)
    (hsource : ∀ x, R < ‖x‖ → a x = 0) :
    weightedContinuumMean ρ (graphCapRegion (wedgeRegulatorProfile k H))
      (fun p => a (spatialPart p)) = wedgeProfileMean ρ k (wedgeTangentialProfile a) := by
  have hs : HasCompactSupport a := HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun x hx => hsource x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
  have hc : Continuous (fun x : Spatial => a x * planeKernel ρ (k * x 0)) :=
    ha.mul ((continuous_planeKernel ρ).comp (continuous_const.mul (continuous_apply 0)))
  have hi : Integrable (fun x : Spatial => a x * planeKernel ρ (k * x 0)) :=
    hc.integrable_of_hasCompactSupport hs.mul_right
  have hm : MeasurableSet {x : Spatial | 0 < x 0} :=
    (isOpen_lt continuous_const (continuous_apply 0)).measurableSet
  rw [weighted_wedgeRegulator_reduction hk hk1 H ρ a ha,
    ← integral_indicator (wedgeRegulator_data hk hk1 H).measurableSet_positive]
  have he : {x | 0 < wedgeRegulatorProfile k H x}.indicator
      (fun x => a x * planeKernel ρ (wedgeRegulatorProfile k H x)) =
      {x : Spatial | 0 < x 0}.indicator (fun x => a x * planeKernel ρ (k * x 0)) := by
    ext x
    by_cases hx : ‖x‖ ≤ R
    · simp only [Set.indicator, mem_setOf_eq, wedgeRegulator_eq_affine hk.le hH hx,
        mul_pos_iff_of_pos_left hk]
    · simp [Set.indicator, hsource x (lt_of_not_ge hx)]
  rw [he, integral_spatial_first _ (hi.indicator hm)]
  have hf (r : ℝ) : (∫ z : Fin 2 → ℝ, {x : Spatial | 0 < x 0}.indicator
      (fun x => a x * planeKernel ρ (k * x 0)) (Fin.cons r z)) =
      (Ioi (0 : ℝ)).indicator
        (fun r => planeKernel ρ (k * r) * wedgeTangentialProfile a r) r := by
    by_cases hr : 0 < r
    · simp [Set.indicator, hr, wedgeTangentialProfile, integral_mul_const, integral_const_mul, mul_comm]
    · simp [Set.indicator, hr]
  simp_rw [hf]
  rw [integral_indicator measurableSet_Ioi]
  have hc' := integral_comp_mul_left_Ioi
    (fun s => planeKernel ρ s * wedgeTangentialProfile a (s / k)) 0 hk
  simpa [wedgeProfileMean, mul_zero, mul_div_cancel_left₀ _ hk.ne', smul_eq_mul] using hc'

theorem integrableOn_wedgeProfile {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ r, 0 ≤ r → ‖B r‖ ≤ C) :
    IntegrableOn (fun s => planeKernel ρ s * B (s / k)) (Ioi (0 : ℝ)) := by
  apply integrableOn_planeKernel_mul_bounded ρ hρ _
    (hB.comp (measurable_id.div_const k)) C
  intro s hs
  exact hbound _ (div_nonneg hs.le hk.le)

/-- The full signed profile has the positive-angle coefficient, using the
existing mass theorem. Only right continuity is required at the joint. -/
theorem wedgeProfileMean_limit {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (B : ℝ → ℝ) (hB : Measurable B) (hB0 : ContinuousWithinAt B (Ici 0) 0)
    (C : ℝ) (hbound : ∀ r, 0 ≤ r → ‖B r‖ ≤ C) :
    Tendsto (fun ρ => wedgeProfileMean ρ k B) atTop (𝓝 (jointCoth k * B 0)) := by
  have h0 : ContinuousWithinAt (fun s => B (s / k)) (Ici 0) 0 := by
    exact hB0.comp_of_eq (f := fun s : ℝ => s / k)
      (continuousWithinAt_id.div_const k)
      (fun _ hs => div_nonneg hs hk.le) (by simp)
  have hl := planeKernel_halfLine_limit_right (fun s => B (s / k))
    (hB.comp (measurable_id.div_const k)) h0 C
    (fun s hs => hbound _ (div_nonneg hs hk.le))
  have hc := (jointRapidity_identities k hk hk1).2.2.2.2
  simpa [wedgeProfileMean, hc, one_div] using hl.const_mul k⁻¹

/-- The regulated wedge limit from the actual four-dimensional weighted
action, with all analytic hypotheses discharged from a continuous compactly
supported spatial test observable. Invariant-area interpretation is separate. -/
theorem weighted_wedgeRegulator_limit {k H R : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hH : 2 * k * R ≤ H) (a : Spatial → ℝ) (ha : Continuous a)
    (hsource : ∀ x, R < ‖x‖ → a x = 0) :
    Tendsto (fun ρ => weightedContinuumMean ρ
      (graphCapRegion (wedgeRegulatorProfile k H)) (fun p => a (spatialPart p)))
      atTop (𝓝 (jointCoth k * ∫ z : Fin 2 → ℝ, a (Fin.cons 0 z))) := by
  have hc := continuous_wedgeTangentialProfile a ha R hsource
  obtain ⟨C, hC⟩ := (hasCompactSupport_wedgeTangentialProfile a R hsource).exists_bound_of_continuous hc
  simpa only [weighted_wedgeRegulator_eq_profile hk hk1 hH _ a ha hsource] using
    wedgeProfileMean_limit hk hk1 _ hc.measurable hc.continuousWithinAt C (fun r _ => hC r)

/-- An absolute error estimate *after* the signed mass cancellation. The
constant uses the proved finite first absolute moment; it is uniform when
`k` has a fixed positive lower bound and the normal Lipschitz constant is fixed. -/
theorem wedgeProfileMean_error {ρ k L : ℝ} (hρ : 0 < ρ) (hk : 0 < k)
    (B : ℝ → ℝ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ r, 0 ≤ r → ‖B r‖ ≤ C)
    (hLip : ∀ r, 0 ≤ r → ‖B r - B 0‖ ≤ L * r) :
    ‖wedgeProfileMean ρ k B - k⁻¹ * B 0‖ ≤
      (L * (Real.sqrt (Real.sqrt ρ))⁻¹ / k ^ 2) *
        ∫ u in Ioi (0 : ℝ), u * |planeKernel 1 u| := by
  let ε := (Real.sqrt (Real.sqrt ρ))⁻¹
  have hε : 0 < ε := inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hρ))
  let f := fun u => planeKernel 1 u * B (ε * u / k)
  have hi : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply integrableOn_planeKernel_mul_bounded 1 zero_lt_one _
      (hB.comp ((measurable_const.mul measurable_id).div_const k)) C
    intro u hu
    exact hbound _ (div_nonneg (mul_nonneg hε.le hu.le) hk.le)
  have he : wedgeProfileMean ρ k B - k⁻¹ * B 0 =
      k⁻¹ * ∫ u in Ioi (0 : ℝ), planeKernel 1 u * (B (ε * u / k) - B 0) := by
    rw [wedgeProfileMean, integral_planeKernel_mul_eq_rescaled _ ρ hρ]
    simp only [mul_sub]
    rw [integral_sub hi (integrableOn_planeKernel.mul_const (B 0)),
      integral_mul_const, integral_planeKernel_Ioi]
    ring
  have hest : ‖∫ u in Ioi (0 : ℝ), planeKernel 1 u * (B (ε * u / k) - B 0)‖ ≤
      (L * ε / k) * ∫ u in Ioi (0 : ℝ), u * |planeKernel 1 u| := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (integrableOn_mul_abs_planeKernel.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Real.norm_eq_abs (planeKernel 1 u)]
    calc
      _ ≤ |planeKernel 1 u| * (L * (ε * u / k)) :=
        mul_le_mul_of_nonneg_left
          (hLip _ (div_nonneg (mul_nonneg hε.le (le_of_lt hu)) hk.le)) (abs_nonneg _)
      _ = _ := by ring
  rw [he, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
  convert mul_le_mul_of_nonneg_left hest (inv_nonneg.mpr hk.le) using 1
  dsimp [ε]
  ring

end BoundaryDraft
