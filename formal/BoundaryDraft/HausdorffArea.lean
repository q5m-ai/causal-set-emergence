import BoundaryDraft.HausdorffLinear

/-!
# The variable-Jacobian area formula for scalar Euclidean graphs

Local graph/tangent distortion and the exact tangent-image calculation give
local domination, absolute continuity, and shrinking closed-ball ratios. The
Lebesgue differentiation uniqueness theorem then identifies the pullback.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace BoundaryDraft

/-- The area density of a scalar graph, using its actual Euclidean derivative. -/
def surfaceGraphJacobian (g : SurfacePlane → ℝ) (x : SurfacePlane) : ℝ :=
  Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)

theorem surfaceGraphJacobian_pos (g : SurfacePlane → ℝ) (x : SurfacePlane) :
    0 < surfaceGraphJacobian g x := Real.sqrt_pos.2 (by positivity)

/-- Normalized local bounds on every subset of a small ball. -/
theorem surfaceGraph_local_measure_bounds (g : SurfacePlane → ℝ)
    (hg : Continuous g) (U : Set SurfacePlane) (hU : IsOpen U)
    (hgU : ContDiffOn ℝ 1 g U) (a : SurfacePlane) (ha : a ∈ U)
    (ε : ℝ≥0) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧ ∀ s ⊆ ball a r,
      ENNReal.ofReal ((1 - (ε : ℝ)) ^ 2 * surfaceGraphJacobian g a) * volume s ≤
        surfaceGraphPullbackMeasure g s ∧
      surfaceGraphPullbackMeasure g s ≤
        ENNReal.ofReal ((1 + (ε : ℝ)) ^ 2 * surfaceGraphJacobian g a) * volume s := by
  obtain ⟨r, hr, hU', hb⟩ := surfaceGraph_local_hausdorff_bounds g U hU hgU a ha ε hε0 hε1
  refine ⟨r, hr, hU', fun s hs => ?_⟩
  have h := hb s hs
  have hl := mul_le_mul_left' h.1 (ENNReal.ofReal (Real.pi / 4))
  have hu := mul_le_mul_left' h.2 (ENNReal.ofReal (Real.pi / 4))
  have hc : ∀ c : ℝ≥0∞,
      ENNReal.ofReal (Real.pi / 4) * (c * μH[2] (surfaceGraphDerivative (fderiv ℝ g a) '' s)) =
        c * (ENNReal.ofReal (surfaceGraphJacobian g a) * volume s) := by
    intro c
    rw [mul_left_comm]
    exact congrArg (c * ·) (normalizedHausdorffTwo_surfaceGraphDerivative_image _ s)
  rw [hc] at hl hu
  rw [surfaceGraphPullbackMeasure_apply hg]
  have hminus : ENNReal.ofReal (1 - (ε : ℝ)) = ((1 - ε : ℝ≥0) : ℝ≥0∞) := by
    simpa only [NNReal.coe_sub hε1.le, NNReal.coe_one] using
      (show ENNReal.ofReal ((1 - ε : ℝ≥0) : ℝ) = ((1 - ε : ℝ≥0) : ℝ≥0∞) from
        ENNReal.ofReal_coe_nnreal)
  have hplus : ENNReal.ofReal (1 + (ε : ℝ)) = ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
    simpa only [NNReal.coe_add, NNReal.coe_one] using
      (show ENNReal.ofReal ((1 + ε : ℝ≥0) : ℝ) = ((1 + ε : ℝ≥0) : ℝ≥0∞) from
        ENNReal.ofReal_coe_nnreal)
  simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow
    (sub_nonneg.mpr (show (ε : ℝ) ≤ 1 from hε1.le)),
    ENNReal.ofReal_pow (show 0 ≤ 1 + (ε : ℝ) by positivity), hminus, hplus, mul_assoc] using
      And.intro hl hu

/-- Local finiteness is obtained from the upper distortion bound, not assumed
in the density-uniqueness step. -/
theorem surfaceGraphPullbackMeasure_locallyFinite {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) : IsLocallyFiniteMeasure (surfaceGraphPullbackMeasure g) := by
  constructor
  intro x
  obtain ⟨r, hr, _, hb⟩ := surfaceGraph_local_measure_bounds g hg.continuous univ isOpen_univ
    hg.contDiffOn x (mem_univ x) (1 / 2) (by norm_num)
      (by exact_mod_cast (show (1 / 2 : ℝ) < 1 by norm_num))
  refine ⟨ball x r, ball_mem_nhds x hr, (hb _ (Subset.refl _)).2.trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top isBounded_ball.measure_lt_top

/-- Local domination preserves null sets; second countability globalizes it. -/
theorem surfaceGraphPullbackMeasure_absolutelyContinuous {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) : surfaceGraphPullbackMeasure g ≪ volume := by
  intro s hs
  apply measure_null_of_locally_null s
  intro x _
  obtain ⟨r, hr, _, hb⟩ := surfaceGraph_local_measure_bounds g hg.continuous univ isOpen_univ
    hg.contDiffOn x (mem_univ x) (1 / 2) (by norm_num)
      (by exact_mod_cast (show (1 / 2 : ℝ) < 1 by norm_num))
  refine ⟨ball x r ∩ s, ?_, ?_⟩
  · simpa only [inter_comm] using inter_mem_nhdsWithin s (ball_mem_nhds x hr)
  apply le_antisymm _ (zero_le _)
  have hz : volume (ball x r ∩ s) = 0 := measure_mono_null inter_subset_right hs
  simpa only [hz, mul_zero] using (hb (ball x r ∩ s) inter_subset_left).2

/-- At every C¹ point, the shrinking closed-ball density is the graph
Jacobian. The squeeze is valid in the extended nonnegative reals. -/
theorem surfaceGraphPullbackMeasure_tendsto_closedBall_ratio
    {g : SurfacePlane → ℝ} (hg : Continuous g) (U : Set SurfacePlane)
    (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) (x : SurfacePlane) (hx : x ∈ U) :
    Tendsto (fun r => surfaceGraphPullbackMeasure g (closedBall x r) /
      volume (closedBall x r)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (surfaceGraphJacobian g x))) := by
  let j := surfaceGraphJacobian g x
  have hb (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal ((1 - ε) ^ 2 * j) ≤
          surfaceGraphPullbackMeasure g (closedBall x r) / volume (closedBall x r) ∧
        surfaceGraphPullbackMeasure g (closedBall x r) / volume (closedBall x r) ≤
          ENNReal.ofReal ((1 + ε) ^ 2 * j) := by
    obtain ⟨R, hR, _, hbounds⟩ := surfaceGraph_local_measure_bounds g hg U hU hgU x hx
      ⟨ε, hε.1.le⟩ hε.1 hε.2
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hR)] with r hr0 hrR
    have hvol0 : volume (closedBall x r) ≠ 0 := (measure_closedBall_pos volume x hr0).ne'
    have hvoltop : volume (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
    have hh := hbounds (closedBall x r) (closedBall_subset_ball hrR)
    have hlo := ENNReal.div_le_div_right hh.1 (volume (closedBall x r))
    have hup := ENNReal.div_le_div_right hh.2 (volume (closedBall x r))
    rw [ENNReal.mul_div_cancel_right hvol0 hvoltop] at hlo hup
    exact ⟨hlo, hup⟩
  have hl : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ 2 * j))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal j)) := by
    have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ 2 * j)) :=
      ENNReal.continuous_ofReal.comp
        ((continuous_const.sub continuous_id).pow 2 |>.mul continuous_const)
    simpa only [sub_zero, one_pow, one_mul] using h.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hu : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ 2 * j))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal j)) := by
    have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ 2 * j)) :=
      ENNReal.continuous_ofReal.comp
        ((continuous_const.add continuous_id).pow 2 |>.mul continuous_const)
    simpa only [add_zero, one_pow, one_mul] using h.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one))
  apply tendsto_order.2
  constructor
  · intro c hc
    obtain ⟨ε, hε, hcε⟩ := (he.and ((tendsto_order.1 hl).1 c hc)).exists
    exact (hb ε hε).mono fun r hr => hcε.trans_le hr.1
  · intro c hc
    obtain ⟨ε, hε, hεc⟩ := (he.and ((tendsto_order.1 hu).2 c hc)).exists
    exact (hb ε hε).mono fun r hr => hr.2.trans_lt hεc

/-- The variable-Jacobian graph area formula, obtained by closed-ball density
uniqueness after proving local finiteness and absolute continuity. -/
theorem surfaceGraphPullbackMeasure_eq_withDensity {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) :
    surfaceGraphPullbackMeasure g =
      volume.withDensity (fun x => ENNReal.ofReal (surfaceGraphJacobian g x)) := by
  letI := surfaceGraphPullbackMeasure_locallyFinite hg
  exact measure_eq_withDensity_of_tendsto_closedBall_ratio _ _
    (surfaceGraphPullbackMeasure_absolutelyContinuous hg)
    (fun x => surfaceGraphPullbackMeasure_tendsto_closedBall_ratio hg.continuous
      univ isOpen_univ hg.contDiffOn x (mem_univ x))

theorem continuous_surfaceGraphJacobian {g : SurfacePlane → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (surfaceGraphJacobian g) :=
  (continuous_const.add ((hg.continuous_fderiv le_rfl).norm.pow 2)).sqrt

/-- Equivalent pushforward form of the area formula. -/
theorem normalizedHausdorffTwo_restrict_surfaceGraph {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) :
    normalizedHausdorffTwo.restrict (range (surfaceGraph g)) =
      Measure.map (surfaceGraph g)
        (volume.withDensity (fun x => ENNReal.ofReal (surfaceGraphJacobian g x))) := by
  rw [← surfaceGraphPullbackMeasure_eq_withDensity hg]
  exact ((continuous_measurableEmbedding_surfaceGraph hg.continuous).map_comap _).symm

/-- The area formula restricted to any measurable parameter domain. -/
theorem normalizedHausdorffTwo_restrict_surfaceGraph_image {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) (s : Set SurfacePlane) (hs : MeasurableSet s) :
    normalizedHausdorffTwo.restrict (surfaceGraph g '' s) =
      Measure.map (surfaceGraph g)
        ((volume.restrict s).withDensity (fun x => ENNReal.ofReal (surfaceGraphJacobian g x))) := by
  let hf := continuous_measurableEmbedding_surfaceGraph hg.continuous
  rw [← restrict_withDensity hs]
  have h := hf.restrict_map
    (volume.withDensity (fun x => ENNReal.ofReal (surfaceGraphJacobian g x)))
    (surfaceGraph g '' s)
  rw [hf.injective.preimage_image, ← normalizedHausdorffTwo_restrict_surfaceGraph hg,
    Measure.restrict_restrict_of_subset (image_subset_range _ _)] at h
  exact h

/-- Signed graph integration, derived from the measure identity. Integrability
is not assumed to manufacture the equality; both sides use the same Bochner
integral convention when they are not integrable. -/
theorem integral_normalizedHausdorffTwo_surfaceGraph {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) (f : JointSpace → ℝ) (s : Set SurfacePlane)
    (hs : MeasurableSet s) :
    (∫ y in surfaceGraph g '' s, f y ∂normalizedHausdorffTwo) =
      ∫ x in s, surfaceGraphJacobian g x * f (surfaceGraph g x) := by
  rw [normalizedHausdorffTwo_restrict_surfaceGraph_image hg s hs,
    (continuous_measurableEmbedding_surfaceGraph hg.continuous).integral_map,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_surfaceGraphJacobian hg).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (surfaceGraphJacobian_pos g x).le, smul_eq_mul]

/-- Absolute integrability transforms by the same genuine area density. -/
theorem integrable_normalizedHausdorffTwo_surfaceGraph_iff {g : SurfacePlane → ℝ}
    (hg : ContDiff ℝ 1 g) (f : JointSpace → ℝ) (s : Set SurfacePlane)
    (hs : MeasurableSet s) :
    IntegrableOn f (surfaceGraph g '' s) normalizedHausdorffTwo ↔
      IntegrableOn (fun x => surfaceGraphJacobian g x * f (surfaceGraph g x)) s := by
  unfold IntegrableOn
  rw [normalizedHausdorffTwo_restrict_surfaceGraph_image hg s hs,
    (continuous_measurableEmbedding_surfaceGraph hg.continuous).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (continuous_surfaceGraphJacobian hg).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (surfaceGraphJacobian_pos g _).le, smul_eq_mul,
    Function.comp_apply]

end BoundaryDraft
