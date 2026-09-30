import BoundaryDraft.DimensionSpacetime
import BoundaryDraft.DimensionNormalizedKernel
import BoundaryDraft.EllipsoidAngle

/-!
# Euclidean regulated local wedges in arbitrary dimension

The regulator and the bilocal observable are the actual geometric objects from
`DimensionSpacetime`: only the first endpoint is weighted, and every causal
partner in the cap is retained. Normal/tangential volume transport and the
signed tangential profile are derived here using Euclidean spaces, including
zero tangential dimension (two-dimensional spacetime).

The finite-density identities need no kernel-mass premise. The general limit
helpers explicitly separate the geometric reduction from integrability and
unit mass of the actual density-one vertical kernel. The final physical
corollaries discharge both using the independent normalization theorem in
`DimensionNormalizedKernel`. There is no higher-dimensional global or null
theorem, and the optional `jointCoth` reformulation uses only a scalar identity.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

private def dimensionWedgeEuclideanEquiv (n : ℕ) : DimensionSpatial n ≃ᵐ (Fin n → ℝ) :=
  { WithLp.equiv 2 _ with
    measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin n => ℝ)).measurable
    measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin n => ℝ)).measurable }

/-- Normal and tangential coordinates, with a genuinely Euclidean tangential space. -/
def dimensionWedgePoint {n : ℕ} (r : ℝ) (z : DimensionSpatial n) : DimensionSpatial (n + 1) :=
  (WithLp.equiv 2 _).symm (Fin.cons r ((WithLp.equiv 2 _) z))

/-- The Euclidean coordinate split is a measurable equivalence in every
nonnegative tangential dimension, including `n = 0`. -/
def dimensionWedgeCoordinates (n : ℕ) :
    (ℝ × DimensionSpatial n) ≃ᵐ DimensionSpatial (n + 1) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (dimensionWedgeEuclideanEquiv n)).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.trans
      (dimensionWedgeEuclideanEquiv (n + 1)).symm)

@[simp] theorem dimensionWedgeCoordinates_apply (n : ℕ) (p : ℝ × DimensionSpatial n) :
    dimensionWedgeCoordinates n p = dimensionWedgePoint p.1 p.2 := by
  simp [dimensionWedgeCoordinates, dimensionWedgeEuclideanEquiv, dimensionWedgePoint,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  exact ⟨rfl, rfl⟩

/-- Both `WithLp` transports preserve canonical Euclidean volume; the middle
`piFinSuccAbove` split preserves product volume. No supremum norm is identified
with the Euclidean norm. -/
theorem measurePreserving_dimensionWedgeCoordinates (n : ℕ) :
    MeasurePreserving (dimensionWedgeCoordinates n) := by
  have hprod : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (dimensionWedgeEuclideanEquiv n)) := by
    exact (MeasurePreserving.id volume).prod (PiLp.volume_preserving_equiv (Fin n))
  have hsplit : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
  have hEuclidean : MeasurePreserving (dimensionWedgeEuclideanEquiv (n + 1)).symm :=
    PiLp.volume_preserving_equiv_symm _
  exact hEuclidean.comp (hsplit.comp hprod)

@[simp] theorem dimensionWedgePoint_zero {n : ℕ} (r : ℝ) (z : DimensionSpatial n) :
    dimensionWedgePoint r z 0 = r := by simp [dimensionWedgePoint]

@[simp] theorem dimensionWedgePoint_succ {n : ℕ} (r : ℝ) (z : DimensionSpatial n)
    (i : Fin n) : dimensionWedgePoint r z i.succ = z i := by simp [dimensionWedgePoint]

/-- Pythagoras for the actual Euclidean normal/tangential split. -/
theorem norm_dimensionWedgePoint_sq {n : ℕ} (r : ℝ) (z : DimensionSpatial n) :
    ‖dimensionWedgePoint r z‖ ^ 2 = r ^ 2 + ‖z‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]

theorem norm_le_dimensionWedgePoint {n : ℕ} (r : ℝ) (z : DimensionSpatial n) :
    ‖z‖ ≤ ‖dimensionWedgePoint r z‖ := by
  nlinarith [norm_dimensionWedgePoint_sq r z, norm_nonneg z,
    norm_nonneg (dimensionWedgePoint r z), sq_nonneg r]

theorem abs_le_dimensionWedgePoint {n : ℕ} (r : ℝ) (z : DimensionSpatial n) :
    |r| ≤ ‖dimensionWedgePoint r z‖ := by
  simpa using PiLp.norm_apply_le (dimensionWedgePoint r z) 0

theorem continuous_dimensionWedgePoint (n : ℕ) :
    Continuous (fun p : ℝ × DimensionSpatial n => dimensionWedgePoint p.1 p.2) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases continuous_fst (fun j => ?_) i
  exact (continuous_apply j).comp ((PiLp.continuous_equiv 2 _).comp continuous_snd)

/-- Product Fubini in Euclidean normal/tangential coordinates. -/
theorem integral_dimensionWedgeCoordinates (n : ℕ) (f : DimensionSpatial (n + 1) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ r : ℝ, ∫ z : DimensionSpatial n, f (dimensionWedgePoint r z) := by
  have hE := measurePreserving_dimensionWedgeCoordinates n
  have hi := (hE.integrable_comp_emb (dimensionWedgeCoordinates n).measurableEmbedding).mpr hf
  simp only [Function.comp_def, dimensionWedgeCoordinates_apply, Measure.volume_eq_prod] at hi
  rw [← hE.integral_comp' f, Measure.volume_eq_prod]
  simpa only [dimensionWedgeCoordinates_apply] using integral_prod _ hi

/-- The signed tangential profile is derived from the actual spatial source. -/
def dimensionWedgeTangentialProfile (n : ℕ) (w : DimensionSpatial (n + 1) → ℝ) (r : ℝ) : ℝ :=
  ∫ z : DimensionSpatial n, w (dimensionWedgePoint r z)

/-- Measure transport identifies the Euclidean profile with the coordinate
profile used by the independently proved graph-cap reduction. -/
theorem dimensionWedgeTangentialProfile_eq_coordinate (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (r : ℝ) :
    dimensionWedgeTangentialProfile n w r = dimensionTangentialProfile n w r := by
  have hE : MeasurePreserving (dimensionWedgeEuclideanEquiv n) :=
    PiLp.volume_preserving_equiv _
  exact hE.integral_comp' (fun z => w (dimensionSpatialCons r z))

theorem dimensionWedgeTangentialProfile_eq_compact (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (r : ℝ) :
    dimensionWedgeTangentialProfile n w r =
      ∫ z in Metric.closedBall (0 : DimensionSpatial n) R, w (dimensionWedgePoint r z) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hsource _ ((by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz :
    R < ‖z‖).trans_le (norm_le_dimensionWedgePoint r z))

/-- Every signed tangential slice is absolutely integrable, including the
boundary slice that appears in the local coefficient. -/
theorem integrable_dimensionWedge_slice (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (r : ℝ) :
    Integrable (fun z : DimensionSpatial n => w (dimensionWedgePoint r z)) := by
  have hc : Continuous (fun z : DimensionSpatial n => w (dimensionWedgePoint r z)) :=
    hw.comp ((continuous_dimensionWedgePoint n).comp (continuous_const.prodMk continuous_id))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : DimensionSpatial n) R)
  intro z hz
  exact hsource _ ((by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz :
    R < ‖z‖).trans_le (norm_le_dimensionWedgePoint r z))

theorem continuous_dimensionWedgeTangentialProfile (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Continuous (dimensionWedgeTangentialProfile n w) := by
  simp_rw [show dimensionWedgeTangentialProfile n w = fun r =>
      ∫ z in Metric.closedBall (0 : DimensionSpatial n) R, w (dimensionWedgePoint r z) from
    funext (dimensionWedgeTangentialProfile_eq_compact n w R hsource)]
  apply continuous_parametric_integral_of_continuous _ (isCompact_closedBall 0 R)
  exact hw.comp (continuous_dimensionWedgePoint n)

theorem dimensionWedgeTangentialProfile_eq_zero (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) {r : ℝ} (hr : R < |r|) :
    dimensionWedgeTangentialProfile n w r = 0 := by
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun z => hsource _ (hr.trans_le (abs_le_dimensionWedgePoint r z))

theorem hasCompactSupport_dimensionWedgeTangentialProfile (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    HasCompactSupport (dimensionWedgeTangentialProfile n w) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
  intro r hr
  apply dimensionWedgeTangentialProfile_eq_zero n w R hsource
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] using hr

theorem exists_bound_dimensionWedgeTangentialProfile (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    ∃ C : ℝ, ∀ r, ‖dimensionWedgeTangentialProfile n w r‖ ≤ C :=
  (hasCompactSupport_dimensionWedgeTangentialProfile n w R hsource).exists_bound_of_continuous
    (continuous_dimensionWedgeTangentialProfile n w hw R hsource)

/-- The zero-dimensional tangent space carries unit point mass, not zero
volume. Thus the same profile really includes two-dimensional spacetime. -/
@[simp] theorem dimensionWedgeTangentialProfile_zero_dim
    (w : DimensionSpatial 1 → ℝ) (r : ℝ) :
    dimensionWedgeTangentialProfile 0 w r = w (dimensionWedgePoint r 0) := by
  unfold dimensionWedgeTangentialProfile
  rw [volume_euclideanSpace_eq_dirac]
  exact integral_dirac _ _

/-- The full regulated bilocal action is the normal integral of the actual
vertical kernel. Geometric admissibility and affine agreement on the source
ball are supplied by `dimensionWedgeRegulator_data` and
`dimensionWedgeRegulator_eq_affine`; neither assumes a mass identity. -/
theorem dimensionWeighted_wedge_eq_normalIntegral (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ : ℝ) :
    dimensionWeightedAction (n + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2) =
      ∫ r : ℝ in Ioi 0, dimensionWedgeTangentialProfile n w r *
        dimensionVerticalKernel (n + 1) a β c ρ (κ * r) := by
  simp_rw [dimensionWedgeTangentialProfile_eq_coordinate]
  exact dimensionWeighted_wedgeRegulator_eq_profile n hκ hκ1 hH w hw hsource a β c ρ

/-- Absolute integrability of the finite-density normal reduction follows
from the source support and continuity, before any half-line kernel estimate. -/
theorem integrableOn_dimensionWedge_normalProfile (n : ℕ)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w) (R : ℝ)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ κ : ℝ) :
    IntegrableOn (fun r => dimensionWedgeTangentialProfile n w r *
      dimensionVerticalKernel (n + 1) a β c ρ (κ * r)) (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun r => dimensionWedgeTangentialProfile n w r *
      dimensionVerticalKernel (n + 1) a β c ρ (κ * r)) :=
    (continuous_dimensionWedgeTangentialProfile n w hw R hsource).mul
      ((continuous_dimensionVerticalKernel (n + 1) a β c ρ).comp
        (continuous_const.mul continuous_id))
  exact (hc.integrable_of_hasCompactSupport
    (hasCompactSupport_dimensionWedgeTangentialProfile n w R hsource).mul_right).integrableOn

/-- The inverse slope in height coordinates comes from an exact change of
variables, not from defining or renaming a scalar expression as an action. -/
theorem dimensionWeighted_wedge_eq_heightIntegral (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ : ℝ) :
    dimensionWeightedAction (n + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2) =
      κ⁻¹ * ∫ s : ℝ in Ioi 0, dimensionVerticalKernel (n + 1) a β c ρ s *
        dimensionWedgeTangentialProfile n w (s / κ) := by
  rw [dimensionWeighted_wedge_eq_normalIntegral n hκ hκ1 hH w hw hsource a β c ρ]
  have hs := integral_comp_mul_left_Ioi
    (fun s => dimensionVerticalKernel (n + 1) a β c ρ s *
      dimensionWedgeTangentialProfile n w (s / κ)) 0 hκ
  simpa only [mul_zero, mul_div_cancel_left₀ _ hκ.ne', smul_eq_mul, mul_comm] using hs

/-- Exact density scaling of the genuine regulated action into the existing
signed analytic reduction. All partners remain in the cap, not the source ball. -/
theorem dimensionWeighted_wedge_eq_rescaled (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ : ℝ) (hρ : 0 < ρ) :
    dimensionWeightedAction (n + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2) =
      regulatedVerticalReduction (dimensionVerticalKernel (n + 1) a β c 1)
        (dimensionWedgeTangentialProfile n w) κ (ρ ^ (1 / ((n + 2 : ℕ) : ℝ))) := by
  rw [dimensionWeighted_wedge_eq_normalIntegral n hκ hκ1 hH w hw hsource a β c ρ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [dimensionVerticalKernel_density_scaling (n + 1) (by omega) a β c ρ (κ * r)
    hρ (mul_nonneg hκ.le hr.le)]

/-- The existing signed reduction lemma with an arbitrary boundary value.
The profile may be signed and its value at zero need not be one. -/
theorem regulatedVerticalReduction_limit_at_boundary (G B : ℝ → ℝ)
    (hG : IntegrableOn G (Ioi 0)) (hmass : (∫ u : ℝ in Ioi 0, G u) = 1)
    (hB : Continuous B) (C : ℝ) (hbound : ∀ r, ‖B r‖ ≤ C) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (regulatedVerticalReduction G B κ) atTop (𝓝 (κ⁻¹ * B 0)) := by
  have hl := signed_rescaling_limit (volume.restrict (Ioi 0)) G (fun x => B (x / κ))
    hG (hB.comp (continuous_id.div_const κ)) C (fun x => hbound _)
  simp only [hmass, one_mul, zero_div] at hl
  have hi := (hl.comp tendsto_inv_atTop_zero).const_mul κ⁻¹
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
  exact (regulatedVerticalReduction_rescale G B hκ hk).symm

/-- Density-scaled concentration with arbitrary signed boundary value. This
is general analysis conditional on absolute integrability and unit mass. -/
theorem regulatedVerticalReduction_density_limit_at_boundary (d : ℕ) (hd : 0 < d)
    (G B : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hmass : (∫ u : ℝ in Ioi 0, G u) = 1) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ r, ‖B r‖ ≤ C) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ρ : ℝ => regulatedVerticalReduction G B κ (ρ ^ (1 / (d : ℝ))))
      atTop (𝓝 (κ⁻¹ * B 0)) :=
  (regulatedVerticalReduction_limit_at_boundary G B hG hmass hB C hbound hκ).comp
    (tendsto_rpow_atTop (div_pos (by norm_num) (Nat.cast_pos.mpr hd)))

/-- Conditional local wedge limit for the ACTUAL weighted bilocal action.
Only integrability and mass of its density-one kernel remain external; source
profile regularity, geometry, transport, and finite-density reduction are all
derived. No mass or limit premise is inserted into geometric admissibility. -/
theorem dimensionWeighted_wedge_limit_of_mass (n : ℕ) (a β c : ℝ)
    (hG : IntegrableOn (dimensionVerticalKernel (n + 1) a β c 1) (Ioi 0))
    (hmass : (∫ s : ℝ in Ioi 0, dimensionVerticalKernel (n + 1) a β c 1 s) = 1)
    {κ H R : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (n + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : DimensionSpatial n, w (dimensionWedgePoint 0 z))) := by
  have hc := continuous_dimensionWedgeTangentialProfile n w hw R hsource
  obtain ⟨C, hC⟩ := exists_bound_dimensionWedgeTangentialProfile n w hw R hsource
  have hl := regulatedVerticalReduction_density_limit_at_boundary (n + 2) (by omega)
    (dimensionVerticalKernel (n + 1) a β c 1) (dimensionWedgeTangentialProfile n w)
    hG hmass hc C hC hκ
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (dimensionWeighted_wedge_eq_rescaled n hκ hκ1 hH w hw hsource a β c ρ hρ).symm

/-- Scalar rapidity reformulation of the conditional result. This invokes no
new Lorentz-geometric interpretation in arbitrary dimension. -/
theorem dimensionWeighted_wedge_coth_limit_of_mass (n : ℕ) (a β c : ℝ)
    (hG : IntegrableOn (dimensionVerticalKernel (n + 1) a β c 1) (Ioi 0))
    (hmass : (∫ s : ℝ in Ioi 0, dimensionVerticalKernel (n + 1) a β c 1 s) = 1)
    {κ H R : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (n + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2))
      atTop (𝓝 (jointCoth κ * ∫ z : DimensionSpatial n, w (dimensionWedgePoint 0 z))) := by
  rw [(jointRapidity_identities κ hκ hκ1).2.2.2.2, one_div]
  exact dimensionWeighted_wedge_limit_of_mass n a β c hG hmass hκ hκ1 hH w hw hsource

/-- Identification with the independently normalized finite-height kernel.
The sphere factor is derived by Euclidean radial integration in
`DimensionSpacetime`, not assigned by the desired kernel mass. -/
theorem dimensionWedge_verticalKernel_eq_planeKernel (n : ℕ) (H : ℝ) :
    dimensionVerticalKernel (n + 1) (dimensionPointCoefficient (n + 2))
      (dimensionPairCoefficient (n + 2)) (dimensionIntervalCoefficient (n + 2)) 1 H =
      dimensionPlaneKernel (n + 2) H := by
  rw [dimensionVerticalKernel_one]
  unfold dimensionPlaneKernel verticalActionReduction
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [dimensionRadialSlice_eq_sigma (n + 1) (by omega)
    (dimensionIntervalCoefficient (n + 2)) 1 t ht.1.le]
  simp only [mul_one, dimensionConeSlice, dimensionPhysicalSlice, dimensionSphereArea]
  ring

/-- Unconditional physical local wedge limit with the independent published
point, pair, and interval coefficients. No kernel-mass premise remains. -/
theorem dimensionWeighted_wedge_limit (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (n + 1)
      (dimensionPointCoefficient (n + 2)) (dimensionPairCoefficient (n + 2))
      (dimensionIntervalCoefficient (n + 2)) ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : DimensionSpatial n, w (dimensionWedgePoint 0 z))) := by
  apply dimensionWeighted_wedge_limit_of_mass n
    (dimensionPointCoefficient (n + 2)) (dimensionPairCoefficient (n + 2))
    (dimensionIntervalCoefficient (n + 2)) _ _ hκ hκ1 hH w hw hsource
  · simp_rw [show dimensionVerticalKernel (n + 1) (dimensionPointCoefficient (n + 2))
        (dimensionPairCoefficient (n + 2)) (dimensionIntervalCoefficient (n + 2)) 1 =
        dimensionPlaneKernel (n + 2) from funext (dimensionWedge_verticalKernel_eq_planeKernel n)]
    exact integrableOn_dimensionPlaneKernel (n + 2) (by omega)
  · simp_rw [dimensionWedge_verticalKernel_eq_planeKernel]
    exact integral_dimensionPlaneKernel (n + 2) (by omega)

/-- The proved physical coefficient in scalar rapidity notation. This does
not assert a new dimension-general Lorentz-geometric or global joint theorem. -/
theorem dimensionWeighted_wedge_coth_limit (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (n + 1)
      (dimensionPointCoefficient (n + 2)) (dimensionPairCoefficient (n + 2))
      (dimensionIntervalCoefficient (n + 2)) ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2))
      atTop (𝓝 (jointCoth κ * ∫ z : DimensionSpatial n, w (dimensionWedgePoint 0 z))) := by
  rw [(jointRapidity_identities κ hκ hκ1).2.2.2.2, one_div]
  exact dimensionWeighted_wedge_limit n hκ hκ1 hH w hw hsource

end BoundaryDraft
