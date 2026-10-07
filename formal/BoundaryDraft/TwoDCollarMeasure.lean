import BoundaryDraft.TwoDEndpointCollar

/-! # Unit Lebesgue transport in a physical inward 2D endpoint collar -/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

def twoDUnitLine (n : TwoDSpace) (hn : ‖n‖ = 1) : ℝ ≃ₗᵢ[ℝ] TwoDSpace := by
  let L : ℝ →ₗᵢ[ℝ] TwoDSpace := {
    toLinearMap := LinearMap.toSpanSingleton ℝ TwoDSpace n
    norm_map' := fun s => by change ‖s • n‖ = ‖s‖; rw [norm_smul, hn, mul_one] }
  exact LinearIsometryEquiv.ofSurjective L
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [TwoDSpace, DimensionSpatial] : Module.finrank ℝ ℝ = Module.finrank ℝ TwoDSpace)).mp L.injective)

@[simp] theorem twoDUnitLine_apply (n : TwoDSpace) (hn : ‖n‖ = 1) (s : ℝ) :
    twoDUnitLine n hn s = s • n := rfl

def twoDPositiveCollar (h : TwoDSpace → ℝ) (x : TwoDSpace) (B : ℝ) : Set TwoDSpace :=
  Metric.ball x B ∩ {y | 0 < h y}

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem measurableSet_positiveCollar (x : TwoDSpace) (B : ℝ) :
    MeasurableSet (twoDPositiveCollar h x B) :=
  measurableSet_ball.inter hf.isOpen_positive.measurableSet

theorem endpointPoint_measurePreserving (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    MeasurePreserving (twoDEndpointPoint h x) volume volume :=
  (measurePreserving_add_left volume x).comp
    (twoDUnitLine (twoDInward h x) (hf.inward_norm x hx)).measurePreserving

theorem endpointPoint_measurableEmbedding (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    MeasurableEmbedding (twoDEndpointPoint h x) :=
  (Homeomorph.addLeft x).measurableEmbedding.comp
    (twoDUnitLine (twoDInward h x) (hf.inward_norm x hx)).toHomeomorph.measurableEmbedding

theorem endpointPoint_dist (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) (s : ℝ) :
    dist (twoDEndpointPoint h x s) x = |s| := by
  rw [twoDEndpointPoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
    hf.inward_norm x hx, mul_one, Real.norm_eq_abs]

theorem endpointPoint_preimage_collar (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h)
    {B : ℝ} (_hB : 0 < B)
    (hsign : ∀ s ∈ Icc (-B) B, 0 < h (twoDEndpointPoint h x s) ↔ 0 < s) :
    twoDEndpointPoint h x ⁻¹' twoDPositiveCollar h x B = Ioo 0 B := by
  ext s
  simp only [twoDPositiveCollar, mem_preimage, mem_inter_iff, Metric.mem_ball,
    hf.endpointPoint_dist x hx, mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨ha, hh⟩
    have hs := abs_le.mp ha.le
    exact ⟨(hsign s hs).mp hh, (le_abs_self s).trans_lt ha⟩
  · rintro ⟨hs, hb⟩
    exact ⟨by rwa [abs_of_pos hs], (hsign s ⟨by linarith, hb.le⟩).mpr hs⟩

/-- Exact unit Jacobian for arbitrary observables, not merely constants. -/
theorem integral_positiveCollar (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h)
    {B : ℝ} (hB : 0 < B)
    (hsign : ∀ s ∈ Icc (-B) B, 0 < h (twoDEndpointPoint h x s) ↔ 0 < s)
    (F : TwoDSpace → ℝ) :
    (∫ y in twoDPositiveCollar h x B, F y) = ∫ s in (0 : ℝ)..B, F (twoDEndpointPoint h x s) := by
  rw [← (hf.endpointPoint_measurePreserving x hx).setIntegral_preimage_emb
    (hf.endpointPoint_measurableEmbedding x hx), hf.endpointPoint_preimage_collar x hx hB hsign,
    intervalIntegral.integral_of_le hB.le]
  change (∫ s, F (twoDEndpointPoint h x s) ∂volume.restrict (Ioo 0 B)) = _
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]

end SmoothTwoD
end BoundaryDraft
