import BoundaryDraft.TwoDEndpointCoefficient
import BoundaryDraft.MovingCollarJet

/-!
# Actual smooth moving endpoint roots and their collar two-jets

At each regular endpoint use the physical inward unit spatial direction.
The root equation is the actual translated future/height gap. The inverse
function theorem supplies its root and uniqueness; no root or jet hypothesis
is added to `SmoothTwoD`. Interior critical points are not involved.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

def twoDInward (h : TwoDSpace → ℝ) (x : TwoDSpace) : TwoDSpace :=
  ‖twoDGradient h x‖⁻¹ • twoDGradient h x

def twoDShortGapLinear (f : TwoDSpace → ℝ) (x : TwoDSpace) : TwoDSpacetime →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ TwoDSpace -
    (fderiv ℝ f x).comp (ContinuousLinearMap.snd ℝ ℝ TwoDSpace)

@[simp] theorem twoDShortGapLinear_apply (f : TwoDSpace → ℝ) (x : TwoDSpace) (z : TwoDSpacetime) :
    twoDShortGapLinear f x z = z.1 - fderiv ℝ f x z.2 := rfl

def twoDEndpointPoint (h : TwoDSpace → ℝ) (x : TwoDSpace) (s : ℝ) : TwoDSpace :=
  x + s • twoDInward h x

/-- Root normalization in a physical inward coordinate, NOT an assumed height chart. -/
def twoDEndpointGap (h f : TwoDSpace → ℝ) (x : TwoDSpace) (p : TwoDSpacetime × ℝ) : ℝ :=
  p.2 + (twoDShortGap f p.1 (twoDEndpointPoint h x p.2) - h (twoDEndpointPoint h x p.2)) /
    ‖twoDGradient h x‖

def twoDEndpointCorrection (h f : TwoDSpace → ℝ) (x : TwoDSpace)
    (η : TwoDSpacetime → ℝ) : TwoDSpacetime → ℝ :=
  MovingCollar.fibre (fun _ => ‖twoDGradient h x‖) (twoDEndpointGap h f x) η

private theorem endpoint_root_differential {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {q : P × ℝ → ℝ} {η : P → ℝ} (L : P →L[ℝ] ℝ)
    (hq : HasFDerivAt q (L.comp (ContinuousLinearMap.fst ℝ P ℝ)) (0, 0))
    (hη : DifferentiableAt ℝ η 0) (hη₀ : η 0 = 0)
    (hr : ∀ᶠ p in 𝓝 0, η p = q (p, η p)) : fderiv ℝ η 0 = L := by
  have hq' : HasFDerivAt q (L.comp (ContinuousLinearMap.fst ℝ P ℝ)) (0, η 0) := by
    simpa only [hη₀] using hq
  have hd := hq'.comp 0 ((hasFDerivAt_id 0).prodMk hη.hasFDerivAt)
  change η =ᶠ[𝓝 0] (fun p => q (p, η p)) at hr
  change HasFDerivAt (fun p => q (p, η p)) _ 0 at hd
  rw [hr.fderiv_eq, hd.fderiv]
  ext v
  rfl

/-- The general collar Hessian needs the vanishing height DIFFERENTIAL,
not the stronger identity that the gap vanish along the entire reference fibre. -/
private theorem endpoint_fibre_hessian {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {q : P × ℝ → ℝ} {η : P → ℝ} (d : ℝ) (L : P →L[ℝ] ℝ)
    (hq : ContDiffAt ℝ 3 q (0, 0))
    (hD : HasFDerivAt q (L.comp (ContinuousLinearMap.fst ℝ P ℝ)) (0, 0))
    (hη : ContDiffAt ℝ 3 η 0) (hη₀ : η 0 = 0)
    (hr : ∀ᶠ p in 𝓝 0, η p = q (p, η p)) (v w : P) :
    fderiv ℝ (fderiv ℝ (MovingCollar.fibre (fun _ => d) q η)) 0 v w = d * L v * L w := by
  let W : ℝ → ℝ := fun _ => d
  let G : P × ℝ → P →L[ℝ] ℝ := fun p => W p.2 •
    (fderiv ℝ q p).comp (ContinuousLinearMap.inl ℝ P ℝ)
  have hG : ContDiffAt ℝ 1 G (0, 0) := contDiffAt_const.smul
    ((hq.fderiv_right (m := 1) (by decide)).clm_comp contDiffAt_const)
  have hseg : ∀ t ∈ uIcc 0 (η 0), ContDiffAt ℝ 1 G (0, t) := by
    simp only [hη₀, uIcc_self, mem_singleton_iff]
    intro t ht
    subst t
    exact hG
  have hd := MovingCollar.hasFDerivAt_movingIntegral
    (hη.differentiableAt (by norm_num)).hasFDerivAt hseg
  change HasFDerivAt (MovingCollar.fibreDifferential W q η) _ 0 at hd
  rw [(MovingCollar.eventually_fderiv_fibre contDiffAt_const hq hη hη₀ hr).fderiv_eq, hd.fderiv,
    endpoint_root_differential L hD (hη.differentiableAt (by norm_num)) hη₀ hr]
  simp only [hη₀, intervalIntegral.integral_same, zero_add, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, G, W, hD.fderiv,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  change L v * (d * L w) = d * L v * L w
  ring

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem endpoint_gradient_pos (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    0 < ‖twoDGradient h x‖ := by
  rw [twoDGradient_norm]
  exact norm_pos_iff.mpr (hf.regular_zero x hx.1 hx.2)

theorem inward_norm (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    ‖twoDInward h x‖ = 1 := by
  rw [twoDInward, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (hf.endpoint_gradient_pos x hx)), inv_mul_cancel₀ (hf.endpoint_gradient_pos x hx).ne']

theorem height_inward (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    fderiv ℝ h x (twoDInward h x) = ‖twoDGradient h x‖ := by
  rw [twoD_differential_eq_inner, twoDInward, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [(hf.endpoint_gradient_pos x hx).ne']
  ring

theorem contDiffAt_endpointGap (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    ContDiffAt ℝ 3 (twoDEndpointGap h f x) (0, 0) := by
  let φ : TwoDSpacetime × ℝ → TwoDSpace := fun p => twoDEndpointPoint h x p.2
  have hφ : ContDiff ℝ 3 φ := contDiff_const.add (contDiff_snd.smul contDiff_const)
  have hφ₀ : φ (0, 0) = x := by simp [φ, twoDEndpointPoint]
  have hfx := (hf.future_smoothAt x hx.1).of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)
  have hhx := (hf.height_smoothAt x hx.1).of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)
  have hfφ : ContDiffAt ℝ 3 f (φ (0, 0)) := hφ₀.symm ▸ hfx
  have hfφb : ContDiffAt ℝ 3 f (φ (0, 0) + (0 : TwoDSpacetime).2) := by
    simpa [φ, twoDEndpointPoint] using hfx
  have hhφ : ContDiffAt ℝ 3 h (φ (0, 0)) := hφ₀.symm ▸ hhx
  exact contDiffAt_snd.add
    ((((contDiffAt_fst.fst.sub (hfφb.comp (0, 0) (hφ.contDiffAt.add contDiffAt_fst.snd))).add
      (hfφ.comp (0, 0) hφ.contDiffAt)).sub (hhφ.comp (0, 0) hφ.contDiffAt)).div_const _)

/-- Exact cancellation of the inward differential in the normalized root equation. -/
theorem hasFDerivAt_endpointGap (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    HasFDerivAt (twoDEndpointGap h f x)
      ((‖twoDGradient h x‖⁻¹ • twoDShortGapLinear f x).comp
        (ContinuousLinearMap.fst ℝ TwoDSpacetime ℝ)) (0, 0) := by
  let φ : TwoDSpacetime × ℝ → TwoDSpace := fun p => twoDEndpointPoint h x p.2
  let N : TwoDSpacetime × ℝ →L[ℝ] TwoDSpace :=
    (ContinuousLinearMap.snd ℝ TwoDSpacetime ℝ).smulRight (twoDInward h x)
  have hφ : HasFDerivAt φ N (0, 0) := by
    convert (hasFDerivAt_const x (0 : TwoDSpacetime × ℝ)).add
      ((hasFDerivAt_snd (𝕜 := ℝ)).smul_const (twoDInward h x)) using 1
    simp [φ, N, twoDEndpointPoint]
  have hφ₀ : φ (0, 0) = x := by simp [φ, twoDEndpointPoint]
  have hF := ((hf.future_smoothAt x hx.1).differentiableAt (by simp)).hasFDerivAt
  have hH := ((hf.height_smoothAt x hx.1).differentiableAt (by simp)).hasFDerivAt
  let S : TwoDSpacetime × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ TwoDSpace).comp (ContinuousLinearMap.fst ℝ TwoDSpacetime ℝ)
  let B : TwoDSpacetime × ℝ →L[ℝ] TwoDSpace :=
    (ContinuousLinearMap.snd ℝ ℝ TwoDSpace).comp (ContinuousLinearMap.fst ℝ TwoDSpacetime ℝ)
  have hFb : HasFDerivAt f (fderiv ℝ f x) (φ (0, 0) + B (0, 0)) := by
    simpa [φ, twoDEndpointPoint] using hF
  have hFφ : HasFDerivAt f (fderiv ℝ f x) (φ (0, 0)) := hφ₀.symm ▸ hF
  have hHφ : HasFDerivAt h (fderiv ℝ h x) (φ (0, 0)) := hφ₀.symm ▸ hH
  have hd := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : TwoDSpacetime × ℝ))).add
    ((((S.hasFDerivAt.sub (hFb.comp (0, 0) (hφ.add B.hasFDerivAt))).add
      (hFφ.comp (0, 0) hφ)).sub (hHφ.comp (0, 0) hφ)).mul_const (‖twoDGradient h x‖⁻¹))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    twoDShortGapLinear_apply, S, B, N, ContinuousLinearMap.smulRight_apply]
  change v.2 + ‖twoDGradient h x‖⁻¹ *
    (v.1.1 - fderiv ℝ f x (v.2 • twoDInward h x + v.1.2) +
      fderiv ℝ f x (v.2 • twoDInward h x) - fderiv ℝ h x (v.2 • twoDInward h x)) =
    ‖twoDGradient h x‖⁻¹ * (v.1.1 - fderiv ℝ f x v.1.2)
  rw [map_add, map_smul, map_smul, hf.height_inward x hx]
  simp only [smul_eq_mul]
  field_simp [(hf.endpoint_gradient_pos x hx).ne']
  ring

/-- A native smooth root and collar two-jet at EVERY regular endpoint. -/
theorem exists_movingEndpoint_twoJet (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    ∃ η : TwoDSpacetime → ℝ, η 0 = 0 ∧ ContDiffAt ℝ 3 η 0 ∧
      (∀ᶠ z in 𝓝 0, η z = twoDEndpointGap h f x (z, η z)) ∧
      (∀ᶠ p in 𝓝 ((0 : TwoDSpacetime), (0 : ℝ)),
        p.2 = twoDEndpointGap h f x p → p.2 = η p.1) ∧
      ContDiffAt ℝ 3 (twoDEndpointCorrection h f x η) 0 ∧
      twoDEndpointCorrection h f x η 0 = 0 ∧
      fderiv ℝ (twoDEndpointCorrection h f x η) 0 = 0 ∧
      ∀ v w : TwoDSpacetime, fderiv ℝ (fderiv ℝ (twoDEndpointCorrection h f x η)) 0 v w =
        twoDShortGapLinear f x v * twoDShortGapLinear f x w / ‖twoDGradient h x‖ := by
  have hq := hf.contDiffAt_endpointGap x hx
  have hD := hf.hasFDerivAt_endpointGap x hx
  have hx0 : h x = 0 := hx.2
  obtain ⟨η, hη₀, hη, hr, hu⟩ := MovingCollar.exists_contDiff_root hq
    (by simp [twoDEndpointGap, twoDEndpointPoint, twoDShortGap, hx0]) _ hD
  have hvan := MovingCollar.fibre_vanishing_oneJet (W := fun _ => ‖twoDGradient h x‖)
    contDiffAt_const hq hη hη₀ hr
  refine ⟨η, hη₀, hη, hr, hu, MovingCollar.contDiffAt_fibre contDiffAt_const hq hη hη₀ hr,
    hvan.1, hvan.2, ?_⟩
  intro v w
  rw [twoDEndpointCorrection, endpoint_fibre_hessian _ _ hq hD hη hη₀ hr]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [(hf.endpoint_gradient_pos x hx).ne']

end SmoothTwoD
end BoundaryDraft
