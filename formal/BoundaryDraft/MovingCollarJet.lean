import BoundaryDraft.MovingCollarIntegral

/-!
# The two-jet of an actual moving collar fibre

At zero displacement the moving root and the gap vanish. The first derivative
of the collar correction is zero; its second derivative is the rank-one form
of the gap differential. The weight requires only C² regularity.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace MovingCollar

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The root differential equals the parameter differential of the gap when
the gap is identically zero along the base height fibre. -/
theorem fderiv_root_eq_partial {q : P × ℝ → ℝ} {η : P → ℝ} {p₀ : P}
    (hq : DifferentiableAt ℝ q (p₀, 0)) (hη : DifferentiableAt ℝ η p₀)
    (hη₀ : η p₀ = 0) (hq₀ : ∀ t, q (p₀, t) = 0)
    (hroot : ∀ᶠ p in 𝓝 p₀, η p = q (p, η p)) :
    fderiv ℝ η p₀ = (fderiv ℝ q (p₀, 0)).comp (ContinuousLinearMap.inl ℝ P ℝ) := by
  let L := fderiv ℝ q (p₀, 0)
  have hheight : L.comp (ContinuousLinearMap.inr ℝ P ℝ) = 0 := by
    have ht := hq.hasFDerivAt.comp (f := fun t : ℝ => (p₀, t)) 0
      (hasFDerivAt_prodMk_right p₀ 0)
    have he : (fun t : ℝ => q (p₀, t)) = fun _ => 0 := funext hq₀
    change HasFDerivAt (fun t => q (p₀, t)) _ 0 at ht
    rw [he] at ht
    exact ht.unique (hasFDerivAt_const 0 (0 : ℝ))
  have hq' : HasFDerivAt q L (p₀, η p₀) := by simpa only [hη₀] using hq.hasFDerivAt
  have hd := hq'.comp p₀ ((hasFDerivAt_id p₀).prodMk hη.hasFDerivAt)
  change HasFDerivAt (fun p => q (p, η p)) _ p₀ at hd
  change η =ᶠ[𝓝 p₀] (fun p => q (p, η p)) at hroot
  rw [hroot.fderiv_eq, hd.fderiv]
  ext v
  change L (v, fderiv ℝ η p₀ v) = L (v, 0)
  have hv : (v, fderiv ℝ η p₀ v) = (v, (0 : ℝ)) + (0, fderiv ℝ η p₀ v) := by ext <;> simp
  have hz := congrArg (fun A : ℝ →L[ℝ] ℝ => A (fderiv ℝ η p₀ v)) hheight
  change L (0, fderiv ℝ η p₀ v) = 0 at hz
  rw [hv, map_add, hz, add_zero]

/-- The true first derivative agrees locally with the endpoint-cancelled
integral. Locality is needed before taking one further derivative. -/
theorem eventually_fderiv_fibre {W : ℝ → ℝ} {q : P × ℝ → ℝ} {η : P → ℝ} {p₀ : P}
    (hW : ContDiffAt ℝ 2 W 0) (hq : ContDiffAt ℝ 3 q (p₀, 0))
    (hη : ContDiffAt ℝ 3 η p₀) (hη₀ : η p₀ = 0)
    (hroot : ∀ᶠ p in 𝓝 p₀, η p = q (p, η p)) :
    fderiv ℝ (fibre W q η) =ᶠ[𝓝 p₀] fibreDifferential W q η := by
  have hWq : ∀ᶠ a : P × ℝ in 𝓝 (p₀, (0 : ℝ)),
      ContDiffAt ℝ 1 W a.2 ∧ ContDiffAt ℝ 1 q a :=
    (continuousAt_snd.tendsto.eventually
      ((hW.of_le (m := 1) (by norm_num)).eventually (by simp))).and
        ((hq.of_le (m := 1) (by norm_num)).eventually (by simp))
  have hseg := eventually_heightSegments hη.continuousAt hη₀ hWq
  filter_upwards [hseg, hroot, hη.eventually (by simp)] with p hp hr hηp
  exact (hasFDerivAt_fibre (hηp.differentiableAt (by norm_num)) hr
    (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2)).fderiv

/-- Zero root implies zero collar value and first differential. -/
theorem fibre_vanishing_oneJet {W : ℝ → ℝ} {q : P × ℝ → ℝ} {η : P → ℝ} {p₀ : P}
    (hW : ContDiffAt ℝ 2 W 0) (hq : ContDiffAt ℝ 3 q (p₀, 0))
    (hη : ContDiffAt ℝ 3 η p₀) (hη₀ : η p₀ = 0)
    (hroot : ∀ᶠ p in 𝓝 p₀, η p = q (p, η p)) :
    fibre W q η p₀ = 0 ∧ fderiv ℝ (fibre W q η) p₀ = 0 := by
  refine ⟨by simp [fibre, hη₀], ?_⟩
  rw [(eventually_fderiv_fibre hW hq hη hη₀ hroot).eq_of_nhds]
  simp [fibreDifferential, hη₀]

/-- The Hessian comes from the moving endpoint of the first differential;
there is no derivative of the C² weight in this coefficient. -/
theorem fderiv_fderiv_fibre {W : ℝ → ℝ} {q : P × ℝ → ℝ} {η : P → ℝ} {p₀ : P}
    (hW : ContDiffAt ℝ 2 W 0) (hq : ContDiffAt ℝ 3 q (p₀, 0))
    (hη : ContDiffAt ℝ 3 η p₀) (hη₀ : η p₀ = 0) (hq₀ : ∀ t, q (p₀, t) = 0)
    (hroot : ∀ᶠ p in 𝓝 p₀, η p = q (p, η p)) (v w : P) :
    fderiv ℝ (fderiv ℝ (fibre W q η)) p₀ v w =
      W 0 * (fderiv ℝ q (p₀, 0) (v, 0)) * (fderiv ℝ q (p₀, 0) (w, 0)) := by
  let G : P × ℝ → P →L[ℝ] ℝ := fun p => W p.2 •
    (fderiv ℝ q p).comp (ContinuousLinearMap.inl ℝ P ℝ)
  have hG : ContDiffAt ℝ 1 G (p₀, 0) :=
    ((hW.of_le (m := 1) (by norm_num)).comp (p₀, 0) contDiffAt_snd).smul
      ((hq.fderiv_right (m := 1) (show (1 : WithTop ℕ∞) + 1 ≤ 3 by decide)).clm_comp contDiffAt_const)
  have hseg : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 G (p₀, t) := by
    simp only [hη₀, uIcc_self, mem_singleton_iff]
    intro t ht
    subst t
    exact hG
  have hd := hasFDerivAt_movingIntegral (hη.differentiableAt (by norm_num)).hasFDerivAt hseg
  change HasFDerivAt (fibreDifferential W q η) _ p₀ at hd
  rw [(eventually_fderiv_fibre hW hq hη hη₀ hroot).fderiv_eq, hd.fderiv,
    fderiv_root_eq_partial (hq.differentiableAt (by norm_num))
      (hη.differentiableAt (by norm_num)) hη₀ hq₀ hroot]
  simp only [hη₀, intervalIntegral.integral_same, zero_add, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, G,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end MovingCollar
end BoundaryDraft
