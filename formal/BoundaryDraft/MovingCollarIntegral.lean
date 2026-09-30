import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Moving-height roots and collar integrals

This module contains local analytic tools for the moving collar. Root
existence and regularity are consequences of the inverse function theorem,
not assumptions about an overlap or its Taylor remainder.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace MovingCollar

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

/-- A scalar contact equation with zero height derivative at the reference
point has a C³ moving root. The derivative in the other parameters is free.
The local uniqueness assertion concerns the original equation. -/
theorem exists_contDiff_root {q : P × ℝ → ℝ} {p₀ : P}
    (hq : ContDiffAt ℝ 3 q (p₀, 0)) (hq₀ : q (p₀, 0) = 0)
    (L : P →L[ℝ] ℝ)
    (hD : HasFDerivAt q (L.comp (ContinuousLinearMap.fst ℝ P ℝ)) (p₀, 0)) :
    ∃ η : P → ℝ, η p₀ = 0 ∧ ContDiffAt ℝ 3 η p₀ ∧
      (∀ᶠ p in 𝓝 p₀, η p = q (p, η p)) ∧
      (∀ᶠ a in 𝓝 (p₀, (0 : ℝ)), a.2 = q a → a.2 = η a.1) := by
  let F : P × ℝ → P × ℝ := fun a => (a.1, a.2 - q a)
  let e : (P × ℝ) ≃L[ℝ] P × ℝ :=
    (ContinuousLinearEquiv.refl ℝ P).skewProd (ContinuousLinearEquiv.refl ℝ ℝ) (-L)
  have hF : ContDiffAt ℝ 3 F (p₀, 0) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sub hq)
  have hFD : HasFDerivAt F (e : (P × ℝ) →L[ℝ] P × ℝ) (p₀, 0) := by
    convert hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub hD) using 1
  have hF₀ : F (p₀, 0) = (p₀, 0) := by simp [F, hq₀]
  let E := hF.toPartialHomeomorph F hFD (by norm_num)
  let η : P → ℝ := fun p => (E.symm (p, 0)).2
  have hsrc : (p₀, (0 : ℝ)) ∈ E.source := hF.mem_toPartialHomeomorph_source hFD (by norm_num)
  have htgt : (p₀, (0 : ℝ)) ∈ E.target := by
    rw [← hF₀]
    exact hF.image_mem_toPartialHomeomorph_target hFD (by norm_num)
  have hinv : ContDiffAt ℝ 3 E.symm (p₀, 0) := by
    rw [← hF₀]
    exact hF.to_localInverse hFD (by norm_num)
  have hη₀ : η p₀ = 0 := by
    change (E.symm (p₀, 0)).2 = 0
    rw [← hF₀]
    exact congrArg Prod.snd (E.left_inv hsrc)
  refine ⟨η, hη₀, (hinv.comp p₀ (contDiffAt_id.prodMk contDiffAt_const)).snd, ?_, ?_⟩
  · have ht : ∀ᶠ p : P in 𝓝 p₀, (p, (0 : ℝ)) ∈ E.target :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (E.open_target.mem_nhds htgt)
    filter_upwards [ht] with p hp
    have he := E.right_inv hp
    have hfirst : (E.symm (p, 0)).1 = p := congrArg Prod.fst he
    have hsecond : (E.symm (p, 0)).2 - q (E.symm (p, 0)) = 0 := congrArg Prod.snd he
    have hpE : E.symm (p, 0) = (p, η p) := Prod.ext hfirst rfl
    rw [hpE] at hsecond
    exact sub_eq_zero.mp hsecond
  · filter_upwards [E.open_source.mem_nhds hsrc] with a ha hroot
    have hE : E a = (a.1, 0) := by
      change (a.1, a.2 - q a) = _
      rw [hroot, sub_self]
    have he := congrArg Prod.snd (E.left_inv ha)
    rw [hE] at he
    exact he.symm

section CompactIntegrals

variable {Q E : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [MeasurableSpace Q] [OpensMeasurableSpace Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Q} [IsFiniteMeasureOnCompacts μ]

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ Q]
  [MeasurableSpace Q] [OpensMeasurableSpace Q] [NormedSpace ℝ E] [CompleteSpace E] in
/-- Compactness turns joint pointwise continuity into one local constant
bound, without differentiating the integration domain. -/
theorem eventually_bound_compact {F : P × Q → E} {x₀ : P} {K : Set Q}
    (hK : IsCompact K) (hF : ∀ y ∈ K, ContinuousAt F (x₀, y)) :
    ∃ M : ℝ, ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, ‖F (x, y)‖ ≤ M := by
  have hcont : ContinuousOn (fun y => F (x₀, y)) K := fun y hy =>
    ((hF y hy).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨M + 1, hK.eventually_forall_of_forall_eventually ?_⟩
  intro y hy
  exact ((hF y hy).norm.eventually (gt_mem_nhds (lt_of_le_of_lt (hM y hy) (lt_add_one M)))).mono
    (fun _ hp => hp.le)

omit [CompleteSpace P] [CompleteSpace E] in
set_option maxHeartbeats 800000 in
/-- Differentiation on a compact fixed domain, from joint C¹ germs alone.
The displayed derivative is the actual parameter derivative of the integrand. -/
theorem hasFDerivAt_integral_compact {F : P × Q → E} {x₀ : P} {K : Set Q}
    (hK : IsCompact K) (hF : ∀ y ∈ K, ContDiffAt ℝ 1 F (x₀, y)) :
    HasFDerivAt (fun x => ∫ y in K, F (x, y) ∂μ)
      (∫ y in K, (fderiv ℝ F (x₀, y)).comp (ContinuousLinearMap.inl ℝ P Q) ∂μ) x₀ := by
  let G : P × Q → P →L[ℝ] E := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ P Q)
  have hG : ∀ y ∈ K, ContinuousAt G (x₀, y) := by
    intro y hy
    exact (((hF y hy).fderiv_right (m := 0) (by norm_num)).clm_comp
      contDiffAt_const).continuousAt
  obtain ⟨M, hM⟩ := eventually_bound_compact hK hG
  have hevent : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, ContDiffAt ℝ 1 F (x, y) :=
    hK.eventually_forall_of_forall_eventually (fun y hy => (hF y hy).eventually (by simp))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hM.and hevent)
  have hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun y => F (x, y)) (μ.restrict K) := by
    filter_upwards [hevent] with x hx
    exact (ContinuousOn.integrableOn_compact hK (fun y hy =>
      ((hx y hy).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt)).1
  have hint : IntegrableOn (fun y => F (x₀, y)) K μ :=
    ContinuousOn.integrableOn_compact hK (fun y hy =>
      ((hF y hy).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt)
  have hGint : IntegrableOn (fun y => G (x₀, y)) K μ :=
    ContinuousOn.integrableOn_compact hK (fun y hy =>
      ((hG y hy).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y => F (x, y)) (F' := fun x y => G (x, y))
    hε hmeas hint hGint.1 (bound := fun _ => M)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy x hx
    exact (hball hx).1 y hy
  · exact integrableOn_const.mpr (Or.inr hK.measure_lt_top)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy x hx
    exact (((hball hx).2 y hy).differentiableAt (by norm_num)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left x y)

omit [CompleteSpace P] in
/-- Finite smoothness commutes with integration over a compact fixed domain.
All domination hypotheses are derived, not added as analytic premises. -/
theorem contDiffAt_integral_compact (n : ℕ) {F : P × Q → E} {x₀ : P} {K : Set Q}
    (hK : IsCompact K) (hF : ∀ y ∈ K, ContDiffAt ℝ n F (x₀, y)) :
    ContDiffAt ℝ n (fun x => ∫ y in K, F (x, y) ∂μ) x₀ := by
  induction n generalizing E with
  | zero =>
      have hevent : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, ContDiffAt ℝ 0 F (x, y) :=
        hK.eventually_forall_of_forall_eventually (fun y hy => (hF y hy).eventually (by simp))
      have hc : ∀ᶠ x in 𝓝 x₀, ContinuousAt (fun x => ∫ y in K, F (x, y) ∂μ) x := by
        filter_upwards [hevent] with x hx
        obtain ⟨M, hM⟩ := eventually_bound_compact hK (fun y hy => (hx y hy).continuousAt)
        have hevent' : ∀ᶠ v in 𝓝 x, ∀ y ∈ K, ContDiffAt ℝ 0 F (v, y) :=
          hK.eventually_forall_of_forall_eventually (fun y hy => (hx y hy).eventually (by simp))
        apply continuousAt_of_dominated (F := fun v y => F (v, y))
          (x₀ := x) (bound := fun _ => M)
        · filter_upwards [hevent'] with v hv
          exact (ContinuousOn.integrableOn_compact hK (fun y hy =>
            ((hv y hy).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt)).1
        · filter_upwards [hM] with v hv
          filter_upwards [ae_restrict_mem hK.measurableSet] with y hy using hv y hy
        · exact integrableOn_const.mpr (Or.inr hK.measure_lt_top)
        · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
          have htest : ContinuousAt (fun v : P => F (v, y)) x :=
            (hx y hy).continuousAt.comp_of_eq
              (continuousAt_id.prodMk continuousAt_const) rfl
          exact htest
      obtain ⟨U, hUC, hU, hxU⟩ := mem_nhds_iff.mp hc
      apply (show ContDiffOn ℝ 0 (fun x => ∫ y in K, F (x, y) ∂μ) U from
        contDiffOn_zero.mpr (fun x hx =>
          (show ContinuousAt (fun v => ∫ y in K, F (v, y) ∂μ) x from hUC hx).continuousWithinAt)).contDiffAt
            (hU.mem_nhds hxU)
  | succ n ih =>
      let G : P × Q → P →L[ℝ] E := fun p =>
        (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ P Q)
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => ∫ y in K, G (x, y) ∂μ, ?_, ?_⟩
      · have hevent : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, ContDiffAt ℝ (n + 1) F (x, y) :=
          hK.eventually_forall_of_forall_eventually (fun y hy => (hF y hy).eventually (by simp))
        refine ⟨{x | ∀ y ∈ K, ContDiffAt ℝ (n + 1) F (x, y)}, hevent, ?_⟩
        intro x hx
        exact hasFDerivAt_integral_compact hK (fun y hy => (hx y hy).of_le (by simp))
      · apply ih
        intro y hy
        exact ((hF y hy).fderiv_right (m := n) (by simp)).clm_comp contDiffAt_const

omit [CompleteSpace P] [CompleteSpace E] in
set_option maxHeartbeats 800000 in
/-- Both displacement derivatives commute with compact fixed-domain
integration. The result is expressed using derivatives of the actual slices,
so a geometric fibre-jet theorem can be inserted directly. -/
theorem integral_twoJet {F : P × Q → E} {x₀ : P} {K : Set Q}
    (hK : IsCompact K) (hF : ∀ y ∈ K, ContDiffAt ℝ 2 F (x₀, y)) :
    IntegrableOn (fun y => fderiv ℝ (fun x => F (x, y)) x₀) K μ ∧
    IntegrableOn (fun y => fderiv ℝ (fderiv ℝ (fun x => F (x, y))) x₀) K μ ∧
    HasFDerivAt (fun x => ∫ y in K, F (x, y) ∂μ)
      (∫ y in K, fderiv ℝ (fun x => F (x, y)) x₀ ∂μ) x₀ ∧
    fderiv ℝ (fderiv ℝ (fun x => ∫ y in K, F (x, y) ∂μ)) x₀ =
      ∫ y in K, fderiv ℝ (fderiv ℝ (fun x => F (x, y))) x₀ ∂μ := by
  let G : P × Q → P →L[ℝ] E := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ P Q)
  let H : P × Q → P →L[ℝ] P →L[ℝ] E := fun p =>
    (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ P Q)
  have hG (y : Q) (hy : y ∈ K) : ContDiffAt ℝ 1 G (x₀, y) :=
    ((hF y hy).fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const
  have hH (y : Q) (hy : y ∈ K) : ContDiffAt ℝ 0 H (x₀, y) :=
    ((hG y hy).fderiv_right (m := 0) (by norm_num)).clm_comp contDiffAt_const
  have hslice (y : Q) (hy : y ∈ K) :
      (fun x => fderiv ℝ (fun v => F (v, y)) x) =ᶠ[𝓝 x₀] (fun x => G (x, y)) := by
    have hs : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 F (x, y) :=
      (continuousAt_id.prodMk continuousAt_const).tendsto.eventually ((hF y hy).eventually (by simp))
    filter_upwards [hs] with x hx
    exact (((hx.differentiableAt (by norm_num)).hasFDerivAt).comp
      (f := fun v : P => (v, y)) x (hasFDerivAt_prodMk_left x y)).fderiv
  have hslice₂ (y : Q) (hy : y ∈ K) :
      fderiv ℝ (fderiv ℝ (fun v => F (v, y))) x₀ = H (x₀, y) := by
    rw [(hslice y hy).fderiv_eq]
    exact (((hG y hy).differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : P => (v, y)) x₀ (hasFDerivAt_prodMk_left x₀ y)).fderiv
  have hGi : IntegrableOn (fun y => G (x₀, y)) K μ :=
    ContinuousOn.integrableOn_compact hK (fun y hy =>
      ((hG y hy).continuousAt.comp_of_eq (continuousAt_const.prodMk continuousAt_id) rfl).continuousWithinAt)
  have hHi : IntegrableOn (fun y => H (x₀, y)) K μ :=
    ContinuousOn.integrableOn_compact hK (fun y hy =>
      ((hH y hy).continuousAt.comp_of_eq (continuousAt_const.prodMk continuousAt_id) rfl).continuousWithinAt)
  have heG : (fun y => G (x₀, y)) =ᶠ[ae (μ.restrict K)]
      (fun y => fderiv ℝ (fun x => F (x, y)) x₀) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hslice y hy).self_of_nhds.symm
  have heH : (fun y => H (x₀, y)) =ᶠ[ae (μ.restrict K)]
      (fun y => fderiv ℝ (fderiv ℝ (fun x => F (x, y))) x₀) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hslice₂ y hy).symm
  change Integrable (fun y => G (x₀, y)) (μ.restrict K) at hGi
  change Integrable (fun y => H (x₀, y)) (μ.restrict K) at hHi
  refine ⟨hGi.congr heG, hHi.congr heH, ?_, ?_⟩
  · exact (hasFDerivAt_integral_compact (μ := μ) hK
      (fun y hy => (hF y hy).of_le (by norm_num))).congr_fderiv (integral_congr_ae heG)
  · have hevent : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, ContDiffAt ℝ 1 F (x, y) :=
      hK.eventually_forall_of_forall_eventually (fun y hy =>
        ((hF y hy).of_le (m := 1) (by norm_num)).eventually (by simp))
    have hdeq : fderiv ℝ (fun x => ∫ y in K, F (x, y) ∂μ) =ᶠ[𝓝 x₀]
        (fun x => ∫ y in K, G (x, y) ∂μ) := by
      filter_upwards [hevent] with x hx
      exact (hasFDerivAt_integral_compact (μ := μ) hK hx).fderiv
    rw [hdeq.fderiv_eq, (hasFDerivAt_integral_compact (μ := μ) hK hG).fderiv]
    exact integral_congr_ae heH

end CompactIntegrals

section Primitives

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace P] in
/-- Fixed oriented intervals retain all finite orders of smoothness. -/
theorem contDiffAt_intervalIntegral (n : ℕ) {F : P × ℝ → E} {x₀ : P} {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ n F (x₀, t)) :
    ContDiffAt ℝ n (fun x => ∫ t in a..b, F (x, t)) x₀ := by
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, uIoc,
    ← integral_Icc_eq_integral_Ioc]
  exact (contDiffAt_integral_compact n isCompact_Icc hF).const_smul _

omit [CompleteSpace P] [CompleteSpace E] in
/-- Fixed-interval differentiation, with the true first-parameter derivative. -/
theorem hasFDerivAt_intervalIntegral {F : P × ℝ → E} {x₀ : P} {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 F (x₀, t)) :
    HasFDerivAt (fun x => ∫ t in a..b, F (x, t))
      (∫ t in a..b, (fderiv ℝ F (x₀, t)).comp (ContinuousLinearMap.inl ℝ P ℝ)) x₀ := by
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, uIoc,
    ← integral_Icc_eq_integral_Ioc]
  exact (hasFDerivAt_integral_compact isCompact_Icc hF).const_smul _

/-- An oriented height primitive with all other parameters fixed. -/
def heightPrimitive (F : P × ℝ → E) (p : P × ℝ) : E := ∫ t in (0 : ℝ)..p.2, F (p.1, t)

omit [CompleteSpace P] in
/-- Smoothness of a moving-height primitive, by rescaling to the compact
unit interval. It asks only for the stated smoothness of the integrand. -/
theorem contDiffAt_heightPrimitive (n : ℕ) {F : P × ℝ → E} {p₀ : P × ℝ}
    (hF : ∀ t ∈ uIcc 0 p₀.2, ContDiffAt ℝ n F (p₀.1, t)) :
    ContDiffAt ℝ n (heightPrimitive F) p₀ := by
  have he : heightPrimitive F = fun p =>
      p.2 • ∫ u in (0 : ℝ)..1, F (p.1, p.2 * u) := by
    funext p
    symm
    simpa only [mul_zero, mul_one, heightPrimitive] using
      intervalIntegral.smul_integral_comp_mul_left (fun t => F (p.1, t)) p.2
        (a := 0) (b := 1)
  rw [he]
  apply contDiffAt_snd.smul
  apply contDiffAt_intervalIntegral n
    (F := fun p : (P × ℝ) × ℝ => F (p.1.1, p.1.2 * p.2))
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
  have ht : p₀.2 * u ∈ uIcc 0 p₀.2 := by
    rcases le_total 0 p₀.2 with hb | hb
    · rw [uIcc_of_le hb]
      exact ⟨mul_nonneg hb hu'.1, by nlinarith [mul_nonneg hb (sub_nonneg.mpr hu'.2)]⟩
    · rw [uIcc_of_ge hb]
      exact ⟨by nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu'.2)],
        mul_nonpos_of_nonpos_of_nonneg hb hu'.1⟩
  exact (hF _ ht).comp (p₀, u)
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.mul contDiffAt_snd))

omit [CompleteSpace P] in
/-- Leibniz' rule for a variable upper endpoint. Joint differentiability is
first obtained on a compact fixed domain; FTC then identifies the height
component of the differential. -/
theorem hasFDerivAt_heightPrimitive {F : P × ℝ → E} {p₀ : P × ℝ}
    (hF : ∀ t ∈ uIcc 0 p₀.2, ContDiffAt ℝ 1 F (p₀.1, t)) :
    HasFDerivAt (heightPrimitive F)
      (((∫ t in (0 : ℝ)..p₀.2, (fderiv ℝ F (p₀.1, t)).comp
          (ContinuousLinearMap.inl ℝ P ℝ)).comp (ContinuousLinearMap.fst ℝ P ℝ)) +
        (ContinuousLinearMap.snd ℝ P ℝ).smulRight (F p₀)) p₀ := by
  have hD : HasFDerivAt (heightPrimitive F) (fderiv ℝ (heightPrimitive F) p₀) p₀ :=
    ((contDiffAt_heightPrimitive 1 hF).differentiableAt (by norm_num)).hasFDerivAt
  have hleft := (hD.comp (f := fun x : P => (x, p₀.2)) p₀.1
    (hasFDerivAt_prodMk_left p₀.1 p₀.2)).unique (hasFDerivAt_intervalIntegral hF)
  have hcont : ContinuousOn (fun t => F (p₀.1, t)) (uIcc 0 p₀.2) := by
    intro t ht
    exact ((hF t ht).continuousAt.comp_of_eq
      (continuousAt_const.prodMk continuousAt_id) rfl).continuousWithinAt
  have ht : ContDiffAt ℝ 1 (fun t => F (p₀.1, t)) p₀.2 :=
    (hF _ (right_mem_uIcc)).comp p₀.2 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨U, hU, hbU, hCU⟩ := ht.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ p₀.2), univ_inter] at hCU
  have hFTC := intervalIntegral.integral_hasDerivAt_right hcont.intervalIntegrable
    (hCU.continuousOn.stronglyMeasurableAtFilter hU _ hbU) ht.continuousAt
  have hright := (hD.comp (f := fun t : ℝ => (p₀.1, t)) p₀.2
    (hasFDerivAt_prodMk_right p₀.1 p₀.2)).unique hFTC.hasFDerivAt
  apply hD.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = (v.1, 0) + (0, v.2) := by ext <;> simp
  rw [hv, map_add]
  have hl := congrArg (fun L : P →L[ℝ] E => L v.1) hleft
  have hr := congrArg (fun L : ℝ →L[ℝ] E => L v.2) hright
  simpa [ContinuousLinearMap.comp_apply] using congrArg₂ (· + ·) hl hr

omit [CompleteSpace P] in
/-- General moving-endpoint rule, including the endpoint term. -/
theorem hasFDerivAt_movingIntegral {F : P × ℝ → E} {η : P → ℝ} {p₀ : P}
    {η' : P →L[ℝ] ℝ} (hη : HasFDerivAt η η' p₀)
    (hF : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 F (p₀, t)) :
    HasFDerivAt (fun p => ∫ t in (0 : ℝ)..η p, F (p, t))
      ((∫ t in (0 : ℝ)..η p₀, (fderiv ℝ F (p₀, t)).comp
        (ContinuousLinearMap.inl ℝ P ℝ)) + η'.smulRight (F (p₀, η p₀))) p₀ := by
  have hD := (hasFDerivAt_heightPrimitive hF).comp
    (f := fun p => (p, η p)) p₀ ((hasFDerivAt_id p₀).prodMk hη)
  apply hD.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.comp_apply]

end Primitives

omit [NormedSpace ℝ P] [CompleteSpace P] in
/-- One neighborhood controls every point of every small oriented height
segment, including negative endpoints. -/
theorem eventually_heightSegments {η : P → ℝ} {p₀ : P} (hη : ContinuousAt η p₀)
    (hη₀ : η p₀ = 0) {U : Set (P × ℝ)} (hU : U ∈ 𝓝 (p₀, (0 : ℝ))) :
    ∀ᶠ p in 𝓝 p₀, ∀ t ∈ uIcc 0 (η p), (p, t) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hc : ContinuousAt (fun p => (p, η p)) p₀ := continuousAt_id.prodMk hη
  have he : ∀ᶠ p in 𝓝 p₀, (p, η p) ∈ Metric.ball (p₀, (0 : ℝ)) ε := by
    simpa only [hη₀] using hc.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  filter_upwards [he] with p hp t ht
  apply hball
  have hab : |t| ≤ |η p| := by simpa using abs_sub_left_of_mem_uIcc ht
  have hd : dist (p, t) (p₀, (0 : ℝ)) ≤ dist (p, η p) (p₀, (0 : ℝ)) := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_le_max le_rfl hab
  exact hd.trans_lt hp

section Fibres

/-- The oriented correction for one height fibre. -/
def fibre (W : ℝ → ℝ) (q : P × ℝ → ℝ) (η : P → ℝ) (p : P) : ℝ :=
  ∫ t in (0 : ℝ)..η p, W t * (q (p, t) - t)

/-- The derivative predicted by endpoint vanishing. No derivative of `W`
appears in this first parameter differential. -/
def fibreDifferential (W : ℝ → ℝ) (q : P × ℝ → ℝ) (η : P → ℝ)
    (p : P) : P →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..η p, W t •
    (fderiv ℝ q (p, t)).comp (ContinuousLinearMap.inl ℝ P ℝ)

omit [CompleteSpace P] in
/-- Endpoint vanishing gives the fibre derivative with only C¹ integrands.
This is an identity for the actual oriented integral. -/
theorem hasFDerivAt_fibre {W : ℝ → ℝ} {q : P × ℝ → ℝ} {η : P → ℝ} {p₀ : P}
    (hη : DifferentiableAt ℝ η p₀) (hroot : η p₀ = q (p₀, η p₀))
    (hW : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 W t)
    (hq : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 q (p₀, t)) :
    HasFDerivAt (fibre W q η) (fibreDifferential W q η p₀) p₀ := by
  let F : P × ℝ → ℝ := fun p => W p.2 * (q p - p.2)
  have hF : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 F (p₀, t) := fun t ht =>
    ((hW t ht).comp (p₀, t) contDiffAt_snd).mul ((hq t ht).sub contDiffAt_snd)
  have hD := hasFDerivAt_movingIntegral hη.hasFDerivAt hF
  have hend : F (p₀, η p₀) = 0 := by simp [F, ← hroot]
  have hz : (fderiv ℝ η p₀).smulRight (0 : ℝ) = 0 := by ext; simp
  rw [hend, hz, add_zero] at hD
  apply hD.congr_fderiv
  apply intervalIntegral.integral_congr
  intro t ht
  have hpartial := ((hF t ht).differentiableAt (by norm_num)).hasFDerivAt.comp
    (f := fun p : P => (p, t)) p₀ (hasFDerivAt_prodMk_left p₀ t)
  have hqpartial := ((hq t ht).differentiableAt (by norm_num)).hasFDerivAt.comp
    (f := fun p : P => (p, t)) p₀ (hasFDerivAt_prodMk_left p₀ t)
  exact hpartial.unique ((hqpartial.sub_const t).const_mul (W t))

omit [CompleteSpace P] in
/-- The collar fibre is C³ with a C² weight, not a falsely strengthened C³
Jacobian hypothesis. The gain is obtained by differentiating the vanishing
endpoint first, then proving its differential is C² on a fixed interval. -/
theorem contDiffAt_fibre {W : ℝ → ℝ} {q : P × ℝ → ℝ} {η : P → ℝ} {p₀ : P}
    (hW : ContDiffAt ℝ 2 W 0) (hq : ContDiffAt ℝ 3 q (p₀, 0))
    (hη : ContDiffAt ℝ 3 η p₀) (hη₀ : η p₀ = 0)
    (hroot : ∀ᶠ p in 𝓝 p₀, η p = q (p, η p)) :
    ContDiffAt ℝ 3 (fibre W q η) p₀ := by
  have hWq : ∀ᶠ a : P × ℝ in 𝓝 (p₀, (0 : ℝ)),
      ContDiffAt ℝ 1 W a.2 ∧ ContDiffAt ℝ 1 q a :=
    (continuousAt_snd.tendsto.eventually
      ((hW.of_le (m := 1) (by norm_num)).eventually (by simp))).and
        ((hq.of_le (m := 1) (by norm_num)).eventually (by simp))
  have hseg := eventually_heightSegments hη.continuousAt hη₀ hWq
  have hD : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fibre W q η) (fibreDifferential W q η p) p := by
    filter_upwards [hseg, hroot, hη.eventually (by simp)] with p hp hr hηp
    exact hasFDerivAt_fibre (hηp.differentiableAt (by norm_num)) hr
      (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2)
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 2)).mpr
  refine ⟨fibreDifferential W q η, ⟨_, hD, fun p hp => hp⟩, ?_⟩
  let G : P × ℝ → P →L[ℝ] ℝ := fun p => W p.2 •
    (fderiv ℝ q p).comp (ContinuousLinearMap.inl ℝ P ℝ)
  have hG : ContDiffAt ℝ 2 G (p₀, 0) :=
    (hW.comp (p₀, 0) contDiffAt_snd).smul
      ((hq.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const)
  have hGP : ContDiffAt ℝ 2 (heightPrimitive G) (p₀, η p₀) := by
    apply contDiffAt_heightPrimitive 2
    simp only [hη₀, uIcc_self, mem_singleton_iff]
    intro t ht
    subst t
    exact hG
  exact hGP.comp p₀ (contDiffAt_id.prodMk
    (hη.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)))

end Fibres

section UniformRoots

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [ProperSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Compact gluing of locally unique moving roots. The only local input is
an ordinary implicit-function root, not an overlap regularity assertion.
The common height and displacement radii are independent of the planar point. -/
theorem exists_uniform_roots {q : (Y × Z) × ℝ → ℝ} {K : Set Y} (hK : IsCompact K)
    (hq₀ : ∀ y, q ((y, 0), 0) = 0)
    (hlocal : ∀ y ∈ K, ∃ r : Y × Z → ℝ,
      r (y, 0) = 0 ∧ ContDiffAt ℝ 3 r (y, 0) ∧
        (∀ᶠ p in 𝓝 (y, (0 : Z)), r p = q (p, r p)) ∧
        (∀ᶠ a in 𝓝 ((y, (0 : Z)), (0 : ℝ)), a.2 = q a → a.2 = r a.1)) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ η : Y × Z → ℝ,
      (∀ y ∈ K, η (y, 0) = 0) ∧
      ∀ y ∈ K, ∀ z ∈ Metric.ball (0 : Z) δ,
        ContDiffAt ℝ 3 η (y, z) ∧ |η (y, z)| < ε ∧
          η (y, z) = q ((y, z), η (y, z)) ∧
          ∀ t, |t| < ε → t = q ((y, z), t) → t = η (y, z) := by
  classical
  have hdata : ∀ y : K, ∃ r : Y × Z → ℝ, ∃ a : ℝ, 0 < a ∧
      (∀ p ∈ Metric.ball (y.val, (0 : Z)) a,
        ContDiffAt ℝ 3 r p ∧ r p = q (p, r p)) ∧
      ∀ p ∈ Metric.ball ((y.val, (0 : Z)), (0 : ℝ)) a,
        p.2 = q p → p.2 = r p.1 := by
    intro y
    obtain ⟨r, _, hr, he, hu⟩ := hlocal y.val y.property
    have hv := (continuousAt_fst.tendsto.eventually ((hr.eventually (by simp)).and he)).and hu
    obtain ⟨a, ha, hb⟩ := Metric.eventually_nhds_iff.mp hv
    refine ⟨r, a, ha, ?_, fun p hp => (hb hp).2⟩
    intro p hp
    apply (hb (show dist (p, (0 : ℝ)) ((y.val, (0 : Z)), (0 : ℝ)) < a by
      change max (dist p (y.val, (0 : Z))) (dist (0 : ℝ) 0) < a
      simpa only [dist_self, max_eq_left dist_nonneg] using hp)).1
  choose r a ha hs hu using hdata
  let U : K → Set Y := fun y => Metric.ball y.val (a y / 2)
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U (fun _ => Metric.isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (ha ⟨y, hy⟩))⟩)
  let n := Fintype.card T
  let j : Fin n → K := fun i => ((Fintype.equivFin T).symm i).val
  have hcover : K ⊆ ⋃ i, U (j i) := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp (hT hy)
    exact mem_iUnion.mpr ⟨(Fintype.equivFin T) ⟨k, hk⟩, by simpa only [j, Equiv.symm_apply_apply] using hyk⟩
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ∀ i : Fin n, ε < a (j i) :=
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and (nhdsWithin_le_nhds
      (eventually_all.mpr fun i => gt_mem_nhds (ha (j i))))
  obtain ⟨ε, hε, hεa⟩ := heps.exists
  have hsmall : ∀ i : Fin n, ∃ d : ℝ, 0 < d ∧ ∀ z ∈ Metric.ball (0 : Z) d,
      ∀ y ∈ Metric.closedBall (j i).val (a (j i) / 2), |r (j i) (y, z)| < ε := by
    intro i
    have hbase (y : Y) (hy : y ∈ Metric.closedBall (j i).val (a (j i) / 2)) :
        ContDiffAt ℝ 3 (r (j i)) (y, 0) ∧ r (j i) (y, 0) = 0 := by
      have hp : (y, (0 : Z)) ∈ Metric.ball ((j i).val, (0 : Z)) (a (j i)) := by
        simp only [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact lt_of_le_of_lt hy (half_lt_self (ha (j i)))
      refine ⟨(hs (j i) _ hp).1, ?_⟩
      have he := hu (j i) ((y, 0), 0)
        (by simpa only [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hp)
        (hq₀ y).symm
      exact he.symm
    have hb : ∀ᶠ z in 𝓝 (0 : Z), ∀ y ∈ Metric.closedBall (j i).val (a (j i) / 2),
        |r (j i) (y, z)| < ε := by
      apply (isCompact_closedBall _ _).eventually_forall_of_forall_eventually
      intro y hy
      have hc : ContinuousAt (fun p : Z × Y => |r (j i) (p.2, p.1)|) (0, y) :=
        ((hbase y hy).1.continuousAt.comp_of_eq
          (continuousAt_snd.prodMk continuousAt_fst) rfl).abs
      exact hc.eventually (gt_mem_nhds (by simpa [(hbase y hy).2] using hε))
    obtain ⟨d, hd, hdb⟩ := Metric.eventually_nhds_iff.mp hb
    exact ⟨d, hd, hdb⟩
  choose d hd hdb using hsmall
  have hdel : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ ∀ i : Fin n, δ < min (d i) (a (j i) / 2) :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and (nhdsWithin_le_nhds
      (eventually_all.mpr fun i => gt_mem_nhds (lt_min (hd i) (half_pos (ha (j i))))))
  obtain ⟨δ, hδ, hδi⟩ := hdel.exists
  let η : Y × Z → ℝ := fun p =>
    if H : ∃ t : ℝ, |t| < ε ∧ t = q (p, t) then Classical.choose H else 0
  have hagree (i : Fin n) (p : Y × Z) (hp : p ∈ U (j i) ×ˢ Metric.ball (0 : Z) δ) :
      η p = r (j i) p ∧ |η p| < ε ∧ η p = q (p, η p) ∧
      ∀ t, |t| < ε → t = q (p, t) → t = η p := by
    have hpa : p ∈ Metric.ball ((j i).val, (0 : Z)) (a (j i)) := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt ((show dist p.1 (j i).val < a (j i) / 2 from hp.1).trans
        (half_lt_self (ha (j i)))) ((show dist p.2 0 < δ from hp.2).trans
        ((hδi i).trans_le (min_le_right _ _)) |>.trans (half_lt_self (ha (j i))))
    have hrb : |r (j i) p| < ε := hdb i p.2
      ((show dist p.2 0 < δ from hp.2).trans ((hδi i).trans_le (min_le_left _ _)))
      p.1 (Metric.ball_subset_closedBall hp.1)
    have hrex := (hs (j i) p hpa).2
    have hex : ∃ t : ℝ, |t| < ε ∧ t = q (p, t) := ⟨r (j i) p, hrb, hrex⟩
    have heta : |η p| < ε ∧ η p = q (p, η p) := by
      dsimp only [η]
      rw [dif_pos hex]
      exact Classical.choose_spec hex
    have huniq (t : ℝ) (ht : |t| < ε) (he : t = q (p, t)) : t = r (j i) p :=
      hu (j i) (p, t) (by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero]
        exact max_lt hpa (ht.trans (hεa i))) he
    have he := huniq _ heta.1 heta.2
    exact ⟨he, heta.1, heta.2, fun t ht heq => (huniq t ht heq).trans he.symm⟩
  refine ⟨ε, δ, hε, hδ, η, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hy)
    exact ((hagree i (y, 0) ⟨hi, Metric.mem_ball_self hδ⟩).2.2.2 0
      (by simpa using hε) (hq₀ y).symm).symm
  · intro y hy z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hy)
    have hp : (y, z) ∈ U (j i) ×ˢ Metric.ball (0 : Z) δ := ⟨hi, hz⟩
    have ha' := hagree i (y, z) hp
    have hpa : (y, z) ∈ Metric.ball ((j i).val, (0 : Z)) (a (j i)) := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt ((show dist y (j i).val < a (j i) / 2 from hi).trans
        (half_lt_self (ha (j i)))) ((show dist z 0 < δ from hz).trans
        ((hδi i).trans_le (min_le_right _ _)) |>.trans (half_lt_self (ha (j i))))
    have heq : η =ᶠ[𝓝 (y, z)] r (j i) :=
      mem_of_superset ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hp)
        (fun p hp => (hagree i p hp).1)
    exact ⟨((hs (j i) (y, z) hpa).1).congr_of_eventuallyEq heq,
      ha'.2.1, ha'.2.2.1, ha'.2.2.2⟩

end UniformRoots

/-- A unique contact separates the positive and negative gap regions.
No monotonicity of the weight, and no sign condition on the weight, is needed. -/
theorem gap_sign_of_unique_root {q : ℝ → ℝ} {B η : ℝ}
    (hη : η ∈ Icc 0 B) (hq : ContinuousOn q (Icc 0 B)) (h₀ : 0 ≤ q 0)
    (hB : q B < B) (hroot : η = q η)
    (hunique : ∀ t ∈ Icc 0 B, t = q t → t = η) :
    (∀ t ∈ Icc 0 η, 0 ≤ q t - t) ∧ (∀ t ∈ Icc η B, q t - t ≤ 0) := by
  classical
  have hc : ContinuousOn (fun t => q t - t) (Icc 0 B) := hq.sub continuousOn_id
  constructor
  · intro t ht
    by_contra hn
    have hneg : q t - t < 0 := lt_of_not_ge hn
    have hcont := hc.mono (Icc_subset_Icc le_rfl (ht.2.trans hη.2))
    obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' ht.1 hcont
      (show (0 : ℝ) ∈ Icc (q t - t) (q 0 - 0) by constructor <;> linarith)
    have he : u = η := hunique u ⟨hu.1, hu.2.trans (ht.2.trans hη.2)⟩ (by dsimp at hgu; linarith)
    have hte : t = η := le_antisymm ht.2 (he ▸ hu.2)
    rw [hte, ← hroot] at hneg
    linarith
  · intro t ht
    by_contra hn
    have hpos : 0 < q t - t := lt_of_not_ge hn
    have hcont := hc.mono (Icc_subset_Icc (hη.1.trans ht.1) le_rfl)
    obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' ht.2 hcont
      (show (0 : ℝ) ∈ Icc (q B - B) (q t - t) by constructor <;> linarith)
    have he : u = η := hunique u ⟨(hη.1.trans ht.1).trans hu.1, hu.2⟩ (by dsimp at hgu; linarith)
    have hte : t = η := le_antisymm (he ▸ hu.1) ht.1
    rw [hte, ← hroot] at hpos
    linarith

/-- The true positive-part height integral equals the oriented moving-root
integral, for an arbitrary signed continuous weight. -/
theorem integral_positivePart_eq_root {q W : ℝ → ℝ} {B η : ℝ}
    (hη : η ∈ Icc 0 B) (hq : ContinuousOn q (Icc 0 B))
    (hW : ContinuousOn W (Icc 0 B)) (h₀ : 0 ≤ q 0) (hB : q B < B)
    (hroot : η = q η) (hunique : ∀ t ∈ Icc 0 B, t = q t → t = η) :
    (∫ t in (0 : ℝ)..B, W t * max 0 (q t - t)) =
      ∫ t in (0 : ℝ)..η, W t * (q t - t) := by
  have hsign := gap_sign_of_unique_root hη hq h₀ hB hroot hunique
  have hc : ContinuousOn (fun t => W t * max 0 (q t - t)) (Icc 0 B) :=
    hW.mul (continuousOn_const.sup (hq.sub continuousOn_id))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (Icc_subset_Icc le_rfl hη.2)).intervalIntegrable_of_Icc hη.1)
    ((hc.mono (Icc_subset_Icc hη.1 le_rfl)).intervalIntegrable_of_Icc hη.2)]
  have hz : (∫ t in η..B, W t * max 0 (q t - t)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with t ht
    rw [uIoc_of_le hη.2] at ht
    rw [max_eq_left (hsign.2 t ⟨ht.1.le, ht.2⟩), mul_zero]
  rw [hz, add_zero]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hη.1] at ht
  dsimp only
  rw [max_eq_right (hsign.1 t ht)]

section AveragedFibres

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Jointly parameterized fibre, with the planar point kept distinct from
the displacement parameter. -/
def parametricFibre (W : Y × ℝ → ℝ) (q : (Y × Z) × ℝ → ℝ)
    (η : Y × Z → ℝ) (p : Y × Z) : ℝ :=
  ∫ t in (0 : ℝ)..η p, W (p.1, t) * (q (p, t) - t)

/-- The displacement differential; planar derivatives of the Jacobian are
not mistakenly introduced into the displacement jet. -/
def parametricFibreDifferential (W : Y × ℝ → ℝ) (q : (Y × Z) × ℝ → ℝ)
    (η : Y × Z → ℝ) (p : Y × Z) : Z →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..η p, W (p.1, t) •
    (fderiv ℝ q (p, t)).comp ((ContinuousLinearMap.inl ℝ (Y × Z) ℝ).comp
      (ContinuousLinearMap.inr ℝ Y Z))

/-- Only C² joint regularity is asserted for the fibre including planar
parameters. This is sufficient for the first differentiation under the disk
integral, and does not overstate the Jacobian's regularity. -/
theorem contDiffAt_parametricFibre_two {W : Y × ℝ → ℝ} {q : (Y × Z) × ℝ → ℝ}
    {η : Y × Z → ℝ} {p₀ : Y × Z} (hη₀ : η p₀ = 0)
    (hW : ContDiffAt ℝ 2 W (p₀.1, 0)) (hq : ContDiffAt ℝ 2 q (p₀, 0))
    (hη : ContDiffAt ℝ 2 η p₀) : ContDiffAt ℝ 2 (parametricFibre W q η) p₀ := by
  let F : (Y × Z) × ℝ → ℝ := fun p => W (p.1.1, p.2) * (q p - p.2)
  have hF : ContDiffAt ℝ 2 F (p₀, 0) :=
    (hW.comp (p₀, 0) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).mul (hq.sub contDiffAt_snd)
  have hp : ContDiffAt ℝ 2 (heightPrimitive F) (p₀, η p₀) := by
    apply contDiffAt_heightPrimitive 2
    simp only [hη₀, uIcc_self, mem_singleton_iff]
    rintro t rfl
    exact hF
  exact hp.comp p₀ (contDiffAt_id.prodMk hη)

/-- The true displacement differential is jointly C² in planar coordinates
and displacement. Thus its compact planar integral is C². -/
theorem contDiffAt_parametricFibreDifferential_two {W : Y × ℝ → ℝ}
    {q : (Y × Z) × ℝ → ℝ} {η : Y × Z → ℝ} {p₀ : Y × Z}
    (hη₀ : η p₀ = 0) (hW : ContDiffAt ℝ 2 W (p₀.1, 0))
    (hq : ContDiffAt ℝ 3 q (p₀, 0)) (hη : ContDiffAt ℝ 2 η p₀) :
    ContDiffAt ℝ 2 (parametricFibreDifferential W q η) p₀ := by
  let G : (Y × Z) × ℝ → Z →L[ℝ] ℝ := fun p => W (p.1.1, p.2) •
    (fderiv ℝ q p).comp ((ContinuousLinearMap.inl ℝ (Y × Z) ℝ).comp
      (ContinuousLinearMap.inr ℝ Y Z))
  have hG : ContDiffAt ℝ 2 G (p₀, 0) :=
    (hW.comp (p₀, 0) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).smul
      ((hq.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const)
  have hp : ContDiffAt ℝ 2 (heightPrimitive G) (p₀, η p₀) := by
    apply contDiffAt_heightPrimitive 2
    simp only [hη₀, uIcc_self, mem_singleton_iff]
    rintro t rfl
    exact hG
  exact hp.comp p₀ (contDiffAt_id.prodMk hη)

/-- Parameter differentiation of a single actual oriented fibre. -/
theorem hasFDerivAt_parametricFibre {W : Y × ℝ → ℝ} {q : (Y × Z) × ℝ → ℝ}
    {η : Y × Z → ℝ} {p₀ : Y × Z} (hη : DifferentiableAt ℝ η p₀)
    (hr : η p₀ = q (p₀, η p₀))
    (hW : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 W (p₀.1, t))
    (hq : ∀ t ∈ uIcc 0 (η p₀), ContDiffAt ℝ 1 q (p₀, t)) :
    HasFDerivAt (fun z => parametricFibre W q η (p₀.1, z))
      (parametricFibreDifferential W q η p₀) p₀.2 := by
  let qy : Z × ℝ → ℝ := fun p => q ((p₀.1, p.1), p.2)
  let J : (Z × ℝ) →L[ℝ] (Y × Z) × ℝ :=
    ((0 : Z × ℝ →L[ℝ] Y).prod (ContinuousLinearMap.fst ℝ Z ℝ)).prod
      (ContinuousLinearMap.snd ℝ Z ℝ)
  have hemb (t : ℝ) : HasFDerivAt (fun p : Z × ℝ => ((p₀.1, p.1), p.2)) J (p₀.2, t) := by
    exact ((hasFDerivAt_const p₀.1 (p₀.2, t)).prodMk hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hD := hasFDerivAt_fibre (W := fun t => W (p₀.1, t)) (q := qy)
    (η := fun z => η (p₀.1, z))
    (hη.comp (f := fun z : Z => (p₀.1, z)) p₀.2
      (hasFDerivAt_prodMk_right p₀.1 p₀.2).differentiableAt) hr
    (fun t ht => (hW t ht).comp t (contDiffAt_const.prodMk contDiffAt_id))
    (fun t ht => (hq t ht).comp (p₀.2, t)
      ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd))
  apply hD.congr_fderiv
  apply intervalIntegral.integral_congr
  intro t ht
  have hqy : HasFDerivAt qy ((fderiv ℝ q (p₀, t)).comp J) (p₀.2, t) :=
    ((hq t ht).differentiableAt (by norm_num)).hasFDerivAt.comp (p₀.2, t) (hemb t)
  change W (p₀.1, t) • (fderiv ℝ qy (p₀.2, t)).comp (ContinuousLinearMap.inl ℝ Z ℝ) = _
  rw [hqy.fderiv]
  apply congrArg (fun L : Z →L[ℝ] ℝ => W (p₀.1, t) • L)
  apply ContinuousLinearMap.ext
  intro v
  rfl

variable [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {μ : Measure Y} [IsFiniteMeasureOnCompacts μ]

set_option maxHeartbeats 800000 in
/-- The explicit displacement differential commutes with compact planar
integration throughout one common neighborhood of zero. -/
theorem eventually_hasFDerivAt_averagedFibre {W : Y × ℝ → ℝ} {q : (Y × Z) × ℝ → ℝ}
    {η : Y × Z → ℝ} {K : Set Y} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hW : ∀ y ∈ K, ContDiffAt ℝ 2 W (y, 0))
    (hq : ∀ y ∈ K, ContDiffAt ℝ 3 q ((y, 0), 0))
    (hη : ∀ y ∈ K, ContDiffAt ℝ 3 η (y, 0)) (hη₀ : ∀ y ∈ K, η (y, 0) = 0)
    (hr : ∀ y ∈ K, ∀ z ∈ Metric.ball (0 : Z) δ, η (y, z) = q ((y, z), η (y, z))) :
    ∀ᶠ z in 𝓝 (0 : Z), HasFDerivAt
      (fun z => ∫ y in K, parametricFibre W q η (y, z) ∂μ)
      (∫ y in K, parametricFibreDifferential W q η (y, z) ∂μ) z := by
  have htwo (y : Y) (hy : y ∈ K) :
      ContDiffAt ℝ 2 (parametricFibre W q η) (y, 0) :=
    contDiffAt_parametricFibre_two (hη₀ y hy) (hW y hy)
      ((hq y hy).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
      ((hη y hy).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
  have hevent : ∀ᶠ z in 𝓝 (0 : Z), ∀ y ∈ K,
      ContDiffAt ℝ 1 (parametricFibre W q η) (y, z) ∧ DifferentiableAt ℝ η (y, z) ∧
      ∀ t ∈ uIcc 0 (η (y, z)),
        ContDiffAt ℝ 1 W (y, t) ∧ ContDiffAt ℝ 1 q ((y, z), t) := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have hs : ∀ᶠ a : (Y × Z) × ℝ in 𝓝 ((y, (0 : Z)), (0 : ℝ)),
        ContDiffAt ℝ 1 W (a.1.1, a.2) ∧ ContDiffAt ℝ 1 q a :=
      ((continuousAt_fst.fst.prodMk continuousAt_snd).tendsto.eventually
        (((hW y hy).of_le (m := 1) (by norm_num)).eventually (by simp))).and
          (((hq y hy).of_le (m := 1) (by norm_num)).eventually (by simp))
    have hseg := eventually_heightSegments (hη y hy).continuousAt (hη₀ y hy) hs
    have hep := (((htwo y hy).of_le (m := 1) (by norm_num)).eventually (by simp)).and
      (((hη y hy).eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
    have hswap : ContinuousAt (Prod.swap : Z × Y → Y × Z) (0, y) := continuous_swap.continuousAt
    have he := hswap.tendsto.eventually (hep.and hseg)
    exact he.mono fun _ hp => ⟨hp.1.1, hp.1.2, hp.2⟩
  have hderiv : ∀ᶠ z in 𝓝 (0 : Z), HasFDerivAt
      (fun z => ∫ y in K, parametricFibre W q η (y, z) ∂μ)
      (∫ y in K, parametricFibreDifferential W q η (y, z) ∂μ) z := by
    filter_upwards [hevent, Metric.ball_mem_nhds (0 : Z) hδ] with z hz hzb
    let F : Z × Y → ℝ := fun p => parametricFibre W q η (p.2, p.1)
    have hF (y : Y) (hy : y ∈ K) : ContDiffAt ℝ 1 F (z, y) :=
      (hz y hy).1.comp (z, y) (contDiffAt_snd.prodMk contDiffAt_fst)
    apply (hasFDerivAt_integral_compact (μ := μ) (F := F) (x₀ := z) hK hF).congr_fderiv
    apply setIntegral_congr_fun hK.measurableSet
    intro y hy
    have hDf : HasFDerivAt F (fderiv ℝ F (z, y)) (z, y) :=
      ((hF y hy).differentiableAt (by norm_num)).hasFDerivAt
    have hd : HasFDerivAt (fun v : Z => parametricFibre W q η (y, v))
        ((fderiv ℝ F (z, y)).comp (ContinuousLinearMap.inl ℝ Z Y)) z :=
      hDf.comp (f := fun v : Z => (v, y)) z (hasFDerivAt_prodMk_left z y)
    exact hd.unique (hasFDerivAt_parametricFibre (W := W) (q := q) (η := η) (p₀ := (y, z))
      (hz y hy).2.1 (hr y hy z hzb)
      (fun t ht => ((hz y hy).2.2 t ht).1) (fun t ht => ((hz y hy).2.2 t ht).2))
  exact hderiv

/-- Compact planar averaging gains the third displacement derivative by
integrating the explicitly identified C² differential. Neither a C³ weight
nor joint C³ smoothness of the fibre in planar coordinates is required. -/
theorem contDiffAt_averagedFibre {W : Y × ℝ → ℝ} {q : (Y × Z) × ℝ → ℝ}
    {η : Y × Z → ℝ} {K : Set Y} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hW : ∀ y ∈ K, ContDiffAt ℝ 2 W (y, 0))
    (hq : ∀ y ∈ K, ContDiffAt ℝ 3 q ((y, 0), 0))
    (hη : ∀ y ∈ K, ContDiffAt ℝ 3 η (y, 0)) (hη₀ : ∀ y ∈ K, η (y, 0) = 0)
    (hr : ∀ y ∈ K, ∀ z ∈ Metric.ball (0 : Z) δ, η (y, z) = q ((y, z), η (y, z))) :
    ContDiffAt ℝ 3 (fun z => ∫ y in K, parametricFibre W q η (y, z) ∂μ) 0 := by
  have hderiv := eventually_hasFDerivAt_averagedFibre (μ := μ) hK hδ hW hq hη hη₀ hr
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 2)).mpr
  refine ⟨fun z => ∫ y in K, parametricFibreDifferential W q η (y, z) ∂μ,
    ⟨_, hderiv, fun z hz => hz⟩, ?_⟩
  apply contDiffAt_integral_compact 2 hK
    (F := fun p : Z × Y => parametricFibreDifferential W q η (p.2, p.1))
  intro y hy
  exact (contDiffAt_parametricFibreDifferential_two (hη₀ y hy) (hW y hy) (hq y hy)
    ((hη y hy).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))).comp (0, y)
      (contDiffAt_snd.prodMk contDiffAt_fst)

end AveragedFibres
end MovingCollar
end BoundaryDraft
