import BoundaryDraft.TwoFaceLongNull

/-!
# Actual fixed-cutoff long-density cancellation for class E

The raw region and actual density are unchanged. The long fibres use the
causal upper envelope, which agrees locally with the raw future germ on the
proved compact interior perturbation tube. The shared proof retains every
contact regime, moving-contact coefficient, three-probe integrability and
finite-support domination. This is not a short or full action limit, uniform
fibre little-o, a shrinking-cutoff theorem or absolute pair-term decay.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- The gap is exactly upper-at-target minus lower-at-source minus elapsed time. -/
theorem gap_eq_envelopes (x y : Spatial) (s : ℝ) :
    twoFaceGap h hf.upperEnvelope x y s = hf.upperEnvelope y - hf.lowerEnvelope x - s := by
  unfold twoFaceGap
  rw [← hf.envelope_gap x]
  ring

theorem translatedOverlap_eq_gap {s : ℝ} {a : Spatial}
    (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoFaceRegion h f) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (twoFaceGap h hf.upperEnvelope x (x + a) s) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.translatedOverlap_eq_gap hz

/-- One common geometric package before either fibre quantifier. In particular,
the old-active smooth tube remains valid after the perturbed gap turns negative. -/
theorem exists_long_hypotheses {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ε c A M B : ℝ, δ < V ∧ 0 < ε ∧ 0 < c ∧ 0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (x : Spatial) (ω : OverlapSphere),
        MonotoneHinge.Hypotheses (twoFaceRayGap h hf.upperEnvelope x ω)
          TwoFaceLongGeometry.weight δ V ε c A M B :=
  TwoFaceLongGeometry.Envelope.exists_hypotheses hf.toLongEnvelopeData hδ

/-- Pointwise disintegration, including zero, with the original full sphere
measure and proper-time Jacobian. This is not an a.e. density replacement. -/
theorem longOverlapDensity_eq_gap_fibres {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hs : σ < δ ^ 2) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ ω, (∫ x : Spatial, ∫ v in Ici δ,
        ((v - σ/v)^2 / (8*v)) * max 0 (twoFaceRayGap h hf.upperEnvelope x ω σ v))
        ∂overlapSphereMeasure := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.longOverlapDensity_eq_gap_fibres hδ hσ hs

/-- Exact finite hinge identification; Fubini follows proved integrability. -/
theorem longOverlapDensity_eq_parameterFibre {δ V σ : ℝ}
    (hδ : 0 < δ) (hV : δ < V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ x ω, twoFaceRayGap h hf.upperEnvelope x ω 0 V ≤ 0) :
    longOverlapDensity (twoFaceRegion h f) δ σ =
      ∫ p : TwoFaceLongNull.Parameter, MonotoneHinge.fibre
        (twoFaceRayGap h hf.upperEnvelope p.2 p.1) TwoFaceLongGeometry.weight δ V σ
        ∂(overlapSphereMeasure.prod volume) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.longOverlapDensity_eq_parameterFibre hδ hV hσ hs hclear

/-- No jet, contact-nullity or root-measurability premise is added to class E. -/
theorem longOverlapDensity_right_quadratic_jet {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 b2 : ℝ,
      (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
        (b0 + b1 * σ + b2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.longOverlapDensity_right_quadratic_jet hδ

theorem integrableOn_longOverlap_bdg (δ ρ : ℝ) :
    IntegrableOn (fun z => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) (longFuture δ) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.integrableOn_longOverlap_bdg δ ρ

theorem integrableOn_longOverlapDensity_bdg (δ ρ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ *
      bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (Ioi 0) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.integrableOn_longOverlapDensity_bdg δ ρ hδ

/-- Signed original-kernel transport, removing only the null endpoint sigma=0. -/
theorem integral_longOverlap_bdg_Ioi {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ in Ioi 0, longOverlapDensity (twoFaceRegion h f) δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.integral_longOverlap_bdg_Ioi hδ ρ

theorem tendsto_longOverlap {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.tendsto_longOverlap hδ

/-- The actual negative signed action contribution, with both density factors,
at EVERY fixed positive cutoff. No assertion about the point or short term. -/
theorem tendsto_normalized_longOverlap {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  rw [hf.region_eq_upperEnvelope]
  exact hf.toLongEnvelopeData.tendsto_normalized_longOverlap hδ

end AdmissibleIndependentTwoFace
end BoundaryDraft
