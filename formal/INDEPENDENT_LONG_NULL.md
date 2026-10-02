# Class-E fixed-cutoff long cancellation (#108)

## Result and limits of the claim

`BoundaryDraft.IndependentFaceLongNull` proves the actual long-density right
quadratic jet and the fully normalized signed long contribution's limit for
every `AdmissibleIndependentTwoFace h f` and every fixed positive cutoff.
The input is exactly the geometric class E from
[the independent-envelope package](INDEPENDENT_FACE_GEOMETRY.md).
There is no combined slope budget, exclusion of interior critical points, or
jet, integrability, root-selection or limit premise in that contract.

The public downstream interfaces are:

```lean
AdmissibleIndependentTwoFace.longOverlapDensity_right_quadratic_jet
AdmissibleIndependentTwoFace.tendsto_longOverlap
AdmissibleIndependentTwoFace.tendsto_normalized_longOverlap
```

The last theorem has the literal original physical normalization:

```lean
theorem AdmissibleIndependentTwoFace.tendsto_normalized_longOverlap
    {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0)
```

This is the actual long pair term, **not** a short or full action limit.
It does not establish uniform fibre little-o, shrinking-cutoff uniformity,
absolute decay of the original pair term, a rate, an expectation limit or
sample-wise convergence. The independently proved finite-density Poisson
bridge remains separate. #107 supplies the actual short proof; #109 owns
coefficient identification and final assembly; PR #104 owns final integration
and its final full audit. This child does not complete #97 or claim independent
human mathematical review.

## Shared proof, unchanged old contracts

`LongEnvelopeData h u` is a derived geometric package for the long proof,
not a replacement admissibility class. It contains regular compact height
geometry, independent strict upper/lower causal envelopes, upper-envelope
smoothness **only inside positivity**, and boundedness of the region.
Every original `AdmissibleTwoFace` supplies it with its original future face.
Every class-E member supplies it with its chosen `upperEnvelope`.
`region_eq_upperEnvelope` proves that this substitution changes no region.

The long geometry, disintegration and averaging implementations are shared in
`TwoFaceLongGeometry`, `TwoFaceLongDisintegration` and `TwoFaceLongNull`.
All old public theorem signatures and callers are retained as wrappers.
`twoFaceGap`, `twoFaceRayGap`, the weight, actual `longOverlapDensity`,
`continuumMean`, the original signed kernel and the sphere measure are unchanged.
The independent hinge, averaged-jet and transverse-cancellation lemmas are
reused, not reproved.

`gap_eq_envelopes` identifies the envelope gap with upper-at-target minus
lower-at-source minus elapsed time. `translatedOverlap_eq_gap` derives its
positive-part integral from the existing causal two-graph formula, including
the vertex and null displacements. No partner is dropped.

## Geometry: the essential repaired interval

`LongEnvelopeData.envelope_bounds` retains separate lower/upper constants.
Its thickness bound is their **sum**, which need not be below one.
`gap_height_margins` proves the two endpoint bounds of (E21), including exact
contact. `exists_gap_height_margin` uses the **minimum** of the two causal
margins. The unchanged finite-difference ray lemmas give strict null decrease,
right proper-time monotonicity and non-opening of the whole cutoff-contact set.

`TwoFaceLongGeometry.perturbationWidth` is exactly (E24) in
[the written audit, section 7](../notes/independent-face-extension.md#7-long-null-audit-replace-the-margin-not-the-cancellation-theorem).
`perturbationWidth_loss` proves the height-loss inequality using the sum, not
the old shortcut requiring thickness below one. `old_endpoint_margin` and
`perturbed_endpoint_margin` put all old-active endpoints in compact positive
superlevel tubes. The latter theorem has **no new-gap positivity hypothesis**.
It therefore retains endpoints after perturbation makes their gap negative.

On an open neighborhood of each such point, `smooth_upper_positive` identifies
the causal envelope with the raw C³ future germ. `Envelope.exists_hypotheses`
bounds the actual second parameter derivative of the weight-times-gap product
on the compact active box. This includes both product cross terms and the
Jacobian derivatives. It does not differentiate a clipped envelope at the joint
or assume nonzero height differential inside positivity. Strict clearance at
the common upper endpoint and global non-opening justify the finite truncation.

## Disintegration, contact coefficients and averaging

The same nonnegative Tonelli argument proves joint measurability and finiteness
before conversion to real integrals. The class-E interfaces
`longOverlapDensity_eq_gap_fibres` and `longOverlapDensity_eq_parameterFibre`
identify the **actual** density pointwise throughout the right neighborhood,
including zero. The long lower endpoint, closed-cutoff convention, full sphere
mass, and proper-time Jacobian are retained. Real Fubini is used only after
absolute integrability has been derived.

`exists_long_hypotheses` supplies the unchanged `MonotoneHinge.Hypotheses`
with common constants preceding both fibre quantifiers. Its three regimes,
right quadratic jet, normalized remainder bound and `coefficients_of_root`
therefore apply. Negative and exact cutoff contacts have zero right fibres
and coefficients. A strictly active root retains the moving-contact coefficient
with its factor one-half. There is no measurable root selection or null-contact
set argument.

`AveragedQuadraticJet.measurable_coefficients_of_right_jet` recovers measurable
coefficients from measurable probes. The unchanged
`TwoFaceLongNull.integrable_coefficients_of_three_probes` supplies coefficient
integrability on the finite active support. Fibres and all coefficients vanish
off that support. Its indicator times the common remainder bound is integrable
on the full sphere-times-space measure; a positive constant is never integrated
over all space. Dominated averaging yields the actual density jet.

The original signed transverse cancellation then applies. The public
`integrableOn_longOverlap_bdg`, `integrableOn_longOverlapDensity_bdg` and
`integral_longOverlap_bdg_Ioi` expose absolute integrability and exact signed
transport at every real density. Removing the single zero endpoint uses
atomlessness; no surrounding near-null layer is removed. Conversion of the
three-halves power at eventually positive density retains both density factors
and the negative physical prefactor.

## Acceptance and regressions

| #108 obligation | Implementation and regression |
| --- | --- |
| Independent margins, monotonicity, compact smooth tube | `LongEnvelopeData`, `TwoFaceLongGeometry.Envelope`, E24 width/loss and steep-thickness regression |
| Actual pointwise triple integral and signed representation | `TwoFaceLongDisintegration`, class-E density/transport contracts including zero |
| All hinge regimes and moving contact | Existing `MonotoneHingeIntegral`; class-E common hypotheses; exact rational steep-capsule contact |
| Measurability, coefficient integrability, finite domination | Shared `TwoFaceLongNull` three-probe proof and `AveragedQuadraticJet`, unchanged analytic contracts |
| Actual density jet and normalized long cancellation | Three public class-E theorems above, independently expanded in `IndependentFaceLongRegression.lean` |
| Steep witness, old compatibility and critical points | Every positive cutoff on the steep capsule, its exclusion from the old class and retained critical point; original planar/unequal-axis callers |

`IndependentFaceLongRegression.lean` also checks the failure of the old
perturbation shortcut at thickness constant three-halves and compact containment
of old-active perturbed endpoints. The rational steep contact uses source and
target at opposite one-third radii and cutoff four-thirds, in every direction.
Its right coefficients vanish, while every positive proper-time perturbation
makes the gap strictly negative. Original standalone component regressions
continue checking approaching contacts, nonuniform fibre little-o, atomic
positive-measure contacts and the nonintegrable-scale negative control.

`test_independent_faces.py` independently checks the steep capsule's original
Jacobian-weighted fibre against direct vertical interval intersection. Its
strictly active rational root has moving-contact coefficient `27/2560`;
omitting it leaves a nonzero quadratic error. At exact cutoff contact the
right fibre instead vanishes. These symbolic/numerical checks complement,
but do not replace, the Lean source/warnings/transitive-axiom audit.
