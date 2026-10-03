# Independent-envelope deterministic and expected limits (#109 / #97)

## Result and exact boundary

`BoundaryDraft.IndependentFaceLimit` assembles the unconditional deterministic
and expected-action limits for **exactly class E**. It consumes the actual short
producer from #107 and the actual long cancellation from #108, not conditional
analytic substitutes. `AdmissibleIndependentTwoFace`, `AdmissibleTwoFace`,
`continuumMean`, the unsmeared discrete action, restricted Poisson law and
intrinsic target are unchanged.

The public conclusions are:

```lean
theorem AdmissibleIndependentTwoFace.twoFaceLimit
    {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f))

theorem AdmissibleIndependentTwoFace.expectedBDGAction_limit
    {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f) :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f))
```

`independentTwoFaceLimitGoal` and `independentTwoFaceExpectedLimitGoal` prove the
corresponding enlarged contracts. The original `TwoFaceLimitGoal`,
`TwoFaceExpectedLimitGoal` and their proofs remain available without changes.
No statement concerns individual sprinklings, a convergence rate, varying
geometry or a density-dependent cutoff.

Class E means a bounded positive-height region, C³ raw height and future germs
near its closure, nonzero height differential only at its zero-level joint,
and two independently strict global causal envelopes. Their difference is the
positive part of the height and they agree with the raw faces on the closure;
they coincide outside positivity. The regular-height boundary-zero field
retains class E's explicit boundary condition. The raw germs need not be
smooth globally; the clipped envelopes need
not be differentiable across the joint. No sum of slope constants below one,
noncritical positive-height interior, nonempty joint, positive volume, jet,
cancellation, integrability, action identity or limit is added as a premise.

## Interface audit

The audit reads the public statements and their producers, not issue states.
The geometry contract is in `IndependentFaceContract.lean`; its fields contain
only geometric data. The intermediate `RawFaceNeighborhood`,
`RegularHeightPair`, `LongEnvelopeData`, angular expansion and remainder bounds
are all **derived**, not passed to either final theorem by a caller.

| Interface | Exact checked convention / producer |
| --- | --- |
| Region and interval regime | The original `twoFaceRegion h f`; `region_eq_twoGraphRegion`, `isOpen_region`, `isBounded_region` and `causallyConvex_region` derive the entire closed ambient interval condition, including null segments. Intrinsic global hyperbolicity alone is not substituted. |
| Raw/envelope replacement | `exists_rawFaceNeighborhood`, `partner_positive`, `raw_envelope_positivePart` and `translatedOverlap_eq_shortGap` prove agreement before displacement differentiation, including null displacements and the vertex. No exterior raw continuity is assumed. |
| Actual short density | `exists_shortOverlapDensity_decomposition` identifies the existing `shortOverlapDensity`, not a new polynomial density. Absolute integrability of the actual and remainder product integrands precedes signed Fubini. |
| Signed kernel and constants | The original `bdgKernel`, interval factor `Real.pi / 24`, sphere mass `4 * Real.pi`, radial Jacobian `(v - σ / v)^2 / (8 * v)` and action prefactor `(4 / Real.sqrt 6) * Real.sqrt ρ` are retained. The pair term retains the additional factor `ρ`. No absolute-value kernel replaces the signed one. |
| All short modes | Constant volume, time-linear slice, time square and spatial square are produced with coefficients `volume.real (twoFaceRegion h f)`, `-4 * Real.pi * volume.real {x : JointSpace | 0 < h x}`, `2 * Real.pi * graphBoundaryIntegral h` and `twoFaceShortCoefficient h f`, in the existing `AbsoluteShortModel.density` convention (which supplies the constant mode's sphere factor). |
| Primitive remainder | `exists_absoluteOverlap_remainder` derives one measurable remainder with value, first-derivative and second-derivative cubic bounds. `exists_shortContinuumMean_limit` discharges every input to the conditional analytic transfer, including the actual point volume and density identity. |
| Short cutoff quantifiers | One positive bound is produced before density varies. Every fixed positive cutoff at most that bound works, **including the bound itself**. The moving lower radial endpoint and sharp upper cutoff are retained. |
| Long geometry | `LongEnvelopeData.envelope_bounds` and `gap_height_margins` keep both endpoint constants; the minimum causal margin and sum-controlled `perturbationWidth` give the compact old-active perturbation tube. No old combined budget is used. |
| Actual long density | `longOverlapDensity_eq_gap_fibres` and `longOverlapDensity_eq_parameterFibre` are pointwise identities near zero, including zero. All hinge regimes, moving-contact coefficient, measurable coefficients, three-probe integrability and finite-support domination are retained. |
| Long cutoff quantifiers | `tendsto_normalized_longOverlap` holds at **every fixed positive cutoff**, with the negative physical prefactor. No uniform fibre little-o, shrinking cutoff or absolute pair-term decay is required. |
| Canonical target | `twoFaceProjectedArea` retains normalized spatial Hausdorff measure `π/4` times the actual Lorentzian Gram density, not the Euclidean spacetime graph density. `IndependentFaceSurface` proves chart derivatives, measure-level chart/overlap compatibility, finiteness and absolute integrability. `IndependentFaceAngle` derives the strictly positive angle of both future unit normals. |
| Probability observable | `expectedBDGAction` integrates the original `discreteBDGAction` against `FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)`. Positive density and the derived bounded causal region instantiate the separately proved `ExpectationBridge`. |

No hidden original-class cap hypothesis or undischarged analytic input was
found in these final interfaces. In particular, `graphBoundaryIntegral h` is
used as a geometric reciprocal-gradient integral, **not** as a claim that the
same-height planar cap is admissible. The steep capsule's planar comparison
remains invalid; no old planar action theorem is invoked on it.

## Conventional assembly argument

### 1. The short coefficient is the independent intrinsic target

The complete raw-germ overlap two-jet has its actual volume and time-linear
slice, the spatial linear term, the bulk future Hessian, and the canonical
surface square. The full-sphere average preserves both quadratic modes.
The analytic backend cancels the constant term with the original point term,
including its logarithmic moment, and cancels the moving-endpoint linear term.
Its two signed quadratic responses and derivative-controlled remainder give
the coefficient in `absoluteShortCoefficient_identification`.

That identification uses `AdmissibleIndependentTwoFace.spatial_divergence`,
derived from `RegularHeightPair` with no cap-slope condition. The bulk future
Laplacian becomes the boundary flux; it is not dropped. The independently
proved `weight_mul_areaDensity` and `boundaryIntegral_eq_spatialCoefficient`
then give exactly `twoFaceBoundaryIntegral h f`, with the positive-angle
branch and canonical Lorentzian area. Finiteness and absolute integrability
precede the conversion. The height atlas transports only a regular collar;
positive-height critical points stay in the fixed interior integral.

This route introduces no weighted source action. The finite atlas sums the
actual collar with its original weights and all partners; it does not add
isolated chart actions. No artificial source-weight derivatives are silently
discarded or claimed to vanish separately. The complete upstream collar sum
and unweighted divergence already produce the absolute coefficient.

### 2. Choose one common cutoff and recombine exactly

For a fixed class-E member, take the positive bound supplied by
`exists_shortContinuumMean_limit` and choose that bound itself as the cutoff.
The endpoint-inclusive quantifier makes this a permitted short cutoff. It is
chosen from geometry once, before density tends to infinity. The long theorem
accepts every positive fixed cutoff, hence accepts this **same** one.

`shortFuture` is the complement of `longFuture` in the causal cone. The domains
are disjoint, exhaust the cone and assign cutoff equality to long. The signed
integrand is absolutely integrable before it is partitioned. The exact
`continuumMean_eq_short_sub_long` assigns the point term once to short and
retains the negative long contribution with both density factors. The new
`continuumMean_eq_short_sub_density` also exposes the existing long density
on the positive proper-time half-line; only its null endpoint is removed.

The chosen short observable tends to the intrinsic target. The actual
normalized long contribution tends to zero at that cutoff. Adding these
limits in the exact identity proves `twoFaceLimit`. There is no residual
cutoff defect and **no limit sending the cutoff to zero**. The implementation
spells out this step in `tendsto_continuumMean_sub_short` and
`tendsto_continuumMean_iff_short`, then applies the short producer.

Only after full assembly, the same equivalence proves
`shortContinuumMean_limit` for every fixed positive cutoff and
`tendsto_short_sub_short` for any two such cutoffs. These corollaries do not
upgrade the local Taylor radius or assert cutoff-uniform estimates.

### 3. Transfer expectations only after the deterministic result

Geometry has already proved measurability, boundedness and closed-interval
causal convexity for the actual region. At every positive density,
`expectedBDGAction_eq` therefore follows from the separately constructed
restricted Poisson law and the original finite-action expectation bridge.
Density is eventually positive along `atTop`; the expectation and
`continuumMean` functions are eventually equal. Applying that equality to the
**already proved unconditional deterministic limit** gives
`expectedBDGAction_limit`. No stochastic convergence or expectation identity
is inserted into geometric admissibility.

## Every #97 acceptance item

All four prerequisite packages are present in this assembly tree. The pinned
parent integration tip is `fc6b35ba824142e2b3c336cc528de97324b136a2`: it contains
#111's analytic backend (PR #104), #106's geometry (PR #110, synchronized by
`7e6cdacc4008fac72d925d6e93e3bd8fbb7d1724`), #108 / PR #112 (merge
`5332cae163b109e8f2014673048620f04a3c5ade`) and #107 / PR #113 (merge
`fc6b35ba824142e2b3c336cc528de97324b136a2`). The fetched `main` base
`82dfb8b246f0e9f1e76190c119b5337ca48f263d` is an ancestor. Separate predecessor
audits are not used as this tree's final validation receipt.

| #97 acceptance item | Integrated declarations and reproducible evidence |
| --- | --- |
| 1. Exactly E; region/strata/area/bridge; old inclusion and genuinely new examples | `AdmissibleIndependentTwoFace`, `AdmissibleTwoFace.toIndependentTwoFace`; `IndependentFaceGeometry`, `IndependentFaceAngle`, `IndependentFaceSurface`; `symmetricEllipsoid_independent`, `steepCapsule_admissible`, `steepCapsule_not_old_cap`, `steepCapsule_not_old_twoFace`; `IndependentFaceRegression.lean`. The regular-height API retains interior critical points. |
| 2. Actual local C³ overlap extension and two-jet; raw/envelope agreement first | `IndependentShortGerm`, `IndependentShortCollar`, `exists_absoluteOverlap_twoJet`, `exists_absoluteOverlap_remainder`; independently expanded primitive bounds in `IndependentShortRegression.lean`. No clipped envelope is differentiated across the joint. |
| 3. Actual fixed-cutoff long proof with independent margins and all contact/averaging obligations | `LongEnvelopeData`, `TwoFaceLongGeometry.Envelope`, `IndependentFaceLongNull`; actual-density right quadratic jet and `tendsto_normalized_longOverlap`; `IndependentFaceLongRegression.lean`, component hinge/averaged-jet regressions and the exact moving-contact regression in `test_independent_faces.py`. |
| 4. Absolute direct-origin short action with all signed modes, normalization and derivative-controlled remainder | `ShortRadialAbsolute`, `AbsoluteShortModel`, `exists_absoluteAngularExpansion`, `exists_shortOverlapDensity_decomposition`, `exists_shortContinuumMean_limit`; `AbsoluteShortRegression.lean`, `IndependentShortRegression.lean`, `test_absolute_short.py`. Constant/point, linear and both quadratic modes are retained; no invalid planar comparison or weighted-action shortcut. |
| 5. Divergence/intrinsic coefficient; one common cutoff; unconditional deterministic then expected limit | `spatial_divergence`, `absoluteShortCoefficient_identification`, `continuumMean_eq_short_sub_density`, `twoFaceLimit`, `expectedBDGAction_limit`, `independentTwoFaceLimitGoal`, `independentTwoFaceExpectedLimitGoal`; expanded full bilocal/action/law/target and common-cutoff contracts in `IndependentFaceLimitRegression.lean`. |
| 6. Old/new/variable-angle/critical-point regressions and full integrated validation | `IndependentFaceLimitRegression.lean` applies both full declarations to the steep critical capsule, the concrete variable-angle symmetric member, every old member, the original planar unequal-axis target and empty geometry with arbitrary exterior raw future data. `test_independent_assembly.py` integrates the full steep-capsule action and recombines actual short/long pieces. The validation receipt below covers the combined tree, separately from human review. |

This also covers #109's interface, common-cutoff, divergence, bridge and
regression acceptance items. Its validation and coverage-report obligations
are recorded below and in the [#90 ledger](../notes/general-contract.md).

## Reproducible calibrations

The Lean regression expands the full deterministic bilocal expression and the
expectation of all four signed discrete layers under the actual Poisson law.
It checks the independent Hausdorff/Lorentzian target, positive-density bridge
inputs, exact partition, cutoff equality, common-cutoff quantifiers, both new
full limits and unchanged old contracts. It is standalone, not dependent on
an unbuilt regression module's cached objects.

The new numerical diagnostic uses time/radius coordinates and the original
signed kernel with the exact capsule overlap; the latter is independently
checked against vertical interval intersections in `test_independent_faces`.
It does not substitute a Taylor polynomial, fit a limit, or use the false
same-height planar cap reduction. The target from normals and Lorentzian
sphere area is `25*pi/6`, approximately `13.089969389957`.

| Density | Full steep-capsule action | Action minus intrinsic target |
| --- | --- | --- |
| 100 | 10.293867433631 | -2.796101956326 |
| 1000 | 11.858131978558 | -1.231837411400 |
| 10000 | 12.583879754636 | -0.506089635322 |

At density 1000, the two fixed cutoffs 0.2 and 0.45 give different short and
long terms but the same full action within the regression tolerance. Dropping
long at finite density fails. Refinement and decreasing errors in this finite
sample are diagnostics, **not** certified error estimates or proofs of
convergence. The Lean theorem supplies the asymptotic claim.

```sh
.venv/bin/python -m unittest -v test_independent_assembly test_independent_faces test_absolute_short
(cd formal && lake env lean -DwarningAsError=true IndependentFaceLimitRegression.lean)
(cd formal && ./check.sh --incremental --base origin/main)
(cd formal && ./check.sh)
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

## Validation, review and integration status

The final integrated local `cd formal && ./check.sh` **passed** after the
last Lean-input change: library build, all 218 local Lean sources including
the aggregate audit, warnings as errors and transitive-axiom enforcement.
The aggregate checked 2,222 public theorems and all public definitions.
Default two workers; measured wall time **1:59:14**. All 222 validation-input
file hashes (sources, checker, dependency pins and build configuration) were
rechecked unchanged afterward; only documentation edits followed.

Focused compilation and expanded Lean regressions, the incremental gate
against `origin/main`, all **183 Python tests**, symbolic checks, exact
`RESULTS.md` reproduction, both site JavaScript syntax checks and
`git diff --check` passed. Markdown lint checked 43 documents with zero
problems; all 20 Markdown tests passed. No rendered equations changed:
new theorem contracts remain Lean code, so no browser math preview was
applicable. The assembly introduces no dependency, checker, original-contract
or action-definition change. Local service handoff and deployment were
skipped; no runtime operation or release/version change applies.

This assembly is a child of integration PR #104 and targets
`issue-97-direct-origin`, not `main`. A child PR or its non-default-branch merge
does not close #97 automatically. PR #104 remains the sole final main-target
closure vehicle. Its body must map the accepted packages and carry the intended
separate closing references, including #109 and #97, once integrated; it must
not become review-ready before final-base synchronization and the full gate
on the final combined Lean inputs. No merge is authorized by this work.

**Conventional argument:** the assembly above and the linked geometry, short,
long and analytic notes. **Machine verification:** only the recorded checked
inputs and validation receipt. **Independent human mathematical/physical
review:** still outstanding under #94/#86; neither Lean nor automated PR
feedback constitutes that review.

The compatible new coverage returned to #86 is a flat four-dimensional,
compact-closure global two-graph deterministic/expected theorem with independent
strict spacelike envelopes and the unchanged intrinsic positive-angle target.
It does not establish general non-two-graph atlases, extra strata, noncompact
tails, curved bulk/joint limits, other-dimensional global limits, arbitrary
null/mixed boundaries, small-angle uniformity, rates, variance or sample-wise
convergence. #86 remains open; no unrelated issue state or general completion
criterion changes. Issue #24's pre-existing GitHub state is not proof evidence.
