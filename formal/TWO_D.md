# Smooth flat 2D: unconditional deterministic and expected limits (#131)

**Implementation complete; final integrated validation pending.** The unchanged
`TwoDDeterministicGoal` and `TwoDExpectedGoal` now have compiled proof terms in
[`TwoDLimit.lean`](BoundaryDraft/TwoDLimit.lean). The deterministic theorem is
proved first from actual short and long producers; only afterward is the
separately proved Poisson-expectation bridge used. Counting, finite-density
expectation, and `twoDExpectedGoal_iff` are not substituted for either limit.
The [conventional proof](../notes/two-d-limit.md) and the Lean implementation
are distinct evidence. Independent human mathematical review remains outstanding.

## Integration and unchanged contracts

- PR [#145](https://github.com/q5m-ai/causal-set-emergence/pull/145) targets
  `issue-81-general-coverage`, deliberately not main.
- Original pinned ancestor: `d41a062aba04552f1db42e9f3d59cb242ec6ed09`.
  Integrated general-coverage ancestor: `df7ef277ae8dc695396e359780ffd7be65b43e9a`,
  merged at `a70a131` with its sibling dimension-five/six, metric-atlas and
  two-tip-null work preserved.
- Task branch: `issue-131-smooth-flat-2d`. The
  [early ownership/API announcement](https://github.com/q5m-ai/causal-set-emergence/issues/131#issuecomment-5995122426)
  remains applicable: new 2D production names are task-owned; shared 3D/4D
  definitions and contracts are unchanged. Root imports are additive.
- `SmoothTwoD`, `twoDRegion`, `twoDAction`, `twoDOverlap` and
  `twoDBoundaryIntegral` are unchanged. Roots, integrability, density jets,
  coefficients and remainders are conclusions, not new admissibility fields.
- References only: #131, with producer work for #141/#142 included in this PR.
  No merge, deployment, agent launch or issue closure is authorized or performed.

All declarations below are in namespace `BoundaryDraft`. Physical dimension
**two** means `DimensionSpacetime 1`, with a genuinely one-dimensional spatial
measure and exactly two angular atoms of unit mass.

```lean
SmoothTwoD (h f : DimensionSpatial 1 → ℝ) : Prop
twoDRegion (h f : DimensionSpatial 1 → ℝ) : Set (DimensionSpacetime 1)
twoDAction (ρ : ℝ) (h f : DimensionSpatial 1 → ℝ) : ℝ
twoDBoundaryIntegral (h f : DimensionSpatial 1 → ℝ) : ℝ
twoDOverlap (h f : DimensionSpatial 1 → ℝ) (t : ℝ)
  (r : DimensionSpatial 1) : ℝ
TwoDDeterministicGoal : Prop
TwoDExpectedGoal : Prop
twoDDeterministicGoal : TwoDDeterministicGoal
twoDExpectedGoal : TwoDExpectedGoal
```

The class is exactly #92's smooth combined-budget candidate, including empty
members, disconnected positive regions and positive-height critical points.
The unsmeared action retains every causal partner. The target was independently
defined from actual future unit normals and `dimensionTwoJointMeasure`, not
from the asymptotic coefficient subsequently identified with it.

## Actual-density producer map (#141)

| Obligation | Produced declarations and source |
| --- | --- |
| Whole region, all strata and actual interval law | `SmoothTwoD.boundedCausalRegion`, `.restricted_interval` (`TwoDGeometry`); `.frontier_region`, `.past_inter_future` (`TwoDClosure`) |
| Canonical actual overlap and signed translation/Fubini | `.displacementOverlap_eq_actual` at every displacement; `.overlap_eq_gap` on the entire causal cone (`TwoDCausalOverlap`); `.integral_causalPair_eq_overlap` (`TwoDDisplacement`) |
| Genuine 2D measure and exact point-once split | `twoDLine`, `twoDDirectionMeasure_eq_dirac`, `twoDNullJacobian`; `.action_eq_short_add_long`, `integral_twoDShortOverlap`, `.integral_longOverlap` (`TwoDLine`, `TwoDCoordinates`, `TwoDShortDensity`, `TwoDLongFibre`) |
| Complete finite interval and endpoint geometry | `.exists_intervalFamily`, `TwoDIntervalFamily` (`TwoDComponents`); no bilocal additivity follows or is assumed |
| Actual moving roots and physical endpoint corrections | `.exists_movingEndpoint_twoJet` (`TwoDMovingEndpoint`); `.exists_endpointCollar` (`TwoDEndpointCollar`); `.integral_positiveCollar` for arbitrary observables with unit Jacobian (`TwoDCollarMeasure`) |
| All collars, bulk and absolute overlap two-jet | `.exists_shortCollar_twoJet`, `.shortBulk_twoJet`, `.exists_absoluteOverlap_twoJet` (`TwoDShortCollar`, `TwoDShortBulk`, `TwoDShortJet`); a compact-complement positive-height margin retains every interior critical point |
| Uniform derivative-controlled remainder | `.exists_absoluteOverlap_remainder` and `TwoDShortRemainder.CubicBounds` (`TwoDShortExpansion`, `TwoDCubicBounds`): one measurable remainder, one fixed positive radius, cubic value / quadratic first-derivative / linear second-derivative bounds |
| Independent normal target equals the coefficient | `.weight_eq_scalar`, `.boundaryIntegral_eq_scalar_sum` (`TwoDEndpointCoefficient`); `.integral_futureHessian_eq_endpoints` on all positive intervals (`TwoDDivergence`); `.short_coefficients_eq_boundaryIntegral` (`TwoDDivergence`) and `.integral_directions_absoluteShortPolynomial` (`TwoDShortAngular`) |
| Contact-uniform fixed-cutoff long jet | `.longDensity_right_quadratic_jet`, `.longDensity_linear_quadratic_bound`, `.longDensity_right_linear_jet` (`TwoDLongJet`), from the actual complete fibres, compact positive endpoint tubes and dominated averaging |
| Actual positive-sigma fibres and logarithmic short jet | `.shortDensity_eq_interval` (`TwoDShortFibre`); `.shortPolynomialDensity_eq` (`TwoDShortBasis`); `.shortDensity_eq_polynomial_add_remainder`, `.shortDensity_logarithmic_jet` (`TwoDShortDensityJet`) |
| Closing-fibre remainder density | `TruncatedLinearJet`; `TwoDShortRemainder.CubicBounds.density_right_affine_jet` (`TwoDRemainderDensity`), using the compensated second-derivative domination, not an integrable inverse-square bound by itself |

The auxiliary displacement notation is explicitly linked to the canonical
`twoDOverlap`. Complete causal-ball overlap equalities include null displacements
and the vertex. Null sets are removed only for integral transport. The original
short density is initially finite **almost everywhere**, and its fibres are
then proved absolutely integrable at **every positive** proper-time square.
There is no claim that the original zero-proper-time fibre is finite. The
remainder density has its own genuinely finite zero fibre.

The exact short primitive retains both logarithmic sectors: volume times
`-(1 / 2) * log σ`, and the independent endpoint integral times
`-(1 / 8) * σ * log σ`. Constant, linear and quadratic terms are retained too;
the apparent square-root sectors cancel in the exact primitive. The actual
remainder has a derived affine right jet with error `o(σ)`. Both directions,
all endpoint terms and all cutoff contacts are included.

## Signed responses and unconditional assembly (#142)

| Obligation | Checked implementation |
| --- | --- |
| Ordinary signed cancellation in physical dimension two | `twoD_affine_cancellation`; `TwoDLogMoments.scaled_power_zero` for powers zero and one |
| Absolute integrability before signed logarithmic integration | `TwoDLogMoments.integrable_log`, `.integral_log_zero`, `.integral_log_one` (`TwoDLogMoments`), with explicit vanishing integration-by-parts endpoint products |
| Positive scaling of both logarithmic sectors | `.scaled_log_zero = -1 / (2 * k)` and `.scaled_log_one = 1 / (2 * k^2)` (`TwoDLogScaling`); zero ordinary moments remove the logarithm of the scale |
| Fixed-threshold exponential tails | `TwoDExponentialTail.moment_tail`, `.logarithmic_tail` and their scaled forms, for the original kernel; absolute values bound only the tail, never replace the complete signed response |
| Short remainder and complete long response vanish | `TwoDShortRemainder.CubicBounds.normalized_density_limit`; `SmoothTwoD.tendsto_longDensity`, `.tendsto_longAction` (`TwoDCancellation`), the latter at every fixed positive cutoff |
| Sharp model with the unchanged point/pair/interval constants | `TwoDShortResponse.low_action_eq`, `.model_error_bound`, `.tendsto_modelAction`; `TwoDQuadraticResponse.limit_of_bound` controls the fixed-cutoff quadratic error |
| Model is the original short action, not an assumed density | `SmoothTwoD.exists_shortDensity_model`, `.exists_shortAction_limit` (`TwoDShortAssembly`) |
| Unconditional deterministic limit | `SmoothTwoD.tendsto_action` and `twoDDeterministicGoal` (`TwoDLimit`) |
| Subsequent independent expectation transfer | `SmoothTwoD.tendsto_expectedAction` and `twoDExpectedGoal`, through `.expectedAction_eq` and eventual positive density (`TwoDLimit`) |

The final action proof uses one produced fixed positive cutoff for both sides
of the exact split. The short logarithmic volume response cancels the point
term exactly; the endpoint response has unit physical normalization. Cutoff
equality belongs to long. The sharp-model tail can be controlled by a global
quadratic comparison, so the assembly does not need to assert a full-action
exponential estimate or a second cutoff limit. The separate exponential-tail
lemmas concern kernel moments only.

## #131 acceptance and regressions

| #131 acceptance | Evidence |
| --- | --- |
| Nonempty smooth bounded class; independent region/action/normal target; complete closed intervals and counting | Unchanged contract, `TwoDGeometry`, `TwoDMetric`, complete frontier/face geometry and `DimensionTwoEndpoints` normalization |
| Actual 2D short/long analysis, including constant/log sectors | Full producer and signed-response maps above; no higher-dimensional angular or kernel normalization is relabelled |
| Deterministic theorem before expectation; common cutoff and point allocation | Both unconditional terms in `TwoDLimit`; `TwoDLimitRegression` expands the full causal-pair action, physical discrete layers, independent Poisson law and normal/Hausdorff target |
| Curved, planar, disconnected/all endpoints, interior critical points and old baselines | `TwoDExamples`, `TwoDDisconnected`, all three standalone 2D regressions; existing 3D/4D source regressions remain in the integrated audit |
| Conventional proof and exact verification boundary; bounded producer ownership | Proof note and this ledger; #141/#142 implementations included, historical validation kept distinct, independent human review not claimed |

`TwoDDisconnected.lean` proves admissibility for two separated shifted interval
heights with the same genuinely curved sine future. Its complete joint is at
line coordinates **minus one, one, three, five**. The arbitrary-observable
endpoint integral sums all four points with unit mass; both positive-height
critical points, at zero and four, remain present. These are actual full-action
and subsequent expected-action examples, not componentwise sums of actions.
The Python disconnected quartic fixture is a separate diagnostic example.

`TwoDLimitRegression.lean` also checks planar, curved and empty full limits,
the supplied density jet, both signed logarithmic moments, fixed-cutoff long
cancellation, exact compatible action splitting and cutoff equality, null
partners, probability/integrability and the expanded physical law/target.
`TwoDRegression.lean` and `TwoDTransportRegression.lean` preserve the finite
geometry, normalization, transport, jet and coefficient consumers.

## Validation boundary and receipts

**Frozen Lean-input commit:** `8d2fe21b846d01673f2edd0f0c1cff7b62edc226`.
All new production modules and the library root build; all three 2D standalone
regressions have passed warnings-as-errors module checks. A fresh ancestor-pinned
incremental check and the one final integrated `formal/check.sh` are pending.
The PR stays draft until the final local gate and current-head CI succeed.

The older [foundation receipt](receipts/issue-131-validation.json),
[input inventory](receipts/issue-131-inputs.json.gz) and
[audit log](receipts/issue-131-full-audit.log.gz) are retained as **historical**
evidence only. That audit checked input commit `508a48acacb3d5d69af2182e78d1ff45f00d840d`,
286 per-source checks and 2,987 public theorems plus all public definitions.
It did **not** cover the density/response/limit continuation or the subsequently
integrated sibling work. Its 32,449-file inventory and earlier green CI are
not current-head completion evidence.

The final receipt must record the exact integrated input commit, all input
hashes, complete audit log, exit status, current Python/symbolic/Markdown
checks and current-head CI. Documentation-only follow-ups do not require a
repeat Lean audit if the validation-input inventory remains byte-identical.
CI does not replace the local source and transitive-axiom audit.

## Remaining scope

This is a fixed-geometry, smooth combined-budget **flat global-graph 2D**
theorem. It does not prove a rate for the complete action, shrinking-cutoff
uniformity, finite-regularity relaxation, degenerating-angle control, variance,
concentration or convergence of an individual sprinkling. General atlas,
non-global-graph, metric and wider null/mixed coverage remain under #81/#24;
neither tracker is closed by this bounded result. Compiler checking, symbolic
or numerical diagnostics and independent human mathematical review remain
separate claims.
