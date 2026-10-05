# Smooth flat 2D integration: exact checked boundary (#131)

**Partial formal delivery, conventional global theorem.**
[The proof note](../notes/two-d-limit.md) derives the full deterministic limit
and only then transfers expectation. New Lean modules check finite geometry
and finite-density inputs, **not** that global limit. Endpoint counting,
`expectedAction_eq`, and `twoDExpectedGoal_iff` are not substitutes for the
missing deterministic theorem. Independent human mathematical review remains
outstanding.

## Integration and ownership

- PR base: `issue-81-general-coverage`, deliberately not main.
- Pinned starting SHA: `d41a062aba04552f1db42e9f3d59cb242ec6ed09`.
  The remote integration branch existed when rechecked and was preserved.
- Task branch: `issue-131-smooth-flat-2d`.
- Early [ownership/API announcement](https://github.com/q5m-ai/causal-set-emergence/issues/131#issuecomment-5995122426).
  This task owns new `TwoD*` production definitions. No shared definition or
  old theorem contract was changed; the library root has two additive imports.
- References only: #131. No merge, deployment, agent launch or issue closure;
  in particular #81/#24 remain open.

## Consumer signatures and what is actually proved

All declarations are in namespace `BoundaryDraft`. Physical dimension two
means `DimensionSpacetime 1`; it is not `DimensionSpacetime 2`.

```lean
SmoothTwoD (h f : DimensionSpatial 1 → ℝ) : Prop
twoDRegion (h f : DimensionSpatial 1 → ℝ) : Set (DimensionSpacetime 1)
twoDAction (ρ : ℝ) (h f : DimensionSpatial 1 → ℝ) : ℝ
twoDBoundaryIntegral (h f : DimensionSpatial 1 → ℝ) : ℝ
twoDOverlap (h f : DimensionSpatial 1 → ℝ) (t : ℝ)
  (r : DimensionSpatial 1) : ℝ
TwoDDeterministicGoal : Prop
TwoDExpectedGoal : Prop
```

The last two are **open propositions**, not theorems. The exact geometry is
#92's smooth combined-budget candidate, including empty and nonempty members;
it neither restricts to one connected component nor excludes interior critical
points. The action is the existing unsmeared dimension-indexed action. Normals
are actual Riesz gradients with future unit normalization. The target uses
`dimensionTwoJointMeasure`, defined before any asymptotic coefficient.

| Module | Checked result | Explicitly not supplied |
| --- | --- | --- |
| `TwoDContract.lean` | Independent geometric contract, whole region, normal/angle, unit-counting target, actual action, separate open goals | An asymptotic premise or a proof of either goal |
| `TwoDGeometry.lean` | Open bounded measurable region; closed ambient interval containment; actual #91 interval rate; all-endpoint finiteness, counting normalization and integral; signed pair integrability; #77 finite-density expectation; conditional transfer | Full face/frontier decomposition, global density transport, an action limit |
| `TwoDMetric.lean` | Strict face slopes from the combined budget; actual future unit normals and tangent orthogonality; positive angle; target equals the all-endpoint coth sum | Identification with a short-action coefficient |
| `TwoDExamples.lean` | Nonempty sine-future and planar interval members, curvature, retained positive-height critical point, empty member | Formal disconnected examples or any example action limit |
| `TwoDOverlap.lean` | Actual whole-region overlap definition, complete causal time-fibre identity and exact dimension-two kernel polynomial | Integrated null-coordinate transport, a supplied jet, or a short/long limit |
| `TwoDRegression.lean` | Expanded closed interval, counting, law/action normalization and target contracts; planar/curved/empty/critical controls and diagonal fibre | An unconditional deterministic/expected proof term |

Key theorem consumers are:

```lean
SmoothTwoD.boundedCausalRegion
SmoothTwoD.restricted_interval
SmoothTwoD.jointMeasure_eq_count
SmoothTwoD.boundaryIntegral_eq_coth_sum
SmoothTwoD.causal_time_fibre
SmoothTwoD.expectedAction_eq
twoDExpectedGoal_iff
```

No original 3D/4D source or hypothesis is changed. Reuse of `JointMetric` is
only its scalar positive-rapidity algebra; no 4D moment or surface area is
extrapolated to 2D. `DimensionTwoEndpoints` is reused unchanged.

## Acceptance map and bounded remaining work

| #131 acceptance item | Delivery and remaining condition |
| --- | --- |
| Freeze nonempty smooth bounded regular class, independent region/action/normal target, closed intervals and canonical counting | Checked new modules above; complete frontier/face description is conventional via #92, not newly checked here |
| Derive actual 2D short responses and long signed disintegration/cancellation, including constant/log sectors | Conventional proof §§2–5, exact symbolic and actual-overlap diagnostics; the full Lean producers remain #141/#142 |
| Global deterministic limit before expectation transfer, compatible cutoffs/point allocation | Conventional theorem §§3–6; only finite-density equality and conditional transfer are checked in this PR. Both Lean goals stay open |
| Nonplanar, planar, disconnected/all endpoints, critical points, unchanged baselines | Curved, planar, empty and retained-critical controls checked as above; all four disconnected endpoints, density jets, signed action and refinement in Python. Formal disconnected/global limit regressions remain prerequisites; old 3D/4D regressions stay in the full source audit |
| Conventional proof and explicit checked boundary; bounded missing producers; residual coverage | Proof note, this ledger, native children #141/#142; no general atlas/metric/null claims or independent human-review claim |

The native prerequisites are:

1. [#141: actual smooth 2D overlap and fixed-cutoff density expansions](https://github.com/q5m-ai/causal-set-emergence/issues/141).
   Owns integrated all-partner transport, finite moving endpoints, actual short
   two-jet/derivative remainder, normal-to-coefficient identity and contact-uniform
   long first-order regularity. Proposed modules: `TwoDCoordinates.lean`,
   `TwoDShortJet.lean`, `TwoDDensity.lean`.
2. [#142: signed logarithmic responses and global assembly](https://github.com/q5m-ai/causal-set-emergence/issues/142),
   blocked by #141. Owns the actual 2D log moments, fixed-cutoff remainder
   transfers, unconditional deterministic theorem and subsequent #77 expectation
   corollary. Proposed modules: `TwoDResponses.lean`, `TwoDLimit.lean`,
   `TwoDLimitRegression.lean`.

Both are native children/blockers of #131, not closure claims. #81/#24 still
own non-global-graph/atlas, general-metric, wider null/mixed and unsupported
dimension coverage. No rate, shrinking-cutoff uniformity or sample-wise
convergence is required or inferred.

## Validation receipt

**Audited Lean-input commit:** `508a48acacb3d5d69af2182e78d1ff45f00d840d`.
The required **full local audit passed**, from 2026-10-05 13:41:25Z to
16:18:09Z: all 286 per-source checks plus the aggregate audit of 2,987 public
theorems and all public definitions. Warnings were errors; only `propext`,
`Classical.choice` and `Quot.sound` were allowed transitively.

It started at the commit above and finished at documentation/Python head
`e130c385606c6ef96e60693b94c22ec962019298`. A complete post-audit manifest
regeneration was **byte-identical** to the pre-audit inventory. No Lean,
checker, dependency or build input changed, so later receipt/documentation
commits do not require a duplicate audit. See the [machine-readable receipt](receipts/issue-131-validation.json)
and [complete compressed audit log](receipts/issue-131-full-audit.log.gz).

- Module builds of all new production modules and warnings-as-errors check
  of `TwoDRegression.lean`: passed.
- `formal/check.sh --incremental --base d41a062aba04552f1db42e9f3d59cb242ec6ed09`:
  passed; the pinned base is an ancestor. This changed-source developer check,
  including the initial local library build, took 14:22.79; it is **not** the
  full source/aggregate audit.
- Full gate: `cd formal && LEAN_NUM_THREADS=2 ./check.sh`, default two source
  workers, exit 0 in **2:36:43**. Peak single-process RSS was 2,976,860 KiB
  (not total concurrent RSS). Before starting, available memory was 7.4 GiB
  and unused swap approximately 3.3 GiB. Worker count was not increased.
  Uncompressed audit-log SHA-256:
  `79ae1d143171e18d1eb7e5dfd55c357de47b849b19581c9c578479750df94376`.
- Lean 4.19.0 (`6caaee842e94`), pinned mathlib
  `c44e0c8ee63ca166450922a373c7409c5d26b00b`; dependency sources are clean.
- [Complete SHA-256 input inventory](receipts/issue-131-inputs.json.gz):
  32,449 files, including all 287 local Lean sources, the checker, Lake config,
  manifest/toolchain selector, every tracked dependency source, consumed
  dependency/local build products and the entire selected toolchain. This is
  a conservative superset of consumed inputs. Paths are checkout-relative;
  each dependency's exact Git revision is also recorded. Compressed SHA-256:
  `d7b89a20d0d500baac89424583936b753fbc949e945ebff7d747367e6e42afa5`.
  Uncompressed JSON SHA-256:
  `4bb93451a9b4573d4d8f60e9357edfc1708c99d4bec8958e1e3c4fa29cba5a82`.
- Final full Python suite: **289 tests passed**, 580.648 s; all 13 new 2D
  tests included. Existing symbolic checks passed. Markdown lint: 59 documents,
  no problems; 20 Markdown tests passed.
- Live GitHub math preview at `e130c385606c6ef96e60693b94c22ec962019298`:
  all **19** proof-note equations produced MathML, no rendering errors, no
  overflow, with visual checks of complete expressions and layout. The local
  browser needed its missing math fonts supplied through scoped Fontconfig;
  successful MathML alone was not treated as a successful visual preview.
- All three applicable CI checks passed at that implementation head;
  production-only jobs skipped as configured. The final PR body records the
  subsequent receipt-only head's observed checks and bounded feedback snapshot.

The manifest records content hashes, not timestamps or a claim of human
mathematical review. Its generated artifacts are diagnostic receipts, not
new build inputs. GitHub CI does not run or replace the required local Lean
audit. The final PR receipt must record its exact observed head/check state.
