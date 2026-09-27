# Four-dimensional program: acceptance and proof-gap audit

This audit covers [tracker #1](https://github.com/q5m-ai/causal-set-emergence/issues/1)
and its separate [probability milestone #40](https://github.com/q5m-ai/causal-set-emergence/issues/40).
The mathematical implementation is merged through
[PR #47](https://github.com/q5m-ai/causal-set-emergence/pull/47), integration commit
[`4a51ce2`](https://github.com/q5m-ai/causal-set-emergence/commit/4a51ce2a8571f738bb14e391cf9d86b0d7f46550).
This post-merge documentation update records that implementation; it does not
assert that an unmerged documentation PR has already satisfied tracker closure.

## Acceptance evidence

| Requirement | Checked declaration or independent contract |
| --- | --- |
| Concrete ellipsoid and null-cap limits are proofs, not just proposition definitions | `ellipsoidLimitGoal` in `BoundaryDraft/EllipsoidLimit.lean`; `nullCapLimitGoal` in `BoundaryDraft/NullCapLimit.lean`; independent full statements in `EllipsoidRegression.lean` and `NullCapRegression.lean` |
| Original actions, targets, and geometric hypotheses retained | `Specification.lean` has only comment changes since its initial definitions; `GraphGeometry.lean` is unchanged since the general admissibility API; `GraphSurface.lean` has only comment changes since its canonical target was introduced |
| The actual signed kernel is verified | `kernelMassGoal`, `kernelTailGoal`, and `planeKernel_rescaling_limit`; the signed collar specialization retains the negative tail |
| General graph-cap boundary limit, without excluding interior critical points | `AdmissibleGraphCap.graphCapLimit`; `GraphLimitRegression.lean` and the quartic example in `GraphCapRegression.lean` |
| Actual finite Poisson probability and measurable count laws | `FinitePoisson.law`, its probability instance, subset and interval count laws, reduced one-/two-point Campbell–Mecke identities, support, simplicity, and factorial moments; `PoissonRegression.lean` |
| Genuine finite-order four-dimensional BDG action | `discreteBDGAction`, `discreteBDGAction_eq_finite_order`, measurability and integrability; independent signed-layer and normalization checks in `DiscreteBDGRegression.lean` |
| Exact normalized expectation, without defining either side from the other | `FiniteSprinkling.expectation_eq_continuumMean`; the probability, action, and both continuum integrals are expanded independently in `ExpectationRegression.lean` |
| Geometric and integrability obligations discharged | `BoundedCausalRegion.sprinkling`, `integrableOn_bilocal_bdg`, the derived discrete-action integrability theorem, `GraphCapData.boundedCausalRegion`, and `boundedCausalRegion_nullCap` |
| All three deterministic limits transferred to expectations | `AdmissibleGraphCap.expectedBDGAction_limit`, its angle form, `ellipsoid_expectedBDGAction_limit`, and `nullCap_expectedBDGAction_limit` in `BoundaryDraft/ExpectedLimits.lean` |
| No admissions, custom axioms, or hidden bridge premises | `check.sh` audits every source in isolation, then `Audit.lean` audits public library declarations transitively; only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The sprinkling and bounded-region structures assume geometry and measure inputs, not expectation identities |
| Accurate proof-status separation | [Main guide](README.md), [expectation API](EXPECTATION_BRIDGE.md), [root README](../README.md), and [proof notes](../notes/first-attempt.md) distinguish the deterministic results, the separately proved bridge, and unproved random convergence |
| Gaps recorded before repair and paper/formal changes landing together | The immutable history below identifies the prior obligations, alternative proofs, and joint implementation/documentation PRs |

The expected-action identity needs a measurable finite-volume causally convex
region and positive density. Boundedness suffices for the checked region
classes but is not an additional premise of the finite-volume bridge theorem.
The concrete limits keep `0 < a < T` for the null cap, and `0 < a` with
`2 * a < b i` for every ellipsoid axis. General graph caps keep the original
`AdmissibleGraphCap` API. No extra reduction, coarea, density-continuity,
normalization, expectation, or limit field was added to make a target true.

## Proof-gap history and disposition

This section is a retrospective **index of existing evidence**, not a
backdated gap report. Git ancestry establishes that the linked earlier
snapshots precede the respective completed proofs; the unmerged draft #29 is
identified separately by its earlier commit/PR chronology. Issue bodies can be
edited, so issue creation dates alone are not used to establish what was
recorded beforehand.

The [initial checked-layer record at `796a91d`](https://github.com/q5m-ai/causal-set-emergence/blob/796a91d0ae70d1cf629b5091f9aba858ea3b9466/formal/README.md#remaining-proof-graph)
already enumerated the missing kernel bounds, justified analytic interchanges,
causal geometry and measures, limit assembly, angle/coarea interpretation, and
separate probability bridge. It expressly distinguished algebra and proposition
definitions from proofs. None of these missing results was declared as an axiom.

### Analytic obligations and concrete limits

- **Differentiation, kernel normalization, and tails (#3/#4).** The initial
  record precedes the scaling/calculus implementation in
  [PR #2](https://github.com/q5m-ai/causal-set-emergence/pull/2).
  Its [checked-calculus snapshot](https://github.com/q5m-ai/causal-set-emergence/blob/2463a08b23129a00af5434699ea2ee0ac4a41fda/formal/README.md#remaining-proof-graph)
  still explicitly leaves the half-line bounds and concrete normalization open.
  [PR #5](https://github.com/q5m-ai/causal-set-emergence/pull/5), commit
  `1d77cf8`, proves them by exact Gaussian cancellation and domination instead
  of assuming differentiated asymptotic remainders. That same commit updates
  `notes/first-attempt.md` with the alternative proof. The sharper expansion
  and its differentiated remainder remain draft-level, not premises of the
  checked limit.
- **Series/integral interchange and exact graph-cap reduction (#6).** The
  earlier record distinguishes coefficient recurrences from justified analytic
  interchanges and future-slice geometry. [PR #7](https://github.com/q5m-ai/causal-set-emergence/pull/7),
  commit `9491dbc`, supplies an exact finite primitive, compact domination,
  coordinate/Fubini justification, and complete future slices. Its proof-note
  update explicitly records the replacement for the unformalized series
  argument; the original series argument is retained as draft provenance.
- **Whole-ellipsoid limit and critical height (#9).** The
  [post-reduction record](https://github.com/q5m-ai/causal-set-emergence/blob/9491dbccc1e3a1604202cc50e7bd60390b9a3af1/formal/README.md)
  leaves the volume/coarea limit unproved. [PR #10](https://github.com/q5m-ai/causal-set-emergence/pull/10),
  commit `34e1aa4`, proves the explicit signed height formula and uses a bounded
  continuous weight, not a globally differentiable square-root weight. The
  same commit records the argument in the proof notes, retaining the critical
  point and negative kernel tail under the original axis assumptions.
- **Null-cap interval, boundary, coordinate, and concentration steps (#11).**
  These were open in the initial record and in #11, rather than consequences
  asserted from algebra alone. [PR #14](https://github.com/q5m-ai/causal-set-emergence/pull/14)
  supplies the interval moments, finite cancellation, rest-frame transport,
  null-set replacement, logarithmic weight, and Gaussian concentration. Its
  final implementation commit `11b9046` updates the proof notes and exports
  the unchanged concrete target. It does not prove arbitrary null geometry or
  the draft error rate.
- **Positive angle and general admissibility (#15/#17).** The initial record
  explicitly says the squared angle relation is not the positive-branch
  geometric theorem. [PR #16](https://github.com/q5m-ai/causal-set-emergence/pull/16),
  commit `8802915`, proves that interpretation and updates the proof notes.
  Its documentation still leaves the general graph-cap program open.
  [PR #18](https://github.com/q5m-ai/causal-set-emergence/pull/18), commit
  `53a3955`, then supplies the general exact-reduction API and its accompanying
  note update. Boundary noncriticality does not exclude critical points
  everywhere; the nonquadratic regression retains an interior maximum.

### Surface normalization and the general collar argument

- **Euclidean area normalization and scalar-graph area (#19).** The
  [pre-normalization notes at `aee8224`](https://github.com/q5m-ai/causal-set-emergence/blob/aee8224b6448638c315ceaa6c42bf64ca2d42b82/notes/first-attempt.md)
  expressly leave the reverse planar inequality, variable-Jacobian area
  formula, and collar argument unproved. [PR #22](https://github.com/q5m-ai/causal-set-emergence/pull/22),
  commit `f5f46ae`, proves the missing isodiametric direction and updates those
  notes in the same commit. The area implementation `50d3def` and its
  accompanying paper/status update `4b024f9` land together in
  [PR #21](https://github.com/q5m-ai/causal-set-emergence/pull/21).
  They are separate commits in one PR, not a claim of simultaneous authorship.
- **Ellipsoid measure compatibility and collar obligations (#23/#30/#31).**
  The [prerequisite-layer notes at `4b024f9`](https://github.com/q5m-ai/causal-set-emergence/blob/4b024f9fe33974e221d900e610872050b90dc605/notes/first-attempt.md)
  explicitly leave canonical/parametric compatibility, coarea, density
  continuity, and `GraphCapLimitGoal` open. The scope split from #19 to #23
  preserves those obligations; it does not mark the general theorem proved.
  [PR #35](https://github.com/q5m-ai/causal-set-emergence/pull/35) (`64dab2a`)
  proves measure compatibility; [PR #36](https://github.com/q5m-ai/causal-set-emergence/pull/36)
  (`f6a74ec`) constructs the atlas and both local transports. Both include
  proof-note updates, without redefining the measures or admissibility.
- **Right continuity, not two-sided continuity (#34).** The
  [draft preparation at `74ed558`](https://github.com/q5m-ai/causal-set-emergence/blob/74ed558446d3db2bded011776db6a6427a07f9b5/formal/README.md)
  records that negative-height density is zero and that two-sided continuity
  would force a zero boundary integral. It explicitly leaves right continuity
  unproved. This precedes [PR #37](https://github.com/q5m-ai/causal-set-emergence/pull/37),
  commit `97b861b`, which proves the required one-sided statement and updates
  the proof notes together. This corrects the interpretation of continuity
  for the zero-extended density, not the existing boundary-limit target.
  The stronger draft collar regularity and rate are not silently certified.
- **Endpoint replacement, overlap-aware coarea, and final assembly (#33/#32).**
  The atlas record and draft preparation leave these steps explicit. The
  preparation retains zeros only inside the closed positive region; it does
  not assume unrelated exterior zeros are null. [PR #38](https://github.com/q5m-ai/causal-set-emergence/pull/38)
  (`2161545`, integrated with density regularity at `12afb3d`) proves coarea;
  [PR #39](https://github.com/q5m-ai/causal-set-emergence/pull/39) (`e18b349`)
  proves the general limit. Both include the corresponding proof-note updates.
  Draft PR #29 was not merged: only the relevant preparatory lemmas were reused,
  and its closing keyword was not used to close an incomplete parent.

### Probability bridge and this completion pass

The initial record already identifies the probability bridge as a separate
missing formalization. [Issues #41–#43](https://github.com/q5m-ai/causal-set-emergence/issues/40)
then split the finite law, discrete action, and expectation theorem explicitly.
[PR #44](https://github.com/q5m-ai/causal-set-emergence/pull/44),
[PR #46](https://github.com/q5m-ai/causal-set-emergence/pull/46), and
[PR #47](https://github.com/q5m-ai/causal-set-emergence/pull/47) each include an
API/proof-route document alongside their Lean implementation. Together they
prove the existing equation (2), not a corrected or redefined continuum action. The
parent's instructions deliberately deferred **main proof-status** updates
until those declarations merged; this pass performs that deferred update.

**Disposition of #1's gap-recording criterion:** the documented analytic gaps,
surface-normalization prerequisites, and one-sided-density clarification are
accounted for above, with prior records and joint paper/formal PRs. No outstanding
mathematical repair within the accepted restricted limits was found, and this
pass changes no mathematical statement, hypothesis, proof term, or numbered
equation. This is not a claim that the independent paper review, sharper rates,
or unrestricted conjectures are complete. Any newly discovered mathematical
gap must still be recorded before repair, with paper and formal changes landing
together; it must not be disguised as a status or formatting edit.

## Validation and closure gate

Use the pinned Lean 4.19.0 and mathlib v4.19.0 setup in the
[reproduction guide](README.md#reproduce), then run:

```sh
./formal/check.sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py > /tmp/causal-set-results.md
cmp RESULTS.md /tmp/causal-set-results.md
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
node --check site/home-3d.js
node --check site/order-fraction-worker.js
git diff --check
```

A fresh `formal/check.sh` run for this completion pass succeeded on all 88
local Lean sources: 87 isolated source checks/audits with warnings as errors,
then the aggregate `Audit.lean`. It audited 727 public library theorems and all
public definitions transitively, matching the merged #47 report. The Python,
symbolic, numerical reproduction, repository Markdown, JavaScript syntax, and
diff checks above also passed. The configured GitHub checks do **not** run
Lean; their success is separate from the local proof audit. Exact-head results for this documentation pass
belong in its PR validation record, not a prediction of future CI success.

Close #40 and then #1 only when this status update is merged, their current
bodies are reconciled with the merged declarations, the acceptance evidence
is linked, and validation is green. Do not close either merely because this
file exists on an open PR branch. No variance, concentration, convergence in
probability, almost-sure convergence, random-dynamics model, arbitrary-null
joint theorem, or unrestricted Conjecture 1′/Conjecture 2 result is part of this
closure. The larger programs remain in #24 and #26.
