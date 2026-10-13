# Full-partner thin flat-torus limit (#138)

## Exact scope and verification boundary

This port consumes the accepted written calculation in
[`notes/general-metric-atlas-gate.md`, section 4](../notes/general-metric-atlas-gate.md)
and the actual measured-order/Poisson foundation of #137 / PR #146.
It uses the existing `CompactTorus.Space L`, Euclidean lattice distance,
`slabVolume L T`, `measuredOrder L`, `MeasuredOrderBDG4.action`,
`MeasuredOrderBDG4.discreteAction`, and original `FinitePoisson.law`.
No existing observable, law, dependency, or admissibility API is changed.

The hypotheses are exactly a positive period and a fixed positive slab height
strictly less than half that period. The result is the compact cubic quotient
slab, not a bounded coordinate region, a spatial maximum-metric torus, or a
shrinking geometric domain. The actual action is not defined to be zero.
`ThinTorusRegression.finite_action_pos` proves it is strictly positive at
period one, height two fifths, and density one.

The source-level proofs and standalone regression compile with warnings as
errors. The exact combined-tree full-audit, CI, feedback and integration receipts
are maintained in [PR #166](https://github.com/q5m-ai/causal-set-emergence/pull/166);
a changed-source check alone is not full-audit acceptance.
Written analysis, compiled proofs, aggregate validation, and independent human
mathematical review are distinct. #94/#86 review obligations remain open.

## Checked declarations and acceptance map

Names in this table are in `BoundaryDraft.CompactTorus`, except where stated.

| Obligation | Checked producer |
|---|---|
| Actual compact slab, ambient causal convexity and interval containment | Existing `slabVolume_univ`, `interval_subset_slab`, `intervalVolume_ambient`; new `compact_closure` |
| Complete boundary, no chart-seam boundary or joint | `frontier_slab`, `compact_faces`, `joint_empty`, `joint_target_zero` |
| Flat metric and independent target | `locally_euclidean`, `chartMetric_quadratic`, `chartMetric_inverse`, `chartMetric_translation`, `face_graphs_smooth`, `face_spacelike`, `chartConnection_zero`, `chartCurvature_zero`, `scalarCurvature_zero`, `bulk_target_zero` |
| Unique causal lift, not same-chart labels | `exists_causal_lift`, `existsUnique_causal_lift`, `slab_time_gap` |
| Every point of the entire interval | `interval_image`, `interval_injective` |
| Geometric quotient volume transport | `cover_measurePreserving`, `spacetimeCover_measurePreserving`, `intervalVolume_lift`, `intervalVolume_thin` |
| Full spatial quotient and both endpoint times | `integral_spatial_causal`, `inner_integral`, `integral_time`, `pair_integral`, `pair_integral_radial` |
| Actual finite-density phase representation | `pair_integral_phase`, `phase_halfline`, `integrable_phaseAmplitude_mul` |
| Evaluated phase and retained logarithm | `phaseAmplitude_eq_log`, `phaseRemainder_eq_smooth` |
| Original signed moments and absolute prerequisites | Existing `NullTransverseCancellation`, `NullTransverseLogMoments`, `ShortRadialAbsolute`, `NullCubicRemainder`; explicit sign regressions in `ThinTorusRegression.lean` |
| Exact physical point cancellation | `integrable_phaseLog`, `phaseLog_response`, `phaseLog_point_cancellation` |
| Actual signed remainder, not a supplied jet | `integrable_phaseRemainder`, `phaseRemainder_exact`, `phaseRemainder_bound` |
| Any fixed positive-phase complement | `phaseAmplitude_bound`, `fixed_phase_complement` |
| Canonical deterministic action | `action_eq_planeKernel`, `action_limit` |
| Separate canonical expected action | `expectedAction_limit`, using the existing positive-density `expectation_eq` |
| Both unconditional proof terms | `BoundaryDraft.thinFlatTorusLimit4` |

The geometry module performs an explicit covering-coordinate calculation of the
constant Lorentz metric, its inverse, Levi-Civita coefficients, curvature and
scalar contraction. Small covering neighborhoods have the actual quotient
Euclidean distance, and translations preserve the metric. The scalar descends
independently of representative choice, including seams. This is a concrete
flat coordinate calculation, **not** a new general manifold curvature API or a
curved-limit theorem. Constant-time face graphs are smooth and their nonzero
spatial tangent vectors are strictly spacelike. Their disjointness makes the
joint contribution zero for any measure and weight, without a zero-angle limit.

## Why no partner, logarithm, or normalization disappears

`coverCube` is only a measure-transport domain. It never replaces the quotient
region in the observable. The causal ball around each source is transported
using its own lift, so targets crossing any fixed representative seam remain.
Thinness makes the *whole* lifted causal interval injective. The interval volume
is obtained from that image and the actual geometric quotient measure; removed
endpoints are null. Null and diagonal pairs are included in the volume theorem.

The pair reduction is a finite-density identity for every real density.
The spatial factor is the full quotient volume. The weighted time integral
contains `T - τ`, produced from both endpoint times, not from a single selected
endpoint. Compact continuous domination precedes signed integration changes.
Radial substitution and rectangular Fubini give the actual `phaseAmplitude`.
Its primitive is differentiated and evaluated to derive `phaseSmooth` plus
`(Real.pi * T / 2) * (w * Real.log w)`. No logarithmic coefficient is assumed.

The previously checked signed logarithmic moment has positive value `1 / 12`.
After the geometric phase scaling, `phaseLog_response` is exactly `T / ρ`.
Thus the physical point term is allocated once and cancels exactly, including
all factors of the spatial volume, density, and four-dimensional prefactor.

### Remainder method: a stronger finite-primitive identity

This implementation does **not** accept a target-valued quadratic jet as an
input. Rather than re-proving Taylor remainder estimates for this explicitly
integrable example, it proves the exact finite-density identity
`action_eq_planeKernel` from the actual quotient action. Independently checked
radial primitives and the existing `GraphTail.abs_planeKernel_density_le` then
control the whole signed remainder after subtracting the derived logarithm.

In particular, `phaseRemainder` is the actual compactly supported amplitude
minus the full logarithmic model on the positive half-line. It includes the
subtracted logarithmic tail, not just a near-origin Taylor error. The identity
`phaseRemainder_exact` precedes the limit and contains no limit hypothesis.
Its bound tends to zero. Separately, boundedness of the actual amplitude gives
an absolute cubic majorant on every *fixed* positive-phase complement;
`fixed_phase_complement` applies the existing absolute cubic-kernel theorem.
There is no density-dependent cutoff and no omitted complement.

The deterministic theorem is proved first. Only afterwards does eventual
positive density permit the original Poisson expectation equality. The result
is convergence of expectations, **not** convergence of random actions on
individual samples.

## Standalone regression coverage

`ThinTorusRegression.lean` expands the actual action, both endpoint measures,
restricted interval volume and original Poisson law without a goal-only alias.
It also checks:

- a nonempty slab of mass two fifths and a strictly positive canonical action
  at density one;
- a causal seam-crossing pair whose raw representatives fail the coordinate
  causal inequality, together with its exact nonzero interval volume;
- the full finite-density radial/phase identities and unchanged prefactor;
- all three zero polynomial moments, the positive logarithmic moment and exact
  physical point cancellation;
- a duplicated smooth constant partition with four ordered pair terms: each
  off-diagonal term is strictly positive at density one, all four reassemble the
  actual pair integral, and the point weights sum to one;
- unchanged coordinate discrete-action compatibility and both original
  two-face limit contracts.

The existing written/numerical regressions additionally retain the nonconstant
periodic partition and same-chart-dropping diagnostics. They are diagnostics,
not a substitute for the checked quotient integration theorem.

## Validation and integration receipts

- Intended integration branch: `issue-81-general-coverage`, never `main`.
- Original pinned ancestor: `76a8dd1c2330ea2207169a203fe3b7f5eaa2c36d`.
- Interval-lifting/volume checkpoint: `577ce2f` (incremental source/axiom audit
  passed; not a full-audit receipt).
- Complete new-source/axiom incremental check against that same pinned ancestor
  passed after the last Lean change; proof checkpoint `4748ec7`.
- PR #164 integration `a1e1f34b648dac06e8fa94488a50d6d55f20d3e8` is incorporated
  by merge `8a9e818`. PR #165 integration
  `63a2f21ff4e98b83985579fc9e69254c76fb2c94` is incorporated by `1b5fc62` before
  the final combined-tree audit. Neither upstream integration changes Lean inputs.
- [PR #166](https://github.com/q5m-ai/causal-set-emergence/pull/166) records the
  full local source/warnings/transitive-axiom and aggregate audit, final
  Python/Markdown checks, exact-head CI, bounded feedback and merge receipts.
  Read the reported result and exact commit there, not an upstream run, when
  assessing integration acceptance.

The final full local `formal/check.sh` must follow the last Lean-affecting
change on the combined integration tree. Documentation-only receipt updates do
not change Lean inputs. Completion of #138 does not complete #81/#24, reopen or
close its prerequisite issues, or absorb #151's distinct curved-coverage work.
Thick slabs, lattice cut transitions, focusing, curved atlases, general topology,
all-dimensional coverage, statistical variance and sample-wise convergence are
outside this theorem. No broader rate or shrinking-cutoff-uniformity claim is
made here.
