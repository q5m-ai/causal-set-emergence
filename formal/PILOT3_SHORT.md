# Actual short-action limit for the smooth 3D pilot

This implements #126's analytic producer for the unchanged `SmoothPilot3`.
The direct-origin argument in [the conventional #79 note](../notes/dimension-three-short.md)
is now connected to the actual overlap and short action in Lean. The original
region, dimension-indexed coefficients, action, intrinsic target and Poisson
law are unchanged. The canonical prerequisites remain documented in
[PILOT3_INTEGRATION.md](PILOT3_INTEGRATION.md).

**Scope:** every sufficiently small **fixed** positive cutoff has the short
limit. The long producer belongs to #125; final global deterministic assembly
and use of the separately proved expectation bridge belong to #80. This does
not close either global goal or assert sample-wise convergence. Independent
human mathematical review remains separate from compilation and numerical
checks. The subsequent [#80 assembly](PILOT3_LIMIT.md) now combines both
actual producers and proves the unchanged global deterministic and expected
goals; it does not expand this short package's own scope.

## Exact consumer contract

Import `BoundaryDraft.Pilot3ShortLimit`. Names below are in `BoundaryDraft`.

```lean
theorem SmoothPilot3.exists_shortAction_limit
    {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop
        (𝓝 (pilot3BoundaryIntegral h f))
```

The radius is produced from the actual geometric collar and Taylor bounds.
There is no jet, cancellation, response, remainder or desired-limit premise.
Choose the cutoff once, before density varies; no shrinking-cutoff interchange
or uniform limit over cutoffs is asserted.

The shared finite-density convention is:

```lean
def pilot3LongFuture (δ : ℝ) : Set Pilot3Spacetime :=
  {z | z ∈ dimensionCausalFuture 0 ∧ δ ≤ z.1 + ‖z.2‖}

def pilot3ShortFuture (δ : ℝ) : Set Pilot3Spacetime :=
  dimensionCausalFuture 0 \ pilot3LongFuture δ

def pilot3ShortAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
    dimensionPairCoefficient 3 * ρ * ∫ z in pilot3ShortFuture δ,
      pilot3DisplacementKernel ρ z * pilot3Overlap h f z)

def pilot3LongPairAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPairCoefficient 3 * ρ * ∫ z in pilot3LongFuture δ,
    pilot3DisplacementKernel ρ z * pilot3Overlap h f z)

theorem SmoothPilot3.action_eq_short_sub_long
    {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (ρ δ : ℝ) :
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f - pilot3LongPairAction ρ δ h f
```

`pilot3DisplacementKernel` is exactly `dimensionBilocalKernel 2` at `(0,z)`,
with the unchanged interval coefficient. The split holds at every real density
and cutoff. Cutoff equality, including null displacements, belongs to long.
The original point volume occurs **once**, in short. Every source component
and every future partner is retained.

## Proof and acceptance map

| Obligation | Checked producer |
| --- | --- |
| Actual overlap shear, signed integrability and exact action split | Canonical `Pilot3Displacement`; compatibility in `Pilot3ActionSplit` |
| Plane polar measure, full-circle mass and sharp proper-time transport | `Pilot3NullCoordinates`, `Pilot3ShortCoordinates`, `Pilot3ShortDensity` |
| Actual moving contact, finite collar sum and complete absolute origin two-jet | `Pilot3ShortCollar`, `Pilot3ShortJet` |
| Circle moments and intrinsic normal/Gram coefficient | `Pilot3CircleMoments`, `Pilot3Coefficient`, `Pilot3ShortAngular` |
| Exact sharp radial primitives and signed moment responses | `Pilot3ShortBasis`, `Pilot3ShortMoments`, `Pilot3ShortResponse` |
| Primitive derivative bounds and sufficient averaged nearly-null residual | `Pilot3CubicBounds`, `TruncatedAffineJet`, `Pilot3ShortRemainder` |
| Actual geometric polynomial and measurable remainder | `Pilot3ShortExpansion` |
| Actual density/action decomposition and unconditional fixed-cutoff limit | `Pilot3ShortAssembly`, `Pilot3ShortLimit` |

### Direct origin, not a planar comparison

`SmoothPilot3.exists_absoluteOverlap_twoJet` constructs a C³ extension on a
fixed causal ball, including the origin and null displacements. Its value is
the actual point volume. Its first derivative retains the moving time slice
and future-gradient bulk term. Its Hessian retains the actual future Hessian
and the canonical joint square divided by the height-gradient norm.
`absoluteShortPolynomial_eq_expanded` states this complete polynomial explicitly.

The collar weights localize the **source** in an exact finite sum. Their moving
representatives are differentiated inside the checked moving-root construction;
partition and canonical measure identities yield the whole overlap jet. No
partner is restricted to the source chart, and no componentwise bilocal-action
additivity is used. This delivery does not assert an externally weighted
short-action theorem or rely on a weighted tangent-wedge replacement.

### New three-dimensional responses

The spatial polar Jacobian is `r`, the full-circle mass is `2 * Real.pi`, and
`pilot3NullJacobian σ v = (1 - σ / v ^ 2) / 4`.
The short-order adapter `pilot3ShortNullJacobian v σ` is definitionally the same
canonical Jacobian, with its arguments reversed. The circle covariance is
`Real.pi` times the identity in two Euclidean coordinates. These facts are
proved for the actual polar measure, not imported four-dimensional constants.

The sharp fibres retain both endpoints. Their signed moments satisfy:

```lean
Pilot3ShortMoments.moment 0 = 0
Pilot3ShortMoments.moment 1 = 0
Pilot3ShortMoments.moment (1 / 2) = -1 / 12
Pilot3ShortMoments.moment (3 / 2) = Real.Gamma (5 / 3) / 4
```

`modelGerm_point_cancellation` proves exact cancellation of the physical point
term using the nonzero half-power moment and the actual point/pair coefficients.
The exact truncated model differs from this germ by a proved vanishing
normalized error; its finite-cutoff integral is not stipulated to equal its
limit. `Ftt_action_limit` gives `1 / Real.pi`, `Frr_action_limit` gives
`-2 / Real.pi`, and the time-linear mode has zero limiting response.

### Nearly-null remainder without a false quadratic claim

`exists_absoluteOverlap_remainder` supplies a globally measurable representative
with cubic value, quadratic first-derivative and linear second-derivative bounds
on a fixed ball. These are produced from the actual C³ extension, not geometric
admissibility fields.

At fixed positive long coordinate, the second proper-time derivative has bound
`T / v`, which is **not** integrable down to zero. `TruncatedAffineJet` instead
controls the truncated fibre's **affine** residual divided by `σ ^ (3 / 2)`
by `3 * T`, both before and after the moving fibre closes. Pointwise quadratic
control and dominated convergence on the finite circle/long-coordinate product
give the sufficient little-o of order three-halves. The two signed integer
moments cancel the affine jet before the remaining absolute estimate.

No pure quadratic bound for the averaged residual, omitted moving endpoint,
full-action convergence rate or density-dependent cutoff is used.

### Intrinsic target, including whole-region flux

`SmoothPilot3.shortCoefficient_identification` proves:

```lean
(pilot3ShortTimeCoefficient h - 2 * pilot3ShortSpaceCoefficient h f) / Real.pi =
  pilot3BoundaryIntegral h f
```

The time coefficient is `Real.pi` times the canonical reciprocal-slope integral.
The spatial coefficient is `Real.pi / 2` times the sum of the bulk Laplacian
and squared future-slope surface integral. Whole-region spatial divergence
supplies the true outward flux. `weight_mul_areaDensity` independently identifies
the normal-angle weight times the Lorentzian Gram density. Hausdorff **one**-measure
retains normalization **one**; the target is never defined through the action.

## Regressions and validation boundary

`Pilot3ShortLimitRegression.lean` independently expands the observable and
fixed target, checks cutoff equality and null points, signed response signs and
point cancellation, and instantiates the final theorem for:

- the curved ball/sine member and its retained positive-height critical point;
- the planar member, as a consequence rather than an analytic premise;
- the complete disconnected curved region;
- both annular boundary components and retained critical points;
- the empty member.

Existing geometry, dimensional, expectation-bridge and original 4D regressions
remain unchanged. The existing `test_dimension_short.py` and symbolic checks
are separate executable evidence, not substitutes for these Lean proofs.

Run the [required full local gate](README.md#reproduce) after the last Lean input
change. It audits every local source and every owned public declaration's
transitive axioms, then the aggregate library. Individual module builds,
incremental checks and GitHub's Python/Markdown CI do not replace it. The PR
validation receipt records the exact audited code commit and observed checks.

### Integration with merged #125

PR #128 landed first. The combined tree retains its `Pilot3Displacement` and
`Pilot3LongCoordinates` as the single canonical owners of the future domains,
short action, overlap integration, polar transport and circle measure.
`Pilot3ActionSplit` now imports those declarations and proves
`pilot3LongAction_eq_neg_pair`, preserving both public action-split contracts.
`Pilot3NullCoordinates` imports the canonical circle/Jacobian and supplies only
the short-order adapter and null-point geometry. No analytic coefficient or
observable changes under this consolidation.

`Pilot3ProducerIntegrationRegression.lean` imports both producers together,
checks the exact sign and Jacobian-order bridges, and proves that one fixed
positive cutoff satisfies both producer contracts, including the whole curved
annular member. It deliberately does not assemble a global or expected limit.
The original independent audit below is historical; the combined-tree audit
receipt is recorded separately on the PR after final validation.

### Original independent local receipt

The full gate passed on code commit
`509459bea9d2f7122609de1c2220d17d85f6bd11`, after the final Lean changes:

- Lean **4.19.0**, mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`;
- all **270** per-source checks, with warnings as errors and transitive-axiom checks;
- aggregate audit of **2,867** public theorems and all public definitions;
- only the permitted `propext`, `Classical.choice` and `Quot.sound` axioms;
- default two workers, elapsed **2:31:48**, exit status **0**.

The incremental check passed against the then-current `origin/main`, resolved
to `c74801692a65f58be3f8e3caf7e0ccf1824946a1`. Symbolic checks, **262** Python
unit tests, the **53**-document Markdown scan and **20** Markdown checker tests
also passed. This receipt is a documentation-only follow-up; it does not change
any Lean validation input or certify a future combination with #125.
