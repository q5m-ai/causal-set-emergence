# Ambient covariance and scaling of the BDG mean

Issue #50 supplies the ambient coordinate-transport part of the flat-space
program. `Poincare.lean` and `ActionTransport.lean` prove finite-density
identities for the **unchanged** four-dimensional `continuumMean`, and transfer
them to the independently defined `expectedBDGAction` through
[`ExpectationBridge`](EXPECTATION_BRIDGE.md). No action, kernel, probability
law, original region hypothesis, or base-case limit definition changes.

## Geometric input, not assumed transport

`PoincareEquiv` contains only:

- a real linear equivalence of the existing four spacetime coordinates;
- an arbitrary translation;
- preservation of the full `minkowskiInner` bilinear form, with signature
  `(+---)`; and
- strict positivity of the time coordinate of the image of `timeAxis 1`.

The last condition selects the future time orientation on **one** timelike
vector. It does not assume transport of every causal pair. There is no
hypothesis about a determinant, measure, integral, expectation, or limit.
In particular, spatial orientation reversal is permitted; restricting to
positive determinant would lose valid transformations.

`toHomeomorph` applies the linear map and then adds the translation. Its
inverse subtracts the translation before applying the inverse linear map.
The public `symm`, `symm_apply_apply`, and `apply_symm_apply` expose both
inverse identities. The inverse's time orientation follows from bilinear
preservation and symmetry, not from an extra orientation hypothesis.

### Derived geometry and volume

1. **Intervals.** Endpoint differences eliminate the translation. Bilinear
   preservation then proves `intervalSq_map` for every pair, including
   spacelike, null, and coincident endpoints.
2. **Time orientation.** The existing Cauchy–Schwarz theorem
   `time_nonneg_of_minkowskiInner_nonneg` from `TimelikeInterval` says that a
   causal vector with nonnegative Minkowski product with a future timelike
   vector is future directed. Apply it to the image of a future causal vector
   and the image of the unit time axis. Their product is the original time
   coordinate. Apply the same argument to the inverse to obtain
   `causalFuture_map` in both directions. Neither the null boundary nor the
   diagonal is removed.
3. **Determinant.** In the original coordinate basis, bilinear preservation
   gives the matrix identity `Lᵀ J L = J`, where `J` is the diagonal signature
   matrix. Taking determinants and using its nonzero determinant gives a
   squared determinant of one. `abs_det_linear` selects absolute value one,
   not determinant one.
4. **Lebesgue measure.** Mathlib's checked linear change-of-variables theorem
   for product Lebesgue measure uses that absolute determinant. Composing with
   translation gives `measurePreserving`; `volume_image` holds on every set.
   This uses the original coordinate product measure, not a Lorentzian norm
   or an ambient Euclidean surface measure.
5. **Regions.** The homeomorphism is a measurable equivalence. Continuity on
   the compact closure of a bounded spacetime set bounds its image. Causal
   interval containment transports through the proved causal equivalence.
   Thus `BoundedCausalRegion.poincare_image` preserves exactly the existing
   bounded, measurable, causally convex region class.

## Actual bilocal integral, before any boundary limit

The public deterministic contract is:

```lean
theorem PoincareEquiv.continuumMean_image (F : PoincareEquiv)
    (ρ : ℝ) (M : Set Spacetime) :
    continuumMean ρ (F '' M) = continuumMean ρ M
```

`image_future_inter` first transports the **whole** intersection of the region
with a causal future. `integral_image` then performs a signed set-integral
substitution through the measure-preserving equivalence. Unfolding the actual
`continuumMean`, apply it to the point term, the outer endpoint integral, and
the inner endpoint integral. The transported intersection is precisely the
original future slice. `intervalSq_map` leaves the kernel argument unchanged.
This proves equality at finite density without any asymptotic argument or
replacement of the action by a geometric target.

The measurable-equivalence substitution is valid even for the totalized
integrals on arbitrary sets, so the deterministic theorem is more general
than the physical region class. Its use on that class is **not** vacuous:
`integrableOn_bilocal_bdg` already gives compact domination of the actual
signed kernel on all bounded causal-pair domains.
`integrableOn_bdg_future_of_bounded` proves absolute integrability of every
inner slice; `integrableOn_bdg_outer` derives outer integrability from bilocal
domination and Fubini with the causal indicator retained. These apply on both
source and image regions. No sign assumption on `bdgKernel` is introduced.

## Positive dilation is a separate transformation

`dilateRegion s M` is explicitly the image under multiplication of **all four**
coordinates by the real scalar `s`. `dilateRegion_eq_smul` identifies it with
the pointwise set scalar action. For positive `s`, `dilationHomeomorph` has
inverse multiplication by the reciprocal, and `causalFuture_smul` proves
causal equivalence. `BoundedCausalRegion.dilate` preserves the same region class.

```lean
theorem continuumMean_dilate {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (M : Set Spacetime) :
    continuumMean ρ (dilateRegion s M) =
      s ^ 2 * continuumMean (ρ * s ^ 4) M
```

The proof tracks each independent factor:

- `intervalSq_smul` gives degree two for the squared interval, hence degree
  four for the interval-volume argument of `bdgKernel`.
- `volume_dilateRegion` and `integral_dilateRegion` give the fourth-power
  Jacobian of the original four-dimensional product measure.
- Substituting **both** endpoints in `bilocal_integral_dilate` gives the
  eighth-power Jacobian and changes the kernel density to `ρ * s ^ 4`.
- The point term has only one fourth-power factor. The square-root density
  normalization at the transformed density contributes a second-power
  factor. Factoring the unchanged action leaves precisely `s ^ 2` outside
  `continuumMean (ρ * s ^ 4) M`.

No boundary area scaling theorem is used to guess the factor. Empty and
nonempty zero-volume regions are permitted. Nonpositive dilation is not the
stated causal-orientation contract.

## Transfer to the existing Poisson expectation

At positive density, both transported regions meet the original exact bridge.
For dilation, the transformed density is also strictly positive. Rewriting
both expectations using `BoundedCausalRegion.expectedBDGAction_eq` gives:

```lean
theorem PoincareEquiv.expectedBDGAction_image (F : PoincareEquiv)
    {M : Set Spacetime} (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (F '' M) = expectedBDGAction ρ M

theorem expectedBDGAction_dilate {M : Set Spacetime}
    (hM : BoundedCausalRegion M) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) :
    expectedBDGAction ρ (dilateRegion s M) =
      s ^ 2 * expectedBDGAction (ρ * s ^ 4) M
```

There is no new Poisson-law pushforward construction or coupling. These are
identities of expectations, not sample-wise convergence statements.

## Independent regressions and scope

`ActionTransportRegression.lean` expands the original bilocal action and
probability integral. It checks:

- a rational boost with velocity three-fifths, both independently written
  inverse coordinate maps, and a nonzero translation;
- inverse membership in the boosted original ellipsoid with axes one, two,
  and three and height parameter one-quarter;
- finite-density deterministic and expected-action covariance, and recovery
  of the original deterministic `48 * Real.pi` limit;
- a spatial parity map constructed from `LorentzReflection`, with determinant
  **minus one**, the explicit coordinate reflection, and volume/action transport;
- closed null pairs, diagonal pairs, and absolute integrability;
- dilation by two: volume factor sixteen, action factor four, and density
  factor sixteen; reciprocal dilation, inverse coordinates, and set recovery;
- empty and nonempty zero-volume deterministic cases.

A boosted graph cap still has a planar future face. Its transported limit is
only a **covariance calibration**, not a new two-curved-face boundary theorem.
Generic induced spacelike joint measure, angle-weighted area, and their Lorentz
transport remain [work package C / #51](https://github.com/q5m-ai/causal-set-emergence/issues/51).
This ambient API does not close tracker #24, prove localization, supply rates
or variance, or establish convergence of individual sprinklings.

## Reproduction

The library root imports both modules. The existing full checker discovers the
independent regression and audits it even outside the library root:

```sh
cd formal
./check.sh
```

It checks every local source with warnings as errors, isolated transitive axiom
audits, and the aggregate public-library audit. Only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` are allowed. The pinned toolchain,
mathlib revision, existing regressions, and action definitions are unchanged.
