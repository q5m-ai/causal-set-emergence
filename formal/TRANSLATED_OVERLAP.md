# Exact translated-overlap reduction (#52)

**Status:** checked deterministic finite-density identities for bounded
measurable regions. The existing action, signed kernel, geometric hypotheses,
and exact base-case reductions are unchanged. This is not a localization,
Taylor-regularity, or two-curved-face limit theorem.

The translated-overlap/volume-of-realisation method is **prior work**:
[Dowker–Liu–Lloyd-Jones, §2.6](https://arxiv.org/html/2501.00139v2#S2.SS6).
This implementation formalizes that representation for the repository's
original action; it does not claim discovery of the method. Its place in the
larger program is [work package D](../notes/flat-localization-plan.md).

## Endpoint pairs to displacements

`TranslatedOverlap.lean` defines the overlap independently of the action:

```lean
def translatedOverlap (M : Set Spacetime) (z : Spacetime) : ℝ :=
  ∫ x in M, M.indicator (fun _ => (1 : ℝ)) (x + z)
```

`translatedOverlap_eq_indicator` identifies it with the integral of the
product of the two region indicators. It uses the existing four-dimensional
**product Lebesgue measure**, not the coordinate norm as a Lorentzian norm.

For measurable bounded `M`, the proofs derive:

- Borel measurability by measurable parameter integration;
- nonnegativity and the pointwise upper bound `volume.real M`;
- zero overlap whenever the displacement norm exceeds `Metric.diam M`, hence
  compact support (the coordinate norm here is only a support-bound tool);
- zero overlap for every zero-volume region, including nonempty ones; and
- absolute integrability of every continuous displacement weight times the
  overlap on the future cone.

Before signed Fubini, the original pair integrand is dominated on the compact
product of the region's closures. The endpoint/displacement shear is proved
measure preserving. `displacementMatrix_apply` identifies its actual block
matrix with `(x,y) ↦ (x,y-x)`, and `det_displacementMatrix` proves determinant
one. Translation preserves both the causal relation and `intervalSq`, including
null-related pairs and the vertex. No nearly-null pairs are discarded.

The resulting theorem starts from **unchanged** `continuumMean`:

```lean
theorem continuumMean_eq_translatedOverlap {M : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M) (ρ : ℝ) :
    continuumMean ρ M = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real M - ρ * ∫ z in causalFuture 0,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
          translatedOverlap M z)
```

Both the outer square-root density and the inner pair density remain. The
normalized pair contribution therefore has the original density to the
three-halves power, not just the square-root prefactor. The entire signed
`bdgKernel` remains inside the integral.

This deterministic equality needs no causal convexity. Interpreting it as the
**isolated Poisson mean** additionally uses `BoundedCausalRegion` and the
already checked `expectedBDGAction_eq` at positive density. The regression
states those additional hypotheses explicitly. Nothing here replaces a
region-restricted interval volume by the unrestricted Minkowski volume in a
non-causally-convex sprinkling.

## Radial null coordinates and the actual density

`OverlapCoordinates.lean` proves polar disintegration for arbitrary measurable
spacetime observables, **without rotational symmetry**. The angular measure is
the full Euclidean polar sphere measure; `overlapSphere_mass` derives its mass
`4 * Real.pi` from the three-ball volume.

The radial null coordinates are unscaled: `u = t-r` and `v = t+r`.
`radialNull_domain`, `radialNull_intervalSq`, and `radialNull_jacobian` check,
respectively, the domain `0 ≤ u ≤ v`, squared proper time `u*v`, and the full
radial Jacobian `(v-u)^2/8`. The time-radius matrix has determinant `1/2`.
These are distinct from the scaled null coordinates used in the older
causal-interval calculation.

Fix `δ > 0` and retain displacements with `v ≥ δ`. Set `σ = u*v`.
`properTimeRadial` sends `(σ,v)` directly to `(t,r)` with
`t = (v+σ/v)/2` and `r = (v-σ/v)/2`.
The proofs derive its actual Fréchet derivative, determinant `1/(2*v)`,
injectivity, and image of the domain. Combining that determinant with the
polar radial square yields the coefficient `(v-σ/v)^2/(8*v)`.
`lintegral_longFuture_properTime` proves the measure transformation before
any signed kernel is inserted.

`OverlapDensity.lean` then defines `longOverlapDensityENN` by integrating
this coefficient times the **actual** `translatedOverlap`, first over `v`
and then over the sphere. `longOverlapDensityENN_eq_average` identifies the
long-coordinate domain with `v ≥ max δ (Real.sqrt σ)` for `σ ≥ 0`.
The density is zero at negative `σ`. `longOverlapDensity` is its real-valued
conversion, not a polynomial or an assumed regular representative.

The proofs derive:

- joint measurability of the coordinate integrand and measurability of both
  versions of the averaged density;
- a uniform finite dominator on `δ ≤ v ≤ 2 * Metric.diam M`;
- finiteness of the nonnegative average at **every** `σ`, a uniform bound for
  the real density, and compact support in `0 ≤ σ ≤ (2 * Metric.diam M)^2`;
- finite total mass and absolute integrability; and
- integrability after multiplication by every continuous proper-time weight,
  in particular the finite-density signed BDG kernel.

`map_longOverlapMeasure` identifies the proper-time pushforward of the
independently defined geometric overlap measure with Lebesgue measure weighted
by that density. Only then does `integral_longOverlap` transport signed test
weights. Its BDG specialization is:

```lean
theorem integral_longOverlap_bdg {M : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ,
      bdgKernel ((Real.pi/24)*ρ*intervalSq 0 z^2) * translatedOverlap M z) =
      ∫ σ : ℝ, bdgKernel ((Real.pi/24)*ρ*σ^2) * longOverlapDensity M δ σ
```

Integrating over the whole real line adds only zeros at negative proper-time
square. The cutoff stays fixed; there is no claim about cutoff removal or
uniform asymptotic estimates as the cutoff tends to zero.

## Separate global two-graph subclass

`GraphOverlap.lean` defines `twoGraphRegion lower upper` and a separate
`StrictGraphLipschitz` predicate using the **Euclidean spatial distance**.
For continuous graphs enclosing a bounded region, vertical Fubini first gives
the positive part of the difference between the minimum of the two upper
bounds and the maximum of the two lower bounds. For future-causal displacements,
the global Lipschitz inequalities then simplify those bounds:

```lean
theorem translatedOverlap_twoGraph_causal {lower upper : Spatial → ℝ}
    (hl : StrictGraphLipschitz lower) (hu : StrictGraphLipschitz upper)
    (hb : Bornology.IsBounded (twoGraphRegion lower upper))
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoGraphRegion lower upper) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (upper (x + a) - s - lower x)
```

This subclass does **not** strengthen `GraphCapData` or `AdmissibleGraphCap`.
For every original reduction-admissible cap, the lower causal envelope
`fun x => -max 0 (h x)` and the zero upper graph satisfy this API and enclose
exactly `graphCapRegion h`. `GraphCapData.translatedOverlap_causal` derives the
corresponding overlap formula without requiring global Lipschitz control of
the raw height. Interior critical points and irrelevant exterior zeros remain
allowed. This is coordinate compatibility, not the unfinished two-face
geometric theorem contract in #49.

## Verification and remaining boundary

`OverlapRegression.lean` independently restates the original finite-density
identity, the conditional expectation interpretation, negative kernel sign,
eight-coordinate determinant, radial and proper-time Jacobians, sphere mass,
retained macroscopic null displacements, empty and singleton regions, density
integrability/support/boundedness, and both graph APIs. It equates the new
expression with the existing unequal-axis ellipsoid reduction and the original
null-cap Gaussian reduction at `T = 2`, `a = 1`, at every positive density.
All original exact reductions remain available unchanged.

Run `cd formal && ./check.sh` for the full library build, every-source
warnings-as-errors check, and transitive axiom audit. The new modules are
imported by the library root. Only Lean's standard foundations are allowed.

**Still open:** smoothness or Taylor behavior at translated tangencies,
geometric long-null cancellation, tangent-wedge asymptotics, curved-face
stability, and globalization. None is a field, hypothesis, or conclusion of
this exact reduction. The separate conditional cancellation task #53 must
still be connected to geometric regularity; these results do not close #24.
