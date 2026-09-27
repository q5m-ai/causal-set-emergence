# Controlled two-curved-face diagnostics (#54)

**Exploratory deterministic evidence, not a localization theorem.** This is
work package F of the [plan](flat-localization-plan.md). It uses the restricted
[geometry contract](two-face-contract.md), the [exact overlap representation](../formal/TRANSLATED_OVERLAP.md),
the [independent joint geometry](../formal/JOINT_GEOMETRY.md), and the
[conditional cancellation criterion](../formal/NULL_TRANSVERSE.md). It does
not add regularity to admissibility, update checked theorem status, establish
sample-wise convergence, or close #24. No Monte Carlo or dynamics model is used.

## Reproduction and numerical contract

```sh
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python -m unittest -v test_two_face_diagnostics
.venv/bin/python reproduce_two_faces.py --orders 16 32 48 > results/two-face-diagnostics.json
# Short exploratory run, not the recorded refinement study:
.venv/bin/python reproduce_two_faces.py --orders 12 20 --densities 1e4 > /tmp/two-faces.json
```

The [recorded JSON](../results/two-face-diagnostics.json) includes every parameter,
quadrature order, density, volume, geometric target, signed regime contribution,
refinement spread, cancellation ratio and calibration. Progress goes to stderr;
the output has no timestamps or random seeds. The default experiment takes
minutes rather than being a unit test. CI runs the regression tests, including
independent base-case integration, not the whole density sweep or a Lean audit.

## Regions, bounds, and causal envelopes

The region is always the open set between the **raw** face germs `f-h` and `f`.
It is equally the set between the globally causal envelopes `f-max(0,h)` and
`f`. These are not interchangeable as functions outside the positive region.
`region_data` exposes both; exterior negative heights enclose no points.

The axial family is

```math
h(x)=d\left(1-\sum_{i=1}^3 x_i^2/a_i^2\right),\qquad
f(x)=b\sin(x_1/a_1),\qquad
\kappa=2d/\min_i a_i,\quad \lambda=|b|/a_1.
```

The radial matched-joint family is

```math
h(x)=d(1-|x|^2/R^2),\qquad
f(x)=b\,[1-|x|^2/c_0^2]_+^4,\qquad
\kappa=2d/R,\quad
\lambda=\frac{8|b|}{\sqrt7 c_0}\left(\frac67\right)^3.
```

Here `0<c0<R`. The radial shift is globally C³ (not claimed C⁴), exactly zero
on the entire annulus `|x|>c0`, and nonlinear inside it. Thus **both face germs
bend, but the whole joint neighborhood is unchanged**. It is not just an
unrelated profile with the same area. The raw quadratic height is not globally
Lipschitz: only its positive part has the displayed bound.

Both constructors check `kappa+lambda<1`. Differentiating gives these global
Euclidean bounds for `max(0,h)` and `f`, respectively. The lower envelope has
constant at most their sum, and the upper has constant at most `lambda`.
Their strict epigraph/hypograph are a future/past set: if a causal displacement
has time component at least its spatial length, the strict graph inequality
persists. Their intersection therefore contains every ambient causal interval
between its points, including null segments. It is open, bounded and causally
convex. The smooth raw faces meet only on the regular ellipsoid/sphere zero
level; there are no lateral walls. This is a written verification for these
explicit regions, not a new Lean constructor proof.

The true four-volume, recomputed by vertical integration, is `8*pi*d*prod(a)/15`
or `8*pi*d*R^3/15`. The common time shear has determinant one, so it leaves
volume unchanged, **not** the causal-pair integral. We integrate that changed
pair integral below, never reuse the planar action for a bent region.

Additional implementation restrictions: the axial overlap contact solver
requires `abs(b)<d`. Both support solvers require
`curvature_bound*sqrt(sigma_max) < (1-lambda^2)^(3/2)`, using the bounds
`abs(b)/a1^2` and `8*abs(b)/c0^2` on the second derivative of the shift.
These ensure a unique one-dimensional gap maximum. They restrict this
experiment, not the general geometric contract. All recorded cases satisfy them.

| Case | Fixed geometry | Strict envelope margin |
| --- | --- | ---: |
| Planar calibration | `d=1/4`, axes `(1,2,3)`, `b=0` | 0.5 |
| Matched-joint interior bend | `d=1/4`, `R=1`, `c0=0.65`, `b=0.025` | greater than 0.4267 |
| Nonplanar sine joint | `d=1/4`, axes `(1,2,3)`, `b=1/16` | 0.4375 |
| Small angle, separate run | `d=0.08`, axes `(1,1,1)`, `b=0.01` | 0.83 |
| Smaller angle, separate run | `d=0.04`, axes `(1,1,1)`, `b=0.005` | 0.915 |

The geometries, including positive angles, do not change with density. On the
joint, `|grad h| >= g_min = 2*d/max(a)` (use `R` for the sphere). The normal
formula gives `C^2-1 >= |grad h|^2`, hence the explicit bounds
`theta >= asinh(g_min)>0` and `coth(theta) <= sqrt(1+g_min^(-2))`. The normal
denominators are at least `sqrt(1-(kappa+lambda)^2)`. These are bounds for each
fixed geometry, not uniform in a small-angle limit. Reported angle extrema in
the JSON are **sampled**, distinct from these analytic lower bounds.

## Actual overlap and signed pair integral

Start from D's causal graph identity, not a locality approximation:

```math
V((s,a))=\int_{\mathbb R^3}[h(x)+f(x+a)-f(x)-s]_+\,dx,\qquad s\ge|a|.
```

This use of the raw height is legitimate **only inside the positive part of
this causal integrand**: outside `h>0`, the strict Lipschitz inequality makes
it zero. Positivity also forces the translated spatial point into the original
positive region, by the envelope bounds. It is not an integral of a raw height
over exterior negative fibres.

Two further integrations can be done analytically. Set

```math
\begin{aligned}
L(p,q)&=d(1-p^2/A^2)+f(q)-f(p),\\
c_\delta(\sigma)&=
\begin{cases}(\delta+\sigma/\delta)/2,&0\le\sigma<\delta^2,\ \delta>0,\\
0,&\text{otherwise},\end{cases}\\
a_{\sigma,\delta}(r)&=\max\{\sqrt{r^2+\sigma},c_\delta(\sigma)\}.
\end{aligned}
```

For the axial family, integrate the transverse ellipse in the overlap, then
the transverse displacement radius and time. With `A=a1` this gives

```math
B_\delta(\sigma)=\frac{\pi^2a_2a_3}{6d}
\int_{-a_1}^{a_1}\int_{-a_1}^{a_1}
[L(p,q)-a_{\sigma,\delta}(q-p)]_+^3\,dq\,dp.
```

For the radial family, use endpoint radii `p,q` and their relative angle.
The spatial pair measure is `8*pi^2*p*q*r*dp*dq*dr`; at fixed squared proper
time, time integration has Jacobian `1/(2*s)`. Integrating the displacement
radius between `abs(p-q)` and `p+q`, with the long cutoff, yields (`A=R`)

```math
B_\delta(\sigma)=2\pi^2\int_0^R\int_0^R pq
\left[[L(p,q)-a_{\sigma,\delta}(q-p)]_+^2
-[L(p,q)-\sqrt{(p+q)^2+\sigma}]_+^2\right]_+\,dq\,dp.
```

The final positive part matters when the cutoff exceeds the upper angular
endpoint. The code does not assume overlap is globally C³. These formulae
retain tangencies and all nearly-null causal pairs. They are written reductions,
independently calibrated below, not new checked Lean identities.

The full action uses `B_0`, with the **original signed kernel**:

```math
I_\rho=\int_0^\infty B_0(\sigma)K((\pi/24)\rho\sigma^2)\,d\sigma,
\qquad
\mathcal A_\rho=\frac4{\sqrt6}\sqrt\rho\,(|M|-\rho I_\rho).
```

The JSON's `pair` and three `pair_*` pieces are already multiplied by
`4*rho^(3/2)/sqrt(6)` and are subtracted from `point`. In particular their
small **unscaled** integration error is not the normalized action error.

## Integration, cancellation and independent controls

- All new cubature uses IEEE float64 with `math.fsum` accumulation. Composite
  Gauss–Legendre rules at orders 16, 32 and 48 refine **every** integration
  variable. Support roots are bracketed, with explicit panels at radial bump
  seams, square-root layers, cutoff contacts and kernel sign changes. Outer
  contact bracketing uses a 64-cell scan; it is not a certified root census for
  arbitrary profiles or degenerate contacts.
- Rescale squared proper time by `z=sqrt(pi*rho/24)*sigma`, then integrate in
  `sqrt(z)`. The second substitution resolves the diagonal logarithmic endpoint
  much better than an unsplit rule in `z`. No fitted jet is subtracted from the
  actual density, and the point term is retained before interpreting the residual.
- The support bound is `sigma_max=d^2/(1-lambda^2)`. A conservative coordinate
  time diameter is `T=d+2*abs(b)`. Since `B <= pi*volume*T^2`, truncation at
  `z=9` has the reported absolute normalized tail bound obtained by integrating
  the absolute polynomial coefficients against the Gaussian. This bounds the
  omitted tail, **not cubature error**. The negative kernel tail below that
  cutoff is included.
- The disjoint split is: `v<delta` (diagonal); `v>=delta` and
  `sigma<sigma_split` (long, near null); `v>=delta` and
  `sigma>=sigma_split` (long, safely timelike). The last category does not include
  timelike displacements already assigned to the diagonal. Both cutoffs are
  fixed, `delta=0.15`, `sigma_split=0.01`. We do not discard cross-region pairs
  or claim uniformity as either cutoff is removed.
- The cancellation ratio is `(point+absolute_pair)/abs(action)`, using the
  integral of the absolute signed integrand, not just the sum of three pieces.
  `roundoff_scale_not_bound` is machine epsilon times the numerator. Neither it
  nor the order spread certifies the total error; correlated refinement errors,
  support-root error and near-tangent losses can remain.
- The independent planar reference uses the existing `ellipsoid_action` at
  40 and 60 decimal digits. A second, independent one-dimensional integral of
  `2*pi*sqrt(s^2-sigma)*V(s)` checks the long density at both precisions.
  These checks do not promote the curved cubature to arbitrary precision.
  A separate unreduced four-variable `(p,q,r,s)` causal integral checks the
  **bent radial** pair term at moderate density, without using `B_delta`.
- A separate `(s,r,mu)` cone cubature evaluates the boosted interval square
  in lab coordinates and the overlap after an explicit inverse boost. It tests
  velocities `0, +0.6, -0.6`, not merely a squared-angle identity. The boost is
  only a planar-ellipsoid calibration. Positive dilation integrates the scaled
  nonplanar geometry independently and checks the density-rescaled action law.
- `joint_geometry` never calls the action or overlap. It constructs chart
  tangents and both future unit normals, computes the positive Lorentzian Gram
  determinant and angle weight, and integrates them. Replacing this determinant
  by the ambient Euclidean one is a deliberate **wrong-target** control.

## Near-null regularity and translated tangencies

At fixed positive `delta`, sample `B(0), B(h), B(2h), B(3h)` and report

```math
D(h)=\frac{B(3h)-3B(2h)+3B(h)-B(0)}{h^2}.
```

This annihilates every quadratic jet without fitting its coefficients. A
quadratic little-o expansion implies `D(h)->0`; the converse is **not** asserted.
The synthetic control `sigma^2*log(sigma)` instead gives the nonzero constant
`9*log(3)-12*log(2)`. Refinement differences are amplified by `h^(-2)` too; small
raw density discrepancies cannot be ignored here.

The separate `axial_null_contact` calculation finds the last nonempty translate
on `(s,s*e1)` by solving both zero gap and stationarity in the spatial coordinate.
It samples overlap just inside and outside that contact. A fractional-power
contact is expected even for smooth original faces: numerical smoothness of
individual translates is not the hypothesis on the **averaged** `B_delta`.
The moving cutoff/face contacts in the density are explicitly panel-split.

## Results and limitations

The recorded run uses orders 16, 32, 48. Below are order-48 values, rounded;
the last column is the **32-to-48 action difference at the largest density**,
not an error bound. Full three-order spreads are retained in the JSON.

| Fixed region | Independent target | Action at `1e4` | At `1e6` | At `1e8` | Last refinement difference |
| --- | ---: | ---: | ---: | ---: | ---: |
| Planar ellipsoid | 150.796447 | 156.679278 | 151.886289 | 150.958220 | 1.09e-7 |
| Matched-joint bump | 25.132741 | 26.131879 | 25.313216 | 25.159602 | 1.77e-6 |
| Nonplanar sine | 150.368018 | 156.146914 | 151.443707 | 150.528003 | 1.19e-7 |
| Small angle `d=0.08` | 78.534104 | 21.494984 | 81.573085 | 79.090909 | 7.73e-9 |
| Smaller angle `d=0.04` | 157.076776 | 10.931931 | 98.108169 | 160.316636 | 4.63e-9 |

**Positive calibrations.** The largest-density planar action differs from the
independent 60-digit reference by about `1.31e-8`. The long density agrees with
its independent reference to about `6e-17` in this set. Boosted and unboosted
order-48 actions at density `1e5` agree with the base reference within `1.3e-10`;
the dilation comparison differs by about `1e-13`.

**Matched joint: suggestive, not resolved asymptotics.** Subtracting the
independently computed planar **sphere** action gives `+0.0186661`,
`-0.00116524`, `-0.000101202` at the three densities. There is no persistent
order-one remote-shape effect in this window. However, at `1e8` the coarsest
order gives the opposite sign, and the full order spread is `0.000175`.
This is not a certified exclusion of a leading nonlocal term.

**Independent nonplanar geometry and wrong-area control.** Lorentzian area is
`48.8542433`; the correct weighted target is `150.368018`, versus `150.589638`
with ambient Euclidean area. The nonplanar-minus-planar action differences are
`-0.532364`, `-0.442582`, `-0.430217`, approaching the independently computed
Lorentzian target difference `-0.428429`, rather than the wrong-area difference
`-0.206809`. This is supportive evidence only. The *absolute* action at `1e8`
still has substantial finite-density bias and is actually closer to the wrong
area target; selecting a limit by the nearest single finite-density value
would be misleading.

**Cancellation is large and long pairs matter.** For the sine region at `1e8`,
`point=41041.5946`, the normalized pair term is about `40891.0666`, and the
absolute pair integral is about `31519686.4`. The cancellation ratio exceeds
`209000`. The signed long contributions are `161.954933`, `76.318510`,
`8.479839` across the density sweep, not negligible at the tested densities.
At the last density the safely timelike portion is beyond the Gaussian cutoff;
its omission is covered by the tail bound (less than `1.5e-22` for this case).
No inference is made by taking absolute values before the signed cancellations.

**Quadratic-remainder diagnostic.** At `h=0.001, 0.0005, 0.00025`:

| Region | `D(h)` | `D(h/2)` | `D(h/4)` |
| --- | ---: | ---: | ---: |
| Planar ellipsoid | -10.289753 | -5.267170 | -2.664360 |
| Matched-joint bump | -1.715092 | -0.877926 | -0.444092 |
| Nonplanar sine | -10.306675 | -5.275780 | -2.668702 |
| Synthetic quadratic-log obstruction | 1.569744 | 1.569744 | 1.569744 |

The first three trends are consistent with a vanishing diagnostic, but do not
prove the little-o expansion. Radial probe spreads across all orders are below
`1.2e-8`; axial spreads are below `1e-9`. **Inconclusive:** the `d=0.08` probe
is nonmonotone (`-0.08558, -0.12646, -0.08263`), with the fixed cutoff close to
the support edge. The `d=0.04` long region is empty since `2*T<delta`; its zero
probes say nothing about nontrivial near-null regularity. Smaller fixed cutoffs
and finer steps are needed to investigate those geometries, not a claim of
uniform small-angle behavior.

**Translated contact and negative outcomes.** For the sine family the null-ray
contact is at `s=0.2664622205`. Relative gaps `0.1, 0.01, 0.001` give overlaps
`0.00785796`, `0.0000248249`, `0.0000000784958`; just beyond contact the computed
overlap is zero. The ratios are consistent with a fractional power `5/2`,
warning against assuming global C³ regularity of individual overlaps. They do
not obstruct the separately averaged density criterion. The coarse direct boost
calibration also has error `0.0677` at density `1e5` despite excellent covariance
agreement: covariance without an independent base case is not an accuracy test.
The small-angle runs visibly need larger densities before interpreting a limit.

**Next gate, not a claimed counterexample:** certify cubature/root/tail errors,
probe smaller steps without amplifying numerical error, and analytically examine
averaging across translated tangencies. No geometric obstruction to locality
is established by this batch; neither is the sufficient expansion proved.
A persistent normalized discrepancy would require certified bounds and analytic
review. G1–G4, the general curved-spacetime conjecture and sample-wise convergence
remain open.
