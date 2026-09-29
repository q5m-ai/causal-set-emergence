# Fixed-positive-cutoff geometric long-null cancellation (#61)

**Checked theorem:** for every unchanged `AdmissibleTwoFace h f` and every
fixed positive cutoff, the **actual existing** `longOverlapDensity` has a
right quadratic jet. The original signed-kernel cancellation theorem then
proves vanishing of the fully normalized long-displacement contribution.
No expansion, integrability, root-selection, or contact-nullity premise is
added to admissibility. The region, density, kernel, and action are unchanged.

The final theorems in `TwoFaceLongNull.lean` are:

```lean
AdmissibleTwoFace.longOverlapDensity_right_quadratic_jet
AdmissibleTwoFace.tendsto_longOverlap
AdmissibleTwoFace.tendsto_normalized_longOverlap
```

This resolves the fixed-positive-cutoff proof obligation of #61 / G1, not
#24, the complete two-face action limit, or Conjecture 1′. This note describes
the integrated proof; it does not rewrite the historical status of draft
PR #68 or claim that the integration has been merged.

## 1. The discovered gap, before its repair

The [exact overlap representation](TRANSLATED_OVERLAP.md) and
[conditional analytic theorem](NULL_TRANSVERSE.md) did not give a quadratic
jet. Smooth original faces do not imply smooth individual translated overlaps:
spatial contacts can be critical, and the positive part is not twice
differentiable at zero. Dropping an exceptional set of directions does not
control its surrounding layer.

The preparatory `TwoFaceNullGap.lean` bounded the crossing layer's length,
but that alone gave only a quadratic error bound, not a quadratic expansion
with little-o remainder. Differentiating the positive part away from its zero
set would omit a nonzero moving-contact coefficient. The original partial
proof also lacked a real-valued triple-integral identity and justified
coefficient averaging. These were genuine gaps, not consequences of the
conditional theorem already being checked.

The repair integrates the long coordinate **first**. Null-ray transversality
survives spatial critical contacts. A fixed-interval expansion plus an explicit
rescaled lost-layer calculation gives each fibre's jet. A common bound, not
uniform little-o, then permits averaging after integrability is proved.

## 2. Exact object, hypotheses, and pointwise disintegration

Fix `AdmissibleTwoFace h f` and `delta > 0`. The original slope budget gives
nonnegative constants and a positive margin:

```math
\begin{aligned}
H(x)&=\max(0,h(x)), & m&=1-\kappa-\eta>0,\\
|H(x)-H(y)|&\le\kappa|x-y|, & |f(x)-f(y)|&\le\eta|x-y|.
\end{aligned}
```

Only the original local C³ face germs on the closed positive region are used.
No global smoothness of the positive-part envelope, noncriticality at positive
height, or minimum active height is imposed. For a unit spatial direction:

```math
\begin{aligned}
s(\sigma,v)&=\frac{v+\sigma/v}{2}, &
r(\sigma,v)&=\frac{v-\sigma/v}{2},\\
g(\sigma,v;x,\omega)&=H(x)+f(x+r(\sigma,v)\omega)-f(x)-s(\sigma,v),\\
J(\sigma,v)&=\frac{(v-\sigma/v)^2}{8v}.
\end{aligned}
```

These are exactly `twoFaceRayGap` and `TwoFaceLongGeometry.weight`, not
regularized replacements. `translatedOverlap_eq_gap` gives the spatial
positive-part formula at causal displacements. For **every** nonnegative
`σ < δ²`, `max_cutoff_sqrt_eq` makes the lower long endpoint exactly `δ`.
WP3 (`TwoFaceLongDisintegration.lean`) proves:

```math
B_\delta(\sigma)=\int_{S^2}\int_{\mathbb R^3}
 \int_\delta^\infty J(\sigma,v)[g(\sigma,v;x,\omega)]_+\,dv\,dx\,d\omega.
```

The spherical measure is the unchanged `overlapSphereMeasure`, of mass
`4*pi`, not probability-normalized. WP3 proves joint measurability including
the closed cutoff. The positive spatial gap is integrable by domination by
the compactly supported envelope `H`. Nonnegative Tonelli is used before
real Fubini. The existing density finiteness theorem bounds the full
nonnegative triple integral at **each** `σ`. Conversion to real integrals
therefore gives a pointwise identity in `σ`, including zero; it does not merely
select an almost-everywhere density representative.

In the integration module, `measurable_integrandENN` reuses WP3's joint
measurability with an extra upper cutoff. `fibre_eq_toReal` identifies each
finite real fibre with the real conversion of that nonnegative integral.
`lintegral_fibreENN_lt_top` bounds the parameter integral by WP3's finite
triple integral. Consequently `measurable_integrable_fibre` proves both
measurability and absolute integrability on the **full** product measure
`overlapSphereMeasure.prod volume` before `integral_prod` is used.

## 3. Common geometric constants, support, and the right interval

The endpoint-height estimate includes exact contacts:

```math
|y-x|\le s,\quad H(x)+f(y)-f(x)-s\ge0
\quad\Longrightarrow\quad H(x)\ge ms,\qquad H(y)\ge ms.
```

The first bound follows from the future-face Lipschitz bound; the second uses
the lower causal envelope `f-H`. At positive long separation, both endpoints
are inside the smooth positive region, even at a positive-height critical
point. Null transversality and transverse shrinkage give:

```math
\begin{aligned}
g(0,w)-g(0,v)&\le-\frac{1-\eta}{2}(w-v),\qquad v\le w,\\
-\frac{1+\eta}{2v}(\tau-\sigma)
&\le g(\tau,v)-g(\sigma,v)
\le-\frac{1-\eta}{2v}(\tau-\sigma),\qquad \sigma\le\tau,\quad v>0.
\end{aligned}
```

In particular a nonpositive null gap at the cutoff never opens on the right.
This is a pointwise fact about the **entire** cutoff-contact set, without any
assumption that this set is null. Transversality here is in the long coordinate
at the null cone, not spatial transversality or monotonicity at all timelike
parameters.

WP2 (`TwoFaceLongGeometry.exists_hypotheses`) chooses common constants for
**all** spatial points and directions. If `Hmax` bounds `H` globally, it uses:

```math
c=\frac{1-\eta}{2},\qquad A=\frac{1+\eta}{2\delta},\qquad
V=\delta+\frac{H_{\max}+1}{c},\qquad
\varepsilon=\frac{m\delta^2}{2}.
```

The old active spatial endpoints lie in the compact superlevel tube of height
`m*δ/2`; the perturbed endpoints, on the supplied interval, stay in the compact
tube of height `m*δ/4`. These tubes are contained in the closed positive region,
and the latter is contained in the positive region itself. Compactness bounds
the actual weight by `M` and the second parameter derivative of the actual
product `J*g` by `B`. WP2 proves the derivative identities by the chain rule,
including the Jacobian derivatives and both product cross terms. It never
differentiates the positive-part height in the spatial parameter.

Uniform strict clearance at `V`, followed by the global non-opening estimate
with cutoff `V`, makes the integrand zero for every `v > V` and every
nonnegative `σ`. This justifies the finite truncation, not merely boundedness
of a proposed integration interval. Since `δ < V`, the oriented integral
`δ..V` equals the integral over `Ioc δ V`; atomlessness replaces it by `Icc δ V`.
WP1's `fibre_eq_setIntegral` is the precise convention bridge.

`longOverlapDensity_eq_parameterFibre` thus identifies the actual density with
the product-space integral of the actual `MonotoneHinge.fibre` for every
`0 ≤ σ < δ²`. For averaging, use the single common neighborhood:

```math
e=\min\left(\varepsilon,\frac{\delta^2}{2}\right)>0,
\qquad 0<\sigma\le e\ \Longrightarrow\ \sigma\le\varepsilon,\quad \sigma<\delta^2.
```

This interval does not depend on the fibre or on its distance from contact.

## 4. Fibre expansion and the moving-contact coefficient

WP1 (`MonotoneHingeIntegral.lean`) handles all three regimes. Negative cutoff
gap and exact cutoff contact have identically zero right fibres and all three
coefficients zero. With positive cutoff gap, strict null decrease, continuity,
and clearance give a unique old root `R` strictly between `δ` and `V`.

The old active interval is exactly `[δ,R]`. Expand the smooth product there,
and account separately for the lost layer. In conventional derivative notation
on this smooth active interval:

```math
\begin{aligned}
a(v)&=-\frac{1+D f(x+v\omega/2)[\omega]}{2v},\\
b(v)&=\frac{D^2f(x+v\omega/2)[\omega,\omega]}{8v^2},\\
d(v)&=\frac{1-D f(x+v\omega/2)[\omega]}{2}>0,\\
J_0(v)&=\frac v8,\qquad J_1(v)=-\frac1{4v},\qquad J_2(v)=\frac1{8v^3}.
\end{aligned}
```

Writing `g0(v)=g(0,v)`, the coefficients in the strictly active regime are:

```math
\begin{aligned}
F_0&=\int_\delta^R J_0g_0\,dv,\\
F_1&=\int_\delta^R (J_1g_0+J_0a)\,dv,\\
F_2&=\int_\delta^R (J_2g_0+J_1a+J_0b)\,dv
       +\frac{J_0(R)a(R)^2}{2d(R)}.
\end{aligned}
```

The last term is the moving-contact **coefficient**, not the second derivative.
The factor one-half is essential. At exact cutoff contact the right coefficients
are instead all zero; the interior-root formula is not applied there.

The identity `max 0 g - g = max 0 (-g)` expresses the correction on the old
interval. Its support is within `A*σ/c` of the old root and its height is at
most `M*A*σ`. After substituting `v=R-σ*u`, joint differentiability of the gap
and continuity of the weight give a triangular limiting profile. Its area is
exactly the displayed moving-contact term. No perturbed root needs to be
selected. Scalar Peano expansion on the old interval and dominated convergence
handle the fixed smooth part. Together these prove genuine right little-o:

```math
F(\sigma)-F_0-F_1\sigma-F_2\sigma^2=o(\sigma^2).
```

Only the **pointwise** layer limit can shrink its neighborhood with `R-δ`.
Separately, a twice-applied mean-value bound for the fixed part and a layer
size estimate prove, on the **whole common interval**:

```math
\frac{|F(\sigma)-F_0-F_1\sigma-F_2\sigma^2|}{\sigma^2}
\le D,\qquad
D=2B(V-\delta)+\frac{2MA^2}{c},\qquad 0<\sigma\le\varepsilon.
```

The estimate still holds for fibres that have already closed at that `σ`.
This is uniform domination, **not uniform little-o**. The approaching-contact
regressions explicitly disprove uniform fibre little-o. Neither that stronger
claim nor a positive minimum root-to-cutoff distance is needed for averaging.

## 5. Measurability, coefficient integrability, and finite domination

Set the parameter to `(ω,x)` and use the original sphere × spatial measure.
WP4 (`AveragedQuadraticJet.measurable_coefficients_of_right_jet`) recovers
coefficient measurability from the measurable fibres along one fixed positive
sequence and their pointwise jets. Thus it does not require measurable root
selection, even though WP1 defines an old root for its coefficient formulas.

The integration proof supplies WP4's missing coefficient-integrability input,
rather than leaving it to the final theorem's caller. Define the compact
spatial set `S` by the superlevel tube of height `m*δ/2`, transported from
Euclidean coordinates to the original `Spatial` topology. The product
`P = univ × S` has finite measure because the sphere has finite mass and `S` is
compact. Outside `P`, a nonnegative null gap at `δ` would contradict the
endpoint-height margin. Therefore the fibre on the common right interval and
**all three coefficients** vanish there.

Work first with the finite restricted parameter measure. Put `s=e/3` and use
the three distinct positive probes `s,2s,3s`. Each fibre is integrable by the
nonnegative finite triple identity from section 2. Its error after subtracting
the polynomial is measurable and bounded in norm by `D` times the square of
the probe, so it too is integrable on this finite measure space. Hence the
three polynomial evaluations are integrable. Writing these evaluations as
`P1,P2,P3`, elementary elimination gives:

```math
\begin{aligned}
C_0&=3P_1-3P_2+P_3,\\
C_1&=\frac{-5P_1+8P_2-3P_3}{2s},\\
C_2&=\frac{P_1-2P_2+P_3}{2s^2}.
\end{aligned}
```

`TwoFaceLongNull.integrable_coefficients_of_three_probes` exposes this argument.
The positive probe makes both denominators nonzero. Extension by zero gives
integrability of the unchanged coefficient functions on the full product
measure. This uses no continuity of coefficients at cutoff contacts.

On that **full** parameter space the normalized remainder is dominated by
`D` times the indicator of `P`, an integrable function. A positive constant
is never integrated over all of `Spatial`. The fibre in the averaged theorem
is itself unrestricted, and its product integral equals WP3's nested integrals
by the already justified real Fubini theorem. Thus no restricted-fibre
representative or discarded parameter layer is substituted for the density.

WP4's generic `averaged_right_quadratic_jet` now applies dominated convergence
to the normalized remainders. It moves polynomial subtraction through the
integral only after proving every required integrability statement. The exact
pointwise density identity on the common neighborhood transports the result:

```lean
theorem AdmissibleTwoFace.longOverlapDensity_right_quadratic_jet
    (hf : AdmissibleTwoFace h f) (hδ : 0 < δ) :
    ∃ b0 b1 b2 : ℝ,
      (fun sigma => longOverlapDensity (twoFaceRegion h f) δ sigma -
        (b0 + b1 * sigma + b2 * sigma ^ 2)) =o[𝓝[>] 0]
          (fun sigma => sigma ^ 2)
```

The proof does not assume the cutoff-contact set is null; it treats it
pointwise, including positive-measure contact sets. WP4's atomic-contact
regression checks this distinction independently.

## 6. Signed cancellation, endpoint replacement, and normalization

The existing geometric APIs supply actual-density measurability and global
boundedness. Both the displacement integrand and the density integrand with
the original BDG kernel are absolutely integrable at every real density.
`integral_longOverlap_bdg` is the exact whole-line transport. The actual
density vanishes at negative squared proper time; the equality of the closed
and open positive-half-line integrals uses atomlessness only at `σ=0`.
No near-null layer is removed, and no identification of the point value at
zero with the constant jet coefficient is assumed.

`bdgKernel_transverse_cancellation` is applied with the **original** `bdgKernel`
and exactly `pi/24`, using the newly proved actual-density jet. Its three
signed polynomial moment cancellations occur before absolute domination.
Transport back through the overlap identity gives:

```math
\rho^{3/2}\int_{\mathrm{longFuture}(\delta)}
 K\left(\frac\pi{24}\rho Q(z)^2\right)V_M(z)\,dz\longrightarrow0.
```

For eventually positive density, the three-halves power is exactly the product
of square root and density. Multiplication by the original negative constant
gives the signed contribution in the original action:

```math
-\frac4{\sqrt6}\sqrt\rho\,\rho
\int_{\mathrm{longFuture}(\delta)}
 K\left(\frac\pi{24}\rho Q(z)^2\right)V_M(z)\,dz\longrightarrow0.
```

Both density factors, every sign, the full kernel, and the interval-volume
coefficient are retained. This is the long-displacement causal-pair contribution
in its exact displacement representation, not the point term or the full action.

## 7. Regressions, audit, and remaining limitations

`TwoFaceLongNullRegression.lean` instantiates the unconditional actual-density
jet and both long-overlap limits for:

- every original planar cap;
- the original unequal-axis ellipsoid, retaining its positive-height critical point;
- a cutoff exactly at contact, with zero right fibre coefficients there;
- a family of roots approaching the cutoff inside one fixed region;
- the genuinely curved sine future face, retaining its nonaffinity witness;
- the admissible empty region and zero-volume cases where applicable.

The long contact/root proofs remain in the independently audited component
regressions; the final file adds only short witnesses connecting those same
examples to the unconditional theorem. It retains endpoint and finite-density
transport checks and spells out the full signed normalization and original
kernel coefficient. The separate
components also check nonconstant weights, positive-mass contacts, nonuniform
fibre little-o, and the logarithmic negative control for a nonintegrable scale.

Validation uses focused warnings-as-errors Lean checks, the full integrated
`formal/check.sh` source/transitive-axiom audit, Markdown lint and tests, the
pinned Python unit suite, symbolic checks, numerical reproduction against
`RESULTS.md`, both CI JavaScript syntax checks, and GitHub's live browser math
renderer. Only the standard Lean foundations are allowed; no admissions,
custom axioms, or analytic-conclusion admissibility fields are introduced.

**Exact remaining scope:** the cutoff is fixed and positive throughout the
density limit. There is no claim of uniformity as it tends to zero, a rate,
short-displacement cancellation, cutoff removal, tangent-wedge stability,
globalization, the complete two-face action or expectation limit, Conjecture 1′,
variance, concentration, or sample-wise convergence. The separately checked
Poisson-expectation bridge remains separate from this deterministic theorem.
