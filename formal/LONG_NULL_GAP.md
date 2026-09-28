# Long-null gap estimates and the remaining averaging theorem (#61)

**Partial progress only. Issue #61 / G1 remains open.**
`TwoFaceNullGap.lean` proves the geometric gap estimates below under the
unchanged assumptions. `TwoFaceLongNull.lean` proves endpoint/integrability
facts and a **conditional** application of the existing cancellation theorem.
Neither file proves the actual averaged density's right quadratic expansion.
No obstruction or counterexample has been established either.

This is not completion of either acceptance route in
[issue #61](https://github.com/q5m-ai/causal-set-emergence/issues/61). In
particular, compiling a theorem with the jet as a premise is not discharging
that premise. The original region, density, kernel, action, admissibility,
and open two-face limit contracts are unchanged.

## 1. The gap before attempting a repair

The existing [overlap representation](TRANSLATED_OVERLAP.md) and
[conditional analytic theorem](NULL_TRANSVERSE.md) do not give a quadratic
jet. Smoothness of the original faces does not establish smoothness of
individual translated overlaps: spatial contacts can be critical, and the
positive-part operation is not twice differentiable at zero. Dropping an
exceptional set of directions does not estimate its surrounding layer.

The approach investigated here is to **integrate the long coordinate before
asking for a second-order expansion**. Its null-direction transversality is
available even when spatial transversality fails. The proved estimates
control the crossing layer quantitatively; they do not yet identify its
second-order coefficient or prove a little-o remainder after averaging.

## 2. Exact object and unchanged hypotheses

Fix any `AdmissibleTwoFace h f` and any positive cutoff `delta`. The slope
budget supplies nonnegative constants with the following bounds:

```math
\begin{aligned}
H(x)&=\max(0,h(x)), & m&=1-\kappa-\eta>0,\\
|H(x)-H(y)|&\le\kappa|x-y|, & |f(x)-f(y)|&\le\eta|x-y|.
\end{aligned}
```

The positive-part envelope, not the raw height outside the positive region,
is used in `twoFaceGap`. For a unit spatial direction define

```math
\begin{aligned}
s(\sigma,v)&=\frac{v+\sigma/v}{2}, &
r(\sigma,v)&=\frac{v-\sigma/v}{2},\\
g(\sigma,v;x,\omega)&=H(x)+f(x+r(\sigma,v)\omega)-f(x)-s(\sigma,v),\\
J(\sigma,v)&=\frac{(v-\sigma/v)^2}{8v}.
\end{aligned}
```

`translatedOverlap_eq_gap` identifies the positive part of this same gap
with the existing causal graph-overlap formula; it does not define a smoother
overlap. For nonnegative squared proper time smaller than the squared cutoff,
the existing density formula has lower long-coordinate endpoint `delta`.
The intended order of integration is consequently

```math
B_\delta(\sigma)=\int_{S^2}\int_{\mathbb R^3}
 \left(\int_\delta^\infty J(\sigma,v)
       [g(\sigma,v;x,\omega)]_+\,dv\right)dx\,d\omega.
```

Here the sphere measure has mass `4*pi`. The existing ENNReal formula and
causal graph identity are proved separately. **Their combination into this
threefold real-valued formula, with the required Tonelli/finite-integral
transport, is part of the remaining formalization**, not a new theorem in
this patch.

## 3. Proved geometric estimates

### Both endpoints stay inside the smooth region

For any spatial endpoints with causal elapsed time and a nonnegative gap,
including an exact contact, `exists_gap_height_margin` proves

```math
\begin{aligned}
|y-x|\le s,\quad H(x)+f(y)-f(x)-s\ge0
\quad\Longrightarrow\quad
H(x)\ge ms,\qquad H(y)\ge ms.
\end{aligned}
```

The first bound follows from the future Lipschitz bound. For the second, use
that the lower causal envelope `f-H` is Lipschitz with constant at most
`kappa+eta`. At a positive separation both raw heights are positive
(`gap_endpoints_positive`). On the null cone with `v>=delta` the margin is at
least `m*delta/2`. This does not require the height differential to be nonzero
at positive height or the raw height to be regular outside its positive set.

### Long-coordinate transversality at the null cone

`twoFaceRayGap_null_sub_le` proves the finite-difference estimate

```math
g(0,w)-g(0,v)\le-\frac{1-\eta}{2}(w-v),\qquad v\le w.
```

Thus each fixed spatial point and direction has at most one null-gap zero.
This says nothing about the regularity of the spatial zero locus. In
particular it allows the critical point in the planar ellipsoid regression.
It is an estimate **at the null cone**, not a claim of monotonicity in the
long coordinate throughout the timelike domain. Where derivatives exist,
the long derivative away from that cone also has a proper-time correction:

```math
g_v=\frac{D f(x+r\omega)[\omega]-1}{2}
 +\frac{\sigma}{2v^2}\bigl(D f(x+r\omega)[\omega]+1\bigr).
```

### Right-hand shrinkage, including the cutoff contact

For positive `v`, `twoFaceRayGap_transverse_bounds` proves

```math
-\frac{1+\eta}{2v}(\tau-\sigma)
\le g(\tau,v)-g(\sigma,v)
\le-\frac{1-\eta}{2v}(\tau-\sigma),\qquad \sigma\le\tau.
```

Combining this with null transversality proves
`twoFaceRayGap_nonpos_of_cutoff`: if the null gap at the cutoff is nonpositive,
then the gap is nonpositive for every nonnegative proper-time square and every
long coordinate above the cutoff. An entire set of cutoff contacts is handled
pointwise, without assuming it has measure zero.

### Quantitative crossing-layer bound

`volume_twoFaceRayGap_null_layer` bounds the length of a thin null-gap level
band by its diameter. `volume_twoFaceRayGap_crossing` then proves, for each
spatial point and direction and every nonnegative proper-time square,

```math
\mathrm{length}(\{v\ge\delta:0 < g(0,v),\ g(\sigma,v)\le0\})
\le\frac{(1+\eta)\sigma}{\delta(1-\eta)}.
```

Indeed, all crossing points satisfy

```math
0 < g(0,v)\le\frac{(1+\eta)\sigma}{2\delta}.
```

Null transversality bounds the diameter of this band by twice its height
range divided by `1-eta`; one-dimensional Lebesgue measure is at most that
diameter. This includes the surrounding layer of every translated tangency.
The constant depends on the fixed cutoff. It is not uniform as that cutoff
approaches zero.

## 4. Bounded remaining problem: the length-integrated right jet

The following is a **proposed proof route, not a checked regularity theorem**.
It records the specific missing coefficient and domination obligations, rather
than inserting them into `AdmissibleTwoFace`.

For fixed spatial point and direction let `F(sigma)` be the inner long
integral in section 2. If the null gap at the cutoff is nonpositive, the
proved shrinkage theorem makes `F` identically zero on the right. Otherwise
null transversality and a sufficiently large fixed support bound give a
unique contact `R>delta`. The endpoint-height margin puts the active endpoints
in a compact subset of the original smooth region. The intended next step
is a scalar implicit-function and parameter-integral argument at that root.
No spatial critical-point or exceptional-direction exclusion is needed.

For reference, write `g0(v)=g(0,v)`, and, only on the active smooth set, set

```math
\begin{aligned}
a(v)&=-\frac{1+D f(x+v\omega/2)[\omega]}{2v},\\
b(v)&=\frac{D^2f(x+v\omega/2)[\omega,\omega]}{8v^2},\\
d(v)&=\frac{1-D f(x+v\omega/2)[\omega]}{2}>0,\\
J_0(v)&=\frac v8,\qquad J_1(v)=-\frac1{4v},\qquad J_2(v)=\frac1{8v^3}.
\end{aligned}
```

Formal differentiation of the moving-endpoint integral suggests these
coefficients when the cutoff gap is strictly positive:

```math
\begin{aligned}
F_0&=\int_\delta^R J_0g_0\,dv,\\
F_1&=\int_\delta^R (J_1g_0+J_0a)\,dv,\\
F_2&=\int_\delta^R (J_2g_0+J_1a+J_0b)\,dv
       +\frac{J_0(R)a(R)^2}{2d(R)}.
\end{aligned}
```

The last term is essential: it is the moving-contact contribution. Setting
the pointwise second derivative of the positive part to zero almost
everywhere and differentiating under the integral would miss it. For a gap
zero **at the cutoff**, the right-hand coefficients are instead all zero;
one must not use the interior-root formula there.

What still needs Lean proof:

1. Construct the fixed compact active domain and uniform smooth bounds from
   the original local C3 assumptions and the proved endpoint-height margin.
   Do not use global smoothness of the causal envelopes.
2. Prove the pointwise right expansion of the length integral, including
   the moving-contact coefficient and the entire cutoff-contact set.
3. Bound its normalized second-order remainder uniformly over spatial points
   and directions. The proved crossing-layer length bound times a gap change
   of order `sigma` suggests an order `sigma^2` error bound. **That bound alone
   is not little-o**; identify and subtract the moving-contact coefficient
   before taking the pointwise limit.
4. Prove coefficient measurability/integrability and dominate the quotient
   on one finite-measure spatial/directional domain. Only then use dominated
   convergence to pass the jet to the actual `longOverlapDensity`.
5. Remove the jet premise from the conditional assembly below, and expose the
   cut-off endpoint-pair identity, with its discontinuous cutoff, if the final
   statement is written directly in endpoint variables.

No logarithmic or nonquadratic obstruction has been proved or ruled out by
these preparatory theorems. This patch is not the issue's alternative research
outcome. The explicit follow-up remains **#61 itself**, not a silently weaker
replacement of its original acceptance criteria.

## 5. Checked conditional assembly and normalization

`TwoFaceLongNull.lean` keeps the proposed jet as an explicit premise:

```lean
∃ b0 b1 b2 : ℝ,
  (fun sigma => longOverlapDensity (twoFaceRegion h f) delta sigma -
    (b0 + b1 * sigma + b2 * sigma ^ 2)) =o[𝓝[>] (0 : ℝ)]
      (fun sigma => sigma ^ 2)
```

Given this premise, measurability and boundedness come from the existing
geometric APIs. Absolute integrability of both the displacement and density
integrands is proved without a jet and at every real density. The negative
half-line vanishes by the density definition; atomlessness removes the single
zero endpoint. Neither the point value at zero nor equality of that value
with `b0` is assumed.

The conditional theorem applies `bdgKernel_transverse_cancellation` with
exactly `pi/24`, then uses `integral_longOverlap_bdg` to obtain the limit of

```math
-\frac4{\sqrt6}\sqrt\rho\,\rho
\int_{\mathrm{longFuture}(\delta)}
 K\left(\frac\pi{24}\rho Q(z)^2\right)V_M(z)\,dz.
```

Both density factors and the entire signed polynomial are retained. This is
only the long overlap contribution, not the point term, short-displacement
cancellation, cutoff removal, full action limit, or sample-wise convergence.
The still-open jet premise prevents an unconditional geometric conclusion.

## 6. Regressions and validation scope

`TwoFaceLongNullRegression.lean` independently checks:

- unchanged planar-cap inclusion and gap formulas;
- an original unequal-axis ellipsoid's positive-height critical point, its
  null-ray contact in every direction, a cutoff exactly at contact, and a
  smaller cutoff including the crossing layer;
- a genuinely curved future face with its nonaffinity witness retained, and
  a uniform crossing-layer estimate;
- the conditional signed normalization with the jet premise visible;
- actual finite-density integrability/transport and a changed endpoint weight.

These are **not regressions of a proved geometric jet**. The full source/axiom
audit is `formal/check.sh`; repository checks include `check_markdown.py`,
`check_symbolic.py`, the Python unit suite, numerical reproduction, and the
site JavaScript syntax checks. Green GitHub checks do not replace the local
Lean audit or discharge the remaining mathematical obligation.
