# Smooth flat 2D: full signed deterministic limit, then expectation (#131)

**Status:** conventional proof for exactly `SmoothTwoD` below; not an
end-to-end Lean limit theorem and not independently human-reviewed.
The new [checked interface](../formal/TWO_D.md) proves the region/interval,
normal-angle/counting, complete time-fibre and finite-density expectation
inputs. The density transport, moving-endpoint jet, signed logarithmic
asymptotics and unconditional limit assembly below still require Lean
producers. Neither `TwoDDeterministicGoal` nor `TwoDExpectedGoal` has a
proof term in this delivery. Bounded prerequisite ownership is recorded in
that interface. This distinction is part of acceptance, not a missing premise
inserted into admissibility.

## 1. Frozen geometry and independent target

Use exactly [#92's smooth combined-budget candidate](dimension-two-face-geometry.md#1-dimension-regularity-and-independent-region-data)
in physical dimension two. Identify `DimensionSpatial 1` isometrically with
the real line, with its ordinary Lebesgue normalization. Write

```math
\begin{aligned}
H&=\max(0,h),&\Omega&=\{h>0\},&K&=\overline\Omega,&S&=K\cap\{h=0\},\\
L&=f-H,&U&=f,&M&=\{(s,x):f(x)-h(x)\lt s\lt f(x)\}.
\end{aligned}
```

The positive region is bounded; h and f have smooth ambient germs near K;
h vanishes on the frontier and has nonzero derivative at every point of S.
Globally H and f are respectively kappa- and eta-Lipschitz, with nonnegative
constants satisfying the **combined** strict budget:

```math
\kappa+\eta\lt1.
```

There is no density, overlap, asymptotic, counting, or expectation premise.
The empty case is allowed and trivial. Nonempty examples are given in §7.
All positive-height critical points, components and endpoints remain present.
Raw exterior zeros not in K are excluded, and raw h need not be globally smooth.

The envelope description makes M open and bounded. For a closed causal
interval with endpoints in M, the Lipschitz constants of L and U are at most
kappa+eta and eta. Along each future causal segment the strict lower margin
cannot decrease to zero; along each past segment the upper margin cannot
decrease to zero. Thus the **whole closed ambient interval** lies in M,
including null and coincident endpoints. This is checked by
`SmoothTwoD.causallyConvex_region`. The boundary consists of the two compact
face graphs over K, meeting exactly over S, by the closure-of-fibres argument
in #92 Theorem G. No lateral wall or extra exterior zero sheet is included.
The whole-region geometry is used below; no bilocal-action additivity is assumed.

The inverse function theorem makes every zero in S isolated; compactness
makes S finite. A bounded open subset of the line with this finite regular
boundary is a finite union of disjoint open intervals. Nonzero derivative
excludes a puncture at which positive intervals would meet. This description
is used to differentiate moving endpoints, not to truncate partner integrals.
The intrinsic zero-dimensional tangent Gram determinant is the empty
determinant, one. Consequently each lifted joint point has mass **one**,
using the pre-existing `DimensionTwoEndpoints` Hausdorff/counting normalization.

At an endpoint e, put a=h'(e), q=f'(e), p=q-a. Differentiate H only on the
positive interior and extend the actual h derivative to its closure. The
budget gives absolute face slopes below one, and a is nonzero. Define the
target from the two **future** unit normals before considering the action:

```math
\begin{aligned}
n_-&=\frac{(1,p)}{\sqrt{1-p^2}},&n_+&=\frac{(1,q)}{\sqrt{1-q^2}},\\
C_e&=g(n_-,n_+)>1,&\theta_e&=\log(C_e+\sqrt{C_e^2-1}),\\
\mathcal J(h,f)&=\sum_{e\in S}\coth\theta_e.
\end{aligned}
```

Indeed, the positive numerator and the identity

```math
(1-pq)^2-(1-p^2)(1-q^2)=(p-q)^2=a^2
```

give the independent evaluation

```math
\mathcal J(h,f)=\sum_{e\in S}\frac{1-q_e^2+q_e a_e}{|a_e|}.
```

The normal/positive-angle interpretation and all-endpoint coth sum are checked
in `TwoDMetric.lean`. The last scalar evaluation is proved here and tested
symbolically; it is not claimed as a new compiled coefficient theorem.

## 2. Actual action and full causal overlap

Use the unchanged dimension-two constants from #71/#77/#91:

```math
\begin{aligned}
V_{xy}&=\frac{(t_y-t_x)^2-(x_y-x_x)^2}{2},\\
P(z)&=1-2z+z^2/2,&K_2(z)&=P(z)e^{-z},\\
\mathcal A_\rho(M)&=2\rho|M|-4\rho^2
 \int_M dx\int_{M\cap J^+(x)}dy\,K_2(\rho V_{xy}).
\end{aligned}
```

This is exactly `twoDAction`, not a smeared or retuned observable.
`SmoothTwoD.restricted_interval` uses #91 only after interval containment has
been proved; `integrable_bilocal` retains the entire signed kernel.
Boundedness and kernel continuity on the compact pair box give absolute
integrability at every fixed positive density.

For a future displacement (t,r), let V(t,r) be the actual volume of
M intersected with its translate by minus (t,r). For each source spatial x,
the two complete time intervals intersect. Since the displacement is causal,
the strict envelope bounds select the later lower endpoint and the earlier
upper endpoint without dropping either partner:

```math
\begin{aligned}
t&\ge|r|,\\
\min(U(x),U(x+r)-t)&=U(x+r)-t,\\
\max(L(x),L(x+r)-t)&=L(x),\\
V(t,r)&=\int_{\mathbb R}[H(x)+f(x+r)-f(x)-t]_+\,dx\\
 &=\int_\Omega[h(x)+f(x+r)-f(x)-t]_+\,dx.
\end{aligned}
```

The **complete time-fibre identity** is checked in
`SmoothTwoD.causal_time_fibre`; its volume/Fubini use here is conventional.
When the bracket is positive, both source x and partner x+r belong to the
original positive region. In fact, with g denoting the bracket before clipping,

```math
\begin{aligned}
g\ge0,\quad t>0\quad\Longrightarrow\quad
H(x)&\ge(1-\eta)t,\\
H(x+r)&\ge(1-\eta-\kappa)t>0.
\end{aligned}
```

These margins follow directly from the two Lipschitz bounds; they apply also
at moving contacts. They keep every active nonzero-displacement endpoint in a
compact positive-height subset where the actual raw germs are smooth. If B
bounds H, positive overlap requires t below B/(1-eta), so the displacement
support is bounded. The argument never presumes that sources in one component
have partners only in that component.

Translation/Fubini now rewrites the pair integral as the integral of V(t,r)
against the same kernel over the **whole future cone**. Introduce squared
proper time sigma and two spatial directions:

```math
\begin{aligned}
v&=t+|r|,&\sigma&=t^2-r^2,\\
t&=\frac{v+\sigma/v}{2},&
r&=\varepsilon\frac{v-\sigma/v}{2},&\varepsilon&\in\{-1,1\},\\
v&\ge\sqrt\sigma,&dt\,dr&=\frac{d\sigma\,dv}{2v},\\
D(\sigma)&=\frac12\sum_{\varepsilon=\pm1}
 \int_{\sqrt\sigma}^{\infty}
 V\left(\frac{v+\sigma/v}{2},\varepsilon\frac{v-\sigma/v}{2}\right)\frac{dv}{v},\\
\mathcal A_\rho(M)&=2\rho|M|-4\rho^2
 \int_0^\infty K_2(\rho\sigma/2)D(\sigma)\,d\sigma.
\end{aligned}
```

The ray at r=0 is double-counted only on a Lebesgue-null set. Null and diagonal
points remain in the underlying order/region definitions; their nullity is
used only in these integral changes of variables. The two-direction factor
and Jacobian are genuinely two-dimensional, not a 3D circle measure.

## 3. One fixed cutoff and the actual long density

Choose one sufficiently small positive delta for the local endpoint construction
in §4. Split the **same** v domain into v below delta and v at least delta,
calling the resulting densities D-short and D-long. Allocate the point term
once, to short. This gives an exact signed action split; cutoff equality belongs
to long. There is no density-dependent cutoff or subsequent cutoff limit.

For sigma sufficiently small relative to delta squared, the long lower limit
is exactly delta. For fixed x and sign, write

```math
\begin{aligned}
g(x,v,\sigma)&=h(x)+f(x+r)-f(x)-t,\\
\partial_\sigma g&=-\frac{1+\varepsilon f'(x+r)}{2v},\\
\partial_v g&=\frac{\varepsilon f'(x+r)(1+\sigma/v^2)-(1-\sigma/v^2)}2.
\end{aligned}
```

Near active contacts the endpoint margins in §2 put x and x+r in a common
compact smooth neighborhood. At sigma zero the v derivative is at most
minus (1-eta)/2. Uniformly for small positive sigma it remains strictly
negative: it suffices to bound sigma/delta-squared strictly below
(1-eta)/(1+eta). The contact equation therefore has at most one root in v
for each x and sign; its zero set has product measure zero by Fubini.
Equivalently, the same strict monotonicity follows by finite differences from
the global eta-Lipschitz bound, without differentiating exterior data.

Differentiate the positive part only off this null contact set. The difference
quotients are bounded by (1+eta)/(2v), and the extra density weight is 1/v.
On the fixed compact x domain and v interval starting at delta this is an
integrable bound. In inactive neighborhoods the positive part is identically
zero, so exterior nonsmoothness has no effect. Dominated convergence gives a
right derivative at zero, and hence the **derived actual** expansion

```math
D_{\mathrm{long}}(\sigma)=b_0+b_1\sigma+o(\sigma).
```

This does not postulate a jet in the geometric contract or require
transversality in x. Arbitrary tangencies in x and interior critical heights
are harmless to this v argument. The density is bounded, measurable and
compactly supported. The constant and linear moments in §5 imply

```math
-4\rho^2\int_0^\infty K_2(\rho\sigma/2)
 D_{\mathrm{long}}(\sigma)\,d\sigma\longrightarrow0.
```

## 4. Actual short overlap and its endpoint terms

Use disjoint small neighborhoods of **every** endpoint. The implicit function
theorem solves g=0 there as smooth moving roots in (t,r). On the compact
complement inside the positive intervals, h has a positive minimum, regardless
of its critical points. Thus that interior remains active for small parameters.
Integrating g between each pair of moving roots gives a smooth extension
F(t,r) of the actual overlap for small causal displacements. The extension
may use the raw germs just outside K; on the causal sector its positive
support is inside the original Omega by §2, so it equals V, not an alternative
observable. All endpoint neighborhoods have a common small parameter radius.

Let L0 be the total length of Omega, Q the integral of f' over Omega, and
let a-e and q-e denote the endpoint slopes from §1. Differentiation of the
moving integrals has no first-order boundary term because g=0 at their ends.
At second order it has one contribution per endpoint, including every left
and right end. The result is

```math
\begin{aligned}
F(t,r)={}&|M|-L_0t+Qr+
 \frac{r^2}{2}\int_\Omega f''(x)\,dx
 +\frac12\sum_{e\in S}\frac{(t-rq_e)^2}{|a_e|}+R(t,r),\\
|R(t,r)|&\le C(|t|+|r|)^3,&
|\nabla R(t,r)|&\le C(|t|+|r|)^2.
\end{aligned}
```

The derivative bound comes from the smooth extension's vanishing two-jet,
not from differentiating a value-only big-O estimate. Finite endpoint sums
and bounded derivatives on one compact parameter neighborhood give uniform C.
Take delta small enough that the complete short v region lies there.

Odd powers of r cancel only after summing both actual spatial directions.
Writing the even quadratic part as A times t-squared plus B2 times r-squared,
we obtain

```math
\begin{aligned}
A&=\frac12\sum_{e\in S}|a_e|^{-1},\\
B_2&=\frac12\left(\int_\Omega f''+
 \sum_{e\in S}\frac{q_e^2}{|a_e|}\right),\\
\int_\Omega f''&=-\sum_{e\in S}\frac{a_eq_e}{|a_e|},\\
A-B_2&=\frac{\mathcal J(h,f)}2.
\end{aligned}
```

The third line is the ordinary fundamental theorem of calculus on **all**
positive intervals: h' is positive at a left endpoint and negative at a right
endpoint. No exterior or artificial boundary term is discarded. This identifies
a coefficient with the previously defined normal/counting target; it does
not define the target by that coefficient.

Direct integration of the constant, linear and quadratic modes, including
the moving lower endpoint v=sqrt(sigma), gives

```math
\begin{aligned}
D_{\mathrm{short}}(\sigma)={}&
 |M|\log\frac{\delta}{\sqrt\sigma}
 -\frac{L_0}{2}\left(\delta-\frac{\sigma}{\delta}\right)\\
 &+\frac{A+B_2}{8}\left(\delta^2-\frac{\sigma^2}{\delta^2}\right)
 +\frac{A-B_2}{2}\sigma\log\frac{\delta}{\sqrt\sigma}
 +E(\sigma).
\end{aligned}
```

In particular the apparent square-root terms in the linear mode cancel
between its two null-coordinate pieces. This is why endpoint terms cannot
be estimated separately and discarded.

The remainder has a derived right first-order expansion. Indeed, the
short integrand R/v is bounded by C times v-squared on the causal parameter
triangle. Its sigma derivative is bounded by a constant: the chain-rule
factor is at most a constant divided by v, while the derivative bound on R
is of order v-squared. The lower-end omission from zero to sqrt(sigma) is
of order sigma-to-the-three-halves. To be explicit, subtract the sigma-zero
integral; divide by sigma; on v at least sqrt(sigma) apply the mean value
formula to R and dominated convergence, and on the omitted interval use
that cubic value bound. Thus

```math
\begin{aligned}
E(\sigma)&=e_0+e_1\sigma+o(\sigma),\\
D_{\mathrm{short}}(\sigma)&=
 -\frac{|M|}{2}\log\sigma+c_0+c_1\sigma
 -\frac{\mathcal J(h,f)}8\sigma\log\sigma+o(\sigma).
\end{aligned}
```

This is sufficient even at nearly null displacements. A value-only cubic
estimate, without the derivative control just used, would not justify the
right derivative or its cancellation.

## 5. Full signed cancellation and deterministic theorem

Gamma differentiation (or integration by parts with the exponential
primitives) gives four absolutely convergent moments of the **actual** K2:

```math
\begin{aligned}
\int_0^\infty K_2(z)\,dz&=0,&
\int_0^\infty zK_2(z)\,dz&=0,\\
\int_0^\infty \log z\,K_2(z)\,dz&=-\frac12,&
\int_0^\infty z\log z\,K_2(z)\,dz&=\frac12.
\end{aligned}
```

For example insert P into the integrals of z-to-the-n and
z-to-the-n times log(z), using n-factorial and n-factorial times
(H-n minus Euler's constant), for n from zero through three. The Euler
constants cancel. Absolute integrability of z times the absolute kernel,
including the logarithms at zero, justifies the substitutions and the
remainder estimates. `test_two_d.py` independently checks these exact moments;
these logarithmic integral statements are not yet new Lean theorems.

Put lambda=rho/2. With the coefficients in §4, the two nonzero signed sectors
are exactly

```math
\begin{aligned}
\int_0^\infty K_2(\lambda\sigma)
 \left(-\frac{|M|}{2}\log\sigma\right)d\sigma
 &=\frac{|M|}{4\lambda},\\
\int_0^\infty K_2(\lambda\sigma)
 \left(-\frac{\mathcal J}{8}\sigma\log\sigma\right)d\sigma
 &=-\frac{\mathcal J}{16\lambda^2}.
\end{aligned}
```

These half-line replacements of the local expansion have exponentially small
fixed-cutoff errors: away from zero the actual density is bounded and
compactly supported; the extended polynomial/log terms grow only polynomially
with a logarithm. After multiplying by rho-squared the errors still vanish.
For a local remainder r=o(sigma), given epsilon make its absolute value at
most epsilon times sigma below a fixed threshold. Rescaling bounds its
normalized contribution by a fixed multiple of epsilon times the integral of
z times absolute K2. The part above the threshold is exponentially small.
This proves the needed little-o transfer; no positivity of K2 is assumed.

The first displayed sector cancels **exactly the once-allocated point term**
in the limit calculation. The second gives the target with its full physical
normalization. The constant and linear sectors vanish by their signed moments.
At the same fixed cutoff the long term from §3 vanishes. Consequently:

**Conventional deterministic theorem.** For every fixed `SmoothTwoD h f`,

```math
\lim_{\rho\to\infty}\mathcal A_\rho(M(h,f))=\mathcal J(h,f).
```

There is no componentwise additivity premise, omitted partner set, shrinking
cutoff, asserted rate, or alteration of the unsmeared action.

## 6. Only now transfer to expectation

The geometry in §1 discharges precisely #77's
`DimensionBoundedCausalRegion.expectedAction_eq` hypotheses, using #91's
actual restricted-interval volume on every causal pair. Its finite Poisson
law and discrete action are independent definitions. For every positive rho,
`SmoothTwoD.expectedAction_eq` proves the exact equality of that expectation
with `twoDAction`. Positivity is eventual along density tending to infinity.
The deterministic theorem therefore yields the **conventional expected-action
corollary** with the same target. It supplies no variance, concentration,
rate, or convergence of an individual sprinkling. The checked equivalence
`twoDExpectedGoal_iff` alone proves neither limit.

## 7. Regressions and boundaries

- **Planar:** h=(1-x-squared)/4, f=0. Endpoints are minus one and one, each
  of weight two; the target is four. A tilted planar future f=b*x gives
  target 4*(1-b-squared) in these coordinates, not four at unchanged h.
- **Genuinely nonplanar:** the same h, f=sin(x)/8. The origin is a retained
  positive-height critical point of h; the future has nonzero second derivative
  at x=1/2. The endpoint target is 4*(1-cos(1)-squared/64). Nonemptiness,
  smooth admissibility, curvature and critical point are checked in
  `TwoDExamples.lean`; coefficient evaluation and action diagnostics are separate.
- **Disconnected:** #92's clipped exterior quartic
  h=(x-squared-1/4)*(1-x-squared)/8 inside absolute x below two, zero outside.
  The full positive set consists of (-1,-1/2) and (1/2,1); all **four**
  endpoints are included. Both critical points at signed sqrt(5/8) are retained.
  The planar target is 32, not the value obtained by choosing only the outer
  endpoints. A small sine future gives a nonplanar disconnected control.
- `two_d.py` evaluates the original intersection of both time fibres, actual
  overlap, both null directions, the fixed short/long density split and the
  full signed action. Its numerical action uses only a volume-log subtraction,
  **never the target**. The quadratures and optimizer are diagnostics on named
  fixtures, not arbitrary-input proof procedures; refinement is tested.
- Existing 3D/4D sources and normalization contracts are unchanged. Their
  standalone regressions remain in the required full source audit, and the
  existing Python baseline tests remain in the full suite.

Reproduce the diagnostics with `.venv/bin/python -m unittest -v test_two_d`.
See [the exact acceptance and validation ledger](../formal/TWO_D.md) for the
checked declarations, missing bounded Lean producers and validation receipts.
No unrestricted atlas/global-region, general-metric, null/mixed-boundary,
finite-regularity relaxation, degenerating-angle or other-dimensional theorem
is established; those obligations remain under #81/#24. Human mathematical
review is outstanding, independently of successful compiler/regression checks.
