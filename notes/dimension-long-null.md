# Actual dimensional long-null overlap: 3D first (#78)

**Delivery and verification.** This is a **written proof**, with symbolic and
numerical regressions, for the unchanged [#92 geometry](dimension-two-face-geometry.md).
It proves fixed-positive-cutoff long cancellation for every `SmoothPilot3`.
The bounded transfer test also proves it in dimensions five and six for the
**separately named C⁴ face class**, at every sufficiently small fixed positive
cutoff. It does not assert the corresponding result for arbitrary cutoffs or
for all C³ candidates. No new Lean theorem or independent human mathematical
review is claimed. The existing `dimensionKernel_transverse_cancellation`
checks the analytic implication, not this geometric input.

The canonical 3D Lean region/area port remains owned by
[#115](https://github.com/q5m-ai/causal-set-emergence/issues/115).
[#79](https://github.com/q5m-ai/causal-set-emergence/issues/79) owns the short
coefficient and remainder, and [#80](https://github.com/q5m-ai/causal-set-emergence/issues/80)
owns assembly. These written results cannot be cited as compiled inputs to
an unconditional pilot theorem. No full action limit, new expectation identity,
rate, shrinking-cutoff uniformity, or sample-wise convergence is proved here.

## 1. Frozen observable, displacement and cutoff

Use physical dimension d, spatial dimension $`n=d-1`$, product Lebesgue volume,
ordinary (not probability-normalized) area on $`S^{d-2}`$, and exactly G16 of
[#92](dimension-two-face-geometry.md#5-the-shared-action-and-two-independent-goal-propositions).
Let $`H=\max(0,h)`$, with global Lipschitz constants
$`\kappa,\eta\ge0`$ for H and f and $`\kappa+\eta\lt1`$.
The lower and upper envelopes are $`f-H`$ and f. Write

```math
\begin{aligned}
z&=y-x=(t,r\omega),&u&=t-r,&v&=t+r,&\sigma&=uv,\\
t(\sigma,v)&=\frac{v+\sigma/v}{2},&
r(\sigma,v)&=\frac{v-\sigma/v}{2},&
m&=1-\kappa-\eta>0.
\end{aligned}
\tag{L1}
```

The common sharp cutoff is **long: $`v\ge\delta`$; short: $`v\lt\delta`$**,
with fixed $`\delta>0`$. Its boundary has displacement measure zero. Define
the actual overlap and the actual long pair term before any expansion:

```math
\begin{aligned}
V_M(z)&=\int_{\mathbb R^d}1_M(p)1_M(p+z)\,dp,\\
\mathcal L_{\rho,\delta,d}
 &=-\beta_d\rho^{1+2/d}
   \int_{\substack{t\ge r\ge0\\t+r\ge\delta}}
       K_d(c_d\rho(t^2-r^2)^{d/2})V_M(t,r\omega)\,dz.
\end{aligned}
\tag{L2}
```

Constants and the signed polynomial/exponential are the existing
[dimension kernel definitions](dimension-kernels.md), not 4D coefficients
reused in a new dimension. The point term stays in the short assembly.
All source components and all future partners remain in (L2).

## 2. Exact overlap and signed disintegration

For a causal displacement $`t\ge|w|`$, the translated time interval at spatial
source x intersects the original interval in length

```math
\begin{aligned}
&\big[\min(f(x),f(x+w)-t)
 -\max(f(x)-H(x),f(x+w)-H(x+w)-t)\big]_+\\
&\qquad=\big[H(x)+f(x+w)-f(x)-t\big]_+.
\end{aligned}
\tag{L3}
```

Indeed strict Lipschitz bounds for both envelopes select the indicated upper
and lower endpoints; at the vertex the same equality holds directly. Empty
fibres cause no exception. Vertical Tonelli therefore proves (L3)'s spatial
integral equals **the independently defined** $`V_M`$. Set

```math
\begin{aligned}
g(\sigma,v;x,\omega)&=H(x)+f(x+r(\sigma,v)\omega)-f(x)-t(\sigma,v),\\
J_d(\sigma,v)&=\frac{(v-\sigma/v)^{d-2}}{2^{d-1}v},\\
B_{\delta,d}(\sigma)&=
 \int_{S^{d-2}}\int_{\mathbb R^{d-1}}
 \int_{\max(\delta,\sqrt\sigma)}^\infty
 J_d(\sigma,v)[g(\sigma,v;x,\omega)]_+\,dv\,dx\,d\omega
 \quad(\sigma\ge0).
\end{aligned}
\tag{L4}
```

Set B to zero at negative arguments. This is also exactly the overlap density
in the kernel note: applying Tonelli to (L3) moves its spatial integral back
inside the angular/long-coordinate integral. The coordinate Jacobian is

```math
dz=2^{-(d-1)}(v-u)^{d-2}\,du\,dv\,d\omega
   =J_d(\sigma,v)\,d\sigma\,dv\,d\omega.
\tag{L5}
```

The polar origin is null; in d=2 the sphere means the two counting directions.
No angle-dependent normalization is hidden in J.

Here are the analytic hypotheses **derived from geometry**, rather than
assigned to B. The bounded measurable region gives a continuous overlap:
translation continuity in L¹ of $`1_M`$, paired with its bounded indicator,
proves this, and $`0\le V_M\le |M|`$. If the spatial and time diameters of M
are bounded by D, its nonzero causal displacements have $`v\le2D`$ and
$`\sigma\le D^2`$. At a fixed positive cutoff, J is bounded on
$`\delta\le v\le2D`$, $`0\le\sigma\le v^2`$. Thus B is measurable,
nonnegative, bounded and compactly supported. Formula (L4) is pointwise,
including zero, not just an almost-everywhere representative.

For each positive density the kernel is bounded on that compact displacement
set. Both displacement and density integrals with its absolute value are
finite. Nonnegative Tonelli first, then real signed Fubini and (L5), give

```math
\mathcal L_{\rho,\delta,d}
 =-\beta_d\rho^{1+2/d}\int_0^\infty
 B_{\delta,d}(\sigma)K_d(c_d\rho\sigma^{d/2})\,d\sigma.
\tag{L6}
```

This proves the support, boundedness, measurability and **exact signed**
transport needed by the checked conditional cancellation lemma.

## 3. Uniform geometric controls, including all contacts

The following dimension-free geometric estimates are the mechanism of the
[checked 4D long proof](../formal/LONG_NULL_GAP.md), not its analytic powers.
For a causal displacement, even when the gap is exactly zero,

```math
\begin{aligned}
g\ge0&\ \Longrightarrow\ H(x)\ge mt,\quad H(x+r\omega)\ge mt,\\
g(0,w)-g(0,v)&\le-c(w-v)\quad(w\ge v),& c&=(1-\eta)/2>0,\\
-A(\tau-\sigma)&\le g(\tau,v)-g(\sigma,v)
 \le-\frac{1-\eta}{2v}(\tau-\sigma)\quad(\tau\ge\sigma\ge0),
 &A&=(1+\eta)/(2\delta),\quad v\ge\delta.
\end{aligned}
\tag{L7}
```

The first source bound follows from the upper envelope; the target bound
follows by writing the gap as target height plus lower-envelope increment
minus time. The other inequalities are direct Lipschitz finite differences.
They do not require a nonzero spatial differential of the gap.

Choose an upper endpoint $`V>\delta`$ so large that
$`H_{\max}-cV\lt-1`$. All null gaps are negative there, and the last inequality
in (L7) proves zero integrand for every $`v\ge V`$ on the right. At old active
points $`v\ge\delta`$, both endpoint heights are at least $`m\delta/2`$.
Changing sigma moves the target by at most $`\sigma/(2\delta)`$, so for a
common sufficiently small e, with $`e\lt\delta^2`$, every perturbed target
above an **old** active interval stays in the compact positive-height tube
$`H\ge m\delta/4`$. This remains true if its new gap has become negative.
Only actual smooth germs on that tube are differentiated, not H at the joint.
All relevant derivatives through order two and J's derivatives are uniformly
bounded on these compact sets. No regularity of raw h outside K is used.

The finite parameter support is
$`P=S^{d-2}\times\{H\ge m\delta/2\}`$. If the null gap at the cutoff is
nonpositive, (L7) makes the **entire right fibre zero**. This includes exact
cutoff contacts of positive parameter measure, exceptional directions, and
spatial tangencies. Off P every fibre and coefficient below is zero.

## 4. The actual 3D jet: a uniform quadratic error suffices

For a strictly positive cutoff gap, null monotonicity gives a unique old
root $`R\in(\delta,V)`$. Define $`g_0(v)=g(0,v)`$ and

```math
\begin{aligned}
a(v)&=-\frac{1+Df(x+v\omega/2)[\omega]}{2v},&
b(v)&=\frac{D^2f(x+v\omega/2)[\omega,\omega]}{8v^2},\\
d_0(v)&=\frac{1-Df(x+v\omega/2)[\omega]}2\ge c,\\
J_0(v)&=\frac{v^{d-3}}{2^{d-1}},&
J_1(v)&=-\frac{(d-2)v^{d-5}}{2^{d-1}},&
J_2(v)&=\frac{\binom{d-2}{2}v^{d-7}}{2^{d-1}}.
\end{aligned}
\tag{L8}
```

Let $`F(\sigma;x,\omega)`$ denote the v integral from delta to V in (L4).
The first two coefficients are zero on nonpositive cutoff gaps; otherwise

```math
F_0=\int_\delta^R J_0g_0\,dv,\qquad
F_1=\int_\delta^R(J_1g_0+J_0a)\,dv.
\tag{L9}
```

A Taylor estimate on the **old fixed interval** bounds the error in the
smooth integral of Jg by $`C\sigma^2`$, with one C for all parameters.
Replacing g by its positive part only changes the lost layer. On this layer,
$`g_0\le A\sigma`$, so (L7) puts it within $`A\sigma/c`$ of R, and
$`|g|\le A\sigma`$. Its weighted integral is at most
$`\|J\|_\infty A^2\sigma^2/c`$. This remains valid when the whole old
interval has closed. Hence

```math
|F(\sigma)-F_0-F_1\sigma|\le C_\delta\sigma^2\,1_P,
\qquad 0\le\sigma\le e.
\tag{L10}
```

This is stronger than the half-order remainder needed in 3D. It does **not**
assert a uniform quadratic little-o, which fails near approaching contacts.

For completeness, the pointwise second coefficient is not obtained by simply
differentiating away from contacts. In the strictly active regime it is

```math
F_2=\int_\delta^R(J_2g_0+J_1a+J_0b)\,dv
       +\frac{J_0(R)a(R)^2}{2d_0(R)}.
\tag{L11}
```

On nonpositive cutoff gaps it is zero instead. To derive the last term, put
$`v=R-\sigma s`$ in the lost layer. The gap divided by sigma tends to
$`d_0(R)s+a(R)`$ on a fixed bounded s interval. The correction is the
positive part of its negative, and its integral is the triangle area
$`a(R)^2/(2d_0(R))`$. Bounded convergence proves (L11) and the fibre's
quadratic Peano expansion. This retains the moving-contact coefficient and
its factor one-half; it is not needed to strengthen (L10) in 3D.

Joint measurability of the fibres follows from (L4). F0 is the zero probe and
F1 is the pointwise limit of measurable difference quotients along any fixed
positive sequence tending to zero. Their explicit expressions and compact
bounds give $`|F_i|\le C_i1_P`$, so they are integrable. Integrate (L10),
using the finite measure of P, to obtain the **actual** averaged jet

```math
B_{\delta,3}(\sigma)=b_0+b_1\sigma+O_\delta(\sigma^2)
                   =b_0+b_1\sigma+o(\sigma^{3/2}),
\qquad b_i=\int F_i\,d(x,\omega).
\tag{L12}
```

This proof covers every `SmoothPilot3` and every fixed positive cutoff.
Interior height critical points, all components, and non-generic translated
contacts are retained. In fact the argument only needs the corresponding C²
germs, but the named pilot and its hypotheses are unchanged.

Apply contract K with d=3, using §2 and (L12). Its two **signed** polynomial
moments vanish before absolute domination. Equation (L6) then proves

```math
\lim_{\rho\to\infty}\mathcal L_{\rho,\delta,3}=0
\quad\text{for every fixed }\delta>0.
\tag{L13}
```

No absolute estimate on the original near-null kernel would give this result.

## 5. Bounded 5D/6D transfer: make the cutoff regular, not the faces generic

Define `C4LongPilot56(d)` here to mean exactly
`CandidateTwoFace(d,4;h,f)` from #92, restricted to d=5 or d=6. This is a
**new named sufficient class**, not a modification of the old C³ candidate
or of `SmoothPilot3`. Its members include the smooth ball/sine, disconnected
ball/sine, annular and planar ellipsoid examples of #92 with their unchanged
strict budgets and all their interior critical points.

For a fixed cutoff define the geometric contact function

```math
A_\delta(x,\omega)=h(x)+f(x+\delta\omega/2)-f(x)-\delta/2.
\tag{L14}
```

It is used only near zero gaps, where both endpoints are in the positive
region by (L7), so h=H there. A sufficient **cutoff condition**, not an
admissibility field, is $`\nabla_x A_\delta\ne0`$ at every zero gap.

**Small-cutoff lemma.** For each fixed nonempty candidate with C² germs there
exists $`\delta_0>0`$ such that this condition holds whenever
$`0\lt\delta\lt\delta_0`$.

**Proof.** Compactness and nonvanishing dh on the joint give a collar
$`0\le h\le h_*`$ in K on which $`|\nabla h|\ge b>0`$; otherwise a sequence
of critical or small-gradient positive points converges to a joint point.
At a zero gap,
$`0<h(x)\le(1+\eta)\delta/2`$, so x is in this collar for small delta.
Choose a fixed neighborhood of compact K on which the raw f is C², and a
smaller positive-distance neighborhood whose Hessian is bounded by C.
For sufficiently small delta the segment from x to $`x+\delta\omega/2`$
is in that neighborhood. Consequently

```math
\left|\nabla_x A_\delta-\nabla h(x)\right|
 =|\nabla f(x+\delta\omega/2)-\nabla f(x)|\le C\delta/2.
\tag{L15}
```

Choose additionally $`C\delta/2<b/2`$. This proves a bound b/2 uniformly in
**all** directions and contact points, not just almost every direction.
If the region is empty there are no contacts and B is identically zero. ∎

For an explicit nonempty curved example in each tested dimension, take #92's
ball/sine with $`a=1/4`$ and $`\epsilon=1/8`$. At a cutoff contact,
$`|x|^2\ge1-(1+\epsilon)\delta/(2a)`$ and
$`|\nabla_x A_\delta|\ge2a|x|-\epsilon\delta/2`$.
Thus every $`0<\delta<a/(1+\epsilon)=2/9`$ is regular, in **all** directions.
The origin's height critical point remains in the region, not in this cutoff
contact set. The regression cutoff $`\delta=1/8`$ lies in this explicit range.

**Regular-cutoff integration lemma.** With C⁴ germs and a cutoff satisfying
(L14)'s regularity condition, the actual B has a C³ extension across sigma=0.

**Proof with the moving boundaries included.** Truncate v at the common V
from §3. Near the support of a nonnegative null gap, both endpoints have
uniform positive height. This also localizes all possibly positive gaps at
small *negative* sigma: the finite-difference change is bounded by
$`A|\sigma|`$, so new activity must lie in an arbitrarily small neighborhood
of that compact null-active set. A smooth localization equal to one there
therefore leaves the integral unchanged near zero and has support where h
and both future germs are C⁴. Take V with strict clearance, so there is no
upper-end contact. The only fixed boundary is $`v=\delta`$.

Cover this compact integration set by finitely many charts (including sphere
charts), and use a smooth partition subordinate to slightly larger patches.
There are three types:

1. Away from g=0 the positive part is either the smooth g or identically zero.
2. At g=0 with $`v>\delta`$, (L7) gives $`\partial_vg\le-c`$ at sigma=0.
   The parameter-dependent implicit function theorem makes g itself one
   integration coordinate. The patch is away from the cutoff.
3. At g=0 and $`v=\delta`$, (L14) supplies a nonzero spatial partial derivative.
   Use g in place of that spatial coordinate **while retaining v as a
   coordinate**. Thus the cutoff stays exactly the fixed half-space
   $`v\ge\delta`$; it is not differentiated or omitted.

The same charts work for a common small two-sided sigma interval. The
inverse maps are C⁴, and their absolute Jacobians are C³, with fixed sign of
the nonsingular determinants on each chart. After pullback and extension by
zero of the compactly supported partition weights, each integral is over a
fixed box (or fixed cutoff half-box), with integrand $`a_+`$ times a jointly
C³ compactly supported density. Here a denotes the new g coordinate and is
independent of sigma. Derivatives through order three are uniformly bounded
on a common compact box; differentiation under the integral is therefore
legitimate. Summing the finitely many patches proves the claimed C³
extension. There is no assumption about spatial transversality away from the
cutoff, and no removal of exceptional directions. ∎

Ordinary Taylor/Peano expansion now gives, at each such fixed cutoff,

```math
\begin{aligned}
B_{\delta,5}(\sigma)&=b_0+b_1\sigma+b_2\sigma^2+O_\delta(\sigma^3)
 =b_0+b_1\sigma+b_2\sigma^2+o(\sigma^{5/2}),\\
B_{\delta,6}(\sigma)&=b_0+b_1\sigma+b_2\sigma^2+b_3\sigma^3+o(\sigma^3).
\end{aligned}
\tag{L16}
```

Contract K and (L6) prove long cancellation for d=5,6 in `C4LongPilot56`, at
every sufficiently small fixed positive cutoff. C⁴ is sufficient for this
bounded test: one derivative is spent on the rectifying Jacobian. C³ only
gives C² by this proof and is **not promoted** to the required conclusion.
No theorem in other dimensions is inferred. The original smooth 3D pilot
also satisfies the regular-cutoff lemma, but does not need it for (L13).

## 6. What cannot be transferred at an arbitrary cutoff

The 4D averaging proof controls a quadratic remainder divided by sigma
squared. It cannot simply be divided by sigma cubed. Fibres with root within
$`O(\sigma)`$ of delta may already have closed, and their Taylor error is
still $`O(\sigma^2)`$. Without a measure estimate for that parameter layer,
smoothness of each interior fibre does not give the missing half/full order.
At small cutoffs §5 resolves this by a proved regular coordinate, not by
asserting generic transversality. Arbitrary positive interior heights may be
critical and cannot be handled by that collar argument.

Two explicit **contact-model negative controls**, not substituted overlaps,
retain the problematic terms. For $`0<\sigma<1`$,

```math
\begin{aligned}
\int_{-1}^1(x^2-\sigma)_+^2\,dx
 &=\frac25-\frac43\sigma+2\sigma^2-\frac{16}{15}\sigma^{5/2},\\
\int_0^1(a-\sigma)_+^2(-\log a)\,da
 &=\frac19-\frac12\sigma+\sigma^2
   +\frac13\sigma^3\log\sigma-\frac{11}{18}\sigma^3.
\end{aligned}
\tag{L17}
```

The first has a quadratic tangency in the parameter; the second a logarithmic
contact-value density. Extend each by zero above one. They are bounded
measurable compactly supported test densities. These are diagnostics of the
failed sufficient expansion, **not claims that either expression is the
complete overlap of an admissible fixed region**.

For the actual dimension kernel, writing M for the transverse moment,

```math
M_5(5/2)=-\frac18\Gamma(7/5),\qquad
M_6(3)=0,\qquad M'_6(3)=\frac1{12}\Gamma(4/3).
\tag{L18}
```

Thus a critical coefficient C multiplying sigma to the power 5/2 in d=5
contributes $`-\beta_5c_5^{-7/5}C M_5(5/2)`$ to the normalized long limit;
a coefficient C multiplying $`\sigma^3\log\sigma`$ in d=6 contributes
$`-\beta_6c_6^{-4/3}C M'_6(3)`$. Neither is silently deleted. In d=6 the first
model's fractional term is even subcritical and its normalized response
scales as $`\rho^{1/6}`$ with nonzero coefficient. The polynomial terms
cancel only by their exact signed moments. Exponential tails justify the
truncations when computing these responses.

This is **not a counterexample to the full action conjecture**. A split at a
critical cutoff may put compensating terms into short and long contributions.
A counterexample would require an admissible fixed region, its complete
normalized signed action (including the point term), and a surviving term
after full assembly. None is asserted here. Even failure of the jet need
not imply failure of long cancellation without checking its signed response.

## 7. Actual examples and executable regressions

`dimension_long_null.py` and `test_dimension_long_null.py` use the original
ball/sine family $`h=a(1-|x|^2)`$, $`f=\epsilon\sin x_1`$ with
$`2a+\epsilon<1`$. The fibre calculation independently intersects the two
actual time intervals and compares with (L3), retaining the spatial Jacobian
and the moving-root coefficient. It includes a genuinely curved future,
exact cutoff contact, a root approaching the cutoff, and the positive-height
critical center. The d=4 coefficients recover the old weight exactly.

A second independent actual-overlap control is the planar ball in each tested
dimension. With $`v_n`$ the unit n-ball volume, vertical/spatial integration
gives, for $`0\le t\le a`$ and $`r\le t`$,

```math
V_M(t,r\omega)=\frac{2v_n}{n+2}a^{-n/2}(a-t)^{(n+2)/2}.
\tag{L19}
```

Changing r to sigma **at fixed t**, rather than using (L5), gives

```math
\begin{aligned}
B_{\delta,d}(\sigma)&=\frac{S_{d-2}}2
 \int_{T_\delta(\sigma)}^a
 (t^2-\sigma)^{(d-3)/2}V_M(t)\,dt,\\
T_\delta(\sigma)&=
 \begin{cases}(\delta+\sigma/\delta)/2,&0\le\sigma<\delta^2,\\
 \sqrt\sigma,&\sigma\ge\delta^2.
 \end{cases}
\end{aligned}
\tag{L20}
```

The integral is zero when its lower bound reaches a, not an oriented negative
integral. Tests compare (L20) with the null-v integral in (L4), including both
sides of the moving lower endpoint. In d=3 this yields the complete formula
$`B_{\delta,3}=\pi^2(a-T_\delta)_+^3/(6a)`$; it is not an assumed polynomial
amplitude. Its full signed finite-density long integral is checked separately.
Tests also exercise 5D/6D Taylor remainders at regular cutoffs and the exact
fractional/logarithmic controls (L17)–(L18). These finite tests are not general
geometric proofs or an admissibility decision procedure.

## 8. Assembly and formalization handoff

| Scope | Written result here | Still required |
| --- | --- | --- |
| `SmoothPilot3`, every fixed positive cutoff | Actual signed disintegration, linear jet with quadratic error, normalized long limit zero | Integrated Lean geometry/overlap port and independent review |
| d=5,6 `C4LongPilot56`, sufficiently small fixed cutoff | Derived cutoff regularity, C³ density, sufficient respective jets and long limits | Formal port; independent short/target analysis before any global limit |
| d=5,6 C³ candidate or arbitrary cutoff | No unconditional extension from this proof | Higher-order control or complete signed obstruction accounting |
| Other dimensions | No new coverage claim | Remain open under #24/#81 |

The canonical #115 interface need only supply the geometric data proved in
#92: bounded/measurable region, strict envelope budget, positive-part overlap
identity, compact superlevel tubes and raw smooth germs there. #78's eventual
formal producer must derive B, its bounds and its jet from those data; a jet
is not a geometry field. The normalized signed transport must use the actual
`dimensionWeightedAction` conventions and ordinary sphere measure. No
uncompiled contract name in this note is a Lean theorem.

For #80's 3D assembly, choose **one** positive cutoff also meeting #79's
short-geometry smallness bounds. Equation (L13) then applies without any
uniformity as the cutoff tends to zero. A cutoff-independent short coefficient
would suffice. The short theorem and its identification with #92's independent
intrinsic target are not supplied here. Only after the deterministic assembly
may the separately proved #77 Poisson identity transfer its limit to
expectations. This does not close #24 or the unsupported-dimensional program.

### Validation and provenance

- **Written:** §§2–5, using ordinary Fubini, implicit-function, Taylor and
  compact-chart integration theorems. Independent human review is outstanding.
- **Executable:** exact algebra, actual-region quadrature and negative controls;
  diagnostic evidence only. No rates for arbitrary regions are inferred.
- **Lean:** the existing dimension cancellation theorem is conditional; no Lean
  source, checker, dependency or build input is changed by this delivery. The
  new geometric specialization is not machine checked. A subsequent formal
  port requires the full integrated `formal/check.sh` audit on its final inputs.

```sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
