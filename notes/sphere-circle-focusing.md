# Endpoint-averaged focusing on the sphere-circle slab (#139)

**GO for the antipodal-neighborhood signed estimate; NARROW the remaining
short/complement assembly. No full-action limit or counterexample.** This is a
conventional written proof, with separate finite symbolic/numerical checks,
not a Lean theorem or independent human mathematical review.

Input: [#133, section 5](general-metric-atlas-gate.md#5-f--non-conformally-flat-curvature-with-interior-focusing),
at `096cbc88f22ca39ffbc8517a9b76ac5fcf2fc732`. The metric,
region, order and observable are unchanged: `g=dt^2-h` on
`R x (S^2_1 x S^1_20)`, `M=(-2,2) x X`, circle circumference 20. The independent
bulk target is `320*pi`, and the joint is empty. We do **not** infer that target
from a local action coefficient. #81/#24, general coverage and human review
under #94/#86 remain open. No common production definitions are changed;
#134's null **boundary** branch and #137's measured-order port are separate.

The result below is deliberately about the actual endpoint-averaged cut
neighborhood. Its density is given exactly, but a pointwise quadratic jet of
that density is neither needed nor asserted. We prove a **summably dominated
cubic jet of its primitive**, sufficient for the signed kernel by integration
by parts. This avoids differentiating across a real secondary transition.

## 1. Full partners, both measures, and exact time contacts

Write `theta` for sphere endpoint distance, `b` for shortest signed circle
separation, and `tau` for time separation. At every causal pair `|b|<=tau<4`.
Every intermediate point has a unique lift to the same circle cover: two
causal lifts would differ by 20 but have total separation less than 8. Thus
intervals, not merely endpoints in convenient charts, lift injectively in the
circle direction. There is **no** analogous unique-geodesic assumption on the
sphere. Speed control and time Fubini give the actual restricted volume

```math
\begin{aligned}
V(\tau;p,q)&=\int_X(\tau-d(p,z)-d(z,q))_+\,d\mathrm{vol}_h(z).
\end{aligned}\tag{F1}
```

A Lorentz boost in the lifted time/circle plane sends the endpoint difference
`(tau,b)` to `(u,0)`, where `u=sqrt(tau^2-b^2)`. It preserves the product metric,
the full lifted interval and its volume. It need not preserve the slab; ambient
interval containment has already justified using the whole interval. Consequently
`V(tau;theta,b)=W(u,theta)`, where W is the **actual** zero-circle-separation
interval, not a geodesic or curvature model.

Source spatial volume is `4*pi*20`; target sphere polar measure is
`2*pi*sin(theta)*dtheta`; target circle measure is `db`. Integrating both endpoint
times first supplies `4-tau`, not an endpoint value. Set `C=160*pi^2`. The complete
pair integral is exactly

```math
\begin{aligned}
P(\rho)&=C\int_0^\pi\sin\theta\int_\theta^4
 G(u)K(\rho W(u,\theta))\,du\,d\theta,\\
G(u)&=2u\left[4\,\mathrm{arcosh}(4/u)-\sqrt{16-u^2}\right],\qquad 0\lt u\lt4,\\
K(v)&=(1-9v+8v^2-\tfrac43v^3)e^{-v},\\
A(\rho)&=\frac4{\sqrt6}\left(320\pi\sqrt\rho-\rho^{3/2}P(\rho)\right).
\end{aligned}\tag{F2}
```

Indeed `d tau = u/sqrt(u^2+b^2) du` at fixed b and the b range is
`[-sqrt(16-u^2),sqrt(16-u^2)]`. Its integral of
`(4-sqrt(u^2+b^2))*u/sqrt(u^2+b^2)` is G. This retains the two closing time
contacts, including the circle separations approaching `sqrt(16-pi^2)` on the
cut. No cutoff in b, or omission of cross-chart partners, was made.

For an independently fixed time cutoff `0<delta<pi`, put

```math
\begin{aligned}
G_{\mathrm{short},\delta}(u)
 &=\mathbf1_{\{u\lt\delta\}}\,2u
   \left[4\,\mathrm{arcosh}(\delta/u)-\sqrt{\delta^2-u^2}\right],\\
G_\delta(u)&=G(u)-G_{\mathrm{short},\delta}(u).
\end{aligned}\tag{F3}
```

The first line uses the displayed expression only for `0<u<delta` and is
zero otherwise. These are the exact weights of `tau<delta` and `tau>=delta`,
respectively. The factor remains **4**, not delta. The square-root contact at `u=delta` is
retained. We need a small fixed short/long cutoff, not uniformity as it moves
to the focusing time; the theorem is for every fixed `delta` in `(0,pi)` with
the cut neighborhood chosen below. Neither this cutoff nor that neighborhood
depends on density. Arbitrary cutoffs at or beyond pi are not a claimed uniform
extension of the theorem.

## 2. Exact sphere density, including the secondary branch transition

For `0<theta<pi`, let r and s be sphere distances from an intermediate point to
the endpoints. Set `x=r+s`, `y=r-s`. The two-distance map is two-to-one away
from null seams; its two spherical-triangle orientations together cover the
whole sphere. Their **combined**, not single-sheet, Jacobian is

```math
\begin{aligned}
\theta\le x\le2\pi-\theta,&\qquad -\theta\le y\le\theta,\\
J_\theta(x,y)&=
 \frac{\cos y-\cos x}
 {2\sqrt{(\cos y-\cos\theta)(\cos\theta-\cos x)}},\\
W(u,\theta)&=\int_\theta^{\min(u,2\pi-\theta)}
 \int_{-\theta}^{\theta}J_\theta(x,y)\,L(u;x,y)\,dy\,dx,\\
L(u;x,y)&=\int_x^u\frac{\sqrt{(v^2-x^2)(v^2-y^2)}}{v}\,dv,\\
W_u(u,\theta)&=\int_\theta^{\min(u,2\pi-\theta)}
 \int_{-\theta}^{\theta}J_\theta(x,y)
 \frac{\sqrt{(u^2-x^2)(u^2-y^2)}}{u}\,dy\,dx.
\end{aligned}\tag{F4}
```

To verify the Jacobian, differentiate the two distance functions: their Gram
determinant is
`(cos(r-s)-cos(theta))*(cos(theta)-cos(r+s))/(sin(r)^2*sin(s)^2)`.
Multiply its reciprocal square root by two for the two orientations and by
`1/2` for `(r,s)->(x,y)`. The range follows from the spherical triangle
inequalities, including perimeter at most `2*pi`; it covers the entire sphere.
For fixed r,s the active circle interval in F1 has width
`sqrt((u^2-x^2)*(u^2-y^2))/u`. Differentiating F1 with respect to u gives the
last line, and integration from `u=x` gives L. These formulas are positive
geometric integrals, **before** applying the signed K.

At `theta=pi-a`, the two x endpoints are `pi-a` and `pi+a`. The lower one
opens the unique minimizing endpoint geodesic when `a>0`. At `u=pi+a` the
upper endpoint saturates: the other arc of the great circle enters the
intersection geometry. It is not a second globally minimizing endpoint
geodesic for `a>0`. At `a=0` all meridians minimize. F4 retains all these
possibilities and counts spatial points, not a sum of overlapping diamonds
indexed by geodesics. W is strictly increasing and continuously differentiable
in u for `u>theta`; differentiating it three times across the upper transition
is **not** justified. The inverse needed below exists without doing that.

## 3. Independent antipodal check and the actual transition normal form

Let `D` denote the positive coefficient, not a spatial distance:

```math
\begin{aligned}
D&=\frac{8\pi}{3}\int_0^\pi\sin r
       \sqrt{\frac{2r(\pi-r)}\pi}\,dr>0.
\end{aligned}\tag{F5}
```

For antipodal endpoints F1 reads
`2*pi*integral sin(r)*(pi+epsilon-sqrt(r^2+z^2)-sqrt((pi-r)^2+z^2))_+ dz dr`.
After `z=sqrt(epsilon)*zeta`, its divided integrand tends to
`(1-pi*zeta^2/(2*r*(pi-r)))_+`. The inequality
`distance_N+distance_S>=sqrt(pi^2+4*z^2)` bounds the rescaled support uniformly;
the divided positive part is at most one. Bounded convergence on a fixed compact
domain, with the polar endpoints a null set, therefore proves independently
that `W(pi+epsilon,pi)/epsilon^(3/2)->D`. In particular `W/epsilon^2` diverges;
the one-fibre C2 inverse with a nonzero first derivative remains impossible.
For circle separation b the boost instead gives the coefficient
`D*(sqrt(pi^2+b^2)/pi)^(3/2)` in time excess at its own null arrival.

More generally, fix `A>=0`, `S>-A`. Directly in polar coordinates about the
first endpoint, the second endpoint displaced by `lambda*A` from the antipode
has sphere distance
`pi-r-lambda*A*cos(phi)+O(lambda^2)` for interior r. Rescale only the circle
coordinate by `sqrt(lambda)`. The same support argument, using that changing
an endpoint by a changes distance by at most a, supplies bounded convergence
for both the volume and its first u derivative. Thus the **actual** limits are

```math
\begin{aligned}
\lambda^{-3/2}W(\pi+\lambda S,\pi-\lambda A)
 &\longrightarrow
 \frac{D}{2\pi}\int_0^{2\pi}(S+A\cos\varphi)_+^{3/2}\,d\varphi,\\
\lambda^{-1/2}W_u(\pi+\lambda S,\pi-\lambda A)
 &\longrightarrow
 \frac{3D}{4\pi}\int_0^{2\pi}(S+A\cos\varphi)_+^{1/2}\,d\varphi.
\end{aligned}\tag{F6}
```

For the derivative use the indicator of the positive part in F1; its limiting
zero set has zero `(r,phi,zeta)` measure. Bounds are uniform on compact sets
of `(A,S)` with `S+A` bounded and positive. This is transverse **endpoint**
averaging data, not just the exact antipodal fibre. Define the first expression
at `A=1` as `F(S)`. It includes the transition at `S=1`, on both sides. In fact

```math
\begin{aligned}
F(-1+q)&\sim\frac{3\sqrt2 D}{16}q^2,\qquad q\downarrow0,\\
F(1+h)&=F(1)+F'(1)h-
 \frac{3\sqrt2 D}{16\pi}h^2\log|h|+O(h^2),\\
F(1)&=\frac{8\sqrt2 D}{3\pi},\qquad F'(1)=\frac{3\sqrt2 D}{\pi}.
\end{aligned}\tag{F7}
```

For the first line put `phi=sqrt(2*q)*v` near the opening direction. For the
second, near the closing direction `phi=pi+v`, the local integrand is
`(h+v^2/2)_+^(3/2)`. Its second derivative has singular part
`-(3*sqrt(2)/4)*log|h|` before multiplication by `D/(2*pi)`; the difference
is bounded. Two integrations give F7 on either side. This real logarithm is
why we do **not** propagate a regular single-branch derivative estimate across
that transition. The following primitive argument includes it instead.

## 4. Proved uniform regular-side bounds, not a postulated phase jet

We give the needed estimates in detail. Set `theta=pi-a`, `e=u-theta`, with
`0<a<=a0` and a0 small and fixed. Before the upper transition, `0<=e<2*a`,
the spherical two-distance map in F4 can be compared exactly with its
Euclidean-plane counterpart. Write `sinc(v)=sin(v)/v`, continuously at zero.
Their area ratio is

```math
\begin{aligned}
Q_\theta(r,s)&=
\frac{\mathrm{sinc}(r)\mathrm{sinc}(s)}
{\sqrt{
 \mathrm{sinc}((r+s+\theta)/2)\mathrm{sinc}((r+s-\theta)/2)
 \mathrm{sinc}((\theta+r-s)/2)\mathrm{sinc}((\theta-r+s)/2)}}.
\end{aligned}\tag{F8}
```

This follows by factoring the cosine differences in F4; both maps have two
orientations, so no extra factor two is introduced. In particular Q tends to
one at a Euclidean focal endpoint. Let the fixed unit Minkowski diamond be
`D0={|A|+|B|<=1/2}`, of volume `pi/24`, with `B=(B1,B2,B3)`.
The boosted/scaled flat diamond gives an **exact** formula on this regular side:

```math
\begin{aligned}
W(\theta+e,\theta)&=e^2 H(a,e),\\
H(a,e)&=(2\theta+e)^2\int_{D_0}Q_\theta(r(e),s(e))\,dA\,dB,\\
r(e)^2&=(\theta\ell+eB_1)^2+(2\theta e+e^2)B_2^2,\\
s(e)^2&=(\theta(1-\ell)-eB_1)^2+(2\theta e+e^2)B_2^2,\qquad
\ell=\tfrac12+A+B_1.
\end{aligned}\tag{F9}
```

The other transverse coordinate is the circle coordinate; Q does not depend
on it. The flat Lorentz/dilation determinant is `e^2*(2*theta+e)^2`. Mapping the
Euclidean plane by its two distances sends the **whole** flat interval to F1
when `theta+e<2*pi-theta`. Thus F9 is not a metric Taylor replacement.

Here is a uniform derivative justification, including near the focal endpoints.
On D0, `0<=ell<=1` and `B2^2<=ell*(1-ell)`. The linear coefficient in the
polynomial `r(e)^2` is bounded by `C*ell`; the quadratic coefficient is bounded.
For complex `|e|<=c*a`, a square root can consequently be chosen pointwise
within `C*|e|` of `theta*ell`: if `ell>=C1*|e|`, use the difference of squares;
otherwise both roots have size `O(|e|)`. The same holds for s near
`theta*(1-ell)`. At `e=0` the four denominator arguments in F8 are
`theta,0,theta*ell,theta*(1-ell)`. Their distance from a nonzero sine zero is
at least a. Taking c small makes each sinc factor comparable in modulus to
its value at zero, uniformly over D0.

The product of the four denominator sincs is entire and even separately in
r and s (sign changes permute the factors). It is therefore holomorphic in
`r^2,s^2`; root ambiguities at `r=0` or `s=0` are removable. That product has
no zero in the chosen complex e disk, so its positive-at-zero square root
continues there. The numerator is likewise entire in `r^2,s^2`. Moreover

```math
\begin{aligned}
Q_\theta(r(0),s(0))&=
\sqrt{\frac{\mathrm{sinc}(\theta\ell)
                  \mathrm{sinc}(\theta(1-\ell))}{\mathrm{sinc}(\theta)}}.
\end{aligned}\tag{F10}
```

Its integral is between positive constants times `a^(-1/2)`: the upper bound
is immediate, and for the lower bound restrict to a fixed positive-volume
part of D0 with `1/4<=ell<=3/4`. The complex comparison and Cauchy estimates
now show that `h(a,e)=sqrt(a)*H(a,e)` is holomorphic and uniformly bounded
on `|e|<c*a`. Its value at zero is bounded below. Shrinking a fixed `eta>0`
once gives, on `0<=e<=eta*a`,

```math
\begin{aligned}
0&\lt c_0\le h(a,e)\le C_0,\\
|\partial_e^j h(a,e)|&\le C_j a^{-j}\qquad (j=0,1,2,3,4).
\end{aligned}\tag{F11}
```

This proves the derivative bounds actually used for the inverse Taylor
expansion. It does not assume them from smoothness of the ambient metric.
One useful independent check of its leading coefficient is

```math
\begin{aligned}
H(a,0)&=\pi\theta^2\int_0^1\ell(1-\ell)
 \sqrt{\frac{\mathrm{sinc}(\theta\ell)
                  \mathrm{sinc}(\theta(1-\ell))}{\mathrm{sinc}(\theta)}}\,d\ell,\\
\sqrt a H(a,0)&\longrightarrow\frac{3\sqrt2D}{16}.
\end{aligned}\tag{F12}
```

The lightfront coordinate ell has normalized density `6*ell*(1-ell)` in D0.
This verifies the normalization independently against F7.

No derivative bound is needed outside this regular wedge. F1's endpoint
Lipschitz bound gives
`W(pi+e-2*a,pi)<=W(theta+e,theta)<=W(pi+e,pi)` when the left time is causal.
Together with F5, F11 and monotonicity, this proves, for a common fixed small
`e0>0`,

```math
\begin{aligned}
c\,\frac{e^2}{\sqrt{a+e}}
 &\le W(\pi-a+e,\pi-a)
 \le C\,\frac{e^2}{\sqrt{a+e}},\\
&0\lt a\le a_0,\qquad 0\lt e\le e_0.
\end{aligned}\tag{F13}
```

For `e<=eta*a` use F11. For `eta*a<=e<=4*a` use the value at `eta*a` for the
lower bound and the antipodal upper bound. For `e>=4*a` both antipodal bounds
apply. These three overlapping ranges cover the secondary transition `e=2*a`
and the full-meridian regime. Constants may depend on the fixed eta but never
on density, a or e.

## 5. Actual averaged density and a summable primitive jet

Choose `a0<pi-delta` sufficiently small and `e0` as in F13, also
`pi+e0<4`. Define the fixed cut neighborhood by `0<=a<=a0`, `0<=e<=e0`.
It lies entirely in the long time sector; F3 gives G there. Set **`w=sqrt(V)`**
(no factor `pi/24` in this definition). At positive phase let `U(a,w)` be the
unique root `W(U,pi-a)=w^2`. Put `E(a,w)=U(a,w)-(pi-a)`. For sufficiently small
fixed `w0>0`, all these roots have `E<e0`, including `a=0`, by F13. The exact
near-zero pushforward and its primitive are

```math
\begin{aligned}
B(w)&=C\int_0^{a_0}\sin a\,G(U(a,w))
                  \frac{2w}{W_u(U(a,w),\pi-a)}\,da,\\
N(w)&=C\int_0^{a_0}\sin a
       \int_0^{E(a,w)}G(\pi-a+t)\,dt\,da,
\qquad dN(w)=B(w)\,dw.
\end{aligned}\tag{F14}
```

Globally set E equal to e0 once `w^2>=W(pi-a+e0,pi-a)`; B is zero for that a
past this cap. No continuation of the inverse beyond its domain is assumed.
These are the actual two-measure, full-partner pushforwards. Monotone one-dimensional
substitution at each a, followed by Tonelli for the positive measure, proves
the identity. F4 gives a positive continuous `W_u` for positive excess, so no
singular atom appears at the branch transition. The null surface and `a=0`
have zero pair measure; we do not use that fact as a normalized bound.

For each `a>0`, F11 gives a right Taylor expansion of E in w. Write
`Hj=partial_e^j H(a,0)` and `gj=G^(j)(pi-a)`. Its first three coefficients and
the primitive coefficients are explicitly

```math
\begin{aligned}
\alpha_1&=H_0^{-1/2},\\
\alpha_2&=-\frac{H_1}{2H_0^2},\\
\alpha_3&=\frac{5H_1^2}{8H_0^{7/2}}-\frac{H_2}{4H_0^{5/2}},\\
c_1(a)&=g_0\alpha_1,\\
c_2(a)&=g_0\alpha_2+\tfrac12g_1\alpha_1^2,\\
c_3(a)&=g_0\alpha_3+g_1\alpha_1\alpha_2+\tfrac16g_2\alpha_1^3,\\
|c_j(a)|&\le C_j a^{1-3j/4},\qquad j=1,2,3.
\end{aligned}\tag{F15}
```

All H derivatives here come from the **exact** fixed-domain integral F9.
These are not curvature-fitted or freely prescribed density coefficients.
G is analytic on a fixed neighborhood of pi; in particular all the time-contact
and endpoint-measure terms in its first two derivatives are retained.

For completeness, the needed global remainder bound is as follows. Set
`f(a,w)=integral_0^E G(pi-a+t) dt`. On `w<=kappa*a^(3/4)`, F11 and the uniform
analytic inverse of
`w/a^(3/4)=(E/a)*sqrt(h(a,E))` give a Taylor remainder bounded by
`C*w^3*a^(-5/4)`, and divided by `w^3` it tends to zero for each fixed a.
The inverse is uniform because h is bounded above and below on a fixed disk
in `E/a`, with bounded derivatives there. In the other range F13 gives
`E<=C*(a^(1/4)*w+w^(4/3))<=C*w^(4/3)`. Therefore
`|f|/w^3<=C*w^(-5/3)<=C*a^(-5/4)`.
Every subtracted `c_j*w^j/w^3` has the same bound in that range by F15.
Multiplication by the **actual** endpoint measure proves

```math
\begin{aligned}
\left|\sin a\,
 \frac{f(a,w)-c_1(a)w-c_2(a)w^2-c_3(a)w^3}{w^3}\right|
 &\le C a^{-1/4},\\
N(w)&=n_1w+n_2w^2+n_3w^3+w^3\varepsilon(w),\\
n_j&=C\int_0^{a_0}\sin a\,c_j(a)\,da,
\qquad \varepsilon(w)\longrightarrow0,\quad |\varepsilon(w)|\le C.
\end{aligned}\tag{F16}
```

The majorant is integrable down to the exact cut. All coefficients and
remainders are measurable, since they are integrals, inverse monotone
functions or difference quotients of the displayed continuous data. Dominated
convergence proves F16. In particular no differentiability across `e=2*a`,
uniform Peano jet at `a=0`, or negligible-measure neighborhood assertion is
hidden in this argument. A bounded smooth weight in a can be included in
F14–F16, but arbitrary spacetime endpoint weights have not been proved here.

## 6. Signed response, and a resolved transition-sector diagnostic

The actual signed moments, obtained by integrating the polynomial against the
gamma density, are

```math
\begin{aligned}
M(\beta)&=\int_0^\infty v^\beta K(v)\,dv
 =-\frac43\,\beta(\beta-\tfrac12)(\beta+\tfrac12)\Gamma(\beta+1),
 \qquad \beta>-1,\\
\int_0^\infty z^jK(z^2)\,dz
 &=-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2)=0,
 \qquad j=0,1,2.
\end{aligned}\tag{F17}
```

Use F16 in `P_cut=integral K(rho*w^2) dN(w)`. The three polynomial derivatives
are killed by the three whole-half-line moments. Subtracted polynomial tails,
the boundary term at w0 and the actual cut region with `w>=w0` are exponentially
small after normalization; the latter has finite pair measure and positive
phase. For the primitive remainder integrate by parts and set
`z=sqrt(rho)*w`. Its normalized absolute majorant is a constant times
`z^4*|K'(z^2)|`, integrable at both endpoints. Pointwise `epsilon(z/sqrt(rho))`
tends to zero. This proves the written cut-neighborhood theorem

```math
\begin{aligned}
\rho^{3/2}P_{\mathrm{cut}}(\rho)&\longrightarrow0.
\end{aligned}\tag{F18}
```

This is signed cancellation, not an absolute-kernel estimate; replacing K by
its absolute value would not kill F16's lower orders. It supplies a summable
**primitive** version of #133's sufficient signed-phase interface. It does
not assert that B itself has a uniformly dominated quadratic derivative jet.

One can also resolve a genuine transverse transition sector without confusing
it with the full neighborhood. Fix `-1<s0<s1<infinity`, and take
`u=pi+a*S`, `s0<=S<=s1`, with a in a sufficiently small fixed interval. Its
boundaries are fixed in pair space, not density-dependent cutoffs. F6, F13 and
`sin(a) da du ~ a^2 da dS` show that its **volume-phase** primitive satisfies

```math
\begin{aligned}
N_{[s_0,s_1]}^{V}(v)&\sim Q_{[s_0,s_1]}v^2,\\
Q_{[s_0,s_1]}&=\frac{C G(\pi)}3
                  \int_{s_0}^{s_1}F(S)^{-2}\,dS>0,\\
\rho^{3/2}P_{[s_0,s_1]}(\rho)
 &\sim -2Q_{[s_0,s_1]}\rho^{-1/2}.
\end{aligned}\tag{F19}
```

Proof: rescale `a=v^(2/3)*t` in the sublevel integral. F13 bounds its support
uniformly and supplies `N^V(v)<=C*v^2`; F6 identifies the limit. Rescaling the
Stieltjes integral and integrating by parts then uses **`M(1)=-1`**, not a
presumed zero moment. Thus the leading sector density is `2*Q*v` in the
weak/primitive sense used here, and its signed normalized pair response is
negative but decays. The pair contribution to A has the opposite sign.
F19 applies also across `S=1`; the logarithm of F7 is included in F and is
integrable there. It must **not** be extrapolated through `S=-1`, where
`F(S)^(-2)` is nonintegrable. The unique-minimizer matching wedge there is
handled by F9–F16, not discarded. The unaveraged fractional inverse
`E~w^(4/3)` therefore creates no surviving normalized term in this fixed
cut-neighborhood theorem. No full-action rate is asserted by this diagnostic.

## 7. Exact complement and the subsequent bounded prerequisites

Let `I(H;D)` mean the right side of F2 with weight H on the specified
`(theta,u)` domain. Splitting the original time/pair domain disjointly gives
the following exact weighted equality at **every** positive density (the two
time weights can have overlapping support after b integration):

```math
\begin{aligned}
P&=P_{\mathrm{short},\delta}+P_{\mathrm{cut}}+P_{\mathrm{offcut},\delta}
                                  +P_{\mathrm{excess}},\\
P_{\mathrm{short},\delta}&=I(G_{\mathrm{short},\delta};\ 0\le\theta\le\pi,
                                                     \ \theta\le u\le4),\\
P_{\mathrm{offcut},\delta}&=I(G_\delta;\ 0\le\theta\le\pi-a_0,
                                                     \ \theta\le u\le4),\\
P_{\mathrm{excess}}&=I(G;\ \pi-a_0\le\theta\le\pi,
                                                     \ \theta+e_0\le u\le4).
\end{aligned}\tag{F20}
```

P_excess has a positive phase minimum by continuity and compactness, hence an
exponentially small normalized tail. P_offcut and P_short do **not**: they
still contain genuine nearly-null pairs. In particular `theta,u->0` with
nonzero b can be long in the original time separation. The boost reduction
must not silently relabel all these pairs short. The contact at `u=delta` in
F3 and every fixed artificial boundary in F20 must be restored in any later
assembly. No local action is assigned to an isolated chart or counted twice;
any future finite source/target partition requires the entire ordered double
sum, including off-diagonal labels.

The resulting downstream contracts are now bounded by a proved producer,
not by unproved asymptotic admissibility fields:

```text
F-short/complement (written first; next analytic prerequisite):
  input: exactly this product/slab, actual W and G_short,delta / G_delta;
         one fixed 0<delta<pi and compatible a0,e0 from this note
  derive: actual small-(theta,u) short response with physical point term;
          signed off-cut long estimate including u=delta contacts and
          theta,u->0 long-circle partners; restore every F20 boundary
  identify: the complete surviving coefficient against independent R/2,
            not just the scalar part of a local interval expansion

F-assembly (only after that producer):
  input: that matched short/complement proof plus F18 and the excess tail
  output: a complete deterministic conclusion, or a complete-action obstruction
  expected-action transfer: separately instantiate the actual measured order;
    #137 is needed for a later compiled bridge, not for the written F18 proof
```

**Decision: GO cut cancellation; NARROW to this matched short/complement
producer; STOP any formal full-limit task with those premises unproved.**
An isolated sector, failed sufficient estimate or missing producer is not a
counterexample to the action. No complete deterministic or expected limit,
shrinking-cutoff uniformity, general metric/atlas coverage, or sample-wise
convergence is claimed. No merge or closure of #81/#24 is authorized.

## 8. Verification boundary and reproduction

`sphere_circle_focusing.py` and `test_sphere_circle_focusing.py` check the exact
two-distance Jacobian and circle primitive against independent polar
integration, nonzero circle separation and boost reduction, both sides of the
secondary transition, the antipodal coefficient, the regular-side comparison,
the averaged primitive, signed moments, time-contact and exact-complement
accounting. Finite regressions are evidence, not proofs of F11/F16/F18.

```sh
.venv/bin/python -m unittest -v test_sphere_circle_focusing
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

No Lean source, checker, dependency or build input changes. No fresh Lean audit
is necessary or claimed. Markdown authoring checks and browser-rendering checks
are separate; the PR records their observed results and its bounded review
snapshot. Independent human mathematical review remains outstanding.
