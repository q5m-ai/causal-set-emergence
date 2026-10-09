# Matched 4D sphere-circle short and off-cut producers (#152)

**Written signed producers for #153, not an assumed full-limit interface.**
The result is for exactly the unit round sphere times the circumference-20
circle, with metric `dt^2-h`, slab `(-2,2) x X`, and the selected ambient
order. The action, geometric target and Poisson law are unchanged. This is a
conventional proof with separate finite checks, not a Lean theorem or
independent human mathematical review. It makes no inference from PR #159 or
from a calculation in another dimension.

Input: the accepted [#139 producer](sphere-circle-focusing.md), F1–F20,
in merge `0bfc8bb3d6dce188c39414fedef5e0a3bd646dd5`, contained in the starting
integration head `b86f5dadddaeb6a11299557ff28781e9b33ed743`. Administrative
issue closure is not the input. Its cut estimate is used only on its actual
aggregate pair domain, not on arbitrary weighted atlas cells. No common
production definition is edited.

## 1. Constants, signs, both measures, and the exact domain

Keep F2's kernel K and pair constant C. Write c for the flat interval constant,
r for the **three-dimensional spatial product distance**, and m for the
circle component of its unit direction. These are not the two sphere distances
r,s in F4/F8. Off the antipodal cut, sphere normal polar coordinates and the
unique circle lift give

```math
\begin{aligned}
c&=\frac\pi{24},& C&=(4\pi\cdot20)\,2\pi=160\pi^2,\\
k&=1-m^2,& \theta&=r\sqrt{k},& b&=rm,\\
q&=\tau^2-r^2,& y&=\theta^2=kr^2,& u^2&=y+q,\\
d\mathrm{vol}_h(\text{target})
 &=2\pi r^2\,\mathrm{sinc}(r\sqrt{k})\,dr\,dm,
 &-1&\le m\le1,\\
P_D(\rho)&=C\int_D(4-\tau)r^2\mathrm{sinc}(r\sqrt{k})
 K\bigl(\rho W(\sqrt{y+q},\sqrt y)\bigr)\,d\tau\,dr\,dm.
\end{aligned}\tag{SC1}
```

The source spatial measure is the full `4*pi*20`; integrating both source and
target times gives **`4-tau`**. The circle representatives satisfy `|b|<4<10`,
and F1's interval lifting, not a same-chart restriction, justifies this
coordinate change. At m equal to either endpoint the sphere polar axis is
removable; the sinc and phase below are analytic in y there. No direction is
removed.

Choose **one sufficiently small positive delta**, once and for all, below the
analytic radius established in section 2 and below 1/4. Never send it to zero
with density. Choose a0,e0 from F11–F13, smaller if necessary so that
`d=pi-a0>delta` and `pi+e0<4`. These are likewise fixed. Short means
`tau<delta`; equality belongs to long. The off-cut long domain is exactly
`delta<=tau<=4`, `theta<=d`, `r<=tau`. The cut and excess domains are exactly
F20, not smoothed replacements. Thus at every positive density

```math
\begin{aligned}
P&=P_s+P_c+P_o+P_e,\\
S_\delta(\rho)&=\frac4{\sqrt6}
 \left(320\pi\sqrt\rho-\rho^{3/2}P_s(\rho)\right),\\
L_o(\rho)&=-\frac4{\sqrt6}\rho^{3/2}P_o(\rho),\qquad
L_c(\rho)=-\frac4{\sqrt6}\rho^{3/2}P_c(\rho),\\
L_e(\rho)&=-\frac4{\sqrt6}\rho^{3/2}P_e(\rho),\qquad
A=S_\delta+L_o+L_c+L_e.
\end{aligned}\tag{SC2}
```

The physical point belongs **once** to S. These signs matter: the signed
long action is minus the signed pair integral. SC1 is also exactly F2/F3
before integrating b; in particular `theta,u -> 0` with `b` bounded away
from zero is still long when its original time exceeds delta.

## 2. An actual regular-side phase, including the polar origin

There are a positive q0 and an analytic function H on a neighborhood of
`[0,d^2] x {0}` such that

```math
\begin{aligned}
W(\sqrt{y+q},\sqrt y)&=c q^2 H(y,q),\qquad 0\le y\le d^2,
 \quad 0\le q\le q_0,\\
H(y,0)&>0,\qquad H(0,0)=1,\\
H(y,q)&=1+\frac y{30}-\frac q{90}+O((|y|+|q|)^2)
 \quad\text{near }(0,0).
\end{aligned}\tag{SC3}
```

Here and below analytic means a convergent real power series with a
holomorphic extension to a smaller complex neighborhood. In particular the
remainders have bounded derivatives there; these are not just metric Taylor
remainders. The following construction proves SC3 from the actual interval.

Use the exact area ratio in F8, denoted here by Qs, on the fixed four-dimensional
unit rest diamond D0 of volume c. Set `theta=sqrt(y)`, `u=sqrt(y+q)` and

```math
\begin{aligned}
r_s^2&=\bigl(\theta(\tfrac12+A)+uB_1\bigr)^2+qB_2^2,\\
s_s^2&=\bigl(\theta(\tfrac12-A)-uB_1\bigr)^2+qB_2^2,\\
H(y,q)&=\frac1c\int_{D_0} Qs_\theta(r_s,s_s)\,dA\,dB.
\end{aligned}\tag{SC4}
```

This is F9 divided by `c*(2*theta+e)^2`, with
`q=e*(2*theta+e)`, so it is exact whenever `u<2*pi-theta`. Choose q0 small
enough to ensure that inequality on the entire compact interval `theta<=d`.
At theta zero the limiting two-distance map is interpreted by continuity;
the positive integrals, or directly F1 in polar coordinates, give the same W.

Here is the analytic justification at the potential coordinate singularities.
The product of the four denominator sincs in F8 is entire and even separately
in theta, r_s and s_s: sign changes permute the four factors, using the
evenness of sinc. The numerator is even in r_s and s_s too. For q zero and
`theta<=d<pi` this product is positive on D0, bounded away from zero on that
compact set. Its square root therefore continues on a common neighborhood;
root ambiguities in r_s and s_s are removable. Near theta=u=0 the resulting
integrand is holomorphic in theta,u. Reflection of B1 makes its integral even
separately in theta and u. Its convergent series is consequently a series in
`theta^2,u^2`, hence in y,q. For theta away from zero, F9 and compactness give
the same analytic extension in q. These overlapping neighborhoods prove
SC3, with uniform derivative bounds and positive lower bound for H. No
analyticity through the antipodal transition is being asserted.

For the second jet, expansion of the **exact** F8 ratio gives
`Qs=1+(theta^2-r_s^2-s_s^2)/12+O((|theta|+|u|)^4)`.
Normalized rest-diamond moments are
`<A^2>=1/60`, `<B_i^2>=1/30`, `<A B_1>=0`.
Thus `<theta^2-r_s^2-s_s^2>=2*y/5-2*q/15`, proving both coefficients in
SC3. All sphere Ricci-direction dependence is retained; replacing this by a
scalar-curvature-only interval model would change the calculation.

Use the phase **v**, distinct from F14's w:

```math
\begin{aligned}
v&=\sqrt{W/c}=q\sqrt{H(y,q)},\qquad w=\sqrt c\,v,\\
q&=Q(y,v),\qquad
Q_v(y,v)=\left(\sqrt H+\frac{qH_q}{2\sqrt H}\right)^{-1}_{q=Q(y,v)},\\
Q(y,v)&=v-\frac{yv}{60}+\frac{v^2}{180}
       +O\bigl(v(|y|+|v|)^2\bigr).
\end{aligned}\tag{SC5}
```

The analytic implicit function theorem and the positive lower bound for H
supply a common v0 and bounded derivatives of Q of every fixed order on
`[0,d^2] x [0,v0]`. Also `Q(y,0)=0`, `Q_v>0`, and Q is comparable to v.
One may use a slightly larger y interval still below pi squared for boundary
charts. Choose the delta in section 1 small enough that all the origin
coordinate changes below are analytic on a complex disk containing
`0<=r^2<=2*delta^2`. Choose v0 smaller thereafter, not delta. Any excluded
part with phase at least v0 has finite pair mass and a positive phase gap;
this also covers later secondary transitions outside the regular collar.

## 3. Off-cut long density: all directions and all moving contacts

SC1 and SC5 give the **actual** near-zero phase density

```math
\begin{aligned}
f(r,m,v)&=r^2\mathrm{sinc}(r\sqrt{1-m^2})Q_v((1-m^2)r^2,v)
 \left(\frac4{\sqrt{r^2+Q((1-m^2)r^2,v)}}-1\right),\\
R_T(m,v)^2+Q((1-m^2)R_T(m,v)^2,v)&=T^2,\qquad T\in\{\delta,4\},\\
R_d(m)&=\frac d{\sqrt{1-m^2}},\qquad
m_*(v)=\sqrt{1-\frac{d^2}{16-Q(d^2,v)}},\\
B_o(v)&=C\left[
 \int_0^{m_*(v)}\int_{R_\delta(m,v)}^{R_d(m)} f(r,m,v)\,dr\,dm
 +\int_{m_*(v)}^1\int_{R_\delta(m,v)}^{R_4(m,v)} f(r,m,v)\,dr\,dm
 \right],\\
P_o(\rho)&=\int_0^{v_0}K(c\rho v^2)B_o(v)\,dv
             +\text{positive-phase tail}.
\end{aligned}\tag{SC6}
```

The factor C, rather than C/2, in B_o includes the two signs of m. R4 is only
needed in the second integral, where its sphere coordinate is below d.
Rdelta is below d for every direction. Shrinking v0 once makes all these
claims strict with fixed margins. At zero phase m_* is strictly between zero
and one. Rdelta is at least delta/2, so f has no origin singularity here,
including at m=1. The radial root derivative is `2*r+O(v)` and is bounded
away from zero at either time contact. The moving intersection of the
artificial sphere boundary with the upper time boundary has the explicit
smooth root m_* in SC6. Every integral can therefore be transported to fixed
unit intervals by its displayed endpoints, with uniformly bounded derivatives
through third order (indeed it is analytic).

For clarity, this does **not** differentiate the square-root cusp of F3 at
`u=delta` while keeping theta fixed. It integrates the original long-time
domain first. The moving Rdelta includes exactly that contact. At m near one
and r between Rdelta and R4, theta tends to zero while `b=rm` remains long;
these partners are in SC6, not reclassified as short. At the upper time
contact f is zero because `4/tau-1=0`, but its derivatives need not be zero.

Here is an explicit coefficient prescription that retains every boundary
term. If `J(m,v)=integral_l^h f(r,m,v) dr`, take its derivatives at fixed m:

```math
\begin{aligned}
J_v&=\int_l^h f_v\,dr+f(h)h_v-f(l)l_v,\\
J_{vv}&=\int_l^h f_{vv}\,dr
 +[2f_vh_v+f_rh_v^2+fh_{vv}]_{r=h}
 -[2f_vl_v+f_rl_v^2+fl_{vv}]_{r=l}.
\end{aligned}\tag{SC7}
```

Apply the **same** formulas again to the outer m integrals, with their
endpoints 0,m_*(v),1 and with the corresponding J as integrand. That defines
`b_j=B_o^(j)(0)/j!`, for j=0,1,2, directly from SC4–SC7. In particular it
includes the time-root accelerations and the outer moving-contact terms,
not only integrals of the interior derivatives. The two J values agree at
m_*, so the first outer boundary terms cancel; one may not infer that every
term in the second derivative separately vanishes. Bounded third derivatives
on the fixed rectangles now prove

```math
\begin{aligned}
B_o(v)&=b_0+b_1v+b_2v^2+v^2\epsilon_o(v),\\
|\epsilon_o(v)|&\le C_o v,\qquad
\rho^{3/2}P_o(\rho)\longrightarrow0,\qquad L_o(\rho)\longrightarrow0.
\end{aligned}\tag{SC8}
```

This is an actual signed producer, not the claim that such b_j might exist.
Their prescription is by derivatives of exact compact integrals; all are
measurable and summable. F17's three zero moments kill their whole-half-line
polynomials. For the remaining density set `z=sqrt(c*rho)*v`; the normalized
majorant is a constant times `z^2*|K(z^2)|`, and the factor epsilon_o tends to
zero. The removed polynomial tails and actual positive-phase tail are
exponentially small. Taking the absolute kernel **before** subtracting the
polynomial would not prove SC8.

## 4. Short density: the exact origin singularity and its two logarithms

For short time the sphere cutoff is inactive. In the same phase the exact
density is

```math
\begin{aligned}
B_s(v)&=\frac C2\int_{-1}^1\int_0^{R_\delta(m,v)}
 r^2\mathrm{sinc}(r\sqrt{k})Q_v(kr^2,v)
 \left(\frac4{\sqrt{r^2+Q(kr^2,v)}}-1\right)\,dr\,dm,\\
P_s(\rho)&=\int_0^{v_0}K(c\rho v^2)B_s(v)\,dv
               +\text{positive-phase tail}.
\end{aligned}\tag{SC9}
```

This retains both times through the same factor `4-tau`; the density is not
a single-source full-cone action. The integral of the minus-one term is
analytic in v, including its moving upper root, since Q, sinc and Rdelta
are analytic and the radial lower endpoint is zero. All its terms through
quadratic order must be kept until the signed moments remove them. In
particular one must not first discard the two spacelike-face contacts.

For the term with the square root, set `t(v)=Q(0,v)`. This t is an auxiliary
squared length, **not** the source time. Make the exact radial change

```math
\begin{aligned}
s^2&=r^2+Q(kr^2,v)-t(v),\qquad r^2=s^2 F(s^2,m,v),\\
t(v)&=v+\frac{v^2}{180}+O(v^3),\qquad
F(s^2,m,v)=1+\frac{kv}{60}+O(vs^2+v^2),\\
A(s^2,m,v)&=\mathrm{sinc}(r\sqrt{k})Q_v(kr^2,v)
 \sqrt F\,(F+s^2F_{s^2}),\\
A(s^2,m,v)&=1-\frac{11k}{60}s^2
  +\left(\frac1{90}+\frac{k}{40}\right)v
  +O(s^4+s^2v+v^2),\\
\int_0^{R_\delta}\frac{r^2\mathrm{sinc}(r\sqrt{k})Q_v}{
 \sqrt{r^2+Q}}\,dr
 &=\int_0^{\sqrt{\delta^2-t(v)}}
       \frac{s^2 A(s^2,m,v)}{\sqrt{s^2+t(v)}}\,ds.
\end{aligned}\tag{SC10}
```

The quotient defining s squared divided by r squared has a removable origin,
since `Q(kr^2,v)-Q(0,v)` is divisible by r squared. It equals `1+O(v)`
uniformly. The analytic inverse theorem gives F and all needed derivative
bounds on a common disk, uniformly in m. The upper endpoint is exactly
`sqrt(delta^2-t(v))`, independent of m: the moving short-time contact is
straightened, not frozen. The factor `sqrt(F)*(F+s^2*F_{s^2})` is the full
radial Jacobian. SC3–SC5 yield every coefficient displayed in SC10.

### A summable remainder lemma, not a truncated local model

For analytic A as just constructed, put
`I_n(t)=integral_0^sqrt(delta^2-t) s^(2*n+2)/sqrt(s^2+t) ds`.
The substitution `s=sqrt(t)*sinh(x)`, or integration of
`(s^2+t)-t`, proves that each I_n is an analytic function of t near zero
plus a single multiple of `t^(n+1)*log(t)`. In particular

```math
\begin{aligned}
I_0(t)&=\frac12\left[
 \delta\sqrt{\delta^2-t}
 -t\log\frac{\delta+\sqrt{\delta^2-t}}{\sqrt t}\right],\\
I_0(t)&=\text{analytic part}+\frac t4\log t,\qquad
I_1(t)=\text{analytic part}-\frac{3t^2}{16}\log t,\\
I_{-1}(t)&=\log\frac{\delta+\sqrt{\delta^2-t}}{\sqrt t},\\
I_n(t)&=\frac{\delta(\delta^2-t)^{n+1/2}}{2n+2}
 -\frac{2n+1}{2n+2}t I_{n-1}(t),\qquad n\ge0.
\end{aligned}\tag{SC11}
```

Here is why the entire higher-order remainder, not just two monomials, is
controlled. Choose delta small enough that A's series in s squared converges
absolutely on a disk of radius strictly greater than `4*delta^2`, uniformly
in m and complex v in a smaller disk. Cauchy estimates bound its n-th
coefficient and its first three v derivatives by `M*R^(-n)`, with
`R>4*delta^2`. The above recurrence for I_n has logarithmic coefficient
`(-1)^n*binomial(2*n+2,n+1)/2^(2*n+3)` and an analytic part bounded by a
constant times a polynomial in n times `(2*delta^2)^(n+1)` on a smaller complex
t disk: on `|t|<=delta^2/4`, use `|delta^2-t|<=5*delta^2/4`
in the displayed recurrence and then a geometric-series bound. Cauchy
estimates on a smaller disk give the same normal convergence for the required
derivatives. Consequently both sums converge normally. The whole integral is
`U(m,v)+V(m,v)*log(v)`, with analytic U,V and uniform bounds; use the analytic
identity `log(t(v))=log(v)+log(t(v)/v)`. In V, terms n at least two start at
v cubed; the omitted coefficients in SC10 likewise contribute only v cubed
or higher to V. U includes **all** their nonzero constant, linear and quadratic
terms. Subtracting its actual quadratic Taylor polynomial gives a remainder
bounded by `C*v^3*(1+|log(v)|)`, uniformly in m. This bound is integrable in m;
its quotient by v squared tends to zero. This proves the required Peano
remainder for the actual interval integral without ignoring any interior
Taylor terms or differentiating an unbounded raw origin fibre.

Using SC10–SC11, the two logarithmic coefficients in each radial integral are

```math
\begin{aligned}
\bigl[v\log v\bigr]&=\frac14,\\
\bigl[v^2\log v\bigr]&=\frac1{720}
 +\frac14\left(\frac1{90}+\frac{k}{40}\right)
 +\frac{33k}{960}
 =\frac1{240}+\frac{13k}{320},\\
\int_{-1}^1 k\,dm&=\frac43,\\
B_s(v)&=a_0^{s}+a_1^{s}v+a_2^{s}v^2
       +C v\log v+\frac C8 v^2\log v+v^2\epsilon_s(v),\\
|\epsilon_s(v)|&\le C_s v(1+|\log v|),\qquad \epsilon_s(v)\longrightarrow0.
\end{aligned}\tag{SC12}
```

The symbols a_j with superscript s are analytic-part coefficients, not the
cut width a0. They are the Taylor coefficients of the full U integral and
minus-one term of SC9, with factor C/2; they are not fitted parameters or
admissibility assumptions. The factor 4 in SC9 gives `2*C` times the radial
integrals in SC10. It is responsible both for C and C/8 in SC12. Both endpoint
measures, the phase correction, the radial Jacobian and the moving time
contact were needed to obtain those numbers.

## 5. Actual signed short output and independent bulk normalization

Differentiating the **four-dimensional** F17 moment identity gives

```math
\begin{aligned}
J(j)&=\int_0^\infty z^j K(z^2)\,dz
   =-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2),\\
J(0)&=J(1)=J(2)=0,\qquad J'(1)=\frac1{12},\qquad
J'(2)=-\frac{\sqrt\pi}{12},\\
\int_0^\infty v\log v\,K(c\rho v^2)\,dv&=\frac1{12c\rho},\\
\int_0^\infty v^2\log v\,K(c\rho v^2)\,dv
 &=-\frac{\sqrt\pi}{12(c\rho)^{3/2}}.
\end{aligned}\tag{SC13}
```

Gamma differentiation is valid on a neighborhood of j=1,2 by an integrable
log-weighted majorant. Rescale SC12 as in section 3. Its remainder is dominated
after normalization by `const*z^2*|K(z^2)|` because epsilon_s is bounded,
and tends pointwise to zero. The analytic polynomial, log-polynomial tails,
and positive-phase tail are treated separately; each tail is exponentially
small. Thus no divergent `log(rho)` term has been dropped: its coefficient is
exactly J(1) or J(2), zero. The actual signed producer is

```math
\begin{aligned}
P_s(\rho)&=\frac{320\pi}{\rho}
     -\frac{80\sqrt6\,\pi}{\rho^{3/2}}+o(\rho^{-3/2}),\\
\rho^{3/2}P_s(\rho)-320\pi\sqrt\rho&\longrightarrow-80\sqrt6\,\pi,\\
S_\delta(\rho)&\longrightarrow320\pi.
\end{aligned}\tag{SC14}
```

The first coefficient uses `C/(12*c)=320*pi`; it cancels the physical point
with its **actual** sign in SC2. The second uses
`C*sqrt(pi)/(96*c^(3/2))=80*sqrt(6)*pi`. SC14 is independent of the chosen
sufficiently small fixed cutoff because all cutoff-dependent analytic
coefficients are removed by the signed moments, not by taking delta to zero.

For an independent target check, in a regular product chart the only nonzero
sphere Christoffel symbols are `Gamma^theta_phi,phi=-sin(theta)*cos(theta)`
and `Gamma^phi_theta,phi=Gamma^phi_phi,theta=cot(theta)`. Contract with
[#90's curvature convention](general-contract.md#2-independent-action-order-and-geometric-target)
(the sign opposite the usual positive-sphere contraction after the Lorentzian
metric signs). The sphere Ricci components are `-1,-sin(theta)^2`, the time
and circle components zero, and contraction with
`diag(1,-1,-1/sin(theta)^2,-1)` gives R=2. Consequently

```math
\begin{aligned}
\mu_g(M)&=4\,(4\pi\cdot20)=320\pi,\qquad
\frac12\int_M R_g\,d\mu_g=320\pi,\qquad J=\varnothing.
\end{aligned}\tag{SC15}
```

This curvature computation does not use SC3, the action, or its limit. The
finite regression reuses the independent connection contraction in
`general_metric_gate.product_curvature`; agreement with SC14 is an output,
not a definition of the target. There is no timelike-boundary extension here.

## 6. F20 restoration, signed handoff and acceptance map

The cut producer uses phase w; this note uses v. The conversion is **exactly**
`w=sqrt(c)*v`. Choose v0 also so that `sqrt(c)*v0` is below F14's fixed
phase cap; both proofs then use exactly the rescaling `z=sqrt(c*rho)*v`.
F16 remains a cubic primitive with integrable `a^(-1/4)` domination after
conversion. Neither its artificial a0 boundary nor
its e0 cap changes. It proves `rho^(3/2)*P_c -> 0` and thus `L_c -> 0`.
The excess domain is compact with `e>=e0>0`; continuity and positivity of the
actual W give a minimum nu greater than zero. With finite pair mass,
`|K(rho*W)| <= const*(1+rho^3)*exp(-rho*nu)`, proving the normalized excess
tail tends to zero. No transition-volume model is substituted in that tail.

| Boundary or partner set | Exact retention before taking any limit |
| --- | --- |
| Physical diagonal and point | SC9–SC14; point once in SC2, both logarithms retained |
| `tau=delta`, including `u=delta` in F3 | Rdelta in SC6 and SC9, SC7 derivatives, and the exact upper root in SC10; same strict-short/equality-long split |
| Long circle-nearly-null partners at `theta,u -> 0` | m near either endpoint and r at least delta/2 in SC6; no small-u short allocation |
| Closing slab time `tau=4` | R4 and factor `4/tau-1` in SC6, including their derivatives |
| Sphere boundary `theta=d=pi-a0` | Rd and its moving upper-time intersection m_* in SC6; unchanged lower edge of F14 |
| Cut cap `u=theta+e0` | Actual capped primitive in F14 and the complementary excess in F20 |
| Secondary transition and all minimizing meridians | Accepted F13–F18, not a regular off-cut jet through the transition |
| Circle seams and endpoint chart labels | Whole spatial source volume and both m signs in SC1; only the complete ordered partition sum may be restored before using symmetry |

The finite-density equality SC2 is **exactly** F20. Null equality boundaries
have zero pair measure for that identity; their neighboring integrals and
moving derivatives were not discarded on that account. At the common phase
cap v0 the actual density/primitive boundary and every subtracted polynomial
or logarithmic tail are retained until their positive-phase estimate. No
internal boundary is declared negligible without one of these estimates.

### Actual #153 producer receipt

- **Short:** SC14, with physical point and independent comparison SC15.
  Actual density remainder SC12 is bounded after division by v squared and
  tends to zero; uniform origin-parameter domination is proved in section 4.
- **Off-cut long:** SC8 with SC4–SC7's actual phase and contact derivatives;
  a bounded third derivative on finite rectangles supplies a summable
  quadratic density remainder. This includes all long circle partners.
- **Cut:** accepted F18, with F16's summable primitive remainder and the exact
  phase conversion above. Its signed moment proof, not merely F19's
  isolated transition-sector diagnostic, is the input.
- **Excess:** actual positive-phase minimum and finite pair-mass bound above.
- **Assembly:** SC2 restores the four pair domains and point exactly, at one
  fixed compatible cutoff. These are unconditional written sector outputs
  for this fixed geometry; #153 need not assume any density jet or cancellation.

#153 owns the complete deterministic statement, its geometric admissibility
receipt and the **separate** expectation transfer through the accepted #137
measured-order bridge and the original Poisson law. No expected-limit equality
is assumed here, and there is no sample-wise conclusion. No failed sector is
called a counterexample. #81/#24's general coverage, #94's independent human
review and #86's actual formal-verification gap remain open. This example
provides no arbitrary-dimension, arbitrary-weighted-cell or general-caustic
theorem; no scope change to #24 is proposed.

## 7. Verification boundary

`sphere_circle_complements.py` and `test_sphere_circle_complements.py` evaluate
the actual fixed-diamond phase and its derivative, invert that phase, compare
independent densities with the original F3 contact weights, and check the
origin logarithms, signed normalization and exact finite-domain accounting.
They are finite regressions, not proofs of uniform analytic bounds. The
written analytic and summability arguments are sections 2–5; independent
human acceptance and compiled verification remain distinct.

```sh
python -m unittest -v test_sphere_circle_complements test_sphere_circle_focusing
python sphere_circle_complements.py
python check_symbolic.py
python -m unittest -v
python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

No Lean source, checker, dependency or build configuration is changed; no
fresh Lean audit is necessary or claimed. The PR records observed local,
GitHub-rendering and CI checks, separately from mathematical acceptance.
No agent launch, merge, deployment, automatic closure or shrinking cutoff.
