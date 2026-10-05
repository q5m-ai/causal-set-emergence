# Actual 5D/6D short responses and matched contracts (#132)

**Decision: go on the named C⁴ classes below; narrow, not general coverage.**
This is a conventional written short proof, with symbolic/numerical regressions
and bounded assembly/formalization prerequisites. It is **not a new Lean
result**, an independent human review, or completion of #81/#86/#24.

The research base is `origin/issue-81-general-coverage` pinned at
`d41a062aba04552f1db42e9f3d59cb242ec6ed09`. Inputs are
[#92's independent geometry](dimension-two-face-geometry.md),
[#78's C4LongPilot56 long-only theorem](dimension-long-null.md#5-bounded-5d6d-transfer-make-the-cutoff-regular-not-the-faces-generic),
and [#79's transfer ledger](dimension-three-short.md#7-regressions-and-transferobstruction-ledger).
The latter's power counts are **not** assumed estimates: §5 derives them from
the actual overlap, including its moving lower endpoint. Historical delivery
statements in those notes retain their original scope.

## 1. Precise classes, observable and cutoff match

Use exactly #92's `CandidateTwoFace(d,r;h,f)` (G1), not independent envelopes:

```text
C4ShortPilot5(h,f) := CandidateTwoFace(5,4;h,f).
C4ShortPilot6(h,f) := CandidateTwoFace(6,4;h,f).
```

In each case the positive region is bounded; the clipped height H and future f
have global Lipschitz constants kappa and eta with kappa+eta strictly below one;
h and f have ambient C⁴ germs near the whole closed positive region; dh is
nonzero at every zero there. Interior height critical points, all components,
and all inner boundaries are retained. Exterior zeros are not joint points.
There is no density, asymptotic, or integral field in either class. These are
exactly the respective dimensional slices of **C4LongPilot56**, not stronger
unnamed assumptions on the old C³ contracts. Smooth members are included.
C⁴ is sufficient here, not claimed necessary: 5D short alone uses only C³,
whereas this 6D proof uses a bounded fourth primitive derivative.

Write spatial dimension n=d-1, and put

```math
\begin{aligned}
H&=\max(0,h),&\Omega&=\{h>0\},&K&=\overline\Omega,&S&=\partial\Omega,\\
M&=\{(t,x):f(x)-h(x)\lt t\lt f(x)\},&
p&=\nabla f,&g&=\nabla h,&k&=|g|\quad\text{on }S,\\
z&=(\tau,b),&r&=|b|,&v&=\tau+r,&\sigma&=\tau^2-r^2.
\end{aligned}
\tag{S1}
```

Let w be a real C⁴ spatial source weight near K (including one and signed
smooth partitions). Define it arbitrarily off that neighborhood; it is only
used at sources in M. Let V_w be the actual first-endpoint weighted overlap,
with **every future partner**. Use the unchanged unsmeared constants and layers
from [the kernel note](dimension-kernels.md), and ordinary sphere area, not
probability measure:

```math
\begin{aligned}
V_w(z)&=\int_M w(x)\mathbf1_M((t,x)+z)\,dt\,dx,&V_w(0)&=\int_\Omega wh\,dx,\\
A^\lt_{\rho,\delta,d}[w]
 &=\rho^{2/d}\left[a_dV_w(0)-\beta_d\rho
   \int_{\tau\ge r,\ v\lt\delta}K_d(c_d\rho\sigma^{d/2})V_w(z)\,dz\right].
\end{aligned}
\tag{S2}
```

The point term is assigned to short **once**. Long uses v at least delta, so
the full unweighted action is exactly short plus #78's signed long term.
Null/vertex and cutoff equality strata are retained in the partition; their
integration endpoints are Lebesgue-null. Compact domination at each fixed
positive density justifies signed Fubini and finite partition summation.

**Written short theorem.** For each member of either named class there is a
geometry-selected delta_S>0 such that every fixed cutoff strictly between zero
and delta_S, and every w above, satisfies

```math
\begin{aligned}
A^\lt_{\rho,\delta,d}[w]&\longrightarrow J_w+D_w,\\
J_w&=\int_S w\,\frac{1-|p|^2+p\cdot g}{k}\,dA_S
     =\int_J w\coth\theta\,dA_J,&
D_w&=\int_\Omega\nabla w\cdot p\,dx.
\end{aligned}
\tag{S3}
```

Neither coefficient depends on delta. The area and angle on the right are
#92's independently constructed metric/normal objects, not definitions from
the action. The cutoff does not depend on w; the remainder constant can.

**Match to long.** #78 §5 supplies delta_L>0 for the **same C⁴ class**, making
every smaller fixed cutoff regular and giving the unweighted long limit zero.
Choose once 0<delta<min(delta_S,delta_L). Its coordinates, proper-time constant,
full sphere, partner set and equality convention are exactly (S1)–(S2).
No arbitrary-cutoff long theorem, shrinking-cutoff uniformity, or weighted long
theorem is borrowed. Empty geometry has all terms zero.

## 2. Actual overlap and finite-regularity primitive

The two strict global envelope bounds select the intersecting time endpoints,
as in #78 (L3), giving on the whole future cone

```math
\begin{aligned}
q_z(x)&=\tau-f(x+b)+f(x),&
(1-\eta)\tau&\le q_z\le(1+\eta)\tau,\\
V_w(z)&=\int_\Omega w[h-q_z]_+\,dx\\
 &=V_w(0)-\int_\Omega wq_z\,dx
       +\int_{0\lt h\lt q_z}w(q_z-h)\,dx.
\end{aligned}
\tag{S4}
```

Positivity of the original envelope gap forces **both** source and translated
target heights positive. Thus this formula has neither added exterior partners
nor deleted cross-component/cross-chart partners. Only f is translated. All
small translated segments lie in a fixed C⁴ neighborhood of compact K.

Here is the needed regularity argument, not an assumption of a jet. Compact S
has finitely many precompact C⁴ height charts x=Phi_i(y,t), with h(x)=t, y in
R to the power d-2. A finite smooth ambient partition on the collar gives
weighted Jacobians W_i of class C³, with common compact y supports and a
fixed two-sided height interval. All sufficiently small positive heights are
in that collar: a contrary sequence in K has a zero-height limit outside it.
The remaining bulk domain is fixed; no interior critical point is charted away.

For small z, the height derivative of q_z in each chart is bounded by a
constant times |b|, hence below one-half. Endpoint signs and the implicit
function theorem give a unique C⁴ root T_i(y,z) of t=q_z(Phi_i(y,t)), staying
in the smaller collar. The collar contribution equals

```math
I_i(z)=\int dy\int_0^{T_i(y,z)}
 W_i(y,t)\,[q_z(\Phi_i(y,t))-t]\,dt.
\tag{S5}
```

On the future cone the roots are nonnegative. Oriented upper integrals extend
(S5) to a small full displacement ball; this extension need not be the actual
spacelike covariogram. The first parameter derivative is the integral of
W_i times the corresponding derivative of q: the upper-endpoint gap is zero.
That new integrand is jointly C³. Rescale its oriented height interval to
[0,1]; W_i, q_z and the C⁴ root then have uniformly bounded derivatives through
order three on fixed compact sets. Dominated differentiation proves that the
first derivative of I_i is C³, so I_i is C⁴. This explicitly accounts for the
Jacobian's lost derivative and the later nonzero moving-root terms. The same
argument with C³ face germs proves a C³ extension. Bulk differentiation uses
the fixed compact domain and the actual derivatives of f.

Taylor expansion of this constructed extension gives

```math
\begin{aligned}
\widetilde V_w(\tau,b)={}&V_w(0)-\tau\int_\Omega w
 +\int_\Omega wp\cdot b+\frac12\int_\Omega wD^2f[b,b]\\
 &+\frac12\int_S\frac{w}{k}(\tau-p\cdot b)^2\,dA_S+R_w(\tau,b),\\
|D^jR_w(z)|&\le T_w|z|^{3-j}\quad(0\le j\le3),&
|D^4R_w(z)|&\le T_w.
\end{aligned}
\tag{S6}
```

The first bounds follow from Taylor's integral theorem, also applied to the
first and second derivatives; D³R is bounded. The fourth is needed only in
6D. The root's linear term is tau minus p dot b; integrating the linear gap
minus height gives one-half its square. At height zero, the **summed** chart
Jacobian is dA_S/k by the ordinary coarea formula. This proves the displayed
two-jet, including the future Hessian. All constants are finite for fixed
geometry and w. Choose the displacement ball and delta_S at most one.

## 3. Full angular normalization and actual sharp bases

Put s_d=area of S to the power d-2. Rotational symmetry with ordinary area gives
zero first moments and second moments s_d/n times the Kronecker delta. Thus

```math
\begin{aligned}
\int_{S^{d-2}}\widetilde V_w(\tau,r\omega)\,d\omega
 &=C_w+L_w\tau+Q_w\tau^2+U_wr^2+\int R_w\,d\omega,\\
C_w&=s_dV_w(0),&L_w&=-s_d\int_\Omega w,\\
Q_w&=\frac{s_d}{2}\int_S w/k\,dA_S,&
U_w&=\frac{s_d}{2n}\left[\int_\Omega w\Delta f
                           +\int_S w|p|^2/k\,dA_S\right],\\
s_5&=2\pi^2,&s_6&=8\pi^2/3.
\end{aligned}
\tag{S7}
```

In particular U_w is not the action coefficient beta_d. The full sphere kills
linear spatial and mixed time/spatial terms, not the Hessian or source flux.
The radial Jacobian and limits are obtained from spatial polar coordinates:

```math
\begin{aligned}
\tau&=(v+\sigma/v)/2,&r&=(v-\sigma/v)/2,&
j_d&=\frac{r^{d-2}}{2v}=\frac{v^{d-3}}{2^{d-1}}(1-\sigma/v^2)^{d-2},\\
F_{d,a}(\sigma)&=\int_{\sqrt\sigma}^{\delta}j_da\,dv
 \quad(a=1,\tau,\tau^2,r^2),\\
B_w(\sigma)&=C_wF_{d,1}+L_wF_{d,\tau}+Q_wF_{d,\tau^2}
                     +U_wF_{d,r^2}+B_R(\sigma).
\end{aligned}
\tag{S8}
```

These are the **actual** short densities on 0<sigma<delta squared, zero above
it; signed disintegration of (S2) follows from compact Fubini. Each fibre has
its continuous value at zero and vanishes at the upper cutoff. Their formulas
below have **no angular area included**. Integrating the finite Laurent
polynomial in v at both endpoints gives in 5D

```math
\begin{aligned}
F_{5,1}&=\frac{\delta^3}{48}-\frac{3\delta\sigma}{16}
 +\frac{\sigma^{3/2}}3-\frac{3\sigma^2}{16\delta}
 +\frac{\sigma^3}{48\delta^3},\\
F_{5,\tau}&=\frac{\delta^4}{128}-\frac{\delta^2\sigma}{32}
 +\frac{3\sigma^2}{64}-\frac{\sigma^3}{32\delta^2}
 +\frac{\sigma^4}{128\delta^4},\\
F_{5,\tau^2}&=\frac{\delta^5}{320}-\frac{\delta^3\sigma}{192}
 -\frac{\delta\sigma^2}{32}+\frac{\sigma^{5/2}}{15}
 -\frac{\sigma^3}{32\delta}-\frac{\sigma^4}{192\delta^3}
 +\frac{\sigma^5}{320\delta^5},\\
F_{5,r^2}&=\frac{\delta^5}{320}-\frac{5\delta^3\sigma}{192}
 +\frac{5\delta\sigma^2}{32}-\frac{4\sigma^{5/2}}{15}
 +\frac{5\sigma^3}{32\delta}-\frac{5\sigma^4}{192\delta^3}
 +\frac{\sigma^5}{320\delta^5}.
\end{aligned}
\tag{S9}
```

In 6D write ell=log(delta/sqrt(sigma)). The logarithms are retained:

```math
\begin{aligned}
F_{6,1}&=\frac{\delta^4}{128}-\frac{\delta^2\sigma}{16}
 +\frac{3\sigma^2}{16}\ell+\frac{\sigma^3}{16\delta^2}
 -\frac{\sigma^4}{128\delta^4},\\
F_{6,\tau}&=\frac{\delta^5}{320}-\frac{\delta^3\sigma}{64}
 +\frac{\delta\sigma^2}{32}-\frac{\sigma^3}{32\delta}
 +\frac{\sigma^4}{64\delta^3}-\frac{\sigma^5}{320\delta^5},\\
F_{6,\tau^2}&=\frac{\delta^6}{768}-\frac{\delta^4\sigma}{256}
 -\frac{\delta^2\sigma^2}{256}+\frac{\sigma^3}{32}\ell
 +\frac{\sigma^4}{256\delta^2}+\frac{\sigma^5}{256\delta^4}
 -\frac{\sigma^6}{768\delta^6},\\
F_{6,r^2}&=\frac{\delta^6}{768}-\frac{3\delta^4\sigma}{256}
 +\frac{15\delta^2\sigma^2}{256}-\frac{5\sigma^3}{32}\ell
 -\frac{15\sigma^4}{256\delta^2}+\frac{3\sigma^5}{256\delta^4}
 -\frac{\sigma^6}{768\delta^6}.
\end{aligned}
\tag{S10}
```

Both sets obey F_time-square minus F_radial-square = sigma times F_constant.
In particular neither the 5D fractional endpoint nor the 6D logarithmic
primitive may be discarded as a 4D zero-endpoint shortcut.

## 4. Signed responses and physical point cancellation

For j>-1, finite polynomial/gamma integration gives the absolutely convergent
signed Mellin moment and its derivative (the logarithmic moment):

```math
\begin{aligned}
M_d(j)&=\frac2d\Gamma\!\left(\frac{2(j+1)}d\right)
 \prod_{i=1}^{\lfloor d/2\rfloor+1}\left(1-\frac{j+1}{i}\right),\\
\int_0^\infty\sigma^j K_d(c_d\rho\sigma^{d/2})\,d\sigma
 &=(c_d\rho)^{-2(j+1)/d}M_d(j),\\
\int_0^\infty\sigma^j\log\sigma K_d(c_d\rho\sigma^{d/2})\,d\sigma
 &=(c_d\rho)^{-2(j+1)/d}
 \left[M'_d(j)-\frac2d\log(c_d\rho)M_d(j)\right].
\end{aligned}
\tag{S11}
```

Differentiation in j is justified on any compact subinterval above minus one
by an integrable power/log envelope at zero and exponential decay at infinity.
Here the signed polynomials, not layer coefficients without their factorials,
are

```math
\begin{aligned}
K_5(z)&=(1-215z/16+225z^2/16-125z^3/48)e^{-z},\\
K_6(z)&=(1-34z+141z^2/2-63z^3/2+27z^4/8)e^{-z},\\
c_5&=\pi^2/160,&a_5/\beta_5&=8/3,&
M_5(3/2)&=1/40,&M_5(5/2)&=-\Gamma(7/5)/8,\\
c_6&=\pi^2/360,&a_6/\beta_6&=5/2,&
M'_6(2)&=-1/36,&M'_6(3)&=\Gamma(4/3)/12.
\end{aligned}
\tag{S12}
```

The integer zeros are 0,1,2 in 5D and 0,1,2,3 in 6D. In the log formula this
also kills the apparently density-dependent log term at those integers.

To use whole-line moments for (S9)–(S10), extend their displayed expressions
above delta squared. The difference from the actual zero-extended densities
is supported away from zero and is a finite sum of powers and power/log terms.
Split the kernel exponential into two factors: one is exponentially small at
the fixed cutoff and the other dominates each such term, with any density
prefactor. Hence this extension changes every normalized response by o(1).
It is not an exchange of a density-dependent cutoff limit.

The constant mode's pair response is a_d/beta_d times V_w(0)/rho, up to terms
whose **normalized** response vanishes. Indeed its respective non-polynomial
coefficients give

```math
\frac{s_5}{3c_5}M_5(3/2)=\frac83,
\qquad
-\frac{3s_6}{32c_6}M'_6(2)=\frac52.
\tag{S13}
```

Thus the physical point divergence cancels with the correct unequal point/pair
constants, not by assuming a_d=beta_d. The linear fibres are polynomials:
integer roots cancel their low powers, and all remaining powers have negative
normalized density exponent. The same is true of the polynomial parts of the
quadratic modes. In general that exponent is (d-2j)/d. Terms not at a root
are **not** declared zero at finite density.

With the action's minus sign, the critical responses are

```math
\begin{aligned}
-\beta_5c_5^{-7/5}M_5(5/2)&=15/\pi^2,&
(Q_w/15-4U_w/15)\,15/\pi^2&=(Q_w-4U_w)/\pi^2,\\
-\beta_6c_6^{-4/3}M'_6(3)&=-48/\pi^2,&
(-Q_w/64+5U_w/64)(-48/\pi^2)&=3(Q_w-5U_w)/(4\pi^2).
\end{aligned}
\tag{S14}
```

Both equal 2(Q_w-nU_w)/s_d. These are dimension-specific computations, not
4D responses. The odd reduced-plane first **height** moment remains positive;
the even second height moment remains divergent. Neither is replaced by a
false zero or a finite Taylor moment. Those height moments are not the
transverse Mellin moments in (S11).

## 5. Actual derivative remainder, moving endpoints and domination

Fix a direction, put F(v,sigma)=j_d R_w(tau,r omega), and use (S6).
On the fibre, |z| is at most v, z is affine in sigma, and its sigma derivative
has norm at most 1/v. For derivative orders l up to three the chain rule gives
T_w v to the power 3-2l. For l=4 in 6D the bound is initially T_w v to the
power minus four, which is at most T_w v to the power minus five since v<=1.
The exact differentiated Jacobian is

```math
\partial_\sigma^i j_d
 =\frac{(-1)^i(d-2)!}{2^{d-1}(d-2-i)!}
 v^{d-3-2i}(1-\sigma/v^2)^{d-2-i}\quad(0\le i\le d-2).
\tag{S15}
```

Leibniz, not a trial power count, now proves

```math
\begin{aligned}
|\partial_\sigma^l F|&\le T_w c_{d,l}v^{d-2l},\\
c_{d,l}&=2^{-(d-1)}\sum_{i=0}^l
 \binom li\frac{(d-2)!}{(d-2-i)!},&
0\le l&\le q_d,&q_5&=3,&q_6&=4.
\end{aligned}
\tag{S16}
```

At v=sqrt(sigma), every partial sigma derivative of F of order **below d-2**
vanishes, because the Jacobian has that many zeros and R is regular there.
Consequently repeated moving-endpoint differentiation gives
B_R to derivative order q_d as the angular integral of the corresponding
partial derivative of F: all Leibniz boundary terms through the orders used
here are zero **by this calculation**, not by keeping the endpoint fixed.
All these differentiations are first done at positive sigma, on compact
positive-v intervals. As a useful check, the boundary contribution at the next
differentiation, **if its interior derivative exists**, would be

```math
-\frac{\partial_\sigma^{d-2}F(\sqrt\sigma,\sigma)}{2\sqrt\sigma}
 =\frac{(-1)^{d-1}(d-2)!}{2^d}\sigma^{-d/2}R_w(\sqrt\sigma,0).
\tag{S17}
```

For the smooth test R=tau cubed this is 3/(16 sigma) in 5D and
-3/(8 sigma to power 3/2) in 6D. Thus there is no license to differentiate
one more time and omit the endpoint. That extra derivative is **not needed**.

Let C=T_w s_d max(c_d,l) over the used derivative orders. In 5D, (S16)
gives integrable dominators v to powers 5,3,1 for the first three probes.
Dominated convergence supplies B_R, B_R' and B_R'' at zero. Its third derivative
is bounded by C log(delta/sqrt(sigma)). In 6D the corresponding powers are
6,4,2,0; all four zero probes exist, and the fourth derivative is bounded by
C/sqrt(sigma). In particular these highest derivatives are locally integrable
at zero. Iterated fundamental theorem of calculus is justified, not just a
formal Taylor expansion at a singular endpoint. If P_5 is the quadratic jet
and P_6 the cubic jet at zero, integration yields

```math
\begin{aligned}
|B_R-P_5|&\le C\sigma^3\left[
 \frac16\log\frac\delta{\sqrt\sigma}+\frac{11}{72}\right]
 &&(d=5),\\
|B_R-P_6|&\le\frac{16C}{105}\sigma^{7/2}
 &&(d=6),\\
|[\sigma^j]P_d|&\le
 \frac{C\delta^{d+1-2j}}{j!(d+1-2j)}
 &&(0\le j\lt q_d).
\end{aligned}
\tag{S18}
```

For example, the first constant uses the integral of
(1-t) squared times minus log(t), equal to 11/18; the second uses the beta
integral with parameters one-half and four. Bounds (S18) hold below the cutoff.
Above it B_R is zero. The last line bounds the subtracted polynomial there.
Using boundedness of x to power one-half times log(1/x) for 0<x<=1 gives the
following **global**, measurable dominators with finite constants C_5,C_6:

```math
\begin{aligned}
|B_R(\sigma)-P_5(\sigma)|&\le C_5\sqrt\delta\,\sigma^{11/4},\\
|B_R(\sigma)-P_6(\sigma)|&\le C_6\sigma^{7/2}\qquad(\sigma>0).
\end{aligned}
\tag{S19}
```

Their signed polynomial moments vanish **before** taking absolute values.
Substitution into (S11)'s absolute version proves remainder bounds proportional
to rho to power minus 1/10 in 5D and minus 1/6 in 6D, times finite absolute
moments of orders 11/4 and 7/2 respectively. Hence both actual remainder
responses tend to zero. These are deliberately loose fixed-cutoff **remainder**
estimates, not full-action rates or cutoff-uniform estimates. The 5D logarithmic
bound is not a pure cubic bound. Smooth test R=tau to the fourth power produces
a surviving higher-order fractional term sigma to power 7/2 divided by 35 in
5D and a log term -3 sigma to the fourth power log(sigma)/512 in 6D; both have
vanishing normalized response. Nonzero terms are not erased just because the
limit permits discarding them.

## 6. Independent coefficient, partitions and nonvacuity

Combining (S7), (S14) and §5 leaves

```math
\begin{aligned}
\frac{2(Q_w-nU_w)}{s_d}
 &=\int_S\frac{w(1-|p|^2)}k\,dA_S-\int_\Omega w\Delta f,\\
\int_\Omega w\Delta f
 &=-\int_S\frac{w\,p\cdot g}{k}\,dA_S
   -\int_\Omega\nabla w\cdot p\,dx.
\end{aligned}
\tag{S20}
```

The divergence theorem applies to the entire bounded C⁴ domain; its outward
normal is **minus** g/k. It includes holes and all components, not artificial
chart walls. #92 (G6)–(G13) constructs the intrinsic positive metric, ordinary
Euclidean surface area, chart gluing and finite Lorentzian joint area before
any action. Its Gram density is sqrt(1-|p_T| squared), and its independent
normal identity multiplies this by coth(theta) to give
(1-|p| squared+p dot g)/k. Thus (S20) proves exactly (S3).

For a finite signed smooth spatial partition summing to one near K, actual
weighted overlaps and point terms add exactly at every density. Gradients sum
to zero, so the D_w terms cancel **after the complete sum**. Partners are never
restricted to a chart. A zero joint-trace weight may still have nonzero D_w.
No tangent-wedge-only replacement or missing global planar base theorem is
used: the direct-origin route supplies the point and Hessian terms itself.

**Nonvacuity in each dimension.** #92 (G20) with a=1/4, epsilon=1/8 gives
smooth nonempty ball/sine members, with the positive-height critical center
retained and genuinely curved future. The cosine phase variant has the same
strict budget and a nonzero integrated future Hessian. #92's annuli and planar
ellipsoids also belong, including their inner boundaries. This is not just a
planar test class. For either ball phase, #78's explicit cutoff regularity
bound delta<2/9 still holds. Choosing delta additionally below delta_S supplies
a nonempty interval of matched cutoffs, without claiming delta_S=2/9.

For reproducible actual-region checks, integrating all transverse source
coordinates in the cosine family, with w depending on x_1 only, gives

```math
\begin{aligned}
V_w(\tau,b)&=\frac{2v_{d-2}}{d\,a^{(d-2)/2}}
 \int_{-1}^1 w(x)
 [a(1-x^2)-\tau+\epsilon(\cos(x+b_1)-\cos x)]_+^{d/2}\,dx,\\
v_m&=\frac{\pi^{m/2}}{\Gamma(1+m/2)}.
\end{aligned}
\tag{S21}
```

This is the actual overlap, not the quadratic model. Bulk slices have density
v_(d-2) times (1-x squared) to power (d-2)/2, and joint slices have density
area(S to power d-3) times (1-x squared) to power (d-4)/2. These independently
compute the jet, source derivative and normal/Gram target. For the planar unit
ball the exact overlap is #78 (L19); the independent fixed-time short density is

```math
B^\lt_{\delta,d}(\sigma)=\frac{s_d}{2}
 \int_{\sqrt\sigma}^{(\delta+\sigma/\delta)/2}
 (t^2-\sigma)^{(d-3)/2}
 \frac{2v_{d-1}}{d+1}a^{-(d-1)/2}(a-t)^{(d+1)/2}\,dt
\tag{S22}
```

for 0<sigma<delta squared and delta<a, and zero above. The independent target
is s_d/(2a). In 5D the actual overlap is cubic, **not** the quadratic model;
in 6D it has power 7/2. Tests distinguish these objects.

## 7. Go/narrow/stop ledger and matched global-limit contracts

| Dimension/scope | Decision and proved written input | Boundary / remaining work |
| --- | --- | --- |
| 5D C4ShortPilot5 | **Go, narrow:** actual C³ primitive, (S9), signed fractional responses, actual logarithmically bounded remainder, independent target | C⁴ retained to match #78; no all-C³ or arbitrary-cutoff long claim |
| 6D C4ShortPilot6 | **Go, narrow:** actual C⁴ primitive, (S10), signed logarithmic responses, fourth-derivative remainder and target | No finite even second height moment; fourth primitive derivative must be supplied by a formal port |
| Old C³ candidate in either dimension | **Stop this extension:** not proved by the matched route | #78's rectified long density loses a Jacobian derivative; 6D's present short proof also needs more control. Failure of these sufficient estimates is not a full-action counterexample |
| Other dimensions / independent envelopes / arbitrary long cutoffs | **Stop this pass** | No generalized theorem, shrinking-cutoff interchange or sample-wise convergence |

The following are **written contracts**, not Lean declaration names:

```text
For d=5 or 6 and CandidateTwoFace(d,4;h,f):
  Geometry: #92's actual M, finite intrinsic J_d, bounded Borel causal convexity.
  Cutoff: choose fixed 0 < delta < min(delta_S, delta_L).
  Short producer (this note): actual A_short(rho,delta;1) -> J_d.
  Long producer (#78 section 5): actual L(rho,delta) -> 0.
  Exact assembly: A_full = A_short + L, with the point assigned once.
  Matched deterministic goal: D(d,4) in #92 (G19).
  Matched expected goal: E(d,4), using the independent Poisson finite-order
    observable and the separate finite-density identity after actual region
    and restricted-interval hypotheses have been discharged.
```

At the conventional level the two written producers and exact addition justify
these **bounded C⁴** deterministic contracts; #92's bounded measurable causal
convexity discharges the mathematical hypotheses for the separate expectation
bridge, giving the corresponding conventional expectation corollary. This is
not an unconditional Lean assembly, nor general 5D/6D coverage. The weighted
short theorem alone does not supply a weighted long/global theorem. No new
probability identity, rate for the full action or individual-sprinkling limit
is asserted. Independent human review remains outstanding for the written
producers and their combination.

Only the following bounded formal work is justified by these inputs:

1. **Shared finite geometry, exactly d=5,6 and C⁴:** port #92's actual region,
   overlap, compact height atlas/coarea, whole-domain divergence, canonical
   area/normal target and nonempty examples. Reuse the existing dimensional
   interval and expectation APIs only after these hypotheses are proved.
2. **Actual short producer:** derive (S5)–(S6), signed disintegration, ordinary
   sphere moments, the four bases, Mellin/log responses, endpoint vanishing and
   the global remainder dominators. Do not put any of these in admissibility.
3. **Actual long producer:** port #78 §5 on the very same C⁴ class and sufficiently
   small fixed cutoff, including cutoff regularity and compact rectification.
   The checked conditional transverse-cancellation lemma is not this producer.
4. **Assembly only after both producers and geometry are checked:** choose one
   common cutoff, add the actual signed pieces, then specialize the existing
   expectation bridge. Regression obligations include the unequal point/pair
   constants, nonzero Hessian/source derivative, holes and every partner.

These are bounded prerequisites for future #81 children, not work launched by
this pass or a promise to port the entire analysis. Coordinate formal ownership
before changing Lean; use the pinned ancestor for incremental feedback and the
full local integrated audit after the final Lean-affecting edit. No Lean work
is necessary for this written delivery.

## 8. Acceptance and verification boundary

| #132 acceptance | Evidence here |
| --- | --- |
| Named nonvacuous compatible classes and regularity | §§1–2, §6; same C4LongPilot56 slices, not a changed C³ contract |
| Actual two-jet, bases, angular measure, signed coefficients and point term | (S4)–(S14); no false parity moments |
| Actual moving endpoints and compact remainder domination | (S5)–(S6), (S15)–(S19), including the first unused nonzero boundary term |
| Independent intrinsic target and matched cutoff | §§1,6–7; all components, Hessian flux and source derivatives retained |
| Go/narrow/stop and exact bounded prerequisites | §7; no general-dimensional closure or model counterexample |

- **Written proof:** (S3) and the explicitly bounded conventional matched
  contracts above. Classical compact-chart, coarea, Taylor, divergence and
  dominated-integration arguments; not independently human-reviewed.
- **Symbolic/numerical evidence:** `dimension_short_56.py` and
  `test_dimension_short_56.py` check the actual bases, signed moments,
  normalization, endpoint terms, nonzero subleading responses, actual planar
  and curved overlaps, and independent normal/Gram and signed partition
  regressions. Model actions are labeled as models. Numerical tolerances are
  not certified error bounds or proofs for arbitrary regions.
- **Lean:** no source, formal checker, dependency or build inputs changed; no
  new theorem or local Lean audit is claimed. Python/Markdown checks do not
  machine-verify this written proof. Existing checked results retain their scope.

```sh
.venv/bin/python -m unittest -v test_dimension_short_56
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
