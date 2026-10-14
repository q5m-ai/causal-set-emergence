# Complete conformally curved 4D single-cone response (#169)

**Conventional written proof, not a Lean theorem or independent acceptance.**
For the **entire** class requested in #169, the complete deterministic action
has the curvature-plus-induced-SN-area limit. The actual-law expectation is
transferred separately in §8. The new step is a future-endpoint cone-ball
resolution of characteristic contacts, followed by a two-variable Mellin
calculation with a controlled remainder. It is neither the false weighted
Gaussian identity nor a spacelike-to-null limiting argument.

Source baseline: `0358c32f7ca19a4491b7e904ee5eaf44003619d3`, the fetched
`origin/issue-81-general-coverage`, containing #168/#170/#171/#167.
The live #169/#156/#81/#24, accepted [#84 geometry](null-mixed-assembly.md),
[dimensional cone proof](null-cone-dimensions.md), and
[NC1–NC4 blocker](null-mixed-required-coverage.md#4-continued-curved-null-research-and-the-concrete-stopping-point)
are inputs, not issue-state substitutes for proofs. Shared definitions are
unchanged. #172's intrinsic spacelike work is independent: no changing order
or volume there is frozen, and no G-SS face theorem is applied to a null sheet.

## 1. Exact class, action and independent target

Use signature (+---) and #90's curvature convention. Fix **any** smooth
H on R3, H(0)=T>0, with global Lipschitz constant lambda<1, and **any**
fixed smooth positive Omega on a neighborhood of the compact causal enclosure.
Put a=Omega^4, g=Omega^2 eta. Smoothness on a compact enclosure means restriction
of a smooth function on a neighborhood; a smaller neighborhood has positive
lower and finite upper bounds and all needed finite derivative bounds.
No jet, cancellation or limit is an admissibility hypothesis.

```math
\begin{aligned}
M&=\{(t,x):-H(x)\lt t\lt-|x|\},& C&=I^-(0),\\
f(t,x)&=\mathbf1_{t+H(x)>0},& d\mu_g&=a(t,x)\,dt\,dx,\\
R(\omega)&=H(R(\omega)\omega),&
\frac{T}{1+\lambda}&\le R(\omega)\le\frac{T}{1-\lambda},\\
\mathcal T_g&=3\int_M\Omega\Box_\eta\Omega\,dt\,dx
 +\int_{S^2}R(\omega)^2\Omega(-R,R\omega)^2\,d\omega.
\end{aligned}\tag{CC1}
```

MA1–MA7 prove compact closure, the smooth spacelike floor, null upper face,
regular SN joint and one future tip, with no lateral wall or hidden crease.
Conformal order preservation leaves those **sets** unchanged. The floor
future-set and cone past-set arguments contain every closed ambient interval
between actual endpoints. Thus isolated restricted intervals equal the actual
ambient intervals, including their interior density, not a flat volume law.
Each source still has the whole interval to the tip as its future fibre, up
to a null set. All interval sets below are physical point sets, counted once;
there are no overlapping route volumes to add.

Independently, the positive joint metric is Omega^2 R^2 times the unit sphere
metric, and R_g=6 Omega^(-3) Box_eta Omega. Hence CC1 is exactly half scalar
curvature plus induced SN area in the original convention. Both are finite.

Keep the original kernel and normalization, and allow smooth endpoint fields
chi, phi on a neighborhood of the closure. Ordinary sphere measure has mass
4 pi, not one. Fields may have signs.

```math
\begin{aligned}
K(z)&=(1-9z+8z^2-4z^3/3)e^{-z},& c&=\pi/24,& C_4&=4/\sqrt6,\\
P_{\chi,\phi}(\rho)&=\int_{M\times M}\mathbf1_{p\preceq q}
 \chi(p)\phi(q)K(\rho V_g(p,q))\,d\mu_g(p)d\mu_g(q),\\
A_{\chi,\phi}(\rho)&=C_4\sqrt\rho
 \left[\int_M\chi\phi\,d\mu_g-\rho P_{\chi,\phi}(\rho)\right],\\
\mathcal A_{\rho,4}(M,g)&=A_{1,1}(\rho).
\end{aligned}\tag{CC2}
```

**Theorem CC.** Every fixed member above satisfies
$`\mathcal A_{\rho,4}(M,g)\to\mathcal T_g`$. More generally §6 derives the
actual weighted limit, with generator and partition terms retained. No
constant, time-only, polynomial-density or round-floor restriction is used.

## 2. Actual whole-interval response and characteristic contact resolution

Parameterize the **future** endpoint, not a transverse intersection of a
null sheet with its own generator. Let z range over the unit three-ball,
n over S2, v>=0, ell>=0, 0<=xi<=1, and b=sqrt(1-xi). Set

```math
\begin{aligned}
q&=(-v,vz),& u&=(1,bn),& p&=q-\ell u,\\
\sigma(p,q)&=\ell^2\xi,&
L(b,n)&=H(-L(b,n)bn),\\
U+\ell&=H(Uz-\ell bn),&
0&\le\ell\le L(b,n),\\
0&\le v\le U(\ell,b,z,n),&
 dp\,dq&=\tfrac12\ell^3\sqrt{1-\xi}\,v^3\,d\ell\,d\xi\,dn\,dv\,dz.
\end{aligned}\tag{CC3}
```

These domains are exact. If q is in C and p precedes q, then p is in C.
The sole remaining mask is p above the floor; it also puts q above the floor
by the future-set property. For fixed ell,b,z,n the function
`v+ell-H(v*z-ell*b*n)` has derivative at least 1-lambda. It has a positive
root exactly when `ell<H(-ell*b*n)`. That last inequality defines the initial
interval ending at L, whose defining derivative is at least 1-lambda.
Consequently L and U are smooth in their displayed non-square-root parameters,
with bounded derivatives on the compact domains. In particular U=0 at ell=L,
and U>0 below it. The Jacobian in CC3 follows from `dq=v^3 dv dz` and
`r^2 dr=ell^3 sqrt(1-xi) dxi/2` for r=ell*b. The coordinate singularities at
v=0 and r=0 have their actual vanishing factors; they are not deleted sectors.

This resolution retains the whole future sphere |z|=1, including pairs on the
same generator. It uses transversality of the **floor in v**, never of the
null face along n. The failure in NC4 therefore remains true but does not
obstruct CC3. Nonmonotone or annular positive-proper-time source slices need
no extra assumption.

Here is the actual weighted phase. Let D0 be the unit-duration flat rest
diamond with coordinates (A,B), centered at zero, and volume c. Resolve B into
components parallel and perpendicular to n. The full affine boosted map is

```math
\begin{aligned}
X_t&=q_t-\ell/2+\ell A+\ell b B_{\parallel},\\
X_x&=q_x-\ell bn/2+\ell b A n+\ell B_{\parallel}n
                       +\ell\sqrt\xi B_{\perp},\\
h(q,\ell,\xi,n)&=c^{-1}\int_{D_0}a(X)\,dA\,dB,\\
V_g(p,q)&=c\ell^4\xi^2 h(q,\ell,\xi,n),\\
P_{\chi,\phi}(\rho)&=\tfrac12\int_{S^2}\int_{B^3}\int_0^1\int_0^L\int_0^U
 \ell^3\sqrt{1-\xi}\,v^3 a(p)\chi(p)a(q)\phi(q)
 K(c\rho\ell^4\xi^2h)\,dv\,d\ell\,d\xi\,dz\,dn.
\end{aligned}\tag{CC4}
```

For xi>0 the map is one-to-one onto the entire interval, with determinant
ell^4 xi^2. This is the faithful conformal whole-diamond map GC5 from
[#167](geometric-long-cancellation.md#derive-the-actual-phase-not-just-a-causal-coordinate-reduction),
whose interval-map hypotheses hold here; its G-SS contact/assembly theorem
is **not** imported. This proves CC4, not just a comparison with an interval volume.
The normalized h is between the positive bounds of a. Reflection of
B_perp proves evenness in sqrt(xi), hence bounded derivatives of every fixed
order in xi near zero, jointly with q,ell,n. One can see this directly by
Taylor's integral remainder in sqrt(xi); reflection cancels odd terms, and
smooth a supplies arbitrarily many derivatives. Local frames for n suffice;
the integrated expression is frame independent. Near xi=1 only bounded ell
and q derivatives are needed below. No derivative of sqrt(1-xi) is taken
there. Every assertion is uniform down to ell=0 and both interval tips.

Thus CC4 is the weighted full-partner response. It is **not**
`1-rho*integral K=exp(-rho*V(p,0))`; NC1 remains a valid refutation of that
shortcut. Both endpoint densities and the **interior** density are present.

## 3. One fixed temporal cutoff; actual long cancellation

Choose once `0<delta<T/[4*(1+lambda)]`. Short means ell<delta; equality belongs
to long. The physical point is allocated only to short. All quantities below
are at fixed geometry and this fixed cutoff.

For long use `ell=delta+(L-delta)*theta`, `v=U*y`, with theta,y in [0,1].
Since L>=T/(1+lambda), the entire parameter domain is fixed, including floor
closure. Its density contains `(L-delta)*U^4*y^3`. U=0 is harmless for every
required derivative, including at simultaneous floor/tip contact. Near xi=0
put `w=ell^2*xi*sqrt(h)` **after** these substitutions. Its derivative at zero
is `ell^2*sqrt(h)>0`, uniformly. The actual inverse exists on a common fixed
w collar. The remaining fixed domain has finite measure.

For clarity the coefficients of the derived density can be written explicitly.
At each remaining parameter let `w=xi D(xi)`, and let J(xi) be the full
CC4 density without dxi or the kernel, after the substitutions. Taylor
coefficients use `D=D0+D1*xi+D2*xi^2+...`, and similarly for J. Then

```math
\begin{aligned}
\alpha&=D_0^{-1},&\beta&=-D_1/D_0^3,&
\gamma&=2D_1^2/D_0^5-D_2/D_0^4,\\
\xi(w)&=\alpha w+\beta w^2+\gamma w^3+O(w^4),\\
J(\xi(w))\xi'(w)
 &=J_0\alpha+(2J_0\beta+J_1\alpha^2)w\\
 &\quad +(3J_0\gamma+3J_1\alpha\beta+J_2\alpha^3)w^2+O(w^3),\\
\int_0^\infty w^j K(c\rho w^2)\,dw&=0\qquad(j=0,1,2).
\end{aligned}\tag{CC5}
```

The remainder is uniform and integrable over the compact parameter domain:
bounded fourth derivatives of the inverse and of J follow from CC3–CC4.
These are **computed geometric** coefficients, not stipulated jets. They
include both weights, both measures, the moving L,U and the cutoff boundary.
Above the fixed collar the positive lower bound on a and ell gives a positive
volume floor, hence an exponentially small retained complement. Polynomial
tails above the collar are retained too. CC5 and the integrable absolute
third-moment remainder prove `rho^(3/2)*P_long -> 0`. No null generator rank
or G-SS forbidden-face clearance was used.

## 4. Matched short estimate: meromorphic continuation with a summable remainder

We now derive, rather than assume, the missing short coefficient and error.
The following complex variable s is a Mellin variable, not squared distance.
On the original strip `0<Re(s)<1/2`, Mellin inversion and absolute Fubini give

```math
\begin{aligned}
\widehat K(s)&=\Gamma(s)(1-2s)(1-s)(1-2s/3),\\
P_{\chi,\phi}^{<\delta}(\rho)
 &=\frac1{2\pi i}\int_{\mathrm{Re}(s)=s_0}
       \widehat K(s)\rho^{-s}Z_\delta(s)\,ds,\\
Z_\delta(s)&=\frac{c^{-s}}2\int_0^\delta\ell^{3-4s}
       \int_0^1\xi^{-2s}F_s(\ell,\xi)\,d\xi\,d\ell,\\
F_s(\ell,\xi)&=\sqrt{1-\xi}\int_{S^2}\int_C
 a(q)\phi(q)a(q-\ell u)\chi(q-\ell u)f(q-\ell u)
 h(q,\ell,\xi,n)^{-s}\,dq\,dn.
\end{aligned}\tag{CC6}
```

The integrability strip follows directly from ell^3 and xi^0 in CC3 and the
positive bounds on h. Gamma decay makes the contour integral absolutely
convergent. The apparent discontinuity f has **already been resolved** by
`0<v<U`, followed by `v=U*y`. For ell<=delta, the floor gap at v=0 is at least
T-(1+lambda)delta, so U is uniformly positive. The transformed amplitude is
smooth in ell and near xi=0, holomorphic in s, and its mixed derivatives of
any fixed order have bounds polynomial in |s| on bounded real strips. This
includes the differentiated moving floor. The future-tip factor remains U^4 y^3.

Here are sufficient explicit remainder operations. Taylor expand in ell
through order two and write the exact remainder as ell^3 E_s(ell,xi). The
function E and its first three xi derivatives near zero obey the same
polynomial bounds, by mixed Taylor's integral remainder. In a fixed xi collar,
subtract its Taylor polynomial through xi^2, and do the same for each of the
three ell coefficients. The remaining double integral is bounded by constants
times `ell^(6-4*Re(s))*xi^(3-2*Re(s))`, integrable for
`Re(s)<7/4` and `Re(s)<2`, respectively. The subtracted xi terms have denominators
`j+1-2s`, j=0,1,2. Away from the collar, xi is bounded below and the
sqrt(1-xi) factor is integrable with bounded ell derivatives.

This constructs a meromorphic continuation to `Re(s)<7/4` with polynomial
vertical growth away from its poles. The possible poles are the simple
null-edge poles 1/2,1,3/2 and the diagonal poles 1,5/4,3/2; coincidences can
be double. All subtracted terms and finite-upper-limit terms are kept. This
is the **matched** estimate: it does not Taylor expand at fixed ell and then
integrate a nonsummable ell denominator. In particular the critical logarithm
at the intersection ell=xi=0 is retained as a double pole.

For later contour shifting, choose any fixed line between 3/2 and 7/4.
The continued expression times Gamma(s) and its cubic polynomial decays
exponentially in |Im(s)|, up to a polynomial. Horizontal contours tend to
zero, and the remaining inverse integral is `o(rho^(-3/2))`. This is the
required normalized error at fixed geometry/cutoff; no uniform rate family,
shrinking cutoff or extra regularity optimization is claimed.

## 5. Derive every surviving coefficient from the interval geometry

Use eta contractions and write D=u^a partial_a. The normalized rest-diamond
moments are `mean A^2=1/60`, `mean B_i B_j=delta_ij/30` and zero odd moments.
Integration of the two ordinary radius-(1/2-|A|) balls derives these constants.
The map CC4 consequently gives, uniformly in xi and n,

```math
\begin{aligned}
h&=a-\frac\ell2 Da
 +\ell^2\left(\frac3{20}D^2a-\frac\xi{60}\Box_\eta a\right)+O(\ell^3),\\
A&=a\chi f,& B&=a\phi,\\
T_0(s)&=\int_C B a^{-s}A\,dq,\\
T_1(s)&=\int_C B a^{-s}\left[-A_t+\frac{sA}{2a}a_t\right]dq,\\
X(s)&=\int_C B a^{-s}\left[
 \tfrac12 A_{tt}-\frac{s}{2a}A_ta_t-\frac{3sA}{20a}a_{tt}
 +\frac{s(s+1)A}{8a^2}a_t^2\right]dq,\\
Y(s)&=\int_C B a^{-s}\left[
 \tfrac12\Delta A-\frac{s}{2a}\nabla A\cdot\nabla a
 -\frac{3sA}{20a}\Delta a+\frac{s(s+1)A}{8a^2}|\nabla a|^2\right]dq,\\
Z(s)&=\frac{s}{60}\int_C B a^{-s}\frac{A}{a}\Box_\eta a\,dq.
\end{aligned}\tag{CC7}
```

Derivatives of f here are distributions, a concise notation for the actual
moving-floor derivatives, **not** a smoothing limit of the geometry. Their
pairings with C are well-defined: in cone-ball coordinates the floor defining
function has v derivative bounded away from zero, including at |z|=1, and
its support is away from the tip. Differentiating the smooth U formula in
CC3 gives precisely these delta and delta-prime pairings. Thus there is no
product of tangent singular masks and no lost floor-contact term. Auxiliary
compact test cutoffs can equal one on the entire relevant support.

Multiply the Taylor expansions of `A(q-ell*u)` and h^(-s), retaining their
cross term. Spherical integration uses mean n_i=0 and mean n_i n_j=delta_ij/3.
The three ell coefficients of the **actual** F in CC6 are

```math
\begin{aligned}
F_s(\ell,\xi)&=4\pi\sqrt{1-\xi}\left[T_0(s)+\ell T_1(s)\right]\\
 &\quad+4\pi\ell^2\sqrt{1-\xi}
 \left[X(s)+\frac{1-\xi}{3}Y(s)+\xi Z(s)\right]
 +\ell^3 E_s(\ell,\xi).
\end{aligned}\tag{CC8}
```

The remainder is the one proved in §4, not only a pointwise Taylor error.
For example the spatial/time variation of a affects all four second-order
terms in X,Y. Keeping only the density at an endpoint gives a wrong coefficient.

For an explicit matched formula, set `B_j(s)=B(1+j-2s,3/2)` with the beta
function continued by §4's subtractions. Integrating the three ell coefficients
in CC8 gives

```math
\begin{aligned}
Z_\delta(s)&=2\pi c^{-s}\biggl[
 \frac{\delta^{4-4s}}{4-4s}T_0(s)\mathcal B_0(s)
 +\frac{\delta^{5-4s}}{5-4s}T_1(s)\mathcal B_0(s)\\
 &\quad+\frac{\delta^{6-4s}}{6-4s}\left\{
 (X(s)+Y(s)/3)\mathcal B_0(s)
 +(Z(s)-Y(s)/3)\mathcal B_1(s)\right\}\biggr]
 +\mathcal E_\delta(s),\\
\mathcal B_j(s)&=\frac{\Gamma(1+j-2s)\Gamma(3/2)}{\Gamma(5/2+j-2s)}.
\end{aligned}\tag{CC8a}
```

The remainder E_delta is the ell^3 remainder in §4, continued by its own xi
subtractions. In `Re(s)<7/4` it has at most the **simple** null-edge poles,
with the proved polynomial vertical bounds, so the kernel kills those poles.
The xi integrals of the first two coefficients are B_0(s). At s=5/4
this beta function is zero: its denominator is Gamma(0), while its numerator
factors are finite. Therefore the possible diagonal 5/4 pole cancels, rather
than producing a face divergence. No absolute integral at a divergent beta
argument is being assigned an integral value.

All **simple** null-edge poles at 1/2,1,3/2 are killed by the corresponding
zeros of the actual Mellin kernel. The two double-pole coefficients are
obtained from the xi^1 coefficient -1/2 of sqrt(1-xi) and the xi^2 coefficient
of the quadratic bracket. With Q0=integral_M chi*phi dmu_g and
`Q2=(-X(3/2)+Y(3/2)-4Z(3/2))/8`, they are

```math
\begin{aligned}
\bigl[(s-1)^{-2}\bigr]Z_\delta(s)&=-\frac{\pi}{8c}Q_0,&
\widehat K'(1)&=\frac13,\\
\bigl[(s-3/2)^{-2}\bigr]Z_\delta(s)&=\frac{\pi}{4c^{3/2}}Q_2,&
\widehat K'(3/2)&=-\frac{\sqrt\pi}{3},\\
P_{\chi,\phi}^{<\delta}(\rho)
 &=\frac{Q_0}{\rho}
 +\frac{\pi^{3/2}}{12c^{3/2}}\frac{Q_2}{\rho^{3/2}}
 +o(\rho^{-3/2}),\\
\lim_{\rho\to\infty}A_{\chi,\phi}(\rho)
 &=-16Q_2=2\left[X(3/2)-Y(3/2)+4Z(3/2)\right].
\end{aligned}\tag{CC9}
```

To check signs, shifting a Mellin inversion contour to the **right** subtracts
its enclosed residues. The double denominators are
`(4-4s)*(2-2s)` and `(6-4s)*(3-2s)`, giving the factor 1/8 in each case.
The factor 2 pi is the CC3 half-Jacobian times the sphere mass.
Substitution of c and C4 gives
`C4*pi^(3/2)/(12*c^(3/2))=16`. Thus the first coefficient cancels the physical
point exactly once and the second has the displayed sign and normalization.

There is no log-density term: each double geometric pole is reduced to a
simple pole by the kernel zero. The delta factors from integrating ell to
delta equal one at the corresponding diagonal poles; their other coefficients
are only simple geometric poles, annihilated by the kernel. Together with
CC5 this accounts for all artificial temporal-cutoff terms, not a claim that
the finite-density short or long pieces are cutoff independent.

## 6. Independent target identification, generators and the future tip

For phi=1, put chi*f in place of f in the following algebra. For chi=phi=1,
CC7–CC9 simplify first to

```math
\begin{aligned}
\lim\mathcal A_{\rho,4}
&=\int_C\bigl[
 a^{-1/2}\Box_\eta(af)
 -\tfrac32a^{-3/2}\partial(af)\cdot\partial a\\
&\qquad -\tfrac14a^{-1/2}f\Box_\eta a
 +\tfrac{15}{16}a^{-3/2}f\,\partial a\cdot\partial a\bigr]dq\\
&=3\int_M\Omega\Box_\eta\Omega\,dq
 +\int_C\partial_\alpha\left(\Omega^2\partial^\alpha f\right)dq.
\end{aligned}\tag{CC10}
```

Here the dot is the Lorentzian contraction, not a positive Euclidean norm.
Expanding a=Omega^4 cancels the gradient-square terms: their coefficients are
9 and -9. The floor terms are exactly
`Omega^2 Box f+2 Omega partial Omega dot partial f`, a divergence. Neither
curvature nor the SN coefficient was inserted into CC7.

The boundary of C is t=-r. Its outward coordinate conormal is (1,omega).
The floor distribution has gradient delta(t+H)*(1,grad H), whose Lorentzian
contraction with that conormal is `delta(H-r)*(1-partial_r H)`. Hence

```math
\begin{aligned}
\int_C\partial_\alpha(\Omega^2\partial^\alpha f)\,dq
 &=\int_{S^2}\int_0^\infty r^2\Omega(-r,r\omega)^2
       \delta(H(r\omega)-r)(1-\partial_r H)\,dr\,d\omega\\
 &=\int_{S^2}R^2\Omega(-R,R\omega)^2\,d\omega.
\end{aligned}\tag{CC11}
```

This divergence identity can be read as ordinary integration by parts in v
and the radial variable after CC3, or as the transverse distributional Gauss
identity. The radial zero is simple with exactly the Jacobian
1-partial_r H; **every generator endpoint** is retained. The floor derivative
support is bounded away from the future tip, so no extra tip flux occurs in
CC11. The interior and long arguments have already retained its full
neighborhood via v^3, including simultaneous closing fibres. Zero volume of
the tip alone was never the estimate.

For a smooth **source** weight chi, the same calculation gives the useful
full-partner identity at the limit:

```math
\begin{aligned}
\lim A_{\chi,1}
 &=3\int_M\chi\Omega\Box_\eta\Omega\,dq
   +\int_{S^2}R^2\Omega(-R,R\omega)^2\chi(-R,R\omega)\,d\omega\\
 &\quad-\int_{S^2}\int_0^R r^2\Omega(-r,r\omega)^2
             \frac{d}{dr}\chi(-r,r\omega)\,dr\,d\omega.
\end{aligned}\tag{CC12}
```

This retains the generator derivative `-partial_t+omega dot grad_x`, not a
spacelike normal derivative. Its integrand is integrable at r=0, even when
chi does not vanish there. A fixed source partition near the tip therefore
has its actual generator flux, not a presumed zero local action. For constant
Omega, CC12 reduces to MA11 with the correct scaling. Artificial source cuts
have opposite endpoint/derivative terms only after their complements are
restored. No shrinking collar or null-face limit enters the proof.

Equations CC9–CC11 prove Theorem CC with the independently defined CC1 target.
They also explain why a smooth whole-diamond map **alone** was insufficient:
the nontrivial missing work is the resolved floor/cone domain, its matched
diagonal/null Mellin remainder, and the surviving transverse distributional
flux, all supplied here.

## 7. Full partitions and restoration audit

At finite density all integrals are absolutely finite. For smooth finite
endpoint partitions summing to one on a neighborhood of the closure,

```math
\begin{aligned}
\sum_{i,j}P_{\chi_i,\phi_j}&=P_{1,1},&
\sum_{i,j}\int_M\chi_i\phi_j\,d\mu_g&=\mu_g(M),\\
A_{\chi,\phi}
 &=C_4\sqrt\rho\int_M\chi\phi\,d\mu_g
   -C_4\rho^{3/2}P_{\chi,\phi}^{<\delta}
   -C_4\rho^{3/2}P_{\chi,\phi}^{\ge\delta}.
\end{aligned}\tag{CC13}
```

Every ordered pair of labels is present, including off-diagonal labels. In
CC7 the coefficients are linear in A=a*chi*f and B=a*phi, so their full sum
is exactly the unit-field result; all derivatives of partition functions
cancel only in this sum. This is not componentwise additivity of subregion
actions, which would change partners and restricted intervals. CC12 separately
shows the generator terms for first-endpoint partitions. Fixed temporal
cutoff conversion is the exact signed difference of CC13, never an assumed
vanishing finite-density correction.

| Sector / potential omission | Where it is retained and controlled |
| --- | --- |
| Full physical intervals and interior density | CC4, an actual bijective diamond map; no Gaussian substitution or overlapping route sum |
| Both endpoint measures and cross-chart partners | CC2–CC4, CC7–CC9, full ordered CC13 sum |
| Macroscopic characteristic pairs, including a shared future generator | Fixed cone-ball domain CC3; derived long inverse/remainder CC5 |
| Floor contacts and all radial generator endpoints | Smooth U,L, distributional floor derivatives CC7, transverse flux CC11 |
| Future tip and closing floor/tip fibres | v^3 and U^4 y^3 on the closed fixed domains; no deleted tip neighborhood |
| Diagonal/null intersection and critical logarithms | Double-variable subtraction in §4, both double poles and residues CC9 |
| Possible single-face divergence | Actual beta zero at 5/4, not a spacelike boundary theorem |
| Point and artificial temporal/source cuts | Point-once CC9/CC13, cutoff factors in §5, generator derivatives CC12 |
| Complete deterministic action | All preceding sectors restored before CC10–CC11 identify CC1 |

## 8. Separate original-law expectation transfer

Only now use probability. M is nonempty, bounded and Borel by MA1–MA5. The
positive smooth density makes its actual volume finite and nonzero and its
measure atomless. Closed ambient order is the Minkowski closed order, preserved
by the positive conformal metric. The three-point interval indicator is Borel;
its actual weighted integral is CC4. Containment proves that this is the
isolated restricted interval rate. Endpoints, null cones and boundary graphs
are null for the smooth volume; this does not change the closed discrete order.

Construct N with Poisson mean rho*mu_g(M), then sample N independent points
from mu_g|M/mu_g(M), and forget labels. This is the original finite Poisson law,
not an action-defined expectation. Simplicity holds almost surely. The original
four layer counts obey the bound `N+16*N*(N-1)` for the absolute action bracket,
so its Poisson second factorial moment proves integrability. Reduced two-point
Mecke, with the actual endpoint-excluded interval, gives

```math
\begin{aligned}
\mathbb E L_k
 &=\rho^2\int_{M\times M}\mathbf1_{p\preceq q,\ p\ne q}
 e^{-\rho V_g(p,q)}\frac{(\rho V_g(p,q))^k}{k!}\,d\mu_g(p)d\mu_g(q),\\
\mathbb E A^{\mathrm{disc}}_{\rho,4}
 &=\mathcal A_{\rho,4}(M,g)\longrightarrow\mathcal T_g.
\end{aligned}\tag{CC14}
```

The first equality is the genuine finite-density bridge; the layer factorials
produce K and both intensity factors remain. The arrow uses the already proved
deterministic theorem, not interchange with a sample-wise limit. #93/#137's
checked foundations support this written specialization; no new compiled
geometric instance or stochastic convergence is claimed.

## 9. Regressions, coverage and verification boundary

`conformal_cone.py` and `test_conformal_cone.py` exercise the actual interval
moments/map, the cone-ball reduction, the matched beta/residue arithmetic and
the independent target. The nonplanar floor `1+epsilon*sin(x1)` and positive
factor `Omega=(1+b*t^2+d*|x|^2)^(1/4)` vary in both space and time; no coefficient is
fitted to a large-density action. Complete pair quadrature is compared with an
independent source-to-tip rest-diamond integration at finite density. Endpoint
partitions, nonzero off-diagonal pairs, point-once, temporal complements and
wrong-density/flat-Gaussian controls are retained. The older round time-only
NC1–NC3 calculation remains a calibration, not the extent of the theorem.
Anisotropic mixed time/space quadratic densities and a positive nonpolynomial
density separately test the whole-interval formula and short jet. Floating
quadrature/refinement and symbolic algebra are diagnostics, **not**
certified asymptotic errors or substitutes for §4's proof.

| #169 acceptance | Written delivery / boundary |
| --- | --- |
| Whole class and actual weighted full-partner reduction | CC1–CC4; arbitrary admitted H and smooth positive spacetime-dependent Omega |
| Characteristic contact coefficients and summable remainder | CC3–CC9; no null-generator transversality, assumed jet or G-SS short import |
| Complete deterministic curvature-plus-induced-SN target | CC9–CC13, including all floor/generator/tip/cutoff/point terms |
| Actual original-law expectation afterward | CC14 with discharged order, measure, interval and integrability hypotheses |
| Regressions and exact #156 ledger | Diagnostic files and the updated required-coverage ledger; no wider-dimensional or multi-tip promotion |

This completes **the written #169 class**, not #156/#81/#24. Arbitrary null
fronts, other curved-null dimensions/metrics, multiple tips, seams, creases,
generator cut/caustic regimes and higher intersections retain #156 ownership.
#172's intrinsic G-SS extension remains separate. No parent contract, action,
target, order, measure or law is changed, and no issue is closed.

No Lean source/checker/dependency/build input changes; no new Lean audit or
compiled asymptotic theorem is claimed. Repository checks, exact-head CI,
GitHub browser math inspection and one bounded PR feedback pass are recorded
in the delivery receipt. Independent human mathematical/physical scrutiny,
intended-statement/provenance review and justified formalization remain
**#94/#86**. No agent launch, merge, deployment, timelike extension, shrinking
cutoff, sample-wise inference or novelty certification accompanies this proof.

Refs #169, #156, #81, #24, #84, #90, #93, #137, #167, #172, #94, #86.
