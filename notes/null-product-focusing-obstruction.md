# An admitted all-null region with a complete focusing obstruction (#156)

**Written complete-action obstruction; not a Lean theorem or human acceptance.**
This realizes the existing spherical focusing mechanism in a connected region
whose **entire boundary is null**, including its same-side seams and regular
past–future NN joints. It is not an interior residue transplanted from a
spacelike slab. The new endpoint overlap, complete pair weight, origin/point
matching, short target and original-law expectation are derived below.

The subsequent [complete-domain/remainder audit](null-closure-audit.md#3-np-audit-complete-failure-not-an-interior-residue)
checks this argument before reuse. Its [NA3 consequence](null-closure-audit.md#7-intrinsic-correction-np-rules-out-a-universal-local-jet-repair)
proves that even additive density-dependent local-finite-jet terms cannot
reproduce this family's leading coefficient. That is a necessary nonlocal
correction, not a universal replacement theorem; NP's statements below remain
unchanged.

Use [O5–O13](seven-dimensional-focusing-obstruction.md) only for the actual
seven-dimensional ambient interval and its matched spherical cut response.
The slab's endpoint weight, complete action, and G-SS short theorem are **not**
inputs. The rational certificate O13 proves the sign of the same full matched
model integral I, not of the new complete geometry by itself. All earlier
sources/certificates remain unchanged.

## 1. Geometry, order, strata and independent target

Fix T=4 and L=20. The ambient spacetime and region are

```math
\begin{aligned}
X&=S^2_1\times\mathbb R_z\times(\mathbb R/L\mathbb Z)^3,
&g&=dt^2-h_{S^2}-dz^2-|db|^2,\\
M&=\{(t,x,z,b): |t|+|z|\lt T/2\},
&V_Y&=4\pi L^3,\qquad \mu(M)=V_YT^2/2.
\end{aligned}\tag{NP1}
```

X is a complete Riemannian product; t is a Cauchy time, and compact spatial
closed balls plus bounded time intervals give compact causal diamonds.
Thus the ambient spacetime is globally hyperbolic. M is nonempty, open,
connected and precompact. Its inequalities are -T/2<t+z<T/2 and
-T/2<t-z<T/2. Along a future causal curve both t+z and t-z are nondecreasing.
Every closed ambient interval between endpoints in M therefore stays in M,
including all null intervals and all minimizing sphere routes. This also
identifies intrinsic and restricted ambient order. An ambient diamond between
M endpoints is closed, compact, and contained in M; strong causality is
inherited. Hence M itself is globally hyperbolic. This is an independent
containment proof, not an inference from intrinsic global hyperbolicity.

The whole frontier consists of four planar-in-(t,z) null faces, times
Y=S2 times T3. The two past faces meet at t=-T/2,z=0; the two future faces
meet at t=T/2,z=0. These are compact spacelike **same-side seams**, not past–
future joints and not omitted tips. The two past–future NN joints are
(t,z)=(0,±T/2), each a copy of Y. No face is timelike; there is no lateral
wall, unrecorded corner or degenerate coincident-ray NN joint. At an NN
joint the distinct future null normals have inner product two in the
standard normalization. The positive screen metric is exactly h_Y. There
are no further intersections. All these strata belong to #90's retained
null/mixed taxonomy, not to its G-SS subcase.

The product curvature calculation in O1a applies unchanged: R=2, since only
the unit sphere contributes, with #90's sign convention. Measures are induced
area and length, not normalized Haar measures. Independently of the action,

```math
\begin{aligned}
\mathcal T_{\mathrm{reg}}(M)
 &=\frac12\int_M R\,d\mu+\int_{J_{\mathrm{NN}}}dA
 =V_Y(T^2/2+2)=40\pi L^3.
\end{aligned}\tag{NP2}
```

No coefficient is assigned to the same-side seams. The calculation below
retains them and shows that even adding a finite density-independent stratum
term cannot repair the divergent complete action.

## 2. Physical intervals and both endpoint measures

For endpoint time gap tau, sphere distance theta and four flat displacements
(z,b), causality is tau>=sqrt(theta^2+z^2+|b|^2). Since tau<T<L/2, every
causal interval has a unique lift in the three compact flat factors: distinct
lifts differ by length at least L, whereas combined causal path lengths are
less than 2T. The entire lifted interval projects injectively. The real z
factor needs no lift, and no unique sphere geodesic is assumed.

A Lorentz boost in the lifted time/four-flat block gives
u=sqrt(tau^2-z^2-|b|^2). The actual interval volume W(u,theta) is exactly O4–O5:
its time Fubini integrand is the positive part of u minus the two product
distances. It counts intermediate points once, including both sphere sheets
and all antipodal meridians. It is not a geodesic-volume sum. Containment in
§1 makes it the actual isolated restricted volume for M.

The crucial new endpoint calculation is in the original (t,z) plane. Its
source null coordinates each range over an interval of length T; their
Jacobian is 1/2. For a causal displacement their increments tau±z are
nonnegative. The exact source-overlap measure is therefore

```math
\begin{aligned}
H_T(\tau,z)&=\frac12(T-\tau-z)_+(T-\tau+z)_+,\\
P(\rho)&=C\int_0^\pi\sin\theta\int_\theta^T
 G_N(u)K_7(\rho W(u,\theta))\,du\,d\theta,
& C&=2\pi V_Y,\\
G_N(u)&=4\pi u\int_u^T v\sqrt{v^2-u^2}
 \left[(T^2+v^2)\log(T/v)-T^2+v^2\right]dv.
\end{aligned}\tag{NP3}
```

To derive the last line rather than postulate a weight, first change tau to
u at fixed flat displacement, d tau=u d u/tau. Put v=sqrt(u^2+|b|^2) and
z=v*sinh eta, tau=v*cosh eta. The overlap permits exactly
|eta|<log(T/v). Integrating (u/2)*[(T^2+v^2)-2Tv cosh eta] in eta gives
u*[(T^2+v^2)log(T/v)-T^2+v^2]. Finally d3b=4*pi*v*sqrt(v^2-u^2)dv.
The source Y volume and target sphere azimuth give C. All four faces,
both same-side seams, both NN joints and both endpoint time restrictions
are in H_T. The original pair integral, not a routewise kernel, was reduced.

G_N is positive for 0<u<T, smooth on that open interval, integrable at both
ends, and vanishes at T. Positivity follows also directly from H_T, which is
positive on an open allowed displacement set. There is no endpoint-mass
approximation at u=pi.

## 3. Exact weight, origin matching and a fixed physical cutoff

Let R=sqrt(T^2-u^2). Elementary integration by parts in NP3 gives

```math
\begin{aligned}
G_N(u)=4\pi u\left[
 \frac{4R^5}{225}-\frac{8u^2R^3}{45}-\frac{7u^4R}{15}
 +\frac{u^3(5T^2+2u^2)}{15}\arccos(u/T)\right],\\
G_N(u)&=G_{\mathrm{odd}}(u)+g_4u^4+g_6u^6,\\
g_4&=2\pi^2T^2/3,\qquad g_6=4\pi^2/15.
\end{aligned}\tag{NP4}
```

Here G_odd is analytic and odd on a neighborhood of zero. To check the
antiderivatives, the log terms in NP3 are
J0=R^3/9-u^2R/3+u^3 arccos(u/T)/3 and
J1=R^5/25+2u^2R^3/45-2u^4R/15+2u^5 arccos(u/T)/15;
the nonlog term is -2R^5/15. Taking T^2 J0+J1 gives NP4.
The even powers come only from the pi/2 in arccos, not a fitted jet.

Fix once 0<delta<min(T/2,pi/4), smaller if necessary for the actual local
interval inverse of O14/O17. Split by original tau<delta and its exact
complement, allocating the physical point only to short. When tau<delta,
|z|<=tau<T-tau, so the two closing masks in H_T are inactive but their
polynomial weight remains. Angular averaging in four flat dimensions gives
mean z^2=(tau^2-u^2)/4. Thus the **actual** short weight is

```math
\begin{aligned}
G_{s,\delta}(u)&=\mathbf1_{u\lt\delta}\,\pi^2u\int_u^\delta
 \left[(T-\tau)^2-\frac{\tau^2-u^2}{4}\right](\tau^2-u^2)\,d\tau,\\
G_{\ell,\delta}&=G_N-G_{s,\delta}.
\end{aligned}\tag{NP5}
```

The indicator is not a changed cutoff: the physical split is in tau. Near zero,
G_s is an odd polynomial plus the **same** g4*u^4+g6*u^6 as NP4, by evaluating
the lower integration endpoint. Consequently G_long is analytic odd near
zero. No long partners parallel to a flat direction have been lost.

For clarity the short theorem is derived here, not imported from G-SS. The
same actual ambient W at small u has the analytic inverse from O14/O17:
X=u^2, w=(W/c7)^(2/7), Y=theta^2=Y(X,w), and
A(X,w)=-sinc(sqrt(Y))*Y_w/2, with A(0,0)=1/2. Its independent interval
calculation gives
A=1/2-17X/192+83w/864+O((|X|+|w|)^2) and
X_min(w)=w+w^2/432+O(w^3).
With a fixed smooth origin partition, all odd-u terms integrate analytically
in X. The missing lower integrals of g4*u^4 and g6*u^6 give the pushed density

```math
\begin{aligned}
B_s(w)&=B_{\mathrm{smooth}}(w)-\frac{Cg_4}{10}w^{5/2}
 -C\left(\frac{g_4}{140}+\frac{g_6}{14}\right)w^{7/2}
 +o(w^{7/2}),\\
c_7&=\pi^3/2688,\qquad a_7=8\beta_7,
\qquad \beta_7=\frac{c_7^{2/7}}{4\Gamma(9/7)},\\
\int_0^\infty z^{7/2}K_7(z^{7/2})\,dz&=\frac5{64}\Gamma(9/7),\\
S^\delta(\rho)&\longrightarrow
 \beta_7 C\left(\frac{g_4}{140}+\frac{g_6}{14}\right)c_7^{-9/7}
             \frac5{64}\Gamma(9/7)
 =\mu(M)\left(1+\frac4{T^2}\right)=\mathcal T_{\mathrm{reg}}(M).
\end{aligned}\tag{NP6}
```

The coefficient 1/140 is the O17 **local interval** calculation, unchanged
by the endpoint weight; 1/14 is the elementary integral of u^6/2. Taylor
bounds of the analytic inverse give the displayed remainder and higher
bounds. The cutoff transition, away from u=0, has a smooth phase inverse;
its actual integral has a Taylor remainder without differentiating the
fixed upper endpoint u=delta. The smooth density powers through w^3 are
annihilated by K7's four zeros at Mellin exponents 2/7,4/7,6/7,8/7. The
w^(5/2) term cancels the point as explicitly checked below. The remaining
scaled remainders have integrable polynomial times exponential majorants;
fixed-positive-phase and subtracted tails are retained. This proves NP6
at fixed delta, including the null-face corners, not merely its coefficient.

## 4. The full matched focusing response and all complements

Choose fixed small a0,e0 with pi+e0<T and pi-a0>delta. The actual cut
primitive is now

```math
\begin{aligned}
N_c(v)&=C\int_0^{a_0}\sin a\int_0^{E(a,v)}G_N(\pi-a+e)\,de\,da,\\
W(\pi-a+E(a,v),\pi-a)&=v,\\
N_c(v)&=b_1v^{2/7}+b_2v^{4/7}+b_3v^{6/7}+C_Nv+o(v),\\
C_N&=\frac{C G_N(\pi)}{3D}I>0,
& D&=\frac{16\pi}{3}(12-\pi^2),\qquad
\frac1{400}\lt I\lt\frac{13}{5000}.
\end{aligned}\tag{NP7}
```

Here O6–O13 really apply to the **same entire physical interval W**. The
hypotheses involving the endpoint weight must be rechecked: G_N has bounded
derivatives of every required finite order on the fixed neighborhood of pi,
and G_N(pi)>0 by NP3. Those, rather than its former slab-polynomial formula,
are all the weight properties used in O9–O12. More explicitly, the actual
regular-side inverse gives coefficient bounds a^(1-6j/7), j=1,2,3. After
sin a averaging they are integrable. Subtract those actual coefficients,
put a=v^(1/3)t, and retain both the head and upper tail. The small-t bound
is C(t+t^(8/7)+t^(2/7)+t^(-4/7)), the large-t bound C*t^(-10/7).
Both are integrable, exactly as in O10. The scaled weight tends to G_N(pi);
its smooth error is dominated by the same bounds. The full matched integral,
including O11's boundary subtraction and both transition sides, is I/(3D).
This proves NP7. It does not retain only a positive inner sector.

Outside that cut neighborhood and the origin, O7's exact regular interval
inverse is uniform on compact theta subintervals. Integrating its Taylor
remainder gives only the powers v^(2j/7), j<=3, and O(v^(8/7))=o(v).
Artificial theta/a/e boundaries are retained as the edges of these complete
integrals. The u=T closing region has positive phase (T>pi), so its integrable
weight contributes only an exponentially small term. The same holds for
fixed positive excess away from the null set. The full complementary origin
partition vanishes near zero, so it introduces no additional fractional
coefficient.

At the origin, NP4 and the actual inverse used in NP6 give the **whole**
primitive coefficient -Cg4/(35*c7)=-1024*mu(M)/5 at order v. The g6 term
and curvature corrections have order v^(9/7)=o(v), and every analytic fourth
power is also o(v). The exact full positive sublevel primitive therefore is

```math
\begin{aligned}
N^V(v)&=\sum_{j=1}^3d_jv^{2j/7}
 +\left[-\frac{1024}{5}\mu(M)+C_N\right]v+o(v),\\
\widehat K_7(s)&=\Gamma(s)\prod_{j=1}^4(1-7s/(2j)),
&\int_0^\infty K_7(z)\,dz&=-5/128,\\
\rho P(\rho)&\longrightarrow8\mu(M)-\frac5{128}C_N,\\
\rho^{-2/7}\mathcal A_{\rho,7}(M)
 &=a_7\mu(M)-\beta_7\rho P(\rho)
 \longrightarrow\gamma_N=\frac{5\beta_7}{128}C_N>0.
\end{aligned}\tag{NP8}
```

The passage from primitive to signed response is Stieltjes integration by
parts, subtraction of the three actual powers, then v=z/rho. The bounded
little-o remainder is dominated by z*|K7'(z)|, integrable. Fixed upper tails
are kept before using the genuine Mellin zeros; no analytic continuation of
a divergent absolute moment is used. The complete physical point cancels
because a7=8*beta7. NP6 also shows, at the **same fixed physical delta**, that
short tends to the independent finite target and long has positive leading
growth gamma_N*rho^(2/7). There is no unexamined short cancellation of the
focal term. Both endpoint measures and all masks/unions were already restored
before taking these limits.

All finite smooth endpoint partitions are harmless only with every ordered
label pair restored: their pair sum is one and their diagonal point sum is
one. No weighted-cell focusing theorem is inferred from rotational symmetry.
Thus NP8 is a complete-action counterexample in an admitted all-null region,
not an analogy with the old spacelike example.

## 5. Original-law expectation and the correction it actually proves

M has finite positive smooth atomless volume. The ambient order is the closed
product-distance relation; the exclusive three-point interval indicator is
Borel. Its integrated physical volume is W by the proved containment and
lifts. Single endpoints and null endpoint-time graphs are volume-null without
changing the selected closed discrete order. The original finite Poisson law
has intensity rho times this restricted volume and finite second factorial
moment. Each of the five dimension-seven layers is bounded by N(N-1).
Reduced two-point Mecke with the actual interval count, both intensity factors
and original layer factorials gives, separately from the asymptotic proof,

```math
\begin{aligned}
\mathbb E A^{\mathrm{disc}}_{\rho,7}(M)&=\mathcal A_{\rho,7}(M),\\
\rho^{-2/7}\mathbb E A^{\mathrm{disc}}_{\rho,7}(M)&\longrightarrow\gamma_N>0.
\end{aligned}\tag{NP9}
```

This is a written specialization of the checked dimension-indexed bridge,
not a new compiled instance and not sample-wise divergence.

**Refuted statement:** the canonical bulk-plus-regular-screen target is a
universal finite deterministic or expected limit for the original admitted
null/mixed class in every dimension. The region NP1 already refutes it in
7D, with full matched action NP8 and finite independent target NP2.

**Justified correction, not a new observable:** on this explicit nonconformal
all-null product family the canonical action has the positive divergent
asymptotic NP8; the finite short target survives, while the genuine focal
long response does not vanish. The derivation also holds for any fixed
pi<T<L/2, with T in NP1–NP8 and a sufficiently small fixed delta. The actual
interval estimates near pi and zero are unchanged, the far compact domain
has positive phase, and G_N(pi)>0. No parameter varies with density.
No finite density-independent crease coefficient repairs this family.

Together with [NF](regular-null-front-limit.md) this gives a general positive
regular-SN theorem and a complete admitted null failure, **not yet the corrected
general theorem required to close #156**. In particular it says nothing
unproved about all null geometries in 2D–6D or other 7D geometries. Accepting
only this positive/failure split as the parent's endpoint would be a scope
change requiring user approval; it is not enacted. The exact missing statements
and distinct continuation attempts remain in the crosswalk/handoff.

Diagnostics in `null_front_accounting.py` and `test_null_front_accounting.py`
check the actual endpoint-overlap integral, independent unreduced pair weight,
fixed temporal complements, origin coefficients, finite layer valuation and
sign/normalization. Floating tests are not the proof of NP7's remainder or
independent expert acceptance. #94/#86 retain scrutiny and provenance.
