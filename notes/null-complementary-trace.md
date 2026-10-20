# Complementary null response: triangle data and anchored transport

**Written partial results; original contract STILL BLOCKED.** This continues
#156 / draft #184 from `0277a469fc8d544d82c40c9f60a6bb2d50996d58`, on the
same branch targeting `issue-81-general-coverage`. It consumes, rather than
reproves, [SM's origin theorem](null-suspension-matching.md). Two distinct
attempts produce a critical triangle-phase replacement and an anchored signed
transport criterion. A sharper geometric fold estimate also upgrades the
**six-dimensional flat suspension** from leading growth to growth plus its
independent finite term with an o(1) remainder. Neither attempt constructs
the arbitrary-Y complementary trace. The sole original-item crosswalk is
[required coverage §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).
These arguments are not independent acceptance, new Lean certification or
sample-wise conclusions.

## 1. Exact missing theorem and the normalization being tested

Fix d>=2, a closed smooth Riemannian Y of dimension n=d-2, and the actual
product suspension IN4. Components are handled as in SM1: finitely many,
no cross-component causal pairs, both point and pair integrals additive.
Let q=d/2, b=1+2/d, and use the original a_d, beta_d and K_d. Fix the geometry,
a compact positive width range, one compatible positive **physical temporal
cutoff** delta, and an auxiliary SM cutoff chi supported below that width
range and the normal-locality radius. For convenience choose 0<=chi<=1.
No cutoff depends on density. IN7's rapidity restriction, not merely u<delta,
defines physical short; its complement is restored before this calculation.

Write W(u;y,y') for IN5's **endpoint-conditional whole** triangle potential,
F_rho for IN6's signed Y-pair integral, and G_T for its actual null cap. Set

```math
\begin{aligned}
\mathcal T_Y(T)&=T^2R_Y^{\mathrm{tot}}/4+2V_Y,\\
C_\rho^\chi(T)&=\int_0^T(1-\chi(u))G_T(u)
 \int_{Y^2}\mathbf1_{d_Y(y,y')\lt u}
 K_d(\rho W(u;y,y'))\,d\mu_Y(y)d\mu_Y(y')\,du,\\
\mathcal A_{\rho,d}(M_T)
 &=\mathcal T_Y(T)-\beta_d\rho^b C_\rho^\chi(T)+r_\rho^\chi(T),\\
\sup_T|r_\rho^\chi(T)|&\le C\rho^{-1/d}(1+\log\rho)^2.
\end{aligned}\tag{CT1}
```

The last bound is SM3–SM5, for rho>=1 on the stated compact width range.
**The missing output**, not an admissibility premise, is independently
geometric data specifying a complementary response Gamma_Y(rho,T) such that

```math
\begin{aligned}
\sup_{T\in I}\left|
 -\beta_d\rho^b C_\rho^\chi(T)-\Gamma_Y(\rho,T)\right|&\longrightarrow0,\\
\mathcal A_{\rho,d}(M_T)&=
 \mathcal T_Y(T)+\Gamma_Y(\rho,T)+o(1).
\end{aligned}\tag{CT2}
```

A fixed T version suffices for fixed-geometry acceptance; uniformity on a
compact I is a useful stronger output, not an added parent gate. Gamma may
include a finite nonlocal term, growing terms, logarithms or nonclassical
scale dependence. No universal finite power/log list is presumed. It may
**not** be defined as the first expression in CT2, a filtered copy of that
expression, or its assumed limit. Any decomposition into growing and finite
terms needs its own geometric definition and remainder proof. CT2 is a
precise research obligation, not the corrected general theorem.

Changing chi changes its complementary response by o(1), by the two SM5
estimates and the exact finite-density partition. Both matching tails and
the single physical point are already present in CT1. No separate moment,
sector, weighted-test or absolute-integrability limit is required.

### Audit of the consumed SM conclusions and remainder orders

- SM2 uses the actual endpoint Jacobian and interval quadratic jet. S1–S8
  in [the short remainder proof](general-metric-short-remainders.md) supply
  the whole-interval smooth positive ratio, not only bounded-rapidity G3.
  In the product the flat-block boost is an isometry of that whole interval.
- In SM4 the polar density after the phase change has power d-4+j.
  Three interpolation derivatives for j=1, one for j=3, give interior power
  d. The S11 moving-diagonal terms are retained; each phase derivative costs
  two powers. Integration of the next derivative yields precisely the
  displayed log-weighted remainder. The genuinely zero polynomial moments
  are subtracted on the full half-line **before** bounding it.
- SM3's odd-dimensional H_0 and H_2 tails have orders -5 and -3. Only the
  stated convergent Mellin moments are used. The divergent H_2 power-three
  moment is truncated, not continued and multiplied by zero. These facts
  give CT1's error, including both finite truncation tails.
- SM5's local-width result additionally resolves the normal-local complement;
  its all-width d=3 result additionally resolves the circle's two independent
  phases, all three sectors and physical overlap. Neither follows merely
  from the origin theorem. They remain product results, not #177.
- SM7 recomputes the null spectator cap and retains both fold branches and
  centers. SM8's O(w^4) **primitive** error becomes O(rho^(1-6/d)); SM9's
  physical-union comparison is o(1). Thus the 5D full limit is justified,
  but those estimates alone do not give a finite renormalized limit in d=6
  or higher. The improvement below requires an additional argument.

This reconstruction finds no blocking discrepancy at the scopes consumed.
It is an author audit, not #94/#86 scrutiny or a replacement for those proofs.

## 2. First route: conditional triangle data, without route selection

For endpoints in the same component put ell=d_Y(y,y'). Push the **physical
intermediate-point measure** forward by
`x -> (e,xi)=(d_Y(y,x)+d_Y(x,y')-ell, d_Y(y,x)-d_Y(x,y'))`.
Call this finite positive conditional measure nu_(y,y'). It is defined from
distance and volume alone, without K, density parameter, an action limit,
geodesic multiplicities or a presumed smooth density. The triangle inequalities
give e>=0 and |xi|<=ell. It must remain conditional on both endpoints.

On the complement of the origin collar, all sufficiently small-volume
causal pairs have ell bounded positively below. Indeed u is bounded below
there; if u-ell has a fixed positive margin, compactness and a contained
short timelike diamond give a positive volume margin. Write u=ell+h and
use IN5's actual Abel derivative, then integrate from h=0. Tonelli gives

```math
\begin{aligned}
W(\ell+h;y,y')&=
 \int\int_e^h\sqrt{t-e}\sqrt{(\ell+t)^2-\xi^2}
 A_\ell(t,e)\,dt\,d\nu_{y,y'}(e,\xi),\\
A_\ell(t,e)&=\frac{\sqrt{2\ell+t+e}}{\ell+t},\\
A_{\ell,N}(t,e)&=\sqrt{\frac2\ell}
 \sum_{i+j\le N}{1/2\choose i}
 \left(\frac{t+e}{2\ell}\right)^i
 \left(-\frac t\ell\right)^j.
\end{aligned}\tag{CT3}
```

The inner integral is zero when e>=h. The square root involving xi is kept
**exact**, including xi=±ell at both physical tips. Freezing it at t=0
would not give a uniform relative estimate at those tips. A_ell is the only
factor approximated. Since 0<=e<=t<=h and ell has a positive lower bound,
its displayed Taylor polynomial has uniform remainder O(h^(N+1)) and stays
positive on one sufficiently small fixed collar. Let W_N use A_(ell,N)
there and the exact W outside, with a fixed bounded interpolation between.
This is a kernel-independent geometric auxiliary phase, **not** a correction.

### A critical, not just leading-order, replacement theorem

For every fixed d and Y take N=floor(d/2). The following estimate holds for
the complete complementary cap pairing, uniformly on its compact width range:

```math
\begin{aligned}
|W_N-W|&\le Ch^{N+1}W\le CW^{1+\eta},
 &\eta&=\frac{N+1}{q}>1,\\
\mu_{\mathrm{pair}}\{0\lt W\le v\}&\le Cv^{1/q},\\
\rho^b\left|C_{\rho,N}^\chi(T)-C_\rho^\chi(T)\right|
 &\le C\rho^{1-\eta}+O(\rho^{b+m+1}e^{-c\rho})=o(1),
 &m&=\lfloor d/2\rfloor+1.
\end{aligned}\tag{CT4}
```

Here the bounded measure weight is `(1-chi)G_T du dmu_Y dmu_Y` on causal
pairs; it includes both endpoints, not an averaged triangle measure.
To justify the geometric bounds, choose any minimizing Y geodesic and its
final segment of a fixed small length below the normal radius and ell/2.
The rest-frame interval from that segment's initial point to the target
advanced by h is contained in the whole interval. Its squared proper gap
is `2 s h+h²`, so its actual local volume is at least c h^q. Constants are
uniform on the compact endpoint set, regardless of whether the original
minimizer is unique or conjugate. Thus h<=C W^(1/q). Integration in the
single excess coordinate h gives the sublevel bound in CT4. A choice of a
minimizer is used only to prove containment; no measurable winning route
is integrated or selected.

Positive weights in CT3 bound the relative Taylor error by C h^(N+1).
For comparable positive phases, the mean value theorem for the actual
polynomial-exponential K gives
`|K(rho W_N)-K(rho W)| <= C rho W^(1+eta)
 (1+(rho W)^m) exp(-c rho W)`.
Integrating this **difference**, using the sublevel bound, gives
O(rho^(-eta-1/q)). One may use dyadic volume shells: below rho W=1 their
sum converges because eta>0, and above one the polynomial-exponential
shell sum converges. Multiplication by rho^b gives rho^(1-eta).
The fixed positive-volume complement supplies the last tail in CT4.
No bound on the absolute uncancelled action, inverse of W, or classical
expansion of nu is used. The physical point and origin phase are unchanged.
This is a genuine critical stability result for all closed smooth Y.

### Where the independent trace construction still stops

A natural candidate for *extracting*, rather than retaining, the singular
geometry is the thin-triangle family
`nu_(y,y')({e <= h a, xi in B})`, with a and B fixed probes. At regular
unique nonconjugate endpoints its leading tube rescaling is given by the
geodesic index form; this is consistent with GT8, not a new global theorem.
Keeping only those almost-everywhere coefficients loses the joint endpoint
blow-up near the exceptional set. SM's flat fold already makes that loss
observable after critical normalization; IU's spherical blow-up has a
different order and a continuous secondary transition. Atomic or conjugate-
only data cannot represent both.

CT4 removes all sufficiently high-order error in the elementary Abel factor,
including both tips. It does **not** remove the full conditional measure nu
from inside the nonlinear kernel. Keeping all of nu in CT3 and calling the
result Gamma would rename the original observable. Conversely, replacing nu
by its regular-endpoint tangent has no proved complete critical remainder.
Smoothness gives no finite-type or finite-route resolution here. This is the
first route's precise unsupplied implication. The next calculation shows
what an independent trace and an adequate remainder look like where the
joint distance geometry can actually be resolved.

## 3. Extracted fold trace and a complete six-dimensional refinement

Keep **exactly** SM6's flat null suspensions: d>=5, p=d-4,
`Y=K x (R/10Z)^p`, `1<T<sqrt(5)/2`. All lift enumeration, containment,
source translations, two centers, both inverse branches and physical unions
are those checked in SM6–SM9. No new geometry is substituted. The extracted
contact data are the four physical phases, their first rank loss
`D(s)=-lambda dot s+(s_3-s_4)²/8`, lambda=(1,1,-1,-1), and the actual smooth
amplitude `a(s)=10^p F_(p,T)(A(s))/(8 sqrt(2))`. They are distance/endpoint
measure data, not a kernel residual.

Let `m_q=E[(-Z_1-Z_2+Z_3+Z_4)_+^(7/2)]`, with the independent auxiliary
Weibull densities from SM8. The geometric trace can also be displayed as
an explicit locally finite positive measure in the rest separation u:

```math
\begin{aligned}
d\Lambda_d(u)&=c_d^{\mathrm{fold}}
 \mathbf1_{u\gt1}(u^2-1)^{(p-2)/2}\,du,\\
c_d^{\mathrm{fold}}&=
 \frac{\beta_d10^p |S^{p-1}|}{336\sqrt2}
 c_d^{-7/d}R_d m_q,\\
\mathfrak D_d(T)&=\int_1^T G_T(u)\,d\Lambda_d(u).
\end{aligned}\tag{CT5}
```

The label c_d^fold is distinct from the canonical interval coefficient c_d.
To derive CT5, change the spectator radius in SM7 to
`u=sqrt(1+|b_vec|²)`. Its factor is `|S^(p-1)|/2`, and its remaining power
is `(u²-1)^((p-2)/2)`. Combining with `1/(8 sqrt(2))` and SM8's `1/21`
gives `1/(336 sqrt(2))`. The measure is integrable even at u=1 when p=1.
The all-fifteen-sector coefficient m_q, not the all-positive coefficient,
remains. This is an independently evaluated contact trace on this family;
its relation to CT2 still depends on a critical error estimate.

### Improve the fold error in d=6, rather than reusing O(w^4)

Now restrict to d=6, q=3, p=2. The following sharper primitive result holds:

```math
\begin{aligned}
N_S^{1-\chi}(w)&=\sum_{j=1}^4 b_jw^j+
 \mathfrak B_{6,T}C_3w^{7/2}+O(w^{9/2}),\\
\mathcal A_{\rho,6}(M_T)&=
 \mathfrak D_6(T)\rho^{1/6}+400
 +O\!\left(\rho^{-1/6}(1+\log\rho)^2\right),\\
\frac{\mathfrak D_6(T)}{c_6^{\mathrm{fold}}}
 &=\frac{T^4}{16}+\frac{T^2}{4}-\frac5{16}
       -\left(\frac{T^2}{2}+\frac14\right)\log T>0.
\end{aligned}\tag{CT6}
```

The new proof of the first line is important. SM8 used an absolute estimate
for translating the inverse-square-root singularity; that gives only a
half-power gain. Here integrate that translation in transverse coordinates
**before** estimating it.

For a nonempty active subset I with k inactive coordinates, use SM8/K6's
inactive-coordinate integrations by parts with their actual compact cutoffs.
All far-cutoff terms are smooth in the active coordinates: an inactive
coordinate bounded away from zero has nonzero D derivative and absorbs
parameter derivatives. Repetition to one higher finite order makes their
remaining fibre functions C4. Their integrals over the positive q-ball have
integer powers through four and error O(w^5). Boundary terms at all inactive
zero faces are retained. The leading full-corner term has exponent k-1/2;
terms where a smooth amplitude was differentiated have at least one extra
antiderivative, hence degree at least 9/2 after active integration.

For the leading term put `s_I=w r theta`, theta on the positive part of the
unit Euclidean sphere and r nonnegative. The q-ball's upper radius is
`(sum theta_i³)^(-1/3)`, smooth on every closed face. Its linear angular
factor is `d_0(theta)=-lambda_I dot theta`; its perturbation is
`w r d_1(theta)`. At every zero of d_0 on this sphere there are two nonzero
coordinates i,j with opposite lambda signs. The vector
`theta_j partial_i-theta_i partial_j` is tangent to the sphere and to every
face through that point, and its derivative of d_0 is nonzero. Thus d_0 is
a transverse coordinate **on every relevant boundary face**, not merely
in the open orthant. If all active signs agree it has no zero. Compactness
gives a finite collection of these angular charts and a partition; no new
assumption on general contacts is being made.

First set r equal to its angular upper radius times v, 0<=v<=1. In each
angular chart straighten `d_0+w r d_1` by its nonzero angular derivative,
keeping v and the face coordinates. This is a uniformly smooth small-w
change of variables. It leaves the singular weight as the fixed integrable
power `x_+^(k-1/2)`. All amplitudes, Jacobians, cutoffs and transformed
angular ends now differ by O(w v); use cutoffs supported inside the charts,
and retain their partition complements. The radial power is r^(5/2),
since `|I|+k=4`, and is integrable at zero. Hence the complete rescaled
corner integral differs from its value at w=0 by O(w), not merely O(sqrt(w)).
The same argument bounds the extra-antiderivative terms. It proves the
O(w^(9/2)) error in CT6 with all fifteen sectors and both matching sides.
No derivative of an unknown O(w^4) remainder was taken. The cubic q-ball
and the actual cap amplitude supply every needed finite derivative here;
this proof does not assert an all-dimensional or arbitrary-Y expansion.

For K6 the four integer primitive powers are genuine zeros. Signed
Stieltjes integration of the retained O(w^(9/2)) remainder gives
O(rho^(-1/6)), with constant continuation of N and full tails of the
subtracted powers. SM9's physical-union error is O(w^(q+2))=O(w^5),
so its normalized response is O(rho^(-1/3)). Add CT1's origin remainder.
The independent local term is `2 Vol(Y)=2*(2*10²)=400`, not a fitted
constant. This proves the second line, uniformly on compact subintervals
of `(1,sqrt(5)/2)`. The final line follows by integrating the actual G_T
from 1 to T in CT5; positivity follows from G_T>0 inside that interval,
not from numerical subtraction of the closed formula. No uniform crossover
at T=1 or complete higher-dimensional finite remainder is asserted.

In d=5, SM9 still gives the complete finite limit `40+D_5(T)>40` with
CT5's same independently derived trace. For d>=7 the retained conclusion
is only SM9's complete leading growth, unless a separate stronger result
is supplied. In particular CT6 must not be extrapolated by its notation.

## 4. Second route: anchored complete signed transport

This route uses neither a triangle-density expansion nor branchwise phase
inverses. Fix an anchor a in the normal-local width range above supp(chi),
and restrict T to a fixed compact interval with T>=a>0. Set
`f_rho(u)=-beta_d rho^b (1-chi(u)) F_rho(u)`.
At each finite rho it is bounded on compact u intervals. Split its full cap
integral at a. With m_j and l_j its **actual finite** moments over [0,a],

```math
\begin{aligned}
m_j&=\int_0^a u^j f_\rho(u)\,du,&
l_j&=\int_0^a u^j\log u\,f_\rho(u)\,du,\quad j=1,3,\\
H_\rho(T)&=T^2[(\log T-1)m_1-l_1]
                 +(\log T+1)m_3-l_3,\\
V_\rho(u)&=\frac12\int_a^u(u-v)^2 f_\rho(v)\,dv,\\
-\beta_d\rho^b C_\rho^\chi(T)
 &=H_\rho(T)-\int_a^T G_T'''(u)V_\rho(u)\,du,\\
G_T'''(u)&=6\log(T/u)+T^2/u^2-5\qquad(u\lt T).
\end{aligned}\tag{CT7}
```

Primes here mean **u derivatives**, not IN8's width derivatives. Three
ordinary integrations by parts prove CT7: V,V',V'' vanish at a, and G,G',G''
vanish at u=T. Its cubic closing has G'''(T-)=-4, not zero. The interval
[0,a] was not deleted: it is exactly H_rho. Its four moments are o(1), by
SM5's normal-local complementary phase calculation with the smooth weights
u^j and u^j log u away from zero. More explicitly, at u bounded away from
zero the actual normal radial phase density and its fixed finite derivatives
are bounded; integration over the fixed interval ending at a preserves them.
Its polynomial moments cancel and its positive-volume tails decay. Thus
H_rho=o(1) uniformly on the stated T range; no derivative of an already
asserted action limit is used to obtain anchor data.

The two **nonzero** limiting homogeneous modes of the full action are still
CT1's independently matched T² curvature and constant screen. The two
logarithmic homogeneous coefficients vanish by SM's four moment estimates.
CT7 therefore fixes all four modes instead of trying to recover them by
integrating IN8 with guessed data at zero.

Here is a concrete sufficient signed estimate, not a new necessity. Suppose
geometry supplies an independently evaluated source distribution g_rho on
[a,B], whose anchored third primitive V_geom is an L1 function, and whose
pairing defines Gamma(T)=`-integral_a^T G_T''' V_geom`. If

```math
\begin{aligned}
\|V_\rho-V_{\mathrm{geom}}\|_{L^1(a,B)}&\longrightarrow0,\\
\sup_{a\le T\le B}|-\beta_d\rho^bC_\rho^\chi(T)-\Gamma(T)|
 &\le\sup_T|H_\rho(T)|+
 [6\log(B/a)+B^2/a^2+5]
 \|V_\rho-V_{\mathrm{geom}}\|_{L^1(a,B)}.
\end{aligned}\tag{CT8}
```

This is an integrated negative-order estimate for the **already signed**
complete source. It requires no uniform variation bound for f_rho or the
unsummed target response. The actual cap, rather than an arbitrary smooth
test, is controlled. Independently geometric g_rho is essential: defining
it to be f_rho would be circular. CT5 supplies such source data in its proved
family (with the appropriate density power); CT8 does not assert that their
L1 remainder follows just from a known cap limit. We do not impose CT8 on
any original admissible geometry or on alternative proof methods.

### Smooth-test transport alone is still insufficient at physical closing

A tempting weaker route would prove distributional convergence of f_rho
against smooth tests away from the origin, then integrate IN8. The following
**abstract control**, not a spacetime example, isolates the missing step.
Fix a<T_*<B and a smooth compactly supported phi with phi(0)!=0. Set
`e_h(u)=h^(-4) phi''''((u-T_*)/h)` for small h>0. Four integrations by parts
against any fixed smooth test give O(h), so e_h tends to zero in distributions.
Nevertheless the actual zero-extended cap gives

```math
\begin{aligned}
\int_a^B G_{T_*}(u)e_h(u)\,du&\longrightarrow4\phi(0),\\
I_a^3e_h(u)&=h^{-1}\phi'((u-T_*)/h),&
\|I_a^3e_h\|_{L^1(a,B)}&=\|\phi'\|_{L^1}>0.
\end{aligned}\tag{CT9}
```

Indeed G_(T_*)(T_*+hz)=(2/3)h³(-z)_+³+O(h^4) on the fixed support.
The fourth distributional derivative of (-z)_+³ is 6 delta_0. This proves
the first line with its sign. The second line follows from the anchored
primitives, since the support is away from a. It exhibits exactly the
boundary concentration not controlled by smooth-test convergence; it does
not prove that such a concentration occurs in an admitted geometry.
IN3's actual diamond separately rules out demanding bounded total variation
before all signed integrations. CT8 avoids that false necessity but still
requires a new geometric estimate. This is the second route's stopping point,
different from the first route's failure to extract joint triangle data.

## 5. Adversaries, full restoration and separate expectation

**Topology and focusing are different.** CT5 is nonzero for a flat Y with
no conjugate points. IU7–IU8 retain instead the spherical focal coefficient,
its secondary seven-halves transition, fourth kernel zero and both matching
tails, including `log(5/2)/3`. Using IN10, its independently extracted source
measure is a positive constant times
`1_(u>pi) sqrt(u²-pi²) du`: the constant is
`(5 beta_7/128)*(2 pi V_Y I/(3D))*4 pi²`.
Its G_T pairing is precisely IU8's gamma(T); its density power is rho^(2/7),
and its finite term remains `V_Y(T²/2+2)` from CT1. No spherical profile is
used for the flat fold, and no cut/holonomy coefficient is inferred from
curvature alone. CT4 changes either actual pairing by o(1), not its trace.

**Completed low dimensions.** SM5 supplies Gamma=0 for all fixed widths in
d=2,3 and for normal-local widths in every dimension, including the circle's
physical antipodal closing. The point-Y diamond remains exactly
`2(1-exp(-rho T²/2))`. Its limiting 2 is CT1's screen, not a constant recovered
from the annihilated width equation. These known complete theorems check
CT7's matching; they do not prove CT8 as a necessary norm statement.

**Common-tip controls.** IN2, not the product cap formula, is the applicable
whole-target transport for CS. Its actual common-tip fibre, bounded combined
homothety/boost, derived signed mass and both CS9 tails already prove the
complete conformal 3D result and the uniform cusp-tube bound. The generally
nonzero inverse-lambda tail in CS8a is retained. Intrinsic common-tip equality
preserves the fibre but not that map or mass identity. Non-common-tip fibres
remain `F intersect I^-(q)` with actual overlaps, not a sum of tip actions.

**Restoration in the new complete result.** CT6 uses all of SM's same physical
pairs, both endpoint measures, all fifteen folded sectors, inactive matching
strips, closing spectator fibres and the regular complement. The two-tip
union comparison retains every higher multiplicity by an upper bound, not
pairwise-only inclusion–exclusion. The auxiliary triangle replacement is
not needed for CT6 and is not silently substituted there. Sum every ordered
endpoint partition and both physical temporal masks before assembly; their
point weights sum to one. No separate sector-zero or bilocal-additivity claim
is made. All fixed positive-phase and full-half-line polynomial tails remain.

**Only then transfer probability.** The six-dimensional quotient suspension
has the same finite atomless metric volume, standard Borel space, measurable
closed ambient order and exclusive intervals, and t±z containment verified
in SM6/SM9. Null pairs are product-null without changing the discrete order.
Every original layer is bounded by the square of the finite Poisson
cardinality. The separately proved ordered Mecke identity therefore identifies
its expectation with the complete deterministic action at each rho. CT6,
including the finite 400 after subtraction of the independently defined
growing term, transfers to that expectation. There is no interchange of a
random limit, sample-wise assertion, or general expectation-limit result for
an unresolved deterministic CT2.

## 6. Corrected statement required, smallest missing implication and ownership

The exact false quantifier is **every admitted null suspension over every
closed smooth Y in every dimension has the finite local CT1 target**, or
that any correction is zero whenever curvature and conjugate points are
absent. SM9 refutes it with a fixed admitted complete 5D action, and its
higher-dimensional actions grow. CT6 now gives the full corrected 6D formula,
not merely an unbounded leading term. IU8 supplies a distinct complete focal
formula. These do not refute the existence of a more general nonlocal
asymptotic, nor establish a universal power/log expansion or its failure.
No abstract control above is promoted to an admitted counterexample.

The corrected **general** statement still required by #156/#81/#24 must
independently derive the nonlocal geometric response (or a precise alternative
not requiring a finite asymptotic list), prove its complete signed critical
error, include the established local terms and all contacts, and transfer the
original-law expectation afterward. In the suspension route this is CT2.
It must recover CT5/CT6, IU8, the low-dimensional zero complements and the
structurally distinct common-tip controls, not stipulate them as target-valued
admissibility. Beyond products, the actual two-front unions, non-common-tip,
merging, infinitely flat and singular-end regimes remain required.

**Focused expert question:** after the proved CT4 replacement, can the
endpoint-conditional thin-triangle measures be resolved or controlled jointly
in their endpoint variables so as to extract an independently geometric
source and bound its **cap-tested** signed remainder at order rho^(-b)?
Equivalently as a sufficient transport attack, can one prove CT8 for a source
constructed from those contact data, rather than only convergence on smooth
tests? The estimates must retain both tips and physical closing, and allow
nonclassical scale dependence. No finite route/type premise is available.
This is materially smaller than redoing origin matching or all null geometry.

No general implication of this strength has been proved in either attempt.
The elementary Abel factor is no longer the obstruction; the unresolved part
is the joint conditional distance/contact geometry at critical normalization.
An explicit parent decision would be needed to accept the proved restricted
package instead of the original general theorem. No such scope decision is
adopted or required for continued research. #156 retains these producers;
#81 the corrected general consumer; #177 and #94/#86 remain unresolved and
#185's claim-to-Lean mapping remains deferred. No agents or reviewers are
launched. **STILL BLOCKED.**

**Plain language:** both known mechanisms survive complete accounting: global
identifications can leave a finite charge, and focusing or higher-dimensional
cut interactions can cause growth. The six-dimensional growth now has a
controlled finite remainder. For arbitrary geometry we can simplify the
triangle formula without changing the answer, but we still cannot extract
and bound all the nonlocal contributions. A transport equation or weak test
limit alone does not supply that missing inference.

`null_complementary_trace.py` and its tests check finite Taylor, cap, signed
moment and contact identities only. They do not certify the uniform analytic
remainders or independent acceptance. No production action/law, Lean/checker,
dependency, build configuration or workflow is changed.
