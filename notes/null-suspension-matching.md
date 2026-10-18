# Null suspensions: origin matching and a flat nonlocal charge

**Written analytic results; original contract STILL BLOCKED.** This continues
[IN5–IN10](independent-null-investigation.md), after their integration into
#184. It proves the missing origin/homogeneous-mode matching for every closed
smooth Riemannian Y, without using the differentiated width equation. It
assembles the local-width theorem in every dimension and the all-width
suspension theorem in d=2,3. It then uses a different signed-integration method to obtain a **complete finite
nonlocal correction in dimension five on a flat null suspension** and complete
action growth in higher dimensions. Thus curvature or conjugate points are
not necessary for a surviving correction. The remaining arbitrary-Y response
is not computed, and these results do not constitute the corrected general
theorem required by #156/#81/#24.

These are conventional arguments, not new Lean certification, independent
mathematical acceptance, or sample-wise convergence. The single original-item
crosswalk remains [§8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).
No new acceptance condition, finite-route hypothesis on general Y, ownership
transfer or exhaustive-classification gate is introduced.

**Subsequent complementary-response continuation:**
[CT1–CT9](null-complementary-trace.md) audits these conclusions without redoing
the origin theorem. It proves a critical elementary-Abel-factor replacement
for arbitrary closed Y and extracts the flat fold's rest-separation trace.
An additional angular transverse-coordinate argument sharpens the same 6D
family to growth plus its independent finite 400 with o(1) error; SM8's
O(w^4) estimate alone did not imply that refinement. The d>=7 claim below
remains leading growth only. A different anchored signed transport route
retains the homogeneous modes and exposes a physical-closing test gap.
The arbitrary-Y trace and original general theorem remain unproved; the
SM arguments and their stated estimates below are preserved.

## 1. Complete observable and the four moments

Keep IN4's product metric, closed ambient order, whole contained intervals and
both endpoint measures. Write n=d-2, q=d/2, b=1+2/d, m=floor(d/2)+1,
V_Y=Vol(Y), and R_Y^tot for the integral of the Riemannian scalar curvature.
The canonical constants are those of `dimension_kernels.py`. Fix a compact
positive width range, a compatible **fixed positive physical temporal cutoff**
delta, and a positive reference length ell_star. None depends on density.
IN7's physical short and long weights are restored before the following
estimates; in particular small u does not mean small physical time separation.
A closed Y need not be connected: it has finitely many manifold components,
there are no ordered pairs between different components, and the point and
pair integrals add exactly. Work componentwise as in IN4 and take minima of
the finitely many locality radii. This is justified absence of cross pairs,
not a bilocal additivity assumption for overlapping regions.

For any bounded auxiliary weight chi(u), define the following *truncated*
signed moments of the actual endpoint-conditional observable F from IN6:

```math
\begin{aligned}
M_j^\chi(T)&=\int_0^T\chi(u)u^jF_\rho(u)\,du,\\
L_j^\chi(T)&=\int_0^T\chi(u)u^j\log(u/\ell_*)F_\rho(u)\,du,
 \qquad j=1,3,\\
P_\rho^\chi(T)&=T^2\{[\log(T/\ell_*)-1]M_1^\chi-L_1^\chi\}\\
 &\quad+[\log(T/\ell_*)+1]M_3^\chi-L_3^\chi,\\
P_\rho&=P_\rho^\chi+P_\rho^{1-\chi}.
\end{aligned}\tag{SM1}
```

This is expansion of the actual cap weight, not integration of IN8. Finite
mass and bounded K justify all finite-density integrals, including the
integrable logarithm at zero. A change of ell_star cancels exactly between
the displayed terms. In general only their **combined signed response** is
required; four separate asymptotic traces are not new acceptance premises.

Choose now a smooth chi equal to one near zero and supported in
`0 <= u < epsilon`, with epsilon below a fixed normal/locality radius of Y
and below the smallest width. This is an **auxiliary proper-separation
partition**, not a replacement temporal cutoff or a new wall. The exact
Lorentz symmetry in the flat (t,z) block carries the entire ambient interval
to separation (u,0), even when its original rapidity is large. All physical
rapidities and endpoint masks have already been integrated into G_T.
Small rest separation therefore puts the actual Y interval in a uniform
normal neighborhood. This uses the product isometry and compact normal
locality, not a boost-uniform assertion for an arbitrary spacetime metric.

## 2. Derive the local reference independently

For d>2 use source-normal Y coordinates y'=exp_y(r theta), 0<=r<u. The
source volume is **not** frozen. The angular integral of Ric_Y(theta,theta)
is R_Y(y)/n times the sphere area. The normal-coordinate endpoint density is
`1-r² Ric_Y(theta,theta)/6+O(r³)`. The actual interval's quadratic factor is
`1+A_d r² Ric_Y(theta,theta)-B_d R_Y(y)(u²-r²)`, where
`A_d=d/[24(d+1)]` and `B_d=A_d/(d+2)`.

Here the Lorentzian Ricci tensor restricted to Y is minus Ric_Y in the
repository's curvature convention. Both coefficients follow from the cone
and volume-element computation G3–G7, not by fitting a desired target.
The bounded-rapidity G3 alone would be insufficient: S1–S8 in
[the actual short producers](general-metric-short-remainders.md) derive the
whole-interval ratio factor and all needed derivatives down to the null
edge. Only that local geometric lemma and the signed comparison calculation
are used here, **not** its G-SS short or boundary theorem.

Let a prime on K mean its derivative and Z=c_d(u²-r²)^q. At unit density
set S to the area of the unit (n-1)-sphere and define

```math
\begin{aligned}
H_0(u)&=S\int_0^u r^{n-1}K_d(Z)\,dr,\\
H_2(u)&=S\int_0^u r^{n-1}
 \left\{-\frac{r^2}{6n}K_d(Z)
 +\left[\frac{A_dr^2}{n}-B_d(u^2-r^2)\right]ZK_d'(Z)\right\}dr,\\
F_{\rho,\mathrm{ref}}(u)&=
 V_Y\rho^{-n/d}H_0(\rho^{1/d}u)
 +R_Y^{\mathrm{tot}}\rho^{-(n+2)/d}H_2(\rho^{1/d}u).
\end{aligned}\tag{SM2}
```

The reference is constructed from the tangent metric and the actual curvature
and endpoint jets. It is not the filtered action or an unexplained residual.
For d=2, each connected Y component is one point, H_0(u)=K_2(u²/2) and the
curvature term is absent.
For d=3 the actual one-dimensional Y also has zero curvature; the displayed
formal H_2 coefficient will only be multiplied by zero.

### Signed profile tails before moment evaluation

Substitute w=u²-r² in H_0. For even d>=4 the factor
`(u²-w)^((d-4)/2)` is a polynomial. Its full-half-line moments vanish, leaving
only exponential upper tails. For odd d split at w=u²/2 and Taylor-expand
the same factor on the first part. The first m moments vanish; the first
possible remainder is O(u^-5). On the second part the true kernel is
polynomial times `exp(-c_d u^d/2^q)`. The same calculation with r² and with
w Z K' gives H_2=O(u^-3) in odd d and exponential tails in even d.
Near zero H_0=O(u^n) and H_2=O(u^(n+2)). All statements concern the integrated
signed profiles, not an absolutely integrable uncombined cone kernel.

Consequently the H_0 moments at powers 1 and 3, with or without one logarithm,
are ordinary absolutely convergent integrals **after** this signed radial
integration. H_2's power-1 moments are also integrable. Its power-3 moment
need not be integrable in odd dimensions and will never be replaced by an
uncut moment.

## 3. Compute the homogeneous data, including the logarithmic partners

Define Phi_d(s) as the Mellin integral of u^s H_0(u). For n>0 direct absolute
Fubini is initially valid only in `-n-1 < Re(s) < 1-n`. The beta integral
there gives Gamma((3-d-s)/2)/Gamma((1-s)/2) times the kernel Mellin
multiplier. Cancel the numerator's poles with its actual m kernel factors.
The tail bounds above then justify continuation as the Mellin transform of
the **integrated** profile up to Re(s)<4 in odd d (with no upper restriction
in even d). The result, factored at both required zeros, is

```math
\begin{aligned}
z_s&=(s+d-1)/d,\\
\Phi_d(s)&=\frac{\pi^{(d-2)/2}c_d^{-z_s}\Gamma(z_s)}{d\,m!}
 \frac{(1-s)(3-s)}4
 \begin{cases}
 1,&d\text{ even},\\
 \Gamma((4-s)/2)/\Gamma((5-s)/2),&d\text{ odd},
 \end{cases}\\
\Phi_d(1)&=\Phi_d(3)=0,\\
\Phi_d'(1)&=-\frac{a_d}{2\beta_d},
 &\Phi_d'(3)&=\frac2{\beta_d},\\
\Psi_d(s)&:=\int_0^\infty u^sH_2(u)\,du\\
 &=\frac{\Phi_d(s+2)}{s+1}
 \left[\frac16+\frac{(s+d+1)(s+2d+1)}{24(d+1)(d+2)}\right],\\
\Psi_d(1)&=0,
 &\Psi_d'(1)&=\frac1{4\beta_d}.
\end{aligned}\tag{SM3}
```

The Phi formula also follows directly for d=2. The Psi formula is used for
d>2 on its convergent strip, in particular near s=1, not at a divergent
odd-dimensional s=3. To derive it, the Mellin integral with an extra r² is
`-n Phi(s+2)/(s+1)`; the one with an extra u²-r² is
`(s+d-1) Phi(s+2)/(s+1)`. Inserting Z K' multiplies each by
`-(s+d+1)/d`, by integration by parts on its initial absolute strip.
This yields the displayed expression and its factor 1/8 at s=1. The two
Phi derivatives reduce to the independent canonical a_d and beta_d via
Gamma recurrence. Logarithmic partners, rather than the vanishing pure
moments, supply the point, curvature and screen data. No zero times an
uncomputed pole is set to zero.

### Fixed truncation and the upper matching tails

Scaling SM2 and using SM3 gives the complete reference data for SM1. Replacing
chi by one in the convergent H_0 moments loses at most
`C rho^(-b-1/d)(1+log rho)`; for example the power-1 tail has scaled order
rho^-1 times (rho^(1/d) epsilon)^-3, while the power-3 tail has order
rho^-b times (rho^(1/d) epsilon)^-1. The H_2 power-1 tail has the latter
order too. For its **truncated** power-3 moment, the O(u^-3) profile tail
bounds the integral by C(1+rho^(1/d) epsilon), with the additional logarithm
where present. Its prefactor is rho^(-1-4/d), again below critical order.
The even-dimensional bounds are stronger. Thus neither a divergent H_2
moment nor a lost matching tail is hidden in this calculation. The reference
length terms multiply the zero pure moments; finite truncation errors remain
controlled, not identically zero.

## 4. Actual-minus-reference estimate, including the logarithmic weight

We now prove that the reference can be used for the **actual** chi-weighted
moments. This is not an assumption that smooth geometry has a global
small-volume expansion.

Put v=u+r, R=(u-r)/(u+r). The local geometric lemma gives
`W=c_d(v²R)^q H(y,theta,v,R)`, with H=1+O(v²), positive and smooth with the
needed finite derivatives on 0<=R<=1. Interpolate by replacing v by lambda v
inside the metric density and H, not in the physical powers of v. Then use
the exact phase coordinate w=v² R H(y,theta,lambda v,R)^(2/d).
Its R derivative is 1+O(v²), uniformly positive for the fixed small collar.
The real r=0 diagonal becomes `v=nu_lambda(w)=sqrt(w) b(lambda sqrt(w))`,
with smooth b, b(0)=1 and b'(0)=0. The actual upper cutoff remains in chi(u);
a fixed v enclosure contains its support.

For u^j du times the Y polar density the pushed v power is d-4+j. The true
factor `(1-R)^(d-3)` is retained. This differs from the full spatial cone's
power d-2; no full-cone slice normalization is transplanted. For j=1 take
three lambda derivatives, comparing with the entire quadratic jet SM2.
For j=3 one derivative suffices to compare with the flat model. In both cases
the differentiated interior has the same worst v power d. With a logarithm,
`log(u/ell_star)=log(v/ell_star)+log((1+R)/2)`. The second summand is smooth;
the first adds only a factor `1+|log v|` to the derivative estimates.

Retain the moving-diagonal contacts. For one, two and three lambda derivatives
they are respectively `a nu_dot`,
`2 a_lambda nu_dot+a_v nu_dot²+a nu_ddot`, and
`3 a_lambdalambda nu_dot+3 a_lambdav nu_dot²+a_vv nu_dot³
 +3 a_lambda nu_ddot+3 a_v nu_dot nu_ddot+a nu_dddot`,
as in S11. They need not vanish merely because r=0. Every additional w
derivative costs two v powers. If N=floor(d/2), the zero-phase integrands
through derivative N are bounded by `v^(d-2j)(1+|log v|)` and are integrable.
All contact limits at zero vanish at these remainder orders. The next
interior integral, from nu to a fixed upper bound, is at worst
`v^(d-2N-2)(1+|log v|)`. Including the differentiated contacts gives, for
Q the relevant lambda derivative of the pushed moment density,

```math
\begin{aligned}
|Q^{(N+1)}(w)|&\le
 \begin{cases}
 Cw^{-1/2}(1+|\log w|),&d=2N,\\
 C(1+|\log w|)^2,&d=2N+1,
 \end{cases}\\
D(w)&=\sum_{j=0}^N d_jw^j+\mathcal R(w),\\
|\mathcal R(w)|&\le Cw^{(d+1)/2}(1+|\log w|)^2,\\
\rho^b\left|\int_0^\infty K_d(c_d\rho w^q)D(w)\,dw\right|
 &\le C\rho^{-1/d}(1+\log\rho)^2=o(1).
\end{aligned}\tag{SM4}
```

Use a fixed phase cutoff in the local collar; its complement has positive
volume and exponential kernel decay. Integral Taylor in w and then lambda
proves the first two lines for the **actual minus entire jet**, including
all diagonal terms. Subtract the polynomial on the full positive half-line:
its j=0,...,N moments are genuine kernel zeros. Its tails and the positive-
volume complement are retained before rescaling w by rho^(-2/d). This proves
the last line, rather than bounding the uncancelled coordinate error.
Passive derivatives of chi and the smooth `log((1+R)/2)` obey the same bounds;
no derivative of a physical face selector occurs. A finite compact normal
atlas supplies the needed dimension-dependent derivatives and uniform
constants. The source measure stays exact throughout.

For d=2 the local interval is exactly flat and no comparison is needed.
For d>2, the quadratic jet at fixed original (u,r,theta) is precisely SM2;
fixed-density differentiation there is legitimate. Thus no formal phase
Taylor series has been substituted for the actual estimate. This explicitly
checks the hypotheses needed to reuse S9–S13's calculation despite the
changed polar dimension and logarithmic weights.

## 5. Origin theorem and exact scale recombination

Combining SM3–SM4 and the retained tails proves, uniformly on each fixed
compact positive width range whose lower endpoint exceeds epsilon,

```math
\begin{aligned}
M_1^\chi&=o(\rho^{-b}),&M_3^\chi&=o(\rho^{-b}),\\
L_1^\chi&=-\frac{a_dV_Y}{2\beta_d}\rho^{-1}
 +\frac{R_Y^{\mathrm{tot}}}{4\beta_d}\rho^{-b}
 +o(\rho^{-b}),\\
L_3^\chi&=\frac{2V_Y}{\beta_d}\rho^{-b}+o(\rho^{-b}),\\
\frac{a_d}2\rho^{2/d}T^2V_Y-\beta_d\rho^bP_\rho^\chi
 &=\frac{T^2}4R_Y^{\mathrm{tot}}+2V_Y+o(1).
\end{aligned}\tag{SM5}
```

The proof gives an O(rho^(-1/d)(1+log rho)^2) error after normalization,
with constants for the fixed geometry and cutoffs. Both homogeneous local
terms are recovered; no arbitrary integration constant is chosen. The
geometric target on the last line was independently computed from bulk
curvature and the two NN screens in IN4. The point is the original full
volume point, counted once after physical short/long restoration.

At finite density the exact subtraction is
`P = integral chi G F_ref + integral chi G(F-F_ref)
   + integral (1-chi) G F`.
SM4 controls the second term, and SM3 controls the first with both matching
ends. Replacing chi by another admissible auxiliary cutoff leaves the exact
sum unchanged; subtracting their two SM5 statements proves their normalized
pair difference tends to zero. Ell_star cancels already in SM1. IN7 retains
the same physical delta on both sides. These are exact recombinations and
proved errors, not sequential limits in density and a shrinking cutoff.

**A complete local-width corollary.** There is a positive geometry-dependent
radius T_0 such that, for each fixed `0<T<T_0`, the complete deterministic
action tends to `T² R_Y^tot/4+2 V_Y`, uniformly on compact subintervals of
(0,T_0). Choose the auxiliary origin collar below the width range. On its
complement every actual interval is still in the same normal locality range.
At fixed u bounded away from zero the radial phase derivative at r=u is
nonzero; changing r to w yields a smooth density with bounded derivatives.
The u integration has the actual weight G_T, fixed range ending at T, and
no moving w-dependent cap. Taylor through degree N and the true kernel
zeros make this complementary response o(1). Positive-volume regions have
exponential tails. This proves the corollary, rather than asserting it from
the origin term. T is never made density-dependent, and no assertion is
made uniform down to T=0: IN9 explicitly forbids that interchange.

**Complete all-width corollary in d=2,3.** In d=2 each component is the
exact flat diamond. In d=3 every closed connected one-dimensional Y is
isometric, by arclength, to a circle of some length L. For every fixed T>0
the complete limit is therefore 2 Vol(Y), with counting volume in d=2.
Here is the additional global argument needed in d=3. A small-volume pair
must approach u=dist_Y(y,y')<=L/2. Away from the antipodal pair there is one
thin flat diamond. Near the antipode there are precisely two potentially
causal lifts; every other lift has a fixed distance gap. In an oriented
endpoint-displacement coordinate theta near L/2 their phases are
`s_1=u²-theta²` and `s_2=u²-(L-theta)²`. Their Jacobian in (u,theta) is
4uL, nonzero there. Thus there is no folded phase density. The actual cap
G_T, extended by zero beyond T, is C2 uniformly on compact positive width
ranges, including T=L/2. The three active sign sectors of the sum-volume
phase consequently have a complete primitive `b_1 w+b_2 w²+O(w³)`:
integrate inactive coordinates with their real cutoffs, and rescale the
positive coordinates in their fixed q-ball; the C2 density has the required
Taylor remainder. Both powers are actual K3 zeros; the normalized remainder
is O(rho^(-1/3)). Both-tip overlap comparison, proved geometrically as in
SM9, changes the response by o(1). The positive-volume complement has
exponential tails. Adding SM5 proves the stated full limit, including at
antipodal closing, uniformly on compact T intervals away from zero. No
all-dimensional finite-lift assumption is inferred. These are product
suspensions, not #177's arbitrary curved G-SS three-manifolds.

**What is still missing for arbitrary widths.** For general closed Y in
dimensions d>=4, SM5 reduces the remaining problem to the critically normalized *complete
signed* pairing of `(1-chi)G_T` with IN5's actual conditional triangle
potential inside K. That unevaluated pairing is **not** named a geometric
correction. Smoothness/local reference subtraction supplies no global
critical estimate through all cut/focal configurations. Four separate
complementary moment limits, GT10, meromorphic continuation or a finite
route list are not mandatory routes to one. The next sections therefore
try direct signed integration on an admitted geometry, not an assumed
arbitrary-Y expansion.

## 6. A different route: a flat suspension with a critical folded contact

For d>=5 put p=d-4 and let
`Y_d = K x (R/10Z)^p`, where the flat Klein bottle K is generated by
`g(x,y)=(x+1,-y)` and `h(x,y)=(x,y+2)`.
Its volume is `V_Y=2*10^p`, its curvature is zero and it has no conjugate
points. Use **the null suspension IN4**, not the spacelike slab K1:
`T=21/20`, or any fixed width strictly between 1 and sqrt(5)/2.
The ambient spacetime is smooth, time oriented and globally hyperbolic.
Monotonicity of t+z and t-z proves whole closed-interval containment.
The independent local target is `2 V_Y`; the four faces are null, with
precisely IN4's seams and two screens. Orientability is not imposed by the
original contract. This is a genuine admitted family, not an abstract scalar
control.

The lift enumeration of [K1–K2](flat-klein-bottle-obstruction.md) applies with
one flat spatial direction now real and already integrated by IN6. Here is
the needed geometric check. The flat torus periods are ten, so at u<T there
is only one relevant lift per spectator direction. Each reflection parity
is a square lattice of side two. Three points in one parity need enclosing
radius at least sqrt(2); two horizontal pairs span at least three; two
vertical pairs have minimum enclosing radius sqrt(5)/2. Thus there are at
most four causal targets, and four require one horizontal and one vertical
pair. This finite list is **derived for this geometry only**.

At the two physical centers y_0=1/2,3/2, use source/target vertical
coordinates y_0+Y,y_0+W, horizontal displacement 1+X, spectator displacement
b_vec, and the IN6 rest gap u. The exact four phases are

```math
\begin{aligned}
s_1&=u^2-(1+X)^2-(W-Y)^2-|b_{\mathrm{vec}}|^2,\\
s_2&=u^2-(-1+X)^2-(W-Y)^2-|b_{\mathrm{vec}}|^2,\\
s_3&=u^2-X^2-(1-W-Y)^2-|b_{\mathrm{vec}}|^2,\\
s_4&=u^2-X^2-(-1-W-Y)^2-|b_{\mathrm{vec}}|^2,\\
D(s)&=(s_3-s_4)^2/8-(s_1+s_2-s_3-s_4)=2(Y-W)^2,\\
A(s)&=1+(s_3+s_4)/2+
       [(s_1-s_2)^2+(s_3-s_4)^2]/16.
\end{aligned}\tag{SM6}
```

The first three independent phase coordinates fix Y+W, so the residual
product is a negative square, not an unrestricted product. This is a cut
contact with rank loss despite zero curvature. At s=0, u²=1+|b_vec|².
In particular it is entirely physically long for a fixed delta<1/10.

### Recompute the endpoint weight; do not import the slab coefficient

Integrate **the actual G_T** over spectators and change u to the common
radial phase. Both folded branches, both centers and source translation
volume give

```math
\begin{aligned}
\mathcal F_{p,T}(A)&=\frac12\int_{\mathbb R^p}
 \frac{G_T(\sqrt{A+|b_{\mathrm{vec}}|^2})}
      {\sqrt{A+|b_{\mathrm{vec}}|^2}}\,db_{\mathrm{vec}},\\
\mathfrak a_{d,T}(s)&=\frac{10^p}{8\sqrt2}\mathcal F_{p,T}(A(s)),\\
dN&=\mathfrak a_{d,T}(s)D(s)_+^{-1/2}
                       ds_1\,ds_2\,ds_3\,ds_4,\\
\mathfrak B_{d,T}&=\mathfrak a_{d,T}(0)>0.
\end{aligned}\tag{SM7}
```

G_T is zero at and above T. For A near one, substitute
`b_vec=sqrt(T²-A) z_vec`; the positive cubic closing factor in G_T factors
out `(T²-A)^(p/2+3)` times a smooth positive integral. Thus F is smooth near
A=1, including the whole moving spectator cap. No closing fibre is removed.
The determinant from (r,-2X,2(Y+W),2YW) to s has absolute value eight;
`dX dY dW=du_1 dv_1 d(Y-W)/8`. Summing the two square-root branches and the
two centers gives exactly the `1/(8 sqrt(2))` in SM7. The earlier slab's
`(T-u)/(2u)` weight would give a different answer and is not used.

The regular complement also needs its cap. At fixed u, a relation among
active phase differentials, with coefficient sum A_0, implies A_0 b_vec=0.
If A_0=0, at most three phases are independent, as follows directly from
the distinct source null covectors and the displayed phases. If A_0 is
nonzero, b_vec=0; the two vertical endpoint equations force separately the
weighted displacement sum in each parity to vanish. Horizontal balance
then allows a stationary one- or two-route contact only at gaps 0, 1/2 or 1.
For three routes, a same-parity pair has opposite unit components; equality
with the other parity either fails or sets its coefficient to zero, reducing
to gap one. None is at T. Fourfold closure has |b_vec|²=T²-1>0 and is already
integrated in SM7. Thus the remaining active phases and u=T boundary can
be used as independent coordinates. At that boundary keep T-u as a
nonnegative integration variable; the actual cubic G_T factor is smooth
in it. No differentiation through its zero extension is required.
Away from the two folded contacts this gives smooth phase densities,
including all closing pieces, and ordinary integer primitive powers.

## 7. Direct signed matching of all fifteen sectors

Use the sum-volume S=c_d sum (s_i positive)^q **only as an auxiliary phase**;
SM9 below restores the physical union. All fifteen nonempty active-positive
subsets must be matched. Set alpha=7/2, lambda_vec=(1,1,-1,-1), and
`P_alpha=alpha(alpha-1)(alpha-2)(alpha-3)=105/16`.
For an inactive complement of size k, its corner antiderivative is
`(-1)^k Gamma(1/2)/[Gamma(k+1/2) product(lambda_inactive)]`
times `(-lambda_active dot s_active)_+^(k-1/2)`.
This includes the inactive matching strips, not just the all-positive sector.

Here the direct-integration calculation K6–K8 can be reused **after** SM7's
new amplitude and cap have been verified. To reconstruct its remainder:
an inactive coordinate has derivative of D equal to minus its lambda plus
O(|s|), bounded away from zero. Transfer derivatives onto its smooth compact
weight until the only nonsmooth boundary is its actual inactive zero corner.
Far-cutoff terms remain smooth; they are not deleted. Repetition raises the
singular exponent and retains every lower-face term. Under s=w z, the
quadratic discriminant perturbation is O(w²); the inverse-square-root change
is O(w^(1/2)) in rescaled integral norm, by splitting a width-O(w) linear
band and integrating O(w)t^(-3/2) outside it. Its first antiderivative is
one-half Hölder, and subsequent ones are differentiable. Smooth-amplitude
remainders add an extra power. These estimates give the complete O(w^4)
primitive error with the integer terms, using only a finite derivative
budget at this fixed smooth amplitude. They do not differentiate an unknown
primitive remainder.

Four mixed antiderivatives of the leading density are
`(-lambda_vec dot s)_+^(7/2)/P_alpha`. Integrate by parts in all four
coordinates against `exp(-sum (s_i positive)^q)`, keeping compact cutoffs
until their lower-face and far terms have been matched. The mixed derivative
is the product of four positive Weibull densities. The all-negative
orthant's point contribution vanishes because this antiderivative is zero
at the origin. Let independent auxiliary Z_i have density
`q z^(q-1) exp(-z^q)` on z>0, and put U=Z_1+Z_2-Z_3-Z_4. These variables are
not the physical Poisson process. Then

```math
\begin{aligned}
C_q&=\frac{\mathbb E[(-U)_+^{7/2}]}
                 {P_\alpha\Gamma(1+7/(2q))}>0,\\
N_S^{1-\chi}(w)&=b_1w+b_2w^2+b_3w^3
                  +\mathfrak B_{d,T}C_qw^{7/2}+O(w^4),\\
R_d&=\prod_{k=4}^{\lfloor d/2\rfloor+1}(1-7/(2k))>0,\\
\mathfrak D_d(T)&=\frac{\beta_d\mathfrak B_{d,T}}{21}
 c_d^{-7/d}R_d\,\mathbb E[(-U)_+^{7/2}]>0,\\
-\beta_d\rho^b P_{\rho,S}^{1-\chi}
 &=\mathfrak D_d(T)\rho^{1-5/d}+O(\rho^{1-6/d}).
\end{aligned}\tag{SM8}
```

The threshold defining N_S is S<=c_d w^q; w is squared proper phase, not
IN6's u or GT's volume variable. All physical weights are retained. The
ordinary primitive powers are killed for d>=5. The fractional multiplier
is `product(1-7/(2k))=-(5/16)R_d`; with the negative action prefactor and
P_alpha it gives precisely 1/21. This computes the sign without fitting.
The auxiliary moment is finite and strictly positive by symmetry,
nondegeneracy and exponential tails. As a calibration, q=1 gives C_1=22/105,
not the all-positive sector's 2/35. Both matching sides are indispensable.
The O(w^4) response uses signed Stieltjes integration and the full kernel
tail, not the derivative of that O-term. Constant continuation of the
physical primitives and full-half-line continuation of subtracted powers
retain all upper endpoints.

### Restore the union before stating an action theorem

Thin individual quotient diamonds project injectively; distinct null arcs
are separated away from both tips. At either tip, the two separated null
linear forms bound the common volume by `C(s_i positive s_j positive)^q`.
Consequently `0 <= S-W <= C sum (s_i positive s_j positive)^q`.
On the sublevel comparison shell, two active phases are independent; moving
the target in a fixed future timelike direction makes every active phase
increase. The shell thickness is O(w^(q+1)), and its second active coordinate
has width O(w). This is the geometric FL5–FL9 proof, which explicitly permits
bounded endpoint weights and face indicators. It applies to the actual
compact suspension domain, not only to spacelike faces. It yields

```math
\begin{aligned}
|N_W^{1-\chi}(w)-N_S^{1-\chi}(w)|&\le Cw^{q+2},\\
\rho^b|P_{\rho,W}^{1-\chi}-P_{\rho,S}^{1-\chi}|&=o(1),\\
\mathcal A_{\rho,5}(M_T)&\longrightarrow
                      2V_Y+\mathfrak D_5(T)>2V_Y,\\
\rho^{-(1-5/d)}\mathcal A_{\rho,d}(M_T)&\longrightarrow
                         \mathfrak D_d(T)>0,\qquad d\ge6.
\end{aligned}\tag{SM9}
```

Every overlap and higher multiplicity is covered by the pairwise upper
bound, not replaced by pairwise inclusion–exclusion. The phase comparison
is an o(1) **difference** estimate; no route-kernel sum is introduced. SM5
restores the complete point and both local screens, including original
physically short and long origin partners. The union error, all regular
pieces and all matching strips are then included before SM9. This supplies
a complete-action theorem, not an isolated folded-sector response.
Constants are uniform on compact width subintervals of `(1,sqrt(5)/2)`.
No uniform width/density crossover at T=1 is claimed. For d>=6 the displayed
conclusion is a leading-growth theorem for the complete action; the
O(rho^(1-6/d)) error is **not** a growth-plus-finite o(1) expansion.
In d=5 it is a genuine finite limit, with an independently specified
nonlocal correction and vanishing full remainder. Here V_Y=20: the local
prediction is 40, while the actual limit is strictly greater than 40.

## 8. Adversaries, expectation and the exact extension boundary

**Flat diamond:** for Y one point, SM3–SM5 give the point and the constant
2; keeping finite upper tails gives exactly `2(1-exp(-rho T²/2))`.
IN8 still annihilates its limit. No boundary constant was extracted from the
differentiated equation, and no small-width/density limits were interchanged.

**Spherical focal growth:** for Y=S² x T³_L, R_Y^tot=2 V_Y. Thus SM5 gives
`V_Y(T²/2+2)`, exactly the independent finite term in IU8. IN10's spectator
integration still gives the actual NP closing weight; it does not modify
IN5's endpoint-conditional nonlinear phase. IU3–IU8's full radial/opening
resolution, secondary seven-halves transition, entire meridian term
`log(5/2)/3`, fourth kernel zero and uniform remainder yield the remaining
`gamma(T) rho^(2/7)+o(1)`. Both sides and both tails remain. SM5 is compatible
with that complete result and cannot erase its positive correction above
pi. Neither the spherical normal form nor SM7's finite lift geometry is
asserted for an arbitrary Y.

**What the new obstruction rules out:** even perfectly planar null faces,
constant interior density, zero curvature and absence of conjugate points
do not force the independent local target after origin matching. Any
purported universal correction that is zero on all such flat suspensions
is refuted by the d=5 complete limit in SM9. The nonlocal term records a
physical cut/holonomy interaction, not a curvature/focal delta. Failure of
a proposed estimate alone was not used as a counterexample. The new
geometric coefficient is SM7–SM8's convergent integral, not a name for the
remaining action. This is stronger evidence than IN8's loss of information,
but it still does **not** prove the corrected arbitrary-metric theorem.

**Separate original-law expectation:** every suspension here has finite
atomless metric volume, standard Borel structure, measurable ambient closed
order and measurable exclusive intervals. The t+z/t-z argument establishes
containment; null pairs have product-volume zero without changing closed
discrete order. Finite Poisson cardinality has the needed second moments,
and each layer is bounded by its square. The already proved finite-density
ordered Mecke/layer-factorial identity therefore transfers each **completed
deterministic** conclusion: SM5's assembled local-width and all-width d=2,3
corollaries, SM9 and the retained IU spherical result. Both intensities and the point occur once.
No expectation/limit interchange, variance or sample-wise claim follows.
SM5's unresolved arbitrary-width complementary pairing receives no new
general expectation-limit claim.

**Beyond suspensions:** the exact flat-block boost, endpoint overlap G_T
and curvature profiles SM2 are product-specific. General nonproduct
null/mixed boundaries, non-common-tip fibres and merging/singular-end
interactions cannot inherit them merely from containment or smoothness.
General cap transport IN2 and the complete signed GT2 route remain possible
alternatives; neither GT10 nor separate sector traces are necessary closure
gates. #156 retains the remaining producers; #81 retains the corrected
general consumer. #177 remains unresolved, #94/#86 retain scrutiny and
provenance, and claim-to-Lean mapping #185 is deferred. No historical
certificate, original issue body or acceptance criterion is changed.

**Plain language:** the missing local terms are now recovered rather than
lost in differentiation. But removing them does not leave a universally
negligible remainder: even a flat compact cross-section can leave a finite
extra charge through its global identifications. The unresolved task is to
compute or control those complete signed nonlocal contributions for the
original general geometry, not to assume them away.

The accompanying `null_suspension_matching.py` diagnostics test finite
moment identities, parity and logarithmic normalization, endpoint weights,
physical partitions and the new geometric coefficient. They do not certify
the uniform asymptotic arguments or replace independent scrutiny. No action,
probability, Lean/checker, dependency or workflow input is changed.
