# First-cut cubic-torus intervals and complete action (#149)

**Written dimension-indexed theorem, not a new Lean result or independent
human review.** The complete deterministic and then expected action tend to
zero for every member of the first-cut family below. The actual overlap
creates a nonzero higher-order fractional primitive in odd dimensions; it is
retained and evaluated, not assumed away. This is the approved bounded family from
[#149's plan](https://github.com/q5m-ai/causal-set-emergence/issues/149#issuecomment-6081311428),
not arbitrary-flat-manifold coverage. Base:
`97cd77e10cf0a45c338906080c5d24c598235fdd` on
`issue-81-general-coverage`. The merged [Minkowski theorem](all-dimensional-flat-limit.md)
and its hypotheses, equations and verification status are unchanged.

#149 owns this flat multiple-route continuation. #151 retains the general
nonlocal interface and curved caustic-response classification. Reuse the
[existing thin-torus theorem](full-partner-globalization.md#5-an-actual-full-partner-long-producer-thin-torus-in-every-dimension),
[actual short theorem](general-metric-short-remainders.md#8-quantified-short-theorem-partition-cancellation-and-the-151-boundary)
and [dimension-indexed measured-order bridge](../formal/DIMENSION_EXPECTATION.md#first-bridge-arbitrary-finite-measured-orders).
None is extended by an unsupported change of its geometric hypotheses.

## 1. Fixed geometry, order and independent target

Fix an integer d at least two. Write k=d-1, p=d-2 and q=d/2. Let

```math
\begin{aligned}
X&=\mathbb R^k/(L\mathbb Z)^k,\\
M&=(-T/2,T/2)\times X,\\
g&=dt^2-h_{\mathrm{flat}},\\
L&>0,\qquad L/2\lt T\lt L/\sqrt2.
\end{aligned}
\tag{FC1}
```

The torus measure is induced Euclidean volume, of mass L to power k, not a
probability-normalized measure. The selected ambient order is
`s-t >= d_X(a,b)`, with the ordinary Euclidean quotient distance, not a
maximum product distance. Completeness of X makes the ultrastatic product
globally hyperbolic; more directly, causal curves have spatial speed at most
one, compact diamonds, and inextendible curves cross every time slice. If a
curve had bounded time range, its spatial Lipschitz bound and completeness
would give an endpoint and a continuation.

Time monotonicity proves ambient closed-interval containment in M for its
endpoints, separately from global hyperbolicity. The closure is compact;
the two entire frontier faces are compact smooth achronal spacelike slices.
Their joint is empty, as expressly permitted by G-SS. There are no additional
strata. Independently, curvature and the joint target are both zero. This
is a positive-volume member of the unchanged core, not a vacuous empty action.

Use the [shared constants and signed pieces](dimension-producer-interface.md)
without alteration. Choose one fixed temporal cutoff below L/2 and below the
applicable short theorem's bound. Equality belongs to long; the physical point
belongs to short once. No density-dependent cutoff is used.

## 2. Geometric gate: lifts, injectivity and the actual union

Work in the cover, with source (0,0), target (tau,a) on the quotient and
0<=tau<T. Causal target lifts are exactly the vectors `a+Lm` of norm at most
tau, for integer vectors m. A lifted causal curve has length at most tau;
conversely the straight segment to any such lift is causal.

**At most two lifts.** Any two causal lifts differ by a lattice vector of norm
at most 2tau, strictly below the square root of two times L. A nonzero such
vector must be one signed coordinate vector times L. Three distinct lattice
points cannot all have pairwise differences of that form: two distinct unit
coordinate displacements have difference of length at least the square root
of two, unless they coincide. Thus three causal lifts are impossible. If two
exist, they differ by exactly one signed coordinate period. Their mutual
separation also gives tau>=L/2. This includes equality and null lifts.

**Each individual diamond projects injectively.** At cover time s, a diamond
slice is contained in both its source ball of radius s and its target ball
of radius tau-s. Its diameter is at most `2*min(s,tau-s)<=tau<L`.
Two different points with the same quotient image differ by a nonzero lattice
vector of length at least L and have the same time. They therefore cannot
belong to that slice. Projection is a local isometry and preserves the
volume of the whole diamond, including its zero-volume null case.

**The projected union is the entire interval.** A point between the quotient
endpoints lies on a concatenation of two causal curves. Lifting that curve
from the chosen source puts the point in a diamond to one of the causal target
lifts. Conversely each cover diamond projects into the ambient interval.
Endpoint removal changes no volume. Consequently, with D_m the cover diamonds,

```math
\begin{aligned}
I_M(x,y)&=\bigcup_{m:\ |a+Lm|\le\tau}\pi(D_m)
\quad\text{up to its removed endpoints},\\
V_M(x,y)&=\mathrm{Vol}\left(\bigcup_m\pi(D_m)\right),\\
V_M(x,y)&=\int_X[\tau-d_X(0,z)-d_X(z,a)]_+\,d\mathrm{vol}_X(z).
\end{aligned}
\tag{FC2}
```

The last identity integrates the actual allowed time interval at each spatial
point. It is neither a sum over path counts nor a chosen shortest-branch
volume. It gives an independent full-interval diagnostic.

### Both overlap components, not just one

When two lifts exist, orient the distinguished axis and write their spatial
vectors as `(s+L/2,b)` and `(s-L/2,b)`. Put

```math
\begin{aligned}
x&=\tau^2-(s+L/2)^2-|b|^2,\\
y&=\tau^2-(s-L/2)^2-|b|^2,\\
a(x,y)&=L^2/4+(x+y)/2+(y-x)^2/(4L^2),\\
s&=(y-x)/(2L),\qquad \tau=\sqrt{a(x,y)+|b|^2},\\
\left|\frac{\partial(\tau,s)}{\partial(x,y)}\right|&=\frac1{4L\tau}.
\end{aligned}
\tag{FC3}
```

Here x,y are branch squared proper times, not endpoint names. They are
nonnegative in the two-lift region. Let H be the cover volume of the two
diamonds' common-source intersection. Intersections of the first diamond
with translates of the second can occur only for translations 0 and L along
the distinguished axis. Indeed translation Lm would require
`2*tau >= L*(|m|+|m-e_1|)` by the future and past ball intersections. All other
integer m give a right side at least `(1+sqrt(2))*L`, or `3*L` on that axis,
which is larger than 2T.

The untranslated intersection has cover time at most tau-L/2. The translated
one has time at least L/2. They are disjoint since tau<L. Time reversal
combined with spatial reflection interchanges these intersections and
preserves volume. Both must be subtracted:

```math
\begin{aligned}
V(x,y)&=c_d(x^q+y^q)-2H_d(x,y;L).
\end{aligned}
\tag{FC4}
```

The factor two counts the source and target overlaps, not two copies of the
physical point or the physical pair. On a single-lift pair, the actual volume
is just the usual one-diamond value.

## 3. Exact overlap integral and a uniform small-phase bound

A Lorentz boost in the transverse b direction sends the two target events
in the cover to time h=sqrt(a(x,y)) and transverse coordinate zero. This is
only a change of variables in a cover-volume calculation, **not** a global
Lorentz transport of the periodic spacetime. The distinguished spatial
period L is unchanged. Define the two positive null excesses

```math
\begin{aligned}
U&=h-L/2-s=\frac{x}{h+L/2+s},\\
W&=h-L/2+s=\frac{y}{h+L/2-s},\\
x&=U(L+W),\qquad y=W(L+U).
\end{aligned}
\tag{FC5}
```

In cover null coordinates u=t-z_1, v=t+z_1 the common-source intersection is
`0<=u<=U`, `0<=v<=W`, with squared transverse radius bounded by the minimum
below. Ordinary Euclidean transverse-ball volume, and `dt*dz_1=du*dv/2`, give

```math
\begin{aligned}
H_d(x,y;L)&=\frac{v_p}{2}\int_0^U\int_0^W
 \min\{uv,(U-u)(L+W-v),(L+U-u)(W-v)\}^{q-1}\,dv\,du,\\
v_p&=\frac{\pi^{p/2}}{\Gamma(1+p/2)}.
\end{aligned}
\tag{FC6}
```

For p=0 the transverse fibre has counting volume one whenever the inequalities
hold; thus H_2=UW/2. If x or y is zero, H=0. No power-zero convention assigns
mass to an empty integration rectangle.

Replacing the minimum by uv supplies an upper bound, not an equality. After
u=U*alpha and v=W*beta, the other terms can be smaller only in the strips
`alpha>1-W/(L+W)` or `beta>1-U/(L+U)`. Their total area is at most `(U+W)/L`,
and the rescaled integrand is bounded by one. Its limiting integral is
`1/q^2`. Since U<=x/L and W<=y/L, this proves, uniformly including axes,

```math
\begin{aligned}
0\le H_d(x,y;L)&\le\frac{v_p}{2q^2L^{2q}}(xy)^q,\\
H_d(x,y;L)&=h_d(xy)^q\left(1+O_{d,L}(x+y)\right),\\
h_d&=\frac{v_p}{2q^2L^{2q}}.
\end{aligned}
\tag{FC7}
```

The multiplicative estimate is read as an absolute error bound at an axis,
where both sides vanish. It follows from actual compact fibre integrals; no
jet or cancellation is a geometric hypothesis. Also the actual union contains
each diamond, so its volume lies between the largest individual diamond
volume and their sum. These inequalities will control its actual sublevels.

## 4. Exact finite-density full-partner identity

Restore any finite ordered source/target partition sum before using spatial
translation invariance. Integrating both endpoint times gives their overlap
length T-tau, not T and not one fixed endpoint time. For unit fields,

```math
\begin{aligned}
P(\rho)&=L^k\int_0^T(T-\tau)\int_X
 \mathbf1_{\{d_X(0,a)\le\tau\}}K_d(\rho V_M(\tau,a))
 \,d\mathrm{vol}_X(a)\,d\tau,\\
\mathcal A_{\rho,d}&=a_d\rho^{1/q}L^kT
 -\beta_d\rho^{1+1/q}P(\rho).
\end{aligned}
\tag{FC8}
```

Temporal long replaces the time domain by `[delta,T]`. Finite volume and the
bounded polynomial-exponential kernel justify signed Fubini. Equality remains
assigned to long. The interface's exact opposite-signed cutoff correction is
retained if another mask is used; no macroscopic shell is assumed to vanish.

## 5. Actual complete long primitive and exact regular-complement matching

Let N-delta(w) be G5's actual long-pair primitive, using the threshold
`V_M<=c_d*w^q`. Introduce a **reference** that counts each causal lift separately
and uses its individual diamond volume. Unfolding the fundamental cube makes
its primitive exactly

```math
\begin{aligned}
N_{\mathrm{ref}}^\delta(w)&=\frac{L^ks_d}{k}
 \int_\delta^T(T-\tau)
 \left[\tau^k-(\tau^2-w)_+^{k/2}\right]d\tau.
\end{aligned}
\tag{FC9}
```

This reference is not the action or interval volume of the thick torus. Its
functional form is the existing thin-torus radial integral, now justified
as a lift-counted auxiliary quantity. In the one-lift region it agrees with
the actual primitive exactly. In the two-lift region it counts two indicators
and must be corrected. This matching is at finite phase, not a presumed
negligible complement.

There is one two-route patch for each of the k coordinate directions. A
coordinate in `(L-T,T)` about L/2 describes both sides of that quotient seam
once. Two such patches cannot overlap on causal pairs by the lift-count
proof. Also `|b|^2<T^2-L^2/4<L^2/4`, so the transverse coordinates lie strictly
inside their fundamental cube. Equations (FC3) and (FC4) therefore yield

```math
\begin{aligned}
F(A)&=\frac1{4L}\int_{\mathbb R^p}
 \frac{[T-\sqrt{A+|b|^2}]_+}{\sqrt{A+|b|^2}}\,db,\\
C(w)&=\int_0^\infty\int_0^\infty F(a(x,y))
 \mathbf1_{\{V(x,y)\le c_dw^q\}}\,dy\,dx,\\
S(w)&=\int_0^w\int_0^\infty F(a(x,y))\,dy\,dx,\\
N^\delta(w)&=N_{\mathrm{ref}}^\delta(w)+L^k k\,[C(w)-2S(w)].
\end{aligned}
\tag{FC10}
```

F is zero for A>=T squared; in p=0 its integral is evaluation at the single
point. The two strip terms are equal by x/y symmetry. The factor k counts
axes, not two copies of each identified face. Since every two-lift pair has
tau>=L/2>delta, the transition patch is entirely long. The reference still
retains its temporal cutoff contact. F retains the entire closing contact
at tau=T and the time weight T-tau. No endpoint time or transverse partner
has been fixed or discarded.

### Derived smoothness, including the closing boundary

Set D=T squared minus A. Rationalizing T minus the square root and rescaling
b by sqrt(D) gives, for D>0,

```math
\begin{aligned}
F(A)&=\frac{D^q}{4L}\int_{|z|\le1}
 \frac{1-|z|^2}
 {\sqrt{A+D|z|^2}\,[T+\sqrt{A+D|z|^2}]}\,dz.
\end{aligned}
\tag{FC11}
```

This also holds for p=0 with point mass one. Near A0=L squared/4 the margin
T squared minus A0 is fixed and positive, and all differentiated integrands
have compact common bounds. Thus F is smooth there. Near A=T squared it is
`D^q*G(A)`, with G smooth through that endpoint; this factor retains, rather
than ignores, the closing boundary. The argument only uses A bounded away
from zero.

For x near zero, the positive y support in the strip is exactly

```math
\begin{aligned}
Y(x)&=x-L^2+2L\sqrt{T^2-x}>0.
\end{aligned}
\tag{FC12}
```

It is the actual root of a(x,y)=T squared. On y=Y(x)*v, `0<=v<=1`, its
remaining depth is
`D=Y(x)*(1-v)*[1/2+(Y(x)*(1+v)-2*x)/(4*L^2)]`.
The bracket is smooth and strictly positive for sufficiently small |x|.
Consequently S-prime is an integral over `[0,1]` of `(1-v)^q` times a smooth
amplitude whose x derivatives of any fixed order are bounded. Differentiation
under that integrable fixed weight proves S is smooth at zero, with S(0)=0.
It does not differentiate an unaccounted moving upper boundary or require
that F itself be smooth through its zero extension at A=T squared. Negative
x or w below are used only to extend these amplitude formulas for Taylor's
theorem; they do not add acausal pairs to the observable.

The reference (FC9) is smooth for |w|<delta squared/2: tau is bounded below
by delta and the original time domain is fixed. This is the same derived
regularity mechanism as the existing thin-torus long proof, not an extension
of its physical unique-lift hypothesis to this slab.

## 6. The actual crossover primitive, including its fractional sector

First keep the sum of the two diamond volumes but temporarily omit their
overlap. Define

```math
\begin{aligned}
C_0(w)&=w^2\int_{\substack{u,v\ge0\\u^q+v^q\le1}}
 F(a(wu,wv))\,du\,dv,\\
N_{\mathrm{sm}}^\delta(w)&=N_{\mathrm{ref}}^\delta(w)
 +L^k k\,[C_0(w)-2S(w)].
\end{aligned}
\tag{FC13}
```

For sufficiently small |w|, the argument of F stays in its smooth
neighborhood of A0. The displayed fixed quarter-ball has finite area and
bounded u,v. All finite w derivatives are dominated by constants there.
Thus C0 and N-sm are smooth at zero, and N-sm(0)=0. This proves integer
Taylor expansions for the *matched* regular and sum-volume contributions.
It has not yet justified omitting the overlap from the real interval.

For that overlap use q-polar coordinates in the positive (x,y) quadrant:

```math
\begin{aligned}
x&=r\,t^{1/q},\qquad y=r(1-t)^{1/q},\qquad 0\le t\le1,\\
dx\,dy&=\frac r q[t(1-t)]^{1/q-1}\,dr\,dt,\\
\frac{V(x,y)}{c_d}
 &=r^q-\lambda_d r^{2q}t(1-t)
   +O_{d,L}\bigl(r^{2q+1}t(1-t)\bigr),\\
\lambda_d&=\frac{2h_d}{c_d}.
\end{aligned}
\tag{FC14}
```

The remainder is uniform up to t=0,1 by (FC7); it is not an expansion at
fixed nonzero t followed by an unjustified endpoint integral. The union
contains both individual diamonds, hence a point with `V<=c_d*w^q` has
`x<=w`, `y<=w`, and `r<=2^(1/q)*w`. It also contains the quarter-ball r<=w.
Thus only a uniformly small shell must be added to C0.

For fixed t the actual volume increases strictly with r. One way to see
this without differentiating a singular volume formula is to use (FC5):
as x and y increase along their ray, both U and W increase. In fact
`r*dU/dr=U*(L+U)/(L+U+W)` and the analogous formula holds for W. The two
future tips then move by the same future-causal vector in the cover. Their
projected union increases, with a positive-volume increase whenever r does.
The actual shell therefore ends at one root r_w(t). The uniform bound just
given and (FC14), or a two-sided Taylor sandwich, give

```math
\begin{aligned}
r_w(t)&=w+\frac{\lambda_d}{q}w^{q+1}t(1-t)
 +O_{d,L}\bigl(w^{q+2}t(1-t)\bigr).
\end{aligned}
\tag{FC15}
```

At t=0 or 1 the root is exactly w. For the sandwich, first use (FC7) and
`r<=2^(1/q)*w` to bound `r-w` by `C*w^(q+1)*t*(1-t)`. Substitution into
(FC14) gives (FC15); the quadratic inverse error is at most the displayed
error because q>=1. This avoids an assumed uniform smooth inverse at either
axis.

Integrate the **actual** shell from w to r_w with the Jacobian in (FC14).
There F equals F(A0)+O(w), uniformly. Its endpoint weight is integrable,
including in every higher dimension. The ordinary convergent beta integral
then proves

```math
\begin{aligned}
C(w)-C_0(w)&=\kappa_d w^{q+2}+O_{d,L,T}(w^{q+3}),\\
\kappa_d&=F(L^2/4)\frac{\lambda_d}{q^2}
 \mathrm{B}(1+1/q,1+1/q)>0,\\
N^\delta(w)&=N_{\mathrm{sm}}^\delta(w)
 +D_d w^{q+2}+O_{d,L,T}(w^{q+3}),\\
D_d&=L^k k\kappa_d>0.
\end{aligned}
\tag{FC16}
```

Positivity is geometric: T>L/2, so F(A0)>0. The overlap term is genuinely
fractional for odd d, and is **not** discarded or folded into a presumed
smooth jet. In even d it is an integer-power contribution. The estimates
exclude logarithmic or other nonpolynomial modes at or below the displayed
order; they do not assert analyticity of the entire actual primitive.

As an independent 2D check, in the two-route sector the full interval volume
is exactly `L*(tau-L/2)`, independent of the circle displacement. Consequently
for sufficiently small w its actual two-route primitive, before the spatial
factor L, is

```math
\begin{aligned}
C(w)&=\frac{T-L/2}{4L^2}w^2-\frac1{12L^3}w^3\qquad(d=2).
\end{aligned}
\tag{FC17}
```

This follows by integrating both endpoint times and the full two-route circle
width `2*(tau-L/2)` through `tau=L/2+w/(2*L)`. It checks the overlap and both
route multiplicities; it is not the proof in other dimensions.

## 7. Critical signed response and complete deterministic theorem

Let n=floor(d/2). Taylor-expand the derived smooth N-sm through degree n+1.
Equation (FC16) gives actual coefficients b_j and a summable remainder:

```math
\begin{aligned}
N^\delta(w)&=\sum_{j=1}^{n+1}b_jw^j+R(w),\\
|R(w)|&\le C\bigl(w^{n+2}+w^{q+2}\bigr),\\
R(w)/w^{q+1}&\longrightarrow0.
\end{aligned}
\tag{FC18}
```

For even d the two powers in the bound are q+2; for odd d the first is
q+3/2. This is the proposed critical-order estimate **proved from the actual
interval**, not an admissibility field. In particular the overlap was allowed
to have its real fractional term before its response was tested.

Apply the existing exact signed Stieltjes identity G5–G6. Continue the actual
primitive constantly beyond its finite support, not by zero. Its zero atom
is absent, as verified below. The derivative polynomial is killed by the
actual moments M_d(0),...,M_d(n). After that signed cancellation, (FC18)
bounds the rescaled residual near zero and makes it tend to zero. Away from
zero boundedness of the primitive and the subtracted polynomial supplies a
global bound for their difference divided by `w^(q+1)`; its degree is at most
q+1. The integrable absolute envelope `z^(2*q)*abs(K_d'(z^q))` in G6 now
justifies dominated convergence. Equivalently, the actual fixed-positive-phase
complement has an exponentially small normalized kernel response. Neither
argument discards a macroscopic almost-null partner or a cutoff endpoint.

The retained overlap primitive alone has the following signed asymptotic,
by G7 and (FC16):

```math
\begin{aligned}
L_{\mathrm{overlap}}(\rho)&=
 -\beta_d(q+2)D_dc_d^{-(q+2)/q}M_d(q+1)\rho^{-1/q}
 +o(\rho^{-1/q}).
\end{aligned}
\tag{FC19}
```

Here M_d is the unchanged ordinary Mellin moment. M_d(q+1) is nonzero: every
factor in its product has a nonzero argument. Thus the fractional sector has
an actual nonzero signed response, but it decays rather than survives the
limit. This is a sector asymptotic, **not a rate assertion for the complete
action**. No divergent moment or analytic continuation was used.

**Theorem (every dimension in the first-cut family).** For each fixed (FC1)
and every sufficiently small fixed temporal cutoff, the actual signed long
contribution tends to zero. The proved general short theorem S30 applies to
this precise smooth G-SS member; for unit fields its bulk and joint terms
are zero. It supplies the actual short point cancellation and all face terms,
not merely a model coefficient. At each density the two pieces partition
every selected ordered pair, with the point once. Therefore

```math
\begin{aligned}
L^\delta_{1,1}(\rho)&\longrightarrow0,\\
S^\delta_{1,1}(\rho)&\longrightarrow0,\\
\mathcal A_{\rho,d}(M,g)&\longrightarrow0.
\end{aligned}
\tag{FC20}
```

No new special-case short proof is needed. Restoring a finite endpoint atlas
first gives exactly the same full action and point weight, including every
off-diagonal label. Individual weighted-cell long jets are not claimed. The
temporal cutoff is the short theorem's cutoff; the older radial-null mask
is not silently identified with it. All margins and L,T are fixed before
density varies. No uniformity as T approaches either end of the band is
asserted.

## 8. Separate all-dimensional measured-order expectation specialization

This step does **not** extrapolate #137's concrete 4D instance. For each k,
the finite product of k length-L circles is a compact metrizable standard
Borel space. Fundamental-cube transport constructs its induced volume with
mass L to power k; time product and restriction give a finite atomless Borel
measure of mass `L^k*T` on M. Atomlessness follows already from the Lebesgue
time factor. No probability-normalized spatial volume is substituted.

The quotient distance is continuous and satisfies the triangle inequality.
Thus the relation `s-t>=d_X(a,b)` is closed, reflexive and transitive;
antisymmetry follows because both time differences can be nonnegative only
at equal times, when distance must be zero. Its interval indicator on triples
is Borel. Tonelli supplies actual exclusive-interval-volume measurability,
and that volume is bounded by the total finite measure. Time monotonicity
proves containment; the endpoint sets have zero volume. Formula (FC2), not
a flat single-route substitution, is its actual interval measure.

For fixed source, null-related targets have time exactly `t+d_X(a,b)`;
Fubini gives zero target volume and then zero product pair volume. A strictly
timelike pair contains an open positive-volume subinterval. Consequently
V_M is zero only on this pair-null set, proving the no-zero-atom fact used
in section 7 without deleting any neighborhood of the cut locus.

Construct the probability law independently as `FinitePoisson.law` of rho
times this restricted measure. Finite atomless intensity gives almost-sure
simplicity. The finite support inherits the actual partial order; exclusive
interval counts use every intermediate sprinkled point, not paths or lifts.
Each ordered layer count is bounded by squared cardinality, whose Poisson
second moment is finite. The finite dimension-indexed layer sum is thus
absolutely integrable.

These discharge, in writing for **every d**, the hypotheses of the existing
generic theorem `dimensionFiniteMeasureAction_expectation` in
`formal/BoundaryDraft/DimensionMeasureExpectation.lean`. Its one-point and
two-point Mecke factors, factorial layer coefficients and density powers
are unchanged. Only now apply the exact equality to (FC20):

```math
\begin{aligned}
\mathbb E_{\mathrm{Pois}(\rho\mu_g|_M)}A^{\mathrm{disc}}_{\rho,d}
 &=\mathcal A_{\rho,d}(M,g)\qquad(\rho>0),\\
\mathbb E_{\mathrm{Pois}(\rho\mu_g|_M)}A^{\mathrm{disc}}_{\rho,d}
 &\longrightarrow0.
\end{aligned}
\tag{FC21}
```

This is a written all-dimensional specialization of a generic checked bridge,
not a newly compiled torus instance. Dimension two uses the existing
dimensionless action; no division by d-2 is introduced. No sample-wise
convergence or variance claim follows.

## 9. Coverage, regressions and verification boundary

| Obligation | Output here | Boundary |
| --- | --- | --- |
| Geometry before asymptotics | At most two causal lifts; individual projection injectivity; exact union and both overlap components | Only L/2<T<L/sqrt(2), fixed cubic periods and ultrastatic slab |
| Actual full-partner primitive | FC9–FC10 exact matching; closing time/cutoff/partition boundaries retained | No same-chart or shortest-route replacement |
| Critical estimate | FC11–FC18 derive smooth matched terms and the actual overlap remainder | No desired polynomial jet is a hypothesis |
| Fractional/log sectors | FC16 and FC19 retain and evaluate the odd-dimensional fractional term; no earlier logarithm survives | No assertion of global analytic phase inversion |
| Complete limit | FC20 consumes the actual short theorem, with the point once | No complete-action rate or shrinking cutoff |
| Expectation | Actual dimension-indexed order, volume, intervals and Poisson hypotheses discharged before FC21 | #137's concrete 4D instance is not an all-dimensional instance |
| Prior work | #157 and the thin-torus results preserved; #138's thin formal port not duplicated | No extrapolation of this family to all flat manifolds |
| Verification | Conventional proof with executable regressions | No new Lean proof, full Lean audit or independent human mathematical review |

`first_cut_flat_torus.py` evaluates actual finite-phase geometry and primitive
components, not a synthetic assumed jet. Its regressions compare independent
interval distance integrals, complete finite lattice enumerations, both
projected overlaps, closing time weights and the matched primitive. Negative
controls omit a route, an overlap or a partition/point contribution. Odd and
even dimensions, the 2D empty-joint case and high-dimensional overlap scaling
are included. Passing tests does not certify the uniform asymptotic proof.

The family does not cover higher-multiplicity lattice intersections, general
flat holonomy, non-ultrastatic flat spacetimes or arbitrary G-SS faces. Those
remain **#149 obligations under its unchanged acceptance contract**, not new
exclusions. #149 owns the flat estimates here; #151's curved caustic
classification is neither duplicated nor discharged. #81 retains general
assembly and #86 independent review and any justified formal port.
#149/#81/#24 remain open.

No Lean source, checker, dependency or build input changes. No new compiled
all-dimensional geometry or limit is claimed. Any eventual formal port needs
its own final integrated source/warnings/transitive-axiom audit. Human expert
checking of the union multiplicity, matched primitive and expectation
specialization remains outstanding. No agents, merge or deployment.

Reproduce the executable and authoring checks with:

```sh
.venv/bin/python -m unittest -v test_first_cut_flat_torus test_full_partner_globalization
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

Refs #149, #150, #151, #77, #137, #138, #81, #86, #24.
