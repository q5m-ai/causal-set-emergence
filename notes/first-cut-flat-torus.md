# First-cut cubic-torus intervals and complete action (#149)

**Written-first continuation; geometric gate established below, analytic
continuation in progress.** This is the approved bounded family from
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
V(x,y)=c_d(x^q+y^q)-2H_d(x,y;L).
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

## 5. Current stopping boundary

The lift count, individual projection injectivity and actual union formula
hold in the approved width band. Equations (FC4) and (FC6) retain **both**
projected overlap components. The next obligation is the complete long-volume
primitive with the regular complement and closing contacts included, followed
by the actual short/expectation assembly. No completed asymptotic theorem is
claimed in this intermediate geometric checkpoint.

The family does not cover higher-multiplicity lattice intersections, general
flat holonomy, non-ultrastatic flat spacetimes or arbitrary G-SS faces. Those
remain #149 obligations under its unchanged acceptance contract, not new
exclusions. #149/#81/#24 remain open. No Lean port, independent human review,
merge, deployment or sample-wise result is claimed.

Refs #149, #150, #151, #77, #137, #138, #81, #86, #24.
