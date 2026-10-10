# Finite lifts, physical unions and the remaining flat producer (#149)

**Written proofs, not new Lean results or independent human review.** Starting
from the [approved reduction plan](https://github.com/q5m-ai/causal-set-emergence/issues/149#issuecomment-6091668078),
this note proves the finite-lift and finite-cone reduction for **every flat
G-SS region in every integer dimension at least two**, without global
developing-map injectivity. It then goes beyond the reduction: the difference
between the physical-volume and sum-of-diamond-volume primitives is above
critical order, including arbitrary multiplicity and self-overlap. Section 7
then derives the sum-volume primitive through cubic order and proves the full
deterministic and expected limit for **all flat G-SS regions in dimensions
two, three and four**, not another example family. The critical producer in
dimensions five and above remains unresolved; section 8 identifies the
failed extensions and the exact residual. No general flat limit or
counterexample is asserted.

Base: `81d99e4bb247b308b33d1917922f43a6fb69c8c0` on
`issue-81-general-coverage`, including #157 and #162. Their statements and
proofs, the shared action, and the original #149/#81/#24 contracts are
unchanged. #149 owns this flat continuation; #151 retains the shared nonlocal
interface and curved focusing classification. The later authorization to
continue replaces the plan's intermediate approval stop, not its mathematical
conditions or the prohibition on unapproved merge/deployment.

## 1. Quantifiers and unchanged observables

Let d be any integer at least two. Let Q be a smooth, time-oriented globally
hyperbolic flat Lorentzian manifold, and M a smooth G-SS region in Q, exactly
as in [the original contract, section 3](general-contract.md#3-a-precise-non-vacuous-general-core-candidate).
In particular M is open, precompact and ambient causally convex; its whole
frontier consists of the two labeled achronal spacelike faces and their
transverse joint. Empty joint and disconnected regions are allowed. Flatness
means vanishing Riemann tensor, not an assumed quotient presentation.

Use the ambient order restricted to M, both Lorentzian endpoint measures,
the exclusive interval, and the existing dimension-indexed constants. Fix a
smooth Cauchy temporal function t. Put q=d/2, n=floor(d/2), K=closure(M), and
use strict temporal short/equality long, with the physical point in short
once. The independent flat target is

```math
\begin{aligned}
\mathcal J(M)&=\int_J\coth\theta\,dA_g,\\
\ell(x,y)&=t(y)-t(x),\\
N_V^\delta(w)&=\int_{M\times M}
 \mathbf1_{\{x\preceq y,\ \ell\ge\delta,\ V_M(x,y)\le c_dw^q\}}
 \chi(x)\phi(y)\,d\mu_g(x)d\mu_g(y).
\end{aligned}
\tag{FL1}
```

The fields may be bounded smooth real fields; auxiliary smooth pair weights
are allowed too. Constants below depend on the fixed compact geometry,
dimension, fields and cutoff, never on density. Statements of small-phase
bounds concern sufficiently small positive w. No density-dependent geometry,
cutoff, global graph, combined slope budget or finite-contact-type hypothesis
is introduced.

## 2. The universal cover and faithful individual diamonds

### Compact causal control also controls the cover

Take a smooth complete auxiliary Riemannian metric h on Q. The compact causal
enclosure D and positive temporal margin m from
[G3](full-partner-globalization.md#2-general-geometric-foundation-without-an-analytic-estimate)
give a common bound R on the h-length of **every** causal curve with endpoints
in K. Enlarge K slightly when constructing chart supports; the same argument
still gives a compact D and a finite R.

Work on one connected ambient component at a time. Only finitely many meet
K, since components are open and K is compact. Let pi be its universal
cover. The lifted Riemannian metric is complete: an h-geodesic extends in the
base and lifts for its whole parameter interval. Hopf--Rinow therefore makes
closed bounded lifted neighborhoods compact. No Lorentzian completeness is
being assumed.

The cover is globally hyperbolic. Strong causality lifts by taking an evenly
covered, causally convex neighborhood inside a base strong-causality
neighborhood. For two fixed lifted endpoints, every joining causal curve
projects into a compact base enclosure and has the common lifted length
bound. Thus it stays in a compact lifted ball. For converging endpoints the
same bounds apply on slightly larger endpoint neighborhoods. Parametrization
by t composed with pi, and the causal limit-curve argument used for G3, show
that the lifted causal relation is closed. Each lifted diamond is consequently
a closed subset of a compact lifted ball. Strong causality and compact
diamonds give global hyperbolicity of the cover.

### Development is derived on each diamond, not assumed globally

Flatness and simple connectivity supply a global parallel orthonormal frame
on the cover. The dual parallel coframe is closed by torsion-freeness and
therefore exact. Integrating it constructs a local isometry
`dev : cover(Q) -> Minkowski(d)`. It need not be globally injective or onto.
Every affinely parametrized geodesic develops to an affine straight line.

For causally related lifted points a,b, global hyperbolicity supplies a
joining causal geodesic (the standard globally hyperbolic
Avez--Seifert existence theorem). Parametrize it on [0,1]. Its initial velocity
is necessarily the inverse differential of dev at a applied to
`dev(b)-dev(a)`. Uniqueness for the geodesic initial-value problem proves both:
there is only one such geodesic, and dev is injective on the **whole causal
future of a**. Indeed two future points with the same developed value would
have identical joining geodesics and identical endpoints. This is not a claim
about two unrelated points in the cover.

Let C be the compact lifted diamond [a,b] and C-flat the Minkowski diamond
between their developed tips. C maps injectively into C-flat. If a is
chronologically before b, the image of its chronological diamond is nonempty
and open in the interior of C-flat, by the local diffeomorphism property.
It is also relatively closed there: dev(C) is compact; and a point of dev(C)
strictly timelike from both developed tips has preimage strictly timelike
from both actual tips, by the causal geodesics just constructed. The interior
of C-flat is connected. The image therefore contains its entire interior,
and compactness adds its boundary. In the null case the unique null geodesic
already covers the whole flat segment. Thus

```math
\begin{aligned}
\mathrm{dev}|_{[a,b]} &: [a,b]\longrightarrow
 [\mathrm{dev}(a),\mathrm{dev}(b)]_\eta
 \quad\text{is a homeomorphism and an interior isometry},\\
\mu_{\widetilde g}([a,b])&=c_d\,
 \eta(\mathrm{dev}(b)-\mathrm{dev}(a),
      \mathrm{dev}(b)-\mathrm{dev}(a))^{d/2}.
\end{aligned}
\tag{FL2}
```

The null value is zero. Compactness of the **actual** lifted diamond is what
fills the developed diamond; local flatness alone would not suffice. This
argument covers Lorentz holonomy and developing-incomplete ambients without
assuming an injective developing map or properness of its holonomy image.

## 3. Finite lift lists and finite local cone formulas

Choose finitely many relatively compact evenly covered endpoint charts near
K, and one compact lifted support A_i above each. For endpoints in supports
i,j, every causal curve starting in A_i ends in the compact lifted
R-neighborhood of A_i. Properness of the deck action implies finiteness of

```math
\begin{aligned}
F_{ij}&=\{\gamma:\gamma A_j\cap
                 \overline B_{\widetilde h}(A_i,R)\ne\varnothing\},\\
D_\gamma(x,y)&=[\widetilde x,\gamma\widetilde y]_{\widetilde g},\\
J^+(x)\cap J^-(y)&=
 \bigcup_{\substack{\gamma\in F_{ij}\\
              \widetilde x\preceq\gamma\widetilde y}}
                  \pi D_\gamma(x,y).
\end{aligned}
\tag{FL3}
```

To prove the last equality, lift a causal curve from x to y through the
chosen intermediate point. Its target is one of these lifts. Conversely a
point of a lifted diamond projects between the endpoints. Ambient containment
places this entire union in M for x,y in M. Removed endpoints have zero
volume. Finiteness is uniform on the chart supports, not a hypothesis about
the fundamental group or a bound of two lifts.

There is also a genuinely local **finite cone presentation** of the causal
relation on any compact endpoint set. At a causally related lifted pair the
joining geodesic has no conjugate point: in a parallel frame its Jacobi fields
are affine. The endpoint map `(a,v) -> (a,exp_a(v))` is therefore a local
diffeomorphism there, including at a=b. Nearby endpoints have the continuing
geodesic; causality of that branch is precisely future causality of its
initial vector. Any causal geodesic for those same lifted endpoints must
have that vector, by the development/uniqueness argument above.

At a fixed base pair, discard only lift labels which are **not** causally
related there: closedness of the lifted relation and the finite list give
an open neighborhood where they remain absent. Continue every related label
as just described. At a noncausal base pair take an open noncausal
neighborhood. Compactness supplies a finite cover of endpoint-pair space by
these neighborhoods. In local flat coordinates each continuing branch has
an affine developed displacement, so its future-cone condition is the
ordinary quadratic Lorentz inequality together with the linear future-time
inequality. At the diagonal these are used as inequalities, not as a smooth
squared-phase coordinate. This is a finite family of formulas, not a claim
that all their intersections with arbitrary smooth faces have finitely many
connected contact strata.

### Exact physical volume, including self-overlap

Choose a smooth partition on this finite pair cover. Refine intermediate
charts when necessary so that each overlap uses one flat coordinate system.
For `(x,z)` and `(z,y)` the local relation is a finite Boolean union of the
just-derived cone conditions. Multiplying the two partitions yields finitely
many smooth weights W_a, and finite Boolean cone formulas B_a, with

```math
\begin{aligned}
\mathbf1_{\{x\preceq z\preceq y\}}
 &=\sum_a W_a(x,z,y)\,\mathbf1_{B_a(x,z,y)},\\
V_M(x,y)&=\sum_a\int_M W_a(x,z,y)
                 \mathbf1_{B_a(x,z,y)}\,d\mu_g(z),\\
V_M(x,y)&=\mu_g\!\left(\bigcup_\gamma\pi D_\gamma(x,y)\right).
\end{aligned}
\tag{FL4}
```

Partitions sum to one on the compact sets in question and have compact
support in the slightly larger charts. These equalities are exact, including
on seams and null relations; endpoint removal is volume-null. In endpoint
integrals keep both physical endpoint measures and their original domains.
A finite signed refinement changes no identity.

In each physical intermediate chart a union indicator may equivalently be
expanded by full finite inclusion--exclusion, including intersections of
**every** order. Different pieces of the same projected diamond can overlap;
there is no global projection-injectivity assertion in (FL4). The Boolean
union counts a physical point once even in that case. Holonomy-equivalent
coordinate formulas are not permission to identify distinct deck labels
before their actual branch domains have been established.

This yields the promised finite chart/physical-union reduction. Its action
kernel is still K_d evaluated at the **entire sum in (FL4)**. It is never a
sum of kernels of chart pieces or intersection volumes.

## 4. Small-volume geometry: what actually becomes uniform

Fix a positive cutoff. Consider the compact set Z of limits of causal long
pairs in M whose actual interval volumes tend to zero. Such limiting pairs
are nonzero null-related physical pairs. A chronological limiting pair would
contain a fixed open subinterval between its tips; openness of chronology
would place that positive-volume subinterval in every sufficiently late
approximating interval, a contradiction. Closedness of causality and the
positive temporal gap give the other assertions.

The limiting causal curves lie in K by containment and compact curve control.
A source on the future face immediately leaves K along a nonzero future
causal direction, since the face conormal is timelike; a target on the past
face gives the reverse contradiction. Both joints are excluded as long
endpoints for the same reason. Compactness supplies clearance. The retained
strata are source interior/past face and target interior/future face. Joints
are **not** removed from the physical short action.

At a point of Z, each causal lift is a null geodesic. Its physical projection
is embedded, since a self-intersection would be a closed causal curve. Two
different such geodesics have distinct initial null rays and distinct terminal
null rays: equal rays would give the same geodesic by initial-value uniqueness,
and temporal monotonicity prevents a second visit to the target. They cannot
meet internally. If the tangents at a meeting differ, splicing their halves
and the push-up property makes the endpoints chronological. If they agree,
geodesic uniqueness makes the two routes identical.

Consequently, on a finite neighborhood cover of Z:

- every candidate branch continues smoothly, with squared phase s_i and
  actual causality exactly s_i>=0 (its future direction stays strict);
- distinct null rays have uniform positive angular separation;
- distinct branch arcs stay separated away from fixed endpoint neighborhoods;
- each sufficiently thin individual diamond projects injectively.

For the last assertion, an embedded compact null arc has a contractible
open tubular neighborhood. Choose its lifted component, on which pi is
injective. Nearby small-phase diamonds stay in that component: otherwise
compact lifted causal control would supply a limiting point outside the
tube on the original null segment. This proves the assertion without any
assumption of injectivity for larger diamonds. The same compact argument
puts all pairwise projected overlaps near the two endpoints. All conclusions
hold uniformly after shrinking finitely many patches.

Write, on these patches and then intrinsically by counting all causal lifts,

```math
\begin{aligned}
S(x,y)&=c_d\sum_i(s_i(x,y)_+)^q,\\
V_M(x,y)&\le S(x,y),\\
\max_i c_d(s_i{}_+)^q&\le V_M(x,y),\\
0\le S-V_M&\le\sum_{i\lt j}
       \mu_g(\pi D_i\cap\pi D_j).
\end{aligned}
\tag{FL5}
```

The lower bound uses the now-proved small-phase projection injectivity.
The last inequality is the elementary pointwise bound `r-1 <= r(r-1)/2`
for a point lying in r sets. It is an **upper bound**, not pairwise-only
inclusion--exclusion. It therefore handles arbitrary higher intersections.
Globally S>=V_M still holds by subadditivity and the measure-nonincreasing
projection of each diamond. The finite lists and compact developed tips bound
S. The action continues to use V_M; S is an auxiliary comparison.

## 5. Actual overlaps are above critical primitive order

### A uniform overlap estimate, including both tips and the axes

Near the common source, use a physical inertial chart and write an intermediate
point as z=(a,b), with a>=|b|. The developed displacement to target lift i is
k_i=(T_i,R_i n_i), where |n_i|=1 and R_i is uniformly bounded below on a
long null patch. If z lies in its diamond, then

```math
\begin{aligned}
2\eta(k_i,z)&\le s_i+\eta(z,z),\\
\eta(k_i,z)&\ge R_i(a-n_i\cdot b),\\
\eta(z,z)&\le2a(a-n_i\cdot b),\\
a-n_i\cdot b&\le C s_i.
\end{aligned}
\tag{FL6}
```

The final inequality follows by taking the source neighborhood with
`a < R_i/2`. All constants can be made uniform on the finite patches.
For two distinct directions, a bounded Lorentz change of coordinates turns
these two null linear forms into positive multiples of u and v. Their
angular separation supplies uniform bounds for the change. The source cone
becomes `u,v>=0`, `|b_perp|^2<=uv`. With p=d-2 and v_p the volume of the
Euclidean unit p-ball, the overlap there is bounded by

```math
\begin{aligned}
\frac{v_p}{2}\int_0^{Cs_i}\int_0^{Cs_j}
                 (uv)^{q-1}\,dv\,du
 &\le C'(s_i s_j)^q,\\
\mu_g(\pi D_i\cap\pi D_j)&\le C(s_i s_j)^q,\\
0\le S-V_M&\le C\sum_{i\lt j}(s_i{}_+s_j{}_+)^q.
\end{aligned}
\tag{FL7}
```

Repeat the argument backward at the target; **both** overlaps are included.
There is no overlap elsewhere after the preceding localization. For d=2
the transverse ball has counting volume one. An axis gives zero volume, so
the bound includes it. No equality of source and target overlap coefficients
or generic multiple intersection is asserted.

### Primitive comparison with a thin-shell proof

Let N_S be (FL1) with threshold S<=c_d w^q, the same order, cutoff, weights
and endpoint domains. For unit nonnegative weights N_V>=N_S. For arbitrary
bounded weights the absolute difference is bounded by their supremum times
the shell measure. In that shell (FL5)--(FL7) imply

```math
\begin{aligned}
0\le s_i{}_+&\le w,\\
c_dw^q\lt S&\le c_dw^q+Cw^{2q}.
\end{aligned}
\tag{FL8}
```

A nonempty shell has at least two active branches i,j. Their phase
differentials are independent: their source covectors are distinct nonzero
null covectors and cannot be proportional. This pairwise rank is derived;
independence of all phases is neither used nor generally true.

Move the target along a fixed future timelike coordinate field E. On a
sufficiently small patch every candidate phase satisfies `E(s_i)>=c>0`.
Use r=s_i as a flow coordinate, and let a be the value of s_j where this
flow meets r=0. Pairwise rank makes a a valid additional transverse
coordinate. All remaining coordinates range in fixed compact boxes with
bounded Jacobian. In (FL8), `0<=r<=w` and `|a|<=Cw`. Along the flow all phases
increase. On `S>=c_d w^q`, one active phase is at least a fixed multiple of w;
therefore `dS/dr>=c' w^(q-1)` almost everywhere. This also holds for q=1,
using the piecewise-linear positive part. Monotonicity and (FL8) bound the
r-length of the shell by C w^(q+1). Multiplying by the a-width, integrating
the compact passive coordinates, and summing the finite branch pairs proves

```math
\begin{aligned}
|N_V^\delta(w)-N_S^\delta(w)|&\le Cw^{q+2},\\
\frac{N_V^\delta(w)-N_S^\delta(w)}{w^{q+1}}&\longrightarrow0.
\end{aligned}
\tag{FL9}
```

Endpoint faces and cutoff indicators only restrict the shell and hence can
be retained without a transversality hypothesis for this bound. In particular
simultaneous face contacts do not invalidate it. A finite chart decomposition
of the compact flow boxes makes the argument local if a flow exits a patch;
the number of boxes and their Jacobian bounds are fixed.

Both primitives are finite signed measures' cumulatives, have no zero atom,
and are continued constantly beyond bounded support, exactly as in G5.
Their difference divided by w^(q+1) is globally bounded and tends to zero.
The exact G5 rescaling, with no polynomial subtraction necessary for this
difference, gives an integrable majorant proportional to
`z^(2q) |K_d'(z^q)|`. Thus their normalized long responses differ by o(1).
This proves the **actual** physical-overlap remainder, not a new definition
of interval volume. It supplies no complete-action convergence rate.

As a separate check, the mean-value bound for the polynomial-exponential
kernel and (FL7) give a sum of integrals bounded by
`C rho (s_i s_j)^q exp(-c rho(s_i^q+s_j^q))`.
The same two-phase coordinates integrate these to
`O(rho^(-1-2/q))` before the physical pair normalization. Multiplication by
`rho^(1+1/q)` again gives a vanishing comparison. Fixed positive-volume
complements for V_M and S are exponentially small; they are not deleted
from the exact finite-density decomposition.

## 6. The residual is a signed sum-volume problem, not an overlap assumption

The preceding argument settles the developing-map gate and the physical
union correction in all dimensions. It does **not** make K_d(rho S) a sum
of single-branch kernels. In a two-candidate patch, after a smooth compact
pair localization, put u=s_1, v=s_2. If F is the actual joint pushforward
including the physical face indicators and both endpoint measures, the
exact primitive correction to the lift-counted reference is

```math
\begin{aligned}
C_q(w)&=\int_{u,v\ge0}\mathbf1_{\{u^q+v^q\le w^q\}}
                                      F(u,v)\,du\,dv,\\
H_1(w)&=\int_0^w\int_0^\infty F(u,v)\,dv\,du,\\
H_2(w)&=\int_0^\infty\int_0^w F(u,v)\,dv\,du,\\
N_S(w)&=N_{\mathrm{ref}}(w)+C_q(w)-H_1(w)-H_2(w).
\end{aligned}
\tag{FL10}
```

The two strips include parts where the other branch has positive volume
bounded away from zero. Discarding them is not a small-volume approximation.
They are exactly the missing reference partners. For more candidates, use
the full Boolean sign decomposition, not independently added pair corrections.

At a physical null pair each single phase is transverse to the retained
physical endpoint strata: a nonzero null covector is not a timelike face
conormal. Thus the single-branch reference, with a smooth compact pair weight,
has the ordinary smooth pushed density. At the temporal cutoff choose delta
sufficiently small using G3 locality. The additional cutoff coordinate is
also regular: after division of d(s_i) by the small endpoint separation,
its limiting endpoint covectors are (-k,k), whereas d(ell) tends to (-dt,dt).
Here k is null and dt timelike. With both active faces the endpoints approach
J; dependence would force the same covector to be proportional to its two
independent face conormals, then force both coefficients to vanish. Compactness
gives a uniform small-cutoff bound. With at most one face, the free endpoint
already proves rank. This is the temporal version of #157's derived cutoff
argument, not an identification of temporal and radial-null masks.

Moreover all multiple-route null pairs stay a positive temporal distance
from the diagonal. Otherwise G3 would place their entire intervals in one
causally convex flat normal chart, where the geodesic is unique. Choose delta
below this separation too. Multiple-route patches are then entirely long;
no artificial cutoff contact is omitted from (FL10).

## 7. A cubic primitive and the complete flat theorem through dimension four

### The ranks that follow from null geometry

Any three distinct future null rays have linearly independent representatives.
Indeed the span of two distinct future null vectors is a Lorentzian
2-plane, whose null cone consists of exactly their two rays. A third null
ray cannot lie in that plane. In dimension two there are only two rays;
geodesic uniqueness and temporal monotonicity then bound the number of null
routes by two. In higher dimensions this argument supplies **triple rank**,
not a bound of three routes.

In each localized null patch write the continuing branch phases as s_i and
the retained face conditions as a(x)>=0, b(y)>=0, when present. Any three
phase differentials are independent by their source components. Each of
(s_i,s_j,a) and (s_i,s_j,b) has rank three by its free endpoint's two distinct
null covectors. Each (s_i,a,b) has rank three because a nonzero null covector
cannot be a timelike face conormal at either endpoint. These ranks persist
on a small compact patch. In dimension two the impossible three-phase case
is simply absent. No independence of four constraints is asserted.

### A first transport derivative without simultaneous transversality

We need a modest shape lemma, not an assumption of a smooth pushforward.
Let a compact integral depend smoothly on parameters and have finitely many
conditions g_j>=0. Suppose each g_j, **individually**, has nonzero differential
in the integration variables on its zero set near the compact support. Then
the integral is locally Lipschitz in its parameters and has a finite
one-sided first derivative along each fixed parameter direction. The
derivative need not be linear in that direction.

Here is a proof that includes coincident and arbitrarily high-order contacts.
The symmetric difference of the domains is contained in the finite union
of bands `|g_j(0,z)|<=C|h|`, whose measures are O(|h|) by the individual
coarea bounds. This also bounds the difference quotient. Telescope the
product of the indicators in a fixed order. In the term where indicator j
changes, use g_j(0,z) as the normal coordinate and rescale it to h times r.
The changed indicator confines r to a fixed bounded interval. Restrict every
other g_k(0,z) to the j-boundary. Its nonzero values give a constant limiting
sign. The part of its zero set where its tangential gradient is nonzero has
boundary measure zero. Almost everywhere on the remaining zero set the
tangential gradient is zero; individual regularity of g_k makes its normal
derivative nonzero. Its rescaled inequality is therefore a nonconstant
linear inequality in r, with the parameter-direction term included. Its
exceptional equality has r-measure zero. Compact dominated convergence now
gives the derivative of every telescoping term, including contacts of any
multiplicity. The smooth-amplitude difference has its ordinary derivative.
This proves the lemma and its uniform Lipschitz bound. It does not claim
ordinary differentiability, a finite contact stratification or a second
derivative without further information.

### Exact sign sectors and the third-order jet

Decompose the local pair domain by the **whole set A of positive phases**;
zero sets are pair-null. Inactive phases are negative, not unconstrained.
The empty sector has no causal-pair measure. All multiple-route patches are
entirely long by section 6. In a one-route patch the cutoff and faces have
already been rectified there. This is an exact alternative to reference/strip
matching: every reference strip in (FL10) is retained by the inactive/active
sign conditions, not dropped.

**One positive phase.** Use u=s_i as a coordinate. The other phases and
physical faces are finitely many inequalities on the u-fibre. Every one is
regular there, and every pair has independent differentials there, by the
triple ranks just proved. Write B(u) for their actual weighted fibre integral.
The transport formula for B' has a bulk term and one coarea flux per boundary.
Each flux is continuous: on that boundary every other constraint is regular,
so its zero set has boundary measure zero. Thus B is C1. On each flux
boundary the remaining constraints are individually regular, even when
several meet nontransversely. Apply the preceding first-derivative lemma to
that flux and to the bulk term. B' has a finite right derivative at zero.
Integrating twice gives

```math
\begin{aligned}
B(u)&=B(0)+B'(0)u+\tfrac12B''(0+)u^2+o(u^2),\\
N_{\{i\}}(w)&=B(0)w+\tfrac12B'(0)w^2
                       +\tfrac16B''(0+)w^3+o(w^3).
\end{aligned}
\tag{FL11}
```

For rigor the transport formula can first be obtained with smoothed step
functions. The individual coarea bounds control first derivatives; pairwise
coarea on the fibre controls the double-boundary terms after one integration
by parts. These give local bounded second weak derivatives for B, justify
passage to the continuous first-derivative formula, and supply its compact
bounds. Applying the shape lemma to each term then supplies the stated
right derivative, not merely a weak derivative at an unspecified point.

**Two positive phases.** Use u=s_i, v=s_j. Every remaining constraint is
individually regular on their joint fibre by triple rank. Its actual
pushforward F is locally Lipschitz and has a one-sided directional derivative
D(r,s) at zero by the shape lemma. On the fixed positive q-ball,
`F(wr,ws)=F(0,0)+w D(r,s)+o(w)` pointwise; the difference quotients are bounded
by a constant times `r+s`. Dominated convergence therefore gives an actual
coefficient at each of orders two and three. D need not be linear: replacing
it by a presumed smooth Taylor differential would miss simultaneous contacts.

**At least three positive phases.** Select any three of them as coordinates
u_1,u_2,u_3, and scale u=w r. The sublevel of S confines each r_i to [0,1].
The other coordinates range in a fixed compact box with bounded Jacobian,
so the sector is O(w^3). Its quotient by w^3 has an actual limit, as follows.
For each remaining phase or face function g, examine g(0,z) on the passive
box. Nonzero values give an eventual sign (and a positive active phase
excludes the sublevel). Almost everywhere on its zero set the passive
gradient is zero; since the full differential of g is nonzero, its differential
in the three scaled coordinates is a nonzero linear form. Taylor expansion
then gives the limiting sign almost everywhere in r. The limiting sublevel
is a sum of positive parts of these linear forms to power q, together with
`r_1^q+r_2^q+r_3^q`, bounded by one. Its boundary has r-measure zero: it is
positive and homogeneous along every nonzero positive radial ray. The
remaining sign boundaries are nonzero linear hyperplanes. Dominated
convergence proves the coefficient at order three even for dependent fourth
and higher phases. No independence of those phases or smoothness of their
joint image was used.

These arguments apply on finitely many compact coordinate patches, with
all partitions and both endpoint measures in the amplitudes. Adding all
sign sectors, including the positive-volume complement, proves in **every**
dimension d>=2 the following actual partial jet:

```math
\begin{aligned}
N_S^\delta(w)&=b_1w+b_2w^2+b_3w^3+o(w^3),\\
N_V^\delta(w)&=N_S^\delta(w)+O(w^{q+2}).
\end{aligned}
\tag{FL12}
```

The complement is zero in these primitives for sufficiently small w, since
its actual volume has a fixed positive lower bound; its finite-density
kernel contribution remains in the exact decomposition and is exponentially
small. In d=2 the last bound does not identify the cubic coefficient of
N_V, nor is that coefficient needed. For d>=3 it is o(w^3).

### Complete theorem for d=2,3,4

**Theorem.** For every smooth flat G-SS region in any ambient Q of section 1
and each d in {2,3,4}, the canonical deterministic action tends to the
independent joint target. Its independently constructed Poisson expectation
has the same limit. No topology, holonomy, width, multiplicity or global
presentation restriction is added.

For d=2 and d=3 subtract the degree-two primitive polynomial from (FL12):
the remainder is respectively O(w^3) and O(w^3), hence o(w^(q+1)). For d=4
subtract all three terms: the remainder is o(w^3)=o(w^(q+1)). The subtracted
polynomial derivatives have precisely the existing zero moments in each
case. The residual divided by w^(q+1) is globally bounded and tends to zero;
constant continuation beyond the bounded primitive support is understood.
G6's integrable majorant therefore proves that the complete long response
tends to zero. This excludes a critical logarithm in 4D and a critical
fractional response in 3D by an actual remainder estimate, not by discarding
such possibilities in advance.

Choose the **same** sufficiently small positive temporal delta here and in
S30. Its unit-field short action tends to the independently defined joint
target, since scalar curvature is zero. G1 and G4 are exact at finite density;
the physical point appears once and the complete ordered partition sum
restores all partners and cancels artificial fluxes. Hence

```math
\begin{aligned}
\mathcal A_{\rho,d}(M,g)
 &=S^\delta_{1,1}(\rho)+L^\delta_{1,1}(\rho)
 \longrightarrow\int_J\coth\theta\,dA_g,
 \qquad d\in\{2,3,4\}.
\end{aligned}
\tag{FL13}
```

In dimension two this integral counts **every** joint point. All joint
components and inner boundaries remain. Different connected components of
M cannot be causally related: a connecting causal curve would lie in M by
containment. This proves their additivity without modifying the selected
order. Source/target partition derivatives, nonzero face fluxes and positive
height critical points remain covered by S30; they are not assigned zero
individually.

### Finite derivative budget, not a new regularity contract

C4 face/field data suffice for the new long argument: one derivative for a
rectifying Jacobian and at most two further transport derivatives, with a
spare continuous derivative for the compact bounds. The triple-scaled limit
uses only first derivatives. For the consumed **flat short proof in d=2,3,4**,
a deliberately nonoptimal budget of eight derivatives suffices. In local
inertial charts H=1 and the normal volume Jacobian is one, so there is no
geodesic-ODE or even-variable derivative loss. A divided face gap costs one
derivative; its implicit depth root remains C7; its differentiated depth
Jacobian and height-chart factors are at least C6. The mixed derivatives of
Psi required in S10 have total order at most N+4, which is at most six in
these dimensions. Temporal-shell rectification and the fixed finite
partitions fit the same budget. Thus the proofs use finitely many compact
C8 bounds. This is a sufficient count for the stated smooth theorems, not
optimality, an all-dimensional C3 assertion or a new finite-regularity class.

## 8. Higher dimensions: investigated extensions and exact blocker

For d>=5 the remaining object is the actual primitive of the finite sum S
in (FL5), with its geometric endpoint domains, not the individual diamond
volumes and not an arbitrary hypothesized density. The cubic jet (FL12)
is insufficient at those dimensions' critical order. To complete #149 one
must derive its critical signed response, for example by proving

```math
\begin{aligned}
N_S^\delta(w)&=\sum_{j=1}^{n+1}b_jw^j+R_S(w),\\
R_S(w)&=o(w^{q+1})
\end{aligned}
\tag{FL14}
```

with G6 domination, **or** retaining and evaluating every surviving critical
mode in the complete matched action. (FL14) is not an admissibility field.

The following alternatives were investigated after the exact reduction and
overlap estimate, rather than stopping at the geometric package:

1. **Simultaneous phase/face rectification.** Where the actual differentials
   of all candidate phases and active face functions are independent, sign
   decomposition gives fixed half-spaces. In a sector with r positive phases,
   scale those phases by w; the domain is a fixed positive q-ball and the
   primitive is w^r times a compact smooth integral. Taylor's theorem and
   the signed moments prove the needed local integer jet there. But the rank
   condition is not universal and its constants need not stay bounded near
   the rank-deficient set. It cannot be inserted into G-SS or used to discard
   the remaining contacts.
2. **Only pairwise phase coordinates.** Their rank and the shell estimate
   are sufficient for the physical-overlap correction. They do not regularize
   the domain of the other phase signs or simultaneous physical faces. The
   transport/triple-scaling alternative in section 7 advances this route to
   the cubic jet, but does not bound its remainder at order w^(q+1) for
   d>=5. Direct absolute control of a two-phase layer gives only O(w^2);
   the physical normalization scales as w^(-q-1). This does not vanish in
   higher dimensions. Signed matching, not a stronger absolute-kernel bound,
   is required.
3. **Algebraic resolution of the cone arrangement.** Branch phases in flat
   charts are quadratic and their finite arrangement can be analyzed
   algebraically. The boundary masks, however, come from arbitrary smooth
   spacelike faces. Flatness does not make those masks analytic or give
   finite contact order. A resolution of the cones alone is therefore not
   a proof of a power/log expansion of the full physical pushforward.

Here are explicit failures of the rank shortcut, not action counterexamples.
At a two-route null pair on a circle of circumference L, use displacement
`L/2+s` and time gap tau. At tau=L/2, s=0,

```math
\begin{aligned}
u&=\tau^2-(L/2+s)^2,\\
v&=\tau^2-(L/2-s)^2,\\
du+dv&=2L\,d\tau,\\
du+dv+2L(da+db)&=0
\end{aligned}
\tag{FL15}
```

when both physical face conormals are those of constant-time slices, with
a the source past depth and b the target future depth. The four constraints
have rank three. This occurs in admissible smooth geometry with actual
two-route pairs arbitrarily near the contact: take on the flat spatial torus

```math
\begin{aligned}
f_\pm(p)&=\pm\bigl(L/4+\varepsilon
                   \sin^2(2\pi p_1/L)\bigr),\\
0&\lt 2\pi\varepsilon/L\lt1.
\end{aligned}
\tag{FL16}
```

The graphs are globally spacelike and achronal, bound a positive-height
precompact region and have empty joint. The slope bound makes past depth
increase and future depth decrease along every future causal curve, proving
ambient containment. At p_1=0 and target coordinate L/2 their conormals are
the constant-time ones. For nearby common translations of these coordinates
the available time gap exceeds L/2, so the two-route sector is genuinely
present. Extra transverse coordinates may be included with sufficiently
large periods. This tests a failed proof lemma, not a replacement family
for the general task; its complete action is not alleged to obstruct anything.

Independence of **all branch phases** already fails without faces. At a
square-lattice corner the four target lifts give the exact identity

```math
\begin{aligned}
s_{++}+s_{--}&=s_{+-}+s_{-+}.
\end{aligned}
\tag{FL17}
```

Their differentials have rank three at the null corner. The higher-fold
arrangement must be treated on its actual image, not integrated as four
independent phase variables. These failures remain even though every pair
of branch phases has the independence used in (FL9).

**Genuine unresolved mathematical blocker:** derive a contact-uniform
critical-order signed pushforward estimate for S, in d>=5, across the
rank-dependent multi-cone arrangement and arbitrary smooth simultaneous
endpoint-face contacts, restoring every reference strip and complement.
The finite-lift, overlap, transport and cubic-jet results proved here do not
provide that estimate. In particular, the dominated-convergence proof for
three-positive-phase sectors gives only o(w^3), not the needed higher-order
remainder; pairwise/triple ranks do not supply a fourth joint coordinate.
Higher transport derivatives encounter intersections whose independence is
not implied by the null-ray argument. These are precise losses in the
successful proof, not just a failed generic rank assumption. Nor has a
surviving complete-action term been
proved. A pure critical fractional mode in odd d or a critical logarithmic
mode in even d must be tested with G7, not ruled out by smooth geometry or
called an obstruction in isolation. There is no justified corrected target
to substitute at this stage.

## 9. Actual expectation hypotheses and coverage ledger

Independently of any asymptotics, the original geometry discharges the
measured-order bridge in **every** dimension here:

- Q and its open subset M are standard Borel. Global hyperbolicity gives a
  closed causal partial order; its restriction and the joint exclusive
  interval indicator on triples are Borel.
- Lorentzian chart volume is finite on the compact closure and atomless.
  Containment equates the restricted interval with the whole physical union
  (FL3)--(FL4), not with S or with a selected branch.
- The null relation has zero pair measure by the achronal-boundary flow-box
  argument and Tonelli. Timelike pairs have positive interval volume. This
  also justifies the zero-atom assertions for both N_V and N_S.
- The law is the existing finite Poisson law of intensity rho times restricted
  geometric volume. Distinct ordered endpoint layers use that actual
  exclusive interval. Each layer is bounded by squared total cardinality;
  its finite Poisson second moment controls every finite signed combination.

Thus the already-proved generic
`dimensionFiniteMeasureAction_expectation` applies, exactly as in the written
manifold discharge in G3's note, and gives

```math
\begin{aligned}
\mathbb E_{\mathrm{Poisson}(\rho\mu_g|_M)}
       A^{\mathrm{disc}}_{\rho,d}
 &=\mathcal A_{\rho,d}(M,g),\\
\lim_{\rho\to\infty}\mathbb E A^{\mathrm{disc}}_{\rho,d}
 &=\int_J\coth\theta\,dA_g,\qquad d\in\{2,3,4\}.
\end{aligned}
\tag{FL18}
```

The first line is a separately discharged finite-density identity for all
flat G-SS geometries and all d>=2. Only the second line uses the new
complete deterministic theorem. It is not extrapolated from the concrete
4D quotient instance, and is not a compiled Lorentzian-manifold instance.

| Original obligation | Proved coverage | Explicitly unresolved |
| --- | --- | --- |
| Every flat ambient topology/holonomy, d>=2 | Finite lift lists; faithful individual developed diamonds; exact physical union/cone chart formulas | No missing global-development assumption is left in the reduction |
| Wider cuts, arbitrary multiplicity, large-diamond self-overlap | Exact finite-density accounting; actual union correction (FL9); sum-volume cubic jet (FL12) | Critical signed sum-volume/contact producer in d>=5 |
| Arbitrary admissible faces, components, joints and both endpoint measures | Exact domains; long clearance; transport through simultaneous contacts; S30 short and independent target; complete ordered partition identities | Higher-order simultaneous face/multi-phase response in d>=5 |
| All flat G-SS in d=2,3,4 | Full deterministic and separate expected limits; all 2D joint endpoints; sufficient finite derivative budget | Independent human review and any justified formal port |
| Minkowski G-SS in every d>=2 | Reuse #157's complete theorem and finite regularity count unchanged | No new gap imposed on that theorem |
| Thin and first-cut cubic slabs in every d>=2 | Reuse the existing thin theorem and #162 unchanged | Those width bands are not generalized by changing their routines |
| Noncubic quotients, Euclidean/Lorentz holonomy, non-ultrastatic and developing-incomplete flat geometries | The all-dimensional reduction, overlap bound and cubic jet; complete theorem in d=2,3,4 | Full d>=5 signed response and consequent limit/finite-regularity budget |
| Odd/even critical fractional/log modes | Existing dimensional moments and G7 apply to the actual residual | No universal list of residual modes or cancellation has been derived |
| Probability law and physical normalization | Actual geometric hypotheses discharged and finite-density identity in every d | Higher-dimensional expectation limits await their deterministic producers |
| Original #149/#81/#24 acceptance | Scope and existing results preserved | #149 remains open; this is not completed general flat coverage |

The next mathematical input is the quantified estimate identified in section
8, not another example band or another expectation API. #81 retains that
residual under #149; #151's curved classification is not re-proved here.
#86 retains independent mathematical review and any justified formalization.
No Lean/checker/dependency/build input changes, new compiled theorem,
sample-wise statement, shrinking-cutoff interchange or complete-action rate
is claimed.

The focused tests are finite algebraic/numerical diagnostics of cone phases,
physical unions, self-overlap, higher intersections, strip restoration and
signed responses. They do not verify the universal geometric proofs or the
unresolved producer. Validation receipts belong to the PR, not to a change
of the mathematical acceptance contract.

Refs #149, #81, #24, #86, #150, #151.
