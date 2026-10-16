# A past-front theorem, not an induction on the number of tips (#156)

**Conventional written result; no new Lean theorem or independent acceptance.**
The theorem below generalizes the mechanism of [CT3–CT12](conformal-two-tip-limit.md)
to a fixed past set. It includes arbitrary finite tip multiplicity under the
explicit geometric contact condition below, including dependent cone normals.
Section 7 derives the genuine all-dimensional version, not a copied 4D kernel.
It is not the whole original #156 contract. [The current crosswalk](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt)
retains tangencies, NN contacts, other metrics/dimensions and their interactions.

Source/base pin: `3ae22f792325634607be5fd518303ff25a404dda`, fetched explicitly
into `origin/issue-81-general-coverage` and checked against `ls-remote` on
2026-10-16. CC and CT are consumed as written arguments, not because #169/#178
are closed. Their sources and receipts are unchanged.

## 1. Geometric hypotheses and independent target

Work in conformally Minkowski four-dimensional spacetime, with the original
closed ambient order, signature and curvature convention of [#90](general-contract.md).
Let H be any smooth globally lambda-Lipschitz function on R3, lambda<1, and P
an open past set. Assume M=F intersect P is nonempty and bounded, where
F={t+H(x)>0}. Let Omega be any fixed smooth positive factor on a neighborhood
of its compact causal enclosure, A=Omega^4. Empty intersections used in §5
have action and target zero.

The following is a **geometric regular-contact hypothesis**, not a jet or
limit premise. Near the compact set where the floor meets the actual upper
front, require a finite smooth atlas with coordinates (y,z) such that:

- membership in P depends only on y and is given by a fixed finite union of
  polyhedral sectors (linear inequalities in y);
- each exposed hypersurface is null, smooth up to its incident strata;
- dF is nonzero on the z directions, tangent to all the incident sector
  hyperplanes. Here F also denotes the defining function t+H(x).

Only the contact atlas is required. No smoothness, fixed multiplicity,
absence of tips, or no-cut/no-caustics hypothesis is imposed on the upper
front **away from the floor**. An open Minkowski past set is locally the
subgraph of a 1-Lipschitz function at each finite frontier point: the past-set
property compares its heights at spatial points by their Euclidean distance.
It consequently has locally finite perimeter, including at its nonsmooth
points. The extra atlas above is needed only where the floor derivatives live.
Smooth regular SN contacts and ordinary transverse null-face corners satisfy
it. It is explicit additional geometry for this theorem, not a restriction
on the parent issue.

Define J as the regular exposed SN pieces. The atlas makes their lower
interfaces have zero two-dimensional area; all components are included. If
an exposed sheet is t=G(x), then |grad G|=1, the contact is H+G=0, and
|grad(H+G)|>=1-lambda on that piece. Its positive induced area is independent
of the action. With ordinary Euclidean surface measure dS_x on this spatial
contact, set

```math
\begin{aligned}
\mathcal T(M)&=3\int_M\Omega\Box_\eta\Omega\,dq+\int_JdA_g,\\
dA_g&=\Omega^2\frac{1+\nabla G\cdot\nabla H}
 {|\nabla(G+H)|}\,dS_x.
\end{aligned}\tag{NF1}
```

To verify the second formula, restrict I-grad(G) tensor grad(G) to the
spatial tangent plane of H+G=0. Its determinant is the squared projection
of grad G onto the unit normal of that plane. That projection is
(1+grad G dot grad H)/|grad(G+H)|, positive by lambda<1. Conformal scaling
multiplies two-dimensional area by Omega^2. The bulk identity follows from
R_g=6 Omega^(-3) Box Omega; neither quantity is extracted from an action fit.

**Theorem NF.** Every fixed member just specified has complete canonical
deterministic limit T(M). Separately, the expectation under the original
Poisson law has that same limit. All physical intervals, both endpoint
measures, ordered endpoint partitions, and one fixed positive temporal split
are retained. No extra *net* same-side-stratum term occurs in this class;
that assertion will follow from the calculation, not enter the target.

## 2. Exact domain and multiplicity-independent long producer

F is a future set: a future causal displacement increases its defining
function by at least (1-lambda) times the time displacement. P is a past set.
Every closed ambient interval between endpoints of M therefore stays in M.
Straight causal segments identify the intrinsic order as well. In particular
the interval in the kernel is the entire physical weighted diamond, not a
sum over tips or routes.

Use the unchanged K, c and C4 of CT3. Write u=(1,sqrt(1-xi)n), p=q-ell*u,
and h for CC4's actual normalized integral of A on the boosted rest diamond.
The two set implications give, exactly,

```math
\begin{aligned}
P_{\chi,\phi}(\rho)&=\frac12\int_P\int_{S^2}\int_0^\infty\int_0^1
 \ell^3\sqrt{1-\xi}\,A(q)\phi(q)A(p)\chi(p)\mathbf1_F(p)
 K(c\rho\ell^4\xi^2h)\,d\xi\,d\ell\,dn\,dq,\\
\mathcal B_{\chi,\phi}(\rho)&=C_4\sqrt\rho
 \left[\int_M\chi\phi\,d\mu_g-\rho P_{\chi,\phi}(\rho)\right].
\end{aligned}\tag{NF2}
```

The endpoint fields are arbitrary fixed smooth functions near the closure.
Compact smooth auxiliary cutoffs can be one on a neighborhood of the entire
physical pair support. They remove no pairs. The density bounds and reflection
in the rest diamond's transverse coordinates prove h is positive, smooth in
xi near zero, with every needed bounded mixed derivative, uniformly down to
ell=0 and both interval tips. Near xi=1 only ell derivatives are used. These
are CC4's actual map facts, independent of P.

Choose once a smooth psi(ell), one below delta/2 and zero above delta, with
delta small enough for §3. Short has psi and the entire point; long has 1-psi.
In long introduce the actual floor and phase coordinates

```math
\begin{aligned}
r&=q_t-\ell+H(q_x-\ell\sqrt{1-\xi}\,n),&
w&=\ell^2\xi\sqrt h,\\
\left.\det\frac{\partial(r,w)}{\partial(\ell,\xi)}\right|_{\xi=0}
 &=-(1+\nabla H(q_x-\ell n)\cdot n)\ell^2\sqrt{h(q,\ell,0,n)},\\
|\det|&\ge(1-\lambda)(\delta/2)^2\sqrt{\inf A}.
\end{aligned}\tag{NF3}
```

The proof of a uniform inverse is exactly the monotone-floor argument:
at w=0 the floor is strictly decreasing in ell; compact inverse neighborhoods
and separation from their complement give a single collar and bounded inverse
derivatives. Long weights extend smoothly by zero near ell=0. After inversion,
q stays in the fixed P and r in the fixed half-line r>0. No boundary of P is
differentiated, and no rank on a generator of its front is needed. Integrating
the transformed smooth density on this fixed finite-measure domain gives
D(w)=D0+D1*w+D2*w^2+O(w^3). The actual three moments of K(c*rho*w^2) vanish.
The remainder contributes O(rho^(-1/2)) after pair normalization rho^(3/2).
The retained fixed-positive-phase complement and polynomial tails decay
exponentially. Thus the complete normalized long response vanishes.

This part works for **any** bounded future-set/past-set intersection with
this strict smooth floor. It does not use the contact atlas, null smoothness,
a tip count, or transverse translated floor/crease contacts. In particular,
there is no list of exceptional three-, four- or five-tip long calculations.

## 3. Short transport and the matched remainder

Here is the exact replacement for CT's use of two independent cone normals.
In a contact chart select a smooth vector field X in the z directions with
dF(X)=1. It is tangent to **every** sector hyperplane, whether or not their
normals are independent. A finite smooth partition combines these fields;
at a physical face every nonzero summand is tangent to it. Hence the combined
field remains tangent to all faces and has dF(X)=1 near the contact set.
Extend it through the interior floor, where partial_t suffices. Elsewhere
the moving floor indicator is locally constant.

For F_ell(q)=F(q-ell*u), compactness and the strict inequalities preserve
dF_ell(X)>0 for all sufficiently small signed ell, all n and all
b=sqrt(1-xi) in [0,1]. The parameter-dependent field
-(partial_ell F_ell)X/dF_ell(X), cut off outside a floor collar, transports
the moving floor while preserving P. Its flow exists on a common compact
neighborhood. It fixes every incident face and higher intersection, rather
than deleting them. This proves smooth moving-floor integrals, mixed ell/xi
derivative bounds near xi=0, and bounded ell derivatives throughout [0,1].
The singular upper front outside that collar is fixed and merely integrated
against bounded smooth densities.

Let U=A*chi*1_F, V=A*phi. Mellin inversion initially on 0<Re(s)<1/2 gives

```math
\begin{aligned}
Z_\psi(s)&=\frac{c^{-s}}2\int_0^\infty\psi(\ell)\ell^{3-4s}
 \int_0^1\xi^{-2s}F_s(\ell,\xi)\,d\xi\,d\ell,\\
F_s(\ell,\xi)&=\sqrt{1-\xi}\int_{S^2}\int_P
 V(q)U(q-\ell u)h^{-s}\,dq\,dn,\\
\widehat K(s)&=\Gamma(s)(1-2s)(1-s)(1-2s/3).
\end{aligned}\tag{NF4}
```

The transport just proved, not an assumed overlap expansion, permits Taylor
subtraction in ell through degree two, then subtraction in xi through degree
two of **both** those coefficients and the ell^3 remainder. The double
remainder is bounded by a polynomial in |s| times
ell^(6-4 Re(s))*xi^(3-2 Re(s)), integrable for Re(s)<7/4. Away from xi=0
the square root at xi=1 is integrable. The continued transform has only
simple null poles at 1/2,1,3/2 and diagonal poles at 1,5/4,3/2, with possible
double coincidences. Bounds are polynomial on vertical substrips; Gamma
decay permits shifting to any fixed 3/2<s1<7/4. The inverse remainder is
o(rho^(-3/2)). All subtracted upper tails and the cutoff transition remain.

For transparency, the residue calculation does not require any cone-specific
coefficient. The actual rest-diamond moments give
h=A-ell*DA/2+ell^2*(3D^2 A/20-xi Box A/60)+O(ell^3).
Spherical averaging yields CT7 with its integration domain replaced by P.
In particular its quadratic bracket is X+(1-xi)Y/3+xi Z. Its xi^2 coefficient
is Q2=(-X+Y-4Z)/8 at s=3/2. The first two ell coefficients have the actual
beta factor B(1-2s,3/2), zero at 5/4; the candidate single-face pole cancels.
The simple null poles are killed by the kernel, while the two double poles give

```math
\begin{aligned}
Q_0&=\int_M\chi\phi\,d\mu_g,\\
P^{\mathrm{short}}_{\chi,\phi}(\rho)
 &=\frac{Q_0}{\rho}
 +\frac{\pi^{3/2}Q_2}{12c^{3/2}\rho^{3/2}}+o(\rho^{-3/2}),\\
\lim\mathcal B_{\chi,\phi}&=2(X-Y+4Z)|_{s=3/2}.
\end{aligned}\tag{NF5}
```

The factors and signs are CT8: rightward contour shift subtracts residues,
the double denominator factor is 1/8, and C4*pi^(3/2)/(12*c^(3/2))=16.
The point is canceled **once**, with the whole Q0. No chart or tip gets its
own additional point. This completes the analytic producer and its critical
remainder, not just a local coefficient.

## 4. Whole deterministic assembly and separate original law

For phi=1, expand A=Omega^4 in that computed coefficient. The gradient-square
terms cancel algebraically, leaving

```math
\begin{aligned}
\lim\mathcal B_{\chi,1}
 &=3\int_M\chi\Omega\Box\Omega\,dq
 +\int_P\partial_\alpha\left(\Omega^2
             \partial^\alpha(\chi\mathbf1_F)\right)dq,\\
\lim\mathcal A_{\rho,4}(M)
 &=3\int_M\Omega\Box\Omega\,dq
 +\sum_{\text{exposed sheets}}\int
 \Omega^2\delta(G+H)(1+\nabla G\cdot\nabla H)\,dx
 =\mathcal T(M).
\end{aligned}\tag{NF6}
```

For the unit field, all floor distributions are supported in the contact
atlas. Transport defines their pairings even at multiple corners. Integration
by parts there is legitimate: the first distributional boundary derivative
of a Lipschitz domain is its hypersurface measure, not an independent edge
mass. Transverse floor/stratum coordinates give bounded densities on the SN
pieces; the portions within coordinate distance epsilon of their interfaces
have area O(epsilon). Coarea and NF1 identify the complete flux. This estimate
concerns the **derived coefficient**; the full Mellin remainder, not a
measure-zero claim, controls the action neighborhoods.

For nonconstant chi the first line retains boundary-generator derivatives
and their real endpoints. A further integration along a generator must keep
both endpoint terms, including tip/crease/cut endpoints; it is not needed
for the unit-field conclusion. It cannot turn an individual weighted term
into zero. Smooth partitions cancel their derivatives only after the full
ordered double sum. At finite density sum_(j,k) chi_j(p)phi_k(q)=1 and the
point diagonal sum is also one. Short plus long equals NF2 with its single
point; a sharp temporal split differs by opposite signed band integrals,
which cancel exactly. Delta is fixed throughout.

Only after NF6 apply probability. M is bounded Borel, with finite positive
atomless measure A dq. The ambient order and exclusive three-point interval
relation are Borel. Containment identifies the rate with NF2's actual interior
volume. Construct the original law by a Poisson cardinality of mean rho*mu(M)
and independent positions distributed as mu|M/mu(M). The finite second
factorial moment bounds every layer and hence the minimal-layer action.
Reduced two-point Mecke gives

```math
\begin{aligned}
\mathbb E L_k&=\rho^2\int_{M\times M}\mathbf1_{p\preceq q,\ p\ne q}
 e^{-\rho V_g(p,q)}\frac{(\rho V_g(p,q))^k}{k!}\,d\mu_g(p)d\mu_g(q),\\
\mathbb E A^{\mathrm{disc}}_{\rho,4}(M)
 &=\mathcal A_{\rho,4}(M)\longrightarrow\mathcal T(M).
\end{aligned}\tag{NF7}
```

Both intensity factors and the layer factorials give the original K.
Null sets justify integral conventions, not altered discrete order. No
sample-wise statement or limit/expectation interchange is made.

## 5. Arbitrarily many tips: geometry and actual pair accounting

Let c_1,...,c_N be **any finite set of distinct spatial centers**, with common
tip time zero, P_i=I^-(0,c_i), H(c_i)>0, and the same H and Omega. There is no
bound on N, no axial symmetry, and no central-overlap assumption. Every
intersection and union with F is bounded, since
|x-c_i|>=|x|-max_i|c_i| and H(x)<=H(0)+lambda|x|.

Here is the checkable regular-contact condition. For each active label set I of cone
sheets meeting the floor, let S_I be their common equality manifold and require
dF restricted to its tangent space to be nonzero. At a zero-dimensional S_I this means the
floor must not pass through it. This condition is explicit; tangential
contacts are not claimed impossible or excluded from #156.

Unlike an assumption of independent normals, this works at **arbitrary
multiplicity**. Relabel one active center as c_1. Away from the apices, t<0
and define

```math
\begin{aligned}
Q_i(t,x)&=t^2-|x-c_i|^2,\\
Q_i-Q_1&=2x\cdot(c_i-c_1)+|c_1|^2-|c_i|^2,\\
r&=\dim\mathrm{span}\{c_i-c_1:i\in I\},\qquad
\mathrm{rank}\,d(Q_1,Q_{i_2}-Q_1,\ldots,Q_{i_{r+1}}-Q_1)=r+1.
\end{aligned}\tag{NF8}
```

The last rank follows from the nonzero time component 2t and r independent
spatial linear forms. Every remaining active Q_i is a constant linear
combination of those coordinates, with its constant zero at the common
intersection. Thus any Boolean combination of these cone inequalities is
**exactly polyhedral** in those coordinates, not only tangent to a polyhedron.
The stated floor condition provides the remaining coordinate. H(c_i)>0
keeps every apex away from the floor; the proof elsewhere integrates the
fixed past set without differentiating its apices. Redundant faces and all
higher intersections remain. NF applies to every nonempty intersection and
the union, with their own exposed geometric SN pieces.

There is also a finite-density valuation, derived before using the nonlinear
kernel. Put M_S=F intersect intersection_(i in S) P_i and U=union_i M_i.
For p preceding q in F, membership in a past set satisfies
q in P_i implies p in P_i. Hence the set of labels containing **both**
endpoints is exactly the set containing q, when both endpoints are in U.
Ordinary inclusion–exclusion on that nonempty label set gives

```math
\begin{aligned}
\mathbf1_U(p)\mathbf1_U(q)\mathbf1_{p\preceq q}
 &=\sum_{\varnothing\ne S\subseteq\{1,\ldots,N\}}
 (-1)^{|S|+1}\mathbf1_{M_S}(p)\mathbf1_{M_S}(q)\mathbf1_{p\preceq q},\\
\mathcal A_\rho(U)
 &=\sum_{\varnothing\ne S\subseteq\{1,\ldots,N\}}
             (-1)^{|S|+1}\mathcal A_\rho(M_S).
\end{aligned}\tag{NF9}
```

Outside F on either endpoint both sides vanish; inside F but q outside U
both sides vanish as well. Each nonzero pair term has the **same full physical
interval** by containment, so multiplication by K of that volume is valid.
Point indicators satisfy the same identity. For restrictions of one finite
configuration the entire ambient interval belongs to every containing M_S,
so the layer index is the same; the discrete identity follows too. There is
no assertion about adding independent configurations. No higher intersection
has been deleted: all 2^N-1 nonempty label subsets occur.

Bulk and exposed-sheet area satisfy the corresponding geometric valuation.
At a regular sheet point with only label i changing, the inclusion–exclusion
sum of its incidences is one exactly when that sheet is exposed in U and zero
otherwise. Multiple incidences at SN interfaces have zero area by the proved
contact rank, not zero normalized action by fiat. Thus the independently
computed targets in NF9 sum to T(U). Both NF's direct proof and this exact
valuation give complete deterministic assembly, then NF7 gives expectation.

Different tip times need no new proof when their actual contact atlas meets
§1. NF8 is the automatic simultaneous-time construction, not a claim that
an arbitrary finite set can be made simultaneous by one Lorentz boost.

## 6. Audit of the two-tip-specific steps

| CT use of “two” | Replacement / exact boundary |
| --- | --- |
| Two past sets in CT3 | Any fixed past set in NF2; same endpoint implications |
| Lens floor/phase inverse CT4–CT5 | NF3; determinant contains no tip count or crease rank |
| Two independent cone normals near the floor | Polyhedral-contact coordinates and tangential floor field; NF8 allows arbitrarily many dependent cone normals |
| Lens has no apex; union has two | No upper-front differentiation away from the floor; all fixed apex neighborhoods stay in NF2/NF4 |
| Two generator endpoint terms | Distributional whole-front flux NF6, with all weighted endpoints retained if resolved generator by generator |
| Two-set pair/layer identity | Full label-set inclusion–exclusion NF9; no truncated Bonferroni sum |
| Two cap hypotheses needed for union assembly | Direct NF theorem, or all actual intersection theorems plus NF9; no common-tip fibre assumption |
| Transverse Gamma in the short proof | Still a real geometric requirement at floor/stratum contacts; not removed merely by increasing N |

This is a complete theorem for broader regular fronts, not the stopping point
for #156. The continued tangency, NN, dimensional and nonconformal attempts,
and the admitted complete null-boundary focusing obstruction, are in
[the continuation](null-mixed-continuation.md) and
[the obstruction proof](null-product-focusing-obstruction.md).

## 7. Continue through the dimensional producer and complete assembly

**Theorem NF-d.** The geometric theorem of §1 holds in every fixed integer
dimension d>=2, with the same contact-atlas definition in dimension d, the
actual metric Omega^2 eta, density A=Omega^d, and independent target
half scalar curvature plus induced SN screen area (counting measure in d=2).
Use exactly `dimension_kernels.py`'s c_d, a_d, beta_d and K_d. This adds
conformally curved regular-front coverage in the previously missing dimensions;
[ND](null-cone-dimensions.md)'s larger *flat lower-null* class remains separate.

Here is the producer and coefficient calculation. Let m=floor(d/2)+1 and
S_d be the area of S^(d-2), equal to two in d=2. The actual interval map has
V=c_d*ell^d*xi^(d/2)*h_d, h_d the normalized integral of A over the unit
d-dimensional rest diamond. Its pair Jacobian is
ell^(d-1)*(1-xi)^((d-3)/2)/2. Reflection still proves smoothness at xi=0;
the factor at xi=1 is integrable also in d=2. In long set
w=ell^2*xi*h_d^(2/d). The floor/phase inverse NF3 remains uniformly regular.
Taylor through degree m-1 gives an O(w^m) remainder. The **actual** moments
of orders 0,...,m-1 vanish, since the kernel Mellin zeros are 2j/d,
j=1,...,m. The normalized remainder is O(rho^(1-2m/d)), tending to zero
in both parities. This is a dimension-dependent estimate, not 4D Gaussian
cancellation.

The short contact transport is geometric and dimension independent. Mellin
inversion starts on 0<Re(s)<2/d, not a fixed 4D strip, and has ell^(d-1-ds), xi^(-ds/2), and angular weight
(1-xi)^((d-3)/2). Subtract the ell Taylor polynomial through degree two
and xi Taylor polynomials through degree m-1, including those of the ell^3
remainder. The remaining double integral is bounded by
ell^(d+2-d Re(s))*xi^(m-d Re(s)/2), times a polynomial in |s|.
It is integrable on a strip strictly beyond s*=1+2/d, up to
Re(s)<min(1+3/d,2(m+1)/d). Simple null poles are killed by the actual
kernel. Gamma decay and polynomial bounds justify the same contour shift
and an o(rho^(-1-2/d)) pair remainder at fixed cutoff.

The rest-diamond moments, obtained by integrating its radius-(1/2-|t|)
spatial balls, are

```math
\begin{aligned}
\langle t^2\rangle&=\frac1{2(d+1)(d+2)},&
\langle x_ix_j\rangle&=\frac{d\delta_{ij}}{4(d+1)(d+2)},\\
h_d&=A-\frac\ell2 DA+\ell^2
 \left[\frac{d+2}{8(d+1)}D^2A
       -\frac{d\xi}{8(d+1)(d+2)}\Box A\right]+O(\ell^3).
\end{aligned}\tag{NF10}
```

With U=A*chi*1_F and V=A*phi, define X-Y by integrating
V*A^(-s) times
(Box U)/2 - s*(partial U dot partial A)/(2A)
- s*(d+2)*U*Box A/[8(d+1)A]
+ s*(s+1)*U*(partial A)^2/(8A^2)
over P. Define Z as the integral of
V*A^(-s)*s*d*U*Box A/[8(d+1)(d+2)A].
These are the computed Taylor coefficients, with distributions interpreted
by the proved contact transport. Spherical averaging gives the quadratic
bracket X+(1-xi)Y/(d-1)+xi Z. No dimensional curvature coefficient was assumed.

The two beta factors have ratio (2-ds)/(d+1-ds), equal to d at s*.
The product of the kernel Mellin transform and the first beta factor has
the following **regular** gamma expression:

```math
\begin{aligned}
E_d(s)&=\widehat K_d(s)\mathrm B(1-ds/2,(d-1)/2)\\
 &=\frac{\Gamma(s)\Gamma((d-1)/2)}{m!}
       \frac{\Gamma(m+1-ds/2)}{\Gamma((d+1-ds)/2)},\\
\frac{\beta_dS_d}{2dc_d}E_d(1)&=a_d,& E_d(1+1/d)&=0,\\
\frac{E_d(1+2/d)}{E_d(1)}
 &=-\frac{\Gamma(1+2/d)}{2(m-d/2)},&
\frac{\beta_dS_d}{2d}c_d^{-1-2/d}E_d(1+2/d)&=-2.
\end{aligned}\tag{NF11}
```

The product identity follows by canceling Gamma(1-ds/2) against the m
linear kernel factors. The point identity follows from gamma duplication
and the existing odd/even a_d,beta_d. For the last identity, m-d/2 is one
in even dimensions and one-half in odd dimensions; respectively
 a_d=4*c_d^(2/d)/Gamma(1+2/d) and
 a_d=2*c_d^(2/d)/Gamma(1+2/d). This proves the normalization for **every**
integer d, not a finite table. At even d the removable beta/kernel product
encodes the double geometric pole; at odd d it encodes a simple diagonal
pole. The vanishing middle value removes the single-face term in both
parities. Rightward residue subtraction and the ell denominator d give

```math
\begin{aligned}
P^{\mathrm{short}}_{\chi,\phi}(\rho)
 &=\frac{a_dQ_0}{\beta_d\rho}
 -\frac{2(X-Y+dZ)|_{s=1+2/d}}{\beta_d\rho^{1+2/d}}
 +o(\rho^{-1-2/d}),\\
\lim\mathcal B_{\chi,\phi}&=2(X-Y+dZ)|_{s=1+2/d}.
\end{aligned}\tag{NF12}
```

The point in the d-dimensional action is a_d*Q0, not C4*Q0. Restoring the
proved long complement cancels it once and gives the last line. Substituting
A=Omega^d for the unit field simplifies that coefficient to

```math
\begin{aligned}
\lim\mathcal A_{\rho,d}
 &=\int_M\left[(d-1)\Omega^{d-3}\Box\Omega
       +\frac{(d-1)(d-4)}2\Omega^{d-4}(\partial\Omega)^2\right]dq\\
 &\quad+\int_P\partial_\alpha
       (\Omega^{d-2}\partial^\alpha\mathbf1_F)\,dq
 =\frac12\int_M R_g\,d\mu_g+\int_JdA_g.
\end{aligned}\tag{NF13}
```

The first bracket is independently the conformal scalar-curvature density
in #90's sign convention. The same coarea flux calculation gives the screen
measure, with Omega^(d-2). In d=2 the spatial sphere consists of two atoms;
a regular SN contact is a point and the flux coefficient is one. No
vanishing tip-neighborhood bound is asserted in 2D: the fixed past domain,
all source neighborhoods and the point remain in the proof.

Every step in §4's restoration and separate law argument now uses the
original dimension-d action and its m+1 actual layer factorials. Finite
second moments justify the bridge. Thus the deterministic NF13 theorem
precedes the original-law expected limit in every dimension. For simultaneous
tips NF8 uses r independent center differences in R^(d-1); its rank proof
and the full NF9 pair/layer identity are unchanged. This includes arbitrary
finite multiplicity satisfying the stated contact condition in each d,
without promoting smoothness to tangential-contact control or to a
nonconformal interval map.
