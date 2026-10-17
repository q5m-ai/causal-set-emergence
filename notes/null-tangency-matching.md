# Joint signed matching at a two-sheet tangency (#156)

**Conventional written proof, not Lean-checked or independently accepted.**
This continues [NT1–NT3](null-mixed-continuation.md). The new method resolves
**the displacement at closing before estimating the phase integral**. It does
not differentiate a scalar positive part three times, impose finite contact
order, or interchange a spacelike-to-null limit. It supplies a complete
producer, deterministic consumer and subsequent original-law expectation.
It does **not** complete general NN or intrinsic-metric coverage. See the
[current closure audit](null-closure-audit.md) and the single original-item
crosswalk in the [required ledger](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).

## 1. Exact theorem and independent geometric quantities

Fix any integer dimension d at least two. Use the same globally conformally
Minkowski spacetime, smooth positive conformal factor, strict smooth spacelike
floor F=t+H(x), open past set P, nonempty bounded M=F-positive intersect P,
physical interval and canonical dimension-d action as [NF-d](regular-null-front-limit.md).
The conformal factor is positive and smooth on a neighborhood of the compact
causal enclosure; geometry is fixed. Allow the following finite contact cover:

1. NF's regular polyhedral-contact charts, unchanged, including its arbitrary
   finite multiplicity and dependent normals.
2. Charts where the actual upper front consists of **two distinct smooth null
   sheets** meeting transversely in a smooth spacelike codimension-two crease C.
   P is locally their past-side intersection or union. The floor may meet C
   in an arbitrary smooth height zero set: no transversality, contact-order,
   isolated-critical-value or measure-zero hypothesis on that set is imposed.

The second condition is actual face geometry. It is not a genericity
restriction on #156: contacts with three or more incident sheets that fail
NF's rank condition, coincident rays, and intrinsic nonconformal intervals
remain outside **this theorem**, not outside the parent contract. Away from
floor contacts P can retain all its fixed tips and singularities as in NF.
A finite cover does not require a finite number of components of a height
zero set. All integrals below use the actual geometric measures.

Let J_reg be the exposed regular SN pieces. Let E_union be the subset of the
union-type creases where F=0, with their induced (d-2)-area, restricted as a
Borel measure even when that zero set is not a submanifold. Intersection-type
creases carry no such added atom. Repeated charts count the same crease only
once by a partition of unity. Define, independently of the action,

```math
\begin{aligned}
\mathcal T_{\mathrm{TC}}(M)
 &=\frac12\int_M R_g\,d\mu_g+\int_{J_{\mathrm{reg}}}dA_g
       +2\int_{E_{\mathrm{union}}}dA_g .
\end{aligned}\tag{TC1}
```

**Theorem TC-d.** The complete deterministic action tends to TC1. Separately,
the expectation under the original dimension-d finite Poisson law tends to
TC1. The coefficient **two** is derived in §5, not specified as admissibility.
The complete action, order and law are unchanged. This is a stronger result
than “tangencies have zero volume”: a persistent union-type floor/crease
coincidence can have positive screen area and a nonzero extra term.

For two simultaneous cones at distinct centers, the theorem removes CT's
transverse-floor/crease and central-overlap restrictions in every dimension,
for every smooth globally strict-Lipschitz H with positive value at both tips
and every admitted smooth positive conformal factor. Empty lens intersections
have action and target zero. This is an instantiation of TC-d, not its proof
or a substitute for general front coverage.

## 2. Actual normal geometry, before estimating the kernel

Near C choose coordinates (w,y1,y2), with w on C and both y-coordinates
increasing into the intersection of the past sides. The axes at C can be
chosen as the two past null directions in its Lorentzian normal two-plane.
The restriction of the future timelike covector dF to this normal plane is
future timelike: removing its spacelike tangential component makes its
Lorentzian squared norm more negative in the (-,+,...,+) convention. Consequently both inward derivatives of F are
strictly negative. Compactness of the selected charts gives positive margins.
This argument applies even where dF annihilates the tangent space of C; no tangential floor field
on C is required.

Let u=(1,b*n), b=sqrt(1-xi), and let ell denote the **physical time gap**.
Write h(w)=F(C(w)). At the crease, the actual shifted floor is

```math
\begin{aligned}
g(w,\ell,\xi,n)&=F(C(w)-\ell u)=h(w)-\ell a(w,\ell,\xi,n),\\
a(w,\ell,\xi,n)&=\int_0^1
 [1+b\nabla H(C_x(w)-s\ell b n)\cdot n]\,ds,\\
1-\lambda&\le a\le1+\lambda,\\
\partial_\ell g&=-[1+b\nabla H(C_x(w)-\ell b n)\cdot n]
                 \le-(1-\lambda).
\end{aligned}\tag{TC2}
```

Hadamard's integral formula in the normal coordinates gives
F(q-ell*u)=g-y1*c1-y2*c2, with positive smooth c1,c2 on a common smaller
chart. The map z_i=y_i*c_i is a local diffeomorphism, preserves both coordinate
faces, and makes the actual domain exactly z_i>0, z1+z2<g. Its inverse Q is
smooth in w,ell,b,n and z, including small negative z used for algebraic
extension below. Near xi=0 it has all required uniform xi derivatives;
near xi=1 only boundedness and ell derivatives are used.

Use a fixed smooth endpoint partition subordinate to these charts. Separate
the neighborhood of g=0 from its regular complement by fixed smooth weights.
Choose one sufficiently small positive temporal cutoff delta so all maps
exist on the short support, simultaneously on the finite cover. The ordinary
regular complement is handled by NF. In a crease chart put z=g*s, where s
ranges over the fixed unit two-simplex. After this exact change of variables,
the short pair integrand, including both endpoint densities and the true
whole-diamond phase, has the form

```math
\begin{aligned}
&\int dw\int_{S^{d-2}}dn\int_0^\delta d\ell\,\ell^{d-1}
 \int_0^1d\xi\,(1-\xi)^{(d-3)/2}\\
&\quad\int_\Delta ds\;g_+^2 B(w,\ell,\xi,n,g s)
 K_d\!\left(c_d\rho\ell^d\xi^{d/2}
              h_d(Q(w,\ell,\xi,n,g s),\ell,\xi,n)\right).
\end{aligned}\tag{TC3}
```

The constant Jacobian factor one-half from NF is included in B. Source and
partner fields, normal-coordinate Jacobians and all cutoffs are also in B.
The normalized interval factor h_d is **NF's actual integral of Omega^d over
the boosted diamond**, not the scalar gap h. It is bounded above and below
positively, smooth at xi=0, with the required mixed derivatives. The equation
is a domain identity; it has not replaced the phase by a tangent model.

At finite density every displayed compact integral is absolutely integrable.
This licenses the coordinate changes, not an absolute high-density estimate.
The smooth extensions at negative g are auxiliary signed subtractions only;
no physical interval or observable is redefined on the actual domain.

## 3. The joint signed bound: resolve closing first

For h<=0, TC2 makes the actual domain empty for every positive ell. For h>0,
let ell0 be the unique small root of g=0 whenever it is on the short support.
The implicit-function theorem at h=ell=0, followed by strict monotonicity,
gives ell0=h*L(w,h,xi,n), where L and its reciprocal are positive bounded
smooth functions, with uniform xi derivatives near zero. Extend the root
smoothly over a small fixed h-neighborhood; if it lies beyond the short
support, the following error is simply zero.

There is the **exact** identity

```math
\begin{aligned}
g_+^2&=\mathbf1_{h>0}g^2
       -\mathbf1_{h>0}\mathbf1_{\ell>\ell_0}g^2 .
\end{aligned}\tag{TC4}
```

The first term makes TC3 smooth in ell and xi near zero on the fixed
w-domain h>0. It is the smooth Taylor/Mellin part S. The second is the
closing correction E, still with the same B and actual phase at g*s. This
keeps the entire closing strip and both subtraction tails; E is not discarded
because its source set is small.

For E, set ell=h*L*r, r>=1, **before** the phase estimate. Then

- ell^(d-1) d ell times g^2 equals h^(d+2)*r^(d+1) times a smooth bounded
  factor depending on w,h,h*r,1/r,xi,n,s;
- the phase is c_d*rho*(h*r)^d*xi^(d/2) times a positive smooth factor;
- all required xi derivatives of these factors are bounded uniformly.
  Indeed ell, g and their xi derivatives are bounded by constants times h*r,
  while 1/r lies in [0,1]; the fixed smooth cutoffs vanish beyond their common
  coordinate support. The bounds include the moving temporal cutoff.

In a fixed small xi collar put eta=xi times the positive phase factor to
the power 2/d. Its derivative at xi=0 has a uniform positive lower bound.
The inverse and transformed amplitude have uniform derivatives through
m=floor(d/2)+1. Expand that amplitude through degree m-1. The **actual**
K_d moments of eta^j vanish for j=0,...,m-1. Retain the fixed-positive-phase
complement and the tails of the subtracted polynomials; they are exponentially
small. Taylor's integral remainder therefore proves, uniformly in the other
parameters, the signed xi estimate

```math
\begin{aligned}
\left|\int_0^1 (1-\xi)^{(d-3)/2} b_0(\xi)
 K_d(\Lambda\xi^{d/2}b_1(\xi))\,d\xi\right|
 &\le C(1+\Lambda)^{-2(m+1)/d},\\
\left|\rho^{1+2/d}E_\rho(w)\right|
 &\le C\int_{\rho^{1/d}h(w)}^\infty
       v^{d+1}(1+v^d)^{-2(m+1)/d}\,dv
       \quad(h(w)>0).
\end{aligned}\tag{TC5}
```

Here b1 is positive, b0 includes all the preceding transformed factors,
and the finite n and simplex integrals have been bounded **after signed xi
integration**. The first line uses a smooth xi collar for differentiation;
the endpoint xi=1 has its original integrable angular weight and a uniformly
positive phase. For Lambda<=1, boundedness of K_d gives the same estimate
with an enlarged constant. Neither line is an estimate for the absolute
kernel before cancellation.

The second line follows by integrating r>=1 and substituting
v=rho^(1/d)*h*r. Its majorant is integrable: at infinity its power is -3
for even d and -2 for odd d, and at zero it is d+1. It tends to zero for
each fixed h>0. At h<=0 the correction is exactly zero, including any
positive-measure zero level. The w-domain has finite measure. Dominated
convergence thus proves

```math
\begin{aligned}
\rho^{1+2/d} E_\rho&\longrightarrow0 .
\end{aligned}\tag{TC6}
```

This is the missing **joint physical-phase/angular** estimate for a two-sheet
closing tangency, with arbitrary fixed smooth height gap. Even an infinitely
flat gap or a positive-measure zero set is allowed. There is no required
Dini modulus, extra positive power or third derivative of the integrated
ramp. The intermediate variables depend on density only for estimating an
integral; the physical cutoff delta and all regions/partitions remain fixed.

## 4. Complete short coefficient and long restoration

S in TC4 is smooth on a fixed finite-measure domain. Its derivatives are
uniform even as h decreases to zero, because g^2 B(g*s) and its actual interval
factor are smooth, not inverse powers of h. For each fixed h>0, S agrees with
the actual shifted-floor integral for sufficiently small ell. Its Taylor
coefficients are therefore the same directional derivatives and rest-diamond
moments used in NF; the coordinate change has not introduced arbitrary
angular Taylor coefficients. Integrating these uniformly bounded derivatives
over h>0 preserves their spherical averages. NF10–NF12's two-variable
subtraction therefore applies to S: the point term, vanishing single-face
term, critical coefficient and summable remainder follow with the genuine
dimensional constants. TC6 supplies the entire omitted closing correction.

Here is an independent way to identify that coefficient, without guessing
its flux at a nonsmooth zero set. Raise the floor by a fixed epsilon>0:
replace F by F-epsilon, equivalently H by H-epsilon. For a sequence of positive
regular values epsilon decreasing to zero, all two-sheet contacts are regular
by Sard's theorem on the finitely many crease charts. NF's already transverse
higher contacts persist for sufficiently small epsilon; tips remain off the
floor. NF-d thus computes the **coefficient of S_epsilon** geometrically.
The coefficients of S_epsilon converge to those of S by dominated convergence
on h>epsilon: every derivative used is uniformly bounded and the h=0 level
is excluded on both sides. TC6 applies separately at epsilon=0 and at each
fixed epsilon. This is a limit of explicit coefficient integrals, **not** an
interchange of density with a family of geometries.

For an intersection-type crease the raised-floor SN pieces approach only the
strictly exposed regular SN pieces, and give no area to h=0. To see the side,
move an SN contact a small distance into the past along its own null generator.
The other future null conormal has strictly positive inner product with that
generator, since the two rays are distinct. This moves the contact outside
the other sheet's past-side intersection. The normal derivative has a fixed
positive margin on each compact crease chart. Surface Jacobians remain bounded
and converge smoothly. Dominated convergence of the actual induced-area
integrals gives zero trace on h=0 and the regular SN area elsewhere.

The bulk integral converges by dominated convergence in the finite region;
the floor is a smooth volume-null graph. No boundary contribution was extracted
from a density fit. Together these facts identify the full intersection
coefficient as half curvature plus its regular SN area.

NF3's long floor/phase proof uses only strict spacelikeness of F and the fixed
past set P. It **never used** the floor/crease contact rank. Its all-dimensional
long estimate therefore applies unchanged at these tangencies, at the same
fixed positive temporal split. Add it to the short result, with the physical
point only in short. Complementary smooth/strict temporal bands cancel exactly.
All fixed upper tips, seams and other front singularities away from the floor
remain in P and in the actual integrals throughout.

## 5. Union contacts, the derived extra area, and full partitions

Near a union crease, apply the exact indicator identity for the two smooth
past sides and their intersection in TC3. This is a pointwise identity in the
future endpoint **after** the actual future-set/past-set pair reduction; it
is not componentwise bilocal additivity. Each term uses the same physical
weighted diamond. Smooth single sheets have the NF coefficient and the
intersection has §4's coefficient.

At a regular exposed SN point the signed sum is one. At a strictly hidden
sheet it is zero. At a point of E_union both single-sheet SN contacts tend
to the same geometric screen, each with unit weight, while the intersection
term has zero trace there by §4. Hence the coefficient on that screen is
**1+1-0=2**, proving TC1. For a zero set of zero (d-2)-area this term vanishes
by the derived measure formula, not by deleting an action neighborhood.
In d=2 it is a genuine counting atom at a coincident three-face contact.

A concrete check of the geometric side for simultaneous tips c1,c2 is useful.
For sheet i write x=ci+R_i(omega)*omega and R_i=H(x). Its screen metric is
Omega^(2)*R_i^2*domega^2, with the corresponding (d-2)-area. Raising the floor
has dR_i/d epsilon=-1/(1-grad H dot omega). At equality of the two radii,

```math
\begin{aligned}
\frac{d}{d\varepsilon}(r_i-r_j)
 &=-\frac{1-\omega_i\cdot\omega_j}
          {1-\nabla H\cdot\omega_i}\lt0 .
\end{aligned}\tag{TC7}
```

Thus both coincident contacts become union-exposed and neither becomes
intersection-exposed. Their induced measures at coincidence equal the
independently induced measure on C almost everywhere on its zero-height set.
Indeed the points of that zero set with nonzero tangential derivative of h
have zero (d-2)-area by the implicit-function theorem and a countable chart
cover. At the remaining points both SN tangent spaces agree with that of C. In 4D with
centers at ±a on an axis,
C has screen density a/sqrt(a^2+|w|^2) times ordinary d2w, as computed directly
in TT2; the coincident part has twice this density, with Omega^2. No logarithm
of a rescalable null normal is introduced.

Use a finite smooth endpoint partition in the general theorem. Every ordered
source/partner label pair remains; their sum is one, as is the diagonal point
sum. Source and partner derivative terms in the smooth coefficient cancel
only in this complete sum. TC5 is uniform for each of the finitely many fixed
weights, so their closing errors are summable. Artificial normal-chart and
phase-collar boundaries remain in the smooth amplitudes and complementary
integrals. This restores the whole deterministic action and proves TC1.

For global finite cone unions, NF9 additionally supplies the actual complete
point/pair/exclusive-layer inclusion–exclusion over all nonempty label subsets.
One may use it only after every needed intersection satisfies the theorem's
contact hypotheses. No threefold tangency is converted to a twofold one by
truncating that sum.

## 6. Subsequent expectation and precise remaining boundary

As in NF, M is bounded Borel with finite positive smooth atomless volume.
Future/past-set containment proves every closed ambient interval is inside M;
the conformal metric changes its volume, not this order. The order and exclusive
three-point relation are Borel. The original Poisson cardinality/independent
position law has a finite second factorial moment, bounding every exclusive
ordered layer. Reduced two-point Mecke with both intensity factors and the
actual layer factorials gives, at every positive density,

```math
\begin{aligned}
\mathbb E A^{\mathrm{disc}}_{\rho,d}(M)&=\mathcal A_{\rho,d}(M),\\
\lim_{\rho\to\infty}\mathbb E A^{\mathrm{disc}}_{\rho,d}(M)
 &=\mathcal T_{\mathrm{TC}}(M).
\end{aligned}\tag{TC8}
```

The second line uses the completed deterministic result of §§3–5. No
sample-wise convergence, limit/expectation interchange or new compiled
geometric instance is claimed. Empty intersections use the empty Poisson
configuration and zero action.

**Not a parent closure:** this resolves arbitrary two-sheet closing tangency,
including flat height gaps and persistent coincidences, in the explicitly
stated conformal class. Higher dependent floor/front tangencies, both moving
null fronts, and intrinsic cut/caustic/contact matching still need their own
geometric producers. The audit records two distinct NN attempts and a stronger
necessary consequence of NP for any proposed corrected general statement.
