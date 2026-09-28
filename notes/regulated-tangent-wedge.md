# Regulated tangent-wedge coefficient (#65)

**Status:** the finite-density reduction and deterministic regulated limit below
are machine checked in `WeightedGraphAction.lean` and `TangentWedge.lean`.
The scalar absolute error estimate is also checked. The invariant-frame/area
assembly, the uniform-in-angle argument, and the cross-region subtraction
explanation below are conventional proofs, awaiting independent mathematical
review; they are not an end-to-end Lean theorem about arbitrary joint charts.
Numerical regressions are separate evidence. No two-curved-face limit,
macroscopic cutoff removal, or sample-wise convergence is asserted.

This is G2 of the [flat localization plan](flat-localization-plan.md), independent
of #61. It computes a **first-endpoint-weighted observable** of a finite region's
original action. It is not the unsubtracted action of an infinite wedge or of a
wedge cut into isolated chart regions. The regulator and weight class are fixed
before evaluating any integral or taking any limit.

## 1. Invariant wedge, branch, and independently defined area

Use Lean's signature `(+---)` throughout this note. At a joint point translated
to the origin, let the two spacelike face planes have distinct **future-directed
unit timelike** normals, with their indicated past/future roles. Put

```math
C=g(n_-,n_+)>1,\qquad S=\sqrt{C^2-1},\qquad
\theta=\log(C+S)>0,\qquad k=S/C=\tanh\theta\in(0,1).
```

The inward spacelike direction in the future plane is

```math
e=\frac{C n_+-n_-}{S},\qquad g(e,e)=-1,\quad g(e,n_+)=0.
```

Let the joint plane be the common orthogonal complement of the two normals.
Choose an orthonormal basis on it for the positive metric **minus** the
restricted Minkowski form. Write a point as

```math
X=t n_+ + r e + z,\qquad z\in J,\qquad
W=\{g(n_-,X)>0,\ g(n_+,X)<0\}
  =\{-kr<t<0\}.
```

Thus membership implies positive normal coordinate. This construction fixes the
orientation, rather than recovering a sign from a squared angle relation. The
adapted frame is Lorentz-orthonormal and future oriented; #50's derived absolute
determinant-one law gives the original product Lebesgue measure in these
coordinates, without a guessed volume factor. The joint's area is defined from
its tangent Gram determinant before computing the
action. In these coordinates its density is one, so it is ordinary
two-dimensional Lebesgue measure in the orthonormal joint coordinates. In another
frame it is **not** ambient Euclidean spacetime area.

This is the tangent-plane specialization of #51's `jointGraph_gram`,
`gramDensity`, and derivative-based `jointInducedArea` construction. Its
`JointTransport` theorems preserve that Gram density under affine Lorentz maps,
and multiply it by the square of a positive dilation. The reference spatial
measure there has the independently checked normalized Hausdorff convention.
The wedge itself is noncompact and is not being declared an
`AdmissibleTwoFace`; the geometry is applied pointwise to its joint and compact
test observables. See [the joint geometry proof](../formal/JOINT_GEOMETRY.md).

## 2. A finite regulator specified without reference to the answer

In the above orthonormal frame, write the spatial coordinates as
`x = (r,z1,z2)`. Fix positive constants and a real continuous test function with

```math
R>0,\qquad H\ge 2kR,\qquad
\mathrm{supp}(a)\subseteq\{\lVert x\rVert_\infty\le R\}.
```

There is **no sign restriction** on the test function. Define

```math
h_{k,H}(x)=\min\{kr,H-k\lVert x\rVert_\infty\},\qquad
M_{k,H}=\{-h_{k,H}(x)<t<0\},\qquad w(t,x)=a(x).
\tag{W1}
```

The coordinate cube is only an artificial regulator; its norm is not a
Lorentzian metric or a definition of joint area. On the whole support of the
test function, the height equals the affine wedge height. Positivity of the
height implies the spatial norm is less than the ratio of height parameter to
slope, so the region is bounded. Both functions in the minimum are Lipschitz
with constant at most the slope in **Euclidean spatial distance**; minimum and
positive part retain that bound. Consequently `GraphCapData` applies. In
particular the region is measurable, finite-volume and ambient causally convex.
Its artificial seams need not be smooth. None of the reduction theorems uses
regular-level or collar hypotheses there.

This class is nonempty: take any continuous compactly supported tangential
weight and multiply it by a continuous normal cutoff equal to one at zero.
After enlarging the cube, (W1) applies. For example, a product of three triangular
hat functions, or the negative of `max(0,1-norm x)`, is allowed. The latter is
also exercised by the Lean regression. No field assumes an action value, a
limit, overlap regularity, or normalization.

The regulator is a genuine bounded causal region, so the existing unweighted
`BoundedCausalRegion.expectedBDGAction_eq` interface applies. We do **not**
claim a new weighted discrete-action expectation theorem; the observable below
and its limit are deterministic.

## 3. Observable and proposition

Keep the original constants and the **entire signed** kernel:

```math
c=\frac\pi{24},\qquad
K(v)=\left(1-9v+8v^2-\frac43v^3\right)e^{-v},\qquad
q(x,y)=g(y-x,y-x).
```

For a bounded measurable region and a continuous real weight define

```math
\mathcal A_\rho[M;w]=\frac4{\sqrt6}\sqrt\rho
\left[\int_M w(x)\,dx
-\rho\int_M w(x)\int_{M\cap J^+(x)}
 K\bigl(c\rho q(x,y)^2\bigr)\,dy\,dx\right].
\tag{W2}
```

At weight one, (W2) is exactly the unchanged `continuumMean`. The weight is
attached to the **first endpoint only**; it is not a product of endpoint weights
and is not a redefinition of the BDG action. Both endpoints are still integrated
in the finite region. The prescription is also an exact linear partition of
that original action, as explained in §6.

**Regulated tangent-wedge proposition.** For every regulator and test function
in (W1), and every positive density, with the existing `planeKernel` denoted by
the reduced signed kernel, let

```math
B(r)=\int_J a(r,z)\,dA(z).
```

Then all the integrals in the following identity are absolutely integrable,

```math
\begin{aligned}
\mathcal A_\rho[M_{k,H};w]
 &=\int_J\int_0^\infty a(r,z)G_\rho(kr)\,dr\,dA(z)\\
 &=\frac1k\int_0^\infty G_\rho(s)B(s/k)\,ds,
\end{aligned}
\tag{W3}
```

and

```math
\lim_{\rho\to\infty}\mathcal A_\rho[M_{k,H};w]
 =\frac1k\int_J a(0,z)\,dA(z)
 =\int_J a(0,z)\coth\theta\,dA(z).
\tag{W4}
```

All geometry, weights and regulator sizes are fixed during the density limit.
There is no infinite-volume action and no second limit hidden in (W4).
Changing the height parameter while preserving its margin leaves (W3) unchanged
**at finite density**. Changing the normal cutoff while retaining the same
trace on the joint leaves the limit unchanged. This does not say the full
unweighted regulated action is independent of its artificial boundaries.

## 4. Proof of the reduction, with integrability before cancellation

**Compact domination.** At fixed density the original kernel is continuous on
the compact product of the closures of the finite region. The weight is bounded
there. The causal relation is closed and measurable. A constant on that finite
product box dominates the absolute weighted pair integrand. Thus both signed
Fubini interchanges, the individual future integrals and the outer integral are
legitimate before any cancellation. The same argument works for the
complementary weight used in §6.

**Complete future slices.** The lower epigraph is a future set because its
positive-part height is strictly Lipschitz with constant less than one. If the
first point belongs to the cap, every future causal point below the future
plane still lies above that lower epigraph. Therefore

```math
M_{k,H}\cap J^+(x)=\{y\in J^+(x):y^0<0\}.
\tag{W5}
```

This is the checked `graphCap_complete_future`, including the vertex and null
surface. In particular a partner need not be in the source weight's support.
There is no short-displacement approximation: macroscopic nearly-null pairs
are included in the entire truncated cone.

Translate the cone vertex to the origin and integrate that entire cone using
the checked `coneIntegral` identity. If depth below the future plane is denoted
by the positive variable below, the result is

```math
Q_\rho(d)=\int_{J^+(0)\cap\{y^0<d\}}K\bigl(c\rho q(0,y)^2\bigr)\,dy,
\qquad
\frac4{\sqrt6}\sqrt\rho\,[1-\rho Q_\rho(d)]
 =\frac{\sqrt\rho}{2\pi\sqrt6}F_\rho'''(d).
```

The boundary constant in this identity is essential; it cancels the point term
of (W2). Vertical integration uses the checked finite-fibre FTC:

```math
\int_0^{h(x)}\frac4{\sqrt6}\sqrt\rho\,[1-\rho Q_\rho(d)]\,dd
 =G_\rho(h(x)).
```

The weight is constant along this vertical fibre, so it factors out. This proves
the general `weighted_graphCap_reduction`, with no smoothness or positivity
assumption on the spatial weight. Outside its compact support it vanishes;
on its support (W1) gives the affine height. Spatial Fubini and the substitution
from normal coordinate to height now give (W3). Absolute integrability of this
spatial integrand follows from continuous compact support. The one-dimensional
profile is bounded and compactly supported; it is continuous by dominated
convergence on a **fixed compact tangential domain**. Multiplying it by the
absolutely integrable reduced kernel justifies the half-line expressions too.

Only finite-measure hyperplane endpoints in the time/normal integrals are
changed. No chart seams are deleted. The nonsmooth seams of the tent do not
invalidate the Lipschitz future-set argument. Closed null-related pairs remain
in (W5); they have not been removed to manufacture a localized integral.

## 5. Limit and uniformity away from the degenerate angle

The already checked signed-kernel results give

```math
\varepsilon=\rho^{-1/4},\qquad
G_\rho(s)=\varepsilon^{-1}G(s/\varepsilon),\qquad
\int_0^\infty G(u)\,du=1,\qquad
M_1:=\int_0^\infty u|G(u)|\,du<\infty.
```

The kernel is absolutely integrable but is **not positive**. Substitution in
(W3), followed by subtraction of its signed mass, yields

```math
\mathcal A_\rho[M_{k,H};w]-\frac{B(0)}k
 =\frac1k\int_0^\infty G(u)\,[B(\varepsilon u/k)-B(0)]\,du.
\tag{W6}
```

The bounded profile and absolute kernel mass provide domination. Its derived
continuity at zero proves (W4), without any assumed geometric asymptotic input.
`weighted_wedgeRegulator_limit` checks this conclusion starting from (W2).

For the quantitative class, suppose in addition that the independently chosen
profile obeys a normal Lipschitz bound. Then

```math
|B(r)-B(0)|\le L_B r\quad(r\ge0)
\quad\Longrightarrow\quad
\left|\mathcal A_\rho[M_{k,H};w]-\frac{B(0)}k\right|
\le \frac{L_B M_1}{k^2}\rho^{-1/4}.
\tag{W7}
```

This implication is the checked `wedgeProfileMean_error`. Its inputs can be
verified directly from the observable, not stipulated to imply the answer:
if the spatial weight has a normal Lipschitz constant on each tangential fibre,
bounded by an integrable tangential function, integrating that bound gives the
profile bound with the integral of that function as constant. In particular,
for a separated cutoff and tangential weight it is the cutoff's Lipschitz
constant times the tangential weight's first absolute integral. These classes
contain arbitrary signed continuous compactly supported tangential weights.

Fix a compact positive angle range. The corresponding slopes have a positive
lower bound and an upper bound strictly below one. Choose one source cube and
one regulator height satisfying the margin for the **upper** slope. Formula
(W7) is then uniform, replacing its denominator by the square of the **lower**
slope, for weights with a common normal Lipschitz bound.

Even without a Lipschitz hypothesis, each fixed continuous compactly supported
weight has uniform convergence on that angle range: in (W6), the supremum over
slopes of the profile difference tends to zero for each fixed integration
variable, by continuity at zero and the positive lower slope. It is dominated
by twice the profile bound times the absolute kernel divided by the lower
slope. Dominated convergence proves this uniform assertion. Equicontinuity and
common bounds give the corresponding family version. This supremum argument
and the test-weight-to-profile Lipschitz estimate are conventional, not newly
claimed Lean theorems.

There is **no uniform claim as the angle tends to zero**. The coefficient itself
diverges, and both the rescaled argument and (W7) lose control. Shrinking the
normal cutoff with density is also outside the fixed-regulator proposition.

## 6. Artificial boundaries and both endpoints of cross-patch pairs

The obstacle with a naive finite wedge cut is precise: the action of a smaller
region does not retain causal partners beyond its new walls. Small volume of a
wall neighborhood does not justify discarding the normalized pair term.

The repair is **not** to declare those terms negligible. Use the exact
first-endpoint observable (W2). Linearity gives, at each finite density,

```math
\mathcal A_\rho[M;w]
 =\mathrm{continuumMean}_\rho(M)-\mathcal A_\rho[M;1-w].
\tag{W8}
```

This is `weightedContinuumMean_complement`. The artificial complement is
specified by geometry and the test weight, before taking the limit. It is
subtracted exactly; its unweighted contribution is **not asserted to vanish**.
All partner endpoints from a weighted source still occur. Regulator changes
beyond the stated margin affect neither its future slice nor (W3). Differences
between allowed normal cutoffs with the same joint trace vanish by (W6).

More explicitly, let a measurable source subregion contain the support of the
weight inside the finite region. Restricting partners to that subregion would
change the answer by

```math
\mathcal A_\rho[M;w]-\mathcal A_\rho[S;w]
 =-\frac4{\sqrt6}\rho^{3/2}
   \int_S w(x)\int_{(M\setminus S)\cap J^+(x)}
     K\bigl(c\rho q(x,y)^2\bigr)\,dy\,dx.
\tag{W9}
```

This follows by splitting the actual second-endpoint integral; boundedness
provides absolute integrability. (W3) includes this entire term. We neither
assume it zero nor need it to vanish separately at high density. It is generally
nonzero: with slope one-half, source cube radius one, and regulator height two,
the source `(-0.2,0.8,0.9,0)` has the timelike partner
`(-0.05,0.8,1.02,0)` outside that cube but inside the regulator. With positive
hat weights there is an open positive-volume set of such pairs. Since the
kernel is positive near zero and squared intervals are bounded on the finite
regulator, at sufficiently small positive density the cross integral is
strictly positive. Thus dropping it is not an exact regulator construction.
This is a counterexample to **pair omission**, not to (W4) or Conjecture 1′.

For a finite overlapping partition, sum the weights on the first endpoint while
keeping the whole second-endpoint domain. If both endpoints are partitioned,
the exact pair identity has a double sum over **all** ordered chart labels,
including different labels. Keeping only equal labels is not (W2). Such finite
sums commute with the already absolutely integrable pair integral. This gives
a valid local observable for later stability work, not a proof that arbitrary
curved-face chart contributions can already be replaced by wedges.

## 7. Planar compatibility, boosts, and dilation

For a planar future face the normal height derivative at the joint is the
slope above. The spatial coarea factor is its reciprocal; (W3) uses exactly the
same signed `planeKernel`, normalization and depth integration as the existing
graph-cap reduction. Thus the planar specialization gives the checked
reciprocal-gradient weight, not a separately fitted constant. At slope one-half
the coefficient is two, as independently restated in the Lean regression.

Transport the **region and test observable together** by an affine
time-oriented Lorentz map. The checked
`PoincareEquiv.weightedContinuumMean_image` substitutes both endpoints in (W2),
with the full affine inverse in the weight. Independently, #51's
`inducedArea_comp` and `twoFace_weight` preserve the derivative-based area and
the positive angle quotient. Therefore (W4) has the same invariant meaning
in every such frame, including translations and spatial orientation reversal.
A boost tangent to the joint changes its Euclidean spacetime area but not its
Lorentzian Gram area; the Python regression checks that negative control.

For a positive dilation, transport the observable by inverse dilation. Both
endpoint Jacobians and the unchanged kernel give the checked identity

```math
\mathcal A_\rho[sM;w(\cdot/s)]
 =s^2\mathcal A_{\rho s^4}[M;w].
```

Independently #51's `jointInducedArea_smul` and `boundaryIntegral_dilate` give
that same second-power area factor, with unchanged angle. The source cube and
regulator height dilate along with the region; keeping the old coordinate
cutoffs would be a different observable. Positive and reciprocal dilation are
regression cases.

## 8. Verification boundary and reproduction

New audited Lean modules and independent regression:

- `WeightedGraphAction`: original-action specialization, weighted bilocal
  integrability, exact source linearity/complement, Lorentz/dilation transport,
  vertical Fubini and the signed weighted graph-cap reduction.
- `TangentWedge`: geometric tent admissibility and affine support margin,
  derived tangential profile continuity and compact support, exact
  four-dimensional reduction to that profile, its absolute integrability,
  positive-branch coefficient limit and scalar absolute error estimate.
- `TangentWedgeRegression.lean`: independently expanded bilocal/limit contracts,
  a nonempty regulator, nonzero **negative** test weight, complete partners,
  affine covariance and dilation. No analytic-conclusion structure fields.

The invariant geometric assembly uses the existing #51 transport theorems as
explained above; no new arbitrary-plane induced-area theorem is claimed.
The conventional uniformity and cross-subregion arguments are explicitly
separated from the checked declarations. Run the full source/axiom audit,
not just a library build:

```sh
(cd formal && ./check.sh)
.venv/bin/python -m unittest -v test_tangent_wedge
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

`tangent_wedge.py` independently integrates the **original** polynomial kernel
over the full radial/time future cone. For polynomial compact normal cutoffs,
first-endpoint depth integration gives an elementary polynomial weight, used
without the auxiliary function or reduced kernel. Tests compare this pair
integral with a separate reduced-kernel evaluator, refine quadrature and
precision, vary fixed cutoff shapes, check signed tails and the density limit,
and test independent normal/Gram geometry. Quadrature refinement is not a
certified error bound and does not prove any theorem.

**Remaining gates:** long-null geometric cancellation for actual curved regions
(#61), stability of first-endpoint observables under curved-face replacement
(#66), and overlap-aware globalization/cutoff removal (#67). A finite regulated
wedge computation alone does not settle any of those or close #24.
