# General-metric short geometry and producer derivation (#150)

**Written short theorem, not a compiled proof or independent human review.**
This note derives uniform geometric locality, bounded-rapidity interval
coefficients, all-dimensional model responses, independent target geometry
and exact finite-density restoration. Its
[signed-remainder continuation](general-metric-short-remainders.md) now derives
GM-S1, GM-S2 and GM-S3 from the actual metric interval, in that order: null-edge
rescaling and signed remainder, entire single-face response, and actual moving
corner comparison. The acceptance map is §8. Model coefficients and tests
remain distinct from those proofs. The general **short** theorem is (S30);
no general long, full-action or expectation limit is inferred. #81/#24 remain
open, with nonlocal analysis owned by #151. No new conformal pilot is used.

Base: `0bfc8bb3d6dce188c39414fedef5e0a3bd646dd5` on
`origin/issue-81-general-coverage`. The accepted written
[#76](curved-assembly.md) and [#136](nonpolynomial-short-limit.md) outputs are
calibrations, not general-metric estimates. Their exact rest-diamond phase,
ratio inverse and derivative bounds cannot be transplanted to arbitrary metrics.
No action, probability, formal source, checker or dependency is changed.

Coordination before edits:
[#149 dimension notification](https://github.com/q5m-ai/causal-set-emergence/issues/149#issuecomment-6049612144),
[#151 cutoff notification](https://github.com/q5m-ai/causal-set-emergence/issues/151#issuecomment-6049612362).
#151 subsequently [adopted the same temporal-gap cutoff](https://github.com/q5m-ai/causal-set-emergence/issues/151#issuecomment-6049652763).
The [#149 interface at `dc6233e`](https://github.com/q5m-ai/causal-set-emergence/blob/dc6233ebe3cbf731cc8d5ee2e8a7b0aba08e5636/notes/dimension-producer-interface.md)
was also inspected: its constants, volume phase, signed pieces and exact cutoff
conversion agree with this note. Its flat radial-null cutoff is not identified
with the temporal gap. This is interface coordination, not mathematical review.
Shared coefficients are consumed from [dimension-kernels §§1–4](dimension-kernels.md).
The continuation also inspected #149's Minkowski producer at `7eb3313` and
[#151's new written focusing obstruction at `db69142`](https://github.com/q5m-ai/causal-set-emergence/blob/db691421624f0e598fe9e80a660cccaac4db499a/notes/seven-dimensional-focusing-obstruction.md).
Its seven-dimensional slab is directly covered by the short theorem's (S31);
no unfinished long or flat-manifold conclusion is assumed, and none of this
coordination is independent mathematical review.

## 1. Frozen geometry and observable

Fix an integer physical dimension $`d\ge2`$ and exactly
[G-SS](general-contract.md#3-a-precise-non-vacuous-general-core-candidate): smooth
ambient time-oriented globally hyperbolic spacetime, nonempty precompact open
ambient-causally-convex M, its two compact smooth spacelike faces and transverse
joint, possibly disconnected or empty. No graph, topology, no-caustics or
combined-slope restriction is added. Smoothness is not a conclusion about the
regularity of a pushed phase density.

Use signature $`(+,-,\ldots,-)`$ and **#90's curvature sign**, in which the
normal-coordinate volume density is $`1+\mathrm{Ric}_{ab}X^aX^b/6+O(|X|^3)`$.
Let $`c_d,a_d,\beta_d,K_d`$ be exactly the existing dimension-indexed constants
and kernel. Ordinary sphere measure has mass $`S_{d-2}`$, including $`S_0=2`$.
There is no normalized angular measure hidden in a pair integral. For fixed
smooth endpoint fields chi and phi on a neighborhood of the auxiliary tube,
write the canonical weighted notation

```math
\begin{aligned}
V_M(x,y)&=\mu_g(M\cap(I[x,y]\setminus\{x,y\})),\\
P_{\chi,\phi}(\rho)&=\int_{M\times M}\mathbf1_{x\preceq y}
 \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
A_{\chi,\phi}(\rho)&=a_d\rho^{2/d}\int_M\chi\phi\,d\mu_g
 -\beta_d\rho^{1+2/d}P_{\chi,\phi}(\rho).
\end{aligned}\tag{G1}
```

The independent unit-field target remains half the scalar-curvature integral
plus induced joint area times the positive-normal angle weight. Null relations
remain in the order. Smooth volume is atomless. Ambient causal convexity, not
global hyperbolicity by itself, identifies the restricted and ambient intervals
for actual endpoints in M. Auxiliary pairs outside M use **ambient** interval
volume only and cancel exactly in §5. They are not another observable.
Finite-density Fubini is legitimate here: global hyperbolicity makes the causal
relation closed, hence the three-variable interval indicator Borel. Integrating
that indicator over the compact causal hull of §2 makes V measurable and
bounded. Smooth volume is finite on that hull, the fields are bounded on their
compact domains, and the polynomial-exponential kernel is bounded. Thus each
pair integral and every finite signed sum below is absolutely finite. This is
not a probability construction or an asymptotic estimate.

## 2. Uniform interval locality: a proved geometric lemma

Choose a smooth Cauchy temporal function tau, increasing to the future, and an
auxiliary smooth Riemannian metric h. Existence of such a temporal function is
the standard smooth temporal-function theorem for globally hyperbolic
spacetimes; no metric or observable is replaced by it. Choose a compact
neighborhood C of the closure of M large enough for the local constructions.
Its causal hull $`H=J^+(C)\cap J^-(C)`$ is compact. To see the needed bound,
cover C by finitely many sets $`I^+(p_i)\cap I^-(q_i)`$. Every interval with
endpoints in C is contained in the finite union of compact diamonds
$`J^+(p_i)\cap J^-(q_j)`$; the hull is closed in this compact union.

On H, the future causal h-unit vectors form a compact set and d tau is strictly
positive on it. Its minimum b is positive. Every causal curve in H therefore
satisfies

```math
\begin{aligned}
|\dot\gamma|_h&\le b^{-1}d\tau(\dot\gamma),\\
\mathrm{length}_h(\gamma)&\le b^{-1}
 [\tau(\gamma(1))-\tau(\gamma(0))],\\
z\in I[x,y]&\quad\Longrightarrow\quad
 d_h(x,z)\le b^{-1}[\tau(y)-\tau(x)].
\end{aligned}\tag{G2}
```

Choose finitely many geodesically convex normal neighborhoods U_i and relatively compact source
supports K_i inside them covering a neighborhood of the closure. Near a face
or joint also use smooth temporal-flow coordinates subordinate to U_i: the
flow is future timelike, so each spacelike face is a graph there. At a joint,
transversality gives a regular difference of the two graph heights. These
are **local** presentations, not global envelopes. Shrink supports so each
U_i sees exactly the appropriate interior, single-face or joint strata and
all needed graph germs extend across the support. Compactness gives a positive
h-distance epsilon_i from K_i to the complement of U_i. Normal neighborhoods
and their supports can be chosen with all these properties by shrinking a
finite cover; a normal coordinate system and a face-flattening coordinate
system need not be the same coordinate system.

Choose once $`0<\delta<b\min_i\varepsilon_i`$, and decrease it for the
finitely many graph/tube margins. For x in K_i and causal y in C with
$`\tau(y)-\tau(x)<\delta`$, **every point of the ambient interval** lies in
U_i by (G2). The unique local normal geodesic thus describes that interval;
no other ambient branch can leave U_i and return. For auxiliary full future
cones one obtains the same conclusion without assuming y in C in advance:
put the K_i strictly inside C, bound causal h-speed on C, and use the first
exit from C. Choosing delta smaller than the distance-to-exit times that
speed bound prevents an exit. Then the causal-hull argument applies.

This proves uniform locality even arbitrarily close to the null edge. It
neither asserts a regular phase inverse there nor substitutes small interval
volume for locality. In Minkowski space a fixed displacement with
$`v=t+r=v_0>0`$ and $`u=t-r\downarrow0`$ has volume
$`c_d(uv_0)^{d/2}\to0`$ but does not approach the source. Such pairs with
large temporal gap are retained in long, not discarded as Taylor errors.
The thin-torus seam and sphere-circle cut examples therefore pose no locality
exception to this lemma: only genuinely short intervals are asserted local.

## 3. Restricted interval volume from the metric, with its precise boundary

### Bounded-rapidity theorem

Let o range over a compact set in the above charts, and let U range over a
**compact subset of the future unit timelike bundle**. Put
$`x=\exp_o(-TU/2)`$, $`y=\exp_o(TU/2)`$ for sufficiently small positive T.
If these are actual endpoints in M, the restricted volume equals the ambient
one. In the orthonormal midpoint normal frame with U the time axis,

```math
\begin{aligned}
V(x,y)&=c_dT^d\left[1-A_d\mathrm{Ric}_o(U,U)T^2
                         -B_dR(o)T^2+O(T^3)\right],\\
A_d&=\frac{d}{24(d+1)},\qquad
B_d=\frac{d}{24(d+1)(d+2)}.
\end{aligned}\tag{G3}
```

The bound is uniform on that compact timelike bundle, **not** uniform as its
rapidity tends to infinity. Here is a derivation fixing both signs and both
coefficients, rather than importing 4D values.

The normal-coordinate metric is
$`g_{ab}(X)=\eta_{ab}+R_{acbd}(o)X^cX^d/3+O(|X|^3)`$ in this convention.
Taking its determinant gives the density in §1. Integrating sections of the
flat rest diamond gives its normalized ordinary second moments

```math
\begin{aligned}
\langle t^2\rangle&=\frac{T^2}{2(d+1)(d+2)},&
\langle X_iX_j\rangle&=
 \frac{dT^2\delta_{ij}}{4(d+1)(d+2)},\\
\frac{\Delta V_{\mathrm{density}}}{c_dT^d}
 &=T^2\left[\frac{\mathrm{Ric}_{00}}{24(d+1)}
                -\frac{dR}{24(d+1)(d+2)}\right].
\end{aligned}\tag{G4}
```

For example divide the integrals of t squared and of the spatial ball moments
by $`2S_{d-2}\int_0^{T/2}(T/2-t)^{d-1}dt/(d-1)`$ and use the elementary
beta integral. Also $`\sum_i\mathrm{Ric}_{ii}=\mathrm{Ric}_{00}-R`$.

The light-cone displacement is equally necessary. The signed squared geodesic
separation between X and Y in midpoint normal coordinates, to degree four, is

```math
\begin{aligned}
s_g(X,Y)&=\eta(Y-X,Y-X)
 +\tfrac13R_{acbd}(Y-X)^aX^c(Y-X)^bX^d+O((|X|+|Y|)^5).
\end{aligned}\tag{G5}
```

This follows by inserting the metric expansion in the energy of the straight
segment. Its first variation for the flat metric vanishes with fixed endpoints;
the path correction contributes only at higher order. For X one of the two
tips, the null equation at $`Y=(t,rn)`$ becomes
$`(T/2\mp t)^2-r^2+(T^2r^2/12)R_{i0j0}n_in_j=0`$ to the required order.
Consequently, with $`r_0=T/2-|t|`$,

```math
\begin{aligned}
\Delta r&=\frac{T^2r_0}{24}R_{i0j0}n_in_j,\\
\frac{\Delta V_{\mathrm{cone}}}{c_dT^d}
 &=-\frac{T^2}{24}\mathrm{Ric}_{00},\qquad
 \sum_iR_{i0i0}=-\mathrm{Ric}_{00}.
\end{aligned}\tag{G6}
```

Integrate the radial boundary displacement against $`r_0^{d-2}`$ and use
$`\langle n_in_j\rangle=\delta_{ij}/(d-1)`$. Adding (G4) and (G6) gives
(G3). In particular, keeping only the volume-element correction gives the
wrong directional Ricci coefficient.

**Remainder justification and regularity boundary.** Rescale normal coordinates
by T. The metric is eta plus a quadratic perturbation with Ck remainder of
order T cubed on a fixed compact coordinate set, for each fixed k provided
sufficiently many metric derivatives are bounded. Solve the geodesic ODE from
each tip with null initial direction, parametrizing by coordinate time; its
time derivative is bounded away from zero on this compact timelike family.
The rescaled cone radius divided by time-from-tip is a smooth function of T,
direction and time-from-tip, including zero, by smooth dependence of the ODE.
The two radii meet transversely near rescaled time zero (their time derivatives
at T=0 are +1 and -1). The implicit function theorem gives their smooth
switching time. Integrate each side separately up to this moving switch.
Taylor's integral remainder on these compact parameter domains gives the
relative $`O(T^3)`$ in (G3); differentiating it p times costs at most p powers
of T for $`0\le p\le3`$. Direction/base derivatives of any fixed finite order
are bounded after taking the corresponding additional smooth metric bounds.
This argument avoids dividing a null equation by a vanishing tip radius.
It proves no finite-regularity optimum and no null-edge phase derivative bound.

### Both endpoint measures and the source-normal model

In any fixed chart the pair measure is exactly
$`\sqrt{|\det g(x)|}\sqrt{|\det g(y)|}\,dx\,dy`$.
At the two tips in a **fixed** midpoint normal chart, each factor is
$`1+T^2\mathrm{Ric}_{00}/24+O(T^3)`$ and their product is
$`1+T^2\mathrm{Ric}_{00}/12+O(T^3)`$. This is not the Jacobian for changing a
pair integral to moving midpoint/direction variables; such a change needs its
own Jacobian.

Alternatively keep the source measure exactly and write $`y=\exp_x\xi`$.
Then $`d\mu_g(y)=[1+\mathrm{Ric}_x(\xi,\xi)/6+O(|\xi|^3)]d\xi`$ in a
source orthonormal frame. Replacing midpoint curvature by source curvature in
(G3) changes only the stated bounded-rapidity remainder. Put
$`s=g_x(\xi,\xi)`$, $`Z=\rho c_ds^{d/2}`$. The entire degree-at-most-two
**formal model**, before angular integration, is

```math
\begin{aligned}
\mathcal J_x(\xi)&=\left[\phi+\nabla_a\phi\,\xi^a
 +\tfrac12\nabla_a\nabla_b\phi\,\xi^a\xi^b
 +\tfrac16\phi\,\mathrm{Ric}_{ab}\xi^a\xi^b\right]K_d(Z)\\
&\quad-\phi\left[A_d\mathrm{Ric}_{ab}\xi^a\xi^b+B_dRs\right]ZK'_d(Z).
\end{aligned}\tag{G7}
```

There is no linear metric term in these coordinates, hence no degree-two
$`K''`$ term. In conformal coordinates there **is** such a term; this is a
coordinate difference, not permission to drop it in #76/#136. The source
factor $`d\mu_g(x)`$ stays outside (G7) without being frozen. Extending this
polynomial model over the whole tangent cone is algebraically well defined;
(G3) does not justify replacing the actual integral by that extension. That
replacement is proved separately in the continuation, (S1)–(S19).

## 4. All-dimensional signed responses of the model, not an actual bulk limit

Use an affine time cutoff $`0<\xi^0<\epsilon`$ in the orthonormal frame for
this calculation. It is **not** silently identified with the nonlinear temporal
cutoff in §2. Let F_d and J_k be the already derived signed slice and its
moments in dimension-kernels §4. They obey
$`J_0=a_d/\beta_d`$, $`J_1=0`$, $`J_2=-2/\beta_d`$ in every dimension.
Their even-dimensional tails are $`F_d(t)=O(t^{-5})`$ and their odd-dimensional
tails are exponential. These estimates precede, and justify, their Mellin
evaluations; no divergent cone integral is evaluated by absolute Fubini.

For one spatial component define
$`H_d(t)=S_{d-2}\int_0^t r^dK_d(c_d(t^2-r^2)^{d/2})dr/(d-1)`$.
Differentiating after $`s=t^2-r^2`$ gives $`H'_d(t)=tF_d(t)`$.
Since $`H_d(0)=0`$ and $`J_1=0`$,
$`H_d(t)=-\int_t^\infty uF_d(u)du`$. Thus H is integrable, with an
$`O(t^{-3})`$ even tail, and $`\int_0^\infty H_d=-J_2`$ by justified Fubini.
Angular odd/cross moments vanish. Scaling now proves the tensor responses

```math
\begin{aligned}
-\beta_d\rho^{1+2/d}\int_{0<\xi^0<\epsilon}
 \xi^a\xi^b K_d(Z)\,d\xi&\longrightarrow2\eta^{ab},\\
-\beta_d\rho^{1+2/d}\int_{0<\xi^0<\epsilon}
 \xi^a\xi^b ZK'_d(Z)\,d\xi&\longrightarrow
 -2(1+2/d)\eta^{ab}.
\end{aligned}\tag{G8}
```

The domain in each line is the future tangent cone. For the second line,
differentiate the scaled finite-cutoff integral with respect to rho.
The upper endpoint term tends to zero using the tails just proved. This
supplies its sign and its dimension factor. The point/constant terms cancel
using J_0; the first field term tends to zero using J_1. Their finite-cutoff
tails also vanish after the respective normalizations. Therefore the model
(G7), with the physical point coefficient, responds as

```math
\begin{aligned}
\tfrac12\nabla^2\phi &: \quad \Box_g\phi,\\
\tfrac16\mathrm{Ric}(\xi,\xi)\phi &: \quad R\phi/3,\\
-A_d\mathrm{Ric}(\xi,\xi)\phi ZK'_d &: \quad
 \frac{d+2}{12(d+1)}R\phi,\\
-B_dRs\phi ZK'_d &: \quad \frac{d}{12(d+1)}R\phi,\\
\mathrm{total}&=\Box_g\phi+R\phi/2.
\end{aligned}\tag{G9}
```

No coefficient was fixed by demanding the final line. This calculation consumes
the canonical kernel recurrence/normalization in #149's convention and works
also in 2D. The model calculation alone leaves **two** analytic tasks: the
actual-minus-model signed estimate on the full cone including its null edge,
and the cutoff-overlap term converting the affine calculation to the selected
geometric cutoff. The continuation proves them in (S1)–(S19), including the
nonzero 2D moving-diagonal contact. Neither follows from (G3)'s error.

## 5. Actual finite-density full/face/corner restoration on a finite atlas

Here is an exact short identity that does not presuppose either missing task.
In a temporal-flow joint chart with $`t=\tau`$ write $`x=(t,z)`$,
$`\ell(z)<t<f(z)`$, $`h(z)=f(z)-\ell(z)>0`$ on the physical spatial side.
The functions $`t-\ell(z)`$ and $`t-f(z)`$ have future timelike metric-dual
gradients after shrinking the chart. They strictly increase along future
causal curves there. There is a compactly supported smooth source weight
chi_i inside the chart and an arbitrary target field phi_j; j need not equal i.

Integrate over the physical spatial side h>0, auxiliary sources in the support
of chi_i, and **all ambient** future partners with temporal gap less than delta.
By §2 their intervals and endpoints stay in the larger chart. Set
$`a=\mathbf1_{t>\ell(z)}`$, $`b=\mathbf1_{t<f(z)}`$,
$`c=\mathbf1_{t_y<f(z_y)}`$. Monotonicity gives $`c\le b`$, and a true
source above the past face has every future partner above it. Thus, almost
everywhere on this domain,

```math
\begin{aligned}
\mathbf1_M(x)\mathbf1_M(y)&=abc,\\
abc&=ab-b(1-c)+(1-a)b(1-c),\\
P^{<}_{ij}&=P^{\mathrm{full}}_{ij}-F_{ij}+J_{ij},\\
S_{ij}&=S^{\mathrm{full}}_{ij}
       +\beta_d\rho^{1+2/d}F_{ij}-\beta_d\rho^{1+2/d}J_{ij}.
\end{aligned}\tag{G10}
```

All three pair terms integrate the **same**
$`\chi_i(x)\phi_j(y)K_d(\rho V(x,y))d\mu_g(x)d\mu_g(y)`$ against the
three displayed indicators. The point term belongs only to full. This proves
(G10) even with signed fields/kernel and moving causal boundaries. Equalities
on spacelike faces are null for the endpoint measures. Auxiliary restricted
volumes are never substituted for ambient ones. In a future-only chart take
a=1, so J=0; in a past-only or interior chart take b=c=1, so F=J=0. The past
face is not deleted: it remains the lower source boundary in the full term.

The whole face strip has thickness at most C delta: the mean-value estimate
and (G2) bound the change of t-f along a short causal curve. On J the source
is below the past face as well, so $`0<h(z)\le C\delta`$. Regularity of h
near the joint and the finite atlas put **all** J in a fixed regular joint
collar after decreasing delta once. The spatial restriction h>0 is essential:
without it the two auxiliary terms can include artificial face extensions
outside the physical spatial side, cancelling each other but not individually
being joint-collar terms. No small-collar-volume estimate is used to discard J.

Take finite smooth source weights summing to one near the closure of M, and
finite smooth target weights summing to one on the larger auxiliary target
tube. Source weights need not sum to one at artificial sources: cancellation
there holds separately for each i by (G10). On actual endpoints in M we have

```math
\begin{aligned}
\sum_{i,j}\chi_i(x)\phi_j(y)&=1,\qquad
\sum_{i,j}\chi_i(x)\phi_j(x)=1,\\
S&=\sum_{i,j}\left(S^{\mathrm{full}}_{ij}
       +\beta_d\rho^{1+2/d}F_{ij}-\beta_d\rho^{1+2/d}J_{ij}\right).
\end{aligned}\tag{G11}
```

For each source chart the target partition is evaluated at the actual ambient
partner; no matching-label rule is imposed. Smooth bump functions vanish before
artificial chart edges. Changes of chart preserve both endpoint volume
measures and the scalar ambient interval. Finite linearity therefore proves
(G11) at each density, including overlaps of positive measure. This is exact
cancellation/restoration of artificial chart restrictions **before** asymptotic
expansion, not proof that hypothetical chartwise limiting fluxes cancel.
That latter step uses the summable estimates mapped in §8 and proved in
(S10)–(S13), (S22) and (S27) of the continuation. Cross-component pairs are
always retained if present for the selected order.

## 6. Independent induced geometry and the compensating-flux ledger

In the joint chart put $`p=df`$, $`a=dh`$, $`k=|a|`$ in its spatial Euclidean
reference coordinates, $`w=\sqrt{|\det g|}`$, and define the future conormals
$`\alpha_+=dt-df`$, $`\alpha_-=dt-d\ell=\alpha_++dh`$. At the joint let

```math
\begin{aligned}
s_\pm&=g^{-1}(\alpha_\pm,\alpha_\pm),\qquad
 c=g^{-1}(\alpha_-,\alpha_+),\qquad D=c^2-s_-s_+>0,\\
 n_\pm&=g^{-1}\alpha_\pm/\sqrt{s_\pm},\qquad
 C=g(n_-,n_+)=c/\sqrt{s_-s_+}>1,\\
 dA_g&=\frac{w\sqrt D}{k}\,dA_{\{h=0\}},\qquad
 \coth\theta\,dA_g=\frac{wc}{k}\,dA_{\{h=0\}}.
\end{aligned}\tag{G12}
```

Proof of the measure formula: change coordinates to $`(t-f,h,y)`$, with y
coordinates on the spatial level. The normal inverse Gram determinant for
$`dt-df,dh`$ is $`-D`$. The block determinant identity between this Gram matrix
and the tangential metric gives the induced density w times its square root;
the spatial level change of variables contributes $`1/k`$. Equivalently,
compute the Gram determinant of minus g on the actual graph-lifted tangents.
On overlaps the chain rule multiplies it by the absolute coordinate Jacobian.
This proves equality on Borel overlaps, not just formal agreement of integrals.
In 2D the empty tangential determinant is one: this is counting measure on
**every** joint point. Compactness, spacelikeness and transversality give finite
area, positive angle and bounded integrable weight for each fixed geometry.

In particular there is a geometrically fixed candidate compensation, not an
arbitrary area measure. Put $`b_*=g^{-1}(\alpha_+,dh)`$, so $`c=s_++b_*`$.
The tangent corner model using the linear future gap
$`\alpha_+(\Delta)`$ has depth triangle $`\alpha_+(\Delta)^2/2`$.
Applying (G8) with both constant endpoint measures gives its normalized
negative-pair response $`w\chi\phi s_+/k`$. This calculation is the **model**
response; the actual comparison is the continuation's (S26)–(S29).
The difference from the independent joint coefficient is exactly the flux

```math
\begin{aligned}
\mathcal T_i&=-\int_{h=0}\frac{w\chi_i\phi\,b_*}{k}\,dA,\\
\int_{h=0}\frac{w\chi_i\phi s_+}{k}\,dA-\mathcal T_i
 &=\int_{J\cap U_i}\chi_i\phi\coth\theta\,dA_g.
\end{aligned}\tag{G13}
```

For the spatial vector $`X^r=w\chi_i\phi g^{r\nu}(\alpha_+)_\nu`$,
with all factors restricted to the future graph, the divergence theorem on
h>0 gives $`\int\partial_rX^r dz=\mathcal T_i`$, since its outward normal
at h=0 is $`-dh/k`$. Any artificial edge has compactly supported weight; if
one uses sharp chart cuts instead, its extra boundary flux must be included
on both neighboring pieces. No metric or trace derivative in this divergence
is declared zero. Formula (G13) specifies the compensation a face/corner
producer must account for; the identity by itself does not prove that the
actual face integral has this response or exclude additional contributions.
The continuation derives its complete signed face response in (S20)–(S25).

Independently, Green's identity on the piecewise smooth region gives **both**
oriented spacetime-face fluxes:

```math
\begin{aligned}
\int_M\chi\Box_g\phi\,d\mu_g
 &=-\int_M g^{-1}(d\chi,d\phi)\,d\mu_g\\
 &\quad+\int_{\Sigma_+}\chi n_+(\phi)\,d\Sigma_g
       -\int_{\Sigma_-}\chi n_-(\phi)\,d\Sigma_g.
\end{aligned}\tag{G14}
```

The codimension-two set has zero hypersurface measure in this divergence
identity; it need not have zero action contribution. If a face response is
written using $`\int_{\Sigma_+}(\phi n_+\chi-\chi n_+\phi)d\Sigma_g`$,
that entire antisymmetric flux must also remain until partition summation.
For unit fields derivative terms vanish; the geometric flux (G13) generally
does **not**. In the conformal graph coordinates of #76/#136,
$`w b_*=\Omega^{d-2}p\cdot a`$, recovering precisely their nonzero
compensation, not just conformal angle invariance.

## 7. Exact fixed-cutoff and overlap interface for #151

Define q(x,y)=tau(y)-tau(x). Let $`P^<_q`$ retain all causal pairs with
$`q<\delta`$, and $`P^\ge_q`$ all with $`q\ge\delta`$. Allocate the physical
point term once, to $`S_q`$, and put
$`L_q=-\beta_d\rho^{1+2/d}P^\ge_q`$. Then $`A=S_q+L_q`$ exactly.
Equality belongs to long even without a zero-measure-level argument.

A second cutoff (including the pilots' $`v=t+r`$, an affine tangent cutoff,
or a different temporal function) has short indicator e'. With
$`e=\mathbf1_{q<\delta}`$, define the actual signed overlap

```math
\begin{aligned}
\mathcal O_{e,e'}(\rho)
 &=-\beta_d\rho^{1+2/d}\int_{M\times M}\mathbf1_{x\preceq y}
 (e-e')\chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
S_e-S_{e'}&=\mathcal O_{e,e'},\qquad
L_e-L_{e'}=-\mathcal O_{e,e'},\\
\mathcal O_{e,e'}+\mathcal O_{e',e''}&=\mathcal O_{e,e''}.
\end{aligned}\tag{G15}
```

This proof is subtraction of finite integrals. The overlap need not vanish:
a positive lower bound on coordinate displacement is **not** a positive lower
bound on interval volume. The same formula on auxiliary domains is needed when
comparing (G10) to tangent models. All such domains, weights and ambient versus
restricted phases must be specified; their artificial parts cancel by (G10).
For the sufficiently small local temporal/radial-normal/affine cutoffs used
in the short proof, the continuation's (S17)–(S18) now proves that the actual
signed shell response vanishes. The exact opposite long allocation in (G15)
still applies. This gives no estimate on a macroscopic or focusing overlap.

The consumer payload to #151 is therefore: geometry and selected order;
actual restricted phase and both measures; tau, delta, finite source/target
partitions; full ordered short/long domains; point allocation; and (G15) for
any differing cutoff. #151 owns long pushforwards including all cut/conjugate
and multiple-branch neighborhoods, not a stipulated zero long limit. No global
phase smoothness follows from the local lemma. The #133 seam and accepted
#139 focusing estimates remain required nonlocal regressions. Probability and
final deterministic/expected assembly stay with #151/#81/#86.

## 8. Producer acceptance map and native residual ownership

The [continuation](general-metric-short-remainders.md) supplies these written
analytic outputs on the unchanged smooth core for each physical dimension.
They are derived conclusions, not new geometric admissibility fields.

1. **GM-S1 — established in (S1)–(S19).** The actual thin interval is contained
   in a uniformly bounded null-rescaled tube. Gauss's lemma removes the
   apparent metric singularities; smooth cone-volume dependence and transverse
   reflection derive the positive smooth ratio phase, including the null edge.
   The inverse and every mixed derivative needed for the signed comparison
   follow from this geometry. The k=0 remainder includes the full moving
   diagonal and the nonzero 2D contact. The actual cutoff shell is also estimated.
2. **GM-S2 — established in (S20)–(S25).** An implicit source-dependent gap
   flattens the entire actual face strip. The k=1 signed comparison retains
   all source/target densities, moving-source and diagonal terms. Its complete
   jet evaluates to the antisymmetric face flux minus exactly (G13). Both
   oriented bulk face fluxes (G14) remain. Bounds are uniform also on the
   non-joint part of the collar, then summable over the finite atlas.
3. **GM-S3 — established in (S26)–(S29).** A coupled depth/height root flattens
   both actual moving boundaries. Its Jacobian includes the additional
   source-time derivative absent in the conformal coordinate pilots. The k=2
   signed comparison keeps the oriented strip and restores the actual face
   compensation to the independently induced (G12), including 2D counting.

The common signed **density** estimate used in all three comparisons is

```math
\begin{aligned}
D_\lambda(w)&=\sum_{j=0}^{\lfloor d/2\rfloor}b_j(\lambda)w^j
                   +w^{d/2}E_\lambda(w),\\
E_\lambda(w)&\longrightarrow0,\qquad
 |E_\lambda(w)|+\sum_j|b_j(\lambda)|\le G(\lambda),\quad
 \int G(\lambda)\,d\lambda<\infty.
\end{aligned}\tag{G16}
```

Here D is the **actual-minus-entire-model** density, lambda lists the remaining
geometric parameters, and common bounded phase support and integrable tails
are required. The existing signed moments then prove the normalized error
vanishes by rescaling and dominated convergence. If the proof instead produces
a cumulative primitive, its derivative or integration-by-parts boundary terms
must be controlled too; a primitive bound must not be substituted for (G16)
as if it were a density. The continuation derives the actual densities and
proves (G16) in (S10)–(S13), with explicit parity-dependent remainders and the
complete contact ledger (S11). The critical fractional powers/logarithms are
retained in the model, not hidden in an absolutely bounded Taylor error.
No universal positive Taylor inverse or C3 regularity theorem is asserted.

Native residual ownership: #150 supplies the written **short** producers;
#149 retains its independent dimension-indexed flat analysis and scope;
#151 retains the general nonlocal long producer, #81 the eventual matched
full-action/expectation assembly, and #86 justified formal ports and independent
human review. No unfinished #149/#151 theorem is an input to the short proof.
No issue is automatically closed by this continuation. There is no claim of
compiled or independently reviewed GM-S1–GM-S3, and no transfer of an unproved
short analytic premise to another owner.

## 9. Regressions and verification boundary

`general_metric_short.py`, `test_general_metric_short.py` and
`test_general_metric_short_remainders.py` supply finite diagnostics, not a
numerical proof of general convergence:

- dimension-indexed rest-diamond moments, separate cone/density corrections,
  both endpoint factors, signed model responses and their negative controls;
- actual rest-interval quadrature in flat space, the completed polynomial and
  nonpolynomial metrics, converted using **proper** duration, not conformal
  coordinate duration; nonzero directional Ricci and scalar controls;
- a nonconformally-flat ultrastatic sphere-circle rest interval, independent
  of the conformal phase identity;
- intrinsic Gram/coarea/angle and nonzero compensating flux with non-diagonal
  metric, variable slopes and 2D counting; complete indicator restoration;
- all ordered partition terms and finite-density cutoff-overlap restoration,
  including long nearly-null partners whose volume tends to zero;
- the exact sphere-circle null-rescaled metric and actual nearly-null interval
  distance integral, not its curvature polynomial; all three contact formulas,
  parity remainder bounds in 2D–9D and the indispensable 2D contact;
- actual moving source roots in a variable-lapse chart and the corner Jacobian
  including its source-depth derivative; the general metric/field flux algebra.

The written arguments above have no new compiled Lean counterpart. Tests are
finite symbolic/numerical diagnostics, not estimates or independent human
mathematical review. No Lean validation input changed, so no new integrated
Lean audit is claimed. #86 should port these lemmas only when a bounded
consumer justifies it. The continuation is a written general G-SS **short**
proof, not a general full-action limit. Rates, shrinking-cutoff interchanges,
noncompact tails, degenerating angles and sample-wise convergence are not
supplied.

```sh
.venv/bin/python -m unittest -v test_general_metric_short test_general_metric_short_remainders
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
