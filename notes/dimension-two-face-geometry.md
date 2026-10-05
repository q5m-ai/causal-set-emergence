# Dimension-indexed two-face geometry and intrinsic targets (#92)

**Delivery:** a conventional finite-geometry proof and a shared contract for
[#78](https://github.com/q5m-ai/causal-set-emergence/issues/78),
[#79](https://github.com/q5m-ai/causal-set-emergence/issues/79), and
[#80](https://github.com/q5m-ai/causal-set-emergence/issues/80).
The first new global pilot is **`SmoothPilot3`**, in physical dimension three,
with smooth face germs. The all-dimension C³ candidate is retained separately.
No higher-dimensional action limit, actual overlap jet, or new Poisson bridge
is proved by this geometry package. The separately merged #77 now supplies
the dimension-indexed finite-density expectation identity. The geometric arguments below are **written, not new Lean theorems
or independently human-reviewed results**. Python/SymPy checks are regressions,
not proofs for arbitrary inputs. Existing Lean results are cited explicitly.

**Follow-on port status:** [#115's Lean geometry package](../formal/PILOT3_GEOMETRY.md)
now preserves the exact smooth 3D contract and proves the whole region/strata,
intrinsic canonical joint area and Borel overlaps, finite-atlas gluing, signed
collar coarea, right-sided density regularity and spatial divergence, alongside
actual signed overlap, compact perturbation tubes and the existing Poisson
specialization. It includes admissible disconnected/annular controls, regular
2D endpoint counting and exact compatibility for every original 4D C³ member;
[its integration ledger](../formal/PILOT3_INTEGRATION.md) states the precise
scope. The historical #92 delivery and written all-dimensional statements
below are not promoted wholesale to new Lean theorems. The later
[#80 assembly](../formal/PILOT3_LIMIT.md), using #125/#126's actual formal
producers, now proves the deterministic and expected limits for exactly this
smooth 3D pilot; it does not generalize the all-dimensional candidate.

Read with [the dimensional kernel contracts](dimension-kernels.md),
[the checked ambient transport](../formal/DIMENSION_INTERVALS.md), and
[the original 4D geometry](../formal/JOINT_GEOMETRY.md). No existing Lean
admissibility, action, target, or theorem is changed. This is a partial research
package under [#24](https://github.com/q5m-ai/causal-set-emergence/issues/24).

## 1. Dimension, regularity and independent region data

Fix an integer physical dimension $`d\ge2`$. Put $`n=d-1`$ and $`m=d-2`$;
spacetime is $`\mathbb R\times\mathbb R^n`$ with canonical product Lebesgue
measure and signature $`g((t,x),(s,y))=ts-x\cdot y`$. Thus the existing Lean
type is `DimensionSpacetime (d - 1)`, **not** `DimensionSpacetime d`.

For raw functions $`h,f:\mathbb R^n\to\mathbb R`$, define

```math
\begin{aligned}
H&=\max(0,h),&\Omega&=\{h>0\},&K&=\overline\Omega,&S&=K\cap\{h=0\},\\
L&=f-H,&U&=f,&
M_d(h,f)&=\{(t,x):f(x)-h(x)\lt t\lt f(x)\}.
\end{aligned}
\tag{G1}
```

**`CandidateTwoFace(d,r;h,f)`**, for an integer $`r\ge3`$ or $`r=\infty`$,
means exactly:

1. The positive region is bounded.
2. There are constants $`\kappa,\eta\ge0`$ with $`\kappa+\eta\lt1`$ such
   that H is globally Euclidean $`\kappa`$-Lipschitz and f is globally
   Euclidean $`\eta`$-Lipschitz.
3. At every point of K, h and f have ambient local C-r regularity (each agrees
   with a C-r function on an open neighborhood). The height is zero on the
   frontier of the positive region, and $`dh_x\ne0`$ at every zero in K.

The local formulations patch on the union of their neighborhoods. No condition
is imposed on the differential at positive height. Raw h may be discontinuous
far outside K; it is **H**, not raw h or L, that has the global height bound.
The empty region is allowed. We do not select one connected component or
assume that the joint is connected. Exterior zeros outside K are irrelevant.
There is no density, jet, integral, area, cancellation, expectation identity,
or limit premise in this definition.

The named downstream pilot is

```text
SmoothPilot3(h,f) := CandidateTwoFace(3,infinity;h,f).
DimensionTwoFaceDeterministicGoal(d,r) := D(d,r) of section 5.
DimensionTwoFaceExpectedGoal(d,r)      := E(d,r) of section 5.
Pilot3DeterministicGoal               := D(3,infinity).
Pilot3ExpectedGoal                    := E(3,infinity).
```

These are mathematical contract names, **not compiled Lean declarations**.
The stronger smooth pilot avoids promising that C³ faces suffice for a new
critical-order jet. It does not strengthen the existing 4D C³ class. The
finite geometry below already works with C¹ germs; we retain C³ in the
candidate to match that existing class exactly. Smoothness of raw germs does
not assert smoothness of the clipped height across S.

Define the closed faces, lift, and joint before any action:

```math
\begin{aligned}
F_f(x)&=(f(x),x),\\
\Sigma_-&=\{(f(x)-h(x),x):x\in K\},&
\Sigma_+&=F_f(K),&J&=F_f(S).
\end{aligned}
\tag{G2}
```

## 2. Region theorem: boundedness, measurability and all strata

**Theorem G.** For every candidate in §1, M is open, bounded, measurable,
finite-volume and ambient-causally-convex, including closed null intervals.
The faces and joint are compact, and

```math
\begin{aligned}
\overline M&=\{(t,x):x\in K,\ L(x)\le t\le U(x)\},\\
\partial M&=\Sigma_-\cup\Sigma_+,&
\Sigma_-\cap\Sigma_+&=J,&
|M|&=\int_\Omega h(x)\,dx.
\end{aligned}
\tag{G3}
```

**Proof.** Positivity of H and of h are equivalent, so continuity of H makes
the positive region open; its bounded closure K is compact. Continuity of h
near K gives nonnegative height on K and $`S=\partial\Omega`$. Conversely a
zero in K is not interior to the positive set, hence is on its frontier.
The implicit function theorem at every point of S, applied on an ambient
regular neighborhood, puts K locally on the nonnegative side of a C-r regular
hypersurface. This establishes the manifold-with-boundary description; it
does not require a noncritical interior. When K is empty all statements have
their empty-set meanings.

Pointwise, the time fibre in (G1) is empty when $`h\le0`$ and otherwise equals
$`(L(x),U(x))`$. Consequently M is the intersection of two strict continuous
envelope inequalities, and is open. Its spatial projection is the positive
region. The continuous envelopes are bounded on compact K, so M lies in a
compact time-interval/ball product. It is Borel, of finite volume. Vertical
Fubini gives the last equality in (G3).

The envelope constants are $`\lambda_-=\kappa+\eta\lt1`$ and
$`\lambda_+=\eta\lt1`$. If $`p\preceq z\preceq q`$ and p,q belong to M,
then $`|x_z-x_p|\le t_z-t_p`$ and $`|x_q-x_z|\le t_q-t_z`$. Therefore

```math
\begin{aligned}
t_z-L(x_z)&\ge t_p-L(x_p)+(1-\lambda_-)(t_z-t_p)>0,\\
U(x_z)-t_z&\ge U(x_q)-t_q+(1-\lambda_+)(t_q-t_z)>0.
\end{aligned}
\tag{G4}
```

Thus the **whole closed ambient causal interval** lies in M. No chronology
restriction, convex-hull substitution, or intrinsic-causality assumption is
used. This argument also covers endpoints in different components whenever
they are causally related; it is not a componentwise truncation of the action.

Every limit of points in M lies in the closed set on the right of (G3).
Conversely, above a positive spatial point the closed fibre is approached
vertically from its open fibre. Above a point of S the fibre is a singleton;
approach it by positive spatial points with their midpoint times. This proves
the closure identity. Subtracting the open region leaves precisely the two
face graphs, whose equality at a common spatial point is equivalent to zero
height. Graph projection is an inverse to each embedding. Compactness and
(G2) prove all remaining assertions, with no lateral wall, omitted inner
boundary, or exterior zero sheet. Each face is a compact C-r spacelike
hypersurface-with-boundary and its boundary is exactly J: inside the positive
region differentiate the envelope bounds to obtain

```math
\begin{aligned}
|\nabla h|\le\kappa,\qquad |\nabla f|\le\eta,\qquad
|\nabla(f-h)|\le\kappa+\eta\lt1.
\end{aligned}
\tag{G5}
```

Continuity of the actual differentials extends these bounds to K. This does
not differentiate the nonsmooth clipped H at S. Nonzero dh makes the two
face conormals independent at J. There are no other boundary strata. ∎

## 3. Metric, normals and an intrinsic finite measure

At $`x\in S`$ write $`a=\nabla h(x)`$, $`k=|a|>0`$, $`\nu=a/k`$,
$`q=\nabla f(x)`$, $`p=q-a`$, and $`b=q-(q\cdot\nu)\nu`$.
The spatial tangent space is $`T_xS=\ker dh_x=\nu^\perp`$.
The actual derivative of the lift takes $`v`$ to $`(q\cdot v,v)`$.
Define the positive joint metric independently of any action by

```math
\begin{aligned}
\gamma_x(v,w)&=-g(DF_f(v),DF_f(w))\\
 &=v\cdot w-(q\cdot v)(q\cdot w).
\end{aligned}
\tag{G6}
```

For nonzero v, Cauchy–Schwarz and (G5) give
$`\gamma_x(v,v)\ge(1-\eta^2)|v|^2>0`$. In dimension two the tangent space is
zero dimensional; positive definiteness is vacuous and its empty determinant
is one. The **future** unit normals to the future and past faces are

```math
\begin{aligned}
n_+=\frac{(1,q)}{\sqrt{1-|q|^2}},\qquad
n_-=\frac{(1,p)}{\sqrt{1-|p|^2}}.
\end{aligned}
\tag{G7}
```

Their time components are positive, their Minkowski squares are one, and
they are orthogonal to the respective graph tangents. In particular both
are orthogonal to the joint; the past normal is inward, not past-directed.
Put

```math
\begin{aligned}
A&=1-|q|^2,&B&=1-|p|^2,&N&=1-q\cdot p,\\
C&=g(n_+,n_-)=\frac{N}{\sqrt{AB}},&
j_L&=\sqrt{1-|b|^2}.
\end{aligned}
\tag{G8}
```

Both A,B and N are positive. Direct expansion, using $`p=q-a`$, gives

```math
\begin{aligned}
N^2-AB=|a|^2(1-|q|^2)+(a\cdot q)^2=k^2j_L^2>0.
\end{aligned}
\tag{G9}
```

Hence $`C>1`$, not just $`C^2>1`$. Define the positive-normal angle and weight:

```math
\begin{aligned}
\theta=\log\bigl(C+\sqrt{C^2-1}\bigr)>0,\qquad
W=\coth\theta=\frac{C}{\sqrt{C^2-1}}.
\end{aligned}
\tag{G10}
```

### Actual charts and their compatibility

Let $`X:V\subset\mathbb R^m\to S`$ be any regular injective local chart
constructed by the implicit function theorem. Set $`E=DX`$, viewed as a matrix
with m independent columns, and $`\Psi=F_f\circ X`$. The induced Gram matrix
of the **actual derivative** is

```math
\begin{aligned}
G_\Psi&=E^{\mathsf T}E-(E^{\mathsf T}q)(E^{\mathsf T}q)^{\mathsf T},\\
\det G_\Psi&=\det(E^{\mathsf T}E)(1-|b|^2).
\end{aligned}
\tag{G11}
```

For $`m>0`$, the matrix determinant lemma proves this because
$`E(E^{\mathsf T}E)^{-1}E^{\mathsf T}`$ is orthogonal projection onto
$`T_xS`$. For $`m=0`$, the two determinants are empty determinants and b is
zero, so (G11) is still valid. This proof is independent of a spatial cross
product and therefore does not assume three spatial dimensions.

Define intrinsic area in each chart by the density $`\sqrt{\det G_\Psi}`$
against m-dimensional Lebesgue measure. If $`X_2=X_1\circ\varphi`$ on an
overlap, the chain rule gives

```math
\begin{aligned}
G_{\Psi_2}&=D\varphi^{\mathsf T}(G_{\Psi_1}\circ\varphi)D\varphi,\\
\sqrt{\det G_{\Psi_2}}&=|\det D\varphi|\sqrt{\det(G_{\Psi_1}\circ\varphi)}.
\end{aligned}
\tag{G12}
```

The ordinary change-of-variables theorem proves equality of the two measures
on **every Borel subset of the overlap**, including overlaps of positive
measure and orientation-reversing transitions. A countable atlas thus glues
to one Borel measure on J; equivalently, use disjoint Borel differences of a
finite covering by precompact chart patches. The equality on overlaps makes
that construction independent of chart order, refinement and chosen atlas.
For zero-dimensional charts the domain is a singleton of volume one; gluing
assigns mass **one to each point**, not a half and not ambient Lebesgue mass.

Let $`dA_S`$ be Euclidean hypersurface area on S, normalized to ordinary
Lebesgue measure on an m-plane. The Euclidean C¹ chart area formula and
(G11) prove the coordinate identity, including equality of measures:

```math
\begin{aligned}
dA_J&=(F_f)_*(j_L\,dA_S),\\
\mathcal J_d(h,f)&:=\int_J W\,dA_J
 =\int_S Wj_L\,dA_S\\
 &=\int_S\frac{1-|q|^2+q\cdot a}{|a|}\,dA_S.
\end{aligned}
\tag{G13}
```

The last equality follows from (G9) and the positive square-root branches;
it is an **evaluation of an independently defined geometric target**, not its
identification with a coefficient of an action. The metric in (G6), not
Euclidean spacetime distance, defines area. That wrong metric would give
$`\sqrt{1+|b|^2}`$ instead of $`j_L`$.

### Nondegeneracy, finite area and absolute integrability

Compact S has a finite cover by smaller regular chart patches with closures
inside their parameter domains. On each closure DX is bounded, so its
Euclidean Gram density is bounded on a finite-volume parameter box. The area
formula then proves finite Euclidean area, before any evaluation of (G13).
In dimension two, regular zeroes are isolated; a compact discrete manifold
has a finite subcover of singleton charts, hence finitely many points. This
also proves finite counting measure directly.

Since $`0<\sqrt{1-\eta^2}\le j_L\le1`$, the induced area is finite and
nondegenerate. On nonempty compact S, continuity and strictness give positive
minima of k and $`C-1`$. The angle and W are continuous there, W is bounded,
and consequently absolutely integrable with respect to the finite induced
area. On empty S the measure and target are zero; no positive-minimum claim
is needed. These bounds are for each **fixed region**, not uniform bounds for
families approaching zero angle or null faces. All components and holes are
covered by the same proof.

## 4. Ambient transport, the regulated coefficient and exact 4D recovery

For an affine future-preserving Lorentz map $`T(z)=\Lambda z+c`$, define
area on the transformed joint from the actual embedding $`T\circ\Psi`$ by
(G6), not by stipulating a pushforward. Its derivative is $`\Lambda D\Psi`$,
so each Gram entry is unchanged. Thus the chart construction proves
$`dA_{TJ}=T_*dA_J`$. The transported normals $`\Lambda n_\pm`$ remain future
unit normals and preserve C, theta and W. It follows that

```math
\begin{aligned}
\mathcal J_d(TJ,T\Sigma_-,T\Sigma_+)=\mathcal J_d(J,\Sigma_-,\Sigma_+).
\end{aligned}
\tag{G14}
```

Translations, boosts, and spatial orientation reversal are included. A
transported presentation need not satisfy the original slope budget in the
new coordinates; this is a theorem about the embedded faces, **not** an
assertion that the coordinate class is Lorentz invariant.

For dilation by $`s>0`$, the tangent Gram matrix gains $`s^2`$, its determinant
$`s^{2m}`$, and area $`s^m`$. The same unit normals are normal to the dilated
tangent planes; the angle is unchanged. Hence

```math
\begin{aligned}
\mathcal J_d(sJ,s\Sigma_-,s\Sigma_+)=s^{d-2}\mathcal J_d(J,\Sigma_-,\Sigma_+).
\end{aligned}
\tag{G15}
```

This includes exponent zero for counting measure. These geometric laws match
#91's **separately checked** `DimensionPoincareEquiv.weightedAction_image` and
`dimensionWeightedAction_dilate`: the action's density changes to
$`\rho s^d`$ and its prefactor to $`s^{d-2}`$. Geometry does not assume an
action transport or limit in order to prove (G14)–(G15).

At any joint point a Lorentz frame can take the future normal to the time
axis. In its orthogonal spacelike hyperplane choose an orthonormal basis for
the common joint tangent plane. The other future unit normal has a component
$`\cosh\theta`$ along time and a component of magnitude $`\sinh\theta`$ along
the remaining spatial normal; reversing that spatial normal if needed makes
the inward wedge slope $`\kappa_0=\tanh\theta\in(0,1)`$. The tangential
basis has induced Gram matrix I, so #88's **fixed-regulator** theorem
`dimensionWeighted_wedge_coth_limit`, at tangential index $`m=d-2`$, has local
coefficient W per unit induced area. Arbitrary tangent coordinates multiply
it by $`\sqrt{\det G_\Psi}`$ by (G12). #91 transports the **whole regulated
observable** with its first-endpoint weight and all partners. This supplies
the invariant meaning of that local coefficient; it does not replace curved
faces by tangent wedges, discard artificial complements, or remove a regulator.
Those remain #78/#79 obligations.

**Exact 4D compatibility, not only a spherical check.** For $`d=4,r=3`$,
the coordinate identification from `DimensionSpatial 3` to `JointSpace` and
the time-first `dimensionSpacetimeCoordinates 3` sends (G1)–(G2) to the
unchanged `twoFaceRegion`, `twoFacePast`, `twoFaceFuture`, and `twoFaceJoint`.
The class is equivalent to `AdmissibleTwoFace`: its height fields are precisely
`AdmissibleGraphCap`; the common budget gives the standalone strict height
bound, and the old local smoothness fields are exactly the germs in §1.
There is no smooth-pilot requirement in this equivalence.

On the spatial joint, normalized Euclidean two-area is exactly the old
`graphSurfaceMeasure`, namely mathlib's unnormalized Hausdorff measure
multiplied by pi/4. Formula (G11) gives the old `twoFaceAreaDensity`; (G7)–(G10)
give the old normals and `twoFaceWeight`. Consequently (G13) gives equality
of the entire projected measure, its spacetime pushforward, and the integral
with `twoFaceProjectedArea`, `twoFaceJointArea`, and `twoFaceBoundaryIntegral`.
The checked `TwoFaceCharts` area theorem supplies that same intrinsic chart
interpretation. The checked `dimensionWeightedAction_four_eq_continuumMean`
supplies **complete** action compatibility, not just a plane-kernel equality.
This paragraph is a written identification using those checked interfaces,
not an additional Lean equivalence theorem.

For a planar future face in **any** supported dimension, q and b vanish,
$`j_L=1`$, and $`W=1/|\nabla h|`$. Thus projected area is exactly spatial
hypersurface area and the target is its reciprocal-gradient integral. In 4D
this recovers the old planar measure and target for **every** old admissible
height with its original hypotheses.

## 5. The shared action and two independent goal propositions

Use exactly the constants, polynomial and layer coefficients of
[the kernel note, §§1–2](dimension-kernels.md#2-actual-action-coefficients-and-finite-density-expectation).
With $`V_{xy}=c_d\sigma_{xy}^{d/2}`$ on future-related pairs, set

```math
\begin{aligned}
\mathcal A_{\rho,d}(M)&=\rho^{2/d}\left[
 a_d|M|-\beta_d\rho\int_M dx\int_{M\cap J^+(x)}dy\,
 K_d(\rho V_{xy})\right],\qquad \rho>0.
\end{aligned}
\tag{G16}
```

In existing Lean terms this is, without redefining that functional:

```text
dimensionWeightedAction (d - 1)
  (dimensionPointCoefficient d) (dimensionPairCoefficient d)
  (dimensionIntervalCoefficient d) rho (M_d(h,f)) (fun _ => 1)
```

Theorem G gives boundedness and measurability. The continuous pair kernel on
a compact product dominates its causal restriction, so all signed integrals
here are absolutely integrable at fixed density. The causal-convexity proof
discharges #91's `DimensionCausallyConvex` hypothesis. Thus its actual
restricted order-interval volume equals the ambient proper-time expression,
including null and coincident endpoints. This is a written instantiation of
#91, not an assumption about interval volume.

Define the probability object **independently**. On finite subsets of M, use
the pushforward of the Poisson configuration mixture

```math
\begin{aligned}
\mathbb P_{\rho,M}=e^{-\rho|M|}\sum_{N=0}^\infty
 \frac{\rho^N}{N!}(\pi_N)_*((dx|_M)^{\otimes N}).
\end{aligned}
\tag{G17}
```

where $`\pi_N`$ forgets labels. The N=0 term is the unit empty configuration;
the total mass is one by the exponential series. This definition also covers
zero-volume M without division by its volume. Lebesgue atomlessness makes
repeated points null. On a finite subset use the **closed causal order**;
count ordered distinct related pairs with exactly k elements in their
exclusive interval as $`N_{k+1}`$. Define

```math
\begin{aligned}
A^{\mathrm{disc}}_{\rho,d}(C)&=\rho^{-(d-2)/d}
 \left[a_d|C|-\beta_d\sum_{k=0}^{\lfloor d/2\rfloor+1}
 C_{k+1}^{(d)}N_{k+1}(C)\right],\\
\mathcal E_{\rho,d}(M)&=\int A^{\mathrm{disc}}_{\rho,d}\,d\mathbb P_{\rho,M}.
\end{aligned}
\tag{G18}
```

The coefficients in (G18) are layer coefficients, not polynomial coefficients
with factorial denominators. Measurable order relations give measurable
counts; their bound by the square of the Poisson cardinality gives absolute
integrability. This construction is not a definition of expectation as
(G16). The dimension-indexed Lean instantiation and exact identity
$`\mathcal E_{\rho,d}=\mathcal A_{\rho,d}`$ are now proved separately in
[#77's expectation bridge](../formal/DIMENSION_EXPECTATION.md), not by #92.
Its `DimensionBoundedCausalRegion.expectedAction_eq` applies to these regions
via the written Theorem G; a compiled dimension-indexed region constructor
remains outstanding. The earlier conventional Mecke argument is recorded in
kernel contract F; no new expectation proof is supplied by this package.

The independent propositions, at fixed geometry, are

```math
\begin{aligned}
D(d,r):\quad&\forall(h,f)\in\mathrm{CandidateTwoFace}(d,r),\quad
 \lim_{\rho\to\infty}\mathcal A_{\rho,d}(M_d(h,f))=\mathcal J_d(h,f),\\
E(d,r):\quad&\forall(h,f)\in\mathrm{CandidateTwoFace}(d,r),\quad
 \lim_{\rho\to\infty}\mathcal E_{\rho,d}(M_d(h,f))=\mathcal J_d(h,f).
\end{aligned}
\tag{G19}
```

Neither is a premise of admissibility. The 3D pilot asks for D(3,infinity)
first, then E(3,infinity) via the separate exact identity. Both now have
[separate unconditional Lean proofs](../formal/PILOT3_LIMIT.md) on the unchanged
smooth pilot, after the actual #125/#126 producer proofs.
D(4,3) and E(4,3) have the existing checked proofs under the exact identification
in §4; no general-dimensional consequence follows. All other global claims
stay open under #24, even though their finite geometry is proved in writing.

| Consumer | Frozen input from this package | Separate obligation |
|---|---|---|
| #78 | `SmoothPilot3`, actual M, product volume and action (G16) | Actual fixed-cutoff overlap disintegration and sufficient averaged jet, or a precise obstruction |
| #79 | The **same** pilot/action and independent target (G13) | Short-overlap estimates, signed coefficient and target identification; a planar base theorem if that route is used |
| #77 (completed) | Bounded measurable causally convex M from Theorem G | The separate checked identity is available; #115 supplies the smooth 3D and unchanged 4D constructors, not a general-dimensional geometry class |
| #80 | D(3,infinity), then E(3,infinity) | Completed separately in `Pilot3Limit`: compatible actual signed pieces at one fixed cutoff, then #77 transfer; not all dimensions |

In particular the source overlap is always the actual
$`V_M(z)=\int 1_M(x)1_M(x+z)\,dx`$, with every endpoint component retained.
No overlap function, cutoff-dependent region, or target renormalization is
substituted into this interface.

## 6. Nonempty curved examples and all-component regressions

**Smooth ball/sine family, every dimension.** Take

```math
\begin{aligned}
h(x)&=a(1-|x|^2),\qquad f(x)=\epsilon\sin x_1,\\
 a&>0,\qquad \epsilon\ge0,\qquad 2a+\epsilon\lt1.
\end{aligned}
\tag{G20}
```

Inside the unit ball $`|\nabla h|\le2a`$; the positive part is zero outside.
Splitting a line segment at its ball intersections proves the global
$`2a`$-Lipschitz bound. The future graph is globally epsilon-Lipschitz.
The germs are smooth, S is the entire unit sphere, and $`|\nabla h|=2a`$
there. The origin is a retained **positive-height critical point**. The time
midpoint at the origin lies in M, proving nonemptiness. For epsilon positive,
the second derivative of f is nonzero at interior points with $`x_1\ne0`$,
so the future face is genuinely curved, not merely a tilted plane. This also
holds for the one-dimensional spatial interval in physical dimension two.
Setting $`a=1/4,\epsilon=1/8`$ gives a concrete `SmoothPilot3`.

For that family's 3D circular joint, parameterize x by
$`(\cos u,\sin u)`$. The induced line element is
$`\sqrt{1-\epsilon^2\cos^2(\cos u)\sin^2u}\,du`$.
The term $`q\cdot a`$ in (G13) integrates to zero by reflection, yielding
the independent exact calibration

```math
\begin{aligned}
\mathcal J_3&=\frac{\pi}{a}
 \left[1-\frac{\epsilon^2}{2}\bigl(1+J_0(2)\bigr)\right],\\
J_0(2)&=\frac1{2\pi}\int_0^{2\pi}\cos(2\cos u)\,du.
\end{aligned}
\tag{G21}
```

Here the last equality can serve as the definition of the Bessel value; no
action asymptotic is used. Direct normal/Gram quadrature checks (G21).

**Disconnected curved 3D regions.** Put the two unit-ball centers at
$`c_\pm=(\pm3,0)`$, set
$`h(x)=a\max(1-|x-c_-|^2,1-|x-c_+|^2)`$, and take
$`f(x)=\epsilon\sin x_2`$ with the same strict budget. The positive part is
the maximum of two globally 2a-Lipschitz positive parts; near each closed
ball the corresponding quadratic strictly wins, giving smooth raw germs.
Both closed balls, both critical centers and both circular joints belong to
the class. Translation along the first coordinate leaves f unchanged, so
the target is twice (G21), with neither component selected as preferred.
The regressions integrate the normals and Gram density on both components.

**Holes, disconnected joints, and irrelevant exterior zeros.** In each spatial
dimension take, for $`|x|<2`$,

```math
\begin{aligned}
h(x)&=a(|x|^2-1/4)(1-|x|^2),\qquad f(x)=\epsilon\sin x_1,\\
a&=1/8,\qquad\epsilon=1/8.
\end{aligned}
\tag{G22}
```

and set raw h to zero when $`|x|\ge2`$. The positive region is
$`1/2<|x|<1`$ and K its closure. On that annulus,
$`|\nabla h|=2a|x|\,|5/4-2|x|^2|\le3a/2`$.
Splitting line segments at the two spheres proves the same global bound for
H; thus $`3a/2+\epsilon<1`$. Raw h is smooth on a neighborhood of K; its
exterior discontinuity is permitted and its exterior zeros do not meet K.
The gradients at radii 1/2 and 1 are nonzero. The critical sphere of radius
$`\sqrt{5/8}`$ has positive height and remains inside M's spatial projection.
Both joint spheres are included. In 2D, the positive region has **two
components** and the joint has four points. Its planar target is exactly
$`2/(3a/4)+2/(3a/2)=4/a`$, using counting measure on all four, not two,
endpoints. Empty h=0 is a separate valid empty-region check: its many exterior
zeroes do not create an infinite joint.

**Unchanged planar ellipsoids.** With positive axes $`b_i`$ and
$`h=a(1-\sum x_i^2/b_i^2)`$, require $`2a/\min b_i<1`$ and set f=0.
The same line-segment argument gives the positive-part bound. Ellipsoid
superlevel volume is $`v_n(\prod b_i)(1-s/a)^{n/2}`$. Differentiate at zero,
or use the sphere parameterization and its Euclidean Gram Jacobian, to get

```math
\begin{aligned}
\mathcal J_d=\frac{S_{d-2}\prod_{i=1}^{d-1}b_i}{2a}.
\end{aligned}
\tag{G23}
```

In 2D this is exactly two reciprocal-gradient endpoint weights. At
$`a=1/4`$, axes (1,2) give $`8\pi`$ in 3D; axes (1,2,3) give the unchanged
$`48\pi`$ in 4D, without a smoothness change to the old general planar theorem.
The existing 4D regressions are retained, not replaced by these examples.

## 7. Regularity ledger: geometry is not an averaged jet

**Subsequent #78 written result:** [the actual long-null analysis](dimension-long-null.md)
now supplies the 3D jet and cancellation at every fixed positive cutoff, and a
bounded 5D/6D transfer for C⁴ germs at sufficiently small fixed cutoffs. It
proves the needed cutoff regularity from the joint collar, rather than assuming
generic transversality. This does not turn the trial policies below into an
all-dimension theorem or a Lean geometric specialization.

The matrix/chart argument needs only C¹ regular germs. More face derivatives
are needed to control an **actual translated overlap**, whose moving contacts
and exceptional directions can lose regularity even with smooth faces.
The conditional analytic cancellation lemma from #88 requires the following:

| Physical dimension | Required actual density remainder at a fixed positive cutoff | A sufficient density regularity | Conservative finite face class to investigate, not a proved implication |
|---|---|---|---|
| 3 | degree one plus little-o of sigma to power 3/2 | right C², or C(1,alpha) with alpha greater than 1/2 | C⁴ germs; `SmoothPilot3` has these derivatives |
| 5 | degree two plus little-o of sigma to power 5/2 | right C³, or C(2,alpha) with alpha greater than 1/2 | C⁵ germs |
| 6 | degree three plus little-o of sigma cubed | right C³ with its Peano remainder | C⁵ germs |

The finite face classes leave a derivative for chart Jacobians and a reserve
for moving-boundary differentiation. They are **trial sufficient-regularity
policies**, not theorems that the desired density regularity follows. Even
C-infinity is not a substitute for tangency/exceptional-direction domination.
#78 must derive the actual jet or record the obstructing fractional/logarithmic
coefficient. Any successful weaker class must be named in its theorem rather
than silently changing `SmoothPilot3`; failure in a model is not a counterexample
to D for the complete action.

#79 must also respect the positive odd first height moment and divergent even
second height moment proved in #88. A regulated wedge coefficient is not the
missing global planar base theorem. No rates, shrinking-cutoff uniformity,
density-dependent geometry, null/mixed-face extension, or convergence of
individual sprinklings is included in this package.

## 8. Verification boundary and reproduction

- **Written proofs:** Theorem G; intrinsic metric/area, chart gluing,
  nondegeneracy, finiteness and integrability; Lorentz/dilation and exact 4D
  identifications; examples. These use the classical implicit function,
  C¹ area and change-of-variables theorems, not an unproved analytic limit.
- **New executable checks:** exact SymPy algebra and numerical regressions
  in `dimension_joint_geometry.py` and `test_dimension_joint_geometry.py`.
  They exercise physical dimensions 2–6, nonlinear chart changes, boosts,
  orientation reversal, reciprocal dilation, empty tangent determinants,
  all four annular endpoints, disconnected and curved 3D integration, and the wrong Euclidean
  spacetime-area negative control. A finite regression range is not a
  universal geometry proof or an admissibility decision procedure.
- **Lean:** the historical #92 package introduced no new Lean artifacts or
  formal proofs. Existing #88/#91 and 4D theorems remain at their original scope.
  The follow-on [#115 port](../formal/PILOT3_INTEGRATION.md) proves smooth 3D
  region/atlas/area/integration geometry and explicit old-4D coordinate
  compatibility. A general-dimensional geometry port remains outstanding;
  downstream code must cite actual compiled declarations, not treat all the
  written contracts here as Lean proofs. Subsequent Lean changes require the
  full integrated `formal/check.sh` source/transitive-axiom audit after the
  last validation-affecting change, not only an incremental check.
- **Independent human mathematical review:** outstanding, separately from
  regression tests and the pre-existing formal verification.

```sh
uv venv --python 3.12 .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
