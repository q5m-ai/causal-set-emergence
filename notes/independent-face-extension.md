# Independent face bounds: enlargement and comparison obstruction (#85)

**Decision: GO on the larger geometry below; STOP the same-height planar
comparison; NARROW the replacement to the direct-origin overlap proof.** This
package takes #85's **obstruction stopping rule**, not its complete-limit branch.
It supplies conventional geometric arguments, an actual local overlap jet,
explicit replacement long-ray bounds, and a counterexample to the selected
comparison mechanism. It does **not** supply an enlarged-class BDG limit.

Baseline: [`04d86fe`](https://github.com/q5m-ai/causal-set-emergence/tree/04d86fe).
The original `AdmissibleTwoFace`, action, target and checked theorems are
unchanged. Read with [the scope gate](general-contract.md),
[the original assembly](two-face-limit.md), and
[the long-null proof](../formal/LONG_NULL_GAP.md).
All new proofs below are **written, not Lean checked or independently human
reviewed**. Executable regressions check their algebra/examples, not arbitrary
admissibility or asymptotic convergence.

## 1. Fixed 4D class E: smooth face germs, independent causal envelopes

Work in Minkowski space with signature $`(+---)`$. Specify raw functions
$`h,f:\mathbb R^3\to\mathbb R`$ and write

```math
H=h_+=\max(0,h),\qquad \Omega=\{h>0\},\qquad
K=\overline\Omega,\qquad S=K\cap\{h=0\}.
```

Require only the following geometric data:

1. The positive region is bounded. The raw functions are C³ on an open
   neighborhood of K. The height vanishes on the frontier of the positive
   region, and its differential is nonzero at every zero in K. Nothing is
   required of that differential at positive height.
2. There are globally defined causal envelopes L and U with

   ```math
   \begin{aligned}
   U-L&=H\quad\hbox{everywhere},& U&=f\quad\hbox{on }K,\\
   |U(x)-U(y)|&\le\lambda_+|x-y|,&
   |L(x)-L(y)|&\le\lambda_-|x-y|,\\
   0&\le\lambda_+\lt1,&0&\le\lambda_-\lt1.
   \end{aligned}
   \tag{E1}
   ```

There is **no bound less than one on the sum** of the constants or on the
Lipschitz constant of H. The envelopes coincide outside the positive region;
they need not be differentiable there or across S. C³ belongs to the *raw
face germs* f and f-h near K. Requiring C³ of both clipped envelopes across S
would wrongly exclude the witness below. Irrelevant exterior values of h and
f are unrestricted; unrelated exterior zeros do not create joints. The empty
region is allowed and has zero action and target.

Define the actual region, closed faces and joint independently of any action:

```math
\begin{aligned}
M&=\{(t,x): f(x)-h(x)\lt t\lt f(x)\}
  =\{(t,x):L(x)\lt t\lt U(x)\},\\
\Sigma_-&=\{(f(x)-h(x),x):x\in K\},\\
\Sigma_+&=\{(f(x),x):x\in K\},&
J&=\{(f(x),x):x\in S\}.
\end{aligned}
\tag{E2}
```

The equality of regions follows pointwise: both fibres are empty when H is
zero; otherwise the spatial point is in K and both bounds agree. These are
exactly the old region and face definitions, but **new geometric hypotheses**.
No overlap jet, cancellation, expectation identity or proposed limit is an
admissibility field. This note does not declare a new Lean structure.

**Every old member is included without strengthening it.** Given the original
budget constants, take U=f and L=f-H. Their constants may be chosen as
$`\lambda_+=\eta`$ and $`\lambda_-=\eta+\kappa\lt1`$.
The original local C³ data supply a common open neighborhood of the compact K.
In the other direction (E1) gives only
$`\mathrm{Lip}(H)\le\Lambda:=\lambda_++\lambda_-\lt2`$.
Section 4 proves strict enlargement even after the known ambient transports.

## 2. Region, all strata and positive-density expectation

**Openness and compact closure.** H is continuous by (E1), so the positive
region is open and K is compact. Continuity near K shows h is nonnegative
there and $`S=\partial\Omega`$. The implicit function theorem at S makes K a
compact C³ domain with boundary S. It does not forbid multiple components,
holes, or interior critical points. The two continuous envelope inequalities
make M open. Over compact K their values are bounded; hence M is bounded,
Borel measurable and has finite four-volume. Vertical Fubini gives

```math
\begin{aligned}
|M|&=\int_\Omega h(x)\,dx.
\end{aligned}
\tag{E3}
```

**Closed ambient intervals, including null segments.** If
$`p\preceq z\preceq q`$ with p and q in M, causality and (E1) imply

```math
\begin{aligned}
t_z-L(x_z)&\ge t_p-L(x_p)
 +(1-\lambda_-)(t_z-t_p)>0,\\
U(x_z)-t_z&\ge U(x_q)-t_q
 +(1-\lambda_+)(t_q-t_z)>0.
\end{aligned}
\tag{E4}
```

Thus the whole closed ambient interval lies in M, not merely the straight
segment or timelike interior. This is the actual causal-convexity requirement
of `BoundedCausalRegion`, not a substitution of intrinsic global hyperbolicity.

**No lateral wall or hidden seam.** Any limit of points in M has spatial part
in K and time between L and U. Conversely, at an interior spatial point all
closed-fibre points are approximated by open-fibre points. At a point of S,
choose spatial points of the positive region approaching it and use their
midpoint times; continuity gives the unique collapsed-fibre point. Therefore

```math
\begin{aligned}
\overline M&=\{(t,x):x\in K,\ L(x)\le t\le U(x)\},\\
\partial M&=\Sigma_-\cup\Sigma_+,&
\Sigma_-\cap\Sigma_+&=J.
\end{aligned}
\tag{E5}
```

Both faces are compact embedded C³ hypersurfaces-with-boundary, with common
boundary exactly J. The graph maps are embeddings and S is a regular compact
C³ surface. In the interior, differentiation of the envelope inequalities
gives $`|\nabla f|\le\lambda_+`$ and
$`|\nabla(f-h)|\le\lambda_-`$; continuity from the interior gives the same
bounds at S. Thus the raw faces are strictly spacelike. Their conormals are
independent at J because their spatial gradients differ by the nonzero
$`\nabla h`$. There are no other boundary strata in this class.

**The exact expectation bridge is now applicable, not before.** The preceding
proof discharges openness/measurability, boundedness and closed-interval
containment. The original, separately checked 4D
`BoundedCausalRegion.expectedBDGAction_eq` consequently applies mathematically
at every positive density:

```math
\begin{aligned}
\mathbb E_{\mathrm{Poisson}(\rho\,d^4x|_M)} A^{\mathrm{disc}}_\rho
 &=\mathrm{continuumMean}(\rho,M),\qquad \rho>0.
\end{aligned}
\tag{E6}
```

This uses the unchanged unsmeared minimal-layer action and isolated restricted
order. Containment identifies its interval volume with the ambient Minkowski
volume. It is a **written instantiation** of an existing bridge, not a new Lean
instance or an expected-limit theorem. No asymptotic statement follows from it.

## 3. Independent induced area and angle

On S put $`p=\nabla f`$, $`g=\nabla h`$, $`k=|g|>0`$ and
$`\nu=g/k`$ (the inward spatial normal). The tangent lift of a spatial tangent
vector w is $`(p\cdot w,w)`$. Thus the positive induced joint metric is
$`|w|^2-(p\cdot w)^2`$. With ordinary Euclidean surface measure on S,

```math
\begin{aligned}
p_T&=p-(p\cdot\nu)\nu,& j_L&=\sqrt{1-|p_T|^2},&dA_L&=j_L\,dA_S,\\
n_+&=\frac{(1,p)}{\sqrt{1-|p|^2}},&
n_-&=\frac{(1,p-g)}{\sqrt{1-|p-g|^2}},\\
N&=1-|p|^2+p\cdot g,&
C&=\frac{N}{\sqrt{(1-|p|^2)(1-|p-g|^2)}}.
\end{aligned}
\tag{E7}
```

Both normals are future directed (the past one points inward). The independent
face bounds make their denominators positive and give N>0. Direct expansion
and the induced Gram determinant give

```math
\begin{aligned}
N^2-(1-|p|^2)(1-|p-g|^2)&=k^2j_L^2>0,\\
C&>1,&\coth\theta\,j_L&=\frac{N}{k},\qquad \theta=\cosh^{-1}C>0,\\
\mathcal J(M)&:=\int_J\coth\theta\,dA_L
 =\int_S\frac{1-|p|^2+p\cdot g}{|g|}\,dA_S.
\end{aligned}
\tag{E8}
```

This is not Euclidean spacetime graph area. It is intrinsically defined by
the restricted Lorentzian metric, so the chart densities agree on overlaps.
It uses the same classical spatial area as the old normalized
`graphSurfaceMeasure` (mathlib's Hausdorff measure multiplied by pi/4).
A finite regular atlas gives finite area. Compactness, the strict face bounds
and k>0 give positive minima of k, j_L and theta, so the weight is bounded and
absolutely integrable. All margins concern **this fixed geometry**, not a
family approaching a null face or zero angle. With a planar future face the
formula reduces to the old reciprocal-gradient target whenever that cap is
admissible. None of (E7)–(E8) uses an action computation.

## 4. Genuine enlargement, including the transport test

Use the scope gate's fixed steep capsule, with $`s=3/4`$:

```math
\begin{aligned}
h(x)&=s(1-|x|^2),& f(x)&=\tfrac{s}{2}(1-|x|^2),\\
H(x)&=s(1-|x|^2)_+,& U(x)&=H(x)/2,& L(x)&=-H(x)/2.
\end{aligned}
\tag{E9}
```

Each envelope is globally s-Lipschitz: inside the unit ball its gradient has
norm at most s, outside it is constant, and splitting any line segment at the
sphere proves the global bound. Both raw germs are polynomials, K is the closed
unit ball, and $`|\nabla h|=2s`$ at the sphere. The origin remains a positive-height
critical point. Thus this is an actual member of E, not a density-dependent
approximation. Its independent target and volume are

```math
\begin{aligned}
\mathcal J(M_s)&=4\pi\frac{1+s^2}{2s}=\frac{25\pi}{6},
& |M_s|&=\frac{8\pi s}{15}=\frac{2\pi}{5}.
\end{aligned}
\tag{E10}
```

The optimal thickness constant is 2s, while the future face alone forces
constant at least s. Already in this frame the old combined budget would
require at least 3s=9/4; even the old height-only bound fails.

**No known transported presentation rescues it.** In any common Lorentz frame,
rotation symmetry lets us take the boost axis through two antipodal joint
points. Write its speed as $`0\le v\lt1`$, choosing the sign convention in
which a graph slope q becomes $`(q+v)/(1+vq)`$. The future slope maximum is at
least u below. At one of these same projected joint points the difference of
the future and past graph slopes has magnitude Delta:

```math
\begin{aligned}
u&=\frac{s+v}{1+sv},&
\Delta&=\frac{2s(1-v^2)}{1-s^2v^2},\\
u+\Delta-1&=
\frac{(1-v)[3s-1+(3s-s^2)v]}{1-s^2v^2}>0\quad(s=3/4).
\end{aligned}
\tag{E11}
```

Any old envelope constant bounds the corresponding one-sided face derivative;
any old positive-thickness constant bounds the derivative difference at that
joint. Their sum must therefore exceed one. Every time-oriented Lorentz map
is a boost composed with spatial orthogonal maps; translations and positive
dilations leave these slope obstructions unchanged. This excludes the old
class **and its known transported/dilated regions**, not just its displayed
coordinates. This is a coverage statement, not a literature novelty claim.

## 5. Rigorous obstruction to #89's same-height planar mechanism

Let P be the proposed reference cap with exactly this H and future time zero:

```math
\begin{aligned}
P&=\{(t,x):-H(x)\lt t\lt0\}.
\end{aligned}
\tag{E12}
```

Its lower raw slope has magnitude $`2s|x|>1`$ when $`2/3\lt|x|\lt1`$.
More decisively, these rational spacetime points satisfy

```math
\begin{aligned}
a&=(-41/128,\ (3/4,0,0)),\\
z&=(-25/128,\ (7/8,0,0)),\\
b&=(-1/8,\ (7/8,0,0)),\\
a,b&\in P,&a\preceq z\preceq b,&z&\notin P.
\end{aligned}
\tag{E13}
```

Indeed a-to-z is null, z-to-b is vertical future timelike, and
$`-H(7/8)=-45/256>-50/256=t_z`$. Thus P is **not causally convex**.
It cannot be fed to the original graph-cap limit or to the flat-volume
expectation bridge. Merely deleting the slope field from a structure would
not repair this failure.

The precise overlap identity used by the comparison also fails. At a future
causal displacement $`(\tau,b)`$, direct intersection of the two vertical
intervals of P gives fibre length

```math
\begin{aligned}
&\left[\min\{H(x)-\tau,H(x+b)\}\right]_+,
\quad\hbox{not in general }[H(x)-\tau]_+.
\end{aligned}
\tag{E14}
```

At $`x=(3/4,0,0)`$, $`b=(1/8,0,0)`$, $`\tau=1/8`$, the proposed value is
13/64 but the actual value is 45/256. Their difference is 7/256. The inequality
persists on an open spatial neighborhood, so it changes the **integrated**
overlap, not merely a zero-measure fibre. The actual fibre never exceeds the
proposed one, so this discrepancy cannot cancel elsewhere. Increasing only
the time displacement to 9/64 gives a **timelike** example with discrepancy
3/256; continuity preserves it on open spatial and timelike-displacement
neighborhoods. It is not an ignorable null set in the pair integral. In fact for
$`b=\tau(1,0,0)`$ and every $`0\lt\tau\lt1/4`$ at this fixed x,

```math
\begin{aligned}
H(x)-\tau-H(x+b)&=\tau/8+3\tau^2/4>0.
\end{aligned}
\tag{E15}
```

Both candidate lengths are positive. Hence the obstruction occurs at
**arbitrarily short null displacements**, not just in a removable long sector.
The C³ jet for the *difference from this planar cap* cannot be imported using
the old planar gap formula. Equal four-volumes still cancel the point terms
algebraically; that alone supplies neither the reference limit nor its jet.

This is a counterexample to a **comparison/reduction**, not to the complete
normalized action conjecture for admissible M. No claim is made about the
limit of P's actual isolated discrete action, or about failure of the limit
for M_s. Changing the reference thickness would also lose the exact volume
cancellation and would require a new proved compensation, not a silent fix.

## 6. What survives: actual overlap and its local two-jet

For every causal displacement with $`\tau\ge|b|`$, the independent envelopes
order the two lower bounds and the two upper bounds. Vertical integration
therefore gives the **actual** overlap, with all partners retained:

```math
\begin{aligned}
V_M(\tau,b)&=\int_{\mathbb R^3}[U(x+b)-L(x)-\tau]_+\,dx.
\end{aligned}
\tag{E16}
```

The gap is at most H(x), and a positive gap forces both endpoints into the
positive region. Compact support and boundedness justify real Fubini and the
old exact signed displacement representation at each density.

There is one new germ/envelope subtlety. The global U need not be smooth at
S, and must **not** be differentiated there. By continuity of the raw face
gradients on K, choose a smaller neighborhood with strict derivative bounds
$`\bar\lambda_\pm\lt1`$. Choose a displacement ball so every segment starting
in K stays in that neighborhood. For x in the positive region let
$`q=\tau-f(x+b)+f(x)`$. Then q is nonnegative on the causal cone. If
$`h(x)-q>0`$, the lower *raw* derivative bound along the segment gives

```math
\begin{aligned}
h(x+b)&\ge h(x)-q+\tau-\bar\lambda_-|b|>0.
\end{aligned}
\tag{E17}
```

Thus a positive raw gap also has its partner in the positive region, where
U=f. Conversely every positive envelope gap has that property. This proves
that the two positive parts agree for these small causal displacements. It
justifies using the smooth raw f locally despite the nonsmooth extension U.

Now split (E16) on the fixed spatial domain:

```math
\begin{aligned}
V_M&=\int_\Omega h-\int_\Omega q
 +\int_{\{0\lt h\lt q\}}(q-h).
\end{aligned}
\tag{E18}
```

A finite C³ height atlas at S covers the last term for small displacement;
compactness keeps all other small positive heights in this collar. In each
chart $`h(\Phi(y,t))=t`$, solve $`\eta=q(\Phi(y,\eta))`$.
The height derivative of q is O(|b|), so after one fixed shrinking the implicit
denominator is at least one-half. The root is C³ and stays in the collar.
Integrate $`W(y,t)[q(\Phi(y,t))-t]`$ from zero to eta with oriented endpoints,
using fixed compact chart supports and the subordinate partition. W is C².
The first displacement derivative has no endpoint term because the gap
vanishes there; the next two derivatives use only one height derivative of
W and derivatives of q through order three. Compact dominated differentiation
gives a C³ extension of the future-cone overlap near zero. This is not a C³
extension of the entire covariogram through all spacelike displacements.

Expansion of (E18) gives its two-jet with the classical coarea normalization:

```math
\begin{aligned}
\widetilde V_M(\tau,b)={}&|M|-\tau|\Omega|
 +\int_\Omega p\cdot b\,dx
 +\tfrac12\int_\Omega D^2f[b,b]\,dx\\
 &+\tfrac12\int_S\frac{(\tau-p\cdot b)^2}{k}\,dA_S+R(\tau,b),\\
|D^jR(z)|&\le T|z|^{3-j},\qquad 0\le j\le3.
\end{aligned}
\tag{E19}
```

Here T is a finite bound from this constructed C³ extension on a smaller closed
ball; it is not an admissibility premise. The collar quadratic term is half
the square of the linear gap times the height Jacobian at zero. No Hessian of
h is needed in that term, and no coarea formula is applied through an interior
critical point. The argument uses exactly the regularity count detailed in
[the original short proof, §3](curved-face-stability.md).

**An independently calculable regression.** For the capsule, completing the
square in the actual vertical gap gives, for all future causal displacements,

```math
\begin{aligned}
V_{M_s}(\tau,b)&=\frac{8\pi s}{15}
 \left(1-\frac\tau s-\frac{|b|^2}{4}\right)_+^{5/2}.
\end{aligned}
\tag{E20}
```

If the radius squared in parentheses is positive, its centered ball lies in
both endpoint unit balls: with $`r=|b|`$, its radius R satisfies
$`R+r/2\le1`$ because $`\tau/s\ge r\ge r-r^2/2`$.
If an endpoint is outside, (E1) forbids a positive causal gap. Integrating
$`s(R^2-|x+b/2|^2)`$ over this ball proves (E20), including the zero case.
Its quadratic expansion has linear coefficient $`-4\pi\tau/3`$ and quadratic
terms $`\pi\tau^2/s-\pi s|b|^2/3`$, independently matching (E19).
This exact overlap calculation is **not** an asymptotic action computation.

## 7. Long-null audit: replace the margin, not the cancellation theorem

Put $`m=\min(1-\lambda_+,1-\lambda_-)>0`$ and
$`\Lambda=\lambda_++\lambda_-`$. For a nonnegative causal gap
$`G=U(y)-L(x)-\tau`$, two separate estimates give

```math
\begin{aligned}
H(x)&\ge(1-\lambda_+)\tau,&
H(y)&\ge(1-\lambda_-)\tau.
\end{aligned}
\tag{E21}
```

For the first write $`G=H(x)+U(y)-U(x)-\tau`$; for the second write
$`G=H(y)+L(y)-L(x)-\tau`$. This avoids the false replacement margin
$`1-\mathrm{Lip}(H)-\mathrm{Lip}(U)`$, which is negative for (E9).
It includes exact contacts and positive-height critical points.

With the old null coordinates and original Jacobian define

```math
\begin{aligned}
\tau(\sigma,v)&=(v+\sigma/v)/2,&r(\sigma,v)&=(v-\sigma/v)/2,\\
G(\sigma,v;x,\omega)&=U(x+r\omega)-L(x)-\tau,&
w(\sigma,v)&=(v-\sigma/v)^2/(8v).
\end{aligned}
\tag{E22}
```

The following are immediate finite-difference consequences of the upper
Lipschitz bound, not differentiation of a clipped envelope:

```math
\begin{aligned}
G(0,w)-G(0,v)&\le-\tfrac{1-\lambda_+}{2}(w-v),\qquad w\ge v,\\
-\frac{1+\lambda_+}{2v}(\sigma'-\sigma)
&\le G(\sigma',v)-G(\sigma,v)
\le-\frac{1-\lambda_+}{2v}(\sigma'-\sigma),\qquad
v>0,\ \sigma'\ge\sigma.
\end{aligned}
\tag{E23}
```

Thus cutoff contact never opens on the right, including a positive-measure
contact set. Fix a positive cutoff delta. Old active null endpoints lie in
$`H\ge m\delta/2`$. Under proper-time perturbation their displacement is at
most $`\sigma/(2\delta)`$. Unlike the old convenient bound, Lambda can exceed
one, so choose the common interval explicitly:

```math
\begin{aligned}
0\le\sigma\le e&:=\min\left\{\delta^2/2,
 \frac{m\delta^2}{2(1+\Lambda)}\right\}.
\end{aligned}
\tag{E24}
```

The height loss is at most $`\Lambda\sigma/(2\delta)\le m\delta/4`$.
All perturbed old-active endpoints therefore remain in the compact **interior**
tube $`H\ge m\delta/4`$, even after their perturbed gap becomes negative.
There U equals the C³ germ f on an open neighborhood. Compactness bounds all
smooth product derivatives used in `MonotoneHingeIntegral`. The source support
lies in the finite-measure compact tube $`H\ge m\delta/2`$.
With $`H_{\max}=\max H`$ and $`c=(1-\lambda_+)/2`$, the fixed upper endpoint
$`V=\delta+(H_{\max}+1)/c`$ has strict clearance; (E23) prevents reopening
beyond it. None of these constants depends on density or distance to contact.

These calculations remove the geometric obstacle to the old **long-ray
mechanism**. They do not license calling an `AdmissibleTwoFace` theorem on an
E member. The port must still connect the actual pointwise triple integral to
the hinge fibres, prove coefficient measurability/integrability and averaged
little-o using finite-measure domination. The moving-contact coefficient,
three-probe integrability argument, nonuniform fibre little-o warning and
signed kernel cancellations in `LONG_NULL_GAP.md` remain necessary, unchanged
analytic tools. No absolute-value bound on the original long pair term or
uniform shrinking-cutoff theorem replaces them.

## 8. Source-level proof/obstruction ledger and bounded replacement

| #89 component / source | Under E | Exact handoff |
| --- | --- | --- |
| `TwoFaceContract`, `TwoFaceGeometry`, `TwoFaceAngle`, `TwoFaceSurface`, `TwoFaceCharts` | Old theorem signatures remain old; (E2)–(E8) prove the new geometry in writing | Encode independent envelopes without extending `AdmissibleGraphCap`; preserve old declarations and prove inclusion |
| `GraphCollar`, height atlas, area/coarea and `GraphDivergence` | Their local regular-domain arguments survive; many current signatures inherit the old height slope | Factor regular compact height geometry from cap admissibility; allow all positive-height critical points |
| `translatedOverlap_twoGraph_causal` in `GraphOverlap`; generic displacement/density APIs | Already accept separate strict graph bounds or bounded measurable sets | Apply to L,U using (E2), (E4), (E16); retain every causal partner |
| `TwoFaceShortOverlapJet`, `ShortOverlapTaylor` | The actual local extension and two-jet survive as (E17)–(E19) | Use raw germs only after proving positive-part agreement; **not** the invalid planar-difference jet |
| `TwoFaceNullGap`, `TwoFaceLongGeometry` | Old combined margin and its convenient perturbation interval cannot be copied | Replace by (E21)–(E24); differentiation stays in positive-height tubes |
| `MonotoneHingeIntegral`, `AveragedQuadraticJet`, `NullTransverseCancellation` | Geometry-independent conditional analytic lemmas survive | Discharge all inputs for the new actual density; include moving contacts and coefficient integrability |
| `TwoFaceShortReduction.volume_region_eq_planar` | Equal volume survives by vertical Fubini | It is only point-term cancellation, not a valid reference theorem |
| `translatedOverlap_sub_planar`, `TwoFaceShortReduction.short_limit_of_density_difference`, `TwoFaceShortLimit` | Same-height graph-cap gap and limit inputs fail on (E9) | (E13)–(E15) obstruct the selected mechanism; do not weaken old hypotheses |
| Sphere moments, logarithmic signed moments, `ShortNullRemainder`, `ShortRadialQuadraticLimit` | Analytic calculations survive; existing quadratic-difference assembly omits the absolute constant/linear terms | Prove a direct-origin short theorem retaining volume-log/point cancellation, the linear endpoint cancellation and the full quadratic jet |
| Spatial divergence and target identity | (E8) survives; outward normal is minus g/k | Keep the future Hessian: its divergence supplies the p-dot-g term; source weights, if used, also require their derivative terms |
| `TwoFaceLimit`, `ExpectedLimits` | No new enlarged-class theorem follows from the old signatures | Combine actual short and long limits at one common fixed cutoff, then use (E6) |

**[Replacement issue #97](https://github.com/q5m-ai/causal-set-emergence/issues/97),
not a disguised limit assumption:** prove the direct-origin 4D action limit
for exactly class E. Its inputs are only §1's geometry and the
unchanged action; its outputs must be the unconditional deterministic limit to
(E8), followed by its expectation transfer. The bounded obligations are:

1. Encode E and its region/area/bridge instances, including old inclusion and
   (E9). Refactor only genuinely geometric dependencies; no jet or limit field.
2. Port the actual local extension/two-jet and the fixed-cutoff long proof with
   (E24). Keep contact coefficients, compact domination and interior critical
   points. Do not pass an invalid same-height cap to the original theorem.
3. Prove the **absolute-overlap** short integral, including its nonzero constant
   and linear terms. The four densities and signed logarithmic moments in
   [the short proof §§4–5](curved-face-stability.md) give the precise route.
   Retain the volume-log cancellation of the point term, the lower moving
   endpoint, all normalization powers, the future Hessian/divergence term and
   the derivative-controlled normalized remainder.
4. Assemble at one common fixed positive cutoff, identify the independent
   target, and only then transfer expectations. Exercise the steep capsule,
   a nonconstant joint-angle member, old planar/unequal-axis cases and interior
   critical points. Require the full integrated Lean/source/axiom audit after
   any Lean/checker input changes, plus Python, symbolic and Markdown checks.

This is a missing proof/encoding task, not a claim that the alternative is
impossible. The obstruction settles why #89's *selected* comparison cannot be
reused verbatim; it does not disprove a direct-origin or differently compensated
comparison proof. Until that task is complete, #90/#86 must count **geometry
and an obstruction, not new global asymptotic coverage**.

## 9. Verification and retained scope

`test_independent_faces.py` independently intersects vertical intervals, checks
the capsule's exact causal overlap against quadrature, its two-jet against
surface/bulk coefficients, induced Gram/normal algebra, the rational
causal-convexity counterexample, arbitrarily short planar failures, and the
new long-ray/tube bounds with thickness Lipschitz constant greater than one.
`test_general_contract.py` retains the all-boost exclusion algebra. These are
symbolic/finite numerical regressions, not machine proofs of the written
geometric statements or any high-density limit.

No `.lean`, checker, dependency or build input changes in this package; no new
Lean verification or rerun of the full integrated audit is claimed. Independent
human mathematical/physical review remains outstanding under #94/#86.

Broader non-two-graph atlases, extra strata, null/mixed boundaries, noncompact
regions, other dimensions and curved geometry remain outstanding. There is no
rate, density-dependent geometry, shrinking-cutoff uniformity, variance,
concentration or individual-sprinkling convergence claim. #24 and #86 stay open.
