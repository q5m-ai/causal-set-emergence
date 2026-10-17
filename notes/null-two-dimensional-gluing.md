# Complete two-dimensional logarithmic and vertex matching (#156)

**Conventional written proof, not independent acceptance or Lean certification.**
This is the two-dimensional companion to [NG](null-complete-gluing.md).
It retains the physical point and the full partners. In particular, the
logarithmic failure of NX13's absolute bound is not repaired by declaring its
coefficient zero.

## 1. A complete flat response with an arbitrary future front

Use $`u=t+x,v=t-x`$, so the volume density is $`w=1/2`$. Let $`F`$ be any
open future set and let $`P_b=\{u\lt b_u,v\lt b_v\}`$ be the past of a null
corner. Assume $`M_b=F\cap P_b`$ is bounded. If it is nonempty then
$`b\in F`$: a causal future of a point in an open future set is still in that
set. In particular a neighborhood of the corner is contained in $`F`$.
If $`b\notin F`$, the entire intersection is empty, not a half-weight corner.

The physical future fibre of every source $`p\in M_b`$ is the full rectangle
from $`p`$ to $`b`$. This assertion uses both future/past implications and is
not inferred from causal convexity alone. Its interval volume is
$`V(p,b)=w(b_u-p_u)(b_v-p_v)`$. Integrating the **actual** two-dimensional
kernel over that fibre gives

```math
\begin{aligned}
K_2(z)&=(1-2z+z^2/2)e^{-z},\\
\rho\int_{q\in P_b,\,q\succeq p}K_2(\rho V(p,q))\,d\mu(q)
 &=\tfrac12\bigl[1-(1-Z)e^{-Z}\bigr],\\
Z&=\rho V(p,b),\\
\mathcal A_{\rho,2}[\chi,1;M_b]
 &=2\rho\int_{M_b}\chi(p)(1-Z)e^{-Z}\,d\mu(p).
\end{aligned}\tag{DL1}
```

The last line includes the physical point, canceled with its entire partner
fibre before taking absolute values. It holds for every smooth source field.
To verify the integral, integrate $`K_2(z)\log(Z/z)`$ from zero to $`Z`$;
its derivative is $`e^{-Z}(1-Z/2)`$ and its value at zero is zero.

Put $`X=b_u-p_u,Y=b_v-p_v`$. The actual domain is a bounded down-set in the
positive quadrant. Write its horizontal extent as $`0\lt X\lt g(Y)`$;
$`g`$ is nonincreasing and has a positive finite limit $`G`$ as $`Y\downarrow0`$.
No smoothness or finite order of this boundary is needed. Integrating DL1 by
parts in $`X`$ gives a boundary integral and the integral of
$`-X\partial_X\chi\,e^{-\rho wXY}`$ over the same down-set. The first tends
to $`2\chi(G,0)`$: use $`Y=z/\rho`$ near zero and dominate away from zero by
$`C/Y`$, then by dominated convergence on fixed intervals. The second tends to
$`-2\int_0^G\partial_X\chi(X,0)dX`$. Indeed, for fixed positive $`X`$ its
exponential Y integral has mass at most two and tends to two whenever that
vertical fibre is nonempty. Dominated convergence in $`X`$ applies.
Consequently

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,2}[\chi,1;M_b]
 &=2\chi(b),\\
\lim_{\rho\to\infty}\mathcal A_{\rho,2}(M_b)&=2.
\end{aligned}\tag{DL2}
```

The two terms at the other end of the null generator cancel explicitly.
This is why a weighted source contribution cannot simply be identified with
a local NN-area atom. The complete unit-field answer is nevertheless two.

For a finite union $`P=\bigcup_j P_{b_j}`$, inclusion–exclusion at the
**future endpoint** gives the exact point/pair identity. Every nonempty
intersection is $`P_{b_J}`$, with $`b_J`$ the coordinatewise minimum of its
corners, and uses the same physical interval. Thus

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,2}[\chi,1;F\cap P]
 &=2\sum_{\varnothing\ne J}(-1)^{|J|+1}
                  \mathbf1_F(b_J)\chi(b_J),\\
\lim_{\rho\to\infty}\mathcal A_{\rho,2}(F\cap P)&=2\,\#\pi_0(F\cap P).
\end{aligned}\tag{DL3}
```

The last equality has a geometric justification independent of the action.
Each nonempty $`F\cap P_{b_J}`$ contracts toward a small past rectangle at
$`b_J`$ contained in $`F`$. Finite intersections have the same property.
The finite cover therefore computes the Euler characteristic by its nerve.
Each component is an open orthogonally convex planar region and has no hole:
a hole would disconnect a horizontal or vertical section. It is contractible,
so this Euler characteristic is its number of components. No independent
Poisson processes or unproved bilocal additivity were used.

This proves the complete flat result for an arbitrary lower future front and
a finite null upper front. In particular it includes all bounded finite-null-
polygon regions, their multiple corners, degenerate ties and pinches.

## 2. The physical short density and its actual logarithms

For a full null rectangle of side lengths $`U,V`$, put $`Q=wUV`$ and denote
an interval volume by $`z`$. Direct displacement integration, with both
endpoint overlap factors, gives

```math
\begin{aligned}
D(z)&=(Q+z)\log(Q/z)-2(Q-z),\\
P_\rho&=\int_0^Q D(z)K_2(\rho z)\,dz,\\
\mathcal A_{\rho,2}&=2(1-e^{-\rho Q}).
\end{aligned}\tag{DL4}
```

For a sharp **physical time** split $`(\Delta u+\Delta v)/2\lt r`$, with
$`2r\lt\min(U,V)`$, put
$`u_\pm=r\pm\sqrt{r^2-z/w}`$. The actual short density is

```math
\begin{aligned}
D_{\lt r}(z)&=(Q+z)\log(u_+/u_-)
              -w(U+V)(u_+-u_-),\\
D_{\lt r}(z)&=-Q\log z-z\log z+C_0+C_1z+O(z^2).
\end{aligned}\tag{DL5}
```

The square root restricts this formula to $`0\lt z\lt wr^2`$.
For the one smooth physical cutoff of NG1, average DL5 against
$`-\psi'(r)dr`$ on its fixed transition band. This retains both transition
sides and leaves the two logarithmic coefficients unchanged. It is not a
cutoff on either null coordinate.

The true kernel moments are
$`\int K_2=\int zK_2=0`$,
$`\int K_2\log z=-1/2`$ and
$`\int zK_2\log z=1/2`$. Hence the first logarithm gives
$`Q/(2\rho)`$, canceling the point, and the second gives
$`-1/(2\rho^2)`$, producing the finite action two. The long density is
smooth through its linear term; its critically normalized remainder is
$`O(\rho^{-1})`$. Fixed-positive-phase tails are exponentially small.
These facts prove the split conclusion, not just the full response DL4.

## 3. A whole tip and its adjoining cross partners

Remove an auxiliary square $`C_s=(U-s,U)\times(V-s,V)`$ at the future tip,
with fixed $`s\lt\delta/2`$. All internal pairs of this square are in the
original short part. Let $`L_s`$ be the rest of the rectangle. It is the union
of two anchored rectangles and is causally convex. Define the four areas
$`Q_1=w(U-s)V`$, $`Q_2=wU(V-s)`$,
$`Q_0=w(U-s)(V-s)`$, $`Q_c=ws^2`$.
The retained incoming pairs from $`L_s`$ to $`C_s`$ have their **whole original
interval**, including its passage across the auxiliary interface. Exact
partition of the pair domain, followed by DL4, yields

```math
\begin{aligned}
4\rho^2P_\rho[L_s,C_s]
 &=2\bigl(1-e^{-\rho Q_1}-e^{-\rho Q_2}+e^{-\rho Q_0}
                 -e^{-\rho Q_c}+e^{-\rho Q}\bigr),\\
\mathcal A_{\rho,2}[C_s,C_s]&=2(1-e^{-\rho Q_c}),\\
\mathcal A_{\rho,2}(M)-\mathcal A_{\rho,2}(L_s)
 &=2\bigl(e^{-\rho Q_1}+e^{-\rho Q_2}
                    -e^{-\rho Q_0}-e^{-\rho Q}\bigr).
\end{aligned}\tag{DL6}
```

The internal action tends to two and the incoming action contribution tends
to minus two. Their **complete** sum tends to zero, uniformly for
$`0\lt s\le s_0\lt\min(U,V)/2`$. The incoming long part tends to zero by
DL5 applied to all three rectangles, uniformly on that fixed range. Its
short part supplies the matching minus two. No outgoing pairs exist from
this future square to its complement. The point volumes add to the original
point once.

The source-only grouping is different and equally exact: sources in
$`C_s`$ have all their partners there, so their complete contribution tends
to two; all other sources together tend to zero. Neither grouping permits
one to infer a universal vanishing singular coefficient. For smooth overlapping
cutoffs NG1 also has mixed point weights; one must not replace them with a
sharp subregion's action or exchange those limits.

The logarithmic source-volume density is
$`\log(Q_c/z)`$. The signed source kernel $`(1-z)e^{-z}`$ has zero mass and
logarithmic moment minus one. Its full response is finite, while its absolute
integral has logarithmic growth. This explicitly resolves a real logarithm
and its adjoining sectors; it is not zero times NX13's divergent bound.

## 4. Conformal finite-null polygons: metric comparison at all vertices

Now let both fronts be finite Boolean combinations of affine null
half-spaces, $`M=F\cap P`$ bounded, and let $`A=\Omega^2`$ be any smooth
positive density on its compact enclosure. The physical interval is the
weighted rectangle, not the flat area. The flat formula DL1 is **not** used
for that interval.

Take a source cutoff supported within distance $`s`$ of a vertex and one
near it. Locally the two null axes give the actual polygonal germ. Compare
with that same germ in a fixed bounding null rectangle with constant density
$`A_0=A(\text{vertex})`$. All partners outside a fixed local neighborhood
have normalized bound $`O(s)`$ by NG5, separately in the real and model
regions; the physical intervals of the retained local pairs stay in the
common neighborhood.

For comparable endpoint annuli of radius $`R`$, the density difference in
rescaled ambient $`C^N`$ norm is $`O(R)`$. The entire point plus near-diagonal
pair calculation is Lipschitz in that norm: on such annuli there is no
vertex, and either one fixed endpoint domain or the regular distinct-ray
transport applies. Differentiate the matched Mellin calculation **after
point cancellation**. Its coefficient and remainder are uniformly Lipschitz;
small rescaled densities follow directly from the bounded integrals.
The comparable-scale difference is therefore $`O(R)`$.

For separated endpoint annuli $`S\ll R`$, NG3–NG5's density-difference
estimate is $`O(S)`$. Sum first over $`S\le s`$, then over the fixed geometric
R annuli. This proves the fully integrated comparison

```math
\begin{aligned}
\limsup_{\rho\to\infty}
\left|\mathcal A^{\mathrm{source}\ e_s}_{\rho,2}(A)
 -\mathcal A^{\mathrm{source}\ e_s}_{\rho,2}(A_0,\mathrm{model})\right|
 &\le C s(1+|\log s|).
\end{aligned}\tag{DL7}
```

Every partner and the point are included before this estimate. The scale
partition is fixed independently of density; no physical cutoff shrinks.
The four possibilities away from an irrelevant straight face are one
quadrant, three quadrants, two opposite spacelike quadrants, and the empty
germ. The two opposite quadrants have no causal pairs between them.
Thus the regular annular calculation has uniform constants in every case.

The model's complete source-weighted limit is DL3, so the vertex charges are
independent of the cutoff profile. They are twice the signed upper-corner
incidences lying in the open future set, not an assigned unit coefficient at
every vertex. Away from vertices, the short coefficient is NF's computed
bulk term plus $`\int_P\Box_\eta(\chi\mathbf1_F)dq_\eta`$; the boundary
weight is conformally invariant in dimension two. Its flat value is exactly
DL3. Long compact smooth-sheet contributions vanish by NX with $`d=2`$.
DL7 restores the omitted vertices and their complete partners. Therefore

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,2}(M)
 &=\frac12\int_M R_g\,d\mu_g+2\,\#\pi_0(M).
\end{aligned}\tag{DL8}
```

Geometrically each connected finite-null-polygon component has two mixed
past/future corner incidences. If components meet at a removed pinch, each
incidence is retained; the point is not counted only once merely because its
coordinates coincide. Thus DL8 is also half curvature plus the induced
counting measure of the actual NN incidences. Same-side corners have the
source charges described above, whose complete sum gives that geometric
identity. This derives their cancellation rather than assuming it.

For example $`M=\{|t|\lt|x|,\ |t|+|x|\lt T\}`$ consists of two opposite
null rectangles. In the flat metric its **whole** action is
$`4(1-e^{-\rho T^2/2})`$, tending to four. Two outer NN atoms and the two
incidences at the central pinch give that target. This is a complete answer
for this tip in dimension two, not an angular-collar estimate.

Finally, all these bounded Borel future/past intersections have finite
atomless volume, original Borel closed order and whole-interval containment.
Reduced two-point Mecke with the unchanged factorials and intensity factors
gives the deterministic integral at every density. Finite second Poisson
moments justify the layer sum. Apply this **after** DL3 or DL8 to obtain their
original-law expected limits. No sample-wise convergence is asserted.
