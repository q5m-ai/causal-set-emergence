# A critical flat Klein-bottle contact

This continues the [finite-lift reduction](finite-lift-flat-reduction.md) and
[quartic-log example](flat-holonomy-obstruction.md), without changing the G-SS
contract, physical action, independent target or Poisson law. The example below
has a **complete-action obstruction in every dimension at least five**. In
particular it reaches the dimension left open by the quartic-log example.
These are conventional written arguments, not new Lean declarations or
independent human review. Executable checks are diagnostics, not certification
of the asymptotic proof.

## 1. Geometry and complete lift lists

Fix an integer $`d\ge5`$, put $`p=d-3`$, $`q=d/2`$, and use spatial coordinates
$`(x,y,b)\in\mathbb R^2\times\mathbb R^p`$. Set

```math
\begin{aligned}
g(x,y,b)&=(x+1,-y,b),& h(x,y,b)&=(x,y+2,b),\\
k_j(x,y,b)&=(x,y,b+10e_j),&1&\le j\le p,\\
X_d&=\mathbb R^{d-1}/\langle g,h,k_1,\ldots,k_p\rangle,\\
M_d&=(-T/2,T/2)\times X_d,&T&=21/20,\\
g_M&=dt^2-h_{\mathrm{flat}},&1&\lt T\lt\sqrt5/2.
\end{aligned}
\tag{K1}
```

Every group element has spatial action
$`(x+m,(-1)^m y+2n,b+10\ell)`$ with integral indices. Its subgroup with even
$`m`$ is a translation lattice; the full action is free, proper and cocompact.
A fundamental domain has volume $`2\,10^p`$. The ambient spacetime
$`\mathbb R\times X_d`$ with the metric in K1 is globally hyperbolic and
flat. Its open slab is precompact and ambient-causally-convex;
its two faces are smooth, closed and spacelike, with empty joint. Thus its
independently computed target is zero. Orientability is not a G-SS hypothesis.

For time separation below $`T`$, there is at most one relevant lift in each
$`b`$ direction. Each reflection parity gives a square lattice of side two
in the $`x,y`$ plane. Three points from that lattice require enclosing radius
at least $`\sqrt2`$, so there are at most two causal targets per parity and
at most four in total. A same-parity pair must be horizontally or vertically
adjacent. Two horizontal pairs have total horizontal span at least three.
Two vertical pairs have horizontal separation at least one; averaging the
squared distances to either pair shows that their enclosing radius is at
least $`\sqrt5/2`$. Both cases are excluded by K1. Consequently a four-route
configuration has one horizontal pair and one vertical pair. This is an
exhaustion of causal lifts, not a selection of four routes from a larger sum.

At a fourfold null contact, choose a target lift with horizontal displacement
near one. Write the source and that target's vertical coordinates as
$`y_0+Y,y_0+W`$, with $`y_0=1/2`$ or $`3/2`$ modulo two. Write their horizontal
displacement as $`1+X`$ and their transverse displacement as $`b`$. The four
squared proper-time phases are exactly

```math
\begin{aligned}
s_1&=\tau^2-(1+X)^2-(W-Y)^2-|b|^2,\\
s_2&=\tau^2-(-1+X)^2-(W-Y)^2-|b|^2,\\
s_3&=\tau^2-X^2-(1-W-Y)^2-|b|^2,\\
s_4&=\tau^2-X^2-(-1-W-Y)^2-|b|^2,\\
r&=\tau^2-1-X^2-Y^2-W^2-|b|^2,\\
u&=-2X,\qquad v=2(Y+W),\qquad h_0=2YW,\\
(s_1,s_2,s_3,s_4)&=(r+u+h_0,r-u+h_0,r+v-h_0,r-v-h_0).
\end{aligned}
\tag{K2}
```

The simultaneous equations $`s_i=0`$ force $`X=0`$, $`Y+W=0`$ and then
$`Y=W=0`$. They give $`\tau^2=1+|b|^2`$. The two stated vertical centers
exhaust the physical ordered endpoint configurations. The source horizontal
coordinate has measure one and its transverse coordinates have measure
$`10^p`$. Changing the target representative reverses a vertical coordinate
but has absolute Jacobian one; it does not identify the two centers.

## 2. The regular complement and the actual closing fibres

Any three distinct null phases have the rank proved in the finite-lift note.
For this explicit family, the additional constant-time boundary can also be
checked, rather than assuming simultaneous transversality. At fixed $`\tau`$,
a linear relation among spatial phase differentials, with coefficient sum
$`A`$, gives $`Ab=0`$. Its two vertical endpoint equations say separately that
the coefficient-weighted vertical displacements within each parity sum to
zero. The horizontal equation says that the coefficient-weighted horizontal
displacements sum to zero.

If $`A=0`$, this would already be a relation among the full differentials.
It is impossible for at most three phases. For four phases, the exact fold
below retains it. If $`A\ne0`$, then $`b=0`$. A single phase can be stationary
only at gap zero. A same-parity pair can be stationary only at gap one; an
opposite-parity pair forces both vertical displacements to vanish, and is
stationary only at half an odd horizontal separation, hence gap $`1/2`$ in
our range. For three phases, take the same-parity pair. A horizontal pair
has displacements $`\pm1`$ at equality, while the other parity has horizontal
displacement zero and must have vertical displacement zero: equal nonzero
lengths are impossible. For a vertical pair, equality gives vertical
components $`\pm1`$; the other parity has zero vertical component.
Equal lengths force the pair's horizontal component to be zero and the
other's to be $`\pm1`$. The horizontal stationarity equation then sets the
other coefficient to zero, reducing to the gap-one pair case. Zero
coefficients are already covered by these smaller subsets.

Thus no one-, two- or three-phase boundary contact is critical at $`\tau=T`$.
The four-phase contact there has $`|b|^2=T^2-1\gt0`$ and is retained by the
following exact integral. A fixed temporal cutoff $`0\lt\delta\lt1/10`$ meets
only regular contacts. No cutoff is sent to zero with density.

Integrating **both endpoint times** gives $`T-\tau`$. Changing from $`\tau`$
to $`r`$ and integrating the spectator $`b`$ gives

```math
\begin{aligned}
F_d(A)&=\frac12\int_{\mathbb R^p}
 \frac{[T-\sqrt{A+|b|^2}]_+}{\sqrt{A+|b|^2}}\,db,\\
A&=1+r+X^2+Y^2+W^2,\\
F_d(A)&=\frac{(T^2-A)^{p/2+1}}2
 \int_{|z|\le1}\frac{1-|z|^2}
 {\sqrt{A+(T^2-A)|z|^2}\,[T+\sqrt{A+(T^2-A)|z|^2}]}\,dz.
\end{aligned}
\tag{K3}
```

This is smooth near $`A=1`$, and $`F_d(1)>0`$. In particular no moving
$`|b|=\sqrt{T^2-A}`$ fibre is discarded. Replacing $`T-\tau`$ by $`T`$
would give a different coefficient.

Away from the two fourfold-null sets, use actual independent active phases
and the boundary rank just checked. The finitely partitioned sublevel
integrals have smooth fibre densities and ordinary integer-power Taylor
expansions. Points with volume bounded away from zero give exponentially
small kernel tails. These arguments include the one-, two- and three-route
regions and all endpoint domains, not only the region with four positive
phases.

## 3. Exact folded density

Put $`\lambda=(1,1,-1,-1)`$ and $`\zeta=Y-W`$. Then

```math
\begin{aligned}
h_0&=v^2/8-\zeta^2/2,&\lambda\cdot s&=4h_0,\\
D(s)&=(s_3-s_4)^2/8-\lambda\cdot s,&\zeta^2&=D(s)/2,\\
A(s)&=1+(s_3+s_4)/2+
 ((s_1-s_2)^2+(s_3-s_4)^2)/16.
\end{aligned}
\tag{K4}
```

The linear map from $`(r,u,v,h_0)`$ to the four phases has determinant of
absolute value eight. Also
$`dX\,dY\,dW=du\,dv\,d\zeta/8`$. Summing both inverse branches of
$`\zeta`$, then both physical centers and the source translation variables,
gives the exact density near the all-zero corner:

```math
\begin{aligned}
 a_d(s)D(s)_+^{-1/2}\,ds_1\,ds_2\,ds_3\,ds_4,
 \qquad a_d(s)&=\frac{10^p}{8\sqrt2}F_d(A(s)),\\
 B_d:=a_d(0)&=\frac{10^p}{8\sqrt2}F_d(1)>0.
\end{aligned}
\tag{K5}
```

Here $`D_+^{-1/2}`$ means $`D^{-1/2}`$ on $`D>0`$ and zero on $`D<0`$;
its value on the null set is immaterial. It is locally integrable. Smooth
cutoffs equal to one near the two contacts may be used; their derivatives
are supported in the regular complement.

This differs from the earlier product-coordinate example: one of the three
actual linear phase coordinates is $`Y+W`$. On its zero fibre the remaining
product is a negative square, not an unrestricted product. Consequently the
density is an inverse square root rather than a logarithm. Pairwise rank
alone would not reveal that distinction.

## 4. Complete sign-sector matching

The sum-volume primitive uses
$`S=c_d\sum_i(s_i{}_+)^q`$ and **every nonempty active-positive subset**.
The all-negative subset is not an ordered pair and is not included.
We now compute the noninteger coefficient of the complete matched primitive,
not the coefficient of the all-four-positive sector alone.

Here is a local matching calculation for the density K5. Write
$`\alpha=7/2`$ and
$`P_\alpha=\alpha(\alpha-1)(\alpha-2)(\alpha-3)=105/16`$.
The leading homogeneous density is
$`B_d(-\lambda\cdot s)_+^{-1/2}`$. If an active subset $`I`$ has complement
of size $`m`$, integration of the inactive negative coordinates contributes
the corner antiderivative

```math
\frac{(-1)^m\Gamma(1/2)}
 {\Gamma(m+1/2)\prod_{j\notin I}\lambda_j}
 (-\lambda_I\cdot s_I)_+^{m-1/2}.
\tag{K6}
```

Far-cutoff terms are smooth functions of the active coordinates. To see this
without a contact-order assumption, use an inactive coordinate on which
$`\partial_j D=-\lambda_j+O(|s|)`$ is bounded away from zero, and move
parameter derivatives onto its smooth compact weight. At least one inactive
coordinate stays away from zero on each far-cutoff term. Repeating this
integration by parts localizes every nonsmooth term at the full inactive
corner, giving K6 and higher-order amplitude terms. This restores all the
reference strips automatically, including strips with an inactive partner
bounded away from zero.

The curvature of $`D`$ in K4 and the nonconstant amplitude do not alter the
leading fractional coefficient. On putting $`s_I=wz_I`$, the linear part
has size $`w`$ and the perturbation has size $`w^2`$. For $`m=0`$, the
inverse-square-root density changes in integral norm by $`O(w^{1/2})`$ after
rescaling: split a linear band of width $`O(w)`$ from its complement, use
coarea on the band, and integrate $`O(w)t^{-3/2}`$ outside. For $`m=1`$,
the square root is one-half Hölder. For $`m\ge2`$, its antiderivative is
continuously differentiable. Hence these errors contribute $`O(w^4)`$ or
better. Derivatives of the smooth amplitude leave one extra antiderivative
power and are higher order. Only finitely many derivatives are required;
this explicit geometry and K3 are smooth to every needed finite order.

It remains to evaluate the sum of all fifteen leading corner coefficients.
A convenient exact identity avoids a fitted numerical sign. Let
$`Z_1,\ldots,Z_4`$ be auxiliary independent variables with density
$`qz^{q-1}e^{-z^q}`$ on the positive axis; these are not the physical Poisson
process. Set $`W=Z_1+Z_2-Z_3-Z_4`$. Then the matched coefficient is

```math
 C_q=\frac{\mathbb E[(-W)_+^{7/2}]}
 {P_\alpha\,\Gamma(1+7/(2q))}>0.
\tag{K7}
```

For completeness, take four mixed coordinate antiderivatives of the leading
homogeneous density. Because $`\prod_i\lambda_i=1`$, the result is
$`(-\lambda\cdot s)_+^{7/2}/P_\alpha`$. Integrate by parts once in **each**
coordinate against $`\exp(-\sum_i(s_i{}_+)^q)`$. Its mixed fourth derivative
is the product of the four stated positive densities, supported on the
positive orthant. Excluding the all-negative orthant adds a mixed point
mass at zero; the fourth antiderivative vanishes there, so it contributes
nothing to this fractional coefficient. The four signs from integration
by parts cancel.
Boundary terms are exactly the smooth far-cutoff terms and lower-face
antiderivatives in K6. Their noninteger parts therefore match, and the
noninteger coefficient of this exponential integral is
$`\mathbb E[(-W)_+^{7/2}]/P_\alpha`$. Passing from a homogeneous primitive of
degree $`\alpha`$ to that exponential integral multiplies its coefficient
by $`\Gamma(1+\alpha/q)`$, proving K7. All these operations may first be
performed with compact cutoffs and the far-cutoff smooth terms retained;
no divergent uncut integral is assigned an ordinary integral value.

The expectation in K7 is finite and strictly positive: the auxiliary
variables are independent, continuous and nondegenerate, with every positive
moment finite; $`W`$ is symmetric and not identically zero. As an algebraic
calibration, at $`q=1`$ the difference of two independent shape-two gamma
variables has density $`e^{-|t|}(1+|t|)/4`$. Thus
$`C_1=22/105`$, while the all-four-positive sector alone gives $`2/35`$.
Their inequality is a negative control for omission of the other sectors.

The complete primitive, including the regular complement, is therefore

```math
 N_S^\delta(w)=b_1w+b_2w^2+b_3w^3+B_d C_qw^{7/2}+O(w^4).
\tag{K8}
```

## 5. Complete deterministic action, not a sector response

Let $`n=\lfloor d/2\rfloor`$. For $`d\ge5`$, the first three integer
primitive powers in K8 are actual roots of the signed kernel. Its response
to the fractional power is given by the existing normalized primitive
identity, with no new action convention:

```math
\begin{aligned}
 R_d&=\prod_{k=4}^{n+1}\left(1-\frac{7}{2k}\right)>0,\\
 \prod_{k=1}^{n+1}\left(1-\frac{7}{2k}\right)&=-\frac5{16}R_d,\\
 D_d&=\frac{\beta_d B_d}{21}\,c_d^{-7/d}
 R_d\,\mathbb E[(-W)_+^{7/2}]>0,\\
 L_S^\delta(\rho)&=D_d\rho^{1-5/d}
 +O(\rho^{1-6/d}).
\end{aligned}
\tag{K9}
```

The empty product in dimension five is one. The remainder estimate follows
by the signed Stieltjes kernel bound applied to the $`O(w^4)`$ remainder;
it does not differentiate an uncontrolled primitive error. Positive-volume
tails are exponentially small. In dimensions where the fourth integer
power is also a root, no use of a stronger error estimate is necessary.

Now restore the **physical** interval-union volume. The finite-lift note's
FL9 applies to this actual quotient and gives a primitive error
$`O(w^{q+2})`$ and signed action error $`o(1)`$. It accounts for both endpoint
overlap regions, all multiplicities and any self-overlap; replacing the
physical kernel by a lift-sum kernel is justified only through this estimate.
At the same fixed temporal cutoff, the existing short theorem S30 includes
the physical point once and tends to the independent empty-joint target,
namely zero. Exact short/long assembly therefore yields

```math
\begin{aligned}
 A_{\rho,5}(M_5,g_M)&\longrightarrow D_5>0,\\
 \frac{A_{\rho,d}(M_d,g_M)}{\rho^{1-5/d}}&\longrightarrow D_d>0,
 &d&\ge6.
\end{aligned}
\tag{K10}
```

Thus the failure survives all partners, sign sectors, endpoint times,
closing fibres, physical overlaps, regular complements and short point
cancellation. K9 is a long sum-volume estimate; K10 is the asserted complete
action result. No complete-action error rate is inferred by combining it
with an unquantified short limit.

## 6. Separate expectation transfer and coverage

The actual quotient has finite atomless metric volume, standard Borel
structure and the ambient-restricted measurable closed causal order. Its
interval is the physical union of all lifted diamonds. Causal convexity
identifies the exclusive interval with the physical region's interval;
null ordered pairs form a pair-null set; chronological intervals have
positive volume. Finite total mass gives the required Poisson second
moments. These are precisely the all-dimensional measured-order hypotheses
discharged in the finite-lift note, so the separately proved finite-density
expectation identity transfers K10 to the original Poisson action. No
sample-wise, variance or shrinking-cutoff assertion follows.

The corrected **dimension coverage** is now exhaustive: the finite-lift note
proves the complete deterministic and separate expected joint limits for all
flat G-SS regions in dimensions two through four; K10 supplies admissible
counterexamples in every dimension at least five. The earlier all-dimensional
Minkowski theorem, bounded first-cut torus theorem and quartic-log family
remain unchanged positive and negative examples in their stated classes.

A universal high-dimensional replacement target or classification of all
flat contact responses remains unproved. The original all-dimensional
assertion is refuted, not rescued by an unannounced holonomy, topology or
regularity exclusion. #149/#81/#24 retain their original scope and open
status; human mathematical scrutiny remains outstanding.
