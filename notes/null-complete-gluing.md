# Signed gluing with the physical point and every partner (#156)

**Conventional written continuation, not independent acceptance or a Lean
certificate.** The original contract is unchanged. The single item-by-item
status record remains [required coverage §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).
This note begins with the complete finite-density accounting, rather than
assuming that a small singular neighborhood has small normalized action.

## 1. Audit before using NX

The starting local, remote and PR #184 head was
`92af9e0666c8fa26904a729be7a5bbdaf0ea2c2e`; the target remains
`issue-81-general-coverage`, based at
`3ae22f792325634607be5fd518303ff25a404dda`. The earlier receipts remain
historical. The following is a source audit, not a second independent proof
or human approval of [NX](null-cartesian-pushforward.md).

- **NX2's Jacobian:** the two actual endpoint normals have measure
  $`dx\,dz=r\,dr\,d\alpha`$. At closing,
  $`\xi_r=-v a_0^{2/d}`$, so both factors of the inverse derivative survive:
  $`r|dr/d\xi|=(H-\xi)/(v^2a_0^{4/d})`$. The endpoint-coordinate Jacobian
  is $`1/4`$. Thus NX2's first power and its displayed coefficient are
  correct; TC's squared gap cannot replace them.
- **NX3–NX6's remainder:** the two full primitive moments vanish through
  index $`m-2`$; the next primitive is bounded, not exponentially decreasing.
  Its normalized error has exponent $`m-1-(d-2)/2\gt0`$. The Fourier bound
  must use the Cartesian squared displacement, with the conformal factor in
  the amplitude. The low-frequency powers are zero and minus one-half in
  the two parities. These are integrable. They do not give a constant uniform
  in a vanishing displacement or in derivatives of shrinking endpoint fields.
- **NX7–NX10's trace:** partial quadratic coordinates leave an unrestricted
  residual function. Its zero set carries ordinary parameter volume, not a
  presumed Hausdorff measure on a smooth critical manifold. Nonzero residual
  values disappear by the integrable Fourier bound. Rank-minimal charts have
  invertible endpoint projections; this is the required continuity for the
  two separate selector approximations. A regular-part atlas alone cannot
  supply those constants at an omitted apex.
- **Short interpretation:** NX12 is a geometric screen formula after the
  boundary flux is restored. It is not permission to discard weighted
  generator terms. For a flat null half-space, the distributional wave
  operator of its indicator is zero; integration along its generators still
  has endpoints. The two-dimensional calculation below makes this distinction
  particularly visible.

No blocking discrepancy was found within NX-long's stated compact
smooth-sheet support. No uniform diagonal estimate is inferred from that
finding. The new estimate below uses a different integration order and does
not differentiate the sheet graphs.

## 2. Complete finite-density decomposition and the estimate actually needed

Write $`K_d`$, $`a_d`$, $`\beta_d`$ and $`c_d`$ for the unchanged canonical
quantities. On any admitted finite-volume region let
$`V=\mu_g(I[p,q])`$ be the **whole physical interval volume**, with its
original closed ambient order. Choose one fixed smooth physical temporal
cutoff $`\psi(\ell)`$, one below $`\delta/2`$ and zero above
$`\delta\gt0`$. A geometric neighborhood parameter $`s`$ below is independent
of density; it is not a replacement temporal cutoff.

Let $`h_s+e_s=1`$, where $`e_s`$ is supported near the unresolved strata and
$`h_s`$ vanishes on a smaller neighborhood. Put
$`w_0=h_s,w_1=e_s`$. Every pair integral below is over $`M\times M`$.
Every additional endpoint chart partition is included in these integrals
and summed over **all ordered labels**:

```math
\begin{aligned}
M_{ab}&=\int_M w_a(x)w_b(x)\,d\mu_g(x),\\
P^{\mathrm{s}}_{ab}(\rho)&=\int_{p\preceq q}
 w_a(p)w_b(q)\psi(\ell)K_d(\rho V)\,d\mu_g(p)d\mu_g(q),\\
P^{\mathrm{l}}_{ab}(\rho)&=\int_{p\preceq q}
 w_a(p)w_b(q)(1-\psi(\ell))K_d(\rho V)\,d\mu_g(p)d\mu_g(q),\\
D_{ab}(\rho,s)&=P^{\mathrm{s}}_{ab}+P^{\mathrm{l}}_{ab}
                 -\frac{a_d}{\beta_d\rho}M_{ab},\\
\mathcal A_{\rho,d}(M)&=-\beta_d\rho^{1+2/d}\sum_{a,b=0}^1D_{ab}(\rho,s).
\end{aligned}\tag{NG1}
```

The point is entirely in short. Its diagonal sum is
$`h_s^2+2h_se_s+e_s^2=1`$, not two copies of the physical point. In particular,
the unmatched terms are **both** cross-partner integrals, the two-singular-
endpoint integral, each one's short and long pieces, and their point weights,
including the overlapping-field point terms. The regular weighted coefficient
also contains derivatives of $`h_s`$ and its chart fields. Those derivatives
can be large on the transition annulus; replacing that coefficient by an
unweighted area with a hole is invalid.

Suppose the regular term has an independently computed coefficient
$`T_{00}(s)`$. A sufficient integrated gluing statement is

```math
\begin{aligned}
\lim_{s\downarrow0}\limsup_{\rho\to\infty}
\left|\rho^{1+2/d}\!
 \sum_{(a,b)\ne(0,0)}D_{ab}(\rho,s)
             +\frac{T_{\mathrm{sing}}(s)}{\beta_d}\right|&=0,\\
\lim_{s\downarrow0}\bigl(T_{00}(s)+T_{\mathrm{sing}}(s)\bigr)&=T.
\end{aligned}\tag{NG2}
```

Here $`T_{\mathrm{sing}}`$ must be derived from the geometry and the chosen
fields, not defined as an action residual. Vanishing of every sector,
absolute summability before signed integration, and a zero singular
coefficient are **stronger sufficient devices, not original-theorem
necessities**. The two-dimensional examples show why these distinctions matter.
A divergent intrinsic correction, such as NP's, instead needs independently
derived density-dependent geometric terms and their corresponding error; NG2
with a finite target cannot conceal that divergence.

An equivalent useful grouping sums the target label first: source fields
$`h_s,e_s`$, point weights $`h_s,e_s`$, and **all** future partners for each.
All ordered terms of NG1 remain present. This grouping is used in the gluing
proof below. It is not deletion of the opposite-endpoint neighborhoods.
Local coordinate/Whitney partitions may subdivide short further; every band
is retained and the original $`\psi+(1-\psi)=1`$ is unchanged. No field or
partition is chosen as a function of density.

## 3. A two-normal identity, rather than a Taylor expansion of shrinking fields

For this section only, assume a globally conformally Minkowski metric,
$`A=\Omega^d`$ smooth positive on a compact causal enclosure, and
$`M=F\cap P`$ with $`F`$ future and $`P`$ past. This is sufficient geometry
for the following result, not a new admissibility condition on #156.
Use null Cartesian coordinates $`(u,v,y)`$. On a pair chart with
$`q_v-p_v\ge cL\gt0`$ and physical gap comparable to $`L`$, set
$`\sigma=(q_u-p_u)(q_v-p_v)-|y_q-y_p|^2`$ and
$`\xi=\sigma a(p,q)^{2/d}`$, using the actual diamond average.
Two axes suffice to cover a causal displacement: at least one of its two
nonnegative null components is at least its physical time component.

At fixed base coordinates, a future set has a half-line as its u fibre and
a past set has an upper half-line. Write their measurable bounds as
$`p_u\gt f(p_v,y_p)`$, $`q_u\lt g(q_v,y_q)`$. Empty and unrestricted fibres
are allowed. No smoothness, nullness, or differentiability of these bounds is
used in this section. Vertical conditions remain base masks.

Put $`\epsilon=(c_d\rho)^{-2/d}`$ and let $`G=\mathcal G_d`$ be NX3's
signed second primitive. With subscripts denoting derivatives in the two u
coordinates, define $`Z=\epsilon^2G(\xi/\epsilon)`$. On a common small
**relative phase** collar, $`\xi_p\xi_q`$ is nonzero. The following is an
exact identity, including the zero extension to noncausal pairs:

```math
\begin{aligned}
\mathbf1_{\sigma\gt0}K_d(c_d\rho\xi^{d/2})
 &=\frac{Z_{pq}}{\xi_p\xi_q}
   -\frac{\xi_{pq}}{\xi_p^2\xi_q}Z_p,\\
F_0&=\frac{B_0}{\xi_p\xi_q},\\
H_0&=\frac{B_0\xi_{pq}}{\xi_p^2\xi_q}.
\end{aligned}\tag{NG3}
```

Here $`B_0`$ includes $`A(p)A(q)/4`$, endpoint fields, pair partitions and
the phase collar. The identity follows by the chain rule; $`G(0)=G'(0)=0`$
means that no light-cone delta term has been suppressed. The physical point
is not in this off-diagonal chart. Integrating **both** normals gives

```math
\begin{aligned}
\int_{p_u\gt f,\,q_u\lt g} B_0K_d
={}&-F_0(f,g)Z(f,g)
 -\int_f^\infty (F_0)_p(p,g)Z(p,g)\,dp_u\\
 &+\int_{-\infty}^g\bigl((F_0)_q+H_0\bigr)(f,q)Z(f,q)\,dq_u\\
 &+\int_f^\infty\int_{-\infty}^g
       \bigl((F_0)_{pq}+(H_0)_p\bigr)Z\,dq_u\,dp_u.
\end{aligned}\tag{NG4}
```

All four terms are required. Only a first normal derivative of each endpoint
field appears. In contrast, Taylor-expanding NX2's already integrated
amplitude differentiates a shrinking endpoint field repeatedly. Its constants
can grow like inverse powers of the neighborhood radius. NG4 avoids that
failed uniformity argument; it does not assume those derivatives are bounded.
The fixed-positive-relative-phase complement is retained and exponentially
small when the rescaled density is large.

### Ambient amplitude expansion and the uniform bound

The coefficients in NG4 are smooth functions of the **ambient endpoint
coordinates**, before evaluation on the fibre bounds. On a unit rescaled
compact box expand those coefficients and the conformal Fourier amplitude
in an absolutely convergent Fourier series in the two ambient endpoints.
A fixed sufficiently large number of ambient derivatives bounds its summed
coefficients. Each Fourier mode factors into one function of each endpoint;
its restriction to a merely measurable graph is still a modulus-one
multiplier. The first derivatives of the endpoint fields are kept outside
this expansion.

For fixed u and v parameters, the remaining transverse phase is
$`-|y_q-y_p|^2`$. If a u parameter is a fibre bound, its extra phase is again
an endpoint multiplier. The exact Fourier-transform operator therefore has
norm $`C|t/\epsilon|^{-n/2}`$, $`n=d-2`$, with no graph-curvature constant.
NX4's Euler-derivative envelopes apply to the ambient Fourier amplitude.
The frequency majorant is integrable in both parities. The factor
$`\epsilon^2`$ from NG3 and the transverse factor
$`\epsilon^{n/2}`$ give exactly the critical pair order.

For clarity, a controlling endpoint norm on a rescaled box is the integral
in its v parameter of the transverse $`L^2`$ trace norm, plus the integrals
in u and v of the transverse $`L^2`$ norms of the field and its first u
derivative. A missing fibre boundary contributes no trace. Cauchy–Schwarz in
the compact parameters bounds each term of NG4 by the product of these two
norms. Thus smooth fields supported in balls of radii $`R,S\le CL`$, with
ordinary first-derivative scale bounds, satisfy

```math
\begin{aligned}
\bigl|\rho^{1+2/d}P_\rho[\chi_R,\phi_S;\ell\asymp L]\bigr|
 &\le C L^{d-2}(R/L)^{d/2}(S/L)^{d/2}\\
 &=C\frac{(RS)^{d/2}}{L^2}.
\end{aligned}\tag{NG5}
```

The constant is uniform in the endpoint scales and density, for a fixed
compact conformal enclosure. At rescaled density below one, the elementary
bounded-kernel estimate gives the same inequality. At positive relative
phase its exponential bound has an extra endpoint-volume factor and also
satisfies NG5. Both angular charts and all normal sectors are included.

The bound also has a locally Lipschitz version in the positive ambient
density and its finitely many derivatives. Differentiate the coefficients
in NG3 and the rescaled Fourier amplitude, keeping the signed primitive;
only the already controlled Euler derivatives occur. A mean-value integral
between two positive densities proves the difference bound. This statement
is about the **physical interval average of the interpolating density**,
not replacement of that average by an endpoint value.

Unlike NX13, NG5 is not restricted to a flat angular collar. Unlike NX-long,
it does not require derivatives of the fronts for the estimate. It is still
a conformal Cartesian estimate: the next sections say where it actually
completes a diagonal assembly, and §8 records the intrinsic obstruction.

## 4. Joint diagonal/end resolution and its precise geometric uses

The off-diagonal bound alone does not cancel the point. Here is the needed
joint argument. Suppose a compact singular set has a finite tubular cover
with volume $`O(s^k)`$, projected volume $`O(s^{k-1})`$ after deleting one
coordinate, and $`O(R^{-(d-k)})`$ balls of radius $`R`$. Suppose also that its
Whitney cells, after rescaling, have uniform regular short charts: interior,
one fixed endpoint front, or distinct-ray NN charts. A two-sided spacelike
pinch is allowed because its two actual local components have no causal
pairs between them. These are checkable geometric conditions, not a premise
that the desired action cancels.

Use a nonnegative smooth source partition into shells at distance $`r`$
from the singular set. The target partition is summed over every partner.
Inside each Whitney cell, integrate the point and the relative near-diagonal
pairs together. The matched dimensional calculation gives a uniform bound
$`Cr^{d-2}`$: at large rescaled density its point pole cancels before the
bound is taken; at small rescaled density use bounded volume and kernel.
After counting cells, this is $`Cr^{k-2}`$. The same proof is Lipschitz in a
bounded positive family of rescaled ambient densities, by differentiating
its matched coefficients and remainder rather than the uncanceled point.

For a relative gap scale $`L\ge cr`$, cover the tube by L-balls. In each unit
rescaled ball the source trace norm is at most $`C(r/L)^{(k-1)/2}`$. Its
normal-derivative norm is at most $`C(r/L)^{k/2-1}`$: use the tubular volume,
the first-derivative bound and Cauchy–Schwarz in the compact u and v variables.
The target norm is bounded. NG4 therefore gives, after counting L-balls,

```math
\begin{aligned}
|\text{normalized shell/gap contribution}|
 &\le C L^{k-2}(r/L)^{(k-2)/2},\\
\sum_{r\le s}\left(r^{k-2}
       +\sum_{L\ge cr}L^{k-2}(r/L)^{(k-2)/2}\right)
 &\le C s^{(k-2)/2}\qquad(k\gt2).
\end{aligned}\tag{NG6}
```

Both sums are over fixed geometric dyadic scales, bounded above by the
compact enclosure. This proves a **uniform complete source-neighborhood
bound**, with the point once, all angular and normal sectors, both
scale-separated endpoint orders, and every target partner. At finite density
these countable partitions are absolutely integrable because the fields have
bounded overlap and the kernel is bounded. The summable normalized bound
then justifies the limit. The relative-gap subdivisions retain every band;
the outer physical cutoff remains NG1's fixed $`\delta`$.

NG6 is a sufficient gluing device, not an original-theorem necessity. In
codimension two it deliberately proves nothing: its sum need not converge.
[DL](null-two-dimensional-gluing.md) instead computes the full signed
logarithmic response and the adjoining sectors. The next section supplies
an all-dimensional application of NG6 with its geometric hypotheses checked,
not an analytic condition added to admissibility.

## 5. Complete conformal finite-null-polyhedron theorem

Let $`F,P`$ be finite Boolean future/past sets made from affine null
half-spaces, and let $`M=F\cap P`$ be bounded in a globally conformal chart.
No bound on the number of faces or independence of their normals is imposed.
Take as auxiliary singular skeleton all rank-at-least-three intersections
of their affine hyperplanes in the compact enclosure, even the inactive
ones. It is a finite union of affine sets of codimension at least three,
so it satisfies the tubular and covering bounds of §4.

Away from that skeleton there are at most two independent active normals.
A Lorentzian two-plane contains just two null directions; dependent null
normals therefore introduce no third direction. Coincident planes can be
merged in the actual Boolean formula; distinct parallel offsets have fixed
positive separation. In the two remaining directions, enumerate the upper
and lower sets of the four quadrants. The resulting local domain is empty,
interior, a half-space, one quadrant, three quadrants with one same-side
front, or the two opposite spacelike quadrants. The latter have **no** causal
cross pairs, also with transverse coordinates present. Thus every local
short domain is one of §4's proved charts. The finitely many angles and
affine offsets give uniform rescaled constants. No genericity is needed.

For $`d\gt2`$, NG6 restores the higher skeleton and all its partners. Weighted
cutoff derivatives in the regular coefficient vanish with the skeleton:
second derivatives times bulk volume, first derivatives times face measure,
and the screen measure are all $`O(s^{k-2})`$. These estimates are for the
computed coefficients; NG6 separately controls the full action remainder.

There is no missing nonlocal planar term. For a critical tangent pair of two
affine null sheets their normals must agree. At zero boundary gap the planes
then coincide, and their normal triangle has nonpositive gap
$`-\lvert y_q-y_p-vb/2\rvert^2`$. It has no positive causal interior. Its
quadratic form is negative definite and its signed primitive response is
zero. Other sheet pairs have no critical zero. NX thus gives zero on the
entire compact long complement; NG6 restores its skeleton neighborhoods.

Define $`J`$ from the actual codimension-two strata. Its multiplicity is one
for a mixed past/future quadrant, two for two opposite such quadrants, and
zero for a same-side crease. This is a geometric incidence count, independent
of density. The screen metric is induced on the intersection of the two null
planes. The complete boundary divergence, including all generator endpoints,
gives this measure. One may equivalently integrate the affine-face currents:
every mixed termination contributes one screen, a spacelike pinch contributes
its two real branches, and internal same-side fluxes cancel after restoration.
The origin of a source-localized current need not be that termination.

Together with the actual dimensional bulk coefficient, this proves

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,d}(M)
 &=\frac12\int_M R_g\,d\mu_g+\int_J\nu\,dA_g.
\end{aligned}\tag{NG7}
```

In dimension two all vertices have the critical codimension. The independent
complete proof is DL1–DL8: retain their real logarithms, compare the conformal
metric with the constant metric at each vertex using the signed estimate,
and restore the complete model response. The boundary term is twice the
number of components, equal to the same mixed-incidence counting measure.
Thus NG7 holds in **every integer dimension at least two** for these finite
null polyhedra. It is not a restriction imposed on all original geometries.

## 6. Beyond the collar: a complete conformal round bicone action

Consider the previously unfinished NX13 region
$`M_T=\{|t|\lt|x|,\ |t|+|x|\lt T\}`$, $`T\gt0`$.
It is the intersection of the future of $`(-T,0)`$ and the exterior of the
origin's closed past cone, with the analogous past set. Its closed physical
intervals stay in the region. It is bounded, globally hyperbolic, and connected
for $`d\gt2`$; for $`d=2`$ it has the two actual components treated in DL.
The metric is any fixed smooth positive conformal factor on its enclosure.

For $`d\gt2`$ the only genuine apex in its boundary is the origin. On each
rescaled annulus the two inner cone faces are smooth and separated. A small
relative diagonal chart meets at most one of them. All other interfaces are
regular: the two same-side seams at radius $`T/2`$, and the outer NN screen at
time zero and radius $`T`$. The short constants on the inner annuli are
uniform, since rescaling the cones fixes their angular geometry and leaves
the conformal density in a bounded positive smooth family. NG4 includes all
other normal/angular sectors and every partner, not only NX13's collar.
NG6 with $`k=d`$ therefore proves complete apex gluing, with no extra local
point atom in these dimensions.

The independent geometric long functional also extends across the apex.
The only critical null pairs are
$`p=(-r,r\omega)`$, $`q=(s,-s\omega)`$ on the two inner faces,
$`0\lt r,s\lt T/2`$. Each shares the null ray through the origin. There is
no other ordered tangent-null pair between the four faces: equating the
straight generator directions on different centers would require $`T=0`$,
or reverse the endpoint order. At the inner pair the transverse quadratic
form is positive definite.

Here is the coefficient in physical radial variables, including its normal
Jacobian. Move each endpoint inward by normal times $`x,z\ge0`$ and write
$`a=x+z`$. Near the antipodal direction at the second endpoint,
$`\sigma=rs|\theta|^2-2(r+s)a+a^2+O(|\theta|^4)`$.
The normal Jacobian is $`1/[4(r+s)^2 a_0^{4/d}]`$, and the two radial endpoint
measures are $`r^{d-2}s^{d-2}dr\,ds\,d\omega\,d\theta`$.
The quadratic transverse change of variables and NX10's independently
computed ray mean give

```math
\begin{aligned}
\mathcal C_T&=\frac{C_d(Q_+)}4
 \int_{S^{d-2}}\int_0^{T/2}\int_0^{T/2}
 \frac{(rs)^{(d-2)/2}A(-r,r\omega)A(s,-s\omega)}
 {(r+s)^2 a_0(p,q)^{1+2/d}}\,dr\,ds\,d\omega,\\
T_T&=\frac12\int_{M_T}R_g\,d\mu_g
 +T^{d-2}\int_{S^{d-2}}\Omega(0,T\omega)^{d-2}d\omega
 -\beta_dc_d^{-1-2/d}\mathcal C_T.
\end{aligned}\tag{NG8}
```

The radial integrand is absolutely integrable at both comparable and
separated zero endpoints for $`d\gt2`$. It is geometric data on the two
actual faces and their shared rays, not an action residual. Its signed
constant is NX11's positive-definite response; it need not be positive in
every odd dimension. It vanishes in even dimensions at least four.

For each fixed apex excision, restore the regular short calculation and
NX's complete off-diagonal calculation. The inner critical pairs lying in
$`\psi`$ contribute that same functional with weight $`\psi`$; those in long
have weight $`1-\psi`$. Their sum is NG8. In particular the original short
piece is **not** asserted to be purely local in the presence of this apex.
NG6 and the integrable geometric density then remove the excision, with
uniform critical error tending to zero. This proves the complete deterministic
limit $`T_T`$, including both seams, the outer screen, all complements and
the point once.

In the flat three-dimensional case,
$`C_3(Q_+)=2\Gamma(2/3)/9`$. Substituting the canonical constants and integrating
$`\sqrt{rs}/(r+s)^2`$ over the square gives

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,3}(M_T)&=(\pi+2)T,\\
\text{independent local bulk/screen target}&=2\pi T.
\end{aligned}\tag{NG9}
```

For example, the integral follows by ordering $`s\le r`$ and setting
$`s=rz`$; $`\int_0^1\sqrt z/(1+z)^2dz=\pi/4-1/2`$.
This is now a **complete** finite nonlocal correction, not NX's isolated
saddle response. Its written complete-action calculation does not close
#156: a corrected general intrinsic statement still has missing cases.
It does not alter #177's separate original curved-three-dimensional scope.

In dimension two the corresponding whole action is DL's two-rectangle
response, with limit four in the flat metric. In a conformal metric DL8 adds
half the scalar-curvature integral. The central pinch has two counting
incidences. Neither its atom nor the odd-dimensional ray correction is
obtained by multiplying a formal zero by NX13's divergent absolute integral.

## 7. Higher smooth floor contacts and a genuinely different null-cusp attempt

[FL1–FL6](null-floor-level-matching.md) resolve arbitrary finite smooth-sheet
contacts at a strict spacelike floor, including dependent higher incidences,
infinitely flat ties, positive-measure coincidences and round apices at the
floor. The method integrates the actual q-time interval before selecting any
sheet. Its scalar-height approximate identity controls the complete signed
closing correction; coarea derives the one/two/zero screen multiplicities.
It restores the smooth term and point, then NF's entire long complement.
This removes that contact-atlas limitation within the stated conformal class.

A different obstruction remains when both fronts move on the same null ray.
It is not the already solved compact long selector problem. To test it,
consider actual smooth null graphs in three dimensions
$`f=y^2/(v+a)`$, $`g=y^2/(v+b)`$, $`a\gt b`$, on a compact v interval where
both denominators are positive. The lower future side is above f and the
upper past side below g. Their diagonal width is a positive multiple of
$`y^2`$, and they meet along a null ray. The boundary squared-displacement
matrix has determinant

```math
\begin{aligned}
\det Q_{p_v,q_v}&=-\frac{(a-b)(q_v-p_v)}{(p_v+a)(q_v+b)},\\
(u,y,v)&=(r^2u',ry',v'),\\
ds_\eta^2&=r^2\bigl(du'\,dv'-dy'^2\bigr).
\end{aligned}\tag{NG10}
```

Thus its rank is higher than NX's minimum at every fixed positive gap, but
one eigenvalue degenerates at the diagonal. The isotropic codimension-two
bound NG6 is nonsummable. The second line is an actual dilation combined
with a boost, not a new physical time cutoff. It fixes these null graphs
and changes density to $`\rho r^3`$, with action scale $`r`$. On a compact
strip away from the two cone ends, the causal inequality for this quadratic
form forces the two transverse coordinates to have comparable magnitude:
the two roots for $`y_q/y_p`$ are positive and uniformly bounded above and
below, including the zero-gap limit. Comparable annuli therefore have fixed
separated fronts after this rescaling; their complete point/short calculation
is uniformly bounded. Their signed contributions sum as $`\sum_r O(r)`$,
not the logarithm from the isotropic tube bound.

This gives a real interior null-cusp strategy and a summable local strip
estimate, but **not** a general null-cusp theorem. Its constants use a lower
bound on both denominators. At a cone end or when additional fronts enter,
that lower bound and the partner-comparability assertion require a new joint
resolution. An arbitrary smooth same-ray contact need not have these
quadratic, boost-homogeneous graphs. No conclusion for all such ends,
infinitely flat null-null cusps, or their higher selections is inferred.
The strict-floor proof does not apply there, because its positive transport
speed is precisely what is lost.

## 8. Intrinsic physical unions: attempt, failure, and remaining inference

NG3's chain-rule identity itself is coordinate-free: for any two commuting
endpoint coordinate derivatives it holds wherever the **actual** phase is
smooth and its two first derivatives are nonzero. Apply it to
$`\xi=(V_g/c_d)^{2/d}`$, not to separate geodesic-route volumes. If the physical
interval is a union, both $`\xi_p\xi_q`$ and $`\xi_{pq}`$ contain derivatives
of that whole union, including overlaps and transition boundaries. A sum of
route-wise kernels or independently computed contact corrections would not
satisfy this identity for the original action.

The further bound does not transfer automatically. Its ambient Fourier
factorization uses the exact Cartesian squared displacement and its constant
mixed transverse block. Near an intrinsic cut/focal transition there may be
neither a smooth common phase collar nor that rank bound. Positivity of volume
and global hyperbolicity do not supply either. The two transition sides must
be included before a new signed primitive can be estimated.

This is not merely an absent technical assumption that can be added to the
parent. NP's complete physical spherical union already has a normalized
contribution growing like $`\rho^{2/7}`$ in the action. A universal bounded
version of NG5 for intrinsic intervals would contradict that proved written
example. NA3 separately rules out repairing it by additive density-dependent
local finite-jet coefficients. Its nonlocal focal coefficient cannot be
replaced by NG8's conformal shared-ray measure: they are different physical
interval geometries and different density orders.

### Test the identity on the actual spherical physical union

There is a more concrete failure than the absence of a preferred Cartesian
chart. Use NP's actual whole interval $`W(U,\theta)`$, not its slab weight,
and the geometric normal form O5–O7. Here
$`U=\sqrt{\tau^2-z^2-|b|^2}`$ is the Lorentz-invariant separation in the
lifted time/four-flat block. At zero flat displacement, differentiate in
$`p_u,q_u`$ with $`u=t+z`$, keeping the other null coordinates fixed. For
$`\xi=(W/c_7)^{2/7}`$ the exact derivatives are

```math
\begin{aligned}
\xi_p&=-\tfrac12\xi_U,&\xi_q&=\tfrac12\xi_U,\\
\xi_{pq}&=-\tfrac14\xi_{UU}+\frac{\xi_U}{4U},&
\frac{1}{\xi_p\xi_q}&=-\frac4{\xi_U^2},\\
\frac{\xi_{pq}}{\xi_p^2\xi_q}
 &=\frac{2(-\xi_{UU}+\xi_U/U)}{\xi_U^3}.
\end{aligned}\tag{NG11}
```

Set $`\theta=\pi-\lambda B`$, $`U=\pi+\lambda S`$ in this same fixed
geometry, and write

```math
\begin{aligned}
\mathcal F(S,B)&=\frac1{2\pi}\int_0^{2\pi}(S+B\cos\varphi)_+^3d\varphi,\\
\Xi(S,B)&=(D/c_7)^{2/7}\mathcal F(S,B)^{2/7}.
\end{aligned}\tag{NG11a}
```

On a compact post-transition sector $`S\gt B\gt0`$, O5 has a fixed x
integration endpoint. Differentiating its polynomial/rational U integrand
there proves the differentiated O6 limits through the three derivatives
needed below. In particular,
$`\xi_U=\lambda^{-1/7}(\Xi_S+o(1))`$ and
$`\xi_{UU}=\lambda^{-8/7}(\Xi_{SS}+o(1))`$.
Choose a small open sector where $`\Xi_{SS}\ne0`$, which exists since the
positive-side profile is the two-sevenths power of a cubic, not a linear
function. Then NG11's first coefficient has size $`\lambda^{2/7}`$, but
its **second** coefficient has size $`\lambda^{-5/7}`$. The differentiated
coefficients required by NG4 have terms of size $`\lambda^{-12/7}`$.
Discarding the chain correction because the first coefficient is small
would miss exactly the dangerous part.

The physical cut measure in NP3 is
$`\sin\theta\,|d\theta|\,dU\asymp\lambda^3 B\,dB\,dS`$, with the actual
smooth positive endpoint weight tending to $`G_N(\pi)`$.
The phase has size $`\lambda^{6/7}`$. Balancing that integration variable
with $`\epsilon=(c_7\rho)^{-2/7}`$ gives the pair order $`\rho^{-1}`$, hence
critical action order $`\rho^{2/7}`$, not a bounded analogue of NG5.
This is a change of variables inside the full fixed-cutoff integral, not a
shrinking physical cutoff or a density-dependent geometry. It identifies
why the conformal normal-coefficient estimate fails; it does not compute
the full signed coefficient from a favorable inner sector. NP7's actual
subtractions, both tails and the verified model sign remain necessary.

The secondary transition has its own real regularity loss. Let $`F`$ be
O6's whole angular positive-part profile and put
$`c_*=32/(35\sqrt2\pi)`$. Reflection of the full angular integral gives
$`F(S)-F(-S)=S^3+3S/2`$, so

```math
\begin{aligned}
F(1-h)&=(1-h)^3+\tfrac32(1-h)
                 +c_*h^{7/2}(1+O(h)),\\
\frac{d^4}{dS^4}
 \left(F(S)-S^3-\tfrac32S\right)\bigg|_{S=1-h}
 &\sim\frac{3\sqrt2}{\pi}\,h^{-1/2}.
\end{aligned}\tag{NG12}
```

This is not only a model artifact. In O5, near
$`x=2\pi-\theta`$, the actual two-distance Jacobian has its integrable
inverse-square-root edge. Multiplication by the squared opening factor and
integration up to $`\min(U,2\pi-\theta)`$ gives a five-halves transition in
$`W_U`$, hence a seven-halves transition in $`W`$, with nonzero coefficient.
At fixed non-antipodal distance the transition volume is positive, so taking
the two-sevenths power preserves this loss of fourth differentiability.
Thus the smooth ambient-amplitude Fourier estimate is unavailable even
before making its constants uniform toward the antipode. Splitting the two
sides and matching them is essential; neither a route-wise sum nor a smooth
Taylor-density assumption repairs it.

One can always push the complete endpoint measure forward by the true volume
and rewrite its signed kernel integral. That exact identity is **not** the
missing corrected general theorem. Requiring that measure to have the desired
critical asymptotic would simply put the conclusion into admissibility.
What remains is an independently derived geometric expansion or equivalent
signed estimate for the actual cut/focal/contact union, at every surviving
order, with both transition sides and complete point restoration. No such
estimate for the full original class is proved here.

## 9. Separate law transfer and original-contract stopping decision

NG7, NG8 and FL1 are complete deterministic conclusions at their stated
geometric scopes; DL supplies the critical two-dimensional vertex assembly.
For each, bounded Borel geometry, atomless volume, Borel closed order and the
exclusive interval relation verify the original finite Poisson law.
Whole-interval containment identifies the same physical rate. Reduced
ordered two-point Mecke, both intensity factors and the unchanged layer
factorials give the deterministic action exactly at each density; finite
second moments justify the finite signed sum. Only **then** apply the proved
limit. No sample-wise conclusion or interchange of limit and expectation
is asserted.

The original contract is **STILL BLOCKED**, not replaced by these sufficient
classes. Uniform gluing is now proved for finite null polyhedra, the full
round bicone (including its conformal density and every sector), and all
finite smooth-sheet strict-floor contacts. The remaining conformal problem
is not those already completed cases: it is general nonregular moving-null
contacts and their singular ends without the verified isotropic or
boost-resolved geometry. The intrinsic physical-union expansion above is
also still missing. NP/NA3 and NG9 constrain the corrected general conclusion
but a list of counterexamples and positive classes is not that conclusion.

These are written arguments needing analyst scrutiny, especially NG3–NG6's
ambient-amplitude and joint-point bounds, DL7's metric comparison, and FL3–FL4's
signed height matching. #94/#86 retain their review, provenance and justified
verification obligations; #177 remains unresolved. Tests, green CI and an
empty feedback collection cannot supply independent acceptance. No closure,
scope transfer, agent launch, merge, deployment or change of law follows.
