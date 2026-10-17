# Matching all finite-sheet contacts with a strict spacelike floor (#156)

**Written analytic result, not independent acceptance or Lean verification.**
This extends the contact calculation, not the original admissibility contract.
[NF](regular-null-front-limit.md) and [TC](null-tangency-matching.md) retain
their historical statements. The complete accounting and remaining general
obligations are in [NG](null-complete-gluing.md) and the single
[original-item crosswalk](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).

## 1. Domain and independently defined contact measure

Fix $`d\ge2`$, a smooth positive conformal factor on the compact causal
enclosure, and $`F=\{t+H(x)\gt0\}`$ with
$`|\nabla H|\le\lambda\lt1`$. Let $`P`$ be an open past set such that
$`M=F\cap P`$ is bounded. Write its height graph as $`t=G(x)`$.
Only near $`G+H=0`$ require that $`G`$ be an actual finite min/max of smooth
null height graphs. Their normals may be dependent, their ties may be
infinitely flat or have positive measure, and any number may be active.
A finite number of round Minkowski cone apices at the floor are allowed as
well. There is no contact-atlas transversality assumption. The upper front
away from the floor stays in the fixed past set and needs no such atlas.

These are sufficient hypotheses of this theorem. They do not remove general
null lower fronts, other singular front germs, or intrinsic cut/focal geometry
from #156. In particular, a finite smooth-sheet representation is not supplied
by an atlas that omits its singular ends.

Put $`h=G+H`$. On each smooth selected sheet,
$`h_i=G_i+H`$ has $`|\nabla h_i|\ge1-\lambda`$. Its zero surface is therefore
smooth. At almost every common zero, with respect to its hypersurface
measure, all other incident zero surfaces have parallel gradients; the
nonparallel intersections have zero such measure by the implicit-function
theorem. Since $`|\nabla G_i|=1`$ and $`|\nabla H|\lt1`$, positive parallel
$`\nabla h_i`$ are equal. There are at most two distinct groups, with
opposite orientations. This is the intersection of a line through an interior
point of the unit ball with its unit sphere, not an independence assumption.

At such a contact surface choose a spatial unit normal $`N`$. Define
$`\nu_+,\nu_-\in\{0,1\}`$ by whether the actual height $`h`$ is positive
to first order on its two normal sides. The finite min/max formula determines
these values before any density limit. Put $`\nu=\nu_++\nu_-`$ and count
each geometric surface once. With $`H_T`$ the tangential gradient, its
independently induced screen measure and the proposed target are

```math
\begin{aligned}
dA_g&=\Omega^{d-2}\sqrt{1-|H_T|^2}\,dS_x,\\
T_{\mathrm{floor}}(M)&=\frac12\int_M R_g\,d\mu_g
                       +\int_{\{h=0\}}\nu\,dA_g.
\end{aligned}\tag{FL1}
```

The square root is the Gram determinant of the metric restricted to the
floor contact. A regular exposed SN piece has multiplicity one. A persistent
union-type coincidence has two; the intersection type has zero. Higher
incidences with nonparallel floor-contact normals have zero screen measure,
but their **normalized action** is dealt with below, not discarded by that
fact. In two dimensions this measure counts points with these multiplicities.

**Theorem FL.** Every fixed member just specified has complete deterministic
limit FL1, followed separately by the same original-Poisson-law expected
limit. No source-to-single-tip fibre formula is used.

## 2. One exact height variable for every active sheet

Use NF's physical displacement $`p=q-\ell(1,bn)`$,
$`b=\sqrt{1-\xi}`$. For fixed spatial $`x=q_x`$, the actual q-time interval is
between $`\ell-H(x-\ell bn)`$ and $`G(x)`$. Define

```math
\begin{aligned}
a(x,\ell,\xi,n)&=1-\frac{H(x-\ell bn)-H(x)}{\ell},\\
g&=h(x)-\ell a,\\
1-\lambda&\le a\le1+\lambda,\\
q_t&=-H(x)+(1-\theta)h(x)+\theta\ell a,
                       \qquad 0\le\theta\le1.
\end{aligned}\tag{FL2}
```

The quotient has its smooth extension at zero. Integrating this **actual**
time interval gives $`g_+`$ times the average in $`\theta`$ of both endpoint
measures, fields, and the actual interval kernel. Crucially, that average,
viewed as a function of $`(x,h,\ell,\xi,n,\theta)`$, is smooth with uniform
parameter bounds. It has no sheet label. The upper front enters only through
its actual scalar height $`h(x)`$. No selector is differentiated.

Split the signed time integral into its extension on $`h\gt0`$ and its
entire closing part on $`\ell\gt\ell_0`$, where
$`\ell_0=hL`$ is the unique solution of $`h=\ell a`$. Call these pair
integrals $`S_\rho,E_\rho`$, so that the actual short pair integral is
$`S_\rho-E_\rho`$. In this representation the gap has **one power**, and
$`g\lt0`$ in the closing part. It is not TC's positive squared gap.
The original fixed temporal cutoff multiplies both terms. Their signed
extensions outside the physical domain cancel exactly; no new pairs are put
into the observable.

## 3. Signed closing bound and its mass

Resolve closing first by $`\ell=hLr`$, $`r\ge1`$. Near $`\xi=0`$ the
positive phase factor gives a uniform phase inverse. Strict spacelikeness is
used here: the possible fold away from zero stays a fixed distance away.
The complementary phase region is retained and exponentially controlled.
Taylor subtraction in the new phase through degree $`m-1`$,
$`m=\lfloor d/2\rfloor+1`$, uses the genuine signed moments. The resulting
pointwise closing contribution, already integrated in phase and angle, obeys

```math
\begin{aligned}
|\rho^{1+2/d}E_\rho(x)|
 &\le C\rho^{1/d}\Phi_d(\rho^{1/d}h(x))\mathbf1_{h(x)\gt0},\\
\Phi_d(z)&=\int_z^\infty
 v^d(1+v^d)^{-2(m+1)/d}\,dv,\\
\int_0^\infty\Phi_d(z)\,dz&\lt\infty.
\end{aligned}\tag{FL3}
```

For completeness, after closing resolution the time measure has size
$`h^{d+1}r^d\,dr`$. The phase remainder is bounded by
$`(1+\rho h^d r^d)^{-2(m+1)/d}`$ after its signed lower moments have been
subtracted. Substitution $`v=\rho^{1/d}hr`$ gives FL3. Smooth endpoint fields
and the real interval factor have bounded parameter derivatives on the
compact enclosure; the same argument bounds their errors. At infinity the
integrand defining $`\Phi_d`$ has powers minus four in even dimensions and
minus three in odd dimensions. Thus its tails have powers minus three and
minus two, respectively. This is an integrable **height** majorant, not a
pointwise assertion that closing vanishes uniformly as height tends to zero.

At a smooth floor point, freeze the density and the first floor derivative
after the rescaling, not before the finite-density identity. The limiting
height profile has total mass

```math
\begin{aligned}
\beta_d\int_0^\infty \mathcal E_x(z)\,dz
   &=\Omega(-H(x),x)^{d-2}(1-|\nabla H(x)|^2).
\end{aligned}\tag{FL4}
```

Here is a check of the sign and normalization without an illicit absolute
interchange at the null cone. Insert a smooth large radial cutoff in the
rescaled displacement. Integrate the height first: its signed closing gap
integrates from zero to $`\ell a`$ to $`-\ell^2a^2/2`$.
Spherical averaging gives
$`a^2=1+(1-\xi)|\nabla H|^2/(d-1)`$ in this integral. Apply NF11's **analytic
kernel identity**, not its contact theorem, to this quadratic polynomial.
At the critical exponent the angular beta ratio is $`-(d-1)`$, and
$`\beta_d S_d c_d^{-1-2/d}E_d(1+2/d)/(2d)=-2`$.
The two minus signs give exactly FL4, including the conformal power.
FL3 holds uniformly for these radial cutoffs: their phase derivatives cost
bounded logarithmic scale derivatives. Dominated convergence removes them.
Thus a divergent unsigned height/phase integral has not been interchanged.

## 4. Measurable ties, higher contacts, and cone apices

Coarea on each $`h_i`$ gives a uniformly bounded height density on its
compact contact charts. FL3 is therefore uniformly integrable after the
height rescaling. At almost every point of a zero surface, sheets not zero
there have fixed sign. Among the remaining sheets, the opposite-normal
group has opposite sign on a sufficiently small normal half-line. Sheets in
the same-normal group have the same first-order height, the same coarea
factor, and the same limiting profile. Their selected labels can oscillate
infinitely often; their **sum** nevertheless has that common profile.
The finite Boolean formula decides whether the positive group is present.

This proves the one-sided trace for the whole selected height, not for each
potentially oscillating selector separately. At nonparallel intersections,
cover their zero-measure subsets of the finitely many zero surfaces by open
sets of arbitrarily small surface measure. FL3 and coarea bound their
critically normalized integrals uniformly by that measure. Dominated
convergence on the complement then proves the complete closing limit.
No finite-contact-order, Dini, measure-zero-tie, or generic-rank condition is
used. In particular, this is not independent pairwise corner summation.

A round cone apex at the floor is also accounted for. For its upper height
$`t_0-|x-c|`$, strict spacelikeness makes $`h\lt0`$ off the apex locally,
so that branch supplies no actual interval there. For
$`t_0+|x-c|`$, the positive height is comparable to $`|x-c|`$ and its radial
derivative is bounded below by $`1-\lambda`$. Its height density is bounded
by $`C h^{d-2}`$. Consequently FL3 gives

```math
\begin{aligned}
\sup_{\rho\ge1}\left|\rho^{1+2/d}
 E_\rho[|x-c|\lt s]\right|&\le C s^{d-2}\qquad(d\gt2).
\end{aligned}\tag{FL5}
```

To verify the bound, substitute $`z=\rho^{1/d}h`$ and bound
$`Z^{-(d-2)}\int_0^Z z^{d-2}\Phi_d(cz)\,dz`$ uniformly for positive $`Z`$.
For each fixed collar the same integral tends to zero as density increases
when $`d\gt2`$. In $`d=2`$ a round cone is exactly two null linear branches;
the preceding two-sided trace, not FL5 with exponent zero, gives its counting
contribution. Finite sheet selection at the apex cannot increase these
bounds: it only restricts the actual height branches.

## 5. Restore the smooth term, flux, point, and original law

The signed extension is smooth in displacement and phase even when its
selected height is not spatially smooth. Those derivatives act on FL2's
smooth parameter function, while the fixed set $`D=\{h\gt0\}`$ and the
height remain integration data. NF's matched displacement/phase subtraction
therefore applies to this extension, with the actual dimensional residues.
Its leading term cancels the **whole physical point once**. For unit fields
its finite coefficient is

```math
\begin{aligned}
T_S&=\frac12\int_M R_g\,d\mu_g
       -\int_D \nabla_x\cdot(w\nabla H)\,dx,\\
w(x)&=\Omega(-H(x),x)^{d-2}.
\end{aligned}\tag{FL6}
```

This can also be checked directly in NF10's coefficient: integrate the
floor delta and its time derivative at $`h\gt0`$. The time-divergence term
integrates to zero; the spatial term is the displayed divergence, with the
chain derivative of $`w`$ included. The missing upper endpoint at zero height
is precisely the closing term FL4, not an additional assumed screen atom.

The finite Boolean set $`D`$ has finite perimeter because its defining
$`h_i`$ have uniformly regular zero surfaces. Gauss–Green is applicable.
Write $`H_N=\nabla H\cdot N`$ and
$`k=\sqrt{1-|H_T|^2}`$. On a positive normal branch its speed is
$`k+H_N`$; on the negative branch it is $`k-H_N`$. The closing densities are
respectively $`w(k-H_N)`$ and $`w(k+H_N)`$, by FL4 and coarea. If only one
side is in $`D`$, the divergence flux in FL6 supplies respectively
$`wH_N`$ or $`-wH_N`$. The sum is $`wk`$, the induced screen measure.
If both sides are present, there is no reduced-boundary flux between them;
the two closing traces sum to $`2wk`$. If neither is present, both are zero.
This proves FL1, including TC's doubled union coincidence, rather than
assuming any of these coefficients.

Arbitrary fixed smooth endpoint fields are treated in the same calculation.
Their closing mass is multiplied by their diagonal product; their smooth
coefficient is the actual NF10 polynomial with both fields. Field-derivative
and generator-endpoint terms are retained. In the complete ordered partition
sum the fields sum to one and their derivative terms cancel. The long part
is NF3's strict-floor inverse on the fixed past set, valid without a contact
atlas, and tends to zero at critical normalization. All phase complements,
subtracted tails, and both sides of the original physical cutoff are included.
This finishes the deterministic action, not only its contact contribution.

Finally use the original finite Poisson cardinality and conditional iid law.
Finite atomless volume, Borel closed order and exclusive interval relation,
whole-interval containment, the two Mecke intensity factors and original
layer factorials give the same deterministic integral at each density.
Finite second Poisson moments justify the finite signed layer sum. Applying
the deterministic conclusion **afterwards** proves the expected limit.
There is no sample-wise claim or limit/expectation interchange.
