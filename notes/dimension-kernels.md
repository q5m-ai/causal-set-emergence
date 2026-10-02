# Dimension-dependent BDG kernels and flat-joint prerequisites (#71)

**Scope:** the unsmeared, minimal-layer, isolated BDG action in integer dimensions
$`d\ge2`$, on bounded measurable ambient-causally-convex subsets of Minkowski
space. This is a normalization prerequisite for [#24](https://github.com/q5m-ai/causal-set-emergence/issues/24),
not the higher-dimensional two-face limit. Dimension one is excluded. No
smearing parameter, curved-space bulk term, null-angle limit, or convergence
of individual sprinklings is introduced.

**Verification:** §§1–6 explain the analytic derivations. Their signed Mellin
integrals, cancellation contract K, parity-specific slice and reduced-kernel
bounds, normalization, and fixed-regulator local coefficient now have Lean
proofs, mapped precisely in §8. The local theorem concerns the actual
first-endpoint-weighted deterministic bilocal observable, not an assumed
mass-one kernel. SymPy and quadrature remain diagnostics, not proofs. A
general-dimensional Poisson-expectation bridge, induced-area transport,
geometric long-null jet construction, and global two-face convergence are
**not** thereby proved. The subsequent [finite-geometry bridge](../formal/DIMENSION_INTERVALS.md)
proves actual interval volumes, ambient Lorentz transport, and finite-density
weighted-action covariance/dilation in every supported dimension. The separate
[#77 expectation bridge](../formal/DIMENSION_EXPECTATION.md) now proves contract F
from a genuine finite-order action, restricted interval volumes and that geometry;
it proves no new global limit. Existing four-dimensional definitions and proofs
are unchanged; an additional equality theorem calibrates the new reduction
against their kernel. The explanatory argument still benefits from independent
mathematical review.

## 1. Sources, conventions and normalization table

The action and coefficients are prior work:

- Glaser, *A closed form expression for the causal set d'Alembertian*,
  [arXiv:1311.1701v3](https://arxiv.org/html/1311.1701v3), equations (5), (7),
  (12)–(15), (17): interval volume, Euler operator, normalization, layer
  coefficients and action. The odd-dimensional operator has the same number
  of factors as the preceding even dimension, **not the same polynomial**:
  the Euler operator still contains the actual dimension.
- Dowker–Liu–Lloyd-Jones,
  [arXiv:2501.00139v2](https://arxiv.org/html/2501.00139v2), equations (3),
  (7)–(8), Appendix A (76)–(78): the discrete action and Poisson mean;
  §§7.1–7.4: lozenge/triangle and constant-angle cone evidence through dimension
  11. Their approximation in (72) is not used as a localization proof here.
- Buck–Dowker–Jubb–Surya, *Boundary terms for causal sets*,
  [CQG 32 (2015) 205004](https://doi.org/10.1088/0264-9381/32/20/205004):
  flat causal-diamond evidence in multiple dimensions. The subsequent
  [#90 passage audit](general-contract-literature.md) finds explicit asymptotic
  evaluations for dimensions 2–16 in §4, not an all-dimension proof. Those
  results are calibrations, not a novelty claim or a proof for spacelike
  two-face regions.

Use signature $`(+,-,\ldots,-)`$, proper time $`\tau`$, squared proper time
$`\sigma=\tau^2`$, and **unnormalized** radial null coordinates
$`u=t-r,\ v=t+r`$. Write

```math
\begin{aligned}
S_{d-2}&=\frac{2\pi^{(d-1)/2}}{\Gamma((d-1)/2)},&
c_d&=\frac{S_{d-2}}{2^{d-1}d(d-1)},\\
V_d(x,y)&=c_d\tau^d=c_d\sigma^{d/2},&
m&=\lfloor d/2\rfloor+1,\qquad n_d=m+1.
\end{aligned}
```

Here $`S_0=2`$ counts the two radial directions. The volume law follows by
integrating spatial balls of radius $`\min(t,T-t)`$ in a rest-frame interval
of duration $`T`$; Lorentz transport gives arbitrary timelike endpoints. Null
intervals have zero volume. **Glaser's coefficient in (5) is
$`\widetilde c_d=2^{d/2}c_d`$**, because his null coordinates have a factor
$`1/\sqrt2`$. Using our coefficient in his normalization without conversion
loses a factor two in both $`a_d`$ and $`\beta_d`$; the kernel argument must
also use the matching coordinate convention.

Let $`a_d=-\alpha_d>0`$ and $`g_d=c_d^{2/d}/\Gamma(1+2/d)`$. Translation of
Glaser's constants gives

```math
\begin{aligned}
a_{2n}&=4g_{2n},&
\frac{\beta_{2n}}{a_{2n}}&=\frac{\Gamma(n+2)\Gamma(n)}{\Gamma(2n)},\\
a_{2n+1}&=2g_{2n+1},&
\frac{\beta_{2n+1}}{a_{2n+1}}&=\frac{2n+2}{2^{2n}}.
\end{aligned}
```

This specifies every integer dimension, not just the finite regression range.
The following table is generated independently by `dimension_kernels.py`.
The last column is the critical long-null remainder power, not an established
geometric regularity statement. Point/pair density powers refer to the
normalized continuum action, including its outer prefactor.

| Dimension | Proper-time coefficient | Point coefficient | Pair/point ratio | Layers | Point/pair density powers | Critical power |
|---|---|---|---|---|---|---|
| 2 | $`1/2`$ | $`4g_2=2`$ | 2 | 3 | 1, 2 | 1 |
| 3 | $`\pi/12`$ | $`2g_3`$ | 1 | 3 | $`2/3,5/3`$ | $`3/2`$ |
| 4 | $`\pi/24`$ | $`4g_4=4/\sqrt6`$ | 1 | 4 | $`1/2,3/2`$ | 2 |
| 5 | $`\pi^2/160`$ | $`2g_5`$ | $`3/8`$ | 4 | $`2/5,7/5`$ | $`5/2`$ |
| 6 | $`\pi^2/360`$ | $`4g_6`$ | $`2/5`$ | 5 | $`1/3,4/3`$ | 3 |
| 7 | $`\pi^3/2688`$ | $`2g_7`$ | $`1/8`$ | 5 | $`2/7,9/7`$ | $`7/2`$ |
| 8 | $`\pi^3/6720`$ | $`4g_8`$ | $`1/7`$ | 6 | $`1/4,5/4`$ | 4 |
| 9 | $`\pi^4/55296`$ | $`2g_9`$ | $`5/128`$ | 6 | $`2/9,11/9`$ | $`9/2`$ |
| 10 | $`\pi^4/151200`$ | $`4g_{10}`$ | $`1/21`$ | 7 | $`1/5,6/5`$ | 5 |
| 11 | $`\pi^5/1351680`$ | $`2g_{11}`$ | $`3/256`$ | 7 | $`2/11,13/11`$ | $`11/2`$ |
| $`2n`$, $`n\ge1`$ | formula above | $`4g_d`$ | gamma ratio above | $`n+2`$ | $`2/d,1+2/d`$ | $`n`$ |
| $`2n+1`$, $`n\ge1`$ | formula above | $`2g_d`$ | ratio above | $`n+2`$ | $`2/d,1+2/d`$ | $`n+1/2`$ |

The normalization is $`l_p^{d-2}S^{(d)}/\hbar`$ for $`d>2`$ with
$`l=\rho^{-1/d}`$. In dimension two it means the dimensionless action
$`S^{(2)}/\hbar`$ of (76); do **not** define a Planck length by raising
$`8\pi G\hbar`$ to $`1/(d-2)`$ there.

## 2. Actual action, coefficients and finite-density expectation

Define the polynomial by a finite recurrence, not by its desired moments:

```math
\begin{aligned}
P_{d,0}(z)&=1,\\
P_{d,i}(z)&=P_{d,i-1}(z)+\frac{d}{2i}z
 \bigl(P'_{d,i-1}(z)-P_{d,i-1}(z)\bigr),\quad 1\le i\le m,\\
P_d&=P_{d,m},\qquad K_d(z)=P_d(z)e^{-z},\qquad
C_{k+1}^{(d)}=k![z^k]P_d(z).
\end{aligned}
```

This is exactly the product of $`(H+2i)/(2i)`$ acting on the exponential,
with $`H=d z\,d/dz`$. Independently, Glaser's finite-difference formula is

```math
C_{k+1}^{(d)}=\sum_{r=0}^k(-1)^r\binom{k}{r}
 \prod_{i=1}^m\left(1+\frac{dr}{2i}\right),\qquad 0\le k\le m.
```

Indeed, applying the Euler product to each term of the exponential multiplies
its coefficient of order $`r`$ by the displayed product; multiplying back by
$`e^z`$ gives the finite difference. The difference is zero above degree $`m`$.
Low-dimensional **layer** coefficients are respectively
`(1,-2,1)`, `(1,-27/8,9/4)`, `(1,-9,16,-8)`. The **polynomial** coefficients
include the factorial denominators. No four-dimensional coefficients are reused
in another dimension.

For a finite causal order, count ordered related endpoint pairs with exactly
$`i-1`$ elements strictly between them as $`N_i`$. Define the observable first:

```math
A^{\mathrm{disc}}_{\rho,d}(C)=\rho^{-(d-2)/d}
 \left[a_d N(C)-\beta_d\sum_{i=1}^{m+1}C_i^{(d)}N_i(C)\right].
```

Separately define the deterministic functional at positive density:

```math
\mathcal A_{\rho,d}(M)=\rho^{2/d}\left[
 a_d|M|-\beta_d\rho\int_M dx\int_{M\cap J^+(x)}dy\,
 K_d\bigl(c_d\rho\tau_{xy}^{d}\bigr)\right].
```

**Finite-density contract F (conventional proof and separate #77 Lean proof):**
for bounded measurable ambient-causally-convex $`M`$ and its independently
constructed finite Poisson sprinkling of intensity $`\rho>0`$,
$`\mathbb E A^{\mathrm{disc}}_{\rho,d}=\mathcal A_{\rho,d}(M)`$.
The one-point Mecke identity gives $`\rho|M|`$. The reduced two-point identity
and the Poisson law on each exclusive interval give

```math
\mathbb E N_i=\rho^2\int_M dx\int_{M\cap J^+(x)}dy\,
 e^{-\rho V_d(x,y)}\frac{(\rho V_d(x,y))^{i-1}}{(i-1)!}.
```

Finite Poisson second moments dominate all layer counts by $`N^2`$; finite
signed summation is therefore legitimate. Distinct endpoints and null cones
are Lebesgue-null in every supported dimension. Causal convexity identifies
the **restricted** interval with the full Minkowski interval up to endpoints.
Without it, the Poisson parameter is the restricted volume, not the displayed
proper-time law. This is the isolated regime; no embedded-regime substitution
is made.

The existing generic `FiniteConfiguration`/`FinitePoisson`/`PoissonIntegration`
construction and Mecke identities are reusable. The subsequent
[dimension-indexed interval geometry](../formal/DIMENSION_INTERVALS.md) now proves
the required actual volume law, nullity and coordinate transport.
`SpacetimeSprinkling`, `DiscreteBDG`, `ExpectationBridge` and their probability
instantiations remain four-dimensional and unchanged. The separate
[dimension-indexed bridge](../formal/DIMENSION_EXPECTATION.md) constructs its
own finite-order observable using those generic probability APIs, proves the
restricted-volume identity before invoking convexity, and recovers the original
4D discrete action and probability law through the proved coordinate map.
Contract F is now checked throughout the supported dimension range.

Positive dilation follows from endpoint Jacobians and the interval law:

```math
\mathcal A_{\rho,d}(sM)=s^{d-2}\mathcal A_{\rho s^d,d}(M),\qquad s>0.
```

The target joint area scales by the same power. Lorentz transformations preserve
Lebesgue measure, proper time and future direction. The ambient and action
identities now have separate dimension-indexed Lean proofs in `DimensionLorentz`
and `DimensionActionTransport`, including both endpoint Jacobians and signed
first-endpoint weights. They do not follow merely by renaming the 4D proofs.
General-dimensional induced joint-area transport remains separate.

## 3. Signed moments, scales and the parity obstruction

For real $`a>0`$, absolute convergence permits finite polynomial expansion.
Alternatively integrate each Euler factor by parts: its boundary term
$`z^a K(z)`$ vanishes both at zero and infinity. Induction gives the Mellin law

```math
\int_0^\infty z^{a-1}K_d(z)\,dz
 =\Gamma(a)Q_d(a),\qquad
Q_d(a)=\prod_{i=1}^m\left(1-\frac{da}{2i}\right).
```

Consequently, for every real $`j>-1`$,

```math
\begin{aligned}
M_d(j)&=\int_0^\infty u^jK_d(u^{d/2})\,du\\
 &=\frac2d\Gamma\!\left(\frac{2(j+1)}d\right)
   \prod_{i=1}^m\left(1-\frac{j+1}{i}\right),\\
\int_0^\infty\sigma^jK_d(c_d\rho\sigma^{d/2})\,d\sigma
 &=(c_d\rho)^{-2(j+1)/d}M_d(j).
\end{aligned}
```

All these signed moments are absolutely integrable. The exact zeros are
$`j=0,\ldots,m-1`$; the first natural nonzero value is
$`M_d(m)=(-1)^m(2/d)\Gamma(2(m+1)/d)`$. For $`j\le-1`$ the ordinary improper
integral diverges at zero because $`K_d(0)=1`$; meromorphic continuation is not
a replacement value. In 4D the formula is exactly
$`-j(j-1)(j-2)\Gamma((j+1)/2)/12`$, retaining the signed third moment $`-1/2`$.

The isotropic endpoint scale is $`\rho^{-1/d}`$, whereas at fixed positive
$`v`$ the near-null width is $`u\asymp(c_d\rho)^{-2/d}/v`$. The displacement
Jacobian and actual fixed-cutoff overlap density are dimension dependent:

```math
\begin{aligned}
dz&=2^{-(d-1)}(v-u)^{d-2}\,du\,dv\,d\omega,\\
B_{\delta,d}(\sigma)&=\int_{S^{d-2}}d\omega
 \int_{\max(\delta,\sqrt\sigma)}^\infty
 \frac{(v-\sigma/v)^{d-2}}{2^{d-1}v}
 V_M\!\left(\frac{v+\sigma/v}{2},
             \frac{v-\sigma/v}{2}\omega\right)dv.
\end{aligned}
```

Here $`V_M(z)=\int1_M(x)1_M(x+z)dx`$ is independently defined. Boundedness of
$`M`$ and fixed $`\delta>0`$ give bounded support and a bounded measurable
density. Signed Fubini is justified on a bounded displacement domain, exactly
as in the 4D overlap representation. In 2D the angular integral is a sum over
two directions. The diagonal endpoint is null; it is not a missing angular
sector.

**Conditional analytic contract K:** put $`q=d/2`$, $`n=\lfloor d/2\rfloor`$.
For any measurable bounded compactly supported $`B`$, the following implication holds:

```math
B(\sigma)=\sum_{j=0}^n b_j\sigma^j+o(\sigma^q)
\quad(\sigma\downarrow0)
\quad\Longrightarrow\quad
\rho^{1+2/d}\int_0^\infty B(\sigma)K_d(c_d\rho\sigma^q)\,d\sigma\longrightarrow0.
```

The jet to the left of the implication is a **hypothesis** of this analytic
lemma, not a geometric admissibility field. The limit to its right is the
conclusion. Subtract the polynomial over the whole
half-line using its exact zero moments. The remainder divided by
$`\sigma^q`$ is globally bounded and tends to zero at zero. Substitution gives
the constant prefactor $`c_d^{-1-2/d}`$ and integrable dominator proportional
to $`u^q|K_d(u^q)|`$. Dominated convergence proves the conclusion. A remainder
$`O(\sigma^{q+\eta})`$, $`\eta>0`$, gives error
$`O(\rho^{-2\eta/d})`$ plus exponential tails, at fixed cutoff only.

| Dimensions | Cancelled natural moments | Sufficient jet | First uncancelled analytic power | Missing geometric input |
|---|---|---|---|---|
| Even $`d=2n`$ | $`0,\ldots,n`$ | degree $`n`$ plus $`o(\sigma^n)`$ | normalized order $`\rho^{-2/d}`$ | actual averaged degree-$`n`$ jet at each cutoff |
| Odd $`d=2n+1`$ | $`0,\ldots,n`$ | degree $`n`$ plus $`o(\sigma^{n+1/2})`$ | normalized order $`\rho^{-1/d}`$ | a half-order stronger remainder, not merely $`o(\sigma^n)`$ |

In particular, the checked 4D quadratic jet is not sufficient in dimension
five. A right $`C^{n,\alpha}`$ density with $`\alpha>1/2`$ is sufficient in odd
dimensions, but has not been derived from the proposed faces. No uniformity
as $`\delta\downarrow0`$ is asserted.

**Logarithmic/fractional exceptions:** differentiation of the convergent moment
integral is legitimate for $`j>-1`$. In even dimensions,

```math
\int_0^\infty u^n\log u\,K_{2n}(u^n)\,du
 =\frac{(-1)^{n+1}}{n(n+1)}\Gamma(1+1/n)\ne0.
```

Thus a critical $`\sigma^n\log\sigma`$ term survives at order one after action
normalization, although $`\sigma^n`$ cancels. Lower-order log terms can diverge.
In odd dimensions $`M_d(d/2)\ne0`$: a critical fractional-power term survives,
and a critical power times a logarithm can produce a logarithmic density
divergence. Such terms must be retained and geometrically cancelled or explicitly
subtracted in a different analytic lemma; they are not permitted silent
subtractions from the physical action. This is an obstruction register, not a
counterexample asserting that these terms occur for admissible regions.

## 4. A dimension-dependent reduced kernel and its normalization

The original signed $`K_d`$ is not a mass-one kernel. Define the complete
future-cone spatial slice at density one, then the **actual vertical action
reduction**:

```math
\begin{aligned}
F_d(t)&=S_{d-2}\int_0^t r^{d-2}K_d\bigl(c_d(t^2-r^2)^{d/2}\bigr)\,dr,\\
G_d(H)&=a_d H-\beta_d\int_0^H(H-t)F_d(t)\,dt,\qquad H\ge0.
\end{aligned}
```

For a bounded graph cap $`-h(x)\lt t\lt 0`$ whose positive height is strictly
Lipschitz, the whole future cone truncated by $`t=0`$ stays in the region.
Fubini over that finite cone and the vertical fibre therefore proves

```math
\mathcal A_{\rho,d}(M_h)=\int_{h>0}G_{\rho,d}(h(x))\,dx,
\qquad G_{\rho,d}(H)=\rho^{1/d}G_d(\rho^{1/d}H).
```

No asymptotic premise enters this identity. In 4D it agrees with the unchanged
`planeKernel` by the already proved cone reduction; it is **not** the claim
that its special auxiliary-second-derivative representation works in all
other dimensions.

### Absolute tails before Mellin continuation

Set $`\sigma=t^2-r^2`$. Then

```math
F_d(t)=\frac{S_{d-2}}2\int_0^{t^2}
 (t^2-\sigma)^{(d-3)/2}K_d(c_d\sigma^{d/2})\,d\sigma.
```

For odd $`d=2n+1`$, the first factor is a polynomial of degree $`n-1`$ in
$`\sigma`$. Its full half-line moments all vanish by §3. Replacing the finite
integrals by minus their tails gives exponential decay times powers of $`t`$.
For even $`d=2n`$, expand $`(1-\sigma/t^2)^{n-3/2}`$ through degree $`n+1`$
on $`0\le\sigma\le t^2/2`$. The first $`n+1`$ terms cancel. The remainder
is bounded by a constant times $`(\sigma/t^2)^{n+2}`$ there, so its absolute
integral is $`O(t^{-7})`$. On the complementary half interval, exponential
decay dominates the polynomial and the integrable endpoint singularity
(the latter occurs in dimension two). The same exponential bounds control
tails of the subtracted polynomial integrals. Thus

```math
F_{2n}(t)=D_d t^{-5}+O(t^{-7}),\qquad
D_d=\frac{S_{d-2}}d\binom{(d-3)/2}{m}
 c_d^{-1-4/d}\Gamma(1+4/d)>0.
```

At zero, $`F_d(t)=O(t^{d-1})`$. These estimates justify all moments of orders
zero through three before they are evaluated. In even dimensions the absolute
fourth moment diverges; in odd dimensions all natural moments converge.

### Evaluation with the correct Mellin strip

For complex $`s`$ initially in $`1-d\lt\Re s\lt 3-d`$, absolute double integration
and a beta substitution give

```math
\begin{aligned}
\int_0^\infty t^{s-1}F_d(t)\,dt
 &=\frac{\pi^{(d-1)/2}}{d\,m!}\,
 c_d^{-(s+d-1)/d}\Gamma\!\left(\frac{s+d-1}{d}\right)
 \frac{\Gamma\!\left(m+1-\frac{s+d-1}{2}\right)}
      {\Gamma(1-s/2)}.
\end{aligned}
```

The intermediate beta factor contains
$`\Gamma((3-d-s)/2)Q_d((s+d-1)/d)`$. With
$`x=(s+d-1)/2`$, its simplification is exactly
$`\Gamma(1-x)\prod_{i=1}^m(i-x)/m!=\Gamma(m+1-x)/m!`$.
This removes apparent poles; it is important not to multiply zero by an
unevaluated infinite gamma value.

The tail estimates make the **integrated slice** Mellin transform holomorphic
on $`1-d\lt\Re s\lt 5`$ in even dimensions and on $`1-d\lt\Re s`$ in odd dimensions,
by domination on compact substrips (including logarithmic derivatives).
In the even strip the right side has no poles. In odd dimensions its gamma
ratio simplifies to $`1-s/2`$, so again it is holomorphic. The identity theorem
extends the equality from the initial nonempty strip. This continues an
already absolutely convergent integral; it does **not** license Fubini on a
divergent unsimplified double integral.

Writing $`J_k=\int_0^\infty t^k F_d(t)dt`$, evaluation at $`s=k+1`$ gives

```math
J_0=\frac{a_d}{\beta_d},\qquad J_1=0,\qquad
J_2=-\frac2{\beta_d},\qquad
J_3=\begin{cases}
0,& d\text{ even},\\
-\dfrac{\pi^{(d-1)/2}}{d\,m!}
 c_d^{-1-3/d}\Gamma(1+3/d),& d\text{ odd}.
\end{cases}
```

For example $`J_0=\pi^{(d-2)/2}/(d\,m!c_d)`$ for even dimensions, and
$`J_0=\pi^{(d-1)/2}/(2d\,m!c_d)`$ for odd dimensions. Substitution of §1
and the gamma duplication identity proves the displayed normalizations for
all dimensions; exact finite regressions include 2–11, 20 and 21.

Use $`J_0,J_1`$ to rewrite the original reduced kernel, without divergent
pieces, as $`G_d(H)=-\beta_d\int_H^\infty(t-H)F_d(t)dt`$. Absolute Fubini
now yields

```math
\int_0^\infty G_d(H)dH=-\frac{\beta_d}2J_2=1,\qquad
\int_0^\infty H G_d(H)dH=-\frac{\beta_d}6J_3.
```

Both absolute integrals are finite. The first signed height moment vanishes
in **even** dimensions but is strictly positive in **odd** dimensions. Thus
the 4D signed-first-moment-zero identity must not be copied into 3D or 5D.
In even dimensions $`G_d(H)\sim-\beta_dD_d/(12H^3)`$: the absolute second
height moment diverges logarithmically, and the signed second moment tends to
negative infinity rather than having a conditionally convergent value. In odd
dimensions the reduced kernel
has exponential decay and all natural absolute moments are finite. The 4D
tail coefficient reduces independently to $`-2\sqrt6/\pi`$, agreeing with
the existing analytic draft (its sharper coefficient is not an old Lean claim).

## 5. Regulated local coefficient and example compatibility

**Local contract L (analytic formulation; a checked regulated weighted
realization is given in §8):** let $`0\lt\kappa\lt 1`$, and choose a
bounded Lipschitz regulator cap agreeing with $`h(s,y)=\kappa s`$ on
$`0\lt s\lt a`$ and the support of a compact continuous tangential weight $`\eta`$.
For example, take
$`h(s,y)=\kappa\max(0,\min(s,L-s,R-|y|))`$ with $`a\lt L/2`$ and support
inside $`|y|\lt R-a`$. In dimension two the tangential space has dimension zero.
Choose a bounded continuous normal cutoff $`\chi`$, zero above $`a`$, with
$`\chi(0)=1`$. Weight the **first endpoint**, not both endpoints, by
$`\eta(y)\chi(s)`$ in the independently defined bounded action. The complete
future partners remain, including partners outside that source patch.

The exact graph reduction is

```math
\left(\int\eta(y)dy\right)\int_0^a\chi(s)G_{\rho,d}(\kappa s)ds
 =\frac{\int\eta(y)dy}{\kappa}
   \int_0^\infty\chi\!\left(\frac{\rho^{-1/d}u}{\kappa}\right)G_d(u)du
 \longrightarrow\frac1\kappa\int\eta(y)dy.
```

This is signed dominated convergence using §4, not positivity of the kernel.
The planar future normal and the normal to the slope-$`\kappa`$ past face
satisfy $`\tanh\theta=\kappa`$. The local coefficient is therefore precisely
$`\coth\theta`$, with unit induced tangential area. Lorentz transformation of
the **whole regulated observable** preserves the coefficient and induced
$`(d-2)`$-area, not ambient Euclidean spacetime area.

For Lipschitz $`\chi`$ extended by zero, an error bound is
$`\|\eta\|_1\mathrm{Lip}(\chi)\rho^{-1/d}\kappa^{-2}\int u|G_d(u)|du`$.
It is uniform for $`\kappa`$ in a compact subinterval of $`(0,1)`$ and for a
fixed controlled family of cutoffs. It is not a zero-angle uniform estimate.
First-endpoint partitions are exactly additive only when all partner terms
are retained. This regulated local statement proves neither curved-face
stability nor disappearance of a regulator's artificial complement.

### Independent calibrations, not global proofs

- **4D:** all layer coefficients, $`c_4`$, $`a_4=\beta_4`$, the full signed
  polynomial, transverse moments, plane reduction and dilation agree with the
  unchanged action. Direct future-cone quadrature is compared with the old
  `calculations.plane_kernel`; a separately derived diamond series is compared
  with `null_cap_action(rho,1,1)`. Old tests remain intact.
- **Constant-angle examples:** a cone of base radius $`RT`$ and height $`T`$
  in the source's §7.4 has base-joint area $`S_{d-2}(RT)^{d-2}`$ and weight
  $`R>1`$. Contract L gives the compatible local normalization
  $`R S_{d-2}(RT)^{d-2}`$, exactly (73). This does not prove that a nonsmooth
  cone apex or a discarded part of its overlap has no extra contribution.
  The 2D triangle/lozenge similarly use counting measure on their joints;
  there is no missing angular factor or extra half per spacelike joint.
- **Causal diamonds:** the target is $`S_{d-2}(T/2)^{d-2}`$, including
  value two in 2D and $`\pi T^2`$ in 4D. The inspected BDJS source explicitly
  evaluates dimensions 2–16; arbitrary-dimensional asymptotic proof provenance
  remains unresolved in the [later audit](general-contract-literature.md).
  Diamonds have null faces and are not instances of contract L or the spacelike
  class below. These limits are not obtained by interchanging density and
  zero/null-angle limits.

For an independent finite-density diamond calculation, radial null coordinates
give the interval power integral

```math
\int_{I(x,q)}\tau_{xy}^{dn}dy=A_d(n)T^{d(n+1)},\qquad
A_d(n)=\frac{S_{d-2}}{2^{d-1}}
 \frac{\Gamma(dn/2+1)\Gamma(d-1)}{d(n+1)\Gamma(dn/2+d)}.
```

Here $`n\ge0`$, $`A_d(0)=c_d`$. On a bounded interval the entire exponential
series converges absolutely and uniformly with its finite Euler derivatives.
Thus two successive interval integrations give the actual pair-kernel integral
as the convergent series

```math
\sum_{n=0}^\infty\frac{(-c_d\rho)^n}{n!}
 \left[\prod_{i=1}^m\left(1+\frac{dn}{2i}\right)\right]
 A_d(n)A_d(n+1)T^{d(n+2)}.
```

In 2D this sums to normalized action $`2(1-e^{-\rho T^2/2})`$, with limit two.
In 4D it matches the unchanged null-cap action at the uncut endpoint. The
finite-density series works in every dimension; this note does not derive the
general diamond asymptotic by exchanging its density limit and infinite sum.
Nor does the special 4D identity
$`\rho\int_{I(x,q)}K_4=1-e^{-\rho c_4T^4}`$ survive unchanged in other
dimensions: even its series coefficients differ in 2D.

## 6. Non-vacuous global contracts, explicitly still open

**Geometry-interface update (#92):** the
[dimension-indexed two-face package](dimension-two-face-geometry.md) supplies
written region/stratum, intrinsic metric/area, chart compatibility, finiteness,
and transport proofs, with exact unchanged 4D identification. It freezes the
stronger smooth `SmoothPilot3` as the first new global pilot and retains this
all-dimension C³ candidate separately. Its geometric proofs are conventional,
not new Lean declarations; the global goals below and actual overlap jets
remain open outside the already checked 4D case.

For each fixed dimension, use spatial Euclidean space $`\mathbb R^{d-1}`$.
A candidate class has bounded $`\Omega=\{h>0\}`$, a globally strictly
Lipschitz positive part $`h_+`$, $`C^3`$ raw height germs near its closure,
zero height and nonzero differential on its boundary, and a global $`C^3`$
future graph $`f`$. Require a strict combined Lipschitz budget
$`\kappa_h+\kappa_f\lt 1`$. Set
$`M_{h,f}=\{(t,x):f(x)-h(x)\lt t\lt f(x)\}`$. Interior critical points of $`h`$
are allowed; exterior zeros do not become joint components. These are geometric
hypotheses, not assumptions of an overlap expansion, action reduction or limit.

The class is nonempty with genuinely curved future faces in every dimension:
$`h(x)=a(1-|x|^2)`$, $`f(x)=\epsilon\sin x_1`$,
$`a,\epsilon>0`$, $`2a+\epsilon\lt 1`$. The positive part has Lipschitz constant
$`2a`$, the joint is the unit sphere (two points in 2D), and the differential
of the height is nonzero there. The origin remains an interior critical point.
Higher regularity, if necessary for higher-dimensional estimates, must be
stated as a new theorem class, not retrofitted into the existing 4D contract.

Define the target **independently**: induce the positive metric $`-g`$ on
joint tangents, let $`dA_{d-2}`$ be its Riemannian area (counting measure in
2D), and use both future unit timelike face normals. Set

```math
\begin{aligned}
C(x)&=\frac{1-\nabla f\cdot\nabla(f-h)}
 {\sqrt{(1-|\nabla f|^2)(1-|\nabla(f-h)|^2)}}>1,\\
\mathcal J_d(h,f)&=\int_J\frac{C(x)}{\sqrt{C(x)^2-1}}\,dA_{d-2}(x).
\end{aligned}
```

Transversality, compactness and the strict slope bounds give finite area and
bounded weight by conventional regular-level geometry. A general-dimensional
Lean induced-area/atlas proof remains outstanding; the existing implementation
is specifically a two-dimensional joint in four-dimensional spacetime.

**Global deterministic goal D:** for this geometric class, prove
$`\mathcal A_{\rho,d}(M_{h,f})\to\mathcal J_d(h,f)`$, or rigorously identify
and state a smaller sufficient class/corrected target. **Global expected goal E:**
prove $`\mathbb E A^{\mathrm{disc}}_{\rho,d}(C_{\rho,M})\to\mathcal J_d(h,f)`$
by contract F and D, not by defining the expectation to be the deterministic
integral. D and E are conjectural in this scope. Contract K may be used only
once its analytic hypotheses are derived for the actual overlap. Contract L
is a regulated calculation, not that missing derivation.

## 7. Proof-obligation ledger and proposed next issues

| Obligation | All-dimension status here | Existing checked 4D anchor | Next proof obligation |
|---|---|---|---|
| Action, coefficients, interval-volume constant | published coefficients, genuine finite-order action, Gamma conversion, actual interval-volume law and ambient Lorentz transport checked | `Specification`, `DiscreteBDG`, `IntervalMoments` | geometric uses beyond finite density |
| Finite Poisson mean | contract F checked separately in #77; actual restricted-volume identity, factorial-moment integrability, Minkowski specialization and exact 4D law transport | `ExpectationBridge` | independently prove a higher-dimensional deterministic limit before expectation transfer |
| Euler polynomials, Mellin multiplier roots, density rescaling | actual absolutely convergent integrals, exact roots, scaling and Rodrigues jets checked | `NullTransverseMoments` | geometric uses and log-inserted derivative identities |
| Slice tails, mass-one plane kernel, local wedge | actual moments, parity tails, unit mass and full-partner regulated weighted action checked | `KernelHalfLine`, `TangentWedge` | general induced-area transport and complementary-region control |
| Fixed-cutoff long-null cancellation | analytic contract K checked in every dimension, conditional on its stated jet | merged #61 / PR #68 | actual higher jets; odd-dimensional fractional remainder and tangency estimates |
| Curved-versus-wedge short error | not supplied here | #66 / PR #70: conventional proof plus checked exact partitions | rederive all powers, signed/log cancellations and partition-derivative terms |
| Global deterministic/expected limits | higher-dimensional goals D/E remain open | #67 completed in merged PR #89 for the original 4D class | port the checked proof decomposition, geometry and dimension-specific estimates, then apply F |
| Conventional expert review | outstanding for this note | machine checking is not peer review | independent mathematical and physical scrutiny |

**Actual dependency snapshot:** this branch starts at `faee2e3` on `main`, after
merged #61 (PR #68), #65 (PR #69), #66 (PR #70), and checker PR #87. At issue
inspection #67 is **open**, with no implementing open PR found. #61 proves the
actual quadratic jet and long-null cancellation at each fixed positive cutoff;
#66's complete short-limit argument is conventional, not end-to-end Lean.
Neither gave #67's full assembly at that snapshot.

**Integration update:** PR #89 subsequently merged at `2f1addf`, completing
#67's original four-dimensional deterministic and expected limit goals.
The present combined candidate includes that proof; see
[its decomposition](two-face-limit.md) and `formal/BoundaryDraft/TwoFaceLimit.lean`.
It does not discharge the higher-dimensional goals D/E or close #24.

Keep these prerequisites and remaining gates distinct:

1. **Dimension-indexed finite-density API:** the Euclidean causal geometry,
   graph-cap bilocal reduction, density scaling, zero-dimensional tangential
   measure, and equality with the unchanged 4D reduced kernel are now checked.
   The subsequent #91 [finite-geometry extension](../formal/DIMENSION_INTERVALS.md)
   proves the actual interval-volume/Lorentz theorem and action covariance/dilation.
   The separate #77 [expectation bridge](../formal/DIMENSION_EXPECTATION.md)
   now proves F from the genuine dimension-indexed discrete observable and
   actual restricted interval rate, without a new probability axiom.
   #92 supplies the independent geometric target and named pilot, not a
   probability port.
2. **Completed integrated-kernel/local-coefficient prerequisite:** the actual
   moments, parity-specific tails, odd positive first height moment, even
   divergent second absolute moment, and regulated deterministic weighted
   action limit are now checked in Lean. This is a local observable, not a
   full-region boundary limit or a general induced-area transport theorem.
3. **Geometric long-null gate:** start with 3D/5D and the even 6D jet; establish
   the actual averaged remainder or exhibit the obstructing fractional/log
   coefficient. Do not add contract K to admissibility. Specify any higher
   face regularity and prove a nonempty class with curved future faces.
4. **Short-distance stability in each parity:** port #66's *argument*, not its
   coefficients, and retain nonzero source-cutoff derivatives until the full
   partition cancels them. Determine whether more curvature terms survive.

**Scoped later issue proposal (not opened as an asserted theorem):**
“Establish a flat two-spacelike-face limit in a specified dimension and
regularity class using the completed four-dimensional assembly.” Before opening
that implementation issue, read #67's now-checked theorem and proof decomposition
in merged PR #89. Use that decomposition as the template, while distinguishing
its checked unweighted planar-comparison route from #66's conventional full
weighted estimates. Require the remaining tasks above and independent
angle/area transport in the new dimension; do not claim an all-dimension
consequence merely from the 4D completion.
Acceptance must require the independently defined D, followed by E, with no
new limit premise, and regressions for unchanged 4D caps and genuinely curved
future faces. Full local source/axiom audit and conventional proof review stay
separate. Curved-space Einstein–Hilbert recovery and arbitrary null/mixed or
sample-wise limits remain outside that issue.

## 8. Reproduction and exact machine-checked boundary

The files below are in `formal/BoundaryDraft/` and are imported by the public
`BoundaryDraft` entry point. They keep independent definitions of the
polynomial, published action constants, physical slice, and finite-height
reduction; none is defined by its desired integral or normalization.

- **`DimensionKernel.lean` and `DimensionMellin.lean`:** the Euler recurrence,
  algebraic roots, actual absolutely convergent Mellin/transverse integrals,
  arbitrary positive-density scaling, failure of integrability at or below the
  lower-endpoint threshold, and surviving odd critical half-orders.
  `dimensionMellinFactor` remains an algebraic product; the integral identity
  is a theorem, not a definition.
- **`DimensionCancellation.lean`:** contract K for measurable bounded
  amplitudes with the specified jet. The global remainder-quotient bound,
  finite-density integrability, exact subtraction, and normalized rescaling
  are proved rather than added as premises. This does not construct a jet
  from geometric admissibility.
- **`DimensionRodrigues.lean`:** the exact derivative identity for the
  recurrence polynomial and all necessary lower-endpoint jet limits/bounds.
  Odd fractional powers are differentiated on the positive domain, without
  assuming arbitrary-order smoothness at zero.
- **`DimensionSlice.lean` and `DimensionSliceMellin.lean`:** the actual
  squared-proper-time slice, including the integrable 2D endpoint singularity;
  odd exponential tails and all natural moments; the positive even fifth-power
  leading tail with seventh-power remainder; absolute slice moments through
  order three and failure at order four in even dimensions. Absolute Fubini
  is proved on its initial strip before complex Mellin continuation evaluates
  the four required signed moments. No divergent integral is assigned a
  continuation value. The alternative Abel proof is not claimed as formalized.
- **`DimensionActionConstants.lean`, `DimensionReduction.lean`, and
  `DimensionNormalizedKernel.lean`:** independent sphere/interval/point/pair
  coefficients, Gamma duplication and low-dimensional calibration; absolute
  tail-moment Fubini; equality of finite action and tail reductions; actual
  unit mass in every physical dimension; finite absolute first height moment,
  zero even signed first moment and strictly positive odd signed first moment.
  The regulated limit and fixed-observable Lipschitz error bound have no
  remaining normalization premise and require no second moment.
- **`DimensionReducedTail.lean`:** the actual negative even cubic leading
  tail with fifth-power remainder, strict positivity of its magnitude,
  eventual negativity, failure of second absolute and signed integrability,
  and divergence of the signed truncated second moment to negative infinity.
  Every natural absolute height moment is finite in odd dimensions.
- **`DimensionGeometry.lean`, `DimensionSpacetime.lean`, and
  `DimensionWedge.lean`:** canonical Euclidean product volume, genuine causal
  futures and squared proper time; full-partner weighted bilocal reduction,
  polar-to-squared-proper-time transport with the proved sphere factor,
  density scaling, and the actual regulated local action limit. Source weights
  may be signed and restrict only the first endpoint. The explicit bounded
  regulator leaves the supported source region unchanged; no regulator-removal
  or uniform zero-angle limit is asserted.
- **`DimensionFourCompatibility.lean`:** pointwise equality with the unchanged
  4D `planeKernel` at every nonnegative height, plus arbitrary-density vertical
  and weighted graph-cap action calibrations. Original 4D action files are
  unchanged.
- **Subsequent #91 finite geometry:** `DimensionCausalInterval`,
  `DimensionLorentz`, `DimensionIntervalVolume`, `DimensionActionTransport`,
  and `DimensionIntervalCompatibility` prove the closed/exclusive order-interval
  API, endpoint/null-pair nullity, actual rest-frame and arbitrary causal-pair
  volumes, restricted-volume equality under ambient causal convexity, ambient
  Lorentz and positive-dilation transport, and unchanged 4D coordinate/measure
  and full-action compatibility. See [the precise contracts and proof map](../formal/DIMENSION_INTERVALS.md).
  No probability identity or general induced-area theorem is inferred.

The final physical theorem's contract has **no mass, moment, convergence, or
integrability assumption**. Its hypotheses describe only the fixed slope,
regulator clearance, and continuous compactly supported source. Here `n` is the
tangential dimension, so `n = 0` includes physical dimension two:

```lean
theorem dimensionWeighted_wedge_limit (n : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (n + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (n + 1)
      (dimensionPointCoefficient (n + 2)) (dimensionPairCoefficient (n + 2))
      (dimensionIntervalCoefficient (n + 2)) ρ
      (dimensionGraphCap (dimensionWedgeRegulator n κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : DimensionSpatial n, w (dimensionWedgePoint 0 z)))
```

`dimensionWeighted_wedge_coth_limit` reformulates this using the existing
scalar rapidity identity. It is not a dimension-general Lorentz-geometric
assembly. The deterministic observable is independently defined. The separate
#77 bridge identifies its unweighted full-region version with an exact Poisson
expectation under ambient causal convexity; it does not supply a weighted
random-action theorem or global assembly.
Log-inserted derivative identities and the proposed geometric construction of
contract K in §3 are not included in the checked map above.

The kernel/local-coefficient `formal/Dimension*Regression.lean` files cover
low-dimensional polynomials and constants, nonunit density, cancellation, an independent toy
slice, the expanded actual mass integral, even/odd moments and divergence,
2D endpoint integrability, endpoint derivative jets, 4D compatibility, signed
weights, and a concrete nonzero 2D bilocal-action limit. The interval/transport
regressions additionally check general-dimensional contracts, joint
measurability, null intermediates, non-convex restricted volume, a translated
non-rest interval, parity, reciprocal dilation and exact 4D volume/action
conversion. The full audit checks all public declarations and their transitive
dependencies, not just these
examples. No admission, custom axiom, or global-limit proposition is assumed.

```sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
cd formal
./check.sh --incremental --base origin/main  # edit loop only
./check.sh                                 # full source and axiom audit
```

The symbolic checker includes independent finite-difference/Euler coefficients,
Gamma-recurrence Mellin factors, slice normalization and parity checks in
2–11, 20 and 21. Tests directly integrate signed transverse and logarithmic
moments and nonunit-density scaling, compare the original 4D kernel and plane
action, and calibrate 2D/4D diamonds from a separate interval series. Numerical
agreement is diagnostic only. Divergent moment requests are rejected, not
assigned analytic-continuation values. GitHub CI runs Python/Markdown checks;
it does not replace the local Lean audit or independent mathematical review.
