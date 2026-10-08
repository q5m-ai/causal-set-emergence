# Shared dimensional producer interface (#149 / #150 / #151)

**Interface, not a general-metric theorem.** This freezes notation and exact
finite-density identities before the producer proofs. It changes no action,
probability law, geometric admissibility or Lean declaration. The normalization
is [the existing dimension kernel](dimension-kernels.md), and the geometry and
independent target are [G-SS](general-contract.md#3-a-precise-non-vacuous-general-core-candidate).
Written proofs, compiled proofs, diagnostics and independent human review are
separate. The integration base for this delivery is
`a64af01f518c859aa63417bb619022fe8b8ac4d8` on `issue-81-general-coverage`.

## 1. Constants and phase (every integer dimension at least two)

Put n=d-1, N=floor(d/2), m=N+1 and q=d/2. Sphere measure is ordinary area,
including **two counting atoms** when d=2. With unnormalized radial null
coordinates u=t-r, v=t+r, the immutable constants are

```math
\begin{aligned}
s_d&=\frac{2\pi^{(d-1)/2}}{\Gamma((d-1)/2)},&
c_d&=\frac{s_d}{2^{d-1}d(d-1)},&
g_d&=\frac{c_d^{2/d}}{\Gamma(1+2/d)},\\
a_{2N}&=4g_{2N},&
\frac{\beta_{2N}}{a_{2N}}&=\frac{\Gamma(N+2)\Gamma(N)}{\Gamma(2N)},\\
a_{2N+1}&=2g_{2N+1},&
\frac{\beta_{2N+1}}{a_{2N+1}}&=\frac{2N+2}{2^{2N}}.
\end{aligned}
```

Use the finite recurrence, not guessed moments or copied four-dimensional
coefficients:

```math
\begin{aligned}
P_{d,0}(z)&=1,&
P_{d,i}(z)&=P_{d,i-1}(z)+\frac{d}{2i}z(P'_{d,i-1}(z)-P_{d,i-1}(z)),\\
K_d(z)&=P_{d,m}(z)e^{-z},&
C_{k+1}^{(d)}&=k![z^k]P_{d,m}(z).
\end{aligned}
```

For the isolated selected order, V_M(x,y) is the actual restricted interval
volume, with both endpoints removed. Containment must be proved before
replacing it by ambient volume. Define a useful **volume phase**, not a
geodesic selection, by

```math
\sigma_M(x,y)=\left(\frac{V_M(x,y)}{c_d}\right)^{2/d},
\qquad K_d(\rho V_M)=K_d(c_d\rho\sigma_M^{d/2}).
```

Only in Minkowski space with discharged containment is this the squared
proper time. Zero curvature on a quotient does not prove that equality for
all partners. A general-metric pushforward in this phase is initially a
measure; existence or regularity of a density is a producer output.

## 2. Exact signed pieces and both endpoint partitions

Choose a fixed, density-independent geometric separation ell and a fixed
positive delta. For smooth bounded endpoint weights chi and phi set

```math
\begin{aligned}
P^{\lt\delta}_{\chi,\phi}(\rho)
 &=\int_{M\times M}\mathbf1_{\{x\preceq y,\ \ell(x,y)\lt\delta\}}
 \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
P^{\ge\delta}_{\chi,\phi}(\rho)
 &=\int_{M\times M}\mathbf1_{\{x\preceq y,\ \ell(x,y)\ge\delta\}}
 \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
S^\delta_{\chi,\phi}(\rho)
 &=a_d\rho^{2/d}\int_M\chi\phi\,d\mu_g
   -\beta_d\rho^{1+2/d}P^{\lt\delta}_{\chi,\phi}(\rho),\\
L^\delta_{\chi,\phi}(\rho)
 &=-\beta_d\rho^{1+2/d}P^{\ge\delta}_{\chi,\phi}(\rho),\\
A_{\chi,\phi}&=S^\delta_{\chi,\phi}+L^\delta_{\chi,\phi}.
\end{aligned}
```

The point is allocated to short **once**, with diagonal weight chi times phi.
In particular, for finite partitions summing to one on M, take the complete
ordered double sum over (i,j). Its diagonal weights also sum to one. No
same-chart restriction, no omission of cross-component pairs, and no extra
point per chart is allowed. Finite volume, bounded weights, bounded interval
volumes and the polynomial-exponential kernel give absolute integrability at
each fixed positive density, so these sums and signed Fubini are legitimate.

In the Minkowski producer ell=v. The time-only proposal from #150 and the
time-plus-spatial-distance proposal from #151 are **not identified**. For any
two short indicators I and I' the exact conversion is

```math
\begin{aligned}
E_{I,I'}(\rho)&=-\beta_d\rho^{1+2/d}
 \int_{M\times M}\mathbf1_{\{x\preceq y\}}(I-I')
 \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
S_I-S_{I'}&=E_{I,I'},&L_I-L_{I'}&=-E_{I,I'}.
\end{aligned}
```

There is no claim that E tends to zero. General-metric consumers must select
one common cutoff or retain this exact signed conversion and prove its
response. A local interval-containment lemma is required independently of
small volume. Neither candidate separation is made a shared manifold
definition by this document.

## 3. Actual flat densities and analytic acceptance signatures

In Minkowski coordinates z=(t,b), r=|b|, sigma=t squared minus r squared,
define the weighted overlap independently by integration over the actual
source and target. Polar/null change of variables gives

```math
\begin{aligned}
V_{\chi,\phi}(z)&=\int_M\chi(x)\mathbf1_M(x+z)\phi(x+z)\,dx,\\
j_d(\sigma,v)&=\frac{v^{d-3}}{2^{d-1}}
 (1-\sigma/v^2)^{d-2},\\
B^\lt_{\chi,\phi}(\sigma)&=
 \int_{S^{d-2}}\int_{\sqrt\sigma}^{\delta}j_d(\sigma,v)
 V_{\chi,\phi}\!\left(\frac{v+\sigma/v}{2},
                       \frac{v-\sigma/v}{2}\omega\right)\,dv\,d\omega,\\
B^\ge_{\chi,\phi}(\sigma)&=
 \int_{S^{d-2}}\int_{\max(\delta,\sqrt\sigma)}^\infty j_d(\sigma,v)
 V_{\chi,\phi}\!\left(\frac{v+\sigma/v}{2},
                       \frac{v-\sigma/v}{2}\omega\right)\,dv\,d\omega.
\end{aligned}
```

The short density is zero for sigma at least delta squared (not an oriented
integral). Both densities vanish for negative sigma. The formulas at positive
sigma are actual disintegrations; a value at zero is chosen separately if
needed. In 2D the short constant mode is logarithmically unbounded at zero:
**bounded short density is not a shared requirement**. Long at a fixed positive
cutoff is bounded and compactly supported for bounded M and bounded weights.

The signed Mellin law, derived from the recurrence by integration by parts, is

```math
\begin{aligned}
M_d(j)&=\frac2d\Gamma\!\left(\frac{2(j+1)}d\right)
 \prod_{i=1}^{N+1}\left(1-\frac{j+1}{i}\right),\qquad j>-1,\\
\int_0^\infty\sigma^jK_d(c_d\rho\sigma^q)\,d\sigma
 &=(c_d\rho)^{-2(j+1)/d}M_d(j).
\end{aligned}
```

The roots are j=0 through N. Log responses use the derivative in j, including
the density-log term until its coefficient is shown to vanish. An ordinary
bounded compactly supported density with a degree-N polynomial plus
little-o(sigma to power q) has zero normalized response. This is an **analytic
implication**, not a permitted geometric hypothesis. Critical fractional terms
in odd dimensions and critical logarithms in even dimensions can survive.

Required producer outputs, never admissibility fields:

- **Short:** actual density, geometrically obtained primitive derivatives and
  summable remainder, signed point cancellation, independent bulk/joint
  coefficient and all weight/partition fluxes. The total short coefficient
  need not be the target before companion fluxes are accounted for.
- **Long:** actual full-partner pushforward, critical signed response and
  domination. A zero limit must be proved; it is not part of this interface.
- **Assembly:** one common fixed cutoff, exact finite-density addition and
  cancellation of partition/cut fluxes, then the deterministic limit.
- **Expectation:** the independently constructed Poisson law and selected
  finite order, Borel order/intervals, finite atomless geometric volume,
  containment and the actual interval-volume identification. Apply the
  separate bridge only after the deterministic theorem.

## 4. Ownership and coverage boundary

#149's [written all-dimensional Minkowski theorem](all-dimensional-flat-limit.md)
supplies the actual flat producers and deterministic/expected assembly. It
derives graph coordinates from G-SS achronality and containment, with no
combined slope budget or global causal-envelope assumption.
#150 owns genuine metric short coefficients/remainders; #151 owns the
manifold nonlocal/atlas producer and compatible cutoff restoration. In
particular flat quotients with holonomy or multiple null routes are not
Minkowski regions merely because their curvature tensor vanishes. Their
complete-action estimates remain with #151/#81 unless separately discharged.

The written flat proof derives the sufficient finite-regularity bound
`r(d) = max(3, ceil(d/2)+1)` from its primitive and rectifying-Jacobian
derivative counts; it is not inferred from smoothness or asserted for the
historical C3 class in every dimension. The bounded 5D/6D written corollaries already in #132 are
calibrations, not new assembly progress. No formal port is introduced here;
new written/compiled gaps and independent human review remain visible to #86.

Refs #149, #150, #151, #81, #86, #24.
