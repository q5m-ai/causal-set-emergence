# A complete-action focusing obstruction in dimension seven (#151)

**Written result; not a Lean theorem or independent human review.** The
all-dimensional G-SS bulk-plus-joint conjecture fails for the unchanged action
on the smooth product below. We derive a positive leading contribution to the
**complete action**, after canceling its physical point term and restoring all
partners. This is not a conclusion from one transition sector, a failed
sufficient estimate, or a fitted asymptotic coefficient. The sign has an exact
rational certificate in §6. Finite numerical regressions are separate from
the proof. PR #159 remains draft for review and general-contract coordination;
#151/#81/#24 are not automatically closed.

The starting point is the actual signed pushforward
[G5–G7](full-partner-globalization.md#4-actual-pushforward-and-the-exact-unresolved-residual).
The uncontrolled contribution is the approach to the first null conjugate
locus. The accepted [4D sphere–circle argument](sphere-circle-focusing.md)
supplies an integrable cubic remainder there; its transverse powers depend on
dimension. We derive those powers anew, rather than assume that estimate in
7D or infer jets for weighted atlas cells.

## 1. Source crosswalk, actual geometry, and example-specific conclusion

### Published conjecture versus the repository's reconstructed predicate

The primary-source target is DLL's **Conjecture 1′**, not the name G-SS.
[DLL v1 §2.5, (11)](https://arxiv.org/html/2501.00139v1#S2.E11)
inherits the globally hyperbolic setting and retains the dimension-indexed
Einstein–Hilbert term while modifying the joint integrand. Its
[v2 §7.4, (68)–(69)](https://arxiv.org/html/2501.00139v2#S7.SS4)
explicitly addresses “d=3 and higher.” The dimensions of calculated examples
are not a restriction of this conjecture to 4D. The description of the paper's
Minkowski examples in §2.4 is likewise not a flatness premise of the general
curvature-bearing conjecture.

The [2020 predecessor §1](https://arxiv.org/html/2007.13206v2#S1)
defines an action for each integer dimension greater than one and states the
conjecture for globally hyperbolic finite-volume Lorentzian spacetimes. Its
[§3.2 slab](https://arxiv.org/html/2007.13206v2#S3.SS2) explicitly has compact
spatial circle slices, spacelike past and future boundaries and **“no joint.”**
Its curvature-order calculation (3.25) is evidence for the bulk-only target,
not a proved general fixed-curvature theorem. DLL changes the joint integrand,
not this empty-joint convention: the empty integral is zero, with no evaluation
of an angle at zero angle. None of these conjecture passages imposes a
no-caustics, simply-connectedness or small-normal-neighborhood condition.

[G-SS](general-contract.md#3-a-precise-non-vacuous-general-core-candidate)
is our precise **reconstruction of a smooth two-face subcase**, not a quotation
of a fully enumerated DLL predicate. The source statement is informal; the
specific slab below lies in both the published general setting and G-SS.
Its inclusion is therefore not an artifact of adding a source-excluded case.
This crosswalk fixes attribution; it changes neither conjecture's scope nor
any previously established restricted 4D result.

### Actual seven-dimensional instance

Fix `T=4`, `L=20`, and the unit round sphere. Write `VolX` for the actual
spatial volume and `VolM=T*VolX`. The geometry is

```math
\begin{aligned}
X&=S^2_1\times(\mathbb R/L\mathbb Z)^4,
&g&=dt^2-h_{S^2}-|db|^2,\\
M&=(-T/2,T/2)\times X,
&\mathrm{VolX}&=4\pi L^4,\qquad \mathrm{VolM}=4\pi L^4T.
\end{aligned}\tag{O1}
```

This is a seven-dimensional G-SS region. Its entire frontier consists of the
two closed smooth spacelike slices at times minus two and two. They are
individually achronal, have empty boundaries and empty intersection. Sphere
poles and torus fundamental-domain seams are coordinate artifacts, not extra
boundary strata; focusing is an interior interval phenomenon.

The complete compact Riemannian spatial product makes t a Cauchy time for the
ultrastatic ambient metric: spatial speed is at most time speed, so a causal
curve with a finite endpoint time has a spatial limit and can be extended.
The slab is also globally hyperbolic, with diamonds contained in compact time
intervals times X. **Separately**, if x and y are slab endpoints and z is in
any ambient causal interval between them, time monotonicity places t(z)
between t(x) and t(y), strictly inside the slab. This proves ambient interval
containment, including null relations, without a unique-geodesic assumption.
It also identifies intrinsic and restricted ambient orders.

The measures are induced geometric measures, not probability-normalized Haar
measures. On a sphere polar chart, the following calculation uses exactly
[#90's Riemann/Ricci sign](general-contract.md#curvature-sign-not-just-metric-signature):

```math
\begin{aligned}
g_{ab}&=\mathrm{diag}(1,-1,-\sin^2r,-1,-1,-1,-1),\\
\det g&=\sin^2r,\qquad
 d\mu_g=\sqrt{|\det g|}\,dt\,dr\,d\varphi\,d^4b
       =\sin r\,dt\,dr\,d\varphi\,d^4b,\\
\Gamma^r_{\varphi\varphi}&=-\sin r\cos r,\qquad
 \Gamma^\varphi_{r\varphi}=\Gamma^\varphi_{\varphi r}=\cot r,\\
\mathrm{Ric}_{rr}&=-1,\qquad
 \mathrm{Ric}_{\varphi\varphi}=-\sin^2r,\qquad R=2,\\
\frac12\int_M R\,d\mu_g&=\mathrm{VolM}=16\pi\,20^4,
 \qquad \int_{\varnothing}\coth\theta\,dA_g=0.
\end{aligned}\tag{O1a}
```

The remaining connection and Ricci components vanish. The polar expression
extends as the round sphere area measure; each quotient length measure has
mass L, so O1 follows by ordinary product integration. In particular, the
absolute determinant is used even though the seven-dimensional determinant
is positive. The independent finite target is VolM, not an action coefficient.

Use the existing dimension kernel and constants, with no redefinition of
order, exclusive intervals, action, or Poisson law:

```math
\begin{aligned}
c_7&=\frac{\pi^3}{2688},\qquad a_7=8\beta_7,
&\beta_7&=\frac{c_7^{2/7}}{4\Gamma(9/7)}>0,\\
\int_0^\infty z^{s-1}K_7(z)\,dz
 &=\Gamma(s)\prod_{j=1}^4\left(1-\frac{7s}{2j}\right),\quad s>0,\\
\int_0^\infty K_7(z)\,dz&=-\frac5{128},
&\mathcal A_{\rho,7}(M)&=a_7\rho^{2/7}\mathrm{VolM}
                  -\beta_7\rho^{9/7}P(\rho).
\end{aligned}\tag{O2}
```

These identities follow directly from the existing recurrence in
[dimension-kernels](dimension-kernels.md), and agree with
[Glaser (12)–(15)](https://arxiv.org/html/1311.1701v3#S0.E12).
Glaser's normalized-null-coordinate interval constant in (5) is
`2^(7/2)*c7`; converting it before using the odd-dimensional formulas gives
the constants in O2. Its five exclusive-layer weights are
`(1, -6307/128, 14749/64, -10633/32, 2401/16)`; for exclusive count
`k=0,...,4`, the polynomial coefficient is Glaser's `C_(k+1)` divided by `k!`. This is the unsmeared minimal-layer action,
with ordered distinct pairs, not a different observable or an unordered-pair
normalization. In particular the last nonzero moment in O2 is **not** one of
the annihilated moments. The source formula, rest-diamond volume and curvature
calculation have separate exact symbolic regressions.

**Theorem.** The complete deterministic action satisfies

```math
\begin{aligned}
\rho^{-2/7}\mathcal A_{\rho,7}(M)&\longrightarrow
 \gamma=\frac{5\beta_7}{128}\,C_{\mathrm{cut}}>0,\\
C_{\mathrm{cut}}&=\frac{2\pi\,\mathrm{VolX}\,G(\pi)}{3D}\,I,
& D&=\frac{16\pi}{3}(12-\pi^2),\\
G(u)&=\frac{\pi^2}{6}u(T-u)^3(T+3u),
&\frac1{400}&\lt I\lt\frac{13}{5000}.
\end{aligned}\tag{O3}
```

The constant I is defined and bounded in §§5–6, not fitted to the action.
Consequently the action diverges to positive infinity, rather than to VolM.

**Expectation specialization, in writing.** The spatial metric distance is
continuous, and ambient causality is the closed relation
`t(y)-t(x) >= distance_X(x,y)`. Reflexivity and transitivity follow from the
metric triangle inequality; causality in both directions forces equal times
and zero spatial distance, giving antisymmetry. The exclusive interval removes
only its two endpoints; its joint indicator on endpoint/intermediate triples
is Borel.
Integrating over the intermediate point against this finite geometric volume
makes the restricted interval volume Borel. Smooth volume is atomless. At fixed spatial target,
a null-related endpoint has one time value; time Fubini gives null pair
measure without deleting any neighborhood of the cut locus. The containment
argument above identifies these restricted intervals with the ambient ones.

These facts discharge, conventionally, the finite atomless measured-order
hypotheses of the existing checked generic theorem
[`BoundaryDraft.dimensionFiniteMeasureAction_expectation`](../formal/BoundaryDraft/DimensionMeasureExpectation.lean).
Specialize its dimension to seven and its finite measure to the actual volume
restricted to M, with intensity `ENNReal.ofReal rho • mu` for positive rho.
The independently defined Janossy Poisson law then has mean cardinality
`rho*VolM`. Each exclusive ordered layer count is bounded by squared
cardinality, whose finite Poisson moment justifies the finite signed sum.
The theorem identifies its expectation with O2 at every positive density;
O3 therefore transfers to expectation without interchanging expectation with
an unproved random limit. **No concrete 7D Lean instance has been compiled.**
This is a written geometric application of checked generic foundations, not
a fresh Lean audit, and it implies no sample-wise conclusion.

O3 replaces the finite-limit prediction **for this particular member**; it is
not #24's required corrected general theorem. The published conjecture and
the reconstructed G-SS target both predict a finite value here, which O3
contradicts at the conventional written-proof level. A general replacement
must account for caustic contributions; neither deleting cut sets nor adding
an unproved cancellation premise repairs the original quantifier. We claim
neither a universal renormalization nor a new no-caustics core. §9 retains the
native owners of that unresolved general work.

## 2. Exact two-measure reduction, with time contacts and all branches

Let theta be sphere endpoint distance, b the shortest flat displacement,
and tau the original time gap. Causality is `tau >= sqrt(theta^2+|b|^2)`.
Because `tau<T<L/2`, the entire interval has a unique lift in the four flat
factors, not merely convenient endpoint lifts. Two causal lifts would differ
by a lattice vector of length at least L but have combined length less than
2T. The lifted diamond projects injectively. There is no such unique-geodesic
claim on the sphere. Ambient containment justifies using the full interval.

A Lorentz boost in the lifted time/flat block gives
`u=sqrt(tau^2-|b|^2)` and preserves the actual interval volume. Write it W at
zero flat separation. With r,s the sphere distances of an intermediate point
to the endpoints, time Fubini gives

```math
\begin{aligned}
W(u,\theta)&=\int_{S^2}\int_{\mathbb R^4}
 \left(u-\sqrt{r^2+|z|^2}-\sqrt{s^2+|z|^2}\right)_+\,dz\,dA,\\
P(\rho)&=C\int_0^\pi\sin\theta\int_\theta^T
                G(u)K_7(\rho W(u,\theta))\,du\,d\theta,
& C&=2\pi\,\mathrm{VolX},\\
G(u)&=2\pi^2u\int_u^T(T-\tau)(\tau^2-u^2)\,d\tau.
\end{aligned}\tag{O4}
```

The last integral evaluates to O3. The source spatial factor is VolX, target
sphere factor is `2*pi*sin(theta)`, and integrating **both** endpoint times
produces `T-tau`. The flat radial measure is `2*pi^2*|b|^3 d|b|`.
Changing tau at fixed b and then integrating b yields the last line. Both
closing time contacts are therefore included. W counts spatial points,
not an overlapping sum of geodesic-indexed diamonds.

For later use the actual two-distance map from the sphere has the combined
two-orientation Jacobian

```math
\begin{aligned}
x&=r+s,\quad y=r-s,\quad
 \theta\le x\le2\pi-\theta,\quad -\theta\le y\le\theta,\\
J_\theta(x,y)&=\frac{\cos y-\cos x}
 {2\sqrt{(\cos y-\cos\theta)(\cos\theta-\cos x)}},\\
W_u(u,\theta)&=\frac{\pi^2}{32}
 \int_\theta^{\min(u,2\pi-\theta)}\int_{-\theta}^{\theta}
 J_\theta(x,y)\frac{(u^2-x^2)^2(u^2-y^2)^2}{u^4}\,dy\,dx.
\end{aligned}\tag{O5}
```

Indeed the allowed flat ball has squared radius
`(u^2-x^2)*(u^2-y^2)/(4*u^2)` and unit four-ball volume `pi^2/2`.
Integrate O5 in u from x to recover W. The Jacobian is the same geometric
sphere Jacobian as #139 F4; changing the number of flat directions does not
change it. It includes the secondary transition `u=2*pi-theta` and all
antipodal minimizing meridians. No derivative across that transition is
needed below. W is continuous and strictly increasing for `u>theta`.

Any finite endpoint atlas is first restored by the full ordered identity G4,
including its off-diagonal labels. O4 then applies to the aggregate. No
arbitrary weighted-cell estimate is inferred from rotational symmetry.

## 3. The actual focusing normal form and derived regular-side bounds

Put `theta=pi-a`, `e=u-theta`. For fixed `A>=0`, `S>-A`, the actual limit is

```math
\begin{aligned}
\lambda^{-3}W(\pi+\lambda S,\pi-\lambda A)
 &\longrightarrow D\,\frac1{2\pi}\int_0^{2\pi}
                             (S+A\cos\varphi)_+^3\,d\varphi,\\
F(S)&=\frac1{2\pi}\int_0^{2\pi}(S+\cos\varphi)_+^3\,d\varphi,\\
F(-1+h)&=c_*h^{7/2}H(h/2),
& c_*&=\frac{32}{35\sqrt2\pi},\\
H(x)&={}_2F_1(1/2,1/2;9/2;x),\quad 0\le h\le2,
&F(S)&=S^3+\tfrac32S\quad(S\ge1).
\end{aligned}\tag{O6}
```

Here is a geometric derivation. At an interior sphere polar radius r, moving
the second endpoint by lambda A from the antipode gives
`s=pi-r-lambda*A*cos(phi)+O(lambda^2)`. Rescale the four intermediate flat
coordinates by `sqrt(lambda)`. The divided positive part in O4 tends to
`(S+A*cos(phi)-pi*|z|^2/(2*r*(pi-r)))_+`; its measure factor is lambda cubed.
The endpoint Lipschitz bound and
`sqrt(r^2+|z|^2)+sqrt(s^2+|z|^2) >= sqrt((r+s)^2+4*|z|^2)` give a fixed
compact rescaled support and a bounded divided integrand. Dominated convergence
applies, uniformly on compact subsets of `S+A>0`. Integrating the flat ball
gives `pi^2/6` times the cube of the positive excess times
`(2*r*(pi-r)/pi)^2`. Thus
`D=(4*pi/3)*integral_0^pi sin(r)*r^2*(pi-r)^2 dr`, which evaluates to O3.
The polar endpoints are harmless for this dominated geometric limit; their
zero measure is not used to bound a normalized cut neighborhood.

For `h<2`, substituting `sin(phi/2)=sqrt(h/2)*t` gives O6's hypergeometric
formula. For `S>=1`, the whole circle is active and ordinary cosine moments
give its polynomial. In particular the transition at S=1 is retained.

We also need uniform estimates outside a compact rescaled transition sector.
They follow from the same **exact** regular-side sphere/Euclidean comparison
as #139 F8–F11, now integrated on the unit flat seven-dimensional diamond
`D7={|A0|+|B|<=1/2}`, with `B in R^6`. Explicitly,

```math
\begin{aligned}
W(\theta+e,\theta)&=e^{7/2}H_0(a,e),\\
H_0(a,e)&=(2\theta+e)^{7/2}\int_{D_7}Q_\theta(r(e),s(e))\,dA_0\,dB,\\
Q_\theta(r,s)&=\frac{\mathrm{sinc}(r)\mathrm{sinc}(s)}
 {\sqrt{\mathrm{sinc}((r+s+\theta)/2)\mathrm{sinc}((r+s-\theta)/2)
 \mathrm{sinc}((\theta+r-s)/2)\mathrm{sinc}((\theta-r+s)/2)}},\\
r(e)^2&=(\theta\ell+eB_1)^2+(2\theta e+e^2)B_2^2,\\
s(e)^2&=(\theta(1-\ell)-eB_1)^2+(2\theta e+e^2)B_2^2,
&\ell&=\tfrac12+A_0+B_1.
\end{aligned}\tag{O7}
```

This is an exact change of variables for `0<e<2a`, not a model interval. The
sphere two-distance map and its Euclidean-plane counterpart each have two
orientations. Their ratio is Q; the other four directions and time are
unchanged. The flat Lorentz/dilation determinant is `e^(7/2)*(2*theta+e)^(7/2)`.

For clarity, the dimension extension in the bound is justified as follows.
On D7, `0<=ell<=1` and `B2^2<=ell*(1-ell)`, exactly as on #139's D0. On a
common complex disk `|e|<c*a`, r and s stay within `C*|e|` of their values at
zero. The four denominator sinc arguments are initially
`theta,0,theta*ell,theta*(1-ell)`, at least a from a nonzero sine zero.
Their product is entire and even separately in r and s; square-root
ambiguities at a focal endpoint are removable in `r^2,s^2`. The nonvanishing
product has its positive-at-zero holomorphic square root on that disk.
At zero Q is
`sqrt(sinc(theta*ell)*sinc(theta*(1-ell))/sinc(theta))`.
Its integral is comparable to `a^(-1/2)`, using an interior positive-volume
part of D7 for the lower bound. Complex comparison and Cauchy estimates,
followed by decreasing a fixed eta, give

```math
\begin{aligned}
h(a,e)&=\sqrt a\,H_0(a,e),\qquad
 0\lt c_0\le h(a,e)\le C_0,\\
|\partial_e^j h(a,e)|&\le C_j a^{-j}
 \quad(0\le e\le\eta a),\\
c\frac{e^{7/2}}{\sqrt{a+e}}&\le W(\pi-a+e,\pi-a)
                  \le C'\frac{e^{7/2}}{\sqrt{a+e}}
 \quad(0\le a\le a_0,\ 0\lt e\le e_0).
\end{aligned}\tag{O8}
```

Any fixed finite number of derivatives is available; four suffice here.
For the last line use the first lines for `e<=eta*a`. For the intermediate
range `eta*a<=e<=4a`, use monotonicity at eta a and the antipodal upper bound.
For `e>=4a`, both antipodal endpoint-Lipschitz comparisons apply:
`W(pi+e-2a,pi)<=W(pi-a+e,pi-a)<=W(pi+e,pi)`, with
`W(pi+v,pi)~D*v^3`. This proves the bound through both the secondary transition
and the meridian regime. Choose a0,e0 fixed and small with `pi+e0<T`.

## 4. Derived averaged remainder: the surviving term

Use **volume phase v**, not the auxiliary G5 phase, in this section. Let E(a,v)
be the actual root `W(pi-a+E,pi-a)=v`. For small fixed v this root is below
e0 for every a in `[0,a0]`, by O8. The complete cut-neighborhood primitive is

```math
\begin{aligned}
f(a,v)&=\int_0^{E(a,v)}G(\pi-a+e)\,de,\\
N_{\mathrm{cut}}^V(v)&=C\int_0^{a_0}\sin a\,f(a,v)\,da,\\
N_{\mathrm{cut}}^V(v)&=b_1v^{2/7}+b_2v^{4/7}+b_3v^{6/7}
                          +C_{\mathrm{cut}}v+o(v).
\end{aligned}\tag{O9}
```

We prove the last line, including its remainder; it is not an input. Set
`zeta=v^(2/7)`. The analytic inverse of
`zeta/a^(6/7)=(E/a)*h(a,E)^(2/7)` is uniform near zero. Taylor expansion of
that constructed inverse and of the actual integral f gives coefficients
c_j(a), j=1,2,3, with

```math
\begin{aligned}
|c_j(a)|&\le C_j a^{1-6j/7},\qquad
 b_j=C\int_0^{a_0}\sin a\,c_j(a)\,da,\\
\left|f(a,v)-\sum_{j=1}^3c_j(a)\zeta^j\right|
 &\le C\zeta^4a^{-17/7}
 \quad(\zeta\le\kappa a^{6/7}),\\
E(a,v)&\le C\left(a^{1/7}v^{2/7}+v^{1/3}\right).
\end{aligned}\tag{O10}
```

The coefficient integrals converge: after multiplying by sin a the worst
power is `a^(-4/7)`. The fourth-order remainder has power `a^(-10/7)` after
that multiplication, **not integrable down to zero**. Unlike in 4D, ordinary
termwise critical Taylor integration is therefore not justified.

Instead subtract the three actual integrable coefficients and set
`lambda=v^(1/3)`, `a=lambda*t`. Divide the resulting integral by v. For large
t the second line of O10 bounds its integrand by `C*t^(-10/7)`. For bounded
t, the last line and the coefficient bounds give the integrable envelope
`C*(t+t^(8/7)+t^(2/7)+t^(-4/7))`. These are independent of v; the moving upper
limit `a0/lambda` is handled by extending the integrand by zero. This is the
required **derived, summable averaged remainder estimate**, not finite-density
domination or a declaration that the cut has measure zero.

O6 identifies the scaled inverse: E divided by lambda tends to
`t*(1+F^(-1)(1/(D*t^3)))`. Its first three large-t coefficients are the limits
of `a^(6j/7-1)*c_j(a)/G(pi)`. To justify convergence of those derivatives,
O7–O8 give a uniformly bounded holomorphic family `h(a,a*z)` on a fixed disk.
O6 identifies its limit on a real interval inside that disk as
`D*F(z-1)/z^(7/2)`, which extends analytically at zero by O6. Compactness of
bounded holomorphic families, uniqueness on that interval and Cauchy's
formula give convergence of all derivatives on smaller disks. The uniform
analytic inverse gives the asserted coefficient limits. No differentiation
across the secondary transition is involved.

Dominated convergence in the rescaled, subtracted integral now proves O9.
It also reduces its coefficient to a convergent matched integral. The next
section evaluates that integral, including the regular-side subtraction;
keeping only a fixed transition sector would give a different coefficient.

## 5. Exact matched coefficient, not a transition-sector fit

For a finite upper endpoint m of the rescaled a integral, Tonelli gives

```math
\begin{aligned}
\int_0^m t^2\left[1+F^{-1}\left(\frac1{Dt^3}\right)\right]dt
 &=\frac13\int_{-1}^\infty
             \min\left(m^3,\frac1{DF(S)}\right)dS.
\end{aligned}\tag{O11}
```

The integral is finite for each m. The right side splits at
`h_m=1+F^(-1)(1/(D*m^3))`. Its first term is `m^3*h_m/3`; the second is the
integral of `1/(3D*F)` from `-1+h_m` to infinity. O6 implies that h_m has a
convergent series in `m^(-6/7)` near infinity. Subtracting the first three
powers `m^(3-6j/7)` is exactly the subtraction in §4. No constant power is
present in those series, since `3-6j/7=0` has no integer solution j. The
remaining constant is `I/(3D)`, where the following **ordinary convergent
integral plus explicit subtraction terms** defines I:

```math
\begin{aligned}
R(x)&=H(x)^{-1},\quad r_1=-\frac1{18},\quad r_2=-\frac{59}{7128},\\
I&=\frac{\log(5/2)}3+\frac{35\pi}{128}
 \left[\int_0^1\frac{R(x)-1-r_1x-r_2x^2}{x^{7/2}}\,dx
       -\frac25-\frac23r_1-2r_2\right].
\end{aligned}\tag{O12}
```

The subtraction coefficients are the first two Taylor coefficients of the
actual H inverse. The subtracted integrand is `O(x^(-1/2))`, hence integrable.
The first term is the exact integral of `1/(S^3+3*S/2)` over `[1,infinity)`.
The prefactor follows from `h=2x` and c-star in O6. Equivalently I is the
finite part of the full integral of `1/F` from -1 to infinity, but O12 fixes
that meaning without analytic continuation or an arbitrary subtraction
constant. Multiplying by `C*G(pi)` proves C_cut in O3. The entire matching
wedge adjacent to S=-1 and the unbounded meridian side are both included.

## 6. Positive sign by rational inequalities

Here is a reproducible exact certificate for the inequality in O3. Write
`H(x)=1+A(x)`, with positive rational coefficients
`a_n=(1/2)_n^2/((9/2)_n*n!)`. The beta integral or O6 at S=1 gives
`H(1)=175*pi/512`. Thus `0<=A(x)<=a*x` on `[0,1]`, with `a=3/40`.
Take `N=32`, `A_N=sum_(n=1)^N a_n*x^n`, and
`Q_N=1-A_N+A_N^2-A_N^3+A_N^4`. Its constant, linear and quadratic coefficients
are exactly those subtracted in O12. Let q_l denote all its rational
coefficients, and set

```math
\begin{aligned}
J_N&=\sum_{l=0}^{128}\frac{2q_l}{2l-5},\\
\Delta_N&=\frac{175\pi_+}{512}-1-\sum_{n=1}^{32}a_n,\\
\varepsilon_N&=\frac{a^5}{5-5/2}+\frac{\Delta_N}{32-3/2},\\
J_N-\varepsilon_N&\le
 \int_0^1\frac{R(x)-1-r_1x-r_2x^2}{x^{7/2}}\,dx
              -\frac25-\frac23r_1-2r_2
 \le J_N.
\end{aligned}\tag{O13}
```

Here pi-plus is an upper rational bound on pi. Proof: the positive coefficient
tail obeys `0<=A-A_N<=Delta_N*x^(N+1)`. The derivative of
`Q(z)=1-z+z^2-z^3+z^4` is between -1 and zero on `[0,3/40]`, and
`Q(A)-1/(1+A)=A^5/(1+A)`. Hence
`0<=Q(A_N)-R<=Delta_N*x^(N+1)+a^5*x^5`. Integrating after the common
quadratic subtraction gives O13. All denominators in J_N are nonzero.

For completeness the implementation obtains pi bounds from Machin's identity
`pi=16*atan(1/5)-4*atan(1/239)`, using 24 terms and the alternating-series
error. Bounds for `log(5/2)` use the first 24 terms of
`2*sum (3/7)^(2j+1)/(2j+1)` and its positive geometric tail bound. Combining
these rational bounds with O13 and `35*pi/128`, observing that both endpoints
for J are negative, gives **strictly** `1/400<I<13/5000`. Every operation in
that certificate uses Python `Fraction`; floating quadrature is not the sign
proof. Independent quadrature gives about `0.00255956`, only as a regression.
The certificate bounds are deliberately much wider than numerical precision.

## 7. Complete complement and the physical point cancellation

It remains essential to prove that no other actual pair sector cancels O9.
Choose a smooth cutoff chi(u) between zero and one, equal to one near zero
and supported below a small fixed u0. Let the origin primitive use this weight in the actual O4
sublevel measure. Partition the full O4 domain into this origin
piece, the cut neighborhood of §4, and their exact complement. The positive
excess part has a positive minimum of W on its compact closure, hence an
exponentially small normalized response. The regular nearly-null remainder
is away from both theta=0 and theta=pi. O7 there has a positive fixed
nonconjugate margin, so the inverse in `(V/c7)^(2/7)` and its weighted primitive
have uniformly bounded derivatives of every fixed order. Integrating its
Taylor expansion on the remaining compact theta interval gives a polynomial
through degree three and `O(w^4)`, where `w=(v/c7)^(2/7)`. The **complementary
weight `1-chi(u)`** vanishes near the origin, hence near the lower theta
endpoint of this regular small-phase complement. Its artificial boundary is
retained without a singular contact. These remainder bounds are derived from
the exact Q formula, not from an assumption about smooth metric coefficients.

Here is the complete origin coefficient. In the small-u range, the same exact
comparison gives
`W=c7*(u^2-theta^2)^(7/2)*B(u^2,theta^2)`, where B is real analytic near
zero and `B(0,0)=1`. To see this evenness, Q is analytic separately in
`r^2,s^2,theta^2` near zero; the boosted r-squares are polynomials in u,theta.
Integration on D7 is invariant under either sign change of u or theta by
reflection of B1. The resulting analytic function is therefore analytic in
their squares. This also constructs its extension across `u=theta`.

Put `X=u^2`, `Y=theta^2`. The analytic inverse of
`w=(X-Y)*B(X,Y)^(2/7)` is `Y=Y(X,w)` with
`-Y_w(0,0)=1`. The lower u endpoint is
`u_min(w)=sqrt(w+O(w^2))`. Pushing `sin(theta) dtheta` forward gives the actual
density factor `A(X,w)=-sinc(sqrt(Y))*Y_w/2`, analytic with `A(0,0)=1/2`.
Here `B_origin` denotes the **pushed density**, not the primitive. At small
positive w its definition and the remaining exact time weight are

```math
\begin{aligned}
B_{\mathrm{origin}}(w)
 &=\frac{d}{dw}N_{\mathrm{origin}}^V(c_7w^{7/2})
   =C\int_{u_{\min}(w)}^{u_0}\chi(u)G(u)A(u^2,w)\,du,\\
G(u)&=g_1u+g_3u^3+g_4u^4+g_5u^5,
&g_4&=\frac{4\pi^2T}{3},\\
B_{\mathrm{origin}}(w)&=B_{\mathrm{analytic}}(w)
                   -\frac{Cg_4}{10}w^{5/2}+O(w^{7/2}),\\
N_{\mathrm{origin}}^V(v)&=\sum_{j=1}^3d_jv^{2j/7}
               -\frac{1024}{5}\mathrm{VolM}\,v+o(v).
\end{aligned}\tag{O14}
```

Indeed each odd-u term times A integrates analytically in `X=u^2`, including
its analytic moving lower endpoint. The even term `g4*u^4` has missing lower
integral `g4*w^(5/2)/10`; terms from `A-1/2` or the corrected lower endpoint
have order at least `w^(7/2)`. The smooth u cutoff is one there; its transition
part has a smooth Taylor remainder and creates no fractional term. Integrating
the displayed density in w gives `-C*g4*w^(7/2)/35`, which equals the last
line since `v=c7*w^(7/2)`. Analytic fourth-order terms are `o(v)` and retained
in that remainder. Both endpoint measures and the `T-tau` closing contact
are indispensable to this coefficient.

Thus the **complete** positive sublevel primitive, in volume phase, is

```math
\begin{aligned}
N^V(v)&=\sum_{j=1}^3e_jv^{2j/7}
       +\left(-\frac{1024}{5}\mathrm{VolM}+C_{\mathrm{cut}}\right)v+o(v),\\
\rho P(\rho)&\longrightarrow
       8\,\mathrm{VolM}-\frac5{128}C_{\mathrm{cut}}.
\end{aligned}\tag{O15}
```

The remainder divided by v is bounded near zero, as proved separately for
each piece above. Use the exact Stieltjes identity, subtract the first three
powers and rescale `v=z/rho`. O2 annihilates these three powers; their fixed
positive-phase tails are exponentially small. The remainder has the
integrable dominator `z*|K7'(z)|`; dominated convergence gives the second
line with the actual nonzero moment in O2. Finite pair measure handles the
remaining positive-phase domain. Finally `a7=8*beta7` cancels the physical
point term **exactly at this order**, leaving O3. This completes the
action-level obstruction rather than just a long-sector diagnostic.

## 8. Shared temporal cutoff, signs, and the accepted regressions

Fix any sufficiently small `0<delta<pi-a0`, as in #150's locality choice.
The strict-short and equality-long weights after the same exact reduction are

```math
\begin{aligned}
G_{\mathrm{short},\delta}(u)
 &=\mathbf1_{\{u\lt\delta\}}\,2\pi^2u
                      \int_u^\delta(T-\tau)(\tau^2-u^2)\,d\tau,\\
G_{\mathrm{long},\delta}(u)&=G(u)-G_{\mathrm{short},\delta}(u),\\
\rho^{-2/7}S^\delta(\rho)&\longrightarrow0,
&\rho^{-2/7}L^\delta(\rho)&\longrightarrow\gamma.
\end{aligned}\tag{O16}
```

T remains four, not delta. The weight is zero for `u>=delta` in the first
line, including its closing contact. On the cut neighborhood the short
weight is identically zero. Near u=0 its `u^4` coefficient is the same g4 as
in O14; subtracting it from G leaves only odd powers u and u cubed. Therefore
the actual short piece has exactly O14's point coefficient, whereas long has
no such origin coefficient and retains C_cut. Elsewhere the fixed-u weight,
including the contact at delta, is integrable; the phase inverse is uniformly
regular, so differentiation of that inverse does not differentiate or discard
the time contact. The same compact remainder argument proves O16.

The sign is the existing `L=-beta7*rho^(9/7)*P_long`; since the kernel moment
is negative and C_cut positive, L's leading coefficient is positive. O16
claims only the displayed leading scale, not a finite short curvature limit.
It rules out cancellation of this long term by the actual short action.
#149's radial-null cutoff is not available globally as a preferred coordinate
on this geometry. Wherever masks are compared, the opposite-signed G2 overlap
correction remains exact; no limit of that correction is assumed zero.

The 4D sphere–circle proof remains valid: its inverse coefficients have
powers `a^(1-3j/4)` and its actual cubic remainder has integrable endpoint
majorant `a^(-1/4)`. Here the inverse exponent is `6/7`, and the first
nonintegrable next-order endpoint power is `a^(-10/7)`. The matched primitive
scale is `v` in 7D, versus `v^2` for the 4D transverse transition scaling.
This does not change the accepted 4D F16/F18 result or complete its complement.
The all-dimensional thin-torus producer has no such loss of inverse margin;
its G9 estimate, including dimension seven, remains an independent regression.
Neither result substitutes for the complete-action argument above.

### Exact local coefficient regression and the pinned short comparison

The [asymptotics AI report](https://github.com/q5m-ai/causal-set-emergence/pull/159#issuecomment-6059885505)
also derived the next local coefficients independently of PR #158's general
short theorem. They are now exact algebraic regressions, not fitted density
jets. Expanding the actual sinc ratio in O7 gives quadratic term
`(theta^2-r^2-s^2)/12`. Integration on the unit D7 gives the independently
integrated normalized moments `E[A0^2]=1/144` and `E[B_i^2]=7/288`. Substitution
in the same local inverse and pushed density of §7 yields

```math
\begin{aligned}
B(X,Y)&=1-\frac7{864}X+\frac{77}{1728}Y
                  +O((|X|+|Y|)^2),\\
A(X,w)&=\frac12-\frac{17}{192}X+\frac{83}{864}w
                  +O((|X|+|w|)^2),\\
X_{\min}(w)&=w+\frac{w^2}{432}+O(w^3),\\
B_{\mathrm{origin}}(w)&=B_{\mathrm{analytic}}(w)
 -\frac{Cg_4}{10}w^{5/2}-\frac{Cg_4}{140}w^{7/2}+O(w^{9/2}),\\
\int_0^\infty z^{7/2}K_7(z^{7/2})\,dz
 &=\frac5{64}\Gamma(9/7).
\end{aligned}\tag{O17}
```

For the new fractional coefficient, the lower-endpoint shift contributes
`1/1728`, the X coefficient contributes `-17/1344`, and the w coefficient
contributes `83/4320`; their sum is `1/140`. With the actual c7 and beta7,
this term has finite short-action coefficient VolM, while the earlier term
cancels the point. Both coefficients are unchanged when G is replaced by the
actual small-temporal-cutoff weight in O16: its even `u^4` coefficient is the
same and full minus short has only odd powers. These exact local checks do
not numerically certify the analytic remainder or a general short theorem;
the main O3 proof still uses only O14–O16's leading-scale cancellation.

The comparison is specifically with
[PR #158, S30–S31 at `0208f7caa8cafad594842dd7eab551586c598ce5`](https://github.com/q5m-ai/causal-set-emergence/blob/0208f7caa8cafad594842dd7eab551586c598ce5/notes/general-metric-short-remainders.md#8-quantified-short-theorem-partition-cancellation-and-the-151-boundary).
That pin predicts the finite short value VolM for this instance, consistent
with the independent coefficient calculation. PR #158 subsequently advanced
and was integrated; neither this comparison nor the AI report is an audit of
its later head or of every step of its general short theorem. No result of
PR #158 is used to prove O3, and no macroscopic cutoff overlap is discarded.

## 9. Acceptance and verification boundary

- **#151:** O3 is a written complete-action obstruction both to the published
  finite-target conjecture on this instance and to its reconstructed G-SS
  prediction, not a universal long-cancellation producer. G5–G7 still apply to
  every G-SS member; O9 exhibits an actual surviving residual. The issue's
  obstruction delivery alternative is distinct from its positive general
  producer. General caustic classification and critical-order remainders remain
  explicitly owned by #151, with the replacement general theorem under
  #24/#81/#86. The two AI cross-checks support the written argument but do not
  replace outstanding human expert checking before any umbrella revision.
- **#81/#86:** own the corrected general coverage/assembly statement and its
  independent mathematical verification. O3 prevents consuming the old
  universal finite-limit target unchanged; it does not authorize silently
  restricting the core. No issue is closed by this note.
- **#150 / PR #158:** own the general finite short bulk/face/joint producer.
  O16 and the exact O17 regressions coordinate this instance's short terms;
  they neither supply nor audit every general boundary term. The comparison
  pin and its limitations above remain explicit.
- **#149:** retains its flat geometric producer and normalization interface.
  **#152/#153:** retain the selected 4D sphere–circle complement/assembly;
  the 7D obstruction does not negate those bounded contracts.
- **#94/#86:** independent human review remains outstanding. No Lean source,
  checker, build input or dependency changes, and no fresh Lean audit is claimed.

`seven_dimensional_focusing.py` and its tests check the rational sign
certificate, independent profile integrals, actual antipodal interval and
regular-side formulas, both transition sides, time-contact restoration,
normalization and point cancellation. The repair additionally differentiates
O7 for the actual primitive coefficients, solves actual interval-volume roots,
and integrates the **subtracted actual cut primitive**, with several fixed
(a0,e0) neighborhoods. Its rescaled panels cover the full finite interval
`0<=t<=a0/v^(1/3)`, including the small-t meridian tail, both transition sides
and the large-t opening/matching wedge. No limiting profile is substituted
for an uncomputed tail. Panel/refinement comparisons are finite diagnostics,
not certified quadrature errors, uniform tail bounds or convergence rates.
Negative controls omit O11's matching term, an actual sphere sheet, opening
or meridian panels, or the physical point. Exact local O17 coefficients are
separate symbolic regressions. None of these tests proves an asymptotic theorem.

For reproducibility, the coarse residual diagnostic uses 12 nodes per panel,
24-point diamond rules and 48-point interval rules. It returns the subtracted
primitive divided by `C*G(pi)*v`, with `v=lambda^3`. Representative results are:

| Fixed `(a0,e0)` | lambda 0.004 | lambda 0.001 | lambda 0.00025 |
| --- | ---: | ---: | ---: |
| `(0.06,0.10)` | 0.0000330300 | 0.0000289268 | 0.0000266567 |
| `(0.12,0.16)` | 0.0000247940 | 0.0000243800 | 0.0000241538 |
| `(0.18,0.22)` | 0.0000085392 | 0.0000154022 | 0.0000191461 |

The matched coefficient in these units is approximately 0.0000239021.
The different finite-phase corrections are retained, not fit away. A refined
16/32/64 rule is also compared at the middle neighborhood's smallest phase.
The test integrates every panel to its actual upper endpoint, which reaches
720 at the smallest phase in the largest neighborhood; dropping either the
opening or meridian part fails even the deliberately broad finite comparison.
This table certifies neither tail domination nor a sign or convergence rate.

Reproduce together with the unchanged accepted regressions:

```sh
.venv/bin/python -m unittest -v test_seven_dimensional_focusing test_full_partner_globalization test_sphere_circle_focusing
.venv/bin/python -m unittest -v
.venv/bin/python check_symbolic.py
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
git diff --check origin/issue-81-general-coverage...HEAD
```

The PR records actual local, CI and browser-rendering results separately.
There is no deployment, merge, sample-wise convergence claim, or automatic
closure of #151/#81/#24.

## 10. One-batch AI-report dispositions

Both the [contract/geometry/normalization report](https://github.com/q5m-ai/causal-set-emergence/pull/159#issuecomment-6059923291)
and the [complete-action asymptotics report](https://github.com/q5m-ai/causal-set-emergence/pull/159#issuecomment-6059885505)
reviewed `db691421624f0e598fe9e80a660cccaac4db499a`. The complete reports and
all five embedded scripts were read; all five were replayed successfully,
including the independent N=16 and N=40 rational enclosures and the actual
subtracted-integrand samples. The three published contract-script checksums
matched. Primary-source passages were also retrieved and read directly.
These are **AI cross-checks of conventional mathematics**, not human expert
review, a formal certificate of the asymptotics, or automatic merge approval.

| Finding / report location | Explicit disposition |
| --- | --- |
| Contract §1 and required repair 1: source scope and G-SS attribution | **Repaired:** §1 cites DLL (11)/(68), the general-dimensional passages and the predecessor's empty-joint slab; G-SS is expressly a reconstruction, not a quotation. No source or conjecture scope changed. |
| Contract §2 and required repair 2: actual geometry, containment, induced measures and curvature | **Repaired:** §1 proves containment separately from GH, computes the volume and signed Ricci contraction in O1a, and retains the full frontier. An exact metric regression was added. |
| Contract §3: action, layer/factorial/interval normalization and Poisson law | **Accepted; retained:** O2 is unchanged; primary Glaser coefficients now have an exact regression. The checked generic expectation theorem is named and its actual 7D hypotheses discharged in writing; no compiled 7D instance is claimed. |
| Contract §4: full partners, matching, rational sign and physical point cancellation | **Accepted; retained:** no change to the O4–O15 argument. Independent arithmetic was replayed; stronger actual-primitive regressions were added without making them proof premises. |
| Contract required repair 3; asymptotics correction 2: density notation | **Repaired:** O14 explicitly defines B_origin as the derivative of the volume primitive after phase conversion, with its selected origin cutoff. No coefficient changed. |
| Contract required repair 4; asymptotics correction 3: whitespace receipt | **Repaired:** O11's trailing space is removed. Validation checks the entire base-to-head PR range, not only a clean working tree. The earlier working-tree-only receipt was insufficient. |
| Asymptotics §1: lifted whole interval, endpoint measures and sphere branches | **Accepted; retained:** both orientations, the secondary transition, all flat partners and both time contacts remain; sheet-omission controls now fail explicitly. |
| Asymptotics §§2–3: matched dominator, coefficient limits, O11 boundary term and sign | **Accepted; retained:** no substantive proof step changed. Derivative-derived coefficients and actual roots exercise opening, transition and meridian regimes; the matching-term omission control is retained. |
| Asymptotics §4 and correction 1: complement cutoff wording | **Repaired:** §7 now refers to the complementary weight `1-chi(u)` vanishing near the origin. The origin weight still equals one there; the intended complement estimate is unchanged. |
| Asymptotics §4: complete point cancellation and density exponent | **Accepted; retained:** O15 and the exponent in O3 are unchanged. Negative controls omit the physical point or half the endpoint measure. |
| Asymptotics §5: independently derived local short coefficients and PR #158 comparison | **Added as exact regressions:** O17 follows from the sinc ratio, independently integrated diamond moments and signed kernel moment. The comparison remains pinned to `0208f7caa8cafad594842dd7eab551586c598ce5`, not the later head or an audit of its general theorem. |
| Asymptotics §6: expectation and verification boundary | **Accepted; clarified:** §1 gives the actual specialization. Generic Lean foundations, written application, numerical diagnostics and human review are separately labeled. |
| Asymptotics decisive-regression request | **Implemented:** the actual subtracted cut primitive is integrated for three fixed neighborhoods and three phases, with full rescaled panel coverage and rule refinement; missing matching, sphere-sheet, tail and point contributions have negative controls. |
| Both reports: positive verdict, no substantiated fatal gap, and limitations | **Recorded as AI evidence only:** O3 remains example-specific. No novelty/exhaustive-provenance claim, human approval or general replacement theorem follows. Human review remains #94/#86; general classification remains #151 and corrected umbrella assembly #24/#81/#86. |

**Repair scope:** the O3 asymptotic and its O4–O15 proof chain are preserved.
The changes clarify attribution, specialize already used geometric hypotheses,
correct notation and a cutoff sentence, and strengthen diagnostics. O17 is an
additional local coefficient calculation, not a new premise for O3. There is
no materially changed leading-divergence step requiring a renewed automatic
full review. Outstanding human expert review is still required; any later
material change should request review of that changed step specifically.

**Delivery assessment:** the example-specific obstruction is the alternative
deliverable in #151, not completion of its positive universal-producer route.
After final-head validation this repair can be reviewed on that basis without
pretending the unresolved general classification is discharged. PR readiness
is distinct from completion or closure of #151/#81/#24. This batch does not
change the draft flag or conjecture predicate; final receipts and the readiness
assessment are published on the PR, without another review/repair loop.
