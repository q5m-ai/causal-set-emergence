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

## 1. Geometry, full observable, and corrected conclusion

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

This is a seven-dimensional G-SS region. The ambient product is smooth,
time-oriented, globally hyperbolic with compact Cauchy slices. The slab is
precompact, open and ambient causally convex. Its two entire boundary faces
are compact smooth spacelike slices; the joint is empty. It has no additional
boundary stratum. The independent scalar curvature, with #90's sign, is two,
so the proposed bulk-plus-joint target is the finite number VolM. No action
coefficient is used to define that target.

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
[dimension-kernels](dimension-kernels.md). In particular the last nonzero
moment is **not** one of the annihilated moments.

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
The separately justified finite-density Poisson expectation equality gives
the same statement for the expectation. No sample-wise conclusion follows.

The corrected statement is O3 for this actual G-SS member, and **not** a
universal finite bulk-plus-joint limit on G-SS in all dimensions. A general
replacement must account for caustic contributions; neither deleting cut sets
nor adding an unproved cancellation premise repairs the original quantifier.
We do not claim a universal renormalization or a new no-caustics core. §9 gives
native residual owners, preserving every original geometry in the record.

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
Choose a smooth cutoff in u equal to one near zero and supported in a small
fixed neighborhood of zero. Partition the full O4 domain into this origin
piece, the cut neighborhood of §4, and their exact complement. The positive
excess part has a positive minimum of W on its compact closure, hence an
exponentially small normalized response. The regular nearly-null remainder
is away from both theta=0 and theta=pi. O7 there has a positive fixed
nonconjugate margin, so the inverse in `(V/c7)^(2/7)` and its weighted primitive
have uniformly bounded derivatives of every fixed order. Integrating its
Taylor expansion on the remaining compact theta interval gives a polynomial
through degree three and `O(w^4)`, where `w=(v/c7)^(2/7)`. The origin cutoff
vanishes near its lower theta endpoint, so its artificial boundary is retained
without a singular contact. These remainder bounds are derived from the
exact Q formula, not from an assumption about smooth metric coefficients.

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
The remaining time weight is exactly

```math
\begin{aligned}
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

## 9. Acceptance and verification boundary

- **#151:** O3 is a written complete-action obstruction to the original
  all-dimensional G-SS conclusion, not a universal long-cancellation producer.
  G5–G7 still apply to every G-SS member; O9 exhibits an actual surviving
  residual. A general classification of caustic contributions and their
  critical-order remainders remains unproved. The smallest next step is
  independent checking of O9's matched subtraction, O12–O13's sign, and O15's
  complete point cancellation before changing the umbrella conjecture.
- **#81/#86:** own the corrected general coverage/assembly statement and its
  independent mathematical verification. O3 prevents consuming the old
  universal finite-limit target unchanged; it does not authorize silently
  restricting the core. No issue is closed by this note.
- **#150:** retains the general finite short bulk/face/joint producer. O16
  coordinates the actual leading short cancellation here; it neither supplies
  #150's general boundary terms nor presupposes them.
- **#149:** retains its flat geometric producer and normalization interface.
  **#152/#153:** retain the selected 4D sphere–circle complement/assembly;
  the 7D obstruction does not negate those bounded contracts.
- **#94/#86:** independent human review remains outstanding. No Lean source,
  checker, build input or dependency changes, and no fresh Lean audit is claimed.

`seven_dimensional_focusing.py` and its tests check the rational sign
certificate, independent profile integrals, actual antipodal interval and
regular-side formulas, both transition sides, time-contact restoration,
normalization and point cancellation. They do not turn finite quadrature
into proof of an asymptotic theorem. Reproduce together with the unchanged
accepted regressions:

```sh
.venv/bin/python -m unittest -v test_seven_dimensional_focusing test_full_partner_globalization test_sphere_circle_focusing
.venv/bin/python -m unittest -v
.venv/bin/python check_symbolic.py
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

The PR records actual local, CI and browser-rendering results separately.
There is no deployment, merge, sample-wise convergence claim, or automatic
closure of #151/#81/#24.
