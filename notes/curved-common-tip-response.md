# Complete curved response of the SE6 cusp (#156)

**Conventional written proof, not independent acceptance or new Lean coverage.**
Starting head: `a377b05ae622d9fdc24035fb591cb1f8ba6d5d8e`; existing branch
`issue-156-general-null-accounting`, target `issue-81-general-coverage`.
[Required coverage §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt)
remains the single original-item crosswalk. No definition, order, law, physical
cutoff, parent acceptance or theorem ownership changes.

**Result.** The actual SE1 cusp with the fixed density `A(t)=1+t*t` has the
complete finite half-curvature plus conformal outer-screen limit. There is
**no additional charge on its shared generator or either cusp end**. The
proof retains every macroscopic past partner. The false exponential identity
is replaced by a signed profile with an integrable tail and a derived mass.
The same mechanism proves the three-dimensional conformal common-past-tip
class below, for arbitrary smooth positive spacetime density and arbitrary
opposite past-set exits. It is not a general intrinsic-union theorem.

## 1. Audit of SE3–SE7 and the exact curved input

[SE3–SE5](null-singular-end-audit.md#4-route-two-a-complete-signed-fibre-theorem-including-both-cusp-ends)
use the stronger **whole partner fibre**, not causal convexity alone. Past-set
membership puts every interior point between a and q back in the region.
The bounding cones and endpoints are volume-null; the discrete order remains
closed. ND's signed dimensional response and its finite mass justify SE4's
bounded coarea argument, including arbitrary measurable exit radii. The
single direction through b changes no angular integral in three dimensions.
The flat proof is not reused with a substituted curved interval volume.

For SE6, the unit three-dimensional rest diamond has centered moments
`mean t*t=1/40` and `mean x_i*x_j=3*delta_ij/80`. The actual boosted map gives
exactly the displayed factor below. In SE7, the entire kernel derivative is
`K_3'(0)=-35/8`, not the derivative of its polynomial alone. Integrating the
constant and linear kernel terms with **the weighted partner measure** gives
its stated nonzero quadratic-density discrepancy. Thus SE7 correctly refutes
an exact exponential, not the high-density conclusion. No blocking error was
found in these scoped statements. This is an author reconstruction, not
independent mathematical acceptance.

Use ordinary coordinates `t=(u+v)/2`, `x=(u-v)/2`, with the same SE1 points
and excluded closed `J+(b)`. For a target q let ell be its actual temporal
displacement from a partner p and sigma their squared Minkowski displacement.
The canonical constants and exact phase are

```math
\begin{aligned}
c&=\pi/12,& \beta=a_3&=2c^{2/3}/\Gamma(5/3),\\
K(z)&=(1-27z/8+9z^2/8)e^{-z},&
\widehat K(w)&=\Gamma(w)(1-3w/2)(1-3w/4),\\
A(t)&=1+t^2,&
V_g(p,q)&=c\sigma^{3/2}
 \left(1+q_t^2-\ell q_t+5\ell^2/16-3\sigma/80\right).
\end{aligned}\tag{CS1}
```

An exact expansion in rho recovers SE7 but does not control large rho: an
absolute bound for its summed power series grows exponentially in rho times
the maximum interval volume. Taking absolute values before the signed partner
integration therefore loses the needed cancellation. We instead resolve the
whole interval jointly with the endpoint approaching the cone.

## 2. Exact joint endpoint/interval scaling; no partners removed

Write `Q=(1,0,0)` and let D be its unit rest diamond with past tip zero.
For this section allow any fixed smooth positive density A on the compact
causal enclosure. A positive smooth extension to a slightly larger compact
box may be used; it changes no physical interval. Put

```math
\begin{aligned}
q&=a+(T,R\omega),& s&=T^2-R^2\gt0,\\
L_{T,R,\omega}X
 &=\left(TX_0+RX_1,\ (RX_0+TX_1)\omega+\sqrt{s}X_2\omega_\perp\right),\\
p&=a+LX,& E(X)&=A(a+LX),& \lambda&=\rho s^{3/2},\\
L^*\eta&=s\eta,& dp&=s^{3/2}dX,&
V_g(p,q)&=s^{3/2}V_E(X,Q),\\
J_E(\lambda)&=\int_D E(X)K(\lambda V_E(X,Q))\,dX,&
\mathcal R_E(\lambda)&=\beta[1-\lambda J_E(\lambda)],\\
\mathcal A_{\rho,3}[1,\chi;M]
 &=\rho^{2/3}\int_M\chi(q)A(q)\mathcal R_E(\rho s^{3/2})\,dq.
\end{aligned}\tag{CS2}
```

For positive s this is an exact Lorentz homothety onto **all** of `I(a,q)`.
Every physical interval from p to q is mapped as a whole before its volume
enters K. The determinant, both endpoint measures and the physical point
are explicit. In particular, p need not be close to the cusp tube.

A bounded T gives uniformly bounded entries of L, including at s=0 and T=0.
Consequently the E family has a common positive lower bound and bounded
derivatives of every fixed order in all reference spacetime coordinates. An
unbounded Lorentz boost in isolation would not give this conclusion: it is
the **combined homothety and boost** in CS2 that has bounded entries. No
inverse at s=0 is asserted. At fixed positive T and s tending to zero,
E tends smoothly on D to a density depending only on `X_0+X_1`.

Keep once and for all the original smooth physical-time cutoff, one below
`delta/2` and zero above `delta`, for example `delta=1/16`. Its argument here
is exactly `T*(1-X_0)-R*X_1`, not a reference time or a null coordinate.
Insert it and its complement in J; their sum is CS2 and the point belongs
only to short. We analyze that exact sum. The reference split used next is
an auxiliary integration partition, not a change of physical cutoff.

## 3. Uniform signed complete-response lemma, including its critical error

For any family of smooth positive E with the bounds just proved, define

```math
\begin{aligned}
\kappa[E]&=E(Q)^{-5/3}\left[
 \frac23\Box E(Q)-\frac59\frac{\partial E(Q)\cdot\partial E(Q)}{E(Q)}
 \right]=\frac12R_{E^{2/3}\eta}(Q),\\
\mathcal R_E(\lambda)
 &=\kappa[E]\lambda^{-2/3}+O(\lambda^{-1})\quad(\lambda\ge1),\\
|\mathcal R_E(\lambda)|&\le C\quad(0\lt\lambda\le1),&
\kappa[A\circ(a+L)]&=s\,\kappa[A](q).
\end{aligned}\tag{CS3}
```

All constants are uniform on that family. The dot and box are Lorentzian.
The last equality follows from the exact metric identity in CS2, not from a
small-density approximation. Here is a derivation of the estimate, rather
than an invocation of a smooth-test-function operator limit at a null face.

Parameterize the entire reference partner diamond from Q by
`X=Q-l*(1,sqrt(1-xi)*n)`, with n on the unit circle. Its exact domain is
`0<xi<1`, `0<l<L(xi)=1/(1+sqrt(1-xi))`; its measure is
`l*l*dl*dxi*dn/2`. The actual normalized interval mean h has
`V_E=c*l^3*xi^(3/2)*h`. The faithful rest-diamond map and transverse reflection
prove smoothness in xi near zero, positivity and all required mixed derivative
bounds uniformly in E, l and n. Near xi=1 only l derivatives are used.
Mellin inversion starts in the absolutely integrable strip `0<Re(w)<2/3`:

```math
\begin{aligned}
Z_E(w)&=\frac{c^{-w}}2\int_{S^1}\int_0^1\int_0^{L(\xi)}
 l^{2-3w}\xi^{-3w/2}E(Q-lu)h^{-w}\,dl\,d\xi\,dn,\\
J_E(\lambda)&=\frac1{2\pi i}\int_{\mathrm{Re}(w)=w_0}
 \widehat K(w)Z_E(w)\lambda^{-w}\,dw,\qquad
u=(1,\sqrt{1-\xi}\,n).
\end{aligned}\tag{CS4}
```

Split the reference l integral at **1/4**, retaining both sides. On its upper
side put `l=1/4+(L(xi)-1/4)*v`. The domain is fixed; three xi subtractions
through degree two leave an integrable remainder for `Re(w)<8/3` and only
simple poles `2/3,4/3,2`. The part away from xi=0 is holomorphic there.

On the lower side Taylor expand in l through degree three. Subtract xi through
degree two from its l-fourth-order remainder as well. The double remainder is
bounded by a polynomial in `abs(w)` times
`l^(6-3*Re(w))*xi^(3-3*Re(w)/2)`, hence integrable for `Re(w)<7/3`.
The diagonal poles are `1,4/3,5/3,2`. The angularly averaged l coefficient
is constant in xi, so there is no double pole at 4/3. The averaged cubic
coefficient has degree at most one in xi: the l-cubic coefficient of h is
`-7*D^3 E/192+3*xi*D*Box E/320`, by the centered rest moments and vanishing
odd centered moments. Products of lower moments have the same angular degree
after the circle average. Thus it has **no xi-squared coefficient**, so there is no
double pole at 2 either. This last check excludes a logarithm in the bound
claimed in CS3. All other edge poles in this strip are simple.

The continued expressions have uniform polynomial vertical growth. The gamma
factor supplies exponential decay. Shift to a fixed line `2<Re(w)<7/3`, keeping
the residue at 2 and every finite-upper-endpoint subtraction. This proves a
uniform expansion through `lambda^(-2)` with a strictly smaller remainder.
The two actual kernel zeros kill the simple poles at 2/3 and 4/3. Nothing
removes the generally nonzero residue at 2; it gives the integrable matching
tail in CS3. No unsigned divergent moment has been assigned an integral value.

For completeness the surviving point and curvature coefficients can be
calculated without inserting a desired target. In these Taylor formulas D
means differentiation in direction u, not the reference integration domain.
The actual interval mean is

```math
\begin{aligned}
h&=E-\tfrac l2DE+l^2\left(\tfrac5{32}D^2E
                          -\tfrac{3\xi}{160}\Box E\right)+O(l^3),\\
\frac1{2\pi}\int_{S^1} E(Q-lu)h^{-w}\,dn
 &=E^{1-w}+l(w/2-1)E^{-w}E_t\\
 &\quad+l^2E^{-w}\left[X+(1-\xi)Y/2+\xi Z\right]+O(l^3),\\
X&=(1/2-5w/32)E_{tt}+w(w-3)E_t^2/(8E),\\
Y&=(1/2-5w/32)\Delta E+w(w-3)|\nabla E|^2/(8E),\qquad
Z=3w\Box E/160,\\
\left[\frac{X+Y/2}{1-3w/2}+\frac{Z-Y/2}{2-3w/2}\right]_{w=5/3}
 &=-\tfrac29\Box E+\tfrac5{27}(\partial E)^2/E.
\end{aligned}\tag{CS5}
```

All derivatives on the right are at Q. At w=1 the geometric residue is 8,
and `Khat(1)=-1/8`; rightward contour shifting subtracts residues, so the
partner coefficient is **exactly** `1/lambda`. At w=5/3,
`Khat(5/3)=3*Gamma(5/3)/8`. Multiplying CS5 by the l-pole factor, angular
measure and the original beta gives exactly kappa in CS3. More explicitly,
`J_E=1/lambda-kappa[E]/(beta*lambda^(5/3))+d_E/lambda^2+O(lambda^(-2-eta))`
for some fixed positive eta. The coefficient d_E is the retained simple
geometric residue at 2; its uniform boundedness was proved above. Small
lambda is bounded directly on the whole finite diamond. This completes CS3.

## 4. Derive the full boundary profile and its mass, not an exponential

Let `k=(1,omega)` and `q_0=a+T*k`. At s=0, the reference density in CS2 is
`E_0(X)=A(a+T*(X_0+X_1)*k)`. Write `f(e)=A(q_0-T*e*k)`. Define H using
ordinary beta weight, which includes the entire null interval, not just an
endpoint density. A fixed-v slice of the rest diamond has volume density
`(2/3)*sqrt(v*(1-v))`; division by its volume `pi/12` gives the normalized
beta weight `8*sqrt(v*(1-v))/pi`. In reference null coordinates the partner set is
`0<v<1`, `y*y/v<u<1-y*y/(1-v)`. Integrating u and y **before any asymptotic
expansion**, with `e=1-v`, gives

```math
\begin{aligned}
H(e)&=\frac8{\pi e^2}\int_0^e\sqrt{x(e-x)}f(x)\,dx,\qquad H(0)=f(0),\\
J_0(\lambda)&=\int_0^1\frac{f(e)\sqrt{1-e}}e
       \int_0^e\sqrt{e-\sigma}
           K(c\lambda H(e)\sigma^{3/2})\,d\sigma\,de,\\
x(e)&=eH(e)^{2/3},\qquad
F(x(e))=\frac{f(e)\sqrt{1-e}}{eH(e)x'(e)},\\
J_0(\lambda)&=\int_0^{x(1)}F(x)
       \int_0^x\sqrt{x-z}K(c\lambda z^{3/2})\,dz\,dx,\\
F(x)&=\frac1x+f_0+O(x),\qquad
f_0=-A(q_0)^{-2/3}\left(\frac12+
                 \frac{T\,D_k A(q_0)}{6A(q_0)}\right).
\end{aligned}\tag{CS6}
```

Both physical null-coordinate bounds and their measure `du*dv*dy/2` are used
in this calculation. The change x(e) is genuinely invertible for **every**
positive smooth f: write
`e^(3/2)*H(e)=(8/pi)*integral_0^e sqrt(x)*sqrt(1-x/e)*f(x) dx`.
Differentiation of this positive integral gives a derivative between
`(3/2)*inf(f)*sqrt(e)` and `(3/2)*sup(f)*sqrt(e)`. Hence x' is bounded above
and away from zero. This is a geometric positivity proof, not a no-caustics
assumption. Expanding `H=f(0)+e*f'(0)/2+O(e*e)` proves the last line.
At x(1), F has the retained integrable square-root endpoint.

Put `R_0(lambda)=beta*(1-lambda*J_0(lambda))`. CS3 applies to E_0;
its derivatives are all in one null direction, so its scalar curvature is
zero. Thus R_0 is bounded at zero and is `O(1/lambda)` at infinity. Its
signed mass in the squared-distance scale is **absolutely convergent**:

```math
\begin{aligned}
\int_0^\infty \mathcal R_0(z^{3/2})\,dz
 &=-4f_0
 =2A(q_0)^{-2/3}
       \left(1+\frac{T D_k A(q_0)}{3A(q_0)}\right),\\
\frac{A(q_0)}2\int_0^\infty\mathcal R_0(z^{3/2})\,dz
 &=\Omega(q_0)+T D_k\Omega(q_0)
 =\frac{d}{dT}\left[T\Omega(a+Tk)\right],\qquad \Omega=A^{1/3}.
\end{aligned}\tag{CS7}
```

Here is a signed evaluation that keeps both matching tails. Initially,
`-1<Re(u)<-1/3` permits absolute Mellin integration of `R_0-beta` in lambda
using CS6. Continue the result to `0<Re(u)<1`, where CS3 makes the Mellin
integral of R_0 itself absolutely convergent. Subtracting the constant at
lambda=0 and retaining its elementary pole gives

```math
\begin{aligned}
\int_0^\infty\lambda^{u-1}\mathcal R_0(\lambda)\,d\lambda
 =-\beta c^{-u-1}\widehat K(u+1)
 \mathrm B(-1/2-3u/2,3/2)
 \underset{\text{continued}}{\int_0^{x(1)}}F(x)x^{-3u/2}\,dx.
\end{aligned}\tag{CS8}
```

The continuation on the right is obtained by subtracting the actual `1/x`
and f_0 terms near zero; the remaining integral is ordinary and integrable
near u=2/3. Its only pole there is `-(2/3)*f_0/(u-2/3)`. The beta factor
has a simple zero with slope `-pi`. Their product is `2*pi*f_0/3`, not zero.
The upper endpoint and both subtracted finite-upper-limit terms are retained;
their holomorphic parts multiply that zero. Using the genuine Khat value
and `dz=(2/3)*lambda^(-1/3) dlambda` gives `-4*f_0`, proving CS7.
The initial subtraction and continuation are justified by splitting the
lambda integral at one: its constant term contributes the same `beta/u`
on both sides. There is no interchange of separately divergent unsigned
integrals. In general the **profile** is nonlocal and signed, even though
its complete critical mass is the local generator derivative in CS7.

The surviving upper tail can also be derived independently of an action fit:

```math
\begin{aligned}
\mathcal R_0(\lambda)&=D_f/\lambda+O(\lambda^{-1-\eta}),\\
D_f&=\frac{\beta}{12c^2}\int_0^1 e^{-5/2}\sqrt{1-e}
              \left[\frac{f(e)}{H(e)^2}-\frac1{f(0)}\right]de.
\end{aligned}\tag{CS8a}
```

This is an ordinary convergent integral: the bracket is of order e squared,
since the linear terms of f and H squared cancel. At Mellin w=2 the beta
factor `B(1-3*w/2,3/2)` has residue 1/12. Its remaining geometric integral
is exactly the integral in CS8a; the constant-density subtraction has
`B(-3/2,3/2)=0` under the same proved continuation. The uniform continuation
in §3 supplies the strictly smaller remainder, with any fixed eta below 1/3.
Thus the complete upper tail is present and generally nonzero, while the
bounded lower tail retains the physical point cancellation. Neither tail is
replaced by an inner-sector sign argument.

## 5. Both adjoining scaling sectors and the complete critical remainder

Set `epsilon=rho^(-2/3)` for rho at least one. CS3 implies, uniformly in the
entire compact endpoint family,

```math
\begin{aligned}
\left|\rho^{2/3}\mathcal R_E(\rho s^{3/2})-\kappa[A](q)\right|
 &\le C\epsilon^{-1}(1+s/\epsilon)^{-3/2},\\
\left|\mathcal R_{E(T,\epsilon z,\omega)}(z^{3/2})
                  -\epsilon\kappa[A](q)\right|
 &\le C(1+z)^{-3/2},\\
\int_L^\infty C(1+z)^{-3/2}\,dz&\le 2C(1+L)^{-1/2}.
\end{aligned}\tag{CS9}
```

For large lambda this follows by **first** using `kappa[E]=s*kappa[A](q)`;
the curvature part becomes exactly the subtracted term. For small lambda,
use boundedness and epsilon at most one. This matches the cone-layer sector
`s/epsilon` bounded to the interior sector `s/epsilon` large. Their full
signed profiles, including the nonzero inverse-lambda tail, have not been
replaced by an exponential or by independent absolute bounds for the point
and pairs. Near z=0 the bound is finite; the full upper tail is CS9. The
physical temporal cutoff is still fixed; epsilon is a change of integration
variable, not a new boundary or a discarded physical band.

Now let P be **any open past set containing a**, with bounded
`M=I+(a) intersect P`, in three dimensions. Let R(omega) be its first null-ray
exit and let chi be any fixed smooth target field. Openness and boundedness
give a measurable R with positive lower and finite upper bounds. The exact
endpoint measure is `dq=dT*ds*domega/2`, with `0<s<T*T`.
For fixed T below R, membership of q for small s follows by openness. For
T above R, choose a null-ray point with radius strictly between R and T;
that point is in the chronological past of q for all small positive s.
The past-set property therefore forbids q. The single value T=R has zero
radial measure, even for a discontinuous measurable exit function.

Subtract the derived curvature term from CS2 and put `s=epsilon*z`. For
fixed positive T,z, E tends to E_0 and the finite partner integral is
continuous under this convergence. The second bound in CS9 dominates the
whole expression on the finite T/circle parameter domain times the entire
positive z axis. Dominated convergence and CS7 give

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,3}[1,\chi;M]
 &=\frac12\int_M\chi R_g\,d\mu_g
  +\int_{S^1}\int_0^{R(\omega)}
   \chi(a+Tk)\frac{d}{dT}[T\Omega(a+Tk)]\,dT\,d\omega,\\
\lim_{\rho\to\infty}\mathcal A_{\rho,3}(M)
 &=\frac12\int_M R_g\,d\mu_g
   +\int_{S^1}R(\omega)\Omega(a+R(\omega)k)\,d\omega.
\end{aligned}\tag{CS10}
```

This proves the complete critically normalized remainder is o(1), not just
its putative coefficient. It includes the far-partner and entering/closing
sectors simultaneously. The tip is not a measure-zero deletion: CS9 bounds
its entire target-weighted point/all-partner response for `0<T<r` by `C*r`
plus the bounded bulk contribution. On a regular exit screen the induced
metric gives precisely `R*Omega*domega`. At arbitrary irregular exits the
last integral is an independently defined ray functional; no unjustified
smooth area or universal stratum decomposition is asserted. If the weighted
ray term is rewritten as screen plus flux, it is exactly
`chi(R)*R*Omega(R)-integral_0^R T*Omega(T)*chi'(T) dT` on each ray.
The generator derivative and every artificial endpoint remain; target-partition
derivatives cancel only in their full sum.

**Structural scope.** The argument uses dimension three, a global conformal
Minkowski causal enclosure with smooth positive density, the common past tip,
and the actual open-past-set fibre property. It uses neither time-only nor
polynomial density, nor finite type, finite sheet count, transversality,
continuous exit radius, or a zero-charge premise. The null-profile calculation
works along each actual ray for spacetime-dependent A. Time reversal gives
the corresponding common-future-tip statement. Other dimensions and intrinsic
multiple-route intervals are not inferred from this proof.

## 6. The actual SE6 cusp: two transition sectors, no extra charge

Return to SE1, with `a=(-1/2,1/2,0)` in ordinary coordinates and A in CS1.
For the full endpoint integral use `T=q_t+1/2`, `s=T*T-R*R`, `0<T<1`.
The exact permitted angular measure is

```math
\begin{aligned}
W(T,s)&=2\pi &&(0\lt T\le1/2,\ 0\lt s\lt T^2),\\
W(T,s)&=2\left[\arccos\frac{s-T}{\sqrt{T^2-s}}
             -\arccos\frac{2-3T+s}{\sqrt{T^2-s}}\right]
 &&(1/2\lt T\lt1,\ 0\lt s\lt2T-1),\\
W(T,s)&=2\pi &&(1/2\lt T\lt1,\ 2T-1\le s\lt T^2),\\
\mathcal A_{\rho,3}(M_*)&=
 \frac{\rho^{2/3}}2\int_0^1\int_0^{T^2}
 W(T,s)\left[1+(T-1/2)^2\right]
 \mathcal R_{E(T,s)}(\rho s^{3/2})\,ds\,dT.
\end{aligned}\tag{CS11}
```

The upper cosine bound is the actual past cone from c; the lower is the
excluded closed future cone from b. Their common transition is `s=2*T-1`.
Both regions occur, including at the entering apex T=1/2 and the closing
end T=1. Formula CS11 is an exact complete curved response, with both endpoint
measures and the whole partner integration of CS2/CS4. Numerical quadrature
is not needed for its asymptotic justification. The value on null boundary
sets is immaterial to these integrals, not permission to change the order.

Let e_r be a uniformly bounded target field supported within Euclidean
distance C*r of the same generator segment K in SE1. It is away from a,
so its angular support about a has length at most C*r, uniformly in T and s.
Integrating CS9 and the bounded bulk term gives

```math
\begin{aligned}
\sup_{\rho\gt0}|\mathcal A_{\rho,3}[1,e_r;M_*]|&\le Cr,\\
R_{\mathrm{out}}(\phi)&=\frac2{3+\cos\phi},\qquad
\mathcal T_*=
 \int_{-1/2}^{1/2}\frac{12-8t^2}{9(1+t^2)^{5/3}}\,B(t)\,dt
 +\int_0^{2\pi}R_{\mathrm{out}}(\phi)
      \left[1+(R_{\mathrm{out}}(\phi)-1/2)^2\right]^{1/3}\,d\phi,\\
\mathcal A_{\rho,3}(M_*)&\longrightarrow\mathcal T_*.
\end{aligned}\tag{CS12}
```

For rho below one use the complete finite-volume response directly. This
uniform estimate restores both cusp ends, every macroscopic partner and the
point; derivatives of e_r are not needed after summing the source labels.
Thus an additional **net** shared-generator charge is proved absent, not
postulated. This target grouping does not assert that every separately
source/target-labeled singular sector vanishes; its opposite contributions
remain in the exact sum.

Here B(t) is the independent spatial area of SE1: for negative t it is
`pi*(t+1/2)^2`; for `0<t<1/2` it is the intersection area of disks of radii
`t+1/2` and `1-t`, separated by 1/2, minus `pi*t*t`. This is additivity of
a local geometric integral, not assumed bilocal action additivity. The
bulk factor is independently `2*Omega''-(Omega')^2/Omega`. The outer-screen
radius follows by intersecting the two actual cones; the exceptional ray
through b has zero angular mass. Direct geometric quadrature gives bulk
`0.5762798189516913`, screen `4.574132601400751`, total
`5.150412420352442`. These decimals are diagnostics, not the definition or
proof of the coefficient. The exact answer is CS12.

## 7. Restore all labels and transfer the original law separately

For any fixed finite endpoint partition, sum every source label before using
CS2. The target labels then sum to one. In NG1 notation this retains the two
cross orders and the both-singular sector; the mixed point weights also sum
to one. It does not assert separate sectorwise limits or bilocal additivity
of subregion actions. The original short and long weights sum identically
on every physical partner pair, including their transition band. Their point
term is counted once. Hence CS10/CS12 are complete deterministic results
at the original fixed physical cutoff.

Only afterward apply probability. The actual bounded open region, smooth
positive atomless volume, closed Borel order and Borel exclusive interval
relation define the original finite Poisson law. Future/past containment
identifies every restricted interval with the same physical interval used
in CS1–CS4. Finite second moments dominate every original minimal-layer count.
Reduced ordered two-point Mecke gives the original two intensity factors and
`exp(-rho*V)*(rho*V)^k/k!`. Summing with the unchanged layer coefficients
therefore gives, at every positive density, the deterministic action above.
Its expectation tends to CS10 and in particular CS12. This is not a change
of law, an interchange with a random limit, or a sample-wise assertion.

## 8. Decisive mathematics and original-contract status

The interval-wide variation of density really invalidates the exponential.
It does **not** leave an extra cusp charge. Jointly rescaling the target and
its entire past diamond produces a bounded family of densities. Signed
Mellin integration cancels the physical point, derives curvature and retains
an integrable inverse-lambda tail. The remaining null-layer profile depends
on distant partners, but its **whole** mass is the derivative of conformal
ray length. That derivative integrates to the independent outer screen.
The uniform tail bound, not small tube volume or a guessed cancellation,
controls the two cusp ends.

SE6's precise analytic blocker is consequently resolved by CS3, CS7, CS9
and CS12; SE7 remains a valid negative control. The generalization CS10 is
proved under its structural hypotheses, not merely proposed for other
polynomial densities. The critical scrutiny points are the uniform Mellin
continuation at w=2 and the continued signed mass at u=2/3.

**STILL BLOCKED under the original #156/#81/#24 acceptance.** The common-tip
homothety is not available for general intrinsic physical unions. The exact
remaining general-producer inference is a uniform signed continuation and
integrated critical remainder for those actual unions, **retaining their
surviving fractional/logarithmic poles and deriving their geometric
coefficients**. IF1's physical seven-halves transition shows why a smooth
Cartesian amplitude cannot simply be asserted; IF3–IF5 perform the needed
matching only for their fixed product family. The specialist question is
whether that physical-union disintegration admits such a uniform matched
continuation through simultaneous focal and boundary closing transitions.
No answer, no no-caustics premise and no parent scope change is adopted here.
This proposed continuation is a sufficient research route, not a new
admissibility condition or a theorem necessity imposed on the parent.
The single original-item crosswalk retains all other original requirements.

#177 remains unresolved; #94/#86 retain independent scrutiny, provenance and
justified verification; #185's claim-to-Lean mapping stays deferred. Written
proofs, finite diagnostics, existing Lean coverage and human acceptance remain
distinct. No agent/reviewer launch, merge, deployment or closure is authorized.
