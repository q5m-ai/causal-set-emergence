# A written complete-action obstruction in curved four dimensions

**Status: written deterministic proof with a separately regenerated model-sign
certificate; not a Lean proof or independent mathematical acceptance.** This
continues [CR1–CR19](curved4-focal-research.md), the
[certificate CC1–CC13](curved4-focal-certificate.md), and the
[physical classification CG1–CG9](curved4-focal-globalization.md). It supplies
the uniform subtracted transfer that was missing at CG10, and then restores
the entire action. Final independent scrutiny remains with #94/#86.

No action, target, ambient order, Poisson law or G-SS quantifier is changed.
In particular, the conclusion is not obtained by excluding quartic focusing,
choosing a density-dependent region, summing geodesic volumes, or dropping a
closing/contact neighborhood.

## 1. Statement and normalization

Use the admitted metric and region CR4:
`H(x)=sin(2*x)^2/4`, `g=2 du dv+H du^2-dx^2-dz^2`, with the original
compact spatial identifications and temporal slab of duration T=7/4.
Both coordinate endpoint measures have density one. Its independent target
is zero: the scalar curvature vanishes and the joint is empty.

Keep the canonical kernel and constants:

```math
\begin{aligned}
K_4(s)&=(1-9s+8s^2-\tfrac43s^3)e^{-s},\qquad
 a_4=\beta_4=4/\sqrt6,\quad c_4=\pi/24,\\
C_{\mathrm{phys}}&=\frac49 I
 \sum_{\text{two cells}}\int_{-p_T}^{p_T}
 400\,G(L_c(p),S_c(p))\,2C(p)^{3/4}\kappa(p)^{-9/7}\,dp>0,\\
D&=\beta_4\frac97\frac{22}{343}\Gamma(9/7)C_{\mathrm{phys}}>0,\\
\mathcal A_{\rho,4}&=-D\rho^{3/14}+O(\rho^{1/6}),\qquad \rho\longrightarrow\infty.
\end{aligned}\tag{CO1}
```

The quantities in the source integral are the **derived physical** ones in
CG4–CG6. The coefficient I is the fully matched model integral CR18, with
both of its subtractions and the opening-well term; CC13 proves it positive.
Here C-phys is defined by the actual pair-measure Mellin residue proved below.
No unsupported pointwise expansion of the unsmoothed primitive is inferred
from that residue.

Thus the complete deterministic action diverges negatively despite the
independently defined target zero. The proof concerns the complete unit-field
observable; it already disproves its proposed universal curved-4D limit on
the original G-SS class. The finite-density expectation bridge is applied
only in section 8, after this deterministic calculation.

## 2. Fix the split and retain every part

Choose one positive temporal cutoff delta below the S30 thresholds audited
in CP1–CP2, and below pi/4. CR9 is its exact strict-short/equality-long split.
The point term occurs only in short. All focal and ordinary cut contacts
classified in CG1–CG8 are strictly long, including their closing contacts.
S30 gives the short limit zero for this metric.

The remaining task is therefore the **whole** long pair integral, with CR8's
physical weight. It is useful to undo only the last b integration, not any
physical partner:

```math
\begin{aligned}
d\nu&=400\,[T-L/2-e-b^2/(2L)]_+\,dp\,dL\,dq\,de\,db,\\
\tau&=L/2+e+b^2/(2L),\qquad e\ge S_L(p,q),\qquad \tau\ge\delta,\\
P_{\mathrm{long}}(\rho)&=\int K_4(\rho W)\,d\nu,\qquad
 L_g^\delta(\rho)=-\beta_4\rho^{3/2}P_{\mathrm{long}}(\rho).
\end{aligned}\tag{CO2}
```

The time weight comes from integrating **both** endpoint times. Integrating
b recovers exactly G, not a substitute density. The faithful r,z lifts and
containment proof remain CR4–CR9. The set Delta-u=0 is measured through its
neighboring regular chart below, not excised with a collar.

Use fixed smooth partitions in compact endpoint charts near the null set.
Away from it W has a positive lower bound, so the complete omitted-from-the-
charts piece has an exponentially small response by CP6a. These auxiliary
partitions are independent of rho and sum to one. They are not new temporal
cutoffs or modified observables.

## 3. An exact common quartic germ

CG1–CG3 classify all minimizing contacts of this metric; this is where the
finite local multiplicity is **derived**, not assumed for G-SS. Along the
conjugate source family the middle action
`U(a)=S_(L/2)(p,a)+S_(L/2)(a,q)` has a unique quartic minimum at its contact.
Its two unfolding derivatives are independent, and its quartic coefficient
C(p) is positive by CG5.

The analytic right normal form with an additive parameter function gives
local coordinates, uniformly on compact source subintervals,

```math
\begin{aligned}
U(X(u;A,B,p))&=d(A,B,p)+P(u;A,B),\qquad
 P(u;A,B)=u^4+Au^2+Bu,\\
\left|\frac{\partial(L,q)}{\partial(A,B)}\right|_c&=2C(p)^{3/4},\qquad
 \partial_u x_c(s)=C(p)^{-1/4}\psi_p(s).
\end{aligned}\tag{CO3}
```

For completeness, the normal-form construction needs no extra jet premise.
The half actions are analytic endpoint actions with lengths uniformly below
pi; Poincare gives a positive Dirichlet second variation, so the shooting
inverse is analytic. Divide the homotopy remainder by the cubic state
derivative of the middle germ. Weierstrass division leaves a quadratic
remainder. The constant, L and q derivatives span its three coefficients,
by the unfolding calculation CG5–CG6. Solve for the two parameter vector
fields, additive constant and state vector field, and integrate this analytic
homotopy on a smaller neighborhood. The quartic coefficient and this
coefficient matrix stay nonzero on the compact source family. This proves
CO3 with smooth, uniformly bounded coordinate changes. A finite source-chart
partition covers the family, including the closing ends.

Every sufficiently small physical lens is included. The middle action has
a fixed gap outside these state neighborhoods, by compactness and the
classification of its minima. Its normal form has one or two global minima;
all of them are retained. If a middle state exceeds the minimum by more than
the endpoint excess, the nonnegative composition defect CG9 excludes it
**exactly**, not by a guessed small-volume approximation.

Let a be a global minimizer of P and put k=A+6a squared. As in CR15,

```math
\begin{aligned}
a&=\sqrt k\,r,\quad -1/2\le r\le1/2,\quad
 A=k-6a^2,\quad B=8a^3-2ka,\\
P(a+\sqrt k\,u)-P(a)&=k^2(u^2+4ru^3+u^4),\\
e-d(A,B,p)&=P(a)+k^2E,\qquad E\ge0,\\
|dA\,dB\,de|&=2k^{7/2}\,dk\,dr\,dE.
\end{aligned}\tag{CO4}
```

The equality of two minima is the boundary r=plus or minus 1/2, counted once
in parameter measure. Its whole neighborhood remains. Put t=sqrt(k) and
write the actual interval as `W=k^(7/2)*f_t(r,E,p)`. The goal is a uniform
statement about this physical f-t, not its compact scaled limit alone.

## 4. Uniform endpoint matching, including the interval union

### 4.1 The endpoint penalty has a uniformly invertible rescaled system

For a source-tip segment s use the **exact** composition identity CG9,
pulled back by CO3's state coordinate. Still denote its defect by D-s.
Choose a fixed small s-zero, below all retained half lengths. On this tip
range its nonnegative defect has the form

```math
\begin{aligned}
D_s(x,u)&=\frac{A_s(x,u)}{2s}(x-X_s(u))^2,\qquad
 0\lt c\le A_s\le C,\\
X_s(u)&=p+sV_s(u),\qquad 0\lt c\le V_s'(u)\le C.
\end{aligned}\tag{CO5}
```

All rescaled coefficients and their derivatives are uniformly smooth down
to s=0. To see this directly, the short action is its flat kinetic term
plus s times a smooth function, obtained by solving the ODE on the unit
interval. The remaining half action has length bounded away from zero and
below pi. Taylor division at its unique minimizing intermediate point gives
CO5. The signs follow from the positive half-segment endpoint inverse. The
other tip is identical after reversing the path.

Around the primary minimum put `u=a+t*xi`, and introduce

```math
\begin{aligned}
\alpha&=\sqrt{\frac{s}{s+k}},\qquad
 \beta=\sqrt{\frac{k}{s+k}},\qquad \alpha^2+\beta^2=1,\\
x&=X_s(a)+t\sqrt{s(s+k)}\,Z,\\
\frac{D_s}{k^2}&=\frac{A}{2\beta^2}
       (Z-\alpha\overline V(\xi))^2,
 \qquad \overline V(0)=0,\quad \overline V'(0)>c.
\end{aligned}\tag{CO6}
```

The apparent singularity at beta=0 is removed with
`eta=(Z-alpha*V_bar(xi))/beta^2`. The minimizing equations become

```math
\begin{aligned}
Z-\alpha\overline V(\xi)&=\beta^2\eta,\\
q_r'(\xi)-A\alpha\overline V'(\xi)\eta
       +\tfrac12\beta^2\eta^2 A_\xi&=0,
 \qquad q_r(\xi)=\xi^2+4r\xi^3+\xi^4.
\end{aligned}\tag{CO7}
```

At the minimum the determinant of this system in xi,eta is
`A*alpha^2*V_bar'(0)^2+2*beta^2`, bounded uniformly away from zero.
The reduced phase has quadratic coefficient
`A/(2*beta^2+A*alpha^2*V_bar'(0)^2)`, also bounded above and below.
Thus the implicit function theorem and the one-dimensional Morse lemma
apply uniformly on the **compact rescaled** parameter set, including both
alpha=0 and beta=0. This is a derived short-penalty inverse, not an assumed
uniform long-geodesic inverse.

To check compactness of its coefficients at the double corner s=k=0, use
`sqrt(s)` and `sqrt(s+k)` as bounded variables. The physical displacement
in CO6 is t times their product; the state displacement is t times xi.
Every coefficient in CO5 is smooth in these physical arguments. Changing
from (t,s) to (0,s) therefore changes the coefficients by at most
`C*(t+beta)`. The same holds for any fixed finite number of Morse Taylor
coefficients and for their uniform analytic remainder. No derivative of
an unscaled singular inverse is exchanged with the endpoint integral.

The volume factor at a tip, after division by k to power 7/2, is a bounded
smooth multiple of `s*sqrt(s+k)`. The two elementary bounds

```math
\begin{aligned}
\int_0^{s_0}s\sqrt{s+k}\,\beta\,ds&=t\int_0^{s_0}s\,ds=O(t),\\
\int_0^{s_0}|s\sqrt{s+k}-s^{3/2}|\,ds&=O(t)
\end{aligned}\tag{CO8}
```

prove an O(t) difference after integrating every needed coefficient and
remainder. On the fixed interior s range, proper subsegments are unique and
nonconjugate; their inverses have a uniform bound on that derived compact
set. The usual interior Morse calculation gives the same O(t) conclusion.
At t=0 the state Jacobian in CO3 gives precisely
`kappa(p)*f_r(E)`, with kappa from CG5, after the entire longitudinal integral.

### 4.2 Both wells, moving opening, and their endpoint overlap

For small fixed E-zero, the quartic sublevel has only its primary Morse
well and, near r=plus or minus 1/2, a second uniformly nondegenerate well.
Its depth d-r is the **exact** quartic depth in CC6. For the second well,
replace 2 in the determinant above by its positive bounded Hessian. The
same uniform construction applies to its positive excess `(E-d_r)_+`.

Do not add their physical volumes blindly. Their normalized spatial centers
in CO6 are separated by a positive multiple of alpha; their Morse widths
are at most a constant times sqrt(E). They can overlap only when
`s <= C*k*E`. At each such split, the physical positive-part integrand is
the maximum of the two local positive-part integrands, not their sum.
Their difference is bounded by `C*E^2` after the normalized spatial
integration. CO8's actual tip factor therefore gives

```math
\begin{aligned}
\left|W-\sum_{\text{open local wells}}W_i\right|
 &\le C k^{7/2}E^2\int_0^{CkE}s\sqrt{s+k}\,ds
 \le C k^6E^4.
\end{aligned}\tag{CO9}
```

This bound uses the nonconstant physical defect CO5 and its uniform inverse,
not a frozen quadratic ansatz. It includes both tips and the entire
well-opening layer. There are no other sublevel states, since D-s is
nonnegative and the exact quartic state sublevel was already exhausted.

Each individual normalized well volume consequently has the form
`A_i(t,r)*E_i^2+B_i(t,r)*E_i^3+E_i^4*C_i(t,r,E_i)`, with positive A-i,
uniformly bounded remainders, and O(t) differences from the corresponding
principal-model coefficients and remainders. CO9 changes only the last
remainder by O(t to power five). These facts hold across the moving opening
boundary; they do not postulate absolutely integrable cubic inverse jets.

### 4.3 The large-E matching tail is physical too

For E bounded below, rescale the state by `E^(1/4)` and put
`a_scale=t*E^(1/4)`. Quartic coercivity contains the sublevel and all its
possible minimizing states in a fixed bounded rescaled interval, uniformly
in r. The rescaled potential P has a bounded derivative there. The constraint
map V has derivative bounded away from zero. With penalty sigma comparable
to `s/a_scale^2`, its exact nonconstant envelope satisfies

```math
\begin{aligned}
0\le P(U_0)-\min_U\left\{P(U)+\tfrac\sigma2 A(Y,U)
       (Y-\mathcal V(U))^2\right\}&\le C/\sigma,
 \qquad \mathcal V(U_0)=Y.
\end{aligned}\tag{CO10a}
```

The upper comparison uses U-zero as trial state. For the lower one,
`P(U)>=P(U0)-C*abs(U-U0)` and the penalty is bounded below by a positive
multiple of `sigma*(U-U0)^2`; complete the square. For large sigma this and
the Lipschitz positive-part power bound the profile error. The integrated
tip error is at most `C*a_scale^2*integral sqrt(s) ds`. Where sigma is
bounded, both profiles have bounded rescaled width; its tip volume is at
most `C*integral_0^(C*a_scale^2) s*sqrt(s+a_scale^2) ds=O(a_scale^5)`.
The physical constraint Jacobian differs from its principal one by
O(a-scale), and the fixed interior has the same bound. Consequently

```math
\begin{aligned}
f_t(r,E,p)&=\kappa(p)f_r(E)(1+O(tE^{1/4})),\qquad E\ge E_0,\\
f_r(E)&\asymp E^{7/4}\qquad(E\ge E_0).
\end{aligned}\tag{CO10}
```

Here the first estimate is used while a-scale is within the fixed physical
germ. Uniform quartic coercivity and the fixed middle-state gap justify that
whole-lens restriction. Outside it the fixed smooth chart cutoff is zero;
comparison with the extended model is still bounded by
`C*t*E^(1/4)*f_r(E)^(-Re(z))`, since a-scale is then bounded below.
Thus the extension's tail is explicitly controlled, not assigned to the
physical observable. Its E integral converges uniformly when Re(z)>5/7.

## 5. Restore the closing fibers before taking the finite part

The b-integrated weight G is only finitely smooth at closing, so do not
freeze it there or differentiate its fractional power. Work with CO2.
On the contact family the closing function is

```math
\begin{aligned}
F_c(p,b)&=T-\tau_c(p)-b^2/(2L_c(p)).
\end{aligned}\tag{CO11}
```

Its gradient in p,b is nonzero on its zero set. If b is nonzero, use its b
derivative. If b=0, closing occurs at p=plus or minus p-T, where tau-c has
nonzero p derivative. At p=b=0 the closing function is strictly positive.
A fixed finite collection of source/partner charts therefore straightens
the **actual** closing function to a coordinate lambda.

Do this in the smooth absolute-energy coordinates `(p,A,B,e-d,b)` of CO3,
*before* choosing a minimum and passing to CO4. The density is then
`lambda_+` times a smooth Jacobian and smooth chart cutoff. Lambda is an
integration variable, not a small parameter. All derivatives used for
matching fall on the smooth factors, and the fixed integrable lambda weight
is retained. Afterwards CO4 is still exact: the quartic polynomial and its
absolute energy are independent of the eliminated p or b coordinate.
The solved-for geometric parameters remain smooth functions of those
coordinates. At small E their energy derivatives carry the factor k squared;
in the large-E regime their changes are controlled by a-scale. Thus
CO8--CO10 and their subtractions remain uniform after this source averaging.
This also includes the source values just outside the limiting p-T window
that enter at nonzero parameters; none is deleted.

Write the resulting pair density as a fixed integrable nonnegative weight
`w(zeta)` times a smooth `j_t(r,E,zeta)`. Its contact value is j-zero,
independent of r,E. Define the subtracted E,r Mellin integral F-t(z,zeta).
Its subtraction coefficients are constructed from the physical well jets,
not chosen to match the model. Write `j=j_t(r,0,zeta)` and
`j_E=partial_E j_t(r,0,zeta)`. The primary terms are the r averages of
`j*A1^(-z)` and `j_E*A1^(-z)-z*j*B1*A1^(-z-1)`, using the actual jets
at that t, not their contact limits. The opening layer adds to the second one

```math
\begin{aligned}
\sum_{r_b=\pm1/2}\frac{j_t(r_b,0,\zeta)}4
 \int_0^1\left[
 \{A_1(t,r_b)+A_2(t,r_b)(1-y)^2\}^{-z}
       -A_1(t,r_b)^{-z}\right]dy.
\end{aligned}\tag{CO12}
```

The denominator four is the actual absolute derivative of the quartic
second-well depth at either boundary. Substitute d-r=E*y, retaining the
moving boundary. CO8--CO9 and Taylor's formula for a positive base to power
-z show that, after these two terms, the head remainder and its difference
from the principal remainder are respectively bounded by
`C*(1+abs(z))^N*E^(2-2*Re(z))` and the same bound times t. The ordinary
Morse remainders have these bounds uniformly; the physical union correction
CO9 has them as well. No third inverse coefficient is averaged absolutely.
Combining with CO10 proves the missing transfer:

```math
\begin{aligned}
F_t(z,\zeta)&=j_0(\zeta)\kappa(\zeta)^{-z}F_0(z)
 +O\bigl(t(1+|z|)^N\bigr),\\
F_0(z)&=\int_0^1\left[\Phi_z(E)-a_0(z)E^{-2z}
                         -a_1(z)E^{1-2z}\right]dE
 +\int_1^\infty\Phi_z(E)\,dE
 +\frac{a_0(z)}{1-2z}+\frac{a_1(z)}{2-2z},\\
\Phi_z(E)&=\int_{-1/2}^{1/2}f_r(E)^{-z}\,dr,\qquad F_0(9/7)=I.
\end{aligned}\tag{CO13}
```

The estimate is locally uniform on vertical strips
`1 < Re(z) < 10/7`, with polynomial vertical growth. In fact the head allows
Re(z)<3/2 and the large-E comparison Re(z)>5/7; the stricter upper bound is
needed for the following k integration. Complex powers cause no hidden
exponential loss: all their bases are positive real numbers, and their
Taylor bounds cost only polynomials in abs(z).

## 6. The actual Mellin pole and the complete regular complement

Let Z-long(z) be the Mellin transform of the actual long phase measure,
namely the integral of W to power -z against CO2. Initially it is absolutely
convergent for `0 < Re(z) < 1/2`, by CP6. In a cusp chart CO4 and CO13 give

```math
\begin{aligned}
Z_c(z)&=\frac{4R^{(9-7z)/2}}{9-7z}
 F_0(z)\int w(\zeta)j_0(\zeta)\kappa(\zeta)^{-z}\,d\zeta
 +H_c(z),\\
H_c&\text{ is holomorphic for }1\lt\Re z\lt10/7,\\
\mathrm{Res}_{z=9/7}Z_{\mathrm{long}}(z)&=-\frac97C_{\mathrm{phys}}.
\end{aligned}\tag{CO14}
```

Here R is fixed inside the physical chart. The radial split at R is just
an integration partition: its full annulus is retained. On that annulus k
is bounded away from zero, and the already derived head expansion continues
its Mellin integral with only the two regular poles. In the inner part the
error gains k to power 1/2, and
`integral k^((7/2)*(1-Re(z))+1/2) dk` converges exactly below 10/7.
Returning the straightened source variables to p,b and integrating b at
the contact gives G and precisely CO1's physical coefficient. The source
partitions sum to one there. All factors other than I are positive on an
open source family, so C-phys is strictly positive.

Here is the continuation from the initial strip, including a possible trap
in using a homogeneous model. Split E at one. In the small-E part, the two
explicit physical subtractions continue the integral with only simple poles
at 1/2 and 1 before 9/7. In the large-E **physical** part use h=k squared
E: its measure is bounded by a constant times `h^(5/4) dh`, while W is
comparable to `h^(7/4)`. This part is holomorphic below 9/7. Thus there is
an overlap with CO13's comparison strip, proving CO14 by continuation.
One must not extend the model's E tail before restoring the physical cutoff:
that extension alone has an irrelevant lower convergence boundary at 4/7.
The actual integral just described has no such extra pole.

### Regular and ordinary-cut pieces

Outside the fixed cusp neighborhoods, the minimizing endpoint inverses have
a uniform bound by compactness and CG1--CG3's exclusion of other minimizing
conjugate points. CG1--CG2 give at most two minimizing paths, not an assumed
branch hypothesis. Proper half segments have length below pi. The same
composition/Morse argument as CO5--CO8, now with a fixed positive minimum
Hessian, gives for a single physical tube a volume
`A*h^2+B*h^3+O(h^4)`, uniformly up to its two tips.

At an ordinary seam its two terminal momenta differ by a uniform positive
amount on each retained compact patch. Use their action difference as a
normal coordinate. The actual inverse-strip correction from opening the
second tube is confined to an action-gap band of width O(sqrt(v)); its
clock width is O(sqrt(v)). Rescaling both quantities gives a compact
transition integral. Taylor expansion of the smooth densities supplies its
v coefficient and an O(v to power 3/2) remainder. The overlap of the two
physical endpoint tubes has volume O(h to power four), by the same argument
as CO9 with a fixed nonzero separation; it does not alter this conclusion.
Thus these pieces have the actual averaged primitive

```math
\begin{aligned}
N_{\mathrm{reg}}(v)&=b_1\sqrt v+b_2v+O(v^{3/2}).
\end{aligned}\tag{CO15}
```

Both coefficients are produced by the physical expansion and transition
integration. Their numerical values are not needed. There are no triple
minima, and the two ordinary seams are disjoint. At closing, CO11's b
coordinate works if b is nonzero. At b=0 the internal-seam time has positive
L derivative, and each rotation closing has nonzero L derivative by CG8.
These directions are tangent to their seam. They straighten closing without
changing its normal coordinate or removing its weight. On a single regular
null branch the derivatives of its arrival time in L,q,b are
`1/2-H_calligraphic-b^2/(2*L^2)`, the terminal x velocity, and `b/L`.
They cannot all vanish: if the last two vanish, the energy is at most 1/8
and the first derivative is at least 3/8. This proves the needed temporal-
level transversality in these actual coordinates. The cutoff shell at delta
is treated by the same moving-normal-coordinate integration; no cut seam
meets that small temporal level.
All such contributions still have CO15.

The chart where Delta-u tends to zero also belongs to this regular part.
Its limiting null generator is the unique straight v generator and has zero
screen tidal curvature. More explicitly, for small L the actual action is
`(q-p)^2/(2L)+L*A(L^2,p,q)` on the unique nearby lift, with smooth A from the
unit-interval ODE. Multiplying the broken action by
`2*L*t*(1-t)`, for s=L*t, gives a uniformly Morse quadratic with smooth
coefficients down to L=0 and t=0,1. Put `z0=L*(e-S_L)` and rescale its Morse
coordinate by `sqrt(2*z0*t*(1-t))`. CR7 then gives
`W=z0^2*B(L,p,q,z0)` with smooth positive B and `B(0,p,p,0)=pi/6`.
In the original temporal clock the derivative of z-zero at this long null
arrival is its time separation, at least delta. Hence the inverse and its
first two averaged coefficients are uniform there as well. Winding
competitors have the diverging kinetic gap. This proves CO15 without
silently dropping the Delta-u=0 neighborhood.

Integration by parts in the physical primitive CO15 continues its Mellin
transform to Re(z)<3/2, with only the simple poles at 1/2 and 1 and polynomial
vertical growth. The positive-phase remainder is entire. Consequently the
**whole** Z-long, not just a selected cusp sector, has only those two regular
poles and CO14's pole before the line Re(z)=4/3.

## 7. Signed response and restoration of the physical point

The kernel Mellin transform is

```math
\begin{aligned}
\widehat K_4(z)&=\Gamma(z)\prod_{j=1}^3(1-2z/j),\\
P_{\mathrm{long}}(\rho)
 &=\frac1{2\pi i}\int_{\Re z=c}
       \widehat K_4(z)\rho^{-z}Z_{\mathrm{long}}(z)\,dz,
 \qquad0\lt c\lt1/2.
\end{aligned}\tag{CO16}
```

Initial absolute convergence follows from CP6 and the gamma decay. Shift
the contour to Re(z)=4/3. The simple regular poles at 1/2 and 1 are canceled
by the exact kernel zeros. The only surviving pole is 9/7. All continued
factors have polynomial vertical growth, while gamma decays exponentially,
so the horizontal integrals vanish and the shifted integral is
O(rho to power -4/3). This rightward contour shift contributes minus the
residue. With the residue sign in CO14 it gives
`P_long=(9/7)*C_phys*K_hat(9/7)*rho^(-9/7)+O(rho^(-4/3))`.
The kernel product there is 22/343, positive. Multiplying by the unchanged
long factor `-beta4*rho^(3/2)` gives CO1's negative leading term.

Finally restore CP2 with the **same** delta. Its short action, including the
single physical point, tends to the independently computed target zero.
Its bounded remainder is smaller than the displayed long error. Every
regular pair, moving or closing contact, cutoff shell, competing well and
positive-phase complement has been accounted for above. No other part has
a 9/7 Mellin pole to cancel the derived positive source integral. This proves
CO1 for the complete canonical action.

## 8. Expectation, corrected theorem, and acceptance status

The actual finite atomless volume, closed ambient causal order, interval
containment and finite Poisson moments were already checked for CR4--CR9.
Apply the existing finite-density bridge **now**, to the unchanged observable
and original Poisson law. Its expectation equals the deterministic CR8
expression at every positive density, and therefore has CO1's negative
divergence. The asymptotic conclusion comes from sections 2--7, not from the
identity alone. Nothing here proves sample-wise convergence or divergence;
expectation divergence by itself is not a substitute for that separate task.

The precise refuted assertion is: every original curved 4D G-SS region has
the complete unit-field canonical action converging to
`(1/2)*integral R + integral_J coth(theta)`. This admitted smooth compact-
Cauchy example has target zero and the different complete asymptotic CO1.
It refutes the corresponding universal expectation limit as well.

The strongest general statements retained here are the geometric first
coefficient and o(rho) result CR3, the unchanged decomposition
`A_rho-T_g=L_g^delta(rho)+o(1)` from CP2, and the sufficient signed hypotheses
in CFT6/CP7--CP8. On the original class, convergence to the target is therefore
equivalent to vanishing of that **actual** complete long response; its
unconditional vanishing is false. No replacement universal long asymptotic
is asserted, no focusing is excluded from G-SS, and no subtraction or new
target is inserted into the observable.

All earlier integrated flat, short, focusing and Poisson results, including
#149/PR #163, are preserved. #151/#81 own this deterministic/expectation
obstruction and its review; their broader contracts, #24 and the independent
human/formal acceptance obligations #94/#86 are not automatically closed.
The accompanying Python checks distinguish the regenerated model certificate
from floating-point physical diagnostics. Neither is a Lean proof or
independent human validation of this complete written argument.

Refs #151, #81, #24, #94, #86.
