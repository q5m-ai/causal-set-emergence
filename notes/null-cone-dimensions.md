# Required dimensional null producer: complete cone-ending limits (#156)

**Written theorem in every integer dimension at least two, for the geometric
cone-ending class below.** This discharges a required dimensional SN/NN branch,
not all of #156's quantified null/mixed contract. The two-tip theorem remains
separate. General null fronts, multiple future tips in other dimensions,
curved metrics and physical cut/caustic contacts retain explicit ownership in
[the required coverage ledger](null-mixed-required-coverage.md).

Inputs are the actual coefficient recurrence and interval moments in
[`dimension_kernels.py`](../dimension_kernels.py),
[the dimension interface](dimension-producer-interface.md), and the
single-tip geometry mechanism of #83/#84. No 4D Gaussian is extrapolated to
other dimensions. The **2D response has a different sign and tip mechanism**.
This is not a new Lean result or independent human mathematical review.
Refs #156, #81, #24, #94, #86.

## 1. Geometric class and independent target

For fixed integer d>=2 use Minkowski space with signature (+,-,...,-),
Lebesgue volume, closed ambient causal order and isolated restricted interval
counts. Let H on the spatial space be globally 1-Lipschitz with H(0)=T>0.
Require the open spatial set D={x:|x|<H(x)} to be bounded. On each ray,
r-H(r*omega) is nondecreasing and starts negative. Thus its negative set is
an initial interval, with endpoint R(omega), and

```math
\begin{aligned}
M_H&=\{(t,x):-H(x)\lt t\lt-|x|\},\\
D&=\{r\omega:0\le r\lt R(\omega)\},\qquad
 T/2\le R(\omega)\le B\lt\infty,\\
J&=\{(-R(\omega),R(\omega)\omega):\omega\in S^{d-2}\},\\
\mathcal J_H&=\int_{S^{d-2}}R(\omega)^{d-2}\,d\omega.
\end{aligned}
\tag{ND1}
```

For the stratum/area interpretation impose only the following **geometric**
regularity, not an analytic response condition. The lower boundary is a finite
piecewise smooth achronal spacelike/null graph with its seams/tips inventoried;
near its intersection with the upper cone the smooth pieces are radially
transverse, `1-partial_r H>0` on their compact closures. R is continuous and
piecewise smooth, with finite piece interfaces of zero sphere area. The joint
is covered almost everywhere by regular SN or past–future NN pieces with
positive induced metric. In d=2 the sphere is the two counting atoms, so
both endpoints must be regular: a higher intersection cannot be erased as a
zero-area exception. No timelike face is admitted.

These hypotheses include every smooth globally strict-Lipschitz floor of
#84, in every dimension. They also include **every flat causal diamond**, by
H(x)=T-|x|: the lower cone's one past tip is explicitly present, R=T/2, and
the joint is regular past–future NN. Piecewise spacelike/null lower graphs
satisfying the stated geometric crossing condition are allowed; no arbitrary
extra future crease is inferred. For the smooth strict-Lipschitz case, compact
closure and the crossing margins follow as in MA1–MA7. For the diamond they
follow directly from the displayed H. Null boundaries are fixed from the
outset, not limits of spacelike boundaries.

The positive induced joint metric is R² times the sphere metric on every
smooth piece: time and radial derivatives cancel. Thus (ND1) is its independent
SN/NN screen area, with unit candidate weight, not an action-defined measure.
In d=2 it is exactly 2 with counting measure. The flat bulk curvature is zero.
The whole frontier is the lower graph, upper cone, their joint, the future
tip, and the stipulated lower seams/tips and their intersections. There is no
lateral wall. None of their normalized neighborhoods is discarded below.

The epigraph t+H(x)>0 is a future set even when the Lipschitz constant is
one. The upper cone is a past set. This proves closed ambient interval
containment for every pair in M_H. It also gives the **stronger actual fibre**:
all future partners of each p in M_H form the complete interval I(p,0), up to
the zero-volume upper boundary. A translated or Lorentz-transported instance
is valid only by the usual measure/order transport, not by identifying an
arbitrary flat quotient with this domain.

## 2. Canonical action and the actual dimensional source response

Keep exactly the constants c_d,a_d,beta_d and the recurrence K_d=P_d*exp(-z)
from the dimension interface. Put q=d/2 and m=floor(d/2)+1. The action is

```math
\begin{aligned}
\mathcal A_{\rho,d}(M_H)&=\rho^{2/d}\left[a_d|M_H|-\beta_d\rho
 \int_{M_H}\int_{M_H\cap J^+(p)}K_d(c_d\rho\sigma(p,y)^q)\,dy\,dp\right],\\
z&=c_d\rho\sigma(p,0)^q,\\
B_d(z)&=a_d-\beta_d\rho\int_{I(p,0)}K_d(c_d\rho\sigma(p,y)^q)\,dy,\\
\mathcal A_{\rho,d}(M_H)&=\rho^{2/d}\int_{M_H}B_d(c_d\rho\sigma(p,0)^q)\,dp.
\end{aligned}
\tag{ND2}
```

The last line retains all partners and cancels the actual point term only
through the derived response. At finite density compact domination justifies
Fubini and uniformly absolutely convergent power series on each interval.
The coefficient of (-z)^n/n! in K_d is
`Q_d(n)=(d*n/2+1)_m/m!`. The actual unit-duration interval moment, divided by
c_d, is `Gamma(d)/[(n+1)*(d*n/2+1)_(d-1)]`. Consequently the complete partner
integral has series

```math
\begin{aligned}
\rho\int_{I(p,0)}K_d
 &=\sum_{n=0}^\infty\frac{(-1)^n z^{n+1}}{n!}
 \frac{\Gamma(d)(qn+1)_m}{m!(n+1)(qn+1)_{d-1}}.
\end{aligned}
\tag{ND3}
```

The series follows from the unchanged recurrence and the actual interval
moment beta integral; it is not an assumed large-density cancellation.
In particular the simplification differs in low dimensions:

```math
\begin{aligned}
B_2(z)&=2(1-z)e^{-z},\\
B_3(z)&=a_3e^{-z},\qquad B_4(z)=a_4e^{-z}.
\end{aligned}
\tag{ND4}
```

For d>=5 set ell=d-1-m>=1 and `C_d=Gamma(d)/(m!*Gamma(ell))`. Cancel the
rising factorials in (ND3), use
`1/(qn+m+1)_ell = integral_0^1 t^(qn+m)*(1-t)^(ell-1) dt/Gamma(ell)`, and sum
`z*sum((-z*t^q)^n/(n!*(n+1)))=(1-exp(-z*t^q))/t^q`. This gives, exactly,

```math
\begin{aligned}
\rho\int_{I(p,0)}K_d
 &=C_d\int_0^1 t^{m-q}(1-t)^{\ell-1}(1-e^{-zt^q})\,dt,\\
a_d&=\beta_d C_d\,\mathrm B(m-q+1,\ell),\\
B_d(z)&=\beta_d C_d\int_0^1
                 t^{m-q}(1-t)^{\ell-1}e^{-zt^q}\,dt.
\end{aligned}
\tag{ND5}
```

The middle equality is elementary substitution of the **existing** odd/even
a_d,beta_d, not a new coefficient choice. The beta integral also justifies
sum/integral interchange at fixed finite z by absolute domination. Thus for
d>=3 the complete signed response is nonnegative and at most a_d. For d>=5
it is a mixture, generally with an algebraic tail, **not** a Gaussian. Setting
it to a_d*exp(-z) would remove real partners/cancellations.

## 3. Derived mass and full deterministic limit for d>2

Tonelli on (ND5), followed by an elementary gamma integral, proves finite
mass in the scaled proper-time-squared variable. For d=3,4 use (ND4).
Substituting the original constants gives

```math
\begin{aligned}
\int_0^\infty B_d(u^q)\,du
 &=\beta_d C_d\Gamma(1+1/q)\,\mathrm B(m-q,\ell)
       &&(d\ge5),\\
c_d^{-2/d}\int_0^\infty B_d(u^q)\,du&=2(d-2)
       &&(d>2).
\end{aligned}
\tag{ND6}
```

Here m-q is 1 in even dimension and 1/2 in odd dimension, so the integral is
actually finite. For a direct normalization check,
`B(m-q,ell)/B(m-q+1,ell)=(q-1)/(m-q)`; with a_d equal to 4 or 2 times
`c_d^(2/d)/Gamma(1+2/d)` this is exactly 2(d-2). No divergent absolute moment
is assigned an analytic-continuation value.

Use p=(-sqrt(r²+s),r*omega) in the full source integral. The actual source
coarea weight is

```math
\begin{aligned}
W(s)&=\int_{S^{d-2}}\int_0^B
 \mathbf1_{\sqrt{r^2+s}\lt H(r\omega)}
 \frac{r^{d-2}}{2\sqrt{r^2+s}}\,dr\,d\omega,\\
0\le W(s)&\le\frac{|S^{d-2}|B^{d-2}}{2(d-2)},\qquad
W(s)\longrightarrow W(0)=\frac{\mathcal J_H}{2(d-2)},\\
\mathcal A_{\rho,d}(M_H)
 &=c_d^{-2/d}\int_0^\infty B_d(u^q)
       W(u/(c_d\rho)^{2/d})\,du
 \longrightarrow\mathcal J_H.
\end{aligned}
\tag{ND7}
```

The radial domain is a subset of (0,R) for positive s. At every fixed
0<r<R the strict height gap persists for sufficiently small s. Domination
by r^(d-3)/2 proves W's right continuity; **no assumption that every positive-s
slice starts at zero is used**. The new positive, integrable mass (ND6)
then proves the last limit on the full domain. This includes all generator
lengths, lower seams/tips, joint intersections and closing radial slices.
No short/long partition or null-face limiting family is involved.

If the future tip is localized by r<delta, the same argument bounds its
all-partner action at every density by `|S^(d-2)|*delta^(d-2)`. This is a
derived normalized estimate for d>2, not a measure-zero argument and not a
claim about each arbitrary boundary-weighted observable.

## 4. The genuinely different two-dimensional proof

The coarea majorant r^(d-3) is not integrable when d=2. We do **not** reuse
(ND7). There are two rays, with positive finite endpoints R+ and R-. The
crossing hypotheses at their regular joints give a fixed radial margin;
away from the endpoints, compactness and the strict gap give clearance.
For small s, the removed radii are therefore an endpoint shell of width
O(s), bounded away from r=0. The exact primitive on each full original ray is
`asinh(R/sqrt(s))/2`. Subtracting its actual removed shell proves

```math
\begin{aligned}
W(s)&=-\tfrac12\log s+\tfrac12\log(4R_+R_-)+O(s),\\
\int_0^\infty(1-u)e^{-u}\,du&=0,\qquad
\int_0^\infty(1-u)e^{-u}\log u\,du=-1,\\
\mathcal A_{\rho,2}(M_H)
 &=\frac2{c_2}\int_0^\infty(1-u)e^{-u}W(u/(c_2\rho))\,du
 \longrightarrow\frac1{c_2}=2=\mathcal J_H.
\end{aligned}
\tag{ND8}
```

In deriving the shell bound, radial transversality is needed only near each
endpoint, not on the entire lower face. It holds for both smooth strict
floors and the diamond's H=T-r. The existing c_2 is 1/2. The constant and
log-density pieces cancel by the first signed identity; the second supplies
the counting normalization. For a fully justified remainder bound, split s
at one fixed small s0: the remainder is O(s) below it; beyond it the compact
weight is bounded by a constant plus |log(s)| and the Gaussian/exponential
tail dominates. Take density to infinity with s0 fixed. No interchange with
a shrinking geometric cutoff is used.

A useful warning follows from this full computation. A small actual future
tip cap with floor H=delta has limiting action **2** for every fixed delta>0.
Its all-partner response inside any larger cone-ending region is the same,
by the complete future fibre. Thus the vanishing tip bound from d>2 cannot
be extended to d=2. This is a localization warning, **not** a counterexample
to the complete counting-target theorem (ND8). It is precisely why dimensions
and stratum attribution cannot be copied from the 4D proof.

## 5. Complete partitions and separate expectation theorem

Equations (ND2)–(ND8) prove the complete deterministic conclusion. Finite
source partitions retain partners in the original region. A further partner
partition keeps all ordered index pairs; their point diagonal weights sum
to one. Any fixed positive cutoff uses the exact signed short/complement
identity of the dimension interface, with the point allocated once. Neither
piece is discarded; the proof evaluates their exact sum. These identities
remain valid for source-dependent measurable masks. No independent action
for each chart replaces the physical action.

For expectation, M_H is nonempty open and bounded; its volume is finite and
positive. Continuity of H and the cone gives Borel region/order/interval
relations. Lebesgue measure is atomless; boundary graphs, null cones and
singletons are volume-null. The future/past-set proof in §1 contains every
closed interval between actual endpoints, so the genuine restricted volume
is c_d*sigma^(d/2), not an intrinsic-order substitute. The finite Poisson law
is constructed separately from rho times this restricted volume. Its finite
second factorial moment controls the minimal-layer action, since each layer
count is at most N(N-1) and there are only m+1 finite coefficients.

Reduced two-point Mecke, with the actual exclusive interval and ordered
endpoints, gives the k-th layer mean `rho² * integral exp(-rho*V)*(rho*V)^k/k!`.
Multiplication by the existing coefficients `k!*[z^k]P_d` yields exactly the
kernel in (ND2). Hence for every positive density, separately from the
asymptotics,

```math
\begin{aligned}
\mathbb E[A^{\mathrm{disc}}_{\rho,d}]&=\mathcal A_{\rho,d}(M_H),\\
\lim_{\rho\to\infty}\mathbb E[A^{\mathrm{disc}}_{\rho,d}]&=\mathcal J_H.
\end{aligned}
\tag{ND9}
```

The generic dimension-indexed measured-order/Poisson bridge is accepted
source; the geometric specialization and new analytics here are written,
not new compiled instances. No sample-wise convergence or limit/expectation
interchange is asserted.

## 6. Actual coverage and verification

This is an actual producer **and complete assembly** for the specified
cone-ending class in all d>=2, not a finite survey of examples or conditional
jet transfer. It includes every smooth strict-Lipschitz single-cone SN member,
and supplies a direct every-integer-dimensional diamond proof with its
independent NN area `|S^(d-2)|*(T/2)^(d-2)` (2 in d=2). This supplies that
mathematical input directly; it does not retroactively expand the inspected
literature's 2–16 proof attribution or resolve Chevalier primary-text access.

The new diagnostic module `null_cone_dimensions.py` compares the response
against the actual signed rest-interval integral, not just another formula
for the mixture. `test_null_cone_dimensions.py` checks every factor and both
parities, point normalization and mass, the non-Gaussian high-dimensional
response, the signed 2D logarithmic/tip mechanism, all-dimensional diamond
and nonplanar finite-density source integrals, and wrong-normalization
controls. Finite tests and quadrature refinements are not quantified proofs.

No Lean/checker/dependency/build inputs change. Applicable Python/symbolic,
Markdown, exact-head CI and browser checks are delivery evidence, not a new
formal audit or human acceptance. The unresolved required rows and actual
failed continuations are in the coverage ledger; #156/#81/#24 remain open.
