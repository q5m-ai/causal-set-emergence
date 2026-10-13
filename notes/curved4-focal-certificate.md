# Certifying the matched quartic coefficient

This continues [CR15–CR19](curved4-focal-research.md#6-match-the-normalized-model-before-assigning-a-sign-to-a-sector).
It concerns **the complete normalized quartic model**, including both wells,
the opening layer and both regular-side subtractions. It does not identify a
coefficient of the physical metric's complete action. The physical transfer
and the original #151/#81/#24 question remain separate.

The analytic bounds below reduce the sign question to a finite validated
integration. The implementation uses Arb ball arithmetic through
`python-flint`; its Gaussian rules are validated, not taken on trust from a
floating-point quadrature package. This is a written argument and a numerical
certificate, not a Lean theorem or independent human acceptance. Final
mathematical scrutiny remains a #94/#86 obligation.

## 1. A finite, explicitly bounded question

Use precisely CR17–CR18's definitions, with no change to their subtraction:

```math
\begin{aligned}
p&=9/7,\quad c=3\pi/8,\quad
 f_r(E)=\int_{\mathbb R}(E-u^2-4ru^3-u^4)_+^{3/2}\,du,\\
\Phi(E)&=\int_{-1/2}^{1/2}f_r(E)^{-p}\,dr,\\
a_0&=c^{-p},\qquad
 a_1=c^{-p}\left[-p/6+\tfrac12\left\{\int_0^1(1+t^2)^{-p}\,dt-1\right\}\right].
\end{aligned}\tag{CC1}
```

Put epsilon=1/100 and B=256. For all E between zero and epsilon we prove

```math
\begin{aligned}
-E^{-4/7}&\le
 \Phi(E)-a_0E^{-18/7}-a_1E^{-11/7}
 \le2E^{-4/7},\\
I&=M_{\varepsilon,B}+R_0+R_\infty,\\
M_{\varepsilon,B}
 &=\int_\varepsilon^B\Phi(E)\,dE
   -\tfrac7{11}a_0\varepsilon^{-11/7}
   -\tfrac74a_1\varepsilon^{-4/7},\\
-\tfrac73\varepsilon^{3/7}&\le R_0\le\tfrac{14}3\varepsilon^{3/7},\qquad
 0\le R_\infty\le3/640.
\end{aligned}\tag{CC2}
```

Thus neither a numerically unresolved head nor an omitted opening well can
be hidden in the finite computation. Section 4 gives the tail bound.

## 2. Uniform primary-well bounds

In the primary well use the signed Morse coordinate
`z=u*sqrt(1+4*r*u+u*u)`. For abs(r) at most 1/2 the two roots of
`1+4*r*u+u*u` have modulus one. On the complex u circle of radius 1/2,
abs(z) is at least 1/4. Rouche's theorem gives a unique inverse near zero
for abs(z) less than 1/4. Lagrange inversion and the beta moments give

```math
\begin{aligned}
f_{r,1}(E)&=cE^2F_r(E),\qquad F_r(E)=1+\sum_{j\ge1}c_j(r)E^j,\\
c_j(r)&=\frac{(1/2)_j}{(3)_j}
 [u^{2j}](1+4ru+u^2)^{-(2j+1)/2},\\
|c_j(r)|&\le C_j:=\binom{4j}{2j}\frac{(1/2)_j}{(3)_j},\qquad
 C_{j+1}\le16C_j,\\
c_1(r)&=5r^2-1/4,\qquad
 c_2(r)=1155r^4/8-315r^2/16+35/128.
\end{aligned}\tag{CC3}
```

The coefficient bound follows from the Gegenbauer integral representation:
its normalized integrand is a power of a complex number of modulus at most
one on the real parameter interval. Its endpoint value is the displayed
binomial coefficient. The ratio bound also follows directly from factorials.
All norms below use dr on [-1/2,1/2], a measure of total mass one.

Exact polynomial integration gives

```math
\begin{aligned}
\lVert c_1\rVert_2&\lt41/100,\qquad \lVert c_2\rVert_2\lt6/5,\\
\lVert c_3\rVert_2&\lt31/5,\qquad \lVert c_4\rVert_2\lt43,\\
C_2&=35/8,\qquad C_3=231/8,\\
C_4&=15015/64,\qquad C_5=138567/64,\\
\int F_r(E)^{-p}\,dr
 &=1-\tfrac p6E-\tfrac{249}{784}E^2
       -\tfrac{64983}{38416}E^3+\mathcal R(E),\\
 |\mathcal R(E)|&\le110E^4.
\end{aligned}\tag{CC4}
```

Here is an explicit remainder check, rather than a formal series assertion.
Writing `a=F_r(E)-1`, CC3 gives abs(a) at most 1.05E and its L2 norm at most
0.423E. The L2 norm of the remainder after `c1*E+c2*E^2+c3*E^3` is at most
69E to the fourth power: use 43 for the fourth coefficient and sum the tail
from C5 with ratio 16E. After expanding `(1+a)^(-p)` through a cubed, the
linear, quadratic and cubic truncation errors have respective bounds
`69*p`, `7.3*p*(p+1)/2` and `4.01*p*(p+1)*(p+2)/6`, times E to the fourth
power. The fourth Taylor remainder is at most
`2*(1.05)^2*(0.423)^2*E^4`. Their sum is less than 110E to the fourth power.
For example, the quadratic error follows from
`2*0.41*(6.2+0.69)+(1.2+0.062+0.0069)^2 < 7.3`.
These are rational inequalities; the implementation checks them exactly.
Consequently

```math
\begin{aligned}
\left|\int F_r(E)^{-p}\,dr-1+\tfrac p6E\right|&\le\tfrac7{20}E^2,\\
1-\tfrac3{10}E&\le F_r(E)\le1+\tfrac{21}{20}E
 \qquad(0\lt E\le1/100).
\end{aligned}\tag{CC5}
```

## 3. The second well and its moving opening boundary

Write q-r for the quartic in CC1. For r near 1/2 write its other minimum
as u=-b, put s=b squared and let d be that minimum's depth. Direct differentiation of the quartic gives

```math
\begin{aligned}
s&=\frac{1+\sqrt{1-12d}}2,\qquad
 r=\frac{2s+1}{6\sqrt s},\qquad
 |dr/dd|=\frac1{4s^{3/2}},\\
q_r(-b+y)&=d+\kappa y^2+h y^3+y^4,\qquad
 \kappa=2s-1,\quad h=\frac{2(1-4s)}{3\sqrt s},\\
F_2(E,d)&:=\frac{f_{r,2}(E)}{cE^2},\qquad
 (1-d/E)^2\le F_2(E,d)
 \le(1-d/E)^2(1+17E/5),\\
1&\le s^{-3/2}\le1+5d\qquad(0\le d\le E\le1/100).
\end{aligned}\tag{CC6}
```

To verify the volume bound, the two positive roots of
`y*y+h*y+kappa` have smaller root at least 857/1000; also s is at least
969/1000 and kappa at least 469/500. Thus kappa times that smaller root
squared exceeds 2/3. Lagrange inversion now has nonnegative coefficients,
majorized by `(3/2)^j*C_j`. The first normalized correction is
`31/(36*kappa^2)+5/(18*kappa^3*(kappa+1))`, at most 6/5. The remaining
series is bounded by `(315/32)*(E-d)^2/(1-24*(E-d))`. Its sum with the first
correction is at most `4*(E-d)/3`. Finally
`kappa^(-1/2) <= 1+3.3*d`, giving CC6. The last inequality in CC6 follows by
convexity and its endpoint value. All endpoint comparisons are rational
power inequalities checked by the implementation.

There are no other open wells at these energies: the quartic has at most
two minima. The second one opens precisely at d=E. Reflecting u handles the
other r endpoint. Put `t=1-d/E`, `a=997/1000`, and
`h(X,Y)=(X+Y)^(-p)-X^(-p)`, with `F1=F_{r(d)}(E)` the primary normalized
volume at the r determined by d. Then h increases with X and decreases with Y.
Its two first derivatives, CC5–CC6, and
`integral_0^1 t^2/(1+t^2)^2 dt = pi/8-1/4 < 1/7` imply

```math
\begin{aligned}
D_-&=\frac{51}{50}\left\{\frac{p(p+1)}{10}+\frac{17p}{35}\right\},\\
D_+&=\frac{51}{50}\left\{\frac{7p(p+1)}{20}+\frac{17p}{35}\right\},\qquad
 S_\pm=\frac{21}{20}D_\pm+\frac{5p}{12},\\
\int_0^1 s(E(1-t))^{-3/2}h(F_1,F_2)\,dt
 &\ge\int_0^1\{(1+t^2)^{-p}-1\}\,dt-S_-E,\\
\left|\int_0^1s(E(1-t))^{-3/2}h(F_1,F_2)\,dt
 -\int_0^1\{(1+t^2)^{-p}-1\}\,dt\right|&\le S_+E.
\end{aligned}\tag{CC7}
```

For clarity, the factor 51/50 bounds both negative powers of a needed in
the derivatives: even `a^(-4)` is smaller. The Jacobian correction uses
`1-(1+t*t)^(-p) <= p*t*t` and
`integral_0^1 (1-t)*t*t dt=1/12`. The two r endpoints give **E/2** times
CC7, not E/4. Combining CC5 and CC7, and using `a0 < 41/50`, proves CC2:
`(41/50)*(7/20+S_minus/2)<1` and
`(41/50)*(7/20+S_plus/2)<2`.
The opening-layer part of a1 in CC1 is present throughout this calculation.

## 4. The upper tail

For E at least one restrict u to abs(u) at most `E^(1/4)/2`. On that interval
`u^2+4*r*u^3+u^4 <= 9*E/16`, uniformly in r. Hence

```math
\begin{aligned}
f_r(E)&\ge(7/16)^{3/2}E^{7/4},\qquad
0\le\Phi(E)\le6E^{-9/4},\\
\int_{256}^\infty\Phi(E)\,dE&\le\frac{24}{5}\,256^{-5/4}=3/640.
\end{aligned}\tag{CC8}
```

The inequality for the constant follows by raising positive rationals to
the fourteenth power. This controls, rather than silently removes, the tail.

## 5. Validating the finite integral

For a fixed E the quartic is affine in r, so f is even and convex in r.
On [0,1/2], f and its derivative in r are nonnegative and increasing. For
`g=f^(-p)` and an r interval [a,b], this gives a bound on the total variation
of the distributional second derivative:

```math
\begin{aligned}
\lVert Dg'\rVert_{[a,b]}
 &\le p(p+1)f(a)^{-p-2}f_r'(b)\{f(b)-f(a)\}
       +pf(a)^{-p-1}\{f_r'(b)-f_r'(a)\},\\
f_r'(E,r)&=-6\int u^3(E-u^2-4ru^3-u^4)_+^{1/2}\,du.
\end{aligned}\tag{CC9}
```

A trapezoid on an interval of length h has error at most h squared times
this bound divided by eight. This remains valid at the well-opening and
well-merging transitions: convexity supplies the derivative measure; no
bounded pointwise second derivative is assumed. The derivative integral is
continuous and finite. Adaptive subdivision uses these rigorous error bounds,
not a difference between two numerical rules.

For the E integration define, for 0<a<b,

```math
\begin{aligned}
m(a)&=\frac{ca^2}{\sqrt{1+4\sqrt a}},\qquad
 R(b)=\frac{1+\sqrt{1+4\sqrt b}}2,\\
M(b)&=3R(b)\sqrt b,\qquad
 D(a)=2/5+6\max(1,a^{-1/4}),\\
\lVert\Phi''\rVert_{L^\infty([a,b])}
 &\le p(p+1)m(a)^{-p-2}M(b)^2+pm(a)^{-p-1}D(a).
\end{aligned}\tag{CC10}
```

One may improve M, when b is less than 1/16, to the smaller of its displayed
value and `c*b*(2+4/sqrt(1-4*sqrt(b)))`.

Here are the bounds behind CC10. Comparing with `(abs(u)+u*u)^2` gives
`f(E,r)>=m(E)` by the substitution `z=abs(u)+u*u`. The sublevel support of
`u*u*(1-abs(u))^2` lies in [-R(E),R(E)], giving the bound on the E derivative
of f. For small E its three positive-u inverse pieces give the improved M.
Integrating the second E derivative of f in r **first** yields

```math
\begin{aligned}
\int_{-1/2}^{1/2}f_{EE}(E,r)\,dr
 &=\frac34\int_0^\infty
 \frac{\sqrt{(E-u^2(1-u)^2)_+}-\sqrt{(E-u^2(1+u)^2)_+}}{u^3}\,du
 \le D(E).
\end{aligned}\tag{CC11}
```

For `u <= min(sqrt(E),1)/4`, rationalize the difference; its contribution is
less than 2/5. On the complement use the square-root Holder bound `2*u^(3/2)`;
its integral is at most `6*max(1,E^(-1/4))`. The weak chain rule and Fubini now
prove CC10, including transition energies. An E trapezoid has error at most
CC10's bound times its length cubed divided by twelve.

### Ball evaluations, roots and Gaussian rules

For each active interval between successive real roots l,h of the quartic,
put `x=l+(h-l)*t`. Polynomial division gives a positive quadratic Q with
`E-q(x)=(h-l)^2*t*(1-t)*Q(t)`. Thus f on this interval is an integral of
`Q(t)^(3/2)` with weight `t^(3/2)*(1-t)^(3/2)`, times `(h-l)^4`.
Arb isolates the quartic roots. Their disjoint ordered real enclosures,
together with `q(0)-E<0`, validate which intervals are active. At the exact
double-root case E=1/16, r=1/2, use
`f=1/(70*sqrt(2))` and `f_r'=17/(20*sqrt(2))` instead.

The n-point Gaussian nodes are roots of the degree-n Gegenbauer polynomial
with parameter 2. Floating-point roots are **only bracket seeds**: sign-changing
disjoint brackets account for all n roots, and Arb bisection refines them.
The exact weight formula and the polynomial identity used for evaluation are

```math
\begin{aligned}
C_n^2(\cos\theta)
 &=\frac{\sin((n+2)\theta)\cos\theta
          -(n+2)\cos((n+2)\theta)\sin\theta}{2\sin^3\theta},\\
w_i&=\frac{\pi(n+1)(n+2)(1-x_i^2)}
 {64(n+3)(C_{n-1}^2(x_i))^2},\qquad t_i=(1+x_i)/2,\\
\left|\int Q^{3/2}\,d\nu-\sum_iw_iQ(t_i)^{3/2}\right|
 &\le2q_*^{3/2}\left|\binom{1/2}{n-2}\right|
                \sum_iw_i|Q(t_i)/q_*-1|^{n-2}.
\end{aligned}\tag{CC12}
```

Here n is even, `dnu=t^(3/2)*(1-t)^(3/2) dt`, and q-star is the midpoint
of a proven nonnegative range for Q. That range makes abs(Q/q-star-1) at
most one. Expand the power 3/2 through degree n-2. Its absolute binomial
tail is bounded by `abs(binom(1/2,n-2))*abs(Q/q_star-1)^(n-2)`.
This latter function is a polynomial of degree 2n-4, so its Gaussian integral
is **also exact**. Positivity of the weights proves CC12. The derivative in
CC9 is independently enclosed by Arb integration, forwarding the analytic
flag to every square root. No uncertified quadrature error estimate is used.

## 6. Reproduction and acceptance boundary

`curved4_focal_certificate.py` regenerated **all 2,527 nodal enclosures**
for the saved `certificates/curved4-focal-model.json`, using 192-bit Arb
arithmetic and the pinned `python-flint==0.8.0`. It also checks all 25 explicit
rational inequalities used above. The E-quadrature error is less than
0.079960. Including nodal uncertainty, both analytic head bounds and the
upper tail gives the deliberately rounded, strictly positive certificate

```math
\begin{aligned}
\frac{1}{4}&\lt I\lt\frac{3}{2}.
\end{aligned}\tag{CC13}
```

The broad enclosure is a sign proof, not a numerical estimate of I's central
value. Regenerate it from the repository root with the Python 3.12 environment:

```sh
python -m pip install -r requirements.txt
python curved4_focal_certificate.py --head-checks
python curved4_focal_certificate.py --generate /tmp/curved4-focal-model.json --workers 2
python -m unittest -v test_curved4_focal_certificate
```

The default is one worker; two were used for the recorded local run after
checking available memory. The full regeneration is separate from the unit
tests. `--replay certificates/curved4-focal-model.json` rechecks the aggregation,
head and tail **but trusts the recorded nodal evidence**. It is not full
regeneration and does not authenticate an arbitrary supplied receipt. Receipt
bounds are outward-rounded dyadic integers; do not parse them as binary64.
The tests check the analytic arithmetic, Gaussian-rule validation, transitions,
selected nodal enclosures and this clearly labeled arithmetic replay.

The new Python dependency changes no Lean source, toolchain, checker or build
input. No new Lean audit or compiled geometric theorem is claimed.

The certificate establishes a property of I only. In particular, its positive
sign must not be renamed `C_phys`: physical source densities, uniform
subtracted matching and complete-action restoration require their own proofs.
Those are supplied separately in the [complete-action continuation](curved4-complete-action-obstruction.md),
not by this certificate. All action constants, the independent target,
ambient order, endpoint measures and original Poisson law remain unchanged.

Refs #151, #81, #24, #94, #86.
