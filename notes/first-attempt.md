# First proof attempt — four-dimensional flat regions

**Status:** a self-contained proof draft for the two classes below, with symbolic
and numerical checks. Not independently reviewed. No claim of priority or of a
proof of the full conjecture. The variable-angle result here has a **planar
future boundary**; it is not a localization theorem for two arbitrary boundaries.

**Formalization:** [the Lean layer](../formal/README.md) checks supporting
algebra, a generic signed-kernel limit lemma, concrete kernel scaling,
differentiation of the auxiliary integral through order three, and its
finite-interval mass and signed first-moment identities. It does not yet verify
either main theorem, the half-line kernel normalization and tail estimates,
or the Poisson-expectation bridge. Explicit full-theorem targets are defined
without asserting unproved results.

## 1. Precise target and conventions

We use Conjecture 1′, equation (11), of Dowker–Liu–Lloyd-Jones,
[arXiv:2501.00139v2](https://arxiv.org/html/2501.00139v2#S2.E11).
In four-dimensional Minkowski space with signature \((-+++ )\), its flat-space
specialization is

\[
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_J\coth\theta\,dA,
 \qquad \mathcal A_\rho:=\frac{l_p^2}{\hbar}\mathbb E S^{(4)}_\rho.
 \tag{1}
\]

Here \(\rho=l^{-4}\), and \(J\) is the intersection of the past and future
boundaries, not the collection of all boundary seams. At a joint with a null
face we use the conjecture's limiting convention \(\coth\theta=1\).
We prove statements about the **mean**, not about concentration of individual
sprinklings. All geometric parameters are fixed as \(\rho\) increases.

Set

\[
 c=\frac\pi{24},\qquad
 P(z)=1-9z+8z^2-\frac43z^3,\qquad K(z)=P(z)e^{-z}.
\]

For a bounded causally convex region, Poisson interval counting gives exactly

\[
 \mathcal A_\rho(M)=\frac4{\sqrt6}\sqrt\rho
 \left[|M|-\rho\int_M dx\int_{J^+(x)\cap M}dy\,
 K\bigl(c\rho\tau_{xy}^4\bigr)\right].
 \tag{2}
\]

Causal convexity is essential: it makes the interval volume equal to the full
Minkowski value \(c\tau^4\). We prove this property for our regions rather than
assuming that every globally hyperbolic subregion of Minkowski space has it.
Boundary sets have four-volume zero and do not affect (2).

## 2. An exact interval identity

For a causal interval \(I(x,q)\) of proper duration \(T\),

\[
 \rho\int_{I(x,q)}K(c\rho\tau_{xy}^4)\,dy
       =1-e^{-c\rho T^4}.
 \tag{3}
\]

**Proof.** Put \(x=0\), \(q=(T,\mathbf0)\), and use radial null coordinates
\(u=(t-r)/\sqrt2\), \(v=(t+r)/\sqrt2\). Their domain is
\(0\le u\le v\le T/\sqrt2\), and the angularly integrated measure is
\(2\pi(v-u)^2\,du\,dv\). Consequently, for every integer \(n\ge0\),

\[
 \int_{I(x,q)}\tau_{xy}^{4n}\,dy
 =\frac{\pi T^{4n+4}}
 {(2n+1)(2n+2)(2n+3)(4n+4)}.
 \tag{4}
\]

The coefficient of \(z^n\) in \(K(z)\) is

\[
 \frac{(-1)^n}{n!}q_n,\qquad
 q_n=\frac{(n+1)(2n+1)(2n+3)}3.
\]

Inserting (4) into the uniformly convergent power series for the kernel gives

\[
 \int_I K(c\rho\tau^4)\,dy
 =cT^4\sum_{n\ge0}\frac{(-c\rho T^4)^n}{(n+1)!},
\]

which is (3). This also independently reproduces the flat specialization of
Dowker's equations (4.8)–(4.13), specifically the flat term in (4.9),
[arXiv:2007.13206v2](https://arxiv.org/html/2007.13206v2).
\(\square\)

## 3. First class: one null-cone future boundary

### Theorem 1

Let \(q\) be an event and \(F\) an open future set, meaning
\(J^+(F)\subset F\), with \(q\in F\). Suppose

\[
 M=F\cap I^-(q)
\]

is bounded. Put \(q=0\). Assume the trace of \(F\) on the past null cone is
\(0\le r<R(\omega)\), where \(\omega\in S^2\) and \(R>0\) is bounded and
piecewise \(C^1\). More precisely, require cone points with \(r>R(\omega)\)
to lie outside \(\overline F\); exceptional directions of measure zero are
harmless. Thus the joint is the radial section

\[
 J=\{(-R(\omega),R(\omega)\omega):\omega\in S^2\}.
\]

Then

\[
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_{S^2}R(\omega)^2\,d\omega=\operatorname{Area}(J).
 \tag{5}
\]

**Proof.** A future set intersected with a past set is causally convex. Strong
causality is inherited from Minkowski space, and the causal diamond between
any two points of \(M\) is the full compact Minkowski diamond contained in
\(M\). Hence \(M\) is globally hyperbolic.

For \(x\in M\), the entire interval \(I(x,q)\) lies in \(F\). Therefore
\(J^+(x)\cap M=I(x,q)\) up to measure-zero sets. Equation (3) reduces the
bilocal action to the positive integral

\[
 \mathcal A_\rho(M)
 =\frac4{\sqrt6}\sqrt\rho\int_M
             e^{-c\rho\tau_{xq}^4}\,dx.
 \tag{6}
\]

Write \(t=-\sqrt{r^2+\sigma}\), \(\sigma=\tau_{xq}^2\ge0\). Then

\[
 dx=\frac{r^2}{2\sqrt{r^2+\sigma}}\,d\sigma\,dr\,d\omega.
\]

For a sufficiently large fixed \(B\), define

\[
 W(\sigma)=\int_{S^2}\int_0^B
 \frac{r^2}{2\sqrt{r^2+\sigma}}
 \mathbf1_F(-\sqrt{r^2+\sigma},r\omega)\,dr\,d\omega.
\]

The integrand is bounded by \(r/2\). The trace hypotheses and dominated
convergence imply

\[
 W(0+)=\frac14\int_{S^2}R(\omega)^2\,d\omega.
\]

On the half-line, \((4/\sqrt6)\sqrt\rho e^{-c\rho\sigma^2}\) has total
mass **4**, independent of \(\rho\), and concentrates at zero. Boundedness
and the right limit of \(W\) prove (5).

Finally the induced metric of this cone section is \(R^2d\omega^2\):
the time contribution \(-dR^2\) cancels the radial spatial contribution.
Its area is exactly the right-hand side of (5). Each joint face has a null
future face, so (1) has this same right-hand side. \(\square\)

### Corollary 1: null-plane-truncated diamond

Take \(p=(-T,\mathbf0)\), \(q=0\), \(T>0\), and \(0<a<T\). With spatial
coordinate \(z\), retain the future side of a null plane:

\[
 M_{T,a}=I^+(p)\cap I^-(q)\cap\{t-z>-a\}.
 \tag{7}
\]

This is a genuine truncation, not a rescaled diamond. If
\(\mu=\omega_z\), its joint section has radius

\[
 R(\mu)=\min\left(\frac T2,\frac a{1+\mu}\right),
\]

with the second term interpreted as infinite at \(\mu=-1\). Thus

\[
 \boxed{\lim_{\rho\to\infty}\mathcal A_\rho(M_{T,a})
       =\pi a(2T-a).}
 \tag{8}
\]

Indeed, splitting the angular integral at \(\mu=2a/T-1\) gives
\(\pi aT\) from the surviving original joint and \(\pi a(T-a)\) from the
new plane–cone joint. The seam between these patches has area zero.

For reproducible finite-density checks, the exact weight in (6) is

\[
 W_{T,a}(\sigma)=\frac\pi4\left[
 a(2T-a)-2(1-a/T)\sigma-\frac{\sigma^2}{T^2}
 -2\sigma\log\frac{aT}{\sigma}\right],\quad 0<\sigma<aT,
 \tag{9}
\]

and zero above \(aT\), with \(W(0)=\pi a(2T-a)/4\). To obtain this, at
fixed \(\sigma\) set \(w=-t=\sqrt{r^2+\sigma}\); the allowed solid angle
is \(2\pi\min(2,\max(0,1+(a-w)/r))\), and
\(r\le(T^2-\sigma)/(2T)\). The change \(r\,dr=w\,dw\) makes the two
angular regimes elementary integrals of \(\sqrt{w^2-\sigma}\).
Integrating (9) also gives

\[
 |M_{T,a}|=\frac{\pi a^2T(3T-2a)}{24}.
\]

For fixed \(T,a\), (9) yields an error
\(O(\rho^{-1/2}\log\rho)\), with lengths held in fixed units.

## 4. A different exact reduction: planar future boundary

The null-cone theorem does **not** test finite \(\theta\). For that we change
the future boundary to a spacelike plane while keeping its causal future
slices exactly computable.

Let \(\Omega\subset\mathbb R^3\) be bounded with \(C^3\) boundary. Let
\(h\in C^3(\overline\Omega)\) satisfy

- \(h>0\) in \(\Omega\) and \(h=0\) on \(\partial\Omega\);
- \(\nabla h\ne0\) on \(\partial\Omega\);
- the extension \(h_+\), equal to \(h\) inside and zero outside, is globally
  \(\kappa\)-Lipschitz for some fixed \(\kappa<1\).

Consider

\[
 M_h=\{(t,x):x\in\Omega,\ -h(x)<t<0\}.
 \tag{10}
\]

The epigraph \(t>-h_+(x)\) is a future set: along a future causal displacement
\((\Delta t,\Delta x)\), \(t+h_+(x)\) increases by at least
\((1-\kappa)\Delta t\). Intersecting it with \(t<0\) proves causal
convexity and global hyperbolicity as in Theorem 1.

For a point at depth \(H=-t\), its future in \(M_h\) is exactly the complete
future cone truncated at time \(H\). In particular, no lateral boundary was
introduced. Define

\[
 F_\rho(H)=4\pi\int_0^H r^2 e^{-c\rho(H^2-r^2)^2}\,dr.
 \tag{11}
\]

The action density obtained by doing the future-point integral first is

\[
 L_\rho(H)=\frac{\sqrt\rho}{2\pi\sqrt6}F_\rho'''(H).
 \tag{12}
\]

This is an exact identity, not an asymptotic expansion.

### Verification of (12), including the boundary constant

Let \(m_n=\int_0^1v^2(1-v^2)^{2n}\,dv=\tfrac12B(3/2,2n+1)\). Then

\[
 F_\rho(H)=4\pi\sum_{n\ge0}
 \frac{(-c\rho)^n}{n!}m_nH^{4n+3}.
\]

The integral of \(K\) over the truncated future cone is

\[
 Q_\rho(H)=4\pi\sum_{n\ge0}
 \frac{(-c\rho)^n}{n!}q_nm_n\frac{H^{4n+4}}{4n+4}.
\]

For \(n\ge1\), the beta-function recurrence gives

\[
 \frac12(4n+1)(4n+2)(4n+3)m_n
       =24q_{n-1}m_{n-1}.
\]

Since \(c=\pi/24\), comparison of coefficients proves
\(F_\rho'''/(8\pi)=1-\rho Q_\rho\). This is (12) by (2).
In particular \(F_\rho'''(0)=8\pi\); losing this constant would lose the
bulk cancellation. Uniform convergence on finite \(H\)-intervals justifies
all differentiations here.

**Checked differentiation, separate from the action-density identity.**
Writing \(r=Hv\) in (11) gives a fixed interval \(0\le v\le1\).
With \(z=c\rho H^4(1-v^2)^2\), its first three parameter derivatives have
integrands \(H^{3-j}v^2R_j(z)e^{-z}\), where
\(R_1=3-4z\), \(R_2=6-36z+16z^2\), and
\(R_3=6-204z+288z^2-64z^3\). For each differentiation, the integrand
and its derivative are jointly continuous and uniformly bounded on every
compact parameter rectangle. This justifies differentiation under the integral.
The argument, including \(F_\rho'(0)=F_\rho''(0)=0\) and
\(F_\rho'''(0)=8\pi\), is now machine-checked in `KernelDerivatives.lean`. The series comparison with
\(Q_\rho\), and thus (12) as an identity for the original action density,
remain formalization obligations.

Integrating (12) over each vertical fibre of (10), using
\(F_\rho''(0)=0\), gives the second exact reduction:

\[
 \boxed{\mathcal A_\rho(M_h)=\int_\Omega G_\rho(h(x))\,dx,\qquad
 G_\rho(H)=\frac{\sqrt\rho}{2\pi\sqrt6}F_\rho''(H).}
 \tag{13}
\]

## 5. The signed approximate identity

Put \(\varepsilon=\rho^{-1/4}\), \(F=F_1\), and
\(G=F''/(2\pi\sqrt6)\). Scaling (11) gives

\[
 G_\rho(H)=\varepsilon^{-1}G(H/\varepsilon).
 \tag{14}
\]

Equation (14) is machine-checked in `KernelScaling.lean`, directly from (11)
with the positive inverse width \(\sqrt{\sqrt\rho}\). This does not presume
any mass or tail estimate.

The kernel satisfies

\[
 G\in L^1(0,\infty),\qquad
 \int_0^\infty G(u)\,du=1,\qquad
 \int_0^\infty u|G(u)|\,du<\infty.
 \tag{15}
\]

It is **not positive**. Its negative tail must not be discarded.

The finite-interval identities
\[
 \int_0^U G(u)\,du=\frac{F'(U)}{2\pi\sqrt6},\qquad
 \int_0^U uG(u)\,du=\frac{UF'(U)-F(U)}{2\pi\sqrt6}
\]
are now machine-checked by the fundamental theorem of calculus. The following
passage to infinity, including **absolute** integrability in (15), is still
an analytic-draft argument, not a completed Lean proof.

**Proof of (15).** Near zero, (11) gives
\(F(u)=4\pi u^3/3+O(u^7)\), so \(G(u)=4u/\sqrt6+O(u^5)\).
For large \(u\), change variable to \(s=u^2-r^2\):

\[
 F(u)=2\pi\int_0^{u^2}\sqrt{u^2-s}\,e^{-cs^2}\,ds
     =2\pi\sqrt6\,u-\frac{12}{u}+O(u^{-3}).
 \tag{16}
\]

The remainder in (16) may be differentiated twice (or three times), with
its \(j\)-th derivative \(O(u^{-3-j})\). Here is a justification rather
than an assumption about differentiating an asymptotic expansion. Insert a
smooth cutoff \(\chi(s/u^2)\) equal to one for \(s/u^2\le1/2\) and zero
for \(s/u^2\ge3/4\). On its support Taylor-expand
\(\sqrt{1-s/u^2}=1-s/(2u^2)+O(s^2/u^4)\), with the corresponding bounds
on its first three \(u\)-derivatives. Integrating these bounds against the
Gaussian gives the stated derivative remainders. Derivatives of the cutoff
are exponentially small. For the complementary integral, return to
\(r=uv\); its support has \(1-v^2\ge1/2\), so this integral and its first
three derivatives are polynomial factors times \(e^{-c u^4/4}\).

It follows that

\[
 G(u)=-\frac{2\sqrt6}{\pi u^3}+O(u^{-5}),
 \qquad F'(\infty)=2\pi\sqrt6,\qquad F'(0)=0.
\]

These facts give absolute integrability, the finite absolute first moment,
and
\(\int G=[F'(\infty)-F'(0)]/(2\pi\sqrt6)=1\).
One also has the signed moment \(\int_0^\infty uG(u)\,du=0\), since
\(uF'(u)-F(u)\to0\). \(\square\)

## 6. Variable-angle theorem

### Theorem 2

For every graph cap (10) satisfying the stated hypotheses,

\[
 \boxed{\mathcal A_\rho(M_h)
 =\int_{\partial\Omega}\frac{dA}{|\nabla h|}
       +O(\rho^{-1/4})
 =\int_J\coth\theta\,dA+O(\rho^{-1/4}).}
 \tag{17}
\]

Constants in the error estimate may depend on the fixed region. The estimate
is not asserted uniformly as the joint becomes tangent, \(|\nabla h|\to0\).

**Proof.** By regularity and compactness of the joint there is a collar
\(0\le h\le\delta\) with no critical points. Coarea gives a \(C^1\)
function on this interval,

\[
 B(s)=\int_{h=s}\frac{dA_s}{|\nabla h|},\qquad
 B(0)=\int_{\partial\Omega}\frac{dA}{|\nabla h|}.
\]

The contribution of this collar to (13) is

\[
 \int_0^{\delta/\varepsilon}G(u)B(\varepsilon u)\,du.
\]

Using (15), its difference from \(B(0)\) is bounded by

\[
 \|B'\|_\infty\varepsilon\int_0^\infty u|G(u)|\,du
 +|B(0)|\int_{\delta/\varepsilon}^\infty|G(u)|\,du
 =O(\varepsilon)+O(\varepsilon^2).
\]

For sufficiently small \(\varepsilon\), on the remainder \(h\ge\delta\)
the tail estimate gives
\(|G_\rho(h)|\le C\varepsilon^2 h^{-3}\). Its integral is
\(O(\varepsilon^2|\Omega|\delta^{-3})\). This argument permits critical
points of \(h\) away from the joint; no regularity of interior level sets
is being assumed. The first equality in (17) follows.

At a joint point let \(n\) be the inward unit spatial normal and
\(k=|\nabla h|\in(0,1)\). The tangent vectors orthogonal to the joint and
pointing into the respective faces can be chosen as

\[
 a=(0,n),\qquad b=(-k,n).
\]

Thus
\(\cosh\theta=1/\sqrt{1-k^2}\), \(\tanh\theta=k\), and
\(\coth\theta=1/k\). This proves the second equality and hence the modified
conjecture for this class. \(\square\)

### Corollary 2: an explicit connected joint with nonconstant angle

Let \(b_i>0\), \(0<a<\tfrac12\min b_i\), and set

\[
 \Omega=\left\{\sum_{i=1}^3x_i^2/b_i^2<1\right\},\qquad
 h(x)=a\left(1-\sum_{i=1}^3x_i^2/b_i^2\right).
 \tag{18}
\]

The positive-part extension is \(2a/\min b_i\)-Lipschitz. On the joint,
parametrized by \(x_i=b_i\omega_i\),

\[
 \tanh\theta(\omega)=2a\sqrt{\sum_i\omega_i^2/b_i^2}.
\]

This varies on a single connected joint whenever the axes are not all equal.
Since

\[
 |\{h>s\}|=\frac{4\pi}{3}b_1b_2b_3(1-s/a)^{3/2},
\]

Theorem 2 gives the completely explicit value

\[
 \boxed{\lim_{\rho\to\infty}\mathcal A_\rho(M_h)
        =\frac{2\pi b_1b_2b_3}{a}.}
 \tag{19}
\]

For \((b_1,b_2,b_3)=(1,2,3)\), \(a=1/4\), the prediction is \(48\pi\),
and \(\tanh\theta\) ranges from \(1/6\) to \(1/2\). This is not merely a
family of constant-angle examples.

## 7. What remains outside this attempt

- Two independently curved spacelike faces: the exact future-cone reduction
  fails. A new estimate for the bilocal kernel is needed.
- General dimension: neither four-dimensional kernel reduction is being
  asserted unchanged in other dimensions.
- General null boundaries, tangential/degenerate joints, or varying the
  geometry simultaneously with density.
- Variance and convergence in probability of the unsmeared random action.
- Independent proof review and a broader novelty/literature check.

A tempting but invalid shortcut is to say that the kernel localizes at short
coordinate separations and then add local wedge answers. Nearly null pairs
can have macroscopic coordinate separation and small interval volume. Our
proofs avoid that step: the complete future integral is done exactly first,
and the remaining limit has an explicit dominating bound or an integrable
signed-kernel estimate. Numerical agreement alone would not repair a missing
bound at this step.
