# Direct-origin short analysis: partial implementation of #97

**Subsequent integration:** #106 supplies the separate
[independent-envelope geometry](../formal/INDEPENDENT_FACE_GEOMETRY.md), and
[#107's actual short proof](../formal/INDEPENDENT_SHORT.md) now derives the
geometric jet, derivative-controlled remainder, actual density decomposition
and fixed-cutoff short limit. The ledger below records this backend package's
own scope; it is not a statement that those later producers are still absent.
Long cancellation and full/expected assembly remain separate obligations.

**Status: analytic backend only. Issue #97 remains open.** This package proves
fixed-cutoff absolute-overlap **basis responses and a conditional remainder
transfer** in Lean. It does not encode class E, derive its actual density
expansion in Lean, port its long-null theorem, or prove an enlarged-class
deterministic/expected-action limit. It is neither a counterexample nor a new
obstruction stopping result for #97. Independent human review remains open.

The intended geometric input for #97 remains exactly class E as specified in
[the independent-face audit](independent-face-extension.md); no geometric
contract, original action, Poisson law or joint target is changed here. That
note's geometry, local overlap jet and long-ray bounds remain **written
arguments**, not new machine-checked instances.

## 1. The missing analytic basis

The existing `ShortOverlapAsymptotics.bdg_action_limit` consumes a difference
of two actual overlaps whose angular expansion contains only a radial-square
term and a derivative-controlled remainder. The same-height comparison
provides that input for the original admissible class. It does not provide it
for E. In particular, the steep capsule's invalid reference cap cannot be
passed to the old proof.

The direct-origin route instead retains the absolute angular expansion:

```math
\begin{aligned}
\int_{S^2}\widetilde V(\tau,r\omega)\,d\omega
 &=4\pi V+\ell\tau+\alpha\tau^2+\beta r^2
   +\int_{S^2}R(\tau,r\omega)\,d\omega,\\
\tau&=(v+\sigma/v)/2,\qquad r=(v-\sigma/v)/2,\\
j(v,\sigma)&=(v-\sigma/v)^2/(8v),\qquad
\sqrt\sigma\le v\lt\delta.
\end{aligned}
```

Here V is the point volume, not an extra constant that may be discarded.
The other coefficients already include full sphere area. All cutoffs are
fixed positive numbers before density tends to infinity. Section 4 of
[the conventional short proof](curved-face-stability.md) gives the four
closed densities (S16); the new code checks the previously missing three.

`ShortRadialAbsolute.lean` proves their identities with the actual integrals
from the moving lower endpoint, including time-linear endpoint cancellation.
It also checks the identity between the time-square density and the sum of
the radial-square density and proper time times the constant density. The
closed definitions retain the zero value outside the sharp cutoff.

## 2. Point cancellation and signed normalization

The first logarithmic moment, already proved for the original kernel, is now
transported to every positive scale with absolute integrability established
before subtraction. The scale-dependent logarithm multiplies the zero first
signed moment. The uncut constant model therefore has the exact response:

```math
\begin{aligned}
c&=\pi/24,\qquad C_4=4/\sqrt6,\\
\int_0^\infty F_0^{\mathrm{model}}(\sigma)
 K(c\rho\sigma^2)\,d\sigma&=\frac{1}{96c\rho},\\
C_4\sqrt\rho\left[V-\rho(4\pi V)
 \int_0^\infty F_0^{\mathrm{model}}(\sigma)
 K(c\rho\sigma^2)\,d\sigma\right]&=0.
\end{aligned}
```

This identity alone is **not** a sharp-cutoff limit. The actual constant
density agrees with the model below the cutoff square. Above it, the model's
polynomial and logarithmic tail has a global cubic envelope with a constant
depending on that fixed cutoff. The existing signed cubic-cancellation theorem
then controls the fully normalized difference. This proves
`shortRadialConstant_point_limit` for the **actual truncated basis density**.

`ShortCutoffPolynomial.lean` similarly compares a truncated quartic polynomial
with its entire quadratic part. It proves a global cubic bound both below and
above the cutoff, establishes integrability, and only then uses the three
vanishing signed moments. Applying it to the time-linear density proves its
normalized response is zero. Adding one third of the radial-square density to
the time-square density cancels their logarithms, leaving just such a
truncated polynomial. The time-square action response is consequently positive
one over twice pi; the existing radial-square response is negative three over
twice pi. Neither quadratic term may be omitted.

`AbsoluteShortModel.action_limit` combines these results with the unchanged
physical normalization:

```math
\begin{aligned}
B_{\mathrm{jet}}&=4\pi V F_0+\ell F_\tau
                 +\alpha F_{\tau\tau}+\beta F_{rr},\\
C_4\sqrt\rho\left[V-\rho\int_0^\infty
 B_{\mathrm{jet}}(\sigma)K(c\rho\sigma^2)\,d\sigma\right]
 &\longrightarrow\frac{\alpha-3\beta}{2\pi}.
\end{aligned}
```

This is a theorem about a polynomial overlap model, **not** a replacement
observable or a theorem about an arbitrary region. All four terms are proved
absolutely integrable before the integral is split. Coefficients may be signed.

## 3. Remainder transfer and the remaining geometric work

`AbsoluteShortModel.action_limit_of_remainder` additionally consumes an exact
positive-proper-time density decomposition and the existing
`ShortNullRemainder.CubicBounds`. Those bounds control the value **and first
two displacement derivatives**, together with C² regularity on the fixed ball.
The already checked null-coordinate/truncated-fibre theorem supplies normalized
remainder cancellation, including the nearly-null part inside the short domain.
A value-only cubic estimate is not substituted for derivative control.

The new conditional interface is deliberately explicit:

```lean
(hR : Measurable R)
(hb : ShortNullRemainder.CubicBounds R δ T)
(hB : ∀ σ, 0 < σ →
  B σ = AbsoluteShortModel.density δ V ℓ α β σ +
    ShortNullRemainder.density R δ σ)
```

These are analytic consumer inputs, not fields of geometric admissibility.
The theorem does not establish `hB` for `shortOverlapDensity` of an E member.
In particular, defining B to be the model would not prove the desired region
theorem. No quantitative geometric rate is asserted here.

### Coverage returned to #90 / #86

| Obligation in #97 | This package | Still required |
| --- | --- | --- |
| Independent-envelope geometry and original inclusion | No new encoding | Encode exactly E; derive region/strata/area/bridge hypotheses and genuinely new instances |
| Actual C³ absolute overlap and two-jet | No new geometric producer | Prove raw-germ/envelope positive-part agreement before differentiating; construct the common atlas and actual angular expansion |
| Fixed-cutoff long density | Original class only, unchanged | Port using the minimum of the two margins and sum of Lipschitz constants; retain contacts, coefficient integrability and finite-measure averaging |
| Absolute short analytic response | Four basis integrals, signed responses, constant/point cancellation and conditional derivative-controlled remainder transfer | Derive the actual density decomposition and remainder hypotheses for E |
| Spatial divergence and intrinsic coefficient | No new E theorem | Port independently of the old cap slope bound, retaining the future Hessian and any artificial weight derivatives |
| Full deterministic and expected limits | **Not proved for E** | Assemble actual short/long terms at one cutoff, identify the target, then apply the original positive-density bridge |

The current type-level gap is concrete: `exists_controlledCollarAtlas` is
under `AdmissibleGraphCap`, and the actual overlap and long-density producers
are under `AdmissibleTwoFace`. The steep capsule's height has joint slope
three-halves, so it cannot inhabit the old graph-cap contract. Changing only
the final short analytic consumer does not remove those hypotheses. Factoring
regular compact height geometry and porting the actual producers remain
necessary; this is missing implementation, not proof that the route fails.

Thus #97 and #86 remain open, and this package does not meet #24's general
completion criterion. A final GitHub status check found that a maintainer had
already closed #24 on 2026-10-01 before this work; that state is left unchanged,
not treated as proof of the conjecture. No closure is requested here. There is
no new global asymptotic coverage to add to the #90 matrix.

## 4. Verification boundary

- `AbsoluteShortRegression.lean` independently expands the moving-endpoint
  densities, checks vertex/contact/empty support, signed scaled logarithmic
  response, physical point cancellation, actual fixed-cutoff limits, all four
  model coefficients, and the explicitly conditional remainder interface.
- `test_absolute_short.py` independently integrates the rational fibres,
  evaluates signed/logarithmic moments, checks the full physical normalization
  and finite-density polynomial corrections, and calibrates the steep capsule's
  coefficient against its independent normal/area expression. That last test
  is **not** an action-limit proof. Existing variable-angle, original planar,
  unequal-axis and positive-height-critical-point regressions are retained.
- Validation completed: the full integrated local build, all 192 local Lean
  sources (including the aggregate audit), warnings-as-errors and transitive
  axiom gate passed on the final Lean inputs with the default two workers.
  All 157 Python tests, symbolic checks, Markdown lint and 20 Markdown tests
  passed. All three changed equations were rendered and visually checked on
  GitHub, with no math errors or overflow. The incremental check also passed
  but is not a substitute for that full audit.
- Independent human mathematical/physical scrutiny remains outstanding under
  #94/#86. No arbitrary-atlas, null/mixed, curved, other-dimensional, rate,
  shrinking-cutoff, variance or individual-sprinkling result is promoted.

```sh
(cd formal && ./check.sh --incremental --base origin/main)
(cd formal && ./check.sh)
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
