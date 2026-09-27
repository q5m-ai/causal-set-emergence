# Conditional null-transverse cancellation

Issue #53 supplies an analytic component of the two-face research program,
not a localization theorem. `NullTransverseMoments.lean` and
`NullTransverseCancellation.lean` use the **unchanged original** `bdgKernel`.
The reduced `planeKernel` still has mass one and is not interchangeable with it.

## Contract and scope

`bdgKernel_transverse_cancellation` has this Lean contract:

```lean
theorem bdgKernel_transverse_cancellation (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C) (b₀ b₁ b₂ : ℝ)
    (hjet : (fun s => B s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2)) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)) atTop (𝓝 0)
```

The hypotheses are measurability, boundedness on the positive half-line, and a
quadratic expansion from the right with little-o remainder. **Compact support
is unnecessary**: the theorem in particular covers bounded compactly supported
weights with a discontinuous positive support cutoff. Neither continuity away
from zero nor the value of `B 0` is constrained. The coefficient `c` and the
weight are fixed during the density limit.

Applying this theorem to the **actual translated-overlap density of #52**
requires a separate geometric expansion theorem. No such hypothesis is added
to geometric admissibility. Translated tangencies may obstruct that expansion;
failure of this sufficient route would not itself refute Conjecture 1′. This
result does not prove the full action limit, short-displacement cancellation,
a quantitative rate, or convergence of individual Poisson sprinklings.

## Proof

### Absolute moments and their signs

With the original coefficients, Lean proves the general natural-order formula:

```math
K(x)=\left(1-9x+8x^2-\frac43x^3\right)e^{-x},\qquad
\int_0^\infty z^jK(z^2)\,dz
=-\frac{j(j-1)(j-2)}{12}\Gamma\!\left(\frac{j+1}{2}\right).
```

`integrableOn_pow_mul_gaussian` establishes absolute integrability of each
Gaussian monomial. Substitution of the square into the Gamma integral gives
`integral_pow_mul_gaussian`. Only then is the polynomial split into four
integrals. Three applications of the Gamma recurrence and exact ring algebra
give the displayed factor. Thus orders zero, one, and two vanish, whereas
order three is **negative one-half**. The subtractions in the factor are real,
not truncated natural subtraction. Both signed and absolute moment integrability
are exported, including the second absolute moment used for domination.

### Subtract the polynomial on the full half-line

Define the quotient for positive arguments by:

```math
P(s)=b_0+b_1s+b_2s^2,\qquad R(s)=\frac{B(s)-P(s)}{s^2}.
```

The little-o hypothesis gives a zero right limit for `R`.
`quadraticRemainder_bounded` derives, rather than assumes, a **global** bound:
near zero use that limit; for any fixed positive lower cutoff, boundedness of
`B` controls the quotient by a constant plus inverse first and second powers.
Compact support is not needed for this argument.

`integral_bdgKernel_transverse_sub_quadratic` proves exact cancellation of the
whole polynomial over the entire positive half-line. Subtracting it only within
`B`'s support would leave nonzero polynomial tails. The original bounded-weight
integrand, every scaled polynomial moment, and the rescaled remainder are each
proved absolutely integrable separately; no inference is made from Lean's
totalized integral having value zero.

### Rescale, then dominate

Positive linear substitution and the three zero moments give the exact identity:

```math
\rho^{3/2}\int_0^\infty B(s)K(c\rho s^2)\,ds
=c^{-3/2}\int_0^\infty z^2K(z^2)
 R\!\left(\frac{z}{\sqrt{c\rho}}\right)\,dz.
```

`integral_bdgKernel_transverse_eq_remainder` performs the substitution and
full-half-line subtraction. `bdgKernel_transverse_normalized_rescaling`
checks the density prefactor; the Lean constant is the cube of the reciprocal
of `Real.sqrt c`. For every fixed positive `z`, the quotient tends to zero.
Its global bound supplies the integrable dominator:

```math
\left|z^2K(z^2)R\!\left(\frac{z}{\sqrt{c\rho}}\right)\right|
\le D z^2|K(z^2)|.
```

`bdgKernel_transverse_remainder_limit` proves the dominated-convergence step.
The absolute value appears **after** the signed cancellations, not in place of
them. No differentiated asymptotic expansion or density-dependent cutoff is
used, and no uniformity as a macroscopic cutoff tends to zero is claimed.

## Independent regressions and validation

`NullTransverseRegression.lean` checks:

- all four signed moment values and absolute integrability;
- the negative value of the original kernel at one, contrasted with the
  unchanged mass-one `planeKernel`;
- a whole family of cubic polynomials cut off at an arbitrary positive endpoint;
- a compactly supported signed example with quadratic jet `(-2, 1, 3)`, nonzero
  cubic remainder, and a **proved discontinuity** at its positive support cutoff;
- a pure nonzero quadratic jet and finite-density absolute integrability.

The regression is independently compiled by `check.sh`. Both new library
modules are imported by `BoundaryDraft.lean`; the isolated and aggregate
transitive axiom audits admit only the existing Lean foundations.
`check_symbolic.py` already provides an independent symbolic check of all four
moments; it is corroboration, not a substitute for the Lean proofs.

```sh
./formal/check.sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

GitHub's Markdown CI does not run Lean. The full local source/axiom audit and
its observed results must therefore be recorded separately in the PR.
