"""Independent exact geometry diagnostics for the #93 conformal pilot.

These calculations are not a second production action definition or a Lean
curvature theorem. The canonical observable is BoundaryDraft.conformalAction.
Signature: (+---). Convention:
R^a_{bcd} = d_c Gamma^a_{db} - d_d Gamma^a_{cb}
           + Gamma^a_{ce} Gamma^e_{db} - Gamma^a_{de} Gamma^e_{cb},
Ric_{bd} = R^a_{bad}, R = g^{bd} Ric_{bd}.
No Einstein--Hilbert coefficient or asymptotic statement is inferred.
"""

from functools import lru_cache

import sympy as s


@lru_cache(maxsize=None)
def conformal_curvature(omega, coordinates):
    """Compute metric, Christoffels, Ricci and scalar directly by contraction.

    ``omega`` must be a SymPy expression in four coordinate symbols. Positivity
    is a geometric precondition on the domain, not checked by this calculator.
    This deliberately does not use a conformal scalar-curvature shortcut.
    """
    if len(coordinates) != 4:
        raise ValueError("The pilot is four-dimensional")
    metric = s.diag(omega**2, -omega**2, -omega**2, -omega**2)
    inverse = metric.inv()
    gamma = s.ImmutableDenseNDimArray([
        s.simplify(sum(
            inverse[a, e] * (
                s.diff(metric[e, c], coordinates[b])
                + s.diff(metric[e, b], coordinates[c])
                - s.diff(metric[b, c], coordinates[e])
            ) / 2
            for e in range(4)
        ))
        for a in range(4) for b in range(4) for c in range(4)
    ], (4, 4, 4))
    ricci = s.ImmutableMatrix(4, 4, lambda b, d: s.simplify(sum(
        s.diff(gamma[a, d, b], coordinates[a])
        - s.diff(gamma[a, a, b], coordinates[d])
        + sum(
            gamma[a, a, e] * gamma[e, d, b]
            - gamma[a, d, e] * gamma[e, a, b]
            for e in range(4)
        )
        for a in range(4)
    )))
    scalar = s.factor(sum(inverse[b, d] * ricci[b, d]
                          for b in range(4) for d in range(4)))
    return s.ImmutableMatrix(metric), gamma, ricci, scalar


def vertical_interval_volume(omega, time, lower, upper):
    """Exact ambient volume of a vertical causal interval for time-only omega.

    Cross-sections are ordinary spatial balls of radius min(t-lower, upper-t).
    The density is omega(t)^4. Endpoints are measure zero. Region restriction
    may be omitted ONLY when causal convexity and endpoint membership hold.
    Polynomial examples avoid any numerical quadrature or interval-volume jet.
    """
    if not (s.sympify(upper - lower).is_positive):
        raise ValueError("A strictly positive time separation is required")
    middle = (lower + upper) / 2
    return s.simplify(4 * s.pi / 3 * (
        s.integrate(omega**4 * (time - lower)**3, (time, lower, middle))
        + s.integrate(omega**4 * (upper - time)**3, (time, middle, upper))
    ))


def check_conformal_identities():
    """Exact nonzero-curvature and volume calibrations, separate from limits."""
    t, x, y, z = s.symbols("t x y z", real=True)
    coordinates = (t, x, y, z)
    omega = 1 + t**2
    metric, _, _, scalar = conformal_curvature(omega, coordinates)
    assert s.factor(metric.det()) == -(1 + t**2)**8
    assert s.simplify(scalar + 12 / (1 + t**2)**3) == 0
    assert scalar.subs(t, -s.Rational(1, 8)) == -s.Rational(3145728, 274625)
    # The points below lie inside the original height-1/4, axes-4 cap in Lean.
    lower, upper = -s.Rational(1, 8), -s.Rational(1, 16)
    curved = vertical_interval_volume(omega, t, lower, upper)
    flat = s.pi / 24 * (upper - lower)**4
    assert s.simplify((curved - flat) / s.pi).is_positive
    for constant in (s.Integer(1), s.Rational(3, 2)):
        _, _, _, constant_scalar = conformal_curvature(constant, coordinates)
        assert constant_scalar == 0
        assert s.simplify(vertical_interval_volume(constant, t, lower, upper)
                          - constant**4 * flat) == 0
    print("PASS: conformal metric determinant, direct nonzero Ricci contraction, and actual interval volume")


if __name__ == "__main__":
    check_conformal_identities()
