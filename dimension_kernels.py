"""Exact BDG normalization prerequisites, not a higher-dimensional limit solver.

Conventions and analytic proofs: notes/dimension-kernels.md. The implemented
family is the unsmeared minimal-layer action in every integer dimension d >= 2.
SymPy identities are regression checks, not general-dimensional Lean proofs.
The original four-dimensional calculations.py and formal definitions are untouched.
"""

from functools import lru_cache

import sympy as s

Z = s.Symbol("z")


def _dimension(d):
    if isinstance(d, bool) or not isinstance(d, int) or d < 2:
        raise ValueError("dimension must be an integer >= 2")
    return d


def factor_count(d):
    return _dimension(d) // 2 + 1


def sphere_area(d):
    """Area of S^(d-2); in d=2 this is counting measure of two directions."""
    d = _dimension(d)
    return 2 * s.pi ** s.Rational(d - 1, 2) / s.gamma(s.Rational(d - 1, 2))


def interval_coefficient(d):
    """V(x,y) = c_d * tau(x,y)^d (NOT Glaser's null-coordinate c_d)."""
    d = _dimension(d)
    return s.simplify(sphere_area(d) / (2 ** (d - 1) * d * (d - 1)))


@lru_cache(maxsize=None, typed=True)
def action_constants(d):
    """Return a=-alpha>0, beta>0; A = rho^(2/d) [a*volume-beta*rho*pairs]."""
    d = _dimension(d)
    c = interval_coefficient(d)
    scale = c ** s.Rational(2, d) / s.gamma(1 + s.Rational(2, d))
    if d % 2:
        return 2 * scale, s.Rational(d + 1, 2 ** (d - 2)) * scale
    a = 4 * scale
    ratio = s.gamma(d // 2 + 2) * s.gamma(d // 2) / s.gamma(d)
    return a, ratio * a


@lru_cache(maxsize=None, typed=True)
def kernel_polynomial(d):
    """Euler-operator recurrence; coefficients are C_(k+1)/k!, not C_(k+1)."""
    d = _dimension(d)
    p = s.Integer(1)
    for i in range(1, factor_count(d) + 1):
        p = s.expand(p + s.Rational(d, 2 * i) * Z * (s.diff(p, Z) - p))
    return p


def layer_coefficients(d):
    """Independent Glaser finite-difference formula, with C_1=1."""
    m = factor_count(d)
    # The gamma ratio is a product of m linear factors, including odd d.
    def q(k):
        return s.prod(1 + s.Rational(d * k, 2 * i) for i in range(1, m + 1))

    return tuple(s.expand(sum((-1) ** k * s.binomial(i, k) * q(k)
                             for k in range(i + 1))) for i in range(m + 1))


def mellin_factor(d, exponent):
    """Integral z^(exponent-1) K_d(z) = Gamma(exponent) * this, exponent>0."""
    m = factor_count(d)
    exponent = s.sympify(exponent)
    return s.prod(1 - d * exponent / (2 * i) for i in range(1, m + 1))


def transverse_moment(d, order):
    """Integral u^order K_d(u^(d/2)) du; require real order > -1.

    Symbolic orders are allowed; their domain is the caller's proof obligation.
    Numeric divergent orders are rejected rather than assigned analytic continuations.
    """
    _dimension(d)
    order = s.sympify(order)
    if order.is_number and (order.is_real is not True or order <= -1):
        raise ValueError("transverse moment requires real order > -1")
    exponent = 2 * (order + 1) / d
    return s.simplify(s.Rational(2, d) * s.gamma(exponent) * mellin_factor(d, exponent))


def interval_power_moment(d, order):
    """Integral over a unit-duration diamond of tau(x,y)^(d*order) dy.

    For natural order; multiply by T^(d*(order+1)) for duration T.
    Derived by a beta integral, independently of the signed coefficients.
    """
    _dimension(d)
    if isinstance(order, bool):
        raise ValueError("interval power order must be a nonnegative integer")
    order = s.sympify(order)
    if order.is_number and (order.is_integer is not True or order.is_nonnegative is not True):
        raise ValueError("interval power order must be a nonnegative integer")
    p = d * order / 2
    return (sphere_area(d) / 2 ** (d - 1) * s.gamma(p + 1) * s.gamma(d - 1)
            / (d * (order + 1) * s.gamma(p + d)))


def cone_slice_moment(d, order):
    """Integral t^order F_d(t) dt at rho=1, after signed cancellation.

    Natural orders only. Even d: order<4 (the first divergent absolute moment
    is order 4). Odd d: all natural orders. See the analytic Mellin-strip proof;
    no divergent double integral is interchanged to define this quantity.
    """
    m = factor_count(d)
    if isinstance(order, bool) or not isinstance(order, int) or order < 0:
        raise ValueError("cone-slice order must be a nonnegative integer")
    if d % 2 == 0 and order >= 4:
        raise ValueError("even-dimensional cone-slice moment diverges for order >= 4")
    c = interval_coefficient(d)
    prefactor = (s.pi ** s.Rational(d - 1, 2) / (d * s.factorial(m))
                 * c ** (-1 - s.Rational(order, d))
                 * s.gamma(1 + s.Rational(order, d)))
    if d % 2:
        # Gamma((3-order)/2)/Gamma((1-order)/2), with removable zeros resolved.
        return s.simplify(prefactor * s.Rational(1 - order, 2))
    if order in (1, 3):
        return s.Integer(0)
    return s.simplify(prefactor * s.gamma(m + 1 - s.Rational(d + order, 2))
                      / s.gamma(s.Rational(1 - order, 2)))


def plane_moment(d, order):
    """Signed reduced-plane moment; even d supports only orders 0 and 1."""
    if isinstance(order, bool) or not isinstance(order, int) or order < 0:
        raise ValueError("plane order must be a nonnegative integer")
    _, beta = action_constants(d)
    return s.simplify(-beta * cone_slice_moment(d, order + 2)
                      / ((order + 1) * (order + 2)))


def even_plane_tail_coefficient(d):
    """Coefficient of H^-3 in G_1(H), even d only; it is strictly negative."""
    m = factor_count(d)
    if d % 2:
        raise ValueError("odd dimensions have an exponential, not an H^-3, tail")
    _, beta = action_constants(d)
    c = interval_coefficient(d)
    return s.simplify(-beta * sphere_area(d) / (12 * d)
                      * s.binomial(s.Rational(d - 3, 2), m)
                      * c ** (-1 - s.Rational(4, d)) * s.gamma(1 + s.Rational(4, d)))


def check_dimension_identities():
    """Exact finite regressions; the all-dimension induction is in the note."""
    a = s.Symbol("a", positive=True)
    for d in (*range(2, 12), 20, 21):
        m = factor_count(d)
        p = kernel_polynomial(d)
        layers = layer_coefficients(d)
        assert s.expand(p - sum(layers[k] * Z ** k / s.factorial(k)
                               for k in range(m + 1))) == 0
        gamma_sum = sum(p.coeff(Z, k) * s.rf(a, k) for k in range(m + 1))
        assert s.expand(gamma_sum - mellin_factor(d, a)) == 0
        assert all(transverse_moment(d, j) == 0 for j in range(m))
        assert transverse_moment(d, m) != 0
        point, beta = action_constants(d)
        assert s.simplify(cone_slice_moment(d, 0) - point / beta) == 0
        assert cone_slice_moment(d, 1) == 0
        assert s.simplify(plane_moment(d, 0) - 1) == 0
        assert s.simplify(interval_power_moment(d, 0) - interval_coefficient(d)) == 0
        if d % 2 == 0:
            assert plane_moment(d, 1) == 0
            assert even_plane_tail_coefficient(d).is_negative
        else:
            assert plane_moment(d, 1).is_positive
    assert s.simplify(even_plane_tail_coefficient(4) + 2 * s.sqrt(6) / s.pi) == 0
    print("PASS: dimension-indexed coefficients, Mellin factors, slice and plane normalization (2..11,20,21)")


if __name__ == "__main__":
    check_dimension_identities()
