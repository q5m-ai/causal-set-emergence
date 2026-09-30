"""Analytic diagnostics for #73, NOT a production curved action or a limit proof.

The canonical finite-density API is owned by #93.  These formulas specialize
its agreed integral to Omega(t)^4 = 1 + b*t^2.  Domains, conventional proofs,
remainder bounds and the still-open unweighted limit are in
notes/curved-bulk-pilot.md.  No Poisson expectation is computed here.
"""

import sympy as s

from dimension_kernels import Z as DIMENSION_Z, kernel_polynomial

Z = s.Symbol("z", positive=True)
INTERVAL_CONSTANT = s.pi / 24
ACTION_CONSTANT = 4 / s.sqrt(6)
KERNEL_POLYNOMIAL = kernel_polynomial(4).subs(DIMENSION_Z, Z)
KERNEL = KERNEL_POLYNOMIAL * s.exp(-Z)


def volume_density(t, b=1):
    """Positive polynomial density for real t and b >= 0."""
    return 1 + s.sympify(b) * s.sympify(t)**2


def interval_factor(t, duration, radius, b=1):
    """Exact average density on a causal diamond, 0 <= radius <= duration.

    This is not a flat proper-time law: the midpoint and boost terms remain.
    The polynomial extends to null/diagonal pairs by continuity.
    """
    t, duration, radius, b = map(s.sympify, (t, duration, radius, b))
    sigma = duration**2 - radius**2
    return 1 + b * ((t + duration / 2)**2 + duration**2 / 20 - sigma / 30)


def interval_volume(t, duration, radius, b=1):
    """Actual conformal interval volume under the causal-domain preconditions."""
    duration, radius = map(s.sympify, (duration, radius))
    return (INTERVAL_CONSTANT * (duration**2 - radius**2)**2
            * interval_factor(t, duration, radius, b))


def null_phase_factor(t, u, v, b=1):
    """H in V = (pi/24)*(u*v)^2*H, for 0 <= u <= v."""
    u, v = map(s.sympify, (u, v))
    return s.expand(interval_factor(t, (u + v) / 2, (v - u) / 2, b))


def scalar_curvature(t, b=1):
    """Independent scalar convention (C4); not defined from an action limit."""
    t, b = map(s.sympify, (t, b))
    return 3 * b * (1 - b * t**2 / 2) / volume_density(t, b)**s.Rational(5, 2)


def radial_primitives(sigma, delta):
    """J_0, J_1, J_2 in (C12), for 0 < sigma < delta^2, delta > 0.

    The fixed coordinate cutoff is v = T+r < delta, not T < delta.
    """
    sigma, delta = map(s.sympify, (sigma, delta))
    logarithm = s.log(sigma / delta**2)
    return ((delta**2 - sigma**2 / delta**2) / 8 + sigma * logarithm / 4,
            (delta - sigma / delta)**3 / 24,
            (delta**4 - sigma**4 / delta**4) / 64 + sigma**2 * logarithm / 16)


def transverse_moment(j):
    """Signed Mellin moment of w^j K(w^2), valid for real j > -1."""
    j = s.sympify(j)
    if j.is_number and (j.is_real is not True or j <= -1):
        raise ValueError("transverse moment requires real order > -1")
    return -j * (j - 1) * (j - 2) * s.gamma((j + 1) / 2) / 12


def kernel_derivative_polynomial(order):
    """p_k = exp(z)*K^(k)(z), used in the explicit Taylor envelope."""
    if isinstance(order, bool) or not isinstance(order, int) or order < 0:
        raise ValueError("derivative order must be a nonnegative integer")
    polynomial = KERNEL_POLYNOMIAL
    for _ in range(order):
        polynomial = s.diff(polynomial, Z) - polynomial
    return s.expand(polynomial)


def derivative_envelope(order, z):
    """Upper bound for |K^(order)| on [z/2, 3z/2], z >= 0."""
    polynomial = kernel_derivative_polynomial(order)
    z = s.sympify(z)
    return s.exp(-z / 2) * sum(abs(polynomial.coeff(Z, j)) * (3 * z / 2)**j
                              for j in range(4))


def second_jet_response(q, q1, q2, phi=1, phi_t=0, phi_tt=0, spatial_laplacian=0):
    """Derived normalized response of the jet MODEL, not the actual action.

    Use the critical log coefficients of J_0 and J_2 and integration-by-parts
    responses of K, zK', z^2K''.  Do not insert R/2 as an input.
    q must be positive.  The endpoint-field derivative terms are essential.
    """
    q, q1, q2 = map(s.sympify, (q, q1, q2))
    j = s.Symbol("j", real=True)
    log_moment = s.diff(transverse_moment(j), j).subs(j, 2)
    common = -ACTION_CONSTANT * 2 * s.pi * q * (INTERVAL_CONSTANT * q)**(-s.Rational(3, 2)) * log_moment
    response = [(-1)**k * s.rf(s.Rational(3, 2), k) for k in range(3)]
    a, d = q1 / q, q2 / q
    coefficient = (
        (phi_tt - spatial_laplacian) / s.Integer(32)
        + a * phi_t * (response[0] + response[1] / 2) / 16
        + phi * d * (response[0] / 32 + response[1] / 192)
        + phi * a**2 * (response[1] / 32 + response[2] / 128)
    )
    return s.simplify(common * coefficient)


def check_curved_pilot_identities():
    """Exact algebra only; does not certify remainder or geometric limits."""
    t, b, T, r, u, v = s.symbols("t b T r u v", real=True)
    sigma = T**2 - r**2
    expected = 1 + b * (t**2 + t * T + 3 * T**2 / 10 - sigma / 30)
    assert s.expand(interval_factor(t, T, r, b) - expected) == 0
    expected_null = 1 + b * (t**2 + t * (u + v) / 2
                             + 3 * (u + v)**2 / 40 - u * v / 30)
    assert s.expand(null_phase_factor(t, u, v, b) - expected_null) == 0
    print("PASS: exact polynomial-density interval and null phase identities")

    j = s.Symbol("j", real=True)
    mellin = sum(KERNEL_POLYNOMIAL.coeff(Z, k) * s.rf((j + 1) / 2, k)
                 for k in range(4)) / 2
    assert s.factor(mellin) == -j * (j - 2) * (j - 1) / 12
    assert [transverse_moment(k) for k in range(4)] == [0, 0, 0, -s.Rational(1, 2)]
    assert s.diff(transverse_moment(j), j).subs(j, 1) == s.Rational(1, 12)
    assert s.simplify(s.diff(transverse_moment(j), j).subs(j, 2) + s.sqrt(s.pi) / 12) == 0
    # The absolute coefficient envelope, not the signed third moment.
    absolute_envelope = sum(abs(KERNEL_POLYNOMIAL.coeff(Z, k)) * s.gamma(k + 2) / 2
                            for k in range(4))
    assert absolute_envelope == s.Rational(99, 2)
    print("PASS: signed/log moments and absolute third-moment envelope")

    q = s.Symbol("q", positive=True)
    q1, q2, phi, pt, ptt, lap = s.symbols("q1 q2 phi pt ptt lap", real=True)
    response = second_jet_response(q, q1, q2, phi, pt, ptt, lap)
    expected_response = (ptt - lap + q1 * pt / (2 * q)
                         + (3 * q2 / (4 * q) - 9 * q1**2 / (16 * q**2)) * phi) / s.sqrt(q)
    assert s.simplify(response - expected_response) == 0
    density = volume_density(t, b)
    pilot = second_jet_response(density, s.diff(density, t), s.diff(density, t, 2))
    assert s.simplify(pilot - scalar_curvature(t, b) / 2) == 0
    print("PASS: derived jet-model response includes curvature and endpoint derivatives")


if __name__ == "__main__":
    check_curved_pilot_identities()
