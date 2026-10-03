"""Exact algebra checks supporting (not replacing) the proof and research notes."""

import sympy as s

from conformal_geometry import check_conformal_identities
from dimension_kernels import check_dimension_identities
from dimension_joint_geometry import check_joint_identities
from dimension_short import check_short3_identities
from dimension_long_null import check_long_null_identities
from curved_bulk_pilot import check_curved_pilot_identities


def main():
    n = s.symbols("n", integer=True, nonnegative=True)
    z, sigma, a, T, rho = s.symbols("z sigma a T rho", positive=True)
    c = s.pi / 24
    q = (n + 1) * (2 * n + 1) * (2 * n + 3) / 3
    coefficient = 1 + 9 * n + 8 * n * (n - 1) + s.Rational(4, 3) * n * (n - 1) * (n - 2)
    assert s.simplify(coefficient - q) == 0
    print("PASS: all-orders coefficient of P(z)*exp(-z)")

    denominator = (2 * n + 1) * (2 * n + 2) * (2 * n + 3) * (4 * n + 4)
    assert s.simplify(s.pi * q / denominator - c / (n + 1)) == 0
    print("PASS: exact interval moment cancellation, all n >= 0")

    # Interior radial wave-operator identity. This alone would NOT account
    # for distributions on the light cone; the proof uses the series instead.
    box = lambda f: -8 * s.diff(f, sigma) - 4 * sigma * s.diff(f, sigma, 2)
    f = s.exp(-c * rho * sigma**2)
    P = 1 - 9 * z + 8 * z**2 - s.Rational(4, 3) * z**3
    residual = box(box(f)) + 8 * s.pi * rho * P.subs(z, c * rho * sigma**2) * f
    assert s.simplify(residual) == 0
    print("PASS: interior radial identity box^2 exp(-c*rho*sigma^2)")

    # Proposed long-null cancellation route in notes/flat-localization-plan.md.
    # Gamma recurrence supplies this factor in the moment of z^j K(z^2).
    # This is the original BDG kernel, NOT the mass-one planeKernel. These
    # algebra checks do not establish regularity of any geometric overlap.
    j = s.symbols("j", integer=True, nonnegative=True)
    gamma_factor = sum(P.coeff(z, k) * s.rf((j + 1) / 2, k) for k in range(4)) / 2
    assert s.simplify(gamma_factor + j * (j - 1) * (j - 2) / 12) == 0
    for order, expected_moment in enumerate([0, 0, 0, -s.Rational(1, 2)]):
        moment = s.integrate(z**order * P.subs(z, z**2) * s.exp(-z**2), (z, 0, s.oo))
        assert s.simplify(moment - expected_moment) == 0
    print("PASS: signed transverse-null moments 0, 1, 2 vanish; moment 3 is -1/2")

    # m_n/m_(n-1), from the beta integral in the plane-cap proof.
    ratio = 4 * (2 * n) * (2 * n - 1) / ((4 * n + 1) * (4 * n + 3))
    recurrence = (4 * n + 1) * (4 * n + 2) * (4 * n + 3) * ratio / 2
    assert s.simplify(recurrence - 24 * q.subs(n, n - 1)) == 0
    print("PASS: all-orders beta recurrence for F'''/(8*pi)=1-rho*Q")

    # Differentiate h^3 exp(-const*h^4) under the auxiliary integral.
    polynomial = s.Integer(1)
    expected = [
        3 - 4 * z,
        6 - 36 * z + 16 * z**2,
        6 - 204 * z + 288 * z**2 - 64 * z**3,
    ]
    power = 3
    for derivative in expected:
        polynomial = s.expand(power * polynomial + 4 * z * (s.diff(polynomial, z) - polynomial))
        assert s.expand(polynomial - derivative) == 0
        power -= 1
    print("PASS: first three auxiliary derivative polynomials")

    # Zero-endpoint primitive replacing the plane-cone series/beta exchange.
    # Lean separately proves compact domination and both coordinate changes.
    v, cone_scale = s.symbols("v cone_scale", real=True)
    w = 1 - v**2
    cone_z = cone_scale * w**2
    R3 = expected[-1]
    primitive = 2 * v**3 * w * (
        -8 * cone_z**2 * (w + 1) + 2 * cone_z * (15 * w + 14) - 15 * w - 12
    ) * s.exp(-cone_z)
    cancellation = v**2 * (
        w**2 * (s.diff(R3, z) - R3).subs(z, cone_z) + 48 * P.subs(z, cone_z)
    ) * s.exp(-cone_z)
    assert s.simplify(s.diff(primitive, v) - cancellation) == 0
    assert primitive.subs(v, 0) == primitive.subs(v, 1) == 0
    print("PASS: exact plane-cone cancellation primitive and both endpoints")

    # Exact primitives used in the Lean absolute tail/moment estimates.
    alpha = s.symbols("alpha", positive=True)
    t, b, d = s.symbols("t b d", real=True)
    gaussian = s.exp(-alpha * t**2)
    cancellation = b - (2 * b + 3 * d) * alpha * t**2 + 2 * d * alpha**2 * t**4
    envelope = b + (2 * b + 3 * d) * alpha * t**2 + 2 * d * alpha**2 * t**4
    primitive = (b * t - d * alpha * t**3) * gaussian
    weighted_primitive = -(
        (3 * b + 7 * d) / 2 + (2 * b + 7 * d) * alpha * t**2 / 2
        + d * alpha**2 * t**4
    ) * gaussian / alpha
    assert s.simplify(s.diff(primitive, t) - cancellation * gaussian) == 0
    assert s.simplify(s.diff(weighted_primitive, t) - t * envelope * gaussian) == 0
    assert s.expand(cancellation.subs({b: 6, d: 8}) - (6 - 36 * alpha * t**2 + 16 * alpha**2 * t**4)) == 0
    assert s.expand(cancellation.subs({b: 2, d: 0}) - (2 - 4 * alpha * t**2)) == 0
    print("PASS: exact Gaussian cancellation and absolute-envelope primitives")

    weight = s.pi / 4 * (
        a * (2 * T - a) - 2 * (1 - a / T) * sigma
        - sigma**2 / T**2 - 2 * sigma * s.log(a * T / sigma)
    )
    assert s.simplify(s.limit(weight, sigma, 0) - s.pi * a * (2 * T - a) / 4) == 0
    assert s.simplify(weight.subs(sigma, a * T)) == 0
    assert s.simplify(s.diff(weight, sigma).subs(sigma, a * T)) == 0
    volume = s.integrate(weight, (sigma, 0, a * T))
    assert s.simplify(volume - s.pi * a**2 * T * (3 * T - 2 * a) / 24) == 0
    print("PASS: null-cut weight endpoints and exact volume")

    k = s.symbols("k", positive=True)
    cosh_squared = 1 / (1 - k**2)
    assert s.simplify(cosh_squared / (cosh_squared - 1) - 1 / k**2) == 0
    print("PASS: coth(theta)=1/|grad h| for 0<|grad h|<1")
    check_dimension_identities()
    check_joint_identities()
    check_short3_identities()
    check_long_null_identities()
    check_conformal_identities()
    check_curved_pilot_identities()
    print("All symbolic checks passed.")


if __name__ == "__main__":
    main()
