"""Independent normalizations and numerical diagnostics; quadrature is not proof."""

import unittest

from mpmath import mp
from scipy.integrate import quad
import sympy as s

import calculations
import dimension_kernels as dk


def _mp_exact(expr):
    return mp.mpf(str(s.N(expr, mp.dps)))


def _mp_kernel(d):
    coefficients = [_mp_exact(dk.kernel_polynomial(d).coeff(dk.Z, k))
                    for k in range(dk.factor_count(d) + 1)]
    return lambda z: mp.polyval(list(reversed(coefficients)), z) * mp.exp(-z)


def _plane_quadrature(d, rho, height):
    """Finite signed future-cone action, without Mellin or scaling formulas."""
    a, beta = map(float, dk.action_constants(d))
    c, sphere = float(dk.interval_coefficient(d)), float(dk.sphere_area(d))
    kernel = s.lambdify(dk.Z, dk.kernel_polynomial(d) * s.exp(-dk.Z), 'math')

    def future_slice(t):
        return sphere * t ** (d - 1) * quad(
            lambda v: v ** (d - 2) * kernel(c * rho * t ** d * (1 - v * v) ** (d / 2)),
            0, 1, epsabs=1e-12)[0]

    pair = quad(lambda t: (height - t) * future_slice(t), 0, height, epsabs=1e-12)[0]
    return rho ** (2 / d) * (a * height - beta * rho * pair)


def _diamond_series(d, rho):
    """Unit-duration diamond, from two independent interval power integrals.

    Moderate-density diagnostic only: direct summation loses precision as the
    Poisson mean grows. The test uses 60 digits and means below 27.
    """
    c = _mp_exact(dk.interval_coefficient(d))
    a, beta = map(_mp_exact, dk.action_constants(d))
    sphere = _mp_exact(dk.sphere_area(d))
    m = dk.factor_count(d)

    def interval_moment(n):
        p = mp.mpf(d * n) / 2
        return sphere / 2 ** (d - 1) * mp.beta(p + 1, d - 1) / (d * (n + 1))

    total = mp.mpf(0)
    for n in range(500):
        q = mp.fprod(1 + mp.mpf(d * n) / (2 * i) for i in range(1, m + 1))
        term = ((-c * rho) ** n / mp.factorial(n) * q
                * interval_moment(n) * interval_moment(n + 1))
        total += term
        if n > 2 * c * rho + 10 and abs(term) < mp.mpf('1e-55'):
            break
    else:
        raise AssertionError("diamond diagnostic did not converge")
    return rho ** (mp.mpf(2) / d) * (a * c - beta * rho * total)


class DimensionKernelTests(unittest.TestCase):
    def test_source_normalizations(self):
        # Pinned source Appendix A (76)-(78), not derived from the recurrence.
        expected_layers = {2: (1, -2, 1),
                           3: (1, -s.Rational(27, 8), s.Rational(9, 4)),
                           4: (1, -9, 16, -8)}
        expected_volumes = {2: s.Rational(1, 2), 3: s.pi / 12, 4: s.pi / 24,
                            5: s.pi ** 2 / 160, 6: s.pi ** 2 / 360}
        for d, expected in expected_layers.items():
            self.assertEqual(dk.layer_coefficients(d), expected)
        for d, expected in expected_volumes.items():
            self.assertEqual(dk.interval_coefficient(d), expected)
        a2, b2 = dk.action_constants(2)
        self.assertEqual((a2, b2), (2, 4))
        a3, b3 = dk.action_constants(3)
        self.assertEqual(s.simplify(a3 - (s.pi / (3 * s.sqrt(2))) ** s.Rational(2, 3)
                                    / s.gamma(s.Rational(5, 3))), 0)
        self.assertEqual(a3, b3)
        a4, b4 = dk.action_constants(4)
        self.assertEqual(s.simplify(a4 - 4 / s.sqrt(6)), 0)
        self.assertEqual(a4, b4)

    def test_operator_and_mellin_identities(self):
        dk.check_dimension_identities()

    def test_original_four_dimensional_kernel_unchanged(self):
        with mp.workdps(50):
            new = _mp_kernel(4)
            for z in map(mp.mpf, ('0', '.2', '.7', '1', '4', '10')):
                self.assertLess(abs(new(z) - calculations.kernel(z)), mp.mpf('1e-47'))
            self.assertLess(new(mp.mpf('.2')), 0)  # signed, not a positive kernel

    def test_transverse_moments_by_direct_quadrature(self):
        with mp.workdps(45):
            for d in (2, 3, 4, 5, 6, 7, 11):
                kernel = _mp_kernel(d)
                q = mp.mpf(d) / 2
                end = mp.mpf(200) ** (1 / q)
                orders = list(range(dk.factor_count(d) + 1)) + [s.Rational(d, 2)]
                for order in orders:
                    j = _mp_exact(order)
                    actual = mp.quad(lambda u: u ** j * kernel(u ** q), [0, 1, end])
                    expected = _mp_exact(dk.transverse_moment(d, order))
                    self.assertLess(abs(actual - expected), mp.mpf('1e-30'), (d, order))

    def test_even_critical_log_moment_is_not_cancelled(self):
        with mp.workdps(45):
            for d in (2, 4, 6, 8):
                n = d // 2
                kernel = _mp_kernel(d)
                end = mp.mpf(200) ** (mp.mpf(2) / d)
                actual = mp.quad(lambda u: u ** n * mp.log(u) * kernel(u ** n),
                                 [0, 1, end])
                expected = ((-1) ** (n + 1) * mp.gamma(1 + mp.mpf(2) / d)
                            * 2 / (d * (n + 1)))
                self.assertLess(abs(actual - expected), mp.mpf('1e-30'))
                self.assertNotEqual(expected, 0)

    def test_positive_density_transverse_scaling(self):
        with mp.workdps(45):
            for d in (2, 3, 4, 5, 8):
                kernel = _mp_kernel(d)
                q = mp.mpf(d) / 2
                c, rho = _mp_exact(dk.interval_coefficient(d)), mp.mpf(7)
                j = dk.factor_count(d)
                scale = (c * rho) ** (1 / q)
                end = (mp.mpf(200) / (c * rho)) ** (1 / q)
                actual = mp.quad(lambda u: u ** j * kernel(c * rho * u ** q),
                                 [0, 1 / scale, end])
                expected = _mp_exact(dk.transverse_moment(d, j)) / scale ** (j + 1)
                self.assertLess(abs(actual - expected), mp.mpf('1e-29'))

    def test_plane_reduction_against_unchanged_4d_action(self):
        # Direct radial future-cone integration, NOT the Mellin normalization.
        for height in (0.4, 1.0, 2.0):
            actual = _plane_quadrature(4, 1, height)
            with mp.workdps(40):
                expected = float(calculations.plane_kernel(height))
            self.assertAlmostEqual(actual, expected, delta=2e-11)

    def test_three_dimensional_slice_moments(self):
        # In 3D the radial integral has this finite primitive. This checks the
        # Mellin-derived J_k against the actual kernel, not against itself.
        sigma = s.Symbol('sigma', positive=True)
        c = dk.interval_coefficient(3)
        z = c * sigma ** s.Rational(3, 2)
        primitive = sigma * (1 - s.Rational(3, 4) * z) * s.exp(-z)
        kernel = dk.kernel_polynomial(3).subs(dk.Z, z) * s.exp(-z)
        self.assertEqual(s.simplify(s.diff(primitive, sigma) - kernel), 0)
        with mp.workdps(45):
            c = _mp_exact(c)
            end = (200 / c) ** (mp.mpf(1) / 3)
            for order in range(4):
                actual = mp.quad(lambda t: mp.pi * t ** (order + 2)
                                 * (1 - mp.mpf(3) / 4 * c * t ** 3)
                                 * mp.exp(-c * t ** 3), [0, 1, end])
                self.assertLess(abs(actual - _mp_exact(dk.cone_slice_moment(3, order))),
                                mp.mpf('1e-30'))

    def test_plane_density_scaling_in_both_parities(self):
        for d in range(2, 8):
            rho, height = 7.0, 1.2
            scale = rho ** (1 / d)
            self.assertAlmostEqual(_plane_quadrature(d, rho, height),
                                   scale * _plane_quadrature(d, 1, scale * height),
                                   delta=2e-10)

    def test_action_dilation_powers(self):
        rho, scale, volume, pairs = s.symbols('rho scale volume pairs', positive=True)
        for d in range(2, 12):
            a, beta = dk.action_constants(d)
            lhs = rho ** s.Rational(2, d) * (a * scale ** d * volume
                                            - beta * rho * scale ** (2 * d) * pairs)
            rhs = scale ** (d - 2) * (rho * scale ** d) ** s.Rational(2, d) * (
                a * volume - beta * rho * scale ** d * pairs)
            self.assertEqual(s.simplify(lhs - rhs), 0)

    def test_diamond_calibrations(self):
        # Exact 2D coefficient reduction, at all series orders, is independent
        # of any numerical asymptotic fit or the proposed spacelike joint target.
        n = s.Symbol('n', integer=True, nonnegative=True)
        q = (n + 1) * (n + 2) / 2
        pair = dk.interval_power_moment(2, n) * dk.interval_power_moment(2, n + 1)
        self.assertEqual(s.simplify(q * pair / dk.interval_coefficient(2) ** 2
                                    - 1 / (2 * (n + 1) * (n + 2))), 0)
        with mp.workdps(60):
            for rho in map(mp.mpf, (2, 50, 200)):
                two = _diamond_series(2, rho if rho < 100 else mp.mpf(40))
                r2 = rho if rho < 100 else mp.mpf(40)
                self.assertLess(abs(two - 2 * (1 - mp.exp(-r2 / 2))), mp.mpf('1e-35'))
                four = _diamond_series(4, rho)
                original = calculations.null_cap_action(rho, 1, 1)
                self.assertLess(abs(four - original), mp.mpf('1e-35'))

    def test_parity_and_divergent_moments(self):
        for d in range(2, 12):
            self.assertEqual(s.simplify(dk.plane_moment(d, 0)), 1)
            if d % 2:
                self.assertTrue(dk.plane_moment(d, 1).is_positive)
                self.assertTrue(dk.plane_moment(d, 2).is_positive)
                self.assertNotEqual(dk.transverse_moment(d, s.Rational(d, 2)), 0)
            else:
                self.assertEqual(dk.plane_moment(d, 1), 0)
                with self.assertRaises(ValueError):
                    dk.plane_moment(d, 2)
        for j in (-1, -2, s.I):
            with self.assertRaises(ValueError):
                dk.transverse_moment(4, j)
        for n in (-1, s.Rational(1, 2), True):
            with self.assertRaises(ValueError):
                dk.interval_power_moment(4, n)
        for d in (0, 1, -2, True, 4.0):
            with self.assertRaises(ValueError):
                dk.kernel_polynomial(d)
        # d=1 is excluded, but the implementation has no dimension-11 ceiling.
        self.assertEqual(dk.factor_count(30), 16)


if __name__ == '__main__':
    unittest.main()
