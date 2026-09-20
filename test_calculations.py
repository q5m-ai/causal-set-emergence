import unittest

from mpmath import mp

from calculations import (
    ellipsoid_action,
    ellipsoid_limit,
    interval_kernel_integral,
    null_cap_action,
    null_cap_area,
    null_cap_volume,
    null_cap_weight,
    null_cap_weight_geometric,
    plane_auxiliary,
    plane_future_kernel_integral,
    plane_kernel,
)


class CalculationsTest(unittest.TestCase):
    def setUp(self):
        self.precision = mp.workdps(35)
        self.precision.__enter__()
        self.addCleanup(self.precision.__exit__, None, None, None)

    def assertNear(self, actual, expected, tolerance="1e-27"):
        self.assertLessEqual(abs(actual - expected), mp.mpf(tolerance) * max(1, abs(expected)))

    def test_interval_identity_direct_quadrature(self):
        for rho, T in [(2, "0.7"), (13, "1.2")]:
            rho, T = mp.mpf(rho), mp.mpf(T)
            actual = rho * interval_kernel_integral(rho, T)
            expected = -mp.expm1(-mp.pi * rho * T**4 / 24)
            self.assertNear(actual, expected)

    def test_null_weight_against_independent_geometry(self):
        # Both sides of sigma=a^2, and multiple truncation fractions.
        for T, a in [(1, "0.3"), (2, "1.2"), (1, 1)]:
            T, a = mp.mpf(T), mp.mpf(a)
            for fraction in ("0.02", "0.2", "0.7", "0.95"):
                sigma = a * T * mp.mpf(fraction)
                self.assertNear(
                    null_cap_weight(sigma, T, a),
                    null_cap_weight_geometric(sigma, T, a),
                )

    def test_null_volume_and_area(self):
        T, a = mp.mpf(2), mp.mpf("0.7")
        volume = mp.quad(lambda sigma: null_cap_weight(sigma, T, a), [0, a * T])
        self.assertNear(volume, null_cap_volume(T, a))
        transition = 2 * a / T - 1
        angular_area = 2 * mp.pi * (
            (T / 2) ** 2 * (transition + 1)
            + mp.quad(lambda mu: (a / (1 + mu)) ** 2, [transition, 1])
        )
        self.assertNear(angular_area, null_cap_area(T, a))
        self.assertNear(null_cap_area(T, T), mp.pi * T**2)
        self.assertNear(null_cap_volume(T, T), mp.pi * T**4 / 24)

    def test_null_finite_density_scaling(self):
        # A has length dimension 2 and rho has length dimension -4.
        factor = mp.mpf("1.7")
        action = null_cap_action(100, 1, "0.4")
        rescaled = null_cap_action(100 / factor**4, factor, mp.mpf("0.4") * factor)
        self.assertNear(rescaled, factor**2 * action)

    def test_null_convergence(self):
        limit = null_cap_area(1, "0.5")
        values = [null_cap_action(rho, 1, "0.5") for rho in (10**4, 10**8, 10**12)]
        self.assertTrue(0 < values[0] < values[1] < values[2] < limit)
        self.assertLess(abs(values[-1] / limit - 1), mp.mpf("0.0001"))

    def test_plane_density_against_direct_future_integral(self):
        rho, H = mp.mpf(7), mp.mpf("0.8")
        direct = 1 - rho * plane_future_kernel_integral(rho, H)
        # F_rho'''(H) = F_1'''(rho^(1/4)*H).
        auxiliary = plane_auxiliary(mp.root(rho, 4) * H, 3) / (8 * mp.pi)
        self.assertNear(direct, auxiliary)

    def test_plane_kernel_two_representations(self):
        for value in ("0.1", "0.9", "2", "4", "8"):
            u = mp.mpf(value)
            integral = plane_auxiliary(u, 2) / (2 * mp.pi * mp.sqrt(6))
            self.assertNear(plane_kernel(u), integral)

    def test_plane_finite_moments(self):
        upper = mp.mpf(6)
        mass = mp.quad(plane_kernel, [0, 1, 2, 3, upper])
        first_moment = mp.quad(lambda u: u * plane_kernel(u), [0, 1, 2, 3, upper])
        F = plane_auxiliary(upper)
        derivative = plane_auxiliary(upper, 1)
        self.assertNear(mass, derivative / (2 * mp.pi * mp.sqrt(6)))
        self.assertNear(first_moment, (upper * derivative - F) / (2 * mp.pi * mp.sqrt(6)))

    def test_plane_gaussian_cancellations_and_bounds(self):
        # Independent square-root coordinates used in the half-line Lean proof.
        # These numerical diagnostics do not establish the uniform bounds.
        for value in ("0.1", "0.9", "2", "4", "8"):
            u = mp.mpf(value)
            a = mp.pi * u**4 / 24

            def cancellation(b, d):
                return mp.quad(
                    lambda t: mp.sqrt(1 - t)
                    * (b - (2 * b + 3 * d) * a * t**2 + 2 * d * a**2 * t**4)
                    * mp.exp(-a * t**2),
                    [0, 1],
                )

            second = 2 * mp.pi * u * cancellation(6, 8)
            moment_boundary = 2 * mp.pi * u**3 * cancellation(2, 0)
            self.assertNear(second, plane_auxiliary(u, 2))
            self.assertNear(moment_boundary, u * plane_auxiliary(u, 1) - plane_auxiliary(u))
            self.assertLessEqual(abs(second), 2832 / u**3)
            self.assertLessEqual(abs(moment_boundary), 240 / u)
            self.assertLessEqual(abs(plane_kernel(u)), 1416 / (mp.pi * mp.sqrt(6) * u**3))

    def test_plane_kernel_sign_and_tail(self):
        self.assertGreater(plane_kernel(1), 0)
        self.assertLess(plane_kernel(4), 0)
        asymptote = -2 * mp.sqrt(6) / mp.pi
        self.assertNear(1000**3 * plane_kernel(1000), asymptote, "0.00001")

    def test_ellipsoid_variable_angle_prediction(self):
        self.assertNear(ellipsoid_limit("0.25", (1, 2, 3)), 48 * mp.pi)
        # Values at the shortest- and longest-axis endpoints of one joint.
        slopes = [2 * mp.mpf("0.25") / b for b in (1, 3)]
        self.assertNear(slopes[0], mp.mpf(1) / 2)
        self.assertNear(slopes[1], mp.mpf(1) / 6)
        self.assertNotEqual(mp.atanh(slopes[0]), mp.atanh(slopes[1]))

    def test_ellipsoid_finite_density_scaling(self):
        factor = mp.mpf("1.5")
        action = ellipsoid_action(1000, "0.25", (1, 2, 3))
        rescaled = ellipsoid_action(
            1000 / factor**4, factor / 4, tuple(factor * b for b in (1, 2, 3))
        )
        self.assertNear(rescaled, factor**2 * action)

    def test_ellipsoid_convergence(self):
        limit = ellipsoid_limit("0.25", (1, 2, 3))
        values = [ellipsoid_action(rho, "0.25", (1, 2, 3)) for rho in (10**4, 10**8, 10**12)]
        self.assertTrue(values[0] > values[1] > values[2] > limit)
        self.assertLess(abs(values[-1] / limit - 1), mp.mpf("0.00002"))

    def test_parameter_rejection(self):
        for args in [(0, 0), (1, "1.1"), (1, "-0.1")]:
            with self.assertRaises(ValueError):
                null_cap_area(*args)
        with self.assertRaises(ValueError):
            null_cap_action(0, 1, "0.5")
        with self.assertRaises(ValueError):
            ellipsoid_limit("0.5", (1, 2, 3))
        with self.assertRaises(ValueError):
            plane_kernel(-1)


if __name__ == "__main__":
    unittest.main()
