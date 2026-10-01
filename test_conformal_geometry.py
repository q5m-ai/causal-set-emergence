"""Exact, independent geometry checks; no stochastic or continuum-limit claims."""

import unittest

import sympy as s

from conformal_geometry import (
    check_conformal_identities,
    conformal_curvature,
    vertical_interval_volume,
)


class ConformalGeometryTests(unittest.TestCase):
    def setUp(self):
        self.coordinates = s.symbols("t x y z", real=True)
        self.t = self.coordinates[0]

    def test_quadratic_factor_nonzero_scalar_from_christoffels(self):
        t = self.t
        omega = 1 + t**2
        metric, gamma, ricci, scalar = conformal_curvature(omega, self.coordinates)
        self.assertEqual(s.factor(metric.det()), -omega**8)
        self.assertEqual(gamma[0, 0, 0], 2 * t / omega)
        self.assertEqual(s.simplify(ricci[0, 0] + 6 * (1 - t**2) / omega**2), 0)
        self.assertEqual(s.simplify(scalar + 12 / omega**3), 0)
        # Numerator is the nonzero constant -12; denominator is positive
        # everywhere, including the whole original fixed region.
        numerator, denominator = s.fraction(scalar)
        self.assertEqual(numerator, -12)
        self.assertTrue(denominator.is_positive)

    def test_unit_and_positive_constant_factors_are_flat(self):
        for omega in (s.Integer(1), s.symbols("c", positive=True)):
            metric, gamma, ricci, scalar = conformal_curvature(omega, self.coordinates)
            self.assertEqual(metric, omega**2 * s.diag(1, -1, -1, -1))
            self.assertEqual(gamma, s.ImmutableDenseNDimArray.zeros(4, 4, 4))
            self.assertEqual(ricci, s.zeros(4, 4))
            self.assertEqual(scalar, 0)

    def test_general_time_factor_sign_convention(self):
        t = self.t
        omega = s.Function("Omega", positive=True)(t)
        _, _, _, scalar = conformal_curvature(omega, self.coordinates)
        self.assertEqual(s.simplify(scalar + 6 * s.diff(omega, t, 2) / omega**3), 0)

    def test_interval_uses_curved_volume_not_flat_formula(self):
        lo, hi = -s.Rational(1, 8), -s.Rational(1, 16)
        flat = s.pi * (hi - lo)**4 / 24
        actual = vertical_interval_volume(1 + self.t**2, self.t, lo, hi)
        self.assertTrue(s.simplify((actual - flat) / s.pi).is_positive)
        c = s.symbols("c", positive=True)
        self.assertEqual(s.simplify(vertical_interval_volume(c, self.t, lo, hi) - c**4 * flat), 0)
        self.assertEqual(vertical_interval_volume(s.Integer(1), self.t, lo, hi), flat)

    def test_invalid_diagnostic_inputs(self):
        with self.assertRaises(ValueError):
            conformal_curvature(s.Integer(1), self.coordinates[:3])
        for lo, hi in ((0, 0), (1, 0)):
            with self.assertRaises(ValueError):
                vertical_interval_volume(s.Integer(1), self.t, lo, hi)

    def test_symbolic_entrypoint(self):
        check_conformal_identities()


if __name__ == "__main__":
    unittest.main()
