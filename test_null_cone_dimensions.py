"""Required dimensional null regressions, with independent interval quadrature."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import action_constants, factor_count, interval_coefficient, interval_power_moment, sphere_area
from null_mixed import SineMixedCap
from null_cone_dimensions import angular_rule, constants, interval_response, joint_area, response, source_action


class DimensionalNullTests(unittest.TestCase):
    def test_series_factor_from_actual_interval_moments(self):
        for d in range(2, 11):
            m, q = factor_count(d), s.Rational(d, 2)
            for n in range(6):
                coefficient = s.rf(q*n+1, m)/s.factorial(m)
                ratio = s.gamma(d)*s.rf(q*n+1, m)/(s.factorial(m)*(n+1)*s.rf(q*n+1, d-1))
                self.assertEqual(s.simplify(coefficient*interval_power_moment(d, n)/interval_coefficient(d)-ratio), 0)

    def test_positive_mixture_point_and_mass_all_parities(self):
        for d in (*range(3, 13), 20, 21):
            m, q = factor_count(d), s.Rational(d, 2)
            ell = d-1-m
            a, beta = action_constants(d)
            c = interval_coefficient(d)
            if ell:
                factor = beta*s.gamma(d)/(s.factorial(m)*s.gamma(ell))
                beta0 = s.gamma(m-q+1)*s.gamma(ell)/s.gamma(m-q+1+ell)
                beta1 = s.gamma(m-q)*s.gamma(ell)/s.gamma(m-q+ell)
                self.assertEqual(s.simplify(factor*beta0-a), 0)
                mass = factor*s.gamma(1+1/q)*beta1
            else:
                mass = a*s.gamma(1+1/q)
            self.assertEqual(s.simplify(c**(-1/q)*mass-2*(d-2)), 0)
            self.assertAlmostEqual(float(response(d, 0)), float(a), places=12)

    def test_actual_full_rest_interval_not_assumed_response(self):
        for d in range(2, 11):
            for z in (0.01, 0.3, 2, 10):
                low, high = interval_response(d, z, 64), interval_response(d, z, 96)
                self.assertAlmostEqual(low, high, delta=1e-8)
                self.assertAlmostEqual(float(response(d, z)), high, delta=1e-8)

    def test_higher_dimensional_response_is_not_a_gaussian(self):
        for d in (5, 6, 7, 8):
            a, _, _ = constants(d)
            values = response(d, np.array([0, 1, 10, 100]))
            self.assertTrue((values > 0).all())
            self.assertTrue((np.diff(values) < 0).all())
            self.assertGreater(float(values[-1]), 1e-5)
            self.assertGreater(abs(float(values[1])-a*math.exp(-1)), 0.01)

    def test_two_dimensional_signed_logarithmic_mechanism(self):
        # Source response has a negative part and zero mass, unlike d>2.
        self.assertLess(float(response(2, 2)), 0)
        mass = quad(lambda u: (1-u)*math.exp(-u), 0, np.inf)[0]
        logmass = quad(lambda u: (1-u)*math.exp(-u)*math.log(u), 0, np.inf)[0]
        self.assertAlmostEqual(mass, 0, places=13)
        self.assertAlmostEqual(logmass, -1, places=11)
        # Complete fixed flat diamond, checked independently against its exact law.
        for rho in (0.1, 1, 20, 100):
            actual = source_action(2, rho, "diamond", 48)
            self.assertAlmostEqual(actual, 2*(1-math.exp(-rho/2)), places=10)
        self.assertEqual(joint_area(2, "diamond"), 2)
        self.assertEqual(joint_area(2, "sine"), 2)
        # Dilation of an actual fixed tip cap does not give the d>2 vanishing bound.
        rho, delta = 1e5, 0.1
        tip = source_action(2, rho*delta*delta, "round", 80)
        self.assertAlmostEqual(tip, 2, delta=0.01)
        self.assertGreater(tip, 1.9)

    def test_angular_measure_and_independent_diamond_targets(self):
        for d in range(2, 13):
            _, weights = angular_rule(d, 16)
            self.assertAlmostEqual(weights.sum(), float(sphere_area(d)), places=11)
            expected = float(sphere_area(d))/2**(d-2)
            self.assertAlmostEqual(joint_area(d, "diamond"), expected, places=11)
        self.assertAlmostEqual(joint_area(4, "diamond"), math.pi, places=12)
        self.assertAlmostEqual(joint_area(4, "sine"), SineMixedCap().joint_area(48), places=10)

    def test_nonplanar_complete_source_integrals_and_existing_4d_member(self):
        for d in (2, 3, 4, 5, 6, 7):
            low = source_action(d, 20, "sine", 40)
            high = source_action(d, 20, "sine", 64)
            self.assertAlmostEqual(low, high, delta=3e-8)
            self.assertGreater(high, 0)
        actual = source_action(4, 20, "sine", 32)
        self.assertAlmostEqual(actual, SineMixedCap().action(20, 32), delta=2e-7)
        self.assertGreater(abs(source_action(5, 20, "sine")-source_action(5, 20, "round")), 1e-3)

    def test_invalid_inputs(self):
        for d in (True, 1, 2.5):
            with self.assertRaises(ValueError):
                response(d, 1)
        for z in (-1, math.nan, math.inf):
            with self.assertRaises(ValueError):
                response(5, z)
        for rho in (0, -1, math.nan):
            with self.assertRaises(ValueError):
                source_action(4, rho)
        with self.assertRaises(ValueError):
            source_action(4, 1, "unselected")


if __name__ == "__main__":
    unittest.main()
