"""Adversarial finite diagnostics for the written TC and NA arguments."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.special import beta

from dimension_kernels import factor_count, transverse_moment
from null_cone_dimensions import response, source_action
from null_contact_matching import (
    closing_model_parts, flat_2d_round_cap_action, matching_tail,
    null_closing_phase, null_displacement,
)
from null_front_accounting import null_time_weight


class NullContactMatchingTests(unittest.TestCase):
    def test_signed_moments_and_uniform_tail_both_parities(self):
        for d in (*range(2, 11), 19, 20):
            m = factor_count(d)
            for j in range(m):
                self.assertEqual(transverse_moment(d, j), 0)
            exponent = d+1-2*(m+1)
            self.assertEqual(exponent, -3 if d % 2 == 0 else -2)
            self.assertGreater(matching_tail(d, 0), 0)
            self.assertGreater(matching_tail(d, 1), matching_tail(d, 4))
            self.assertGreater(matching_tail(d, 4), matching_tail(d, 16))
            power = 2*m-d
            self.assertAlmostEqual(matching_tail(d, 100)*power*100**power, 1,
                                   delta=.0003)

    def test_tail_matches_original_integral_not_just_asymptotic_power(self):
        for d in (2, 3, 4, 7, 10):
            m = factor_count(d)
            for lower in (0., .15, 1., 3.):
                direct = quad(lambda v: v**(d+1)*(1+v**d)**(-2*(m+1)/d),
                              lower, np.inf, epsabs=1e-11)[0]
                self.assertAlmostEqual(matching_tail(d, lower), direct, delta=3e-10)

    def test_closing_first_retains_actual_phase_and_both_subtraction_terms(self):
        for d in (2, 3, 4, 7):
            for height in (.002, .17, 1.2):
                for rho in (.7, 40.):
                    original, smooth, error = closing_model_parts(d, rho, height)
                    self.assertAlmostEqual(original, smooth-error, delta=3e-11)
        original, smooth, error = closing_model_parts(4, 2., .17)
        self.assertGreater(abs(error), 1e-5)
        self.assertNotAlmostEqual(original, smooth, places=5)
        self.assertEqual(closing_model_parts(4, 2., 0.), (0., 0., 0.))
        self.assertEqual(closing_model_parts(4, 2., -.2), (0., 0., 0.))

    def test_positive_speed_margin_and_phase_derivative(self):
        b, mu, v = s.symbols('b mu v', real=True)
        # xi=1-b^2; exact derivative of xi/(1+v*b*mu)^2.
        phase = (1-b*b)/(1+v*b*mu)**2
        derivative = s.simplify(s.diff(phase, b)/(-2*b))
        self.assertEqual(s.simplify(derivative-(1+v*mu/b)/(1+v*b*mu)**3), 0)
        for slope in (.1, .6, .95):
            for cosine in np.linspace(-1, 1, 9):
                for xi in (0., .01*(1-slope)):
                    self.assertGreaterEqual(1+slope*math.sqrt(1-xi)*cosine,
                                            1-slope-1e-15)

    def test_nn_closing_phase_has_two_branches_and_a_moving_fold(self):
        for cosine in (.2, .7, .99):
            turning = 1-cosine*cosine
            peak = null_closing_phase(turning, cosine)
            self.assertAlmostEqual(peak, 1/turning, delta=1e-10)
            self.assertLess(null_closing_phase(turning/2, cosine), peak)
            self.assertLess(null_closing_phase((turning+1)/2, cosine), peak)
        for xi in (.01, .001, .0001):
            self.assertAlmostEqual(xi*null_closing_phase(xi, 1.), 4., delta=.021)

    def test_null_cartesian_map_keeps_order_phase_jacobian_and_time(self):
        v, eta, y = s.symbols('v eta y', positive=True)
        w = eta+y*y/v
        t, x = (v+w)/2, (v-w)/2
        self.assertEqual(s.simplify(t*t-x*x-y*y), v*eta)
        self.assertEqual(s.simplify(s.det(s.Matrix([t, x, y]).jacobian([v, eta, y]))), -s.Rational(1, 2))
        for vv, ee, yy in ((.02, 2., [0., 0.]), (.8, .03, [.4, -.2]), (2., 0., [.3, .5])):
            delta = null_displacement(vv, ee, yy)
            self.assertGreaterEqual(delta[0], np.linalg.norm(delta[1:])-1e-14)
            self.assertAlmostEqual(delta[0]**2-float(delta[1:]@delta[1:]), vv*ee, places=13)
        # Long in physical time even though v is arbitrarily small.
        delta = null_displacement(.02, 2., [0., 0.])
        self.assertGreater(delta[0], .7)
        self.assertLess(.02, .7)

    def test_null_plane_mask_uses_the_whole_transverse_paraboloid(self):
        height = .3
        for vv, ee, yy in ((1., .1, [.2, .1]), (1., .1, [.6, .1]), (.2, .2, [.1, .1])):
            delta = null_displacement(vv, ee, yy)
            actual = height-(delta[0]-delta[1])
            transformed = height-ee-np.dot(yy, yy)/vv
            self.assertAlmostEqual(actual, transformed, places=14)
        # Dropping transverse partners changes membership, not merely a measure.
        self.assertTrue(height-.1 > 0)
        self.assertFalse(height-.1-(.6**2+.1**2) > 0)

    def test_two_dimensional_coincident_crease_is_not_a_zero_measure_point(self):
        for rho in (.4, 2., 15.):
            full = source_action(2, rho, kind='round', order=48)
            self.assertAlmostEqual(flat_2d_round_cap_action(rho), full, delta=2e-11)
            # Independent ordinary triangle integral of the full source response.
            direct = 2*rho*quad(lambda t: quad(
                lambda r: float(response(2, rho*(t*t-r*r)/2)), 0, t,
                epsabs=1e-10)[0], 0, 1, epsabs=1e-10)[0]
            self.assertAlmostEqual(direct, full, delta=2e-10)
        # For centers +/-1 and H=1 the lens is empty; actual valuation doubles
        # the full cap action. Two ordinary exposed counting atoms are not enough.
        whole_union = 2*flat_2d_round_cap_action(10000.)
        self.assertAlmostEqual(whole_union, 4., delta=.001)
        self.assertGreater(abs(whole_union-2.), 1.9)

    def test_np_threshold_coefficient_from_positive_weight(self):
        u = math.pi
        predicted = 256*math.pi*u*math.sqrt(2*u)/945
        self.assertAlmostEqual(float(beta(1.5, 4)), 32/315, places=14)
        errors = []
        for epsilon in (.05, .02, .008):
            actual = null_time_weight(u, duration=u+epsilon)/epsilon**4.5
            errors.append(abs(actual/predicted-1))
        self.assertLess(errors[-1], errors[0])
        self.assertLess(errors[-1], .005)

    def test_np_coefficient_is_not_quadratic_in_width(self):
        widths = math.pi+np.array([.1, .2, .3, .4])
        values = np.array([null_time_weight(math.pi, duration=T) for T in widths])
        # This is a finite negative control, not the NA3 no-go proof.
        self.assertGreater(abs(float(np.diff(values, n=3)[0])), .001)
        h = s.symbols('h', positive=True)
        self.assertEqual(s.limit(h**s.Rational(9, 2)/h**2, h, 0, dir='+'), 0)

    def test_invalid_diagnostic_inputs(self):
        for operation in (lambda: matching_tail(1, 0), lambda: matching_tail(4, -1),
                          lambda: closing_model_parts(4, 0, .1),
                          lambda: closing_model_parts(4, 1, .1, slope=1),
                          lambda: null_closing_phase(0, 1),
                          lambda: null_displacement(0, 1, []),
                          lambda: flat_2d_round_cap_action(-1)):
            with self.assertRaises(ValueError):
                operation()


if __name__ == '__main__':
    unittest.main()
