"""Finite checks of the independent #156 attack; no asymptotic certification."""

import math
import unittest

import sympy as s
from scipy.integrate import quad

from dimension_kernels import Z, action_constants, kernel_polynomial
from null_front_accounting import null_time_weight
from null_suspension import (
    cap_weight, circle_interval, diamond_action, diamond_target_variation,
    physical_section, rapidity_weight, section_radius, short_weight,
    suspended_sphere_weight,
)


class NullSuspensionTests(unittest.TestCase):
    def test_both_endpoint_overlap_and_rapidity_jacobian(self):
        for t in (0.7, 2.0, 4.0):
            for ratio in (0.03, 0.4, 0.91, 0.999):
                u = t*ratio
                self.assertAlmostEqual(cap_weight(u, t), rapidity_weight(u, t),
                                       delta=2e-10*max(1, t**3))

    def test_cubic_closing_coefficient_not_a_constant_cap(self):
        t = 2.0
        for gap in (1e-3, 1e-5, 1e-7):
            self.assertAlmostEqual(cap_weight(t-gap, t)/gap**3, 2/3,
                                   delta=gap)

    def test_true_physical_short_long_restoration(self):
        t, delta = 4.0, 0.4
        for u in (0.01, 0.2, 0.39, 0.4, 0.7, 3.9):
            short = short_weight(u, delta, t)
            self.assertAlmostEqual(short, rapidity_weight(u, t, delta, True),
                                   delta=2e-10)
            self.assertAlmostEqual(short+rapidity_weight(u, t, delta),
                                   cap_weight(u, t), delta=2e-10)
        # u < delta does not mean all partners are physically short.
        self.assertGreater(rapidity_weight(0.2, t, delta), 0.1)

    def test_physical_section_and_abel_derivative(self):
        for u, r, v in ((1.3, .2, .6), (2.1, .8, .7), (1.2, 0., .4)):
            b = section_radius(u, r, v)
            term = lambda x: 0 if x == 0 else x*x*math.asinh(b/x)
            exact = u*b-term(r)-term(v)
            self.assertAlmostEqual(physical_section(u, r, v), exact, places=10)
            h = 1e-5
            derivative = (physical_section(u+h, r, v)
                          - physical_section(u-h, r, v))/(2*h)
            self.assertAlmostEqual(derivative, 2*b, delta=1e-8)
        self.assertEqual(physical_section(1.0, .4, .6), 0)

    def test_actual_circle_interval_has_flat_local_value(self):
        for u, theta in ((1.0, .2), (1.1, .7), (.8, 0.0)):
            actual = circle_interval(u, theta, 8.0)
            flat = math.pi/12 * (u*u-theta*theta)**1.5
            self.assertAlmostEqual(actual, flat, delta=2e-8)

    def test_whole_circle_union_is_not_a_sum_of_route_volumes(self):
        u, theta, length = 3.7, 1.0, 4.0
        actual = circle_interval(u, theta, length)
        route = lambda d: math.pi/12 * max(0, u*u-d*d)**1.5
        self.assertGreater(actual, route(theta)+1e-3)
        self.assertLess(actual, route(theta)+route(length-theta)-1e-3)

    def test_complete_flat_three_d_pair_domain_two_integrations(self):
        # T<L/2 ensures that the actual circle interval just checked is flat.
        # Integrate both endpoint (t,z) masks before/after the boost.
        t, length, rho = .8, 4., 1.3
        kernel = s.lambdify(Z, kernel_polynomial(3)*s.exp(-Z), 'math')
        def angular(u):
            return 2*length*quad(
                lambda theta: kernel(rho*math.pi/12*(u*u-theta*theta)**1.5),
                0, u, epsabs=1e-9)[0]
        reduced = quad(lambda u: cap_weight(u, t)*angular(u),
                       0, t, epsabs=1e-9)[0]
        def temporal(tau):
            zmax = min(tau, t-tau)
            return quad(lambda z: ((t-tau)**2-z*z)
                        * angular(math.sqrt(max(0., tau*tau-z*z))),
                        0, zmax, epsabs=1e-9)[0]
        original = quad(temporal, 0, t/2, epsabs=1e-9)[0]
        original += quad(temporal, t/2, t, epsabs=1e-9)[0]
        self.assertAlmostEqual(reduced, original, delta=2e-8)

    @staticmethod
    def width_operator(f, t):
        for root in (2, 2, 0, 0):
            f = s.expand(t*s.diff(f, t)-root*f)
        return s.simplify(f)

    def test_exact_green_equation_and_boundary_jump(self):
        t, u = s.symbols('T u', positive=True)
        g = u*((t*t+u*u)*s.log(t/u)-t*t+u*u)
        self.assertEqual(self.width_operator(g, t), 0)
        for j in range(3):
            self.assertEqual(s.diff(g, t, j).subs(t, u), 0)
        self.assertEqual(s.diff(g, t, 3).subs(t, u), 4)
        # Test the full Green integral, including its lower boundary.
        for power in (0, 1, 2, 5):
            primitive = s.integrate(g*u**power, (u, 0, t))
            self.assertEqual(self.width_operator(primitive, t), 4*t**(power+4))

    def test_width_operator_loses_both_independent_target_terms(self):
        t = s.Symbol('T', positive=True)
        for term in (s.Integer(1), s.log(t), t*t, t*t*s.log(t)):
            self.assertEqual(self.width_operator(term, t), 0)

    def test_actual_diamond_green_equation_not_zero_action(self):
        t, rho = s.symbols('T rho', positive=True)
        a = rho*t*t/2
        action = 2*(1-s.exp(-a))
        kernel = (kernel_polynomial(2)*s.exp(-Z)).subs(Z, a)
        self.assertEqual(s.simplify(self.width_operator(action, t)
                                   + 16*rho*rho*t**4*kernel), 0)
        self.assertGreater(diamond_action(100, 1.0), 1.999)
        self.assertLess(diamond_action(1, .001), 1.1e-6)

    def test_diamond_complete_pair_integral_and_original_point(self):
        a, beta = map(float, action_constants(2))
        kernel = s.lambdify(Z, kernel_polynomial(2)*s.exp(-Z), 'math')
        for rho in (.01, 1.0, 12.0):
            t = 1.3
            pair = quad(lambda u: cap_weight(u, t)*kernel(rho*u*u/2),
                        0, t, epsabs=2e-12)[0]
            complete = a*rho*t*t/2-beta*rho*rho*pair
            self.assertAlmostEqual(complete, diamond_action(rho, t), places=9)
            if rho == 12:
                self.assertGreater(abs(complete-(-beta*rho*rho*pair)), 10)

    def test_complete_target_variation_grows_while_action_converges(self):
        t = 1.0
        first = diamond_target_variation(2e3, t)
        second = diamond_target_variation(2e5, t)
        self.assertAlmostEqual((second-first)/math.log(100), 4/math.e,
                               places=9)
        self.assertAlmostEqual(diamond_action(2e5, t), 2.0)

    def test_spherical_weight_recovery_preserves_both_endpoints(self):
        for t, u in ((4., .4), (4., math.pi), (5., 2.), (3.3, 3.2)):
            self.assertAlmostEqual(suspended_sphere_weight(u, t),
                                   null_time_weight(u, t),
                                   delta=1e-8*max(1, t**6))

    def test_invalid_inputs(self):
        for u, t in ((-1, 1), (1, 0), (math.nan, 1), (1, math.inf)):
            with self.assertRaises(ValueError):
                cap_weight(u, t)
        for delta in (0, .5, -1, math.nan):
            with self.assertRaises(ValueError):
                short_weight(.1, delta, 1.)
        with self.assertRaises(ValueError):
            circle_interval(1, 3, 4)
        with self.assertRaises(ValueError):
            rapidity_weight(.1, 1., short=True)


if __name__ == '__main__':
    unittest.main()
