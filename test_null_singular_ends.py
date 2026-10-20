"""Finite arithmetic/domain checks, not proofs of SE/IF uniform remainders."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import action_constants, factor_count, interval_coefficient
from null_cartesian_pushforward import kernel, time_density_average
from null_front_accounting import null_time_weight
from null_singular_ends import (
    closing_weight, cusp_action, cusp_bounds, cusp_contains, cusp_partner_roots,
    cusp_volume, matched_profile_parts, secondary_coefficient,
    secondary_derivative_deficit,
)
from seven_dimensional_focusing import (
    ANTIPODAL_COEFFICIENT, OPENING_COEFFICIENT, sign_certificate,
    transition_profile,
)


class SingularEndTests(unittest.TestCase):
    def test_cusp_domain_keeps_closed_order_and_null_generator_exclusion(self):
        for v in (-.8, -.1, 0., .1, .7):
            for y in (-.2, 0., .15):
                lo, hi = cusp_bounds(v, y)
                self.assertEqual(cusp_contains(((lo+hi)/2, v, y)), hi > lo)
        self.assertFalse(cusp_contains((.2, 0., 0.)))  # In closed J+(b).
        self.assertTrue(cusp_contains((.2, -.001, 0.)))
        self.assertTrue(cusp_contains((.2, 0., .01)))
        self.assertFalse(cusp_contains((.1, .4, .2)))  # Exactly on b's cone.

    def test_actual_far_partners_survive_at_the_cusp_end(self):
        qv, z = .4, .2
        for pv in (.01, .001, .0001):
            yp, yq = pv*z, qv*z
            B = -(qv+1)/(pv+1)*yp**2+2*yp*yq-pv/qv*yq**2
            normal = B/(4*(qv-pv))
            pu, qu = yp**2/(pv+1)+normal, yq**2/qv-normal
            self.assertTrue(cusp_contains((pu, pv, yp)))
            self.assertTrue(cusp_contains((qu, qv, yq)))
            sigma = (qu-pu)*(qv-pv)-(yq-yp)**2
            self.assertAlmostEqual(sigma, B/2, delta=1e-15)
            lower, upper = cusp_partner_roots(pv, qv)
            self.assertLess(lower, yq/yp)
            self.assertLess(yq/yp, upper)
        self.assertGreater(cusp_partner_roots(.0001, qv)[1], 7000)

    def test_joint_end_resolution_retains_the_physical_time(self):
        R, theta, U, V, Y = s.symbols('R theta U V Y', positive=True)
        u, v, y = R*theta**2*U, R*V, R*theta*Y
        self.assertEqual(s.simplify(y*y/(v+1)/(R*theta**2)-R*Y*Y/(1+R*V)), 0)
        self.assertEqual(s.simplify(y*y/v/(R*theta**2)-Y*Y/V), 0)
        self.assertEqual(s.simplify(u*v-y*y-R**2*theta**2*(U*V-Y*Y)), 0)
        self.assertNotEqual(s.expand((u+v)/2), R*V/2)  # Not a v-only cutoff.

    def test_whole_cusp_volume_is_not_a_bilocal_decomposition(self):
        expected = math.pi/12*(2**1.5-1)
        self.assertAlmostEqual(cusp_volume(order=44), expected, delta=3e-12)
        # The exact response is integrated over M, not the difference of two
        # autonomous actions. The point volume alone cannot supply that response.
        rho = 7.
        point = float(action_constants(3)[0])*rho**(2/3)*expected
        self.assertGreater(abs(point-cusp_action(rho)), .1)

    def test_complete_signed_fibre_then_two_normal_integrations(self):
        for rho in (.4, 3., 20.):
            primitive = cusp_action(rho, order=48)
            direct = cusp_action(rho, order=64, integrate_normal=False)
            self.assertAlmostEqual(primitive, direct, delta=3e-9)
        values = [cusp_action(rho, order=56) for rho in (1., 10., 1000.)]
        self.assertEqual(values, sorted(values))
        self.assertTrue(all(0 < x < math.pi*math.sqrt(2) for x in values))

    def test_flat_ray_functional_independently_gives_outer_screen(self):
        # About a: c has elapsed time 3/2 and spatial displacement -1/2.
        # Null exit solves (3/2-r)^2-|(-1/2,0)-r*omega|^2=0.
        value = quad(lambda angle: 2/(3+math.cos(angle)), 0, 2*math.pi,
                     epsabs=1e-12)[0]
        self.assertAlmostEqual(value, math.pi*math.sqrt(2), places=11)
        # The single generator stopped earlier by b has no angular mass in d=3.
        self.assertAlmostEqual(2/(3-1), 1)

    def test_actual_curved_three_dimensional_interval_not_endpoint_density(self):
        p, q, sigma = -.7, .4, .8
        ell = q-p
        average = 1+q*q-ell*q+5*ell*ell/16-3*sigma/80
        self.assertAlmostEqual(average, time_density_average(3, p, q, sigma), places=13)
        self.assertGreater(abs(average-(1+q*q)), .01)

    def test_false_curved_fibre_exponential_has_exact_nonzero_error(self):
        x, z, k = s.symbols('x z k', positive=True)
        upper = s.expand((1+k*x*x)*((1+5*k*x*x/16)*x**5/5-3*k*x**7/560))
        lower = s.expand((1+k*((z+1)/2)**2)*(
            (1+5*k*((z+1)/2)**2/16)*z**s.Rational(5, 2)/5
            -3*k*z**s.Rational(7, 2)/560)/2)
        moment = s.pi**2/6*(s.integrate(upper, (x, 0, 1))-s.integrate(lower, (z, 0, 1)))
        volume = s.pi/12*(1+s.Rational(11, 40)*k)
        actual = s.factor(s.Rational(35, 8)*moment-volume**2/2)
        expected = s.pi**2*k*(28080-5429*k)/197683200
        self.assertEqual(s.simplify(actual-expected), 0)
        self.assertGreater(float(actual.subs(k, 1)), 0)
        self.assertEqual(action_constants(3)[0], action_constants(3)[1])

    def test_floor_normalization_and_parity_mass_reconstructed(self):
        for d in range(2, 11):
            m, critical = factor_count(d), 1+s.Rational(2, d)
            def E(exponent):
                return (s.gamma(exponent)*s.gamma(s.Rational(d-1, 2))/s.factorial(m)
                        *s.gamma(m+1-d*exponent/2)/s.gamma((d+1-d*exponent)/2))
            area = 2*s.pi**s.Rational(d-1, 2)/s.gamma(s.Rational(d-1, 2))
            beta, c = action_constants(d)[1], interval_coefficient(d)
            frozen_mass = -beta*area*c**(-critical)*E(critical)/(4*d)
            self.assertEqual(s.simplify(frozen_mass), 1)
            self.assertEqual(s.simplify((d-1)/(d+1-d*critical)), -(d-1))

    def test_closing_weight_keeps_both_endpoint_masks(self):
        for T, U in ((4., 2.), (math.pi, 2.8), (2., 1.9)):
            actual = closing_weight(U, T)
            direct = null_time_weight(U, T)
            self.assertAlmostEqual(actual, direct, delta=2e-10)
        T = math.pi
        leading = 256*math.pi*T*math.sqrt(2*T)/945
        self.assertAlmostEqual(closing_weight(T, T, scaled=True), leading, places=11)
        self.assertEqual(closing_weight(T, T), 0)
        self.assertAlmostEqual(closing_weight(T-1e-5, T, scaled=True), leading, delta=4e-5)

    def test_positive_overlap_bracket_is_exact_not_a_fitted_jet(self):
        T, v = 2.3, 1.6
        actual = (T*T+v*v)*math.log(T/v)-T*T+v*v
        integral = (T-v)**3*quad(lambda t: (1-t)**2*(
            1/(v+(T-v)*t)+v*v/(v+(T-v)*t)**3), 0, 1)[0]
        self.assertAlmostEqual(actual, integral, places=13)
        self.assertGreater(integral, 0)

    def test_threshold_head_and_tail_orders_are_critically_summable(self):
        q = s.Rational(9, 2)
        for j in range(1, 5):
            coefficient = q+1-s.Rational(6*j, 7)
            self.assertGreater(coefficient+1, -1)
            head = s.Rational(2*j, 7)+(q+3-s.Rational(6*j, 7))/3
            self.assertEqual(head, s.Rational(5, 2))
            self.assertAlmostEqual(quad(lambda z: z**(s.Rational(2*j, 7)-1)*kernel(7, z),
                                       0, np.inf, epsabs=1e-9)[0], 0, delta=2e-8)
        self.assertEqual(q+1-s.Rational(30, 7), s.Rational(17, 14))
        self.assertGreater(s.Rational(10, 7), s.Rational(9, 7))
        # The unweighted above-threshold fourth coefficient is not integrable.
        self.assertLess(2-s.Rational(24, 7), -1)

    def test_actual_secondary_union_coefficient_and_omitted_edge(self):
        theta = 2.5
        coefficient = secondary_coefficient(theta)
        self.assertGreater(coefficient, 0)
        for distance, tolerance in ((.01, .003), (.001, .0003)):
            ratio = secondary_derivative_deficit(theta, distance)/(
                3.5*coefficient*distance**2.5)
            self.assertAlmostEqual(ratio, 1., delta=tolerance)
        a = .001
        limit = ANTIPODAL_COEFFICIENT*OPENING_COEFFICIENT
        self.assertAlmostEqual(math.sqrt(a)*secondary_coefficient(math.pi-a)/limit,
                               1., delta=.0009)

    def test_both_profile_sides_and_matching_subtraction_are_indispensable(self):
        for S in (0., .3, .95, 1.2):
            self.assertAlmostEqual(transition_profile(S)-transition_profile(-S),
                                   S**3+1.5*S, delta=3e-13)
        opening, matching, meridian = matched_profile_parts()
        lower, upper = sign_certificate()
        total = opening+matching+meridian
        self.assertLess(float(lower), total)
        self.assertLess(total, float(upper))
        self.assertLess(opening+matching, 0)  # Dropping the meridian reverses sign.
        self.assertGreater(opening+meridian, .3)  # Dropping matching changes coefficient.
        self.assertNotAlmostEqual(matching+meridian, total, places=3)

    def test_invalid_inputs_do_not_silently_drop_a_domain(self):
        calls = (lambda: cusp_contains((0, 0)), lambda: cusp_bounds(-1, 0),
                 lambda: cusp_partner_roots(0, .5), lambda: cusp_action(0),
                 lambda: cusp_action(1, order=True), lambda: cusp_volume(order=2),
                 lambda: closing_weight(2, 1), lambda: closing_weight(0, 1),
                 lambda: secondary_coefficient(math.pi),
                 lambda: secondary_derivative_deficit(2.5, 2))
        for call in calls:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
