"""Checks of written partial research; NOT a complete-action obstruction.

Physical metric/interval tests and normalized-model matching tests are kept
separate. No numerical fit is used as an actual action coefficient.
"""
import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad, solve_ivp

from curved4_focal_geometry import (
    DURATION, MODEL_C, MODEL_POWER, SOURCE_RZ_VOLUME,
    focal_constants, inverse_jet, model_averaged_profile, model_matched_truncation,
    model_profile, model_subtractions, pendulum_endpoint_action,
    physical_focal_volume, physical_regular_volume_jet, physical_segment_action,
    physical_time_weight, segment_jet, symbolic_metric_data,
)
from dimension_kernels import action_constants, interval_coefficient
from full_partner_globalization import primitive_response


class ActualMetricTest(unittest.TestCase):
    def test_metric_curved_but_independent_scalar_target_zero(self):
        metric, ricci, scalar, (_, _, x, _) = symbolic_metric_data()
        self.assertEqual(metric.det(), -1)
        self.assertEqual(ricci[0, 0], -s.cos(4*x))
        self.assertEqual(sum(value != 0 for value in ricci), 1)
        self.assertEqual(scalar, 0)
        # Pullback to (t,r,x,z) has unit absolute Jacobian and spacelike slices.
        change = s.Matrix([[1, -1, 0, 0], [s.Rational(1, 2), s.Rational(1, 2), 0, 0],
                           [0, 0, 1, 0], [0, 0, 0, 1]])
        pulled = change.T*metric*change
        self.assertEqual(change.det(), 1)
        self.assertEqual(s.simplify(pulled.inv()[0, 0]-1+s.sin(2*x)**2/4), 0)
        self.assertAlmostEqual(SOURCE_RZ_VOLUME*math.pi*DURATION, 700*math.pi)

    def test_cone_speed_and_faithful_lift_bounds(self):
        h, velocity = s.symbols('h velocity', real=True)
        cone = 1-velocity**2+h*(1-velocity)**2
        self.assertEqual(s.factor(cone), (velocity-1)*(h*velocity-h-velocity-1))
        self.assertEqual(s.simplify(cone.subs(velocity, -h/(1-h))-1/(1-h)), 0)
        self.assertLess(8*DURATION/3, 20)  # entire r displacement range
        self.assertLess(4*DURATION/math.sqrt(3), 20)  # entire z range
        self.assertLess(8*DURATION/3, 2*math.pi)

    def test_full_and_cutoff_time_weights_against_original_partner_integral(self):
        for length, excess in ((.4, -.02), (1.1, .1), (math.pi, 0), (3.8, -.3)):
            arrival = length/2+excess
            radius = math.sqrt(max(0, 2*length*(DURATION-arrival)))
            for cutoff in (.12, .8, 1.6):
                boundary = math.sqrt(max(0, 2*length*(cutoff-arrival)))
                short_radius = min(radius, boundary)
                integrand = lambda b: DURATION-arrival-b*b/(2*length)
                direct_short = 2*quad(integrand, 0, short_radius, epsabs=1e-13)[0]
                direct_long = 2*quad(integrand, short_radius, radius, epsabs=1e-13)[0]
                short = physical_time_weight(length, excess, cutoff, short=True)
                long = physical_time_weight(length, excess, cutoff)
                self.assertAlmostEqual(short, direct_short, delta=2e-13)
                self.assertAlmostEqual(long, direct_long, delta=2e-13)
                self.assertAlmostEqual(short+long, physical_time_weight(length, excess))
                if length == math.pi and cutoff == .8:
                    self.assertEqual(short, 0)
                    self.assertGreater(long, 0)

    def test_shell_contacts_and_closing_face(self):
        length, excess = .6, -.03
        left, right = .5, 1.1
        a = length/2+excess
        shell = 2*quad(lambda b: DURATION-a-b*b/(2*length),
                        math.sqrt(2*length*(left-a)),
                        math.sqrt(2*length*(right-a)), epsabs=1e-13)[0]
        self.assertAlmostEqual(physical_time_weight(length, excess, left)
                               -physical_time_weight(length, excess, right), shell)
        self.assertEqual(physical_time_weight(2, DURATION-1), 0)
        self.assertEqual(physical_time_weight(2, DURATION), 0)

    def test_global_potential_coercivity_and_winding_gap(self):
        for x in np.linspace(-12, 12, 2401):
            self.assertGreaterEqual(x*x-.25*math.sin(2*x)**2+1e-14,
                                    .5*min(x**4, x*x))
        self.assertGreater(math.pi/2-math.pi/8, 1)
        # Guarded segment regime excludes a different physical circle lift.
        for length in (.2, 2, 3.14):
            for x in (0, .1, math.pi/4):
                alternative = (math.pi-x)**2/(2*length)-length/8
                straight_upper = x*x/(2*length)
                self.assertGreater(alternative, straight_upper)

    def test_actual_pendulum_trace_against_independent_geodesic_ode(self):
        for length, k in ((.3, .1), (2.4, .3), (2.8, .8), (.7, 1), (.4, 1.7)):
            def rhs(_, state):
                x, p, _ = state
                return [p, -.25*math.sin(4*x), .5*(p*p-.25*math.sin(2*x)**2)]
            sol = solve_ivp(rhs, [0, length], [0, k/2, 0], rtol=2e-12, atol=2e-14)
            x, action = pendulum_endpoint_action(length, k)
            self.assertAlmostEqual(x, sol.y[0, -1], delta=2e-11)
            self.assertAlmostEqual(action, sol.y[2, -1], delta=2e-11)

    def test_actual_segment_action_symmetry_and_recovery(self):
        for length, k in ((.6, .3), (2.9, .2), (.1, 1.4)):
            x, action = pendulum_endpoint_action(length, k)
            self.assertAlmostEqual(physical_segment_action(length, x), action, delta=2e-12)
            self.assertEqual(physical_segment_action(length, x),
                             physical_segment_action(length, -x))
        self.assertEqual(physical_segment_action(2, 0), 0)

    def test_quartic_coefficient_from_actual_segment_not_model(self):
        c, _, _ = focal_constants()
        for split in (.4, 1.2, 2.4):
            jet = segment_jet(split)+segment_jet(math.pi-split)
            self.assertAlmostEqual(jet[0], 0, delta=1e-13)
            self.assertAlmostEqual(jet[1]*math.sin(split)**4, c, delta=2e-12)
            errors = []
            for amplitude in (.008, .004):
                target = amplitude*math.sin(split)
                action = (physical_segment_action(split, target)
                          +physical_segment_action(math.pi-split, target))
                errors.append(abs(action/amplitude**4-c))
            self.assertLess(errors[1], errors[0]/3)
            self.assertLess(errors[1], .0002)

    def test_sixth_action_jet_includes_minimizer_correction(self):
        length, target = 1.2, .025
        jet = segment_jet(length)
        approximation = sum(a*target**(2*(i+1)) for i, a in enumerate(jet))
        actual = physical_segment_action(length, target)
        self.assertLess(abs(actual-approximation), 2e-12)
        without_sixth = jet[0]*target**2+jet[1]*target**4
        self.assertGreater(abs(actual-without_sixth), 1e-11)
        self.assertAlmostEqual(actual-without_sixth, jet[2]*target**6, delta=2e-12)
        self.assertLess(jet[2], 0)

    def test_actual_focal_volume_scaling_and_rule_refinement(self):
        _, _, coefficient = focal_constants()
        ratios = [physical_focal_volume(e, 24)/e**1.75 for e in (1e-3, 1e-4, 1e-5)]
        errors = [abs(v/coefficient-1) for v in ratios]
        self.assertTrue(all(x > y for x, y in zip(errors, errors[1:])))
        self.assertLess(errors[-1], .003)
        refined = physical_focal_volume(1e-4, 40)/1e-4**1.75
        self.assertAlmostEqual(refined, ratios[1], delta=1e-5)
        # These are the ACTUAL pendulum intervals, measurably not the exact
        # homogeneous model at finite excess. No fitted coefficient is used.
        self.assertGreater(abs(ratios[0]-coefficient), .09)

    def test_actual_regular_cubic_inverse_coefficient_singular_scaling(self):
        quartic, j, _ = focal_constants()
        expected = -25*quartic**2/(256*(4*j/3*MODEL_C)**1.5)
        errors = []
        for delta in (.1, .03, .01):
            jet = physical_regular_volume_jet(math.pi-delta, 28)
            coefficient = inverse_jet(jet)[2]
            self.assertLess(coefficient, 0)
            errors.append(abs(coefficient*(delta/2)**3.25/expected-1))
        self.assertTrue(all(x > y for x, y in zip(errors, errors[1:])))
        self.assertLess(errors[-1], .012)
        self.assertEqual(-s.Rational(13, 4)+s.Rational(3, 2), -s.Rational(7, 4))

    def test_first_coefficient_flat_null_normalization(self):
        # Independent clock speed eta=1/2, null u length twice temporal span.
        duration = s.Symbol('duration', positive=True)
        from_index_form = s.pi*s.Rational(1, 4)*(2*duration)**2/6
        from_flat_interval = interval_coefficient(4)*(2*duration)**2
        self.assertEqual(s.simplify(from_index_form-from_flat_interval), 0)

    def test_physical_input_guards(self):
        calls = [lambda: physical_time_weight(0, 0),
                 lambda: physical_time_weight(1, 0, 2),
                 lambda: physical_time_weight(1, 0, short=True),
                 lambda: physical_segment_action(math.pi, .01),
                 lambda: physical_segment_action(1, 1),
                 lambda: physical_focal_volume(.01),
                 lambda: pendulum_endpoint_action(1, -1),
                 lambda: physical_regular_volume_jet(math.pi)]
        for call in calls:
            with self.assertRaises(ValueError):
                call()


class MatchedModelTest(unittest.TestCase):
    def test_global_minimum_parameter_jacobian(self):
        a, k, u, r = s.symbols('a k u r', real=True)
        aa, bb = k-6*a*a, 8*a**3-2*k*a
        polynomial = lambda x: x**4+aa*x*x+bb*x
        self.assertEqual(s.expand(polynomial(a+u)-polynomial(a)
                                  -u*u*(u*u+4*a*u+k)), 0)
        self.assertEqual(s.det(s.Matrix([aa, bb]).jacobian([a, k])), 2*k)
        self.assertEqual(s.simplify(s.sqrt(k)*2*k-2*k**s.Rational(3, 2)), 0)

    def test_regular_inverse_coefficients_symbolically(self):
        w, aa, c = s.symbols('w aa c', positive=True)
        first = aa**s.Rational(1, 4)/s.sqrt(c)
        second = 1/(8*c*aa**s.Rational(3, 2))
        third = -25/(256*c**s.Rational(3, 2)*aa**s.Rational(13, 4))
        e = first*w+second*w*w+third*w**3
        volume = c/s.sqrt(aa)*e*e*(1-e/(4*aa*aa)+35*e*e/(128*aa**4))
        self.assertEqual(s.series(volume, w, 0, 5).removeO().expand(), w*w)

    def test_profile_counts_both_opening_wells(self):
        for excess, r in ((.003, 0), (.0004, .49999), (.07, .49), (.4, .5)):
            roots = np.roots([1, 4*r, 1, 0, -excess])
            real = sorted(x.real for x in roots if abs(x.imag) < 1e-9)
            direct = sum(quad(lambda u: max(0, excess-u*u-4*r*u**3-u**4)**1.5,
                              lo, hi, epsabs=2e-14, epsrel=1e-11)[0]
                         for lo, hi in zip(real, real[1:]))
            self.assertAlmostEqual(model_profile(excess, r, 64), direct,
                                   delta=max(1e-13, 2e-7*direct))
            self.assertAlmostEqual(model_profile(excess, -r, 64), direct,
                                   delta=max(1e-13, 2e-7*direct))
        tiny = 1e-5
        # At the equal-minimum boundary BOTH quadratic wells contribute.
        self.assertAlmostEqual(model_profile(tiny, .5)/(MODEL_C*tiny*tiny), 2, delta=.0001)

    def test_quartic_large_excess_scaling(self):
        excess = 1e6
        limit = float(s.beta(s.Rational(1, 4), s.Rational(5, 2))/2)
        for r in (0, .3, .5):
            self.assertAlmostEqual(model_profile(excess, r, 64)/excess**1.75,
                                   limit, delta=.003*limit)

    def test_both_matched_subtractions_required(self):
        a0, a1 = model_subtractions()
        self.assertAlmostEqual(a0, .809993233481564)
        self.assertAlmostEqual(a1, -.2793706641400934)
        for excess in (.001, .0001):
            profile = model_averaged_profile(excess, 48)
            recovered = (profile*excess**(2*MODEL_POWER)-a0)/excess
            self.assertAlmostEqual(recovered, a1, delta=.0004)
            regular_only = -MODEL_POWER*a0/6
            self.assertGreater(abs(recovered-regular_only), .1)
            # Two subtractions leave the integrable E^(-4/7) remainder.
            remainder = (profile-a0*excess**(-18/7)-a1*excess**(-11/7))*excess**(4/7)
            self.assertTrue(-.32 < remainder < -.29)

    def test_finite_matched_truncations_not_a_sign_certificate(self):
        low = model_matched_truncation(.001, 1000, 16)
        high = model_matched_truncation(.001, 1000, 32)
        smaller = model_matched_truncation(.0001, 1000, 32)
        self.assertAlmostEqual(low, high, delta=.004)
        self.assertTrue(.62 < high < .64)
        self.assertTrue(.59 < smaller < .62)
        self.assertGreater(high-smaller, .02)  # omitted low remainder is material
        # No assertion here assigns this value to C_phys or certifies I's sign.

    def test_actual_volume_phase_signed_normalization(self):
        power = s.Rational(9, 7)
        rho = s.Symbol('rho', positive=True)
        moment = s.gamma(power)*s.prod(1-2*power/j for j in range(1, 4))
        self.assertGreater(float(moment), 0)
        expected = -action_constants(4)[1]*power*moment
        # Existing interface uses N(w)=w^(2p), v=c4*w^2; restore that c4.
        actual = primitive_response(4, 2*power, rho)*interval_coefficient(4)**power
        self.assertEqual(s.simplify(actual/rho**s.Rational(3, 14)-expected), 0)

    def test_model_input_guards(self):
        for call in (lambda: model_profile(0, 0), lambda: model_profile(1, .6),
                     lambda: model_profile(1, 0, 3),
                     lambda: model_matched_truncation(.1),
                     lambda: model_averaged_profile(0)):
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
