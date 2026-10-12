"""Physical diagnostics, separate from the written CG/CO proof and model certificate."""
import math
import unittest

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import ellipe, ellipj, ellipk

from curved4_focal_geometry import (DURATION, focal_constants, physical_segment_action,
                                    physical_time_weight)
from curved4_focal_globalization import (
    principal_cusp_density, principal_cusp_prefactor, cusp_source_data,
    cusp_source_window, cusp_time, internal_cut_data, physical_circle_action,
    rotating_cut_data,
)


def trace(source, velocity, length, jacobi=False):
    def rhs(_, state):
        x, v, action = state[:3]
        answer = [v, -.25*math.sin(4*x), .5*(v*v-.25*math.sin(2*x)**2)]
        if jacobi:
            answer += [state[4], -math.cos(4*x)*state[3]]
        return answer
    initial = [source, velocity, 0.]+([0., 1.] if jacobi else [])
    return solve_ivp(rhs, [0, length], initial, rtol=2e-12, atol=2e-14, dense_output=True)


class PhysicalSourceFamilyTest(unittest.TestCase):
    def test_zero_source_recovers_existing_physical_constants(self):
        data = cusp_source_data(0)
        quartic, longitudinal, coefficient = focal_constants()
        self.assertAlmostEqual(data.quartic, quartic)
        self.assertAlmostEqual(data.longitudinal, longitudinal)
        self.assertEqual(data.length, math.pi)
        self.assertEqual(data.action, 0)
        from scipy.special import beta
        self.assertAlmostEqual(data.volume_factor*beta(.25, 2.5)/2, coefficient)
        self.assertAlmostEqual(data.endpoint_jacobian, 2*quartic**.75)

    def test_entire_causal_source_window_and_closing_contact(self):
        edge = cusp_source_window()
        self.assertTrue(0 < edge < math.pi/8)
        self.assertAlmostEqual(cusp_source_data(edge).null_time, DURATION, delta=1e-13)
        values = [cusp_source_data(p).null_time for p in np.linspace(0, edge, 15)]
        self.assertTrue(all(a < b for a, b in zip(values, values[1:])))
        self.assertGreater(cusp_time(.5), DURATION)
        self.assertAlmostEqual(cusp_source_data(-.2).null_time, cusp_source_data(.2).null_time)

    def test_turning_geodesic_and_jacobi_field_against_ode(self):
        for p in (0, .1, .25, .32):
            data = cusp_source_data(p)
            solution = trace(p, 0, data.length, jacobi=True)
            x, velocity, action, j, derivative = solution.y[:, -1]
            self.assertAlmostEqual(x, -p, delta=2e-11)
            self.assertAlmostEqual(velocity, 0, delta=2e-11)
            self.assertAlmostEqual(action, data.action, delta=2e-11)
            self.assertAlmostEqual(j, 0, delta=2e-11)
            self.assertAlmostEqual(derivative, -1, delta=2e-11)
            for t in np.linspace(0, data.length, 17):
                sn, _, dn, _ = ellipj(t, data.parameter)
                self.assertAlmostEqual(solution.sol(t)[3], sn/dn, delta=2e-11)

    def test_quartic_coefficient_from_actual_endpoint_shooting(self):
        for p in (.1, .3):
            data = cusp_source_data(p)
            errors = []
            for velocity in (.02, .01):
                positive = trace(p, velocity, data.length).y[0, -1]
                negative = trace(p, -velocity, data.length).y[0, -1]
                cubic = (positive-negative)/(2*velocity**3)
                errors.append(abs(cubic-4*data.quartic))
            self.assertLess(errors[1], .3*errors[0])
            self.assertLess(errors[1], .01)

    def test_middle_action_quartic_from_global_minima(self):
        for p in (0, .1, .25, .3):
            data = cusp_source_data(p)
            errors = []
            for amplitude in (.02, .01):
                middle = amplitude/math.sqrt(1-data.parameter)
                broken = (physical_circle_action(data.length/2, p, middle)
                          + physical_circle_action(data.length/2, middle, -p)-data.action)
                errors.append(abs(broken/amplitude**4-data.quartic))
            self.assertLess(errors[1], .3*errors[0])
            self.assertLess(errors[1], .0002)

    def test_principal_density_retains_closing_weight_not_a_fitted_action(self):
        edge = cusp_source_window()
        self.assertGreater(principal_cusp_density(0), 0)
        self.assertLess(principal_cusp_density(edge), 1e-15)
        self.assertEqual(principal_cusp_density(edge+.01), 0)
        ratio = principal_cusp_density(edge-.002)/principal_cusp_density(edge-.001)
        self.assertAlmostEqual(ratio, 2**1.5, delta=.04)
        # Source factor in CG7/CO1. This float check is NOT the matching proof.
        self.assertAlmostEqual(principal_cusp_prefactor(), 13.76716822455, delta=1e-8)


class CompleteMinimizerClassificationTest(unittest.TestCase):
    def test_sub_pi_center_action_regression(self):
        for length in (.3, 1.2, 2.8):
            for target in (-.2, .01, .3):
                self.assertAlmostEqual(physical_circle_action(length, 0, target),
                                       physical_segment_action(length, target), delta=2e-12)

    def test_small_positive_u_length_rotation_does_not_lose_energy_root(self):
        length, p, q = 1e-5, .2, 1.1
        leading = (q-p)**2/(2*length)
        action = physical_circle_action(length, p, q)
        self.assertLessEqual(action, leading+1e-8)
        self.assertGreaterEqual(action, leading-length/8-1e-8)
        seam = rotating_cut_data(length)
        self.assertAlmostEqual(seam['action']/(math.pi**2/(8*length)), 1, delta=1e-10)

    def test_center_and_wall_equilibria(self):
        for length in (.5, 2.8, math.pi, 3.6, 4.5):
            self.assertAlmostEqual(physical_circle_action(length, math.pi/4, math.pi/4), -length/8)
            expected = 0 if length <= math.pi else internal_cut_data(length)['action']
            self.assertAlmostEqual(physical_circle_action(length, 0, 0), expected)
            if length > math.pi:
                self.assertLess(expected, 0)

    def test_global_symmetries_and_straight_competitor(self):
        for length in (.4, 2.7, 3.5, 4.4):
            for p, q in ((.2, -.1), (.65, -.6), (.9, .2), (.3, .3), (.1, 1.4)):
                action = physical_circle_action(length, p, q)
                for source, target in ((q, p), (-p, -q), (p+math.pi, q),
                                       (p+math.pi/2, q+math.pi/2)):
                    self.assertAlmostEqual(action, physical_circle_action(length, source, target), delta=2e-11)
                delta = (q-p+math.pi/2) % math.pi-math.pi/2
                straight = delta*delta/(2*length)-.5*quad(
                    lambda t: .25*math.sin(2*(p+t*delta/length))**2, 0, length)[0]
                self.assertLessEqual(action, straight+2e-12)
                self.assertGreaterEqual(action, -length/8-2e-12)

    def test_global_minimum_below_independent_stationary_competitors(self):
        for p in (-.3, .2, .7, .9):
            for velocity in (-.6, -.2, 0., .2, .6):
                solution = trace(p, velocity, 3.4)
                target, _, competitor = solution.y[:, -1]
                minimum = physical_circle_action(3.4, p, target)
                self.assertLessEqual(minimum, competitor+3e-11)

    def test_reflection_and_rotation_seams_are_transverse(self):
        p, length, step = .1, 3.4, 1e-6
        internal = internal_cut_data(length)
        self.assertLess(p, internal['source_radius'])
        for q, data in ((-p, internal), (p+math.pi/2, rotating_cut_data(length))):
            center = physical_circle_action(length, p, q)
            self.assertAlmostEqual(center, data['action'], delta=2e-12)
            left = (center-physical_circle_action(length, p, q-step))/step
            right = (physical_circle_action(length, p, q+step)-center)/step
            speed = math.sqrt(2*data['energy']-.25*math.sin(2*q)**2)
            self.assertAlmostEqual(left, speed, delta=2e-5)
            self.assertAlmostEqual(right, -speed, delta=2e-5)

    def test_all_ordinary_closing_contacts_stay_long(self):
        from scipy.optimize import brentq
        edge = cusp_source_data(cusp_source_window())
        self.assertAlmostEqual(internal_cut_data(edge.length)['null_time'], DURATION, delta=2e-13)
        minimum_length = ellipk(.25)
        self.assertAlmostEqual(rotating_cut_data(minimum_length)['null_time'], ellipe(.25), delta=2e-13)
        closing = [brentq(lambda l: rotating_cut_data(l)['null_time']-DURATION, .4, minimum_length),
                   brentq(lambda l: rotating_cut_data(l)['null_time']-DURATION, minimum_length, 8*DURATION/3)]
        self.assertTrue(closing[0] < minimum_length < closing[1])
        for length in closing:
            data = rotating_cut_data(length)
            self.assertGreater(abs(.5-data['energy']), .01)
        # Same fixed cutoff; every focal pair is long. Point term remains short.
        for p in (0, .2, .3):
            data = cusp_source_data(p)
            self.assertEqual(physical_time_weight(data.length, data.action, .2, short=True), 0)
            self.assertEqual(physical_time_weight(data.length, data.action, .2),
                             physical_time_weight(data.length, data.action))

    def test_input_guards(self):
        for call in (lambda: cusp_source_data(math.pi/4), lambda: cusp_time(1),
                     lambda: cusp_time(float('nan')), lambda: internal_cut_data(2),
                     lambda: rotating_cut_data(0), lambda: physical_circle_action(0, 0, 0),
                     lambda: physical_circle_action(5, 0, 0)):
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
