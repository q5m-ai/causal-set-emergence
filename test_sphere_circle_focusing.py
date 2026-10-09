"""Independent finite evidence for the written #139 cut-density producer."""

import unittest

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

from general_metric_gate import antipodal_coefficient, antipodal_scaled_volume, gauss_rule
from sphere_circle_focusing import (
    PAIR_FACTOR, area_ratio, averaged_coefficients, check_focusing_identities,
    circle_section, cut_primitive, interval_volume, inverse_excess,
    polar_volume, primitive_coefficients, regular_leading, regular_phase,
    regular_phase_jet, sphere_measure, time_weight, transition_profile,
    transition_sector_coefficient, volume_derivative,
)
from two_face_diagnostics import bdg_kernel as kernel


class SphereCircleFocusingTests(unittest.TestCase):
    def test_symbolic_inverse_and_real_signed_moments(self):
        check_focusing_identities()
        for power in (0, 1, 2):
            moment = quad(lambda z: z**power*kernel(z*z), 0, 10, epsabs=1e-12)[0]
            self.assertAlmostEqual(moment, 0, places=12)
        self.assertAlmostEqual(quad(lambda v: v*kernel(v), 0, 80)[0], -1, places=12)
        # The dominating kernel derivative in the primitive proof is integrable.
        derivative = lambda v: (-10+25*v-12*v*v+4*v**3/3)*np.exp(-v)
        bound = quad(lambda z: z**4*abs(derivative(z*z)), 0, 10)[0]
        self.assertTrue(0 < bound < 20)

    def test_both_sphere_sheets_have_full_area(self):
        for theta in (0.9, 2.5, np.pi-0.05):
            actual = sphere_measure(theta)
            self.assertAlmostEqual(actual, 4*np.pi, places=8)
            self.assertGreater(abs(actual/2-4*np.pi), 6)
        # The Euclidean focal endpoint has ratio one, not an extra sheet factor.
        for theta in (1, np.pi-0.01):
            self.assertAlmostEqual(area_ratio(theta, 0, theta), 1)

    def test_circle_section_against_original_positive_part(self):
        for tau, b, r, ss in ((3.5, 0.7, 1.3, 1.8), (3.9, -1.5, 1, 1.9)):
            value = circle_section(tau, b, r, ss, order=48)
            # Untransformed circle representative interval; positive part is
            # zero at and outside the actual ellipse roots, including seams.
            gap = lambda z: tau-np.hypot(r, z)-np.hypot(ss, z-b)
            minimum_location = b*r/(r+ss)
            roots = [brentq(gap, -10, minimum_location),
                     brentq(gap, minimum_location, 10)]
            original = quad(lambda z: max(0, gap(z)), -10, 10,
                            epsabs=1e-11, epsrel=1e-11, points=roots, limit=400)[0]
            self.assertAlmostEqual(value, original, places=8)
            u = np.sqrt(tau*tau-b*b)
            self.assertAlmostEqual(value, circle_section(u, 0, r, ss, order=48), places=10)

    def test_polar_and_two_distance_volumes_across_transition(self):
        a = 0.16
        theta = np.pi-a
        for S in (-0.6, 0, 0.9, 1, 1.1, 2):
            u = np.pi+a*S
            actual = interval_volume(u, theta, order=56, circle_order=40)
            fine = interval_volume(u, theta, order=80, circle_order=48)
            independent = polar_volume(u, theta, order=88, circle_order=48)
            self.assertLess(abs(actual/fine-1), 2e-7)
            self.assertLess(abs(independent/fine-1), 5e-7)
            self.assertGreater(actual, 0)
        with self.assertRaises(ValueError):
            regular_phase(theta, 2*a+1e-12)

    def test_nonzero_transverse_circle_separation_is_not_dropped(self):
        theta, u, b = np.pi-0.12, np.pi+0.04, 1.8
        tau = np.sqrt(u*u+b*b)
        original = polar_volume(tau, theta, b=b, order=80, circle_order=48)
        lifted = interval_volume(u, theta, order=72, circle_order=48)
        self.assertLess(abs(original/lifted-1), 5e-7)
        self.assertGreater(abs(interval_volume(tau, theta)/lifted-1), 5)

    def test_antipodal_three_halves_and_circle_time_coefficient(self):
        D = antipodal_coefficient()
        previous = 1.0
        for e in (0.02, 0.005, 0.00125):
            scaled = interval_volume(np.pi+e, np.pi, order=160, circle_order=48)/e**1.5
            self.assertAlmostEqual(scaled, antipodal_scaled_volume(e, order=160), places=7)
            error = abs(scaled/D-1)
            self.assertLess(error, previous)
            previous = error
        b, e = 1.6, 0.001
        arrival = np.hypot(np.pi, b)
        u = np.sqrt((arrival+e)**2-b*b)
        coefficient = interval_volume(u, np.pi, order=160, circle_order=48)/e**1.5
        self.assertLess(abs(coefficient/(D*(arrival/np.pi)**1.5)-1), 0.002)
        values = [interval_volume(np.pi+e, np.pi, order=128)/e**2 for e in (.01, .0025)]
        self.assertGreater(values[1]/values[0], 1.9)  # wrong eps^2 law diverges

    def test_actual_normal_form_and_first_derivative(self):
        for S in (-0.6, 0, 1, 1.4):
            errors = []
            for a in (.2, .05, .0125):
                actual = interval_volume(np.pi+a*S, np.pi-a, order=64)
                errors.append(abs(actual/a**1.5/transition_profile(S)-1))
            self.assertTrue(errors[2] < errors[1] < errors[0])
            self.assertLess(errors[-1], 0.003)
        a, S = 0.02, 1.0
        theta, u = np.pi-a, np.pi+a*S
        h = 1e-5
        derivative = volume_derivative(u, theta, order=96)
        difference = (interval_volume(u+h, theta, order=96)
                      - interval_volume(u-h, theta, order=96))/(2*h)
        self.assertLess(abs(derivative/difference-1), 2e-5)

    def test_opening_coefficient_and_secondary_log_not_regular(self):
        D = antipodal_coefficient()
        self.assertAlmostEqual(transition_profile(1), 8*np.sqrt(2)*D/(3*np.pi), places=10)
        self.assertLess(abs(transition_profile(-1+0.002)/0.002**2
                            / (3*np.sqrt(2)*D/16)-1), 0.001)
        def second(h):
            return 3*D/(4*np.pi)*quad(lambda phi: (1+h+np.cos(phi))**-0.5,
                                      0, np.pi, epsabs=1e-10)[0]
        log_slope = (second(1e-5)-second(1e-4))/np.log(0.1)
        self.assertLess(abs(log_slope/(-3*np.sqrt(2)*D/(8*np.pi))-1), 0.001)

    def test_exact_rest_diamond_and_derived_regular_jet(self):
        for a in (.3, .1, .03):
            theta = np.pi-a
            hs = regular_phase_jet(theta, order=36)
            self.assertLess(abs(hs[0]/regular_leading(theta)-1), 1e-8)
            e = a/50
            actual = interval_volume(theta+e, theta, order=64)/e**2
            fixed_domain = regular_phase(theta, e, order=36)
            self.assertLess(abs(actual/fixed_domain-1), 1e-7)
            coarse_error = abs(fixed_domain-hs@[1, e, e*e/2])
            fine_error = abs(regular_phase(theta, e/2, order=36)-hs@[1, e/2, e*e/8])
            self.assertGreater(coarse_error/fine_error, 7.8)
            # Check the actual cut-scale derivative bounds, not only a metric jet.
            scaled = np.sqrt(a)*hs*np.array([1, a, a*a])
            self.assertTrue(np.all(np.abs(scaled) < 10))
        a = .003
        self.assertLess(abs(np.sqrt(a)*regular_leading(np.pi-a)
                            / (3*np.sqrt(2)*antipodal_coefficient()/16)-1), 0.001)

    def test_inverse_and_primitive_control_on_both_branches(self):
        for a in (.12, .025, .005):
            coefficients = primitive_coefficients(a)
            self.assertTrue(np.all(np.abs(coefficients)*a**np.array([-.25, .5, 1.25]) < 8))
            for ratio in (.15, 1.9, 2.1, 3):
                e = ratio*a
                if e >= .2:
                    continue
                theta = np.pi-a
                w = np.sqrt(interval_volume(theta+e, theta, order=48))
                actual_e = inverse_excess(a, w, order=48)
                self.assertAlmostEqual(actual_e, e, places=10)
                f = quad(lambda t: time_weight(theta+t), 0, actual_e)[0]
                jet = coefficients@[w, w*w, w**3]
                dominated = abs(np.sin(a)*(f-jet)/w**3)*a**.25
                self.assertLess(dominated, 2)

    def test_actual_endpoint_averaged_primitive_not_a_fibre_model(self):
        coefficients = averaged_coefficients(order=40, diamond_order=32)
        refined = averaged_coefficients(order=48, diamond_order=36)
        np.testing.assert_allclose(coefficients, refined, rtol=2e-6, atol=1e-7)
        self.assertGreater(coefficients[0], 10)
        self.assertLess(coefficients[1], -3)
        for w in (.04, .02):
            actual = cut_primitive(w, order=32, volume_order=56)
            other = cut_primitive(w, order=24, volume_order=40)
            self.assertLess(abs(actual-other)/w**3, .003)
            self.assertLess(abs(actual-coefficients@[w, w*w, w**3])/w**3, .012)
            # Keeping only an antipodal fibre would have the wrong measure/power.
            self.assertLess(abs(actual/w-coefficients[0]), .15)

    def test_time_weights_include_both_contacts_and_fixed_cutoff(self):
        delta = 3.0
        for u in (.7, 2.8, 3.0, np.pi, 3.8):
            end = np.sqrt(16-u*u)
            original = 2*quad(lambda b: (4-np.hypot(u, b))*u/np.hypot(u, b), 0, end)[0]
            self.assertAlmostEqual(time_weight(u), original, places=11)
            lower = np.sqrt(delta*delta-u*u) if u < delta else 0
            long = 2*quad(lambda b: (4-np.hypot(u, b))*u/np.hypot(u, b), lower, end)[0]
            self.assertAlmostEqual(time_weight(u, delta), long, places=11)
            self.assertAlmostEqual(time_weight(u, delta)+time_weight(u, delta, short=True),
                                   original, places=11)
        self.assertGreater(time_weight(np.pi), 2)
        with self.assertRaises(ValueError):
            time_weight(2, short=True)

    def test_full_circle_time_pair_reduction_with_actual_phase(self):
        theta, rho = 2.9, 0.6
        nodes, weights = gauss_rule(44)
        original = 0.0
        for t, wt in zip(nodes, weights):
            tau = theta+(4-theta)*t
            bmax = np.sqrt(tau*tau-theta*theta)
            for z, wz in zip(nodes, weights):
                b = bmax*z
                u = np.sqrt(tau*tau-b*b)
                original += ((4-theta)*wt*2*bmax*wz*(4-tau)
                             * kernel(rho*interval_volume(u, theta, order=28)))
        reduced = quad(lambda u: time_weight(u)*kernel(rho*interval_volume(u, theta, order=36)),
                       theta, 4, points=[2*np.pi-theta], epsabs=2e-6)[0]
        self.assertLess(abs(original-reduced), 1e-5)

    def test_exact_complement_domains_and_point_normalization(self):
        # Independently integrate a nonconstant probe against the exact measures.
        # F20 is an identity for every integrable phase function, not only K.
        delta, a0, e0 = 1.3, .17, .09
        probe = lambda theta, u: 1+theta*u+np.sin(theta+2*u)
        inner = lambda theta, lo, hi, weight: quad(
            lambda u: weight(u)*probe(theta, u), lo, hi, epsabs=1e-10)[0]
        total = quad(lambda theta: np.sin(theta)*inner(theta, theta, 4, time_weight),
                     0, np.pi, epsabs=1e-9)[0]
        short = quad(lambda theta: np.sin(theta)*inner(
            theta, theta, delta, lambda u: time_weight(u, delta, short=True)),
                     0, delta, epsabs=1e-9)[0]
        # Split the remaining u integral at delta: its contact is not deleted.
        def long_inner(theta):
            ranges = [theta, delta, 4] if theta < delta else [theta, 4]
            return sum(inner(theta, lo, hi, lambda u: time_weight(u, delta))
                       for lo, hi in zip(ranges, ranges[1:]))
        offcut = quad(lambda theta: np.sin(theta)*long_inner(theta),
                     0, np.pi-a0, points=[delta], epsabs=1e-9)[0]
        cut = quad(lambda theta: np.sin(theta)*inner(theta, theta, theta+e0, time_weight),
                   np.pi-a0, np.pi, epsabs=1e-10)[0]
        excess = quad(lambda theta: np.sin(theta)*inner(theta, theta+e0, 4, time_weight),
                      np.pi-a0, np.pi, epsabs=1e-10)[0]
        self.assertAlmostEqual(total, short+offcut+cut+excess, places=8)
        self.assertGreater(offcut, cut)
        self.assertGreater(excess, 0)
        self.assertAlmostEqual(PAIR_FACTOR, (4*np.pi*20)*2*np.pi)
        self.assertAlmostEqual(4*(4*np.pi*20), 320*np.pi)

    def test_transition_sector_signed_response_decays_not_counterexample(self):
        coefficient = transition_sector_coefficient(-.4, 1.4)
        self.assertGreater(coefficient, 0)
        # Integrate the complete leading primitive, including its negative tail.
        for rho in (4, 16):
            scaled = quad(lambda z: 2*coefficient*z*kernel(z), 0, 80)[0]/np.sqrt(rho)
            self.assertAlmostEqual(scaled/(-2*coefficient/np.sqrt(rho)), 1, places=12)
        with self.assertRaises(ValueError):
            transition_sector_coefficient(-1, 1.4)


if __name__ == "__main__":
    unittest.main()
