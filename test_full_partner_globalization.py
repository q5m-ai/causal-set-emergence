"""Finite controls for #151's partial proof; no universal estimate is tested."""

import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

from dimension_kernels import (
    Z, action_constants, interval_coefficient, kernel_polynomial, sphere_area,
)
from full_partner_globalization import (
    angular_cosine, periodic_correlation, primitive_response,
    torus_long_density, torus_long_pair_phase, torus_long_pair_radial,
)
from general_metric_gate import gauss_rule, torus_distance
from sphere_circle_focusing import interval_volume, time_weight


class FullPartnerGlobalizationTests(unittest.TestCase):
    def test_actual_phase_density_matches_original_pairs_across_dimensions(self):
        for d in (2, 3, 4, 5, 6, 9):
            with self.subTest(d=d):
                correlation = lambda tau, r: periodic_correlation(
                    d, 1., .4, tau, r, .7, -.4, 1.4, -.8)
                rho = 7 / (float(interval_coefficient(d)) * .4**d)
                original = torus_long_pair_radial(d, 1., .4, .11, rho, correlation)
                phase = torus_long_pair_phase(d, 1., .4, .11, rho, correlation)
                self.assertAlmostEqual(original, phase, delta=3e-11)

    def test_periodic_both_endpoint_average_against_direct_source_time_integral(self):
        # d=2: integrate BOTH S^0 directions, source circle, and source time.
        L, T, tau, r = 1., .4, .25, .19
        nodes, weights = gauss_rule(12)
        p = np.arange(32) * L / 32
        t = -T/2 + (T-tau)*nodes[:, None]
        actual = 0.
        for direction in (-1, 1):
            target = (p + direction*r) % L
            chi = 1 + .7*t + 1.4*np.cos(2*np.pi*p/L)
            phi = 1 - .4*(t+tau) - .8*np.cos(2*np.pi*target/L)
            actual += np.sum(weights[:, None]*chi*phi) / len(p) / 2
        expected = periodic_correlation(2, L, T, tau, r, .7, -.4, 1.4, -.8)
        self.assertAlmostEqual(actual, expected, places=13)
        frozen = periodic_correlation(2, L, T, tau, 0, .7, -.4, 1.4, -.8)
        self.assertGreater(abs(actual-frozen), .2)

    def test_two_direction_and_nonunit_volume_normalization(self):
        # K(0)=1: independent integration of the entire long pair mass in 2D.
        L, T, delta = 2., .7, .2
        density_mass = quad(lambda w: torus_long_density(2, L, T, delta, w),
                            0, T*T, points=[delta*delta], epsabs=1e-11)[0]
        expected = 2*L*quad(lambda tau: (T-tau)*tau, delta, T)[0]
        self.assertAlmostEqual(density_mass, expected, places=11)
        self.assertGreater(abs(density_mass-expected/2), .05)
        # Sphere averaging is a mean; the separate ordinary sphere mass stays.
        for z in (0., .3, 1.7):
            self.assertAlmostEqual(angular_cosine(2, z), np.cos(z), places=13)
            self.assertAlmostEqual(angular_cosine(4, z), np.sinc(z/np.pi), places=13)

    def test_actual_near_zero_density_taylor_coefficients(self):
        # Coefficients derive from differentiating (tau^2-w)^((d-3)/2).
        # Compare with the unsubtracted actual G8 density, not a fitted jet.
        T, delta = .4, .15
        for d in (2, 4, 5, 6, 9):
            n = d//2
            coefficients = [float(s.binomial(s.Rational(d-3, 2), j)) * (-1)**j
                            * float(sphere_area(d))/2 * quad(
                                lambda tau: (T-tau)*tau**(d-3-2*j), delta, T)[0]
                            for j in range(n+1)]
            next_coefficient = abs(float(s.binomial(s.Rational(d-3, 2), n+1))) \
                * float(sphere_area(d))/2 * quad(
                    lambda tau: (T-tau)*tau**(d-3-2*(n+1)), delta, T)[0]
            for w in (delta**2/100, delta**2/200):
                jet = sum(coefficient*w**j for j, coefficient in enumerate(coefficients))
                actual = torus_long_density(d, 1., T, delta, w)
                # Taylor's derivative bound on 0 <= w/tau^2 <= w/delta^2.
                bound = next_coefficient*w**(n+1) * max(
                    1., (1-w/delta**2)**((d-3)/2-n-1))
                self.assertLessEqual(abs(actual-jet), bound*(1+1e-8)+2e-12)
            self.assertAlmostEqual(torus_long_density(d, 1., T, delta, 0),
                                   coefficients[0], places=12)

    def test_all_ordered_partition_pairs_including_signed_fields(self):
        d, L, T, delta, rho = 4, 1., .4, .12, 1.
        # Each pair is the actual spatial/angular correlation of two periodic
        # partitions. The first source weight changes sign; labels may overlap.
        source = ((.3, 1.4), (.7, -1.4))
        target = ((.6, .35), (.4, -.35))
        cells = np.zeros((2, 2))
        for i, (a, alpha) in enumerate(source):
            for j, (b, beta) in enumerate(target):
                correlation = lambda tau, r: a*b + alpha*beta/2*angular_cosine(
                    d, 2*np.pi*r/L)
                cells[i, j] = torus_long_pair_radial(d, L, T, delta, rho, correlation)
        full = torus_long_pair_radial(d, L, T, delta, rho)
        self.assertAlmostEqual(cells.sum(), full, places=13)
        self.assertGreater(abs(full-np.trace(cells)), .05*full)
        point_cells = np.array([[a*b + alpha*beta/2 for b, beta in target]
                                for a, alpha in source]) * L**(d-1)*T
        self.assertAlmostEqual(point_cells.sum(), L**(d-1)*T, places=13)
        self.assertNotAlmostEqual(np.trace(point_cells), L**(d-1)*T)
        self.assertTrue(np.any(point_cells < 0))

    def test_temporal_and_radial_cutoff_exact_signed_overlap(self):
        T, delta, rho = .4, .21, 80.
        c = float(interval_coefficient(4))
        beta = float(action_constants(4)[1])
        kernel = s.lambdify(Z, kernel_polynomial(4)*s.exp(-Z), "numpy")
        pair = lambda tau, r: 4*np.pi*(T-tau)*r*r*kernel(c*rho*(tau*tau-r*r)**2)
        temporal_short = quad(lambda tau: quad(lambda r: pair(tau, r),
                                               0, tau)[0], 0, delta)[0]
        radial_short = quad(lambda tau: quad(lambda r: pair(tau, r),
                                             0, min(tau, delta-tau))[0],
                            0, delta, points=[delta/2])[0]
        shell = quad(lambda tau: quad(lambda r: pair(tau, r),
                                      delta-tau, tau)[0], delta/2, delta)[0]
        self.assertAlmostEqual(temporal_short-radial_short, shell, places=12)
        full_long = torus_long_pair_radial(4, 1., T, delta, rho)
        radial_long = full_long + shell
        signed_short_difference = -beta*rho**1.5*(temporal_short-radial_short)
        signed_long_difference = -beta*rho**1.5*(full_long-radial_long)
        self.assertAlmostEqual(signed_short_difference+signed_long_difference, 0, places=11)
        self.assertGreater(abs(signed_short_difference), .01)

    def test_seam_partners_and_equality_long_not_measure_zero_shortcuts(self):
        # Deliberately an atomic diagnostic of masks, NOT a continuum quadrature.
        gaps = np.array([.05, .1, .2])
        delta = .1
        short, long = gaps < delta, gaps >= delta
        np.testing.assert_array_equal(short+long, np.ones(3, dtype=int))
        self.assertFalse(short[1])
        self.assertTrue(long[1])
        self.assertAlmostEqual(torus_distance([.98], [.02], 1.), .04)
        self.assertGreater(abs(.98-.02), gaps[0])  # Chart clipping loses this pair.
        pair_values = np.array([.7, -.3, 1.2])
        point, normalization = 2.3, 1.7
        S = point-normalization*np.dot(short, pair_values)
        L = -normalization*np.dot(long, pair_values)
        self.assertAlmostEqual(S+L, point-normalization*sum(pair_values))
        self.assertNotAlmostEqual(S-L, S+L)

    def test_primitive_moments_and_log_responses_use_actual_kernel(self):
        rho = s.Rational(7, 3)
        for d in (2, 3, 4, 5, 6, 10, 11):
            for r in range(1, d//2+2):
                self.assertEqual(primitive_response(d, r, rho), 0)
            exponent = s.Rational(d, 2)+1
            pure = primitive_response(d, exponent, rho)
            if d % 2:
                self.assertNotEqual(pure, 0)
            else:
                self.assertEqual(pure, 0)
        for d in (3, 4, 6):
            r = s.Symbol("r", positive=True)
            critical = s.Rational(d, 2)+1
            response = primitive_response(d, r, rho)
            signed_log = float(s.diff(response, r).subs(r, critical))
            c = float(interval_coefficient(d))
            beta = float(action_constants(d)[1])
            kernel = s.lambdify(Z, kernel_polynomial(d)*s.exp(-Z), "numpy")
            q, exponent = d/2, float(critical)
            # w=(c*rho)^(-1/q)*z; differentiate w^r log(w) before integration.
            scale = (c*float(rho))**(-1/q)
            integral = quad(lambda z: z**(exponent-1) * (
                exponent*np.log(scale*z)+1)*kernel(z**q), 0, np.inf,
                epsabs=2e-10, epsrel=2e-11)[0]
            direct = -beta*float(rho)**(1+1/q)*scale**exponent*integral
            self.assertAlmostEqual(signed_log, direct, delta=2e-8)
            if d % 2 == 0:
                self.assertGreater(abs(direct), .1)

    def test_actual_stieltjes_identity_without_a_density_or_jet(self):
        # A signed atomic phase measure has no smooth density. G6 is still an
        # identity, not a regularity claim. Keep arbitrary polynomial subtraction.
        phases, masses = np.array([.04, .11, .3]), np.array([1., -.7, .2])
        rho = 13.
        for d in (2, 3, 4, 5, 7):
            q, n = d/2, d//2
            c, beta = float(interval_coefficient(d)), float(action_constants(d)[1])
            K = kernel_polynomial(d)*s.exp(-Z)
            kernel = s.lambdify(Z, K, "numpy")
            derivative = s.lambdify(Z, s.diff(K, Z), "numpy")
            direct = -beta*rho**(1+1/q)*np.dot(masses, kernel(c*rho*phases**q))
            scale = (c*rho)**(-1/q)
            coefficients = [(-1)**j/(j+2) for j in range(n+1)]

            def integrand(z):
                w = scale*z
                primitive = np.sum(masses[phases <= w])
                polynomial = sum(b*w**(j+1) for j, b in enumerate(coefficients))
                remainder = (primitive-polynomial)/w**(q+1)
                return z**(2*q)*derivative(z**q)*remainder

            edges = [0., *(phases/scale), np.inf]
            response = beta*q*c**(-1-1/q)*sum(quad(
                integrand, lo, hi, epsabs=1e-12, epsrel=1e-12)[0]
                for lo, hi in zip(edges, edges[1:]))
            self.assertAlmostEqual(direct, response, delta=3e-8)

    def test_focusing_phase_sign_and_temporal_long_conversion(self):
        # Reuse accepted actual two-sheet volume, not a regular-null substitute.
        theta, e, delta = np.pi-.08, .2, .5
        u = theta+e  # Beyond the secondary transition e=2*a.
        V = interval_volume(u, theta, order=48)
        c = float(interval_coefficient(4))
        wF, wG = np.sqrt(V), np.sqrt(V/c)
        self.assertAlmostEqual(c*wG*wG, wF*wF, places=13)
        self.assertEqual(time_weight(u, cutoff=delta, short=True), 0.)
        self.assertAlmostEqual(time_weight(u, cutoff=delta), time_weight(u))
        rho = .7/V  # Choose a genuinely negative part of the signed kernel.
        kernel = s.lambdify(Z, kernel_polynomial(4)*s.exp(-Z), "numpy")
        pair = kernel(rho*V)
        self.assertLess(pair, 0)
        self.assertGreater(-float(action_constants(4)[1])*rho**1.5*pair, 0)
        self.assertAlmostEqual(pair, kernel(c*rho*wG*wG), places=13)

    def test_no_thick_torus_or_invalid_dimension_fallback(self):
        for args in ((4, 1., .5, .1), (4, 1., .6, .1),
                     (4, 1., .4, 0.), (1, 1., .4, .1),
                     (True, 1., .4, .1), (3.5, 1., .4, .1)):
            with self.assertRaises(ValueError):
                torus_long_density(*args, .01)
        self.assertEqual(torus_long_density(2, 1., .4, .4, 0), 0)
        self.assertEqual(torus_long_pair_radial(4, 1., .4, .5, 10), 0)
        for exponent in (0, -1):
            with self.assertRaises(ValueError):
                primitive_response(4, exponent, 1)
        with self.assertRaises(ValueError):
            torus_long_pair_phase(4, 1., .4, .1, 0)


if __name__ == "__main__":
    unittest.main()
