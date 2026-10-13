"""Finite identities/negative controls, not proofs of the continuum theorem."""

from fractions import Fraction as F
import unittest

import numpy as np
import sympy as sp

import curved4_corrected_convergence as cc
from general_metric_gate import gauss_rule
from sphere_circle_complements import phase_factor, time_radius
from sphere_circle_focusing import interval_volume, regular_phase, time_weight


def one(t, z):
    return np.ones(np.broadcast_shapes(np.shape(t), np.shape(z)))


def omega(t, z):
    return 1+0.025*t+0.06*np.sin(np.pi*z/10)


def density(t, z):
    return omega(t, z)**4


class CorrectedCurved4Tests(unittest.TestCase):
    def test_full_diamond_measure_and_moments(self):
        a, b1, b2, b3, w = cc.diamond_rule(12)
        c = np.pi/24
        self.assertAlmostEqual(np.sum(w), c, places=13)
        self.assertAlmostEqual(np.sum(w*a*a)/c, 1/60, places=13)
        for b in (b1, b2, b3):
            self.assertAlmostEqual(np.sum(w*b*b)/c, 1/30, places=11)
            self.assertAlmostEqual(np.sum(w*b), 0, places=14)
        self.assertFalse(w.flags.writeable)

    def test_unweighted_full_boost_recovers_old_phase(self):
        for theta, b, q in ((0.0, 1.4, 0.13), (1.1, 0.7, 0.12),
                            (1.1, -0.7, 0.12), (2.7, 0.9, 0.06)):
            actual = cc.regular_volume_factor(-1.8, 19.8, theta, b, q, one, 16)
            expected = np.pi/24*phase_factor(theta*theta, q, 20)
            self.assertAlmostEqual(actual/expected, 1, delta=2e-7)

    def test_weighted_fixed_diamond_against_physical_clock(self):
        # Independent sphere polar integration, resolved circle roots and clocks.
        for theta, b, q in ((1.1, 0.7, 0.24), (2.3, -0.8, 0.3),
                            (0.0, 1.1, 0.35)):
            tau = np.sqrt(theta*theta+b*b+q)
            fixed = q*q*cc.regular_volume_factor(-1.7, 19.7, theta, b, q, density, 16)
            clock = cc.weighted_clock_volume(-1.7, 19.7, tau, theta, b, density,
                                             order=56, circle_order=28)
            self.assertAlmostEqual(fixed/clock, 1, delta=4e-5)

    def test_no_frozen_source_density_substitution(self):
        theta, b, q, ts, zs = 1.1, 0.8, 0.2, -1.5, 0.8
        actual = cc.regular_volume_factor(ts, zs, theta, b, q, density, 14)
        frozen = density(ts, zs)*cc.regular_volume_factor(ts, zs, theta, b, q, one, 14)
        self.assertGreater(abs(actual/frozen-1), 0.05)

    def test_circle_seam_and_periodic_density(self):
        args = (3.45, 3.0, 0.8)
        a = cc.weighted_clock_volume(-1.7, 19.7, *args, density, order=28)
        b = cc.weighted_clock_volume(-1.7, -0.3, *args, density, order=28)
        self.assertAlmostEqual(a, b, places=12)
        h1 = cc.regular_volume_factor(-1.7, 19.7, 1.1, 0.8, 0.1, density)
        h2 = cc.regular_volume_factor(-1.7, -0.3, 1.1, 0.8, 0.1, density)
        self.assertAlmostEqual(h1, h2, places=13)

    def test_physical_transition_both_sides_and_antipode(self):
        # Small positive conformal weights bound the whole physical interval,
        # including the opening second arc; the regular formula is NOT used.
        for theta, u in ((3.0, 3.25), (3.0, 2*np.pi-3.0), (3.0, 3.4),
                         (np.pi, 3.45)):
            actual = cc.weighted_clock_volume(-1.8, 3.0, u, theta, 0, density,
                                               order=64, circle_order=28)
            base = interval_volume(u, theta, order=72, circle_order=32)
            self.assertGreater(actual, 0.89**4*base)
            self.assertLess(actual, 1.11**4*base)
        with self.assertRaises(ValueError):
            cc.regular_volume_factor(-1.8, 0, 3.0, 0, 3.4**2-9, density)

    def test_null_and_empty_clock_fibres(self):
        self.assertEqual(cc.weighted_clock_volume(-1.8, 0, np.pi, np.pi, 0, density), 0)
        self.assertEqual(cc.weighted_clock_volume(-1.8, 0, 3.0, np.pi, 0, density), 0)

    def test_closing_change_recovers_complete_time_weight(self):
        n, w = gauss_rule(40)
        for u in (2.9, np.pi, 3.6):
            integral = 2*sum(wi*cc.closing_pair(2.9, u-2.9, 2*v-1, 0.37, 0, one).amplitude
                             for v, wi in zip(n, w))
            self.assertAlmostEqual(integral/time_weight(u), 1, places=12)

    def test_closing_retains_times_and_exact_zero(self):
        for v in (-1, 1):
            p = cc.closing_pair(3.0, 0.1, v, 0.8, 19.7, density)
            self.assertEqual(p.amplitude, 0)
            self.assertAlmostEqual(p.source_time, -2)
            self.assertAlmostEqual(p.target_time, 2)
        for v in (-0.999, 0.3, 0.999):
            p = cc.closing_pair(3.0, 0.1, v, 0.8, 19.7, density)
            self.assertGreater(p.amplitude, 0)
            self.assertGreaterEqual(p.source_time, -2)
            self.assertLessEqual(p.target_time, 2)
            self.assertAlmostEqual(p.tau*p.tau-p.b*p.b, p.u*p.u)

    def test_both_endpoint_measures_not_one(self):
        c = 1.3
        constant = lambda t, z: c**4*one(t, z)
        p0 = cc.closing_pair(3.0, 0.04, 0.6, 0.4, 0, one)
        p1 = cc.closing_pair(3.0, 0.04, 0.6, 0.4, 0, constant)
        self.assertAlmostEqual(p1.amplitude/p0.amplitude, c**8)
        h0 = cc.cut_volume_factor(0.15, 0.01, 0.6, 0.4, 0, one, 14)
        h1 = cc.cut_volume_factor(0.15, 0.01, 0.6, 0.4, 0, constant, 14)
        self.assertAlmostEqual(h1/h0, c**4)
        self.assertGreater(abs(c**8-c**4), 1)

    def test_cut_zero_and_regular_wedge(self):
        for a, e in ((0.2, 0.0), (0.15, 0.02), (0.08, 0.005)):
            actual = cc.cut_volume_factor(a, e, 0.5, 0.3, 0, one, 18)
            reference = regular_phase(np.pi-a, e, 24)
            self.assertAlmostEqual(actual/reference, 1, delta=3e-6)

    def test_cut_rescaled_bounds_are_finite_diagnostics(self):
        values = []
        for a in (0.2, 0.1, 0.05):
            for ratio in (0, 0.02, 0.1):
                h = cc.cut_volume_factor(a, ratio*a, -0.7, 0.3, 3, density, 14)
                values.append(np.sqrt(a)*h)
        self.assertGreater(min(values), 0.5)
        self.assertLess(max(values), 20)
        # This finite range is explicitly NOT a proof of the uniform bounds.

    def test_moving_closing_data_are_not_frozen(self):
        p0 = cc.closing_pair(3.0, 0, 0.7, 0.8, 19.7, density)
        p1 = cc.closing_pair(3.0, 0.08, 0.7, 0.8, 19.7, density)
        self.assertLess(abs(p1.b), abs(p0.b))
        self.assertLess(p1.source_time, p0.source_time)
        self.assertGreater(p1.target_time, p0.target_time)
        self.assertGreater(abs(p1.amplitude/p0.amplitude-1), 0.02)

    def test_both_signed_circle_directions_remain(self):
        hplus = cc.cut_volume_factor(0.2, 0.02, 0.7, 0.5, 0, density, 14)
        hminus = cc.cut_volume_factor(0.2, 0.02, -0.7, 0.5, 0, density, 14)
        self.assertGreater(abs(hplus/hminus-1), 0.05)

    def test_actual_two_time_roots_and_circle_axis(self):
        for duration, m, w in ((0.2, 0.7, 0.0003), (4.0, 0.9, 0.003),
                               (4.0, -1.0, 0.003)):
            radius = cc.time_contact_radius(duration, m, 0.4, 19.5, w, density, 12)
            q = duration*duration-radius*radius
            factor = cc.regular_volume_factor(-2+0.4*(4-duration), 19.5,
                radius*np.sqrt(1-m*m), radius*m, q, density, 12)
            self.assertAlmostEqual(q*np.sqrt(factor)/w, 1, delta=2e-11)
            self.assertLess(radius, duration)
            # Old v is sqrt(V/c); the new w is sqrt(V).
            unweighted = cc.time_contact_radius(duration, m, 0.4, 0, w, one, 14)
            old = time_radius(duration, m, w/np.sqrt(np.pi/24), order=18)
            self.assertAlmostEqual(unweighted, old, delta=3e-9)

    def test_actual_primitive_coefficient_algebra(self):
        w = sp.symbols('w')
        h0, h1, h2 = sp.Integer(4), sp.Integer(3), sp.Integer(2)
        a1 = 1/sp.sqrt(h0)
        a2 = -h1/(2*h0**2)
        a3 = 5*h1**2/(8*h0**sp.Rational(7, 2))-h2/(4*h0**sp.Rational(5, 2))
        e = a1*w+a2*w*w+a3*w**3
        self.assertEqual(sp.series(e**2*(h0+h1*e+h2*e*e/2)-w*w,
                                   w, 0, 5).removeO().expand(), 0)
        primitive = sp.series(2*e+3*e*e/2+5*e**3/6, w, 0, 4).removeO().expand()
        expected = np.array([float(primitive.coeff(w, j)) for j in (1, 2, 3)])
        np.testing.assert_allclose(cc.primitive_coefficients(4, 3, 2, 2, 3, 5), expected)

    def test_geometric_summability_distinguishes_the_two_foci(self):
        sphere = cc.critical_exponents(1, 1, F(1, 2))
        quartic = cc.critical_exponents(F(3, 2), 2, F(1, 2))
        self.assertTrue(sphere['summable'])
        self.assertEqual(sphere['cubic_majorant'], F(-1, 4))
        self.assertEqual(sphere['transition_volume_power'], 2)
        self.assertFalse(quartic['summable'])
        self.assertEqual(quartic['cubic_majorant'], F(-7, 4))
        self.assertEqual(quartic['transition_volume_power'], F(9, 7))
        # At equality the sufficient lemma makes no claim; nor does failure
        # establish an obstruction without the independently matched coefficient.
        self.assertFalse(cc.critical_exponents(F(1, 4), 1, F(1, 2))['summable'])
        self.assertFalse(cc.critical_exponents(0, 1, F(1, 2))['summable'])

    def test_canonical_moments_and_retained_quartic_mellin_factor(self):
        z = sp.symbols('z')
        multiplier = sp.prod(1-2*z/j for j in (1, 2, 3))
        for zero in (sp.Rational(1, 2), 1, sp.Rational(3, 2)):
            self.assertEqual(multiplier.subs(z, zero), 0)
        self.assertEqual(multiplier.subs(z, sp.Rational(9, 7)), sp.Rational(22, 343))

    def test_independent_constant_and_time_varying_targets(self):
        zero = lambda t, z: 0*one(t, z)
        for c in (1, 1.3):
            target = cc.independent_target(lambda t, z: c*one(t, z), zero, zero)
            self.assertAlmostEqual(target/(320*np.pi), c*c, places=12)
            mass = cc.spacetime_mass(lambda t, z: c**4*one(t, z))
            self.assertAlmostEqual(mass/(320*np.pi), c**4, places=12)
        eps = 1/16
        target = cc.independent_target(lambda t, z: 1+eps*t*t,
                                       lambda t, z: 2*eps, zero)
        self.assertAlmostEqual(target/np.pi, 1522/3, places=10)

    def test_independent_spatially_varying_target(self):
        k, eps = np.pi/10, 0.25
        om = lambda t, z: 1+eps*np.cos(k*z)
        zero = lambda t, z: 0*one(t, z)
        ozz = lambda t, z: -eps*k*k*np.cos(k*z)
        target = cc.independent_target(om, zero, ozz)
        expected = 320*np.pi*(1+eps**2*(1+3*k*k)/2)
        self.assertAlmostEqual(target/expected, 1, places=12)
        self.assertGreater(abs(target-320*np.pi), 30)

    def test_same_kernel_from_original_poisson_layers(self):
        v = 0.04*cc.regular_volume_factor(-1.6, 19.5, 1.2, 0.8, 0.2, density)
        for rho in (0.3, 5, 40):
            s = rho*v
            poisson_combination = sum(c*np.exp(-s)*s**j/sp.factorial(j)
                                      for j, c in enumerate((1, -9, 16, -8)))
            self.assertAlmostEqual(float(poisson_combination),
                                   (1-9*s+8*s*s-4*s**3/3)*np.exp(-s))

    def test_invalid_diagnostic_requests_fail(self):
        with self.assertRaises(ValueError):
            cc.cut_volume_factor(0.1, 0.2, 0, 0.5, 0, one)
        with self.assertRaises(ValueError):
            cc.closing_pair(3, 0, 1.1, 0.5, 0, one)
        with self.assertRaises(ValueError):
            cc.time_contact_radius(4, 0, 0.5, 0, 0.01, one)
        with self.assertRaises(ValueError):
            cc.time_contact_radius(0.2, 1, 0.5, 0, 1, one)
        with self.assertRaises(ValueError):
            cc.regular_volume_factor(-1, 0, 1, 0, 0.1, lambda t, z: -1)
        with self.assertRaises(ValueError):
            cc.critical_exponents(1, 1, 2)


if __name__ == '__main__':
    unittest.main()
