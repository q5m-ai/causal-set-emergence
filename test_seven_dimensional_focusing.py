"""Finite diagnostics, plus exact rational sign arithmetic, for #151's O3."""

from fractions import Fraction
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.optimize import brentq

from dimension_kernels import Z, action_constants, interval_coefficient, kernel_polynomial
from general_metric_gate import gauss_rule
from seven_dimensional_focusing import (
    ANTIPODAL_COEFFICIENT as D, OPENING_COEFFICIENT, PAIR_FACTOR, SPATIAL_VOLUME,
    boosted_flat_section, flat_section, interval_volume, matched_coefficient_quadrature,
    polar_volume, regular_phase, sign_certificate, time_weight, transition_profile,
)


class SevenDimensionalFocusingTests(unittest.TestCase):
    def test_exact_rational_sign_certificate_not_floating_acceptance(self):
        lower, upper = sign_certificate()
        self.assertIsInstance(lower, Fraction)
        self.assertIsInstance(upper, Fraction)
        self.assertLess(Fraction(1, 400), lower)
        self.assertLess(lower, upper)
        self.assertLess(upper, Fraction(13, 5000))
        self.assertLess(upper-lower, Fraction(1, 1_000_000))
        independent = matched_coefficient_quadrature()
        self.assertTrue(float(lower) < independent < float(upper))
        self.assertAlmostEqual(independent, .002559559862229218, delta=2e-10)

    def test_profile_from_independent_active_angle_integral(self):
        for S in (-.98, -.6, 0., .9, 1., 1.1, 3.):
            top = np.arccos(-S) if S < 1 else np.pi
            original = quad(lambda phi: max(0, S+np.cos(phi))**3, 0, top,
                            epsabs=1e-13, epsrel=1e-12)[0]/np.pi
            self.assertAlmostEqual(transition_profile(S), original, delta=2e-12)
        self.assertEqual(transition_profile(-1), 0)
        self.assertAlmostEqual(transition_profile(1), 2.5)
        # This includes the regular-side opening, not only S bounded away from -1.
        h = .001
        self.assertLess(abs(transition_profile(-1+h)/h**3.5/OPENING_COEFFICIENT-1), .00003)

    def test_flat_section_against_original_radial_and_boosted_integrals(self):
        for u, r, ss, b in ((3.3, 1.4, 1.7, 1.1), (3.6, .2, 2.7, .9)):
            radius = brentq(lambda z: u-np.hypot(r, z)-np.hypot(ss, z), 0, u)
            original = 2*np.pi**2*quad(
                lambda z: z**3*(u-np.hypot(r, z)-np.hypot(ss, z)), 0, radius,
                epsabs=1e-12, epsrel=1e-12)[0]
            actual = flat_section(u, r, ss, order=48)
            self.assertAlmostEqual(actual, original, places=11)
            boosted = boosted_flat_section(np.hypot(u, b), b, r, ss, order=56)
            self.assertAlmostEqual(boosted, original, delta=2e-8)

    def test_actual_intervals_on_both_sides_of_secondary_transition(self):
        a = .12
        for S in (-.6, 0., .9, 1., 1.1, 2.):
            u, theta = np.pi+a*S, np.pi-a
            actual = interval_volume(u, theta, order=56, flat_order=32)
            refined = interval_volume(u, theta, order=80, flat_order=40)
            independent = polar_volume(u, theta, order=80, flat_order=40)
            self.assertGreater(actual, 0)
            self.assertLess(abs(actual/refined-1), 3e-7)
            self.assertLess(abs(independent/refined-1), 2e-6)

    def test_actual_antipodal_and_transverse_cubic_scaling(self):
        independent_D = 4*np.pi/3*quad(
            lambda r: np.sin(r)*r*r*(np.pi-r)**2, 0, np.pi, epsabs=1e-12)[0]
        self.assertAlmostEqual(D, independent_D, places=11)
        for S in (-.6, 0., 1., 1.4):
            errors = []
            for a in (.1, .025, .00625):
                actual = interval_volume(np.pi+a*S, np.pi-a, order=72, flat_order=40)
                errors.append(abs(actual/(D*a**3*transition_profile(S))-1))
            self.assertTrue(errors[2] < errors[1] < errors[0])
            self.assertLess(errors[-1], .006)
        errors = [abs(interval_volume(np.pi+e, np.pi, order=160, flat_order=48)/e**3/D-1)
                  for e in (.02, .005, .00125)]
        self.assertTrue(errors[2] < errors[1] < errors[0])
        self.assertLess(errors[-1], .002)

    def test_fixed_diamond_regular_side_and_flat_origin_normalization(self):
        for a in (.3, .1, .03):
            theta, e = np.pi-a, a/40
            actual = interval_volume(theta+e, theta, order=72, flat_order=32)/e**3.5
            fixed_domain = regular_phase(theta, e, order=36)
            self.assertLess(abs(actual/fixed_domain-1), 2e-6)
        errors = [abs(np.sqrt(a)*regular_phase(np.pi-a, 0, order=40)
                      /(D*OPENING_COEFFICIENT)-1) for a in (.012, .003, .00075)]
        self.assertTrue(errors[2] < errors[1] < errors[0])
        self.assertLess(errors[-1], .001)
        theta, e = .015, .01
        actual = interval_volume(theta+e, theta, order=72, flat_order=32)
        minkowski = float(interval_coefficient(7))*((theta+e)**2-theta**2)**3.5
        self.assertLess(abs(actual/minkowski-1), .0001)
        with self.assertRaises(ValueError):
            regular_phase(3., 2*(np.pi-3.)+1e-12)

    def test_complete_time_contacts_and_temporal_masks(self):
        delta = 2.9
        for u in (.02, .8, 2.8, delta, np.pi, 3.8):
            top = np.sqrt(16-u*u)
            original = 2*np.pi**2*quad(
                lambda b: b**3*(4-np.hypot(u, b))*u/np.hypot(u, b), 0, top,
                epsabs=1e-11)[0]
            self.assertAlmostEqual(time_weight(u), original, delta=2e-10)
            lo = np.sqrt(delta*delta-u*u) if u < delta else 0
            long = 2*np.pi**2*quad(
                lambda b: b**3*(4-np.hypot(u, b))*u/np.hypot(u, b), lo, top)[0]
            self.assertAlmostEqual(time_weight(u, delta), long, delta=2e-10)
            self.assertAlmostEqual(time_weight(u, delta)+time_weight(u, delta, short=True),
                                   original, delta=2e-10)
        self.assertEqual(time_weight(delta, delta, short=True), 0)
        self.assertGreater(time_weight(np.pi), 0)

    def test_full_flat_partner_reduction_at_finite_density(self):
        theta, rho = 2.9, .3
        nodes, weights = gauss_rule(28)
        kernel = s.lambdify(Z, kernel_polynomial(7)*s.exp(-Z), "numpy")
        original = 0.
        for t, wt in zip(nodes, weights):
            tau = theta+(4-theta)*t
            top = np.sqrt(tau*tau-theta*theta)
            for z, wz in zip(nodes, weights):
                b = top*z
                u = np.sqrt(tau*tau-b*b)
                original += ((4-theta)*wt*2*np.pi**2*top**4*wz*z**3*(4-tau)
                             * kernel(rho*interval_volume(u, theta, order=32, flat_order=20)))
        reduced = quad(lambda u: time_weight(u)*kernel(
            rho*interval_volume(u, theta, order=48, flat_order=28)), theta, 4,
            points=[2*np.pi-theta], epsabs=2e-7)[0]
        self.assertAlmostEqual(original, reduced, delta=2e-6)

    def test_signed_moment_physical_point_and_short_contact_coefficient(self):
        kernel = s.Poly(kernel_polynomial(7), Z)
        moment = sum(coefficient*s.factorial(power[0]) for power, coefficient in kernel.terms())
        self.assertEqual(moment, -s.Rational(5, 128))
        a, beta = action_constants(7)
        self.assertEqual(s.simplify(a-8*beta), 0)
        c = interval_coefficient(7)
        self.assertEqual(c, s.pi**3/2688)
        # Divide primitive coefficients by VolM to check the complete physical point.
        point_primitive = -2*s.pi*(4*s.pi**2/3)/(35*c)
        self.assertEqual(point_primitive, -s.Rational(1024, 5))
        self.assertEqual(point_primitive*moment, 8)
        self.assertEqual(s.simplify(a-beta*point_primitive*moment), 0)
        u, tau, delta, T = s.symbols("u tau delta T", positive=True)
        full = s.expand(s.pi**2*u*(T-u)**3*(T+3*u)/6)
        short = s.expand(2*s.pi**2*u*s.integrate((T-tau)*(tau*tau-u*u), (tau, u, delta)))
        self.assertEqual(full.coeff(u, 4), 4*s.pi**2*T/3)
        self.assertEqual(short.coeff(u, 4), full.coeff(u, 4))
        self.assertEqual(set(s.Poly(full-short, u).monoms()), {(1,), (3,)})
        lower, _ = sign_certificate()
        cut = PAIR_FACTOR*time_weight(np.pi)/(3*D)*float(lower)
        self.assertGreater(float(beta)*5/128*cut, 0)
        self.assertGreater(SPATIAL_VOLUME, 0)

    def test_matching_identity_restores_the_entire_opening_wedge(self):
        # O11 with D scaled to one: two genuinely different integration orders.
        # This is not an action asymptotic or a fit of the finite-part constant.
        def root(t):
            value = 1/t**3
            upper = max(2., value**(1/3)+1)
            return brentq(lambda S: transition_profile(S)-value, -1, upper, xtol=1e-13)
        for m in (.5, 2., 6.):
            contact = 2.5**(-1/3)
            direct = quad(lambda t: t*t*(1+root(t)), 0, m, epsabs=1e-11,
                          epsrel=1e-11, points=[contact] if contact < m else [])[0]
            split = root(m)
            tail = (np.log1p(1.5/split**2)/3 if split >= 1 else
                    quad(lambda S: 1/transition_profile(S), split, 1,
                         epsabs=1e-11, epsrel=1e-11)[0]+np.log(2.5)/3)
            restored = (m**3*(split+1)+tail)/3
            self.assertAlmostEqual(direct, restored, delta=2e-9)
            self.assertGreater(abs(restored-tail/3), .01)

    def test_no_invalid_geometry_fallback(self):
        for u in (-.1, 4.1, np.nan):
            with self.assertRaises(ValueError):
                time_weight(u)
        with self.assertRaises(ValueError):
            time_weight(2., short=True)
        with self.assertRaises(ValueError):
            time_weight(2., cutoff=4.)
        with self.assertRaises(ValueError):
            flat_section(3., -1., 2.)
        with self.assertRaises(ValueError):
            interval_volume(2., 3.)
        self.assertEqual(interval_volume(3., 3.), 0)


if __name__ == "__main__":
    unittest.main()
