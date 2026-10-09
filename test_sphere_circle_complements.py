"""Finite regressions, separate from the written #152 analytic proof."""

import unittest

import numpy as np
import sympy as sp
from scipy.integrate import quad

from general_metric_gate import gauss_rule
from sphere_circle_complements import (
    FLAT_VOLUME, PAIR_FACTOR, _diamond_rule, check_complement_identities,
    inverse_phase, offcut_density, phase_factor, phase_factor_derivative,
    radial_amplitude, reduced_density, short_density, time_radius,
)
from sphere_circle_focusing import interval_volume, time_weight
from two_face_diagnostics import bdg_kernel as kernel


class SphereCircleComplementTests(unittest.TestCase):
    def test_exact_4d_algebra_and_independent_target(self):
        check_complement_identities()
        for order in (12, 20):
            a, b1, b2, weights = _diamond_rule(order)
            self.assertAlmostEqual(weights.sum(), FLAT_VOLUME, places=13)
            for value, target in ((a*a, 1/60), (b1*b1, 1/30), (b2*b2, 1/30),
                                  (a*b1, 0)):
                self.assertAlmostEqual(weights @ value / FLAT_VOLUME, target, places=12)

    def test_actual_phase_including_sphere_polar_origin(self):
        for y, q in ((0, .03), (.02, .003), (.2, .01), (4, .01), (7.84, .01)):
            actual = interval_volume(np.sqrt(y+q), np.sqrt(y), order=64, circle_order=64)
            fixed = FLAT_VOLUME*q*q*phase_factor(y, q, order=20)
            self.assertLess(abs(actual/fixed-1), 3e-7)
        self.assertAlmostEqual(phase_factor(0, 0), 1, places=12)
        with self.assertRaises(ValueError):
            phase_factor((np.pi-.05)**2, 1)

    def test_derived_two_variable_jet_is_not_a_substituted_phase(self):
        for yy, qq in ((1, 0), (0, 1), (.7, 1.2)):
            errors = []
            for h in (.04, .02, .01):
                actual = phase_factor(h*yy, h*qq, order=16)
                jet = 1+h*yy/30-h*qq/90
                errors.append(abs(actual-jet))
            self.assertGreater(errors[0]/errors[1], 3.9)
            self.assertGreater(errors[1]/errors[2], 3.9)
            self.assertGreater(errors[-1], 1e-10)
        self.assertAlmostEqual(phase_factor_derivative(0, 0), -1/90, places=12)

    def test_actual_inverse_and_derived_phase_derivative(self):
        for y, v in ((0, .005), (.03, .002), (2, .004), (7.84, .002)):
            q, qv = inverse_phase(y, v, order=16)
            self.assertAlmostEqual(q*np.sqrt(phase_factor(y, q, order=16)), v, places=13)
            step = v/100
            finite = (inverse_phase(y, v+step, order=16)[0]
                      - inverse_phase(y, v-step, order=16)[0])/(2*step)
            self.assertLess(abs(qv/finite-1), 2e-9)
            self.assertGreater(qv, 0)

    def test_moving_time_and_artificial_boundary_contacts(self):
        h, d = 1e-5, 2.8
        for duration, m in ((.2, 0), (.2, .99), (4, .9)):
            qv = inverse_phase((1-m*m)*duration**2, 0)[1]
            derivative = -qv/(2*duration)
            moved = time_radius(duration, m, h)
            self.assertLess(abs((moved-duration)/h/derivative-1), .0001)
            r = time_radius(duration, m, .002)
            q = inverse_phase((1-m*m)*r*r, .002)[0]
            self.assertAlmostEqual(np.sqrt(r*r+q), duration, places=12)
            self.assertLess(r, duration)  # freezing the contact loses a real strip
        qcut, _ = inverse_phase(d*d, .002)
        contact = np.sqrt(1-d*d/(16-qcut))
        cap_radius = d/np.sqrt(1-contact*contact)
        self.assertAlmostEqual(time_radius(4, contact, .002), cap_radius, places=12)
        self.assertAlmostEqual(radial_amplitude(cap_radius, contact, .002), 0, places=12)

    def test_nearly_null_long_circle_partners_are_present(self):
        delta = .2
        expected = 4*np.log(4/delta)-4+delta
        for u in (.01, .002, .0004):
            self.assertLess(abs(time_weight(u, delta)/(2*u)-expected), .003)
            self.assertGreater(time_weight(u, delta), 0)
        # m=1 has zero reduced sphere separation, but original time is near 2.
        r, m, v = 2., 1., 1e-5
        self.assertGreater(radial_amplitude(r, m, v), 3.9)
        self.assertLess(np.sqrt(inverse_phase(0, v)[0]), delta)
        self.assertGreater(np.sqrt(r*r+inverse_phase(0, v)[0]), delta)

    def test_actual_short_density_matches_original_F3_contact_weight(self):
        for v in (.002, .008):
            radial = short_density(v)
            original = reduced_density(v, short=True, order=12)
            self.assertAlmostEqual(radial, original, places=9)

    def test_actual_offcut_density_matches_independent_F3_with_cusp(self):
        v = .002
        radial = offcut_density(v, order=12, radial_order=22, direction_order=22)
        original = reduced_density(v, order=16)
        self.assertLess(abs(radial-original), 2e-7)
        self.assertGreater(radial, 9000)  # it is not an empty long complement

    def test_actual_short_second_log_after_annihilating_analytic_terms(self):
        # This uses actual inverse-phase quadratures, NOT the displayed jet.
        # A third difference removes all (unknown) analytic coefficients <=2.
        weights = np.array([-1, 3, -3, 1])
        multiples = np.arange(1, 5)
        denominator = weights @ (multiples**2*np.log(multiples))
        errors = []
        for h in (2.5e-5, 6.25e-6):
            v = h*multiples
            actual = np.array([short_density(x, radial_order=44) for x in v])
            coefficient = (weights @ (actual-PAIR_FACTOR*v*np.log(v)))/(h*h*denominator)
            errors.append(abs(coefficient/(PAIR_FACTOR/8)-1))
        self.assertLess(errors[0], .06)
        self.assertLess(errors[1], .016)
        self.assertLess(errors[1], errors[0]/3)

    def test_actual_offcut_quadratic_density_remainder(self):
        weights = np.array([-1, 3, -3, 1])
        differences = []
        for h in (.001, .0005):
            actual = [offcut_density(i*h, order=10, radial_order=16, direction_order=16)
                      for i in range(4)]
            differences.append(abs(weights @ actual))
        self.assertTrue(7.7 < differences[0]/differences[1] < 8.6)
        self.assertGreater(differences[1], 1e-6)  # actual remainder is not set to zero

    def test_abel_log_recurrence_and_integrable_signed_remainders(self):
        t, delta = sp.symbols("t delta", positive=True)
        # I_-1, then the exact integration-by-parts recurrence for I_n.
        analytic = sp.log(delta+sp.sqrt(delta*delta-t))
        log_coefficient = -sp.Rational(1, 2)
        for n in range(4):
            analytic = (delta*(delta*delta-t)**sp.Rational(2*n+1, 2)/(2*n+2)
                        - sp.Rational(2*n+1, 2*n+2)*t*analytic)
            log_coefficient *= -sp.Rational(2*n+1, 2*n+2)*t
            self.assertEqual(log_coefficient, (-1)**n * sp.binomial(2*n+2, n+1)
                             / 2**(2*n+3) * t**(n+1))
            exact = float((analytic+log_coefficient*sp.log(t)).subs({t: .002, delta: .2}))
            integral = quad(lambda s: s**(2*n+2)/np.sqrt(s*s+.002),
                            0, np.sqrt(.04-.002), epsabs=1e-14)[0]
            self.assertAlmostEqual(exact, integral, places=13)
        majorant = quad(lambda z: z*z*abs(kernel(z*z)), 0, 12)[0]
        self.assertTrue(0 < majorant < 10)
        for j, target in ((1, 1/12), (2, -np.sqrt(np.pi)/12)):
            actual = quad(lambda z: z**j*np.log(z)*kernel(z*z), 0, 12,
                          epsabs=1e-12)[0]
            self.assertAlmostEqual(actual, target, places=10)

    def test_signed_short_finite_density_change_of_variables(self):
        delta, rho = .2, 2000
        nn, wn = gauss_rule(20)
        mm, wm = gauss_rule(6)
        original = 0.0
        for tau, wt in zip(delta*nn, delta*wn):
            for x, wx in zip(nn, wn):
                r = tau*x
                q = tau*tau-r*r
                for m, weight in zip(mm, wm):
                    y = (1-m*m)*r*r
                    volume = FLAT_VOLUME*q*q*phase_factor(y, q, order=8)
                    original += (2*PAIR_FACTOR*wt*wx*weight*(4-tau)*tau*r*r
                                 * np.sinc(np.sqrt(y)/np.pi)*kernel(rho*volume))
        cap = delta*delta*np.sqrt(phase_factor(0, delta*delta, order=8))
        tt, wt = gauss_rule(40)
        denominator = tt**4+(1-tt)**4
        vv = cap*tt**4/denominator
        wv = wt*cap*4*tt**3*(1-tt)**3/denominator**2
        transformed = sum(weight*kernel(rho*FLAT_VOLUME*v*v)
                          * short_density(v, order=8, radial_order=24, direction_order=6)
                          for v, weight in zip(vv, wv))
        self.assertLess(abs(original-transformed), 3e-7)
        self.assertNotEqual(original, 0)


if __name__ == "__main__":
    unittest.main()
