"""Finite M3 diagnostics; no universal geometric remainder is certified."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

import curved_three_d as c
import curved_three_d_matching as m
from dimension_kernels import mellin_factor


class SignedAveragingTests(unittest.TestCase):
    def test_genuine_kernel_second_derivative(self):
        z = s.symbols('z', positive=True)
        f = (1-27*z**s.Rational(3, 2)/8+9*z**3/8)*s.exp(-z**s.Rational(3, 2))
        exact = s.lambdify(z, s.diff(f, z, 2), 'numpy')
        points = np.geomspace(1e-4, 10, 30)
        np.testing.assert_allclose(m.phase_kernel_second(points), exact(points), rtol=2e-12)

    def test_two_zero_moments_and_nonzero_critical_moment(self):
        for power, expected in ((2, 0), (3, 0), (3.5, 35*math.gamma(2/3)/24)):
            value = quad(lambda z: z**power*m.phase_kernel_second(z),
                         0, 14, epsabs=2e-10)[0]
            self.assertAlmostEqual(value, expected, places=9)

    def test_exact_signed_ramp_response_including_linear_tail(self):
        phases = np.array([.03, .2, .65, .9])
        weights = np.array([.7, -.2, 1.1, .4])
        for rho in (1., 7., 31.):
            direct = -c.BETA3*rho**(5/3)*np.dot(
                weights, c.kernel3(c.C3*rho*phases**1.5))
            self.assertAlmostEqual(m.ramp_response(rho, phases, weights), direct, places=8)

    def test_truncating_the_ramp_tail_changes_the_response(self):
        rho, phase = 3., .2
        correct = m.ramp_response(rho, [phase], [1.])
        # If Q is falsely set to zero past the only phase, it is zero everywhere.
        self.assertGreater(abs(correct), .1)

    def test_all_ordered_weights_and_signed_complements(self):
        phases = np.array([.04, .15, .6])
        weights = np.array([1.2, -.4, .8])
        source = np.array([.1, .35, .55])
        target = np.array([.7, .3])
        complete = m.ramp_response(2., phases, weights)
        ordered = sum(m.ramp_response(2., phases, a*b*weights)
                      for a in source for b in target)
        self.assertAlmostEqual(ordered, complete, places=10)
        low = phases < .15
        self.assertAlmostEqual(
            m.ramp_response(2., phases[low], weights[low])+
            m.ramp_response(2., phases[~low], weights[~low]), complete, places=10)
        self.assertNotAlmostEqual(source[0]*target[0]*complete, complete, places=3)

    def test_positive_oscillatory_primitive_has_no_second_coefficient(self):
        a = .75
        self.assertGreater(1-2*.01-a*.01**(1-a), 0)
        for n in (100, 1000, 10000):
            for shift, sign in ((math.pi/2, 1), (3*math.pi/2, -1)):
                w = (2*math.pi*n+shift)**(-1/a)
                # (N-w)/w^2, evaluated without subtractive roundoff.
                self.assertAlmostEqual(math.sin(w**-a), sign, places=8)

    def test_averaged_oscillation_bound_without_a_pointwise_jet(self):
        a = .75
        for w in (.01, .003, .001, .0001):
            remainder = m.oscillatory_q_remainder(w, a)
            self.assertLessEqual(abs(remainder), 2/a*w**(3+a))
            self.assertLessEqual(abs(remainder)/w**3.5, 2/a*w**(a-.5))
        # Independent finite-domain quadrature at a mild frequency, with a
        # rigorously bounded omitted tail, not an unguarded oscillatory integral.
        w, lower, upper = .003, .003**(-a), 1000.
        integral = quad(lambda u: u**(-3/a-1)/a, lower, upper,
                        weight='sin', wvar=1., epsabs=1e-20)[0]
        omitted = 2/a*upper**(-3/a-1)
        self.assertLess(abs(integral-m.oscillatory_q_remainder(w, a)), omitted+1e-20)


class GeometricMechanismTests(unittest.TestCase):
    def test_matched_powers_and_both_restored_subtractions(self):
        for w in (1e-2, 1e-5, 1e-9):
            values = m.quartic_matching_bounds(w)
            scaled = values/w**2.7
            np.testing.assert_allclose(scaled[1:], [2/5, 6/17, 6/7], rtol=2e-14)
            self.assertAlmostEqual(scaled[0], 2*(1-w**.3), places=12)
            self.assertGreater(values[2]+values[3], 0)
        self.assertGreater(s.Rational(27, 10), s.Rational(5, 2))
        self.assertGreater(s.Rational(37, 10), s.Rational(7, 2))

    def test_actual_minimum_coordinates_and_jet_transport(self):
        # Noncanonical controls exercise the error term in M3.6; the
        # simple canonical b_a=4c identity is NOT assumed here.
        a, u, k, aa, bb = s.symbols('a u k A B')
        potential = u**4+aa*(u**2+u**3/10)+bb*(u+u**4/20)
        da = lambda n: s.diff(potential, u, n).subs(u, a)
        solution = s.solve([da(1), da(2)-2*k], [aa, bb])
        pp = s.Matrix([solution[aa], solution[bb]])
        matrix = s.Matrix([[s.diff(da(1), p) for p in (aa, bb)],
                           [s.diff(da(2), p) for p in (aa, bb)]])
        self.assertNotEqual(matrix.subs(a, 0).det(), 0)
        det = s.factor(pp.jacobian([a, k]).det())
        self.assertEqual(s.factor(det+4*k/matrix.det()), 0)
        cubic = s.factor(da(3).subs(solution)/6)
        quartic = da(4).subs(solution)/24
        correction = (s.Matrix([[s.diff(da(3), p) for p in (aa, bb)]])*
                      pp.diff(a))[0]/6
        self.assertEqual(s.factor(s.diff(cubic, a)-4*quartic-correction), 0)
        self.assertNotEqual(s.factor(correction), 0)

    def test_quartic_angular_abundance_and_impossible_independent_panel(self):
        a, k = s.symbols('a k', positive=True)
        # For u^4+A*u^2+B*u: b=4a, c=1, |a|<=sqrt(k)/2.
        self.assertEqual(s.diff(4*a, a), 4)
        self.assertEqual(s.integrate(1, (a, -s.sqrt(k)/2, s.sqrt(k)/2)), s.sqrt(k))
        # A label-independent b=0,c=1 violates the exact k=0 transport.
        self.assertNotEqual(s.diff(s.Integer(0), a), 4*s.Integer(1))

    def test_clipping_bound_does_not_count_zeroes(self):
        for n in (1, 7, 43):
            ratio = .3
            exact = m.clipped_sine_integral(n, ratio)
            band = ratio/n**2
            # Integration by parts: -int clip_s(b)*b''; b=0 at endpoints.
            direct = quad(lambda theta: np.clip(math.sin(theta), -ratio, ratio)*
                          math.sin(theta), 0, 2*math.pi,
                          points=[math.asin(ratio), math.pi-math.asin(ratio),
                                  math.pi+math.asin(ratio), 2*math.pi-math.asin(ratio)],
                          epsabs=1e-11)[0]/n**2
            self.assertAlmostEqual(direct, exact, places=11)
            self.assertLessEqual(exact, 4*band)

    def test_physical_sublens_power_with_all_model_wells(self):
        for k in (1e-4, .01, .2):
            for h in (k**3, k*k, k):
                lower_scale = h**1.5/math.sqrt(k+math.sqrt(h))
                for r in (-.5, -.2, 0, .2, .5):
                    self.assertGreater(m.quartic_sublens(k, h, r)/lower_scale, .4)

    def test_universal_and_angular_exponents_are_distinct(self):
        h, v = s.symbols('h v', positive=True)
        rough = s.integrate(h/2, (h, 0, v**s.Rational(4, 5)))
        angular = s.integrate(s.Rational(2, 5)*h**s.Rational(5, 4),
                              (h, 0, v**s.Rational(4, 5)))
        self.assertEqual(rough, v**s.Rational(8, 5)/4)
        self.assertEqual(angular, s.Rational(8, 45)*v**s.Rational(9, 5))
        self.assertEqual(s.Rational(5, 3)-s.Rational(8, 5), s.Rational(1, 15))
        self.assertEqual(s.Rational(5, 3)-s.Rational(9, 5), -s.Rational(2, 15))


class NegativeControlTests(unittest.TestCase):
    def test_complete_panel_matched_head_not_a_selected_sector(self):
        phi = (1+math.sqrt(5))/2
        for value in (.2, .4, .55):
            left = quad(lambda t: t*(t+2)*(4*t/3+8/5)**(-value)*
                        (1+t)**(-(8-5*value)/4), 0, phi)[0]
            right = quad(lambda u: u**(-1.5*value)*(1+2*u)*
                         (4/3+8*u/5)**(-value), 0, 1/phi)[0]
            self.assertAlmostEqual(m.panel_matched_head(value), left+right, places=8)
        self.assertAlmostEqual(m.panel_matched_head(8/5), m.panel_residue_value(), places=9)
        self.assertLess(m.panel_residue_value(), 0)
        self.assertGreater(float(mellin_factor(3, s.Rational(8, 5))), 0)

    def test_bv_jump_bound_does_not_bound_inverse_cut_constants(self):
        for n in (8, 64, 512):
            jumps, reciprocals = m.fan_jump_sums(n)
            self.assertLess(jumps, 2*math.pi)
            self.assertGreater(reciprocals, n*n/(2*math.pi))
        self.assertGreater(m.fan_jump_sums(512)[1]/m.fan_jump_sums(64)[1], 63)

    def test_invalid_domains_fail_explicitly(self):
        calls = [lambda: m.phase_kernel_second(0),
                 lambda: m.ramp_response(0, [.1], [1]),
                 lambda: m.ramp_response(1, [.1], [math.nan]),
                 lambda: m.ramp_response(1, [-.1], [1]),
                 lambda: m.oscillatory_q_remainder(.1, .5),
                 lambda: m.quartic_matching_bounds(0),
                 lambda: m.quartic_sublens(1, -1),
                 lambda: m.clipped_sine_integral(0, .2),
                 lambda: m.panel_matched_head(4/3),
                 lambda: m.panel_matched_head(2),
                 lambda: m.fan_jump_sums(True)]
        for call in calls:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
