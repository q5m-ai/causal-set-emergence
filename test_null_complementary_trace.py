"""Finite CT checks, not certification of geometric critical remainders."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import Z, kernel_polynomial
from full_partner_globalization import primitive_response
from null_complementary_trace import (
    cap_third, fold_trace_prefactor, replacement_exponent,
    six_dimensional_cap_integral, transport_pairing, triangle_prefactor,
    triangle_section,
)
from null_suspension import cap_weight, diamond_action, physical_section
from null_suspension_matching import klein_charge_prefactor


class NullComplementaryTraceTests(unittest.TestCase):
    def test_total_degree_taylor_not_separate_truncations(self):
        z, t, e, length = s.symbols('z t e length', positive=True)
        expression = s.sqrt(2*length+z*(t+e))/(length+z*t)
        for order in range(5):
            polynomial = s.series(expression, z, 0, order+1).removeO().subs(z, 1)
            expected = float(polynomial.subs({length: 1.3, t: .12, e: .07}))
            self.assertAlmostEqual(triangle_prefactor(1.3, .12, .07, order),
                                   expected, places=13)

    def test_triangle_section_is_the_actual_distance_pair_integral(self):
        for length, height, excess, difference in (
                (1., .3, .1, .4), (2., .4, 0., 2.),
                (2., .4, 0., -2.), (1.4, .2, .05, 0.)):
            r = (length+excess+difference)/2
            t = (length+excess-difference)/2
            expected = physical_section(length+height, r, t)
            self.assertAlmostEqual(triangle_section(length, height, excess, difference),
                                   expected, delta=2e-11*max(1, expected))
        self.assertEqual(triangle_section(1, .1, .1, 0), 0)
        self.assertEqual(triangle_section(1, .1, .2, 0), 0)

    def test_finite_reference_errors_and_both_tip_factors(self):
        for order in (1, 2, 3):
            for h in (.1, .05, .025):
                for ratio in (-1., -.3, 1.):
                    exact = triangle_section(1., h, h/4, ratio)
                    ref = triangle_section(1., h, h/4, ratio, order)
                    self.assertGreater(ref, 0)
                    self.assertLess(abs(ref-exact)/exact, 2*h**(order+1))
        # Freezing the longitudinal square root at t=0 gives zero here,
        # whereas the real tip contribution is strictly positive.
        self.assertGreater(triangle_section(1, .05, 0, 1), 0)
        self.assertGreater(triangle_section(1, .05, 0, -1), 0)

    def test_conditional_geometry_cannot_be_averaged_before_kernel(self):
        kernel = s.lambdify(Z, kernel_polynomial(6)*s.exp(-Z), 'math')
        rho = 30.
        phases = [triangle_section(1, .2, .02, xi) for xi in (0., .99)]
        actual = sum(kernel(rho*v) for v in phases)/2
        averaged = kernel(rho*sum(phases)/2)
        self.assertGreater(abs(actual-averaged), 1e-3)

    def test_critical_replacement_orders_are_strictly_better_than_one(self):
        for d in range(2, 18):
            eta = replacement_exponent(d)
            self.assertGreater(eta, 1)
            expected = 1+((2 if d % 2 == 0 else 1)/d)
            self.assertAlmostEqual(eta, expected)
        # Absolute DIFFERENCE shell model, not an actual spacetime primitive.
        d, eta = 6, replacement_exponent(6)
        alpha = 2/d
        for rho in (3., 17.):
            direct = quad(lambda v: rho*v**(1+eta)*math.exp(-rho*v)
                          * alpha*v**(alpha-1), 0, np.inf)[0]
            expected = alpha*math.gamma(1+eta+alpha)*rho**(-eta-alpha)
            self.assertAlmostEqual(direct, expected, delta=3e-11)

    def test_actual_cap_third_derivative_and_cubic_closing(self):
        u, t = s.symbols('u T', positive=True)
        g = u*((t*t+u*u)*s.log(t/u)-t*t+u*u)
        for order in range(3):
            self.assertEqual(s.diff(g, u, order).subs(u, t), 0)
        self.assertEqual(s.diff(g, u, 3).subs(u, t), -4)
        derivative = s.lambdify((u, t), s.diff(g, u, 3), 'math')
        for a, b in ((.4, 1.3), (.9, 1.), (2.1, 3.)):
            self.assertAlmostEqual(cap_third(a, b), derivative(a, b), places=12)
        self.assertEqual(cap_third(1.3, 1.3), 0)
        self.assertEqual(cap_third(1.4, 1.3), 0)

    def test_exact_anchored_transport_retains_four_lower_moments(self):
        # f(u)=1-3u: signed finite control. Its third anchored primitive
        # follows by ordinary integration, not an asymptotic assumption.
        for anchor, duration in ((.3, 1.4), (.8, 1.4), (.8, .8)):
            f = lambda u: 1-3*u
            moments = []
            for j in (1, 3):
                moments.extend([quad(lambda u: u**j*f(u), 0, anchor)[0],
                                quad(lambda u: u**j*math.log(u)*f(u),
                                     0, anchor)[0]])
            primitive = lambda u: ((1-3*anchor)*(u-anchor)**3/6
                                    -(u-anchor)**4/8)
            direct = quad(lambda u: cap_weight(u, duration)*f(u),
                          0, duration)[0]
            actual = transport_pairing(duration, anchor, moments, primitive)
            self.assertAlmostEqual(actual, direct, delta=2e-11)
            dropped = transport_pairing(duration, anchor, (0, 0, 0, 0), primitive)
            self.assertGreater(abs(dropped-direct), 1e-3)

    def test_green_bound_controls_an_integrated_signed_error(self):
        a, b = .4, 1.8
        error = lambda u: .03*math.sin(29*u)
        l1 = quad(lambda u: abs(error(u)), a, b, limit=200)[0]
        bound = (6*math.log(b/a)+(b/a)**2+5)*l1
        for t in (.4, .8, 1.4, 1.8):
            response = transport_pairing(t, a, (0, 0, 0, 0), error)
            self.assertLessEqual(abs(response), bound)

    def test_smooth_test_zero_does_not_control_the_real_closing_cap(self):
        z = s.Symbol('z', real=True)
        # A compact C5 control suffices for these four integrations; the
        # written CT9 also permits a compact C-infinity bump.
        phi = (1-z*z)**6
        fourth = s.diff(phi, z, 4)
        for j in range(4):
            self.assertEqual(s.integrate(z**j*fourth, (z, -1, 1)), 0)
        self.assertEqual(s.integrate((-z)**3*fourth, (z, -1, 0))*s.Rational(2, 3), 4)
        f4 = s.lambdify(z, fourth, 'math')
        smooth = s.lambdify(z, phi, 'math')
        for h in (.02, .01, .005):
            paired = quad(lambda zz: cap_weight(1+h*zz, 1)*f4(zz)/h**3,
                          -1, 0, epsabs=2e-10)[0]
            self.assertAlmostEqual(paired, 4, delta=5*h)
            # Weak pairing with exp(u), evaluated after four integrations
            # to avoid cancellation, is O(h).
            weak = h*quad(lambda zz: smooth(zz)*math.exp(1+h*zz), -1, 1)[0]
            self.assertLess(weak, 6*h)
        first = s.diff(phi, z)
        self.assertEqual(-s.integrate(first, (z, 0, 1))*2, 2)

    def test_fold_face_transversality_with_all_active_subsets(self):
        signs = np.array([1., 1., -1., -1.])
        mixed = 0
        for mask in range(1, 16):
            active = [i for i in range(4) if mask & (1 << i)]
            plus = [i for i in active if signs[i] > 0]
            minus = [i for i in active if signs[i] < 0]
            if not plus or not minus:
                continue
            mixed += 1
            theta = np.zeros(4)
            theta[plus] = 1/len(plus)
            theta[minus] = 1/len(minus)
            theta /= np.linalg.norm(theta)
            i, j = plus[0], minus[0]
            tangent = np.zeros(4)
            tangent[i], tangent[j] = theta[j], -theta[i]
            self.assertAlmostEqual(theta @ tangent, 0)
            self.assertAlmostEqual(signs @ theta, 0)
            self.assertNotEqual(signs @ tangent, 0)
            for k in set(range(4))-set(active):
                self.assertEqual(tangent[k], 0)
        self.assertEqual(mixed, 9)

    def test_integrate_fold_translation_before_bounding_it(self):
        # Elementary transverse control, NOT a geometric remainder proof.
        # Signed mass is smooth in h; absolute translation error is sqrt(h).
        for h in (.01, .0025, .000625):
            signed = 2*(math.sqrt(1+h)-1)
            absolute = 4*math.sqrt(h)-signed
            self.assertLess(abs(signed), 1.01*h)
            self.assertGreater(absolute, 3*math.sqrt(h))

    def test_fold_trace_measure_matches_the_actual_spectator_cap(self):
        for d in (5, 6, 7, 9):
            p, t = d-4, 1.05
            # u=1+x^2 removes the integrable inverse square root for p=1.
            def integrand(x):
                u = 1+x*x
                return 2*x*cap_weight(u, t)*(u*u-1)**((p-2)/2)
            raw = quad(integrand, 0, math.sqrt(t-1), epsabs=1e-16)[0]
            expected = klein_charge_prefactor(d, t)
            self.assertAlmostEqual(fold_trace_prefactor(d)*raw, expected,
                                   delta=3e-10*expected)

    def test_six_dimensional_cap_closed_expression_and_threshold_order(self):
        for t in (1.02, 1.05, 1.1):
            closed = (t**4/16+t*t/4-5/16-(t*t/2+.25)*math.log(t))
            positive = six_dimensional_cap_integral(t)
            self.assertGreater(positive, 0)
            self.assertAlmostEqual(closed, positive, delta=1e-15)
            expected = klein_charge_prefactor(6, t)
            self.assertAlmostEqual(fold_trace_prefactor(6)*positive, expected,
                                   delta=3e-10*expected)
        t = s.Symbol('T', positive=True)
        closed = (t**4/16+t*t/4-s.Rational(5, 16)
                  -(t*t/2+s.Rational(1, 4))*s.log(t))
        for k in range(4):
            self.assertEqual(s.diff(closed, t, k).subs(t, 1), 0)
        self.assertEqual(s.diff(closed, t, 4).subs(t, 1)/s.factorial(4), s.Rational(1, 6))
        self.assertAlmostEqual(six_dimensional_cap_integral(1.0001)/.0001**4,
                               1/6, delta=1e-4)

    def test_six_dimensional_fourth_zero_and_new_error_order(self):
        for j in range(1, 5):
            self.assertEqual(s.simplify(primitive_response(6, j, 1)), 0)
        for exponent, expected in ((s.Rational(7, 2), s.Rational(1, 6)),
                                   (s.Rational(9, 2), -s.Rational(1, 6)),
                                   (5, -s.Rational(1, 3))):
            self.assertEqual(1+s.Rational(2, 6)*(1-exponent), expected)
        self.assertGreater(float(primitive_response(6, s.Rational(7, 2), 1)), 0)
        self.assertEqual(2*(2*10**2), 400)

    def test_diamond_homogeneous_mode_is_not_zero(self):
        for rho in (10., 100.):
            self.assertGreater(diamond_action(rho, 1), 1.98)
        t = s.Symbol('T', positive=True)
        def op(f):
            d2 = lambda g: t*s.diff(g, t)-2*g
            a = d2(d2(f))
            return s.simplify(t*s.diff(t*s.diff(a, t), t))
        for f in (s.S.One, s.log(t), t*t, t*t*s.log(t)):
            self.assertEqual(op(f), 0)

    def test_invalid_inputs(self):
        for args in ((0, .1, 0), (1, -.1, 0), (1, .1, .2), (1, math.nan, 0)):
            with self.assertRaises(ValueError):
                triangle_prefactor(*args)
        for order in (-1, True, 2.5):
            with self.assertRaises(ValueError):
                triangle_prefactor(1, .1, .05, order)
        for args in ((1, -.1, 0, 0), (1, .1, -.1, 0), (1, .1, 0, 1.1)):
            with self.assertRaises(ValueError):
                triangle_section(*args)
        for d in (1, True, 3.0):
            with self.assertRaises(ValueError):
                replacement_exponent(d)
        for d in (4, True, 6.0):
            with self.assertRaises(ValueError):
                fold_trace_prefactor(d)
        for t in (1, 1.2, math.inf, math.nan):
            with self.assertRaises(ValueError):
                six_dimensional_cap_integral(t)
        with self.assertRaises(ValueError):
            cap_third(0, 1)
        with self.assertRaises(ValueError):
            transport_pairing(1, 0, (0, 0, 0, 0), lambda u: 0)
        with self.assertRaises(ValueError):
            transport_pairing(1, .2, (0, 0), lambda u: 0)


if __name__ == '__main__':
    unittest.main()
