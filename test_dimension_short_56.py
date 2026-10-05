"""Regressions for #132's written proof, not machine verification of that proof."""

import math
import unittest

from mpmath import mp
import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_joint_geometry import joint_point_geometry
from dimension_kernels import (
    action_constants, interval_coefficient, kernel_polynomial, plane_moment,
    sphere_area, transverse_moment, Z,
)
from dimension_short_56 import (
    ball_cos_jet56, ball_cos_overlap56, check_short56_identities,
    jet_short_action56, planar_short_action56, planar_short_density56,
    short_basis56_symbolic,
)


class DimensionShort56Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.x, cls.L, cls.v = s.symbols("sigma delta v", positive=True)
        cls.tau, cls.radius = (cls.v+cls.x/cls.v)/2, (cls.v-cls.x/cls.v)/2

    def test_exact_bases_and_physical_normalizations(self):
        check_short56_identities()
        self.assertEqual(s.simplify(s.Matrix([self.tau, self.radius]).jacobian(
            [self.x, self.v]).det()), 1/(2*self.v))
        for d in (5, 6):
            basis = short_basis56_symbolic(d, self.x, self.L)
            self.assertTrue(basis[1].is_polynomial(self.x))
            for b in basis:
                self.assertTrue(s.limit(b, self.x, 0, dir="+").is_finite)
            # Independent full sphere slice integral, including the second moment.
            area = float(sphere_area(d-1))
            measure = lambda f: area*quad(
                lambda u: f(u)*(1-u*u)**((d-4)/2), -1, 1, epsabs=2e-12)[0]
            self.assertAlmostEqual(measure(lambda _: 1), float(sphere_area(d)), delta=2e-11)
            self.assertAlmostEqual(measure(lambda u: u), 0, delta=2e-12)
            self.assertAlmostEqual(measure(lambda u: u*u), float(sphere_area(d))/(d-1), delta=2e-11)
        self.assertEqual(sphere_area(5), 2*s.pi**2)
        self.assertEqual(sphere_area(6), 8*s.pi**2/3)

    def test_independent_signed_gamma_and_log_moments(self):
        j = s.symbols("j", real=True)
        expected = {
            5: (1, -s.Rational(215, 16), s.Rational(225, 16), -s.Rational(125, 48)),
            6: (1, -34, s.Rational(141, 2), -s.Rational(63, 2), s.Rational(27, 8)),
        }
        for d in (5, 6):
            coefficients = expected[d]
            self.assertEqual(kernel_polynomial(d), sum(c*Z**i for i, c in enumerate(coefficients)))
            direct = sum(s.Rational(2, d)*c*s.gamma(2*(j+1)/d+i)
                         for i, c in enumerate(coefficients))
            for order in range(d//2+1):
                self.assertEqual(s.simplify(direct.subs(j, order)), 0)
            if d == 5:
                self.assertEqual(s.simplify(direct.subs(j, s.Rational(3, 2))), s.Rational(1, 40))
                self.assertEqual(s.simplify((direct+ s.gamma(s.Rational(7, 5))/8).subs(
                    j, s.Rational(5, 2))), 0)
                self.assertGreater(float(plane_moment(d, 1)), 0)
            else:
                derivative = s.diff(direct, j)
                self.assertEqual(s.simplify(derivative.subs(j, 2)), -s.Rational(1, 36))
                self.assertEqual(s.simplify(derivative.subs(j, 3)-s.gamma(s.Rational(4, 3))/12), 0)
                self.assertEqual(plane_moment(d, 1), 0)
                with self.assertRaises(ValueError):
                    plane_moment(d, 2)
            a, beta = action_constants(d)
            self.assertNotEqual(a, beta)  # Copying the 3D/4D equality is wrong here.
            self.assertEqual(s.simplify(a/beta), s.Rational(8, 3) if d == 5 else s.Rational(5, 2))

    def test_model_finite_density_against_signed_quadrature(self):
        with mp.workdps(60):
            angular = tuple(map(mp.mpf, ("-0.2", "1.7", "3.1", "-2.4")))
            rho, delta = mp.mpf(30000), mp.mpf("0.7")
            for d in (5, 6):
                a, beta = [mp.mpf(str(s.N(value, 65))) for value in action_constants(d)]
                c = mp.mpf(str(s.N(interval_coefficient(d), 65)))
                sphere = mp.mpf(str(s.N(sphere_area(d), 65)))
                bases = s.lambdify((self.x, self.L), short_basis56_symbolic(d, self.x, self.L), "mpmath")
                polynomial = s.lambdify(Z, kernel_polynomial(d), "mpmath")

                def integrand(u):
                    if u == 0:
                        return mp.mpf(0)
                    z = c*rho*u**d
                    return 2*u*mp.fdot(angular, bases(u*u, delta))*polynomial(z)*mp.exp(-z)

                integral = mp.quad(integrand, [0, delta/4, delta/2, delta])
                reference = rho**(mp.mpf(2)/d)*(a*angular[0]/sphere-beta*rho*integral)
                actual = jet_short_action56(d, angular, rho, delta, dps=60)
                self.assertLess(abs(actual-reference), mp.mpf("1e-48"))

    def test_actual_fibre_intersection_keeps_all_partners(self):
        # Independent min/max of BOTH real time intervals, not a polynomial jet.
        a, bend = 0.25, 0.125
        for d in (5, 6):
            for x1 in (-1.1, -0.95, 0.0, 0.92):
                x = np.zeros(d-1)
                x[0], x[-1] = x1, 0.1
                for tau, factor in ((0.02, 1), (0.04, -1), (0.06, 0.4)):
                    b = np.zeros(d-1)
                    b[0] = tau*factor
                    target = x+b
                    H = max(0.0, a*(1-float(x@x)))
                    H_target = max(0.0, a*(1-float(target@target)))
                    f, f_target = bend*math.cos(x[0]), bend*math.cos(target[0])
                    actual = max(0.0, min(f, f_target-tau)-max(f-H, f_target-H_target-tau))
                    gap = max(0.0, H+f_target-f-tau)
                    self.assertAlmostEqual(actual, gap, delta=1e-15)
        # Explicit same-budget small-cutoff contact margin, both phases and dimensions.
        delta = 0.125
        self.assertLess(delta, 2/9)
        self.assertGreater(2*a*math.sqrt(1-(1+bend)*delta/(2*a))-bend*delta/2, 0.4)

    def test_actual_curved_overlap_two_jet_not_a_fit(self):
        for d in (5, 6):
            for w, wp in ((None, None), (lambda x: 1+0.4*x, lambda _: 0.4)):
                jet = ball_cos_jet56(d, weight=w, weight_prime=wp)
                self.assertLess(jet["future_hessian"], -0.5)
                if w is not None:
                    self.assertNotEqual(jet["bulk_gradient"], 0)
                    self.assertNotEqual(jet["surface_p"], 0)
                for first, last in ((1.0, 0.0), (0.3, 0.4), (-0.8, 0.0), (0.0, 0.0)):
                    errors = []
                    for tau in (0.032, 0.016, 0.008):
                        b = np.zeros(d-1)
                        b[0], b[-1] = tau*first, tau*last
                        polynomial = (jet["volume"]-tau*jet["spatial_volume"]
                                      + b[0]*jet["bulk_gradient"]
                                      + b[0]**2*jet["future_hessian"]/2
                                      + (tau*tau*jet["surface"]-2*tau*b[0]*jet["surface_p"]
                                         + b[0]**2*jet["surface_pp"])/2)
                        actual = ball_cos_overlap56(d, tau, b, weight=w)
                        errors.append(abs(actual-polynomial))
                        self.assertLess(errors[-1], 80*tau**3)
                    self.assertLess(errors[-1], errors[0]/25 + 1e-11)

    def test_independent_intrinsic_target_and_signed_source_partition(self):
        a, bend = 0.25, 0.125
        weights = [(lambda _: 1.0, lambda _: 0.0),
                   (lambda x: 2*x*x-0.5, lambda x: 4*x),
                   (lambda x: 1.5-2*x*x, lambda x: -4*x)]
        for d in (5, 6):
            jets = []
            for w, wp in weights:
                jet = ball_cos_jet56(d, weight=w, weight_prime=wp)

                def target(x):
                    grad_h = [-2*a*x, -2*a*math.sqrt(1-x*x)] + [0.0]*(d-3)
                    grad_f = [-bend*math.sin(x)] + [0.0]*(d-2)
                    geometry = joint_point_geometry(d, grad_h, grad_f)
                    # Actual positive normals and Lorentzian Gram, not target_density.
                    return w(x)*float(geometry.weight*geometry.area_density)*(1-x*x)**((d-4)/2)

                independent = float(sphere_area(d-1))*quad(target, -1, 1, epsabs=2e-11)[0]
                self.assertAlmostEqual(jet["short_coefficient"], independent+jet["partition_derivative"],
                                       delta=3e-10)
                jets.append(jet)
            self.assertGreater(abs(jets[1]["partition_derivative"]), 0.2)
            self.assertAlmostEqual(jets[1]["partition_derivative"]+jets[2]["partition_derivative"], 0)
            np.testing.assert_allclose(jets[1]["angular"]+jets[2]["angular"], jets[0]["angular"], atol=3e-11)
            spatial = (0.025, 0.01) + (0.0,)*(d-3)
            overlaps = [ball_cos_overlap56(d, 0.04, spatial, weight=w) for w, _ in weights]
            self.assertAlmostEqual(overlaps[1]+overlaps[2], overlaps[0], delta=2e-12)

    def test_planar_actual_overlap_and_two_independent_density_coordinates(self):
        with mp.workdps(40):
            a, delta = mp.mpf("0.25"), mp.mpf("0.18")
            for d in (5, 6):
                n = d-1
                ball = mp.pi**(mp.mpf(n)/2)/mp.gamma(1+mp.mpf(n)/2)
                V = lambda t: 2*ball*a/(d+1)*(1-t/a)**(mp.mpf(d+1)/2)
                for tau in (0.0, 0.04, 0.1):
                    self.assertAlmostEqual(ball_cos_overlap56(d, tau, (tau,)+(0.0,)*(d-2), bend=0),
                                           float(V(tau)), delta=2e-11)
                for fraction in ("0", "0.01", "0.4", "0.999"):
                    sigma = delta**2*mp.mpf(fraction)
                    def null_fibre(v):
                        if v == 0:
                            return mp.mpf(0)
                        tau, r = (v+sigma/v)/2, (v-sigma/v)/2
                        return r**(d-2)/(2*v)*V(tau)
                    reference = n*ball*mp.quad(null_fibre, [mp.sqrt(sigma), delta])
                    self.assertLess(abs(planar_short_density56(d, sigma, delta)-reference), mp.mpf("1e-38"))
                self.assertEqual(planar_short_density56(d, delta**2, delta), 0)
                self.assertEqual(planar_short_density56(d, 2*delta**2, delta), 0)
                # A planar ball is NOT a quadratic overlap in these dimensions.
                t = mp.mpf("0.04")
                jet = V(0)+mp.diff(V, 0)*t+mp.diff(V, 0, 2)*t*t/2
                self.assertGreater(abs(V(t)-jet), mp.mpf("0.001"))

    def test_actual_planar_short_action_at_two_fixed_cutoffs(self):
        # This uses the full overlap in (S22), not a truncated Taylor model.
        with mp.workdps(40):
            for d in (5, 6):
                target = mp.mpf(str(s.N(sphere_area(d), 45)))/mp.mpf("0.5")
                for delta in (mp.mpf("0.1"), mp.mpf("0.18")):
                    errors = [abs(planar_short_action56(d, rho, delta)-target)
                              for rho in (10**18, 10**24)]
                    self.assertLess(errors[1], errors[0]/10)
                    self.assertLess(errors[1], mp.mpf("0.06"))

    def test_remainder_derivatives_and_first_unused_moving_endpoint(self):
        x, L, v = self.x, self.L, self.v
        for d, q in ((5, 3), (6, 4)):
            jacobian = self.radius**(d-2)/(2*v)
            F = s.expand(jacobian*self.tau**3)  # genuinely smooth primitive
            for order in range(d-2):
                self.assertEqual(s.simplify(s.diff(F, x, order).subs(v, s.sqrt(x))), 0)
            boundary = -s.diff(F, x, d-2).subs(v, s.sqrt(x))/(2*s.sqrt(x))
            expected = 3/(16*x) if d == 5 else -3/(8*x**s.Rational(3, 2))
            self.assertEqual(s.simplify(boundary-expected), 0)
            primitive = s.integrate(F, v)
            density = primitive.subs(v, L)-primitive.subs(v, s.sqrt(x))
            partial_primitive = s.integrate(s.diff(F, x, q), v)
            differentiated = partial_primitive.subs(v, L)-partial_primitive.subs(v, s.sqrt(x))
            self.assertEqual(s.simplify(s.diff(density, x, q)-differentiated), 0)
            # Chain/Leibniz envelope (S16) for this smooth cubic, T=6 suffices.
            for order in range(q+1):
                derivative = s.lambdify((x, v), s.diff(F, x, order), "numpy")
                constant = float(sum(s.binomial(order, i)*s.ff(d-2, i)
                                     for i in range(order+1))/2**(d-1))
                for value in (0.02, 0.2, 0.8):
                    for fraction in (0, 0.001, 0.5, 1):
                        self.assertLessEqual(abs(derivative(fraction*value**2, value)),
                                             6*constant*value**(d-2*order)*(1+1e-12))
            # Keep higher-order fractional/log terms even for a smooth remainder.
            primitive4 = s.integrate(s.expand(jacobian*self.tau**4), v)
            density4 = s.expand(primitive4.subs(v, L)-primitive4.subs(v, s.sqrt(x)))
            if d == 5:
                self.assertEqual(density4.coeff(x**s.Rational(7, 2)), s.Rational(1, 35))
            else:
                self.assertEqual(density4.coeff(s.log(x)), -3*x**4/512)
        u = s.symbols("u", positive=True)
        self.assertEqual(s.integrate(-(1-u)**2*s.log(u)/4, (u, 0, 1)), s.Rational(11, 72))
        self.assertEqual(s.integrate((1-u)**3/(6*s.sqrt(u)), (u, 0, 1)), s.Rational(16, 105))

    def test_diagnostic_domain_guards(self):
        for d in (True, 4, 7, 5.0):
            with self.assertRaises(ValueError):
                short_basis56_symbolic(d, self.x, self.L)
        for rho, delta, precision in ((0, 1, 60), (1, 0, 60), (math.inf, 1, 60), (1, 1, True)):
            with self.assertRaises(ValueError):
                jet_short_action56(5, [0]*4, rho, delta, dps=precision)
        with self.assertRaises(ValueError):
            jet_short_action56(6, [0]*3, 1, 1)
        with self.assertRaises(ValueError):
            ball_cos_overlap56(5, 0.1, (0.2, 0, 0, 0))
        with self.assertRaises(ValueError):
            ball_cos_jet56(6, height=0.45, bend=0.2)
        with self.assertRaises(ValueError):
            ball_cos_jet56(6, weight=lambda _: 1)
        for sigma, delta in ((-1, 0.1), (math.nan, 0.1), (0, 0.3)):
            with self.assertRaises(ValueError):
                planar_short_density56(6, sigma, delta)
        # The translation-independent planar overlap needs the strict envelope
        # budget, not merely a positive height and an integration interval.
        with self.assertRaises(ValueError):
            planar_short_density56(5, 0, 0.1, height=0.5)


if __name__ == "__main__":
    unittest.main()
