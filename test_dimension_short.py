"""Independent regressions for the conventional SmoothPilot3 short proof.

No numerical/model check is advertised as a Lean theorem or a global limit.
"""

import math
import unittest

from mpmath import mp
import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_joint_geometry import joint_point_geometry
from dimension_kernels import (
    action_constants, interval_coefficient, kernel_polynomial, plane_moment,
    transverse_moment, Z,
)
from dimension_short import (
    ball_cos_jet3, ball_cos_overlap3, jet_short_action3,
    short_basis3, short_basis3_symbolic,
)
from short_displacement import short_monomials


class DimensionShortTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sigma, cls.delta, cls.v = s.symbols("sigma delta v", positive=True)
        sigma, delta, v = cls.sigma, cls.delta, cls.v
        cls.tau, cls.radius = (v+sigma/v)/2, (v-sigma/v)/2
        cls.jacobian = (1-sigma/v**2)/4
        cls.densities = short_basis3_symbolic(sigma, delta)

    def test_polar_jacobian_and_moving_endpoints(self):
        sigma, delta, v = self.sigma, self.delta, self.v
        transform = s.Matrix([self.tau, self.radius]).jacobian([sigma, v])
        self.assertEqual(s.simplify(transform.det()), 1/(2*v))
        self.assertEqual(s.simplify(self.radius*transform.det()-self.jacobian), 0)
        for density, monomial in zip(self.densities,
                                      (1, self.tau, self.tau**2, self.radius**2)):
            primitive = s.integrate(s.expand(self.jacobian*monomial), v)
            actual = primitive.subs(v, delta)-primitive.subs(v, s.sqrt(sigma))
            self.assertEqual(s.simplify(actual-density), 0)
            self.assertEqual(s.simplify(density.subs(sigma, delta**2)), 0)
        self.assertEqual(s.simplify(self.densities[2]-self.densities[3]
                                   -sigma*self.densities[0]), 0)
        # Lower-endpoint contributions must not be discarded as in 4D.
        self.assertEqual(s.expand(self.densities[0]).coeff(s.sqrt(sigma)), -s.Rational(1, 2))
        self.assertEqual(s.expand(self.densities[2]).coeff(sigma**s.Rational(3, 2)), -s.Rational(1, 6))
        self.assertEqual(s.expand(self.densities[3]).coeff(sigma**s.Rational(3, 2)), s.Rational(1, 3))
        self.assertTrue(self.densities[1].is_polynomial(sigma))

    def test_stable_sharp_fibres_and_null_vertex(self):
        for delta in (0.2, 1.3):
            for fraction in (0.0, 0.05, 0.6, 0.999, np.nextafter(1.0, 0.0)):
                sigma = delta**2*fraction
                actual = short_basis3(sigma, delta)
                with mp.workdps(60):
                    sig, cut = mp.mpf(float(sigma)), mp.mpf(delta)
                    root = mp.sqrt(sig)
                    reference = []
                    for mode in range(4):
                        def fibre(v):
                            tau, r = (v+sig/v)/2, (v-sig/v)/2
                            return r/(2*v)*(1, tau, tau*tau, r*r)[mode]
                        reference.append(float(mp.quad(fibre, [root, cut])))
                # Extremely close endpoints inherit float rounding in delta^2.
                np.testing.assert_allclose(actual, reference, rtol=2e-10, atol=1e-29)
            np.testing.assert_array_equal(short_basis3(delta**2, delta), np.zeros(4))
            np.testing.assert_array_equal(short_basis3(2*delta**2, delta), np.zeros(4))
        for sigma, delta in ((-1, 1), (math.nan, 1), (0, 0), (0, math.inf)):
            with self.assertRaises(ValueError):
                short_basis3(sigma, delta)

    def test_signed_half_moments_and_all_normalizations(self):
        self.assertEqual(kernel_polynomial(3), 1-27*Z/8+9*Z**2/8)
        j = s.symbols("j", real=True)
        # Independent direct polynomial/Gamma calculation.
        moment = sum(coef*s.Rational(2, 3)*s.gamma(s.Rational(2, 3)*(j+1)+k)
                     for k, coef in enumerate((1, -s.Rational(27, 8), s.Rational(9, 8))))
        wanted = (0, -s.Rational(1, 12), 0, s.gamma(s.Rational(5, 3))/4)
        for order, expected in zip((0, s.Rational(1, 2), 1, s.Rational(3, 2)), wanted):
            self.assertEqual(s.simplify(moment.subs(j, order)-expected), 0)
        a, beta = action_constants(3)
        c = interval_coefficient(3)
        self.assertEqual(c, s.pi/12)
        self.assertEqual(a, beta)
        self.assertEqual(s.simplify(beta*s.pi/(12*c)-a), 0)
        response = -beta*c**(-s.Rational(5, 3))*moment.subs(j, s.Rational(3, 2))
        self.assertEqual(s.simplify(-response/6), 1/s.pi)
        self.assertEqual(s.simplify(response/3), -2/s.pi)
        self.assertGreater(float(plane_moment(3, 1)), 0)
        self.assertEqual(plane_moment(4, 1), 0)
        with self.assertRaises(ValueError):
            plane_moment(4, 2)

    def test_finite_density_model_independent_signed_quadrature(self):
        with mp.workdps(50):
            angular = [mp.mpf(x) for x in ("-0.2", "1.7", "3.1", "-2.4")]
            rho, delta = mp.mpf(700), mp.mpf("0.7")
            c = mp.pi/12
            norm = 2*c**(mp.mpf(2)/3)/mp.gamma(mp.mpf(5)/3)
            # x=sqrt(sigma) removes every fractional endpoint singularity.
            def fibre(x):
                sig = x*x
                basis = [delta/4+sig/(4*delta)-x/2,
                         delta**2/16-sig/8+sig**2/(16*delta**2),
                         delta**3/48+sig*delta/16+sig**2/(16*delta)
                         +sig**3/(48*delta**3)-x**3/6,
                         delta**3/48-3*sig*delta/16-3*sig**2/(16*delta)
                         +sig**3/(48*delta**3)+x**3/3]
                z = c*rho*x**3
                return 2*x*mp.fdot(angular, basis)*(1-27*z/8+9*z*z/8)*mp.exp(-z)
            pair = mp.quad(fibre, [0, delta/4, delta/2, delta])
            reference = norm*rho**(mp.mpf(2)/3)*(angular[0]/(2*mp.pi)-rho*pair)
            self.assertLess(abs(jet_short_action3(angular, rho, delta)-reference), mp.mpf("1e-43"))

    def test_actual_planar_short_action_at_two_fixed_cutoffs(self):
        # Unit disk, h=a(1-|x|^2), f=0: exact overlap is quadratic for tau<a.
        with mp.workdps(50):
            a = mp.mpf("0.25")
            angular = [mp.pi**2*a, -2*mp.pi**2, mp.pi**2/a, 0]
            target = mp.pi/a
            for delta in (mp.mpf("0.1"), mp.mpf("0.2")):
                errors = [abs(jet_short_action3(angular, rho, delta)-target)
                          for rho in (10**12, 10**15, 10**18)]
                self.assertGreater(errors[0], errors[1])
                self.assertGreater(errors[1], errors[2])
                self.assertLess(errors[2], mp.mpf("0.001"))
            # Regression includes a null displacement, not just vertical slices.
            for tau, spatial in ((0, (0, 0)), (0.04, (0.04, 0)), (0.08, (0.02, 0.03))):
                expected = float(mp.pi*a/2*(1-mp.mpf(tau)/a)**2)
                self.assertAlmostEqual(ball_cos_overlap3(tau, spatial, bend=0), expected, delta=2e-11)

    def test_actual_curved_overlap_two_jet_with_nonzero_hessian(self):
        a, epsilon = 0.25, 0.125
        # Actual fixed-domain and full-circle source coefficients; no target used.
        jet = ball_cos_jet3(height=a, bend=epsilon)
        self.assertLess(jet["future_hessian"], -0.3)
        volume = math.pi*a/2
        surface_q2 = quad(lambda t: (epsilon*math.sin(math.cos(t)))**2/(2*a),
                          0, 2*math.pi)[0]
        # f depends only on x_1. Its bulk gradient integrates to zero by parity.
        for direction in ((0, 0), (0.5, 0), (0, 0.5), (-0.3, 0.4)):
            remainders = []
            for tau in (0.032, 0.016, 0.008):
                bx, by = (tau*x for x in direction)
                polynomial = (volume-math.pi*tau + math.pi*tau*tau/(2*a)
                              + (jet["future_hessian"]+surface_q2)*bx*bx/2)
                actual = ball_cos_overlap3(tau, (bx, by), height=a, bend=epsilon)
                remainders.append(abs(actual-polynomial))
                self.assertLess(abs(actual-polynomial), 3*tau**3)
            # A value regression, not a substitute for the written derivative proof.
            self.assertLess(remainders[-1], remainders[0]/20 + 1e-11)
        with self.assertRaises(ValueError):
            ball_cos_overlap3(0.1, (0.2, 0))
        with self.assertRaises(ValueError):
            ball_cos_overlap3(0.1, (0, 0), height=0.45, bend=0.2)

    def test_independent_normal_gram_target_and_signed_partition(self):
        a, epsilon = 0.25, 0.125
        weights = [(lambda x: 1.0, lambda x: 0.0),
                   (lambda x: 2*x*x-0.5, lambda x: 4*x),
                   (lambda x: 1.5-2*x*x, lambda x: -4*x)]
        jets = []
        for w, wp in weights:
            jet = ball_cos_jet3(height=a, bend=epsilon, weight=w, weight_prime=wp)
            def target(theta):
                x, y = math.cos(theta), math.sin(theta)
                geometry = joint_point_geometry(3, (-2*a*x, -2*a*y),
                                                 (-epsilon*math.sin(x), 0))
                return w(x)*float(geometry.weight*geometry.area_density)
            independent = quad(target, 0, 2*math.pi, epsabs=2e-11)[0]
            self.assertAlmostEqual(jet["short_coefficient"],
                                   independent+jet["partition_derivative"], delta=3e-11)
            jets.append(jet)
        self.assertGreater(abs(jets[1]["partition_derivative"]), 0.1)
        self.assertAlmostEqual(jets[1]["partition_derivative"]+jets[2]["partition_derivative"], 0)
        np.testing.assert_allclose(jets[1]["angular"]+jets[2]["angular"], jets[0]["angular"], atol=2e-12)
        # Leaving out the future Hessian genuinely changes the answer.
        self.assertGreater(abs(jets[0]["future_hessian"]), 0.1)
        # Signed source partition retains all partners, also at finite displacement.
        actual = [ball_cos_overlap3(0.04, (0.025, 0.01), weight=w) for w, _ in weights]
        self.assertAlmostEqual(actual[1]+actual[2], actual[0], delta=2e-12)

    def test_derivative_remainder_keeps_logarithm_and_endpoint(self):
        sigma, delta, v = self.sigma, self.delta, self.v
        # R=|b|^3 is C^2 with the required derivative bounds; it produces a log.
        integrand = s.expand(self.jacobian*self.radius**3)
        primitive = s.integrate(integrand, v)
        density = s.expand(primitive.subs(v, delta)-primitive.subs(v, s.sqrt(sigma)))
        self.assertEqual(density.coeff(s.log(sigma)), -3*sigma**2/32)
        residual = density-delta**4/128+sigma*delta**2/16
        self.assertEqual(s.limit(residual/sigma**s.Rational(3, 2), sigma, 0, dir="+"), 0)
        # For R=tau^3 the B'' Leibniz boundary term is nonzero: +1/8.
        time_integrand = self.jacobian*self.tau**3
        boundary = -s.diff(time_integrand, sigma).subs(v, s.sqrt(sigma))/(2*s.sqrt(sigma))
        self.assertEqual(s.simplify(boundary), s.Rational(1, 8))
        # Integrate the derived B'' logarithmic bound, including that term.
        u = s.symbols("u", positive=True)
        integral = s.integrate((1-u)*(-s.log(u)/2), (u, 0, 1))
        self.assertEqual(integral, s.Rational(3, 8))
        self.assertEqual(s.Rational(3, 2)*integral+s.Rational(1, 8), s.Rational(11, 16))

    def test_dimension_four_measure_and_basis_unchanged(self):
        sigma, delta, v = self.sigma, self.delta, self.v
        jacobian4 = self.radius**2/(2*v)
        for index, monomial in enumerate((1, self.tau, self.tau**2, self.radius**2)):
            primitive = s.integrate(s.expand(jacobian4*monomial), v)
            density = primitive.subs(v, delta)-primitive.subs(v, s.sqrt(sigma))
            for cutoff, fraction in ((0.3, 0.1), (1.2, 0.7)):
                proper_time = cutoff**2*fraction
                expected = float(density.subs({sigma: proper_time, delta: cutoff}))
                self.assertAlmostEqual(short_monomials(proper_time, cutoff)[index], expected, delta=2e-15)
        # Replacing the 3D response by the 4D coefficient is not compatible.
        alpha, beta = 3.1, -2.4
        self.assertNotAlmostEqual((alpha-2*beta)/math.pi, (alpha-3*beta)/(2*math.pi))


if __name__ == "__main__":
    unittest.main()
