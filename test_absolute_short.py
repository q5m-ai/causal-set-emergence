"""Independent algebra for #97's partial direct-origin analytic backend.

These are signed-kernel/model checks, NOT a class-E limit proof. In particular
no high-density model evaluation is presented as the action of a region.
"""

import math
import unittest

import numpy as np
import sympy as sp

from short_displacement import jet_short_action, short_monomials


class AbsoluteShortTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sigma, cls.delta, cls.v = sp.symbols("sigma delta v", positive=True)
        sigma, delta, v = cls.sigma, cls.delta, cls.v
        time, radius = (v + sigma/v)/2, (v - sigma/v)/2
        jacobian = (v - sigma/v)**2/(8*v)
        cls.primitives = [sp.integrate(sp.expand(jacobian * monomial), v)
                          for monomial in (1, time, time**2, radius**2)]
        cls.densities = [sp.simplify(p.subs(v, delta) - p.subs(v, sp.sqrt(sigma)))
                         for p in cls.primitives]

    def test_actual_moving_endpoint_densities(self):
        sigma, delta = self.sigma, self.delta
        expected = [
            delta**2/16 - sigma*sp.log(delta)/4 - sigma**2/(16*delta**2)
            + sigma*sp.log(sigma)/8,
            delta**3/48 - sigma*delta/16 + sigma**2/(16*delta)
            - sigma**3/(48*delta**3),
            delta**4/128 - sigma**2*sp.log(delta)/16 - sigma**4/(128*delta**4)
            + sigma**2*sp.log(sigma)/32,
            delta**4/128 - sigma*delta**2/16 + 3*sigma**2*sp.log(delta)/16
            + sigma**3/(16*delta**2) - sigma**4/(128*delta**4)
            - 3*sigma**2*sp.log(sigma)/32,
        ]
        for actual, wanted in zip(self.densities, expected):
            self.assertEqual(sp.simplify(actual - wanted), 0)
        for cutoff, fraction in [(0.3, 0.01), (2., 0.4), (0.8, 0.9)]:
            proper_time = cutoff**2*fraction
            actual = np.array([float(f.subs({delta: cutoff, sigma: proper_time}))
                               for f in self.densities])
            np.testing.assert_allclose(short_monomials(proper_time, cutoff), actual,
                                       rtol=1e-8, atol=1e-15)

    def test_linear_lower_endpoint_cancels_but_constant_does_not(self):
        sigma, v = self.sigma, self.v
        self.assertEqual(sp.simplify(self.primitives[1].subs(v, sp.sqrt(sigma))), 0)
        self.assertEqual(sp.simplify(self.primitives[0].subs(v, sp.sqrt(sigma))),
                         -sigma*sp.log(sigma)/8)
        self.assertEqual(sp.simplify(self.primitives[2].subs(v, sp.sqrt(sigma))),
                         -sigma**2*sp.log(sigma)/32)

    def test_proper_time_relation_and_log_free_combination(self):
        sigma, delta = self.sigma, self.delta
        f0, _, ftt, frr = self.densities
        self.assertEqual(sp.simplify(ftt - frr - sigma*f0), 0)
        polynomial = (delta**4/96 - sigma*delta**2/48
                      + sigma**3/(48*delta**2) - sigma**4/(96*delta**4))
        self.assertEqual(sp.simplify(ftt + frr/3 - polynomial), 0)

    def test_signed_moments_and_complete_physical_normalization(self):
        j = sp.symbols("j", real=True)
        # Direct expansion of the original signed kernel, not fitted moments.
        coeffs = [1, -9, 8, -sp.Rational(4, 3)]
        moment = sum(a*sp.gamma((j + 2*k + 1)/2)/2 for k, a in enumerate(coeffs))
        for power in (0, 1, 2):
            self.assertEqual(sp.simplify(moment.subs(j, power)), 0)
        log_one = sp.simplify(sp.diff(moment, j).subs(j, 1))
        log_two = sp.simplify(sp.diff(moment, j).subs(j, 2))
        self.assertEqual(log_one, sp.Rational(1, 12))
        self.assertEqual(log_two, -sp.sqrt(sp.pi)/12)
        rho = sp.symbols("rho", positive=True)
        volume, alpha, beta = sp.symbols("volume alpha beta", real=True)
        c, normalization = sp.pi/24, 4/sp.sqrt(6)
        scale = sp.sqrt(c*rho)
        # The scale-dependent logarithms multiply zero signed moments.
        volume_pair = 4*sp.pi*volume/8 * scale**-2 * log_one
        self.assertEqual(sp.simplify(volume - rho*volume_pair), 0)
        quadratic_pair = (alpha - 3*beta)/32 * scale**-3 * log_two
        response = -normalization * rho**sp.Rational(3, 2) * quadratic_pair
        self.assertEqual(sp.simplify(response), (alpha - 3*beta)/(2*sp.pi))

    def test_finite_density_model_keeps_linear_and_cutoff_corrections(self):
        delta, rho = 0.7, 1e5
        # Signed model data; no geometric admissibility is claimed for it.
        volume, linear, alpha, beta = -0.2, 1.7, 3.1, -2.4
        angular = [4*math.pi*volume, linear, alpha, beta]
        c, normalization = math.pi/24, 4/math.sqrt(6)
        d3 = -linear/(48*delta**3) + beta/(16*delta**2)
        d4 = -(alpha + beta)/(128*delta**4)
        coefficient = (alpha - 3*beta)/(2*math.pi)
        predicted = coefficient + normalization*d3/(2*c**2*math.sqrt(rho))
        predicted += normalization*3*math.sqrt(math.pi)*d4/(2*c**2.5*rho)
        actual = jet_short_action(angular, rho, delta, order=80)
        # At these fixed parameters the omitted Gaussian tail is tiny; this
        # floating-point tolerance is diagnostic, not a certified error bound.
        self.assertAlmostEqual(actual, predicted, delta=3e-8)
        self.assertGreater(abs(predicted-coefficient), 1e-3)

    def test_steep_capsule_coefficient_is_only_an_analytic_calibration(self):
        slope = sp.Rational(3, 4)
        # Derived from the exact absolute overlap in the #85 note, retaining
        # the bulk future Hessian. It is not a global density-limit assertion.
        alpha = 4*sp.pi**2/slope
        beta = -4*sp.pi**2*slope/3
        coefficient = (alpha - 3*beta)/(2*sp.pi)
        # Independent future-normal/induced-area target on the t=0 sphere.
        cosh_angle = (1+slope**2)/(1-slope**2)
        joint = 4*sp.pi*cosh_angle/sp.sqrt(cosh_angle**2-1)
        self.assertEqual(sp.simplify(coefficient-joint), 0)
        self.assertEqual(sp.simplify(joint), 25*sp.pi/6)
        self.assertNotEqual(sp.simplify(alpha/(2*sp.pi)-joint), 0)


if __name__ == "__main__":
    unittest.main()
