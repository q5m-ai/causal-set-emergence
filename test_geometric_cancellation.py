"""Geometric and algebraic regressions; none proves an asymptotic estimate."""

from fractions import Fraction as F
import unittest

import numpy as np
import sympy as sp

from curved4_corrected_convergence import critical_exponents
from general_metric_gate import gauss_rule
from sphere_weighted_lenses import sphere_rule
import geometric_cancellation as gc


class GeometricCancellationTests(unittest.TestCase):
    def test_full_diamond_constant_density_and_both_scalings(self):
        for q in (0., 0.01, 0.8):
            for radius in (0.3, 3.):
                h = gc.conformal_diamond_factor([-.7, .2, -.1, .4], radius,
                                                [0, 0, 1], q, lambda t, x: 1)
                self.assertAlmostEqual(h, np.pi/24, places=13)
                scaled = gc.conformal_diamond_factor([-.7, .2, -.1, .4], radius,
                    [0, 0, 1], q, lambda t, x: 1.3**4)
                self.assertAlmostEqual(scaled/h, 1.3**4)

    def test_physical_quadratic_density_moment(self):
        # Density = 1 + t**2 + |x|**2, not a frozen source value. D0 has
        # E[A**2]=1/60 and E[B_i**2]=1/30; compute independently after boost.
        source = np.array([-.7, .2, -.1, .4])
        radius, q = 2.1, .3
        direction = np.array([1., 2., -1.])/np.sqrt(6)
        tau = np.sqrt(radius*radius+q)
        center = source[1:]+radius*direction/2
        expected = (1+(source[0]+tau/2)**2+center@center
                    + tau*tau/60+radius*radius/30
                    + radius*radius/60+tau*tau/30+2*q/30)
        h = gc.conformal_diamond_factor(source, radius, direction, q,
            lambda t, x: 1+t*t+np.sum(x*x, axis=-1))
        self.assertAlmostEqual(h/(np.pi/24), expected, places=11)
        self.assertGreater(abs(expected-(1+source@source)), 0.5)

    def test_canonical_signed_polynomials_from_actual_kernel(self):
        z = sp.symbols('z', positive=True)
        k = (1-9*z*z+8*z**4-sp.Rational(4, 3)*z**6)*sp.exp(-z*z)
        for j in range(3):
            self.assertEqual(sp.integrate(z**j*k, (z, 0, sp.oo)), 0)
        # A log at critical primitive order is not killed like the pure cubic.
        p = sp.symbols('p')
        multiplier = sp.prod(1-2*p/j for j in (1, 2, 3))
        self.assertNotEqual(sp.diff(multiplier, p).subs(p, sp.Rational(3, 2)), 0)

    def test_strict_geometric_abundance_threshold(self):
        sphere = critical_exponents(1, 1, F(1, 2))
        quartic = critical_exponents(F(3, 2), 2, F(1, 2))
        self.assertEqual(sphere['cubic_majorant'], F(-1, 4))
        self.assertTrue(sphere['summable'])
        self.assertEqual(quartic['cubic_majorant'], F(-7, 4))
        self.assertFalse(quartic['summable'])
        self.assertFalse(critical_exponents(F(1, 4), 1, F(1, 2))['summable'])

    def test_two_face_and_shell_rank_at_joint(self):
        # Columns dx^0,...,dx^3,dr. The shell has dt(k)>0; joint
        # transversality must still be used rather than assuming smoothness.
        x = np.array([1., 0., 0.])
        s, eps = 0.6, 0.2
        alpha_minus = np.r_[1., -(np.array([eps, 0, 0])+s*x)]
        alpha_plus = np.r_[1., -(np.array([eps, 0, 0])-s*x)]
        for n in ([1., 0., 0.], [-1., 0., 0.], [0., 1., 0.]):
            k = np.r_[1., n]
            rows = np.array([np.r_[alpha_minus, 0.],
                             np.r_[alpha_plus, alpha_plus@k], [0., 0., 0., 0., 1.]])
            self.assertGreater(np.linalg.svd(rows, compute_uv=False)[-1], 0.2)
        # Coincident normals lose rank, illustrating why transversality matters.
        bad = np.array([np.r_[alpha_minus, 0.], np.r_[alpha_minus, 1.],
                        [0., 0., 0., 0., 1.]])
        self.assertEqual(np.linalg.matrix_rank(bad), 2)

    def test_independent_variable_angle_joint_integral(self):
        s, eps, b = .6, .2, .1
        points, weights = sphere_rule(24)
        _, angles, areas = gc.capsule_joint_data(points, s, eps, b)
        target = np.sum(weights*angles*areas)
        expected = 2*np.pi/s*(1-eps*eps+s*s)*(1+b)**2
        self.assertAlmostEqual(target/expected, 1, places=12)
        self.assertGreater(np.max(angles)-np.min(angles), 0.01)
        self.assertGreater(np.max(areas)-np.min(areas), 0.01)

    def test_bulk_target_by_independent_radial_integration(self):
        s, b = .6, .1
        n, w = gauss_rule(20)
        actual = 4*np.pi*np.sum(w*n*n*s*(1-n*n)*(-18*b*(1+b*n*n)))
        expected = -144*np.pi*b*s*(1/15+b/35)
        self.assertAlmostEqual(actual, expected, places=13)
        self.assertLess(actual, 0)

    def test_capsule_ambient_containment_via_separate_envelopes(self):
        s, eps = .6, .2
        # Finite negative control only; the proof uses their global Lipschitz
        # constants, not samples. Check a causal segment between interior points.
        lower = lambda x: eps*x[0]-s*max(0, 1-x@x)/2
        upper = lambda x: eps*x[0]+s*max(0, 1-x@x)/2
        x, y = np.array([-.1, .02, .03]), np.array([.1, -.02, -.03])
        t0, t1 = lower(x)+.01, upper(y)-.01
        self.assertGreater(t1-t0, np.linalg.norm(y-x))
        for a in np.linspace(0, 1, 31):
            point, time = (1-a)*x+a*y, (1-a)*t0+a*t1
            self.assertGreater(time, lower(point))
            self.assertLess(time, upper(point))

    def test_failed_tip_dominator_is_not_a_counterexample(self):
        self.assertGreater(gc.optical_tip_dominator(2, 1e-8),
                           gc.optical_tip_dominator(2, 1e-4))
        self.assertAlmostEqual(gc.optical_tip_dominator(2, 1e-8), -np.log(1e-8))
        # Flat optical geometry has the same pessimistic interior scaling,
        # yet its exact volume factor is constant, with no logarithmic term.
        values = [gc.conformal_diamond_factor([0, 0, 0, 0], 2, [1, 0, 0], e,
                                              lambda t, x: 1) for e in (0, 1e-4, 1e-2)]
        np.testing.assert_allclose(values, np.pi/24, atol=2e-14)

    def test_unchanged_complete_action_constant_conformal_scaling(self):
        rho, c, mass, pair = sp.symbols('rho c mass pair', positive=True)
        actual = sp.sqrt(rho)*c**4*mass-rho**sp.Rational(3, 2)*c**8*pair
        rescaled = c**2*(sp.sqrt(rho*c**4)*mass-(rho*c**4)**sp.Rational(3, 2)*pair)
        self.assertEqual(sp.simplify(actual-rescaled), 0)
        # Preserved quartic obstruction under constant scaling, not arbitrary
        # weighted model-sign continuity inferred from order invariance.
        self.assertEqual(2+4*sp.Rational(3, 14), sp.Rational(20, 7))

    def test_invalid_parameters(self):
        with self.assertRaises(ValueError):
            gc.conformal_diamond_factor([0, 0, 0, 0], 0, [1, 0, 0], .1, lambda t, x: 1)
        with self.assertRaises(ValueError):
            gc.conformal_diamond_factor([0, 0, 0, 0], 1, [1, 1, 0], .1, lambda t, x: 1)
        with self.assertRaises(ValueError):
            gc.capsule_joint_data([1, 0, 0], .6, .5, .1)
        with self.assertRaises(ValueError):
            gc.optical_tip_dominator(2, 0)


if __name__ == '__main__':
    unittest.main()
