"""Independent regressions for the written #84 theorem, not a Lean proof."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
from scipy.stats import binom, poisson
import sympy as s

import mixed_poisson as mp
import null_mixed as nm


def in_region(height, point):
    t, x = point[0], np.asarray(point[1:])
    return -height(x) < t < -np.linalg.norm(x)


def causal(p, q):
    delta = np.asarray(q) - np.asarray(p)
    return delta[0] >= 0 and np.dot(delta[1:], delta[1:]) <= delta[0]**2


def interval_from_source(p, rest_point):
    """Lorentz map from I(0,(D,0)) to I(p,0), with no region assumption."""
    p, rest_point = np.asarray(p), np.asarray(rest_point)
    duration = math.sqrt(p[0]**2 - np.dot(p[1:], p[1:]))
    velocity = p[1:] / p[0]
    speed_sq = np.dot(velocity, velocity)
    gamma = -p[0] / duration
    t, x = rest_point[0], rest_point[1:]
    dot = np.dot(velocity, x)
    shift = ((gamma - 1) * dot / speed_sq if speed_sq else 0) + gamma * t
    return p + np.r_[gamma * (t + dot), x + shift * velocity]


class MixedPoissonTests(unittest.TestCase):
    def test_actual_order_counts_normalization_and_permutation(self):
        # Five points strictly in the round mixed region. Endpoints are not
        # counted as interior elements: the four nonempty layers are 4,3,2,1.
        chain = np.c_[np.linspace(-0.9, -0.1, 5), np.zeros((5, 3))]
        self.assertTrue(all(in_region(lambda x: 1, p) for p in chain))
        self.assertEqual(mp.layer_counts(chain), (4, 3, 2, 1))
        for rho in (0.5, 12, 100):
            self.assertAlmostEqual(mp.discrete_action(rho, chain),
                                   4 * nm.ACTION_CONSTANT / math.sqrt(rho))
            self.assertEqual(mp.discrete_action(rho, chain[[3, 0, 4, 1, 2]]),
                             mp.discrete_action(rho, chain))
        # More than three interior elements must contribute no layer weight.
        long_chain = np.c_[np.linspace(-0.9, -0.1, 7), np.zeros((7, 3))]
        self.assertEqual(mp.layer_counts(long_chain), (6, 5, 4, 3))
        self.assertEqual(mp.layer_counts([]), (0, 0, 0, 0))
        self.assertEqual(mp.discrete_action(1, []), 0)
        self.assertAlmostEqual(mp.discrete_action(1, [[-0.5, 0, 0, 0]]), nm.ACTION_CONSTANT)

    def test_closed_null_order_and_spacelike_negative_control(self):
        # Binary-exact coordinates avoid rounding an intended null relation.
        points = [[-0.75, 0, 0, 0], [-0.5, 0.25, 0, 0]]
        self.assertEqual(mp.layer_counts(points), (1, 0, 0, 0))
        self.assertAlmostEqual(mp.discrete_action(1, points), nm.ACTION_CONSTANT)
        points[1][0] = -0.75
        self.assertEqual(mp.layer_counts(points), (0, 0, 0, 0))
        self.assertAlmostEqual(mp.discrete_action(1, points), 2 * nm.ACTION_CONSTANT)

    def test_splitting_into_chart_actions_loses_cross_pairs(self):
        left = [[-0.8, -0.1, 0, 0]]
        right = [[-0.4, 0.1, 0, 0]]
        self.assertTrue(all(in_region(lambda x: 1, p) for p in left + right))
        self.assertEqual(mp.layer_counts(left + right), (1, 0, 0, 0))
        full = mp.discrete_action(10, left + right)
        disjoint_chart_sum = mp.discrete_action(10, left) + mp.discrete_action(10, right)
        self.assertAlmostEqual(disjoint_chart_sum - full, nm.ACTION_CONSTANT / math.sqrt(10))

    def test_boosted_full_future_intervals_for_two_nonround_profiles(self):
        profiles = [lambda x: 1 + 0.2 * math.sin(x[0]),
                    lambda x: 1 + 0.6*x[0] - 0.2*x[1]]
        self.assertLess(profiles[1](np.array([-3, 0, 0])), 0)  # allowed exterior
        for height in profiles:
            for x in (np.array([0., 0., 0.]), np.array([0.2, -0.1, 0.15]),
                      np.array([-0.3, 0.1, 0.])):
                r = np.linalg.norm(x)
                p = np.r_[-(height(x) + r) / 2, x]
                self.assertTrue(in_region(height, p))
                duration = math.sqrt(p[0]**2 - r**2)
                for f in (0.1, 0.3, 0.7, 0.9):
                    for direction in np.r_[np.eye(3), -np.eye(3)]:
                        rest = np.r_[f*duration, 0.8 * min(f, 1-f) * duration * direction]
                        q = interval_from_source(p, rest)
                        self.assertTrue(causal(p, q))
                        self.assertTrue(causal(q, np.zeros(4)))
                        self.assertTrue(in_region(height, q))
                        self.assertGreater(q[0] + height(q[1:]), 0)
                        # Closed subintervals, not just endpoints or one ray.
                        z = 0.4*p + 0.6*q
                        self.assertTrue(in_region(height, z))
                self.assertFalse(in_region(height, np.zeros(4)))  # tip not in open M
                np.testing.assert_allclose(interval_from_source(p, [duration, 0, 0, 0]),
                                           np.zeros(4), atol=5e-16)

    def test_frontier_types_and_no_lateral_wall(self):
        cap = nm.SineMixedCap()
        height = lambda x: 1 + 0.2*math.sin(x[0])
        for mu in (-0.8, 0.2, 0.9):
            omega = np.array([mu, math.sqrt(1-mu**2), 0])
            R = cap.joint_radius(mu)
            x = 0.4*R*omega
            r = np.linalg.norm(x)
            eps = 1e-5
            self.assertTrue(in_region(height, np.r_[-height(x) + eps, x]))
            self.assertFalse(in_region(height, np.r_[-height(x) - eps, x]))
            self.assertTrue(in_region(height, np.r_[-r - eps, x]))
            self.assertFalse(in_region(height, np.r_[-r + eps, x]))
            self.assertAlmostEqual(height(R*omega), R, places=11)
            x_inside, x_outside = (R-eps)*omega, (R+eps)*omega
            self.assertGreater(height(x_inside), np.linalg.norm(x_inside))
            self.assertLess(height(x_outside), np.linalg.norm(x_outside))
        self.assertTrue(in_region(height, [-1 + 1e-5, 0, 0, 0]))  # smooth lower point
        self.assertTrue(in_region(height, [-1e-5, 0, 0, 0]))  # approach unique tip
        self.assertFalse(in_region(height, [1e-5, 0, 0, 0]))

    def test_closed_containment_is_essential_for_the_poisson_rate(self):
        # Removing a middle time band leaves the endpoints but removes a
        # positive-volume subset of their ambient interval.
        p, q = np.array([-0.8, 0, 0, 0]), np.array([-0.2, 0, 0, 0])
        z = (p + q) / 2
        punctured = lambda a: in_region(lambda x: 1, a) and not -0.6 < a[0] < -0.4
        self.assertTrue(punctured(p) and punctured(q))
        self.assertTrue(causal(p, z) and causal(z, q))
        self.assertFalse(punctured(z))
        duration = q[0] - p[0]
        removed = quad(lambda t: 4*math.pi/3 * min(t, duration-t)**3,
                       0.2, 0.4, points=[duration/2])[0]
        ambient = math.pi * duration**4 / 24
        self.assertGreater(removed, 0)
        self.assertLess(removed, ambient)
        self.assertNotAlmostEqual(ambient - removed, ambient)

    def test_independent_joint_metric_and_affine_area(self):
        # Use an orthonormal sphere frame. Derivatives of R can be arbitrary:
        # Lorentzian Gram determinant cancels them, Euclidean one does not.
        R, a, b = s.symbols("R a b", positive=True)
        tangent = s.Matrix([[-a, -b], [a, b], [R, 0], [0, R]])
        screen = tangent.T * s.diag(-1, 1, 1, 1) * tangent
        self.assertEqual(s.simplify(screen), s.diag(R**2, R**2))
        euclidean = tangent.T * tangent
        self.assertEqual(s.factor(euclidean.det()), R**2 * (R**2 + 2*a**2 + 2*b**2))
        # Independent non-round affine calibration; H may be negative outside.
        for slope in (0.2, 0.6):
            area = 2*math.pi * quad(lambda mu: 1/(1-slope*mu)**2, -1, 1)[0]
            self.assertAlmostEqual(area, 4*math.pi/(1-slope**2), places=11)

    def test_poisson_factorials_recover_original_kernel_not_layer_polynomial(self):
        z = s.symbols("z", nonnegative=True)
        weights = [1, -9, 16, -8]
        kernel = sum(weights[k] * z**k / s.factorial(k) for k in range(4)) * s.exp(-z)
        expected = (1 - 9*z + 8*z**2 - s.Rational(4, 3)*z**3) * s.exp(-z)
        self.assertEqual(s.simplify(kernel - expected), 0)
        wrong = sum(weights[k] * z**k for k in range(4)) * s.exp(-z)
        self.assertNotEqual(s.simplify(wrong - expected), 0)

    def test_poisson_cardinality_mixture_excludes_inserted_endpoints(self):
        # Conditional on N and two marked positions, only N-2 independent
        # points can be in their interval. Sum the actual cardinality mixture,
        # rather than assuming a Poisson interior count in this regression.
        for mean, fraction in ((0.5, 0.3), (8, 0.1), (20, 0.7)):
            n = np.arange(2, 160)
            pair_factor = n * (n - 1) * poisson.pmf(n, mean)
            for k in range(4):
                mixture = np.sum(pair_factor * binom.pmf(k, n-2, fraction))
                expected = mean**2 * poisson.pmf(k, mean*fraction)
                self.assertAlmostEqual(mixture, expected, delta=2e-12)
            wrong = np.sum(pair_factor * binom.pmf(0, n, fraction))
            right = mean**2 * math.exp(-mean*fraction)
            self.assertGreater(abs(wrong - right), 1e-5)

    def test_positive_partner_layers_before_signed_cancellation(self):
        for rho, sigma in ((0.5, 0.04), (20, 0.7), (100, 1)):
            layers = mp.interval_layer_integrals(rho, sigma, order=28)
            self.assertTrue(np.all(layers > 0))
            np.testing.assert_allclose(layers, mp.interval_layer_integrals(rho, sigma, 20),
                                       atol=2e-12, rtol=2e-10)
            signed = layers @ np.array([1, -9, 16, -8])
            self.assertAlmostEqual(1-rho*signed,
                                   math.exp(-nm.INTERVAL_CONSTANT*rho*sigma**2), delta=2e-11)
            self.assertLessEqual(sum(layers), nm.INTERVAL_CONSTANT*sigma**2)
        np.testing.assert_array_equal(mp.interval_layer_integrals(1, 0), np.zeros(4))

    def test_independent_expected_layers_round_and_sine(self):
        for cap in (nm.SineMixedCap(epsilon=0), nm.SineMixedCap()):
            for rho in (2, 25, 100):
                low = mp.mixed_layer_means(cap, rho, 16, 16)
                high = mp.mixed_layer_means(cap, rho, 24, 24)
                self.assertAlmostEqual(high.points, rho * cap.volume(), delta=1e-10)
                self.assertTrue(all(x > 0 for x in high.layers))
                np.testing.assert_allclose(low.layers, high.layers, atol=2e-8, rtol=2e-8)
                self.assertAlmostEqual(high.action(), cap.action(rho, 48), delta=2e-7)
                self.assertLess(high.action(), cap.joint_area())  # finite, not the target itself
                # Missing the second intensity or counting unordered pairs
                # changes all four means by a common incorrect factor.
                point, pair = high.points, np.dot(high.layers, [1, -9, 16, -8])
                for divisor in (rho, 2):
                    wrong = nm.ACTION_CONSTANT / math.sqrt(rho) * (point - pair/divisor)
                    self.assertGreater(abs(wrong - high.action()), 0.01)

    def test_invalid_inputs(self):
        for points in ([[0, 0, 0]], [[0, 0, 0, math.nan]], [[0, 0, 0, 0]]*2,
                       np.empty((0, 3))):
            with self.assertRaises(ValueError):
                mp.layer_counts(points)
        for rho in (0, -1, math.nan, math.inf):
            with self.assertRaises(ValueError):
                mp.discrete_action(rho, [])
            with self.assertRaises(ValueError):
                mp.mixed_layer_means(nm.SineMixedCap(), rho)
        for sigma in (-1, math.nan, math.inf):
            with self.assertRaises(ValueError):
                mp.interval_layer_integrals(1, sigma)
        for order in (True, 0, 3, 8.5):
            with self.assertRaises(ValueError):
                mp.interval_layer_integrals(1, 1, order)
        with self.assertRaises(TypeError):
            mp.mixed_layer_means(None, 1)


if __name__ == "__main__":
    unittest.main()
