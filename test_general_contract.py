"""Algebra/example diagnostics for #90, NOT proofs of BDG asymptotics.

The scope decisions and their conventional arguments are in
notes/general-contract.md. No numerical test certifies admissibility for an
arbitrary region, global topology, a Poisson bridge, or a density limit.
"""

import math
import unittest

import numpy as np
import sympy as s
from scipy.optimize import brentq

from dimension_kernels import action_constants, layer_coefficients


class GeneralContractTests(unittest.TestCase):
    def test_minimal_layer_normalization_and_exclusive_index(self):
        # Coefficients of N, L_0, ... in the independently defined observable.
        for d, expected in [(2, [2, -4, 8, -4]),
                            (4, [1, -1, 9, -16, 8])]:
            a, beta = action_constants(d)
            actual = [a] + [-beta * c for c in layer_coefficients(d)]
            if d == 4:
                actual = [s.simplify(c / (4 / s.sqrt(6))) for c in actual]
            self.assertEqual(actual, list(map(s.Integer, expected)))

    def test_curvature_sign_from_christoffels(self):
        # Compute independently from g, using precisely the Riemann sign in §2.
        t, x, y, z, b = s.symbols("t x y z b", real=True)
        coordinates = (t, x, y, z)
        omega = 1 + b * t**2
        metric = s.diag(omega**2, -omega**2, -omega**2, -omega**2)
        inverse = metric.inv()
        gamma = [[[s.simplify(sum(inverse[a, e] * (
            s.diff(metric[e, c], coordinates[q])
            + s.diff(metric[e, q], coordinates[c])
            - s.diff(metric[q, c], coordinates[e])) / 2
            for e in range(4))) for c in range(4)] for q in range(4)]
            for a in range(4)]
        ricci = s.zeros(4)
        for q in range(4):
            for d in range(4):
                ricci[q, d] = sum(
                    s.diff(gamma[a][a][q], coordinates[d])
                    - s.diff(gamma[a][d][q], coordinates[a])
                    + sum(gamma[a][d][e] * gamma[e][a][q]
                          - gamma[a][a][e] * gamma[e][d][q]
                          for e in range(4))
                    for a in range(4))
        scalar = s.simplify(s.trace(inverse * ricci))
        self.assertEqual(s.factor(scalar - 12 * b / omega**3), 0)
        self.assertEqual(scalar.subs(b, 0), 0)
        self.assertEqual(scalar.subs(t, 0), 12 * b)

    def test_steep_capsule_individual_bounds_fail_old_height(self):
        slope = s.Rational(3, 4)
        r = s.symbols("r", nonnegative=True)
        upper = slope * (1 - r**2) / 2
        lower = -upper
        thickness = upper - lower
        self.assertEqual(abs(s.diff(upper, r).subs(r, 1)), slope)
        self.assertEqual(abs(s.diff(lower, r).subs(r, 1)), slope)
        self.assertEqual(abs(s.diff(thickness, r).subs(r, 1)), 2 * slope)
        self.assertLess(slope, 1)
        self.assertGreater(2 * slope, 1)
        self.assertGreater(3 * slope, 1)

    def test_steep_obstruction_in_every_common_boost(self):
        slope, v = s.symbols("s v", real=True)
        u = (slope + v) / (1 + slope * v)
        opposite = (v - slope) / (1 - slope * v)
        delta = 2 * slope * (1 - v**2) / (1 - slope**2 * v**2)
        self.assertEqual(s.factor(u - opposite - delta), 0)
        numerator = (1 - v) * (3 * slope - 1 + (3 * slope - slope**2) * v)
        self.assertEqual(s.factor(u + delta - 1
                                 - numerator / (1 - slope**2 * v**2)), 0)
        # The factors prove positivity for s=3/4, 0<=v<1; samples are guards.
        self.assertEqual(3 * s.Rational(3, 4) - 1, s.Rational(5, 4))
        self.assertGreater(3 * s.Rational(3, 4) - s.Rational(3, 4)**2, 0)
        for speed in [0, s.Rational(1, 2), s.Rational(9, 10),
                      s.Rational(9999, 10000)]:
            self.assertGreater((u + delta - 1).subs({slope: s.Rational(3, 4),
                                                   v: speed}), 0)

    def test_small_angle_and_null_face_are_opposite_limits(self):
        slope = s.symbols("s", positive=True)
        # Future normal of a plane, and future normal of a slope-s graph.
        cosh_angle = 1 / s.sqrt(1 - slope**2)
        weight_squared = s.cancel(cosh_angle**2 / (cosh_angle**2 - 1))
        self.assertEqual(weight_squared, 1 / slope**2)
        self.assertEqual(s.limit(1 / slope, slope, 0, dir="+"), s.oo)
        self.assertEqual(s.limit(1 / slope, slope, 1, dir="-"), 1)

    def test_null_normal_rescaling_is_not_an_invariant_angle(self):
        alpha, beta = s.symbols("alpha beta", positive=True)
        metric = s.diag(1, -1, -1, -1)
        n = s.Matrix([1, 0, 0, 0])
        k = s.Matrix([1, 1, 0, 0])
        ell = s.Matrix([1, -1, 0, 0])

        def inner(a, b):
            return (a.T * metric * b)[0]

        self.assertEqual(inner(k, k), 0)
        self.assertEqual(inner(ell, ell), 0)
        self.assertEqual(inner(n, alpha * k), alpha * inner(n, k))
        self.assertEqual(inner(alpha * k, beta * ell), alpha * beta * inner(k, ell))
        self.assertEqual(s.expand_log(s.log(inner(n, alpha * k))), s.log(alpha))
        self.assertEqual(s.expand_log(s.log(inner(alpha * k, beta * ell) / 2)),
                         s.log(alpha) + s.log(beta))
        self.assertEqual(inner(alpha * k, ell / alpha), 2)
        # Pair normalization does not remove reciprocal rescaling freedom.
        self.assertNotEqual(alpha * k, k)

    def test_mixed_joint_screen_metric_not_euclidean_graph_area(self):
        theta, phi = s.symbols("theta phi", real=True)
        radius = s.Function("r")(theta, phi)
        omega = s.Matrix([s.sin(theta) * s.cos(phi),
                          s.sin(theta) * s.sin(phi), s.cos(theta)])
        psi = s.Matrix([-radius, *(radius * omega)])
        tangents = s.Matrix.hstack(psi.diff(theta), psi.diff(phi))
        induced = s.simplify(-tangents.T * s.diag(1, -1, -1, -1) * tangents)
        expected = s.diag(radius**2, radius**2 * s.sin(theta)**2)
        self.assertEqual(induced, expected)
        euclidean = s.simplify(tangents.T * tangents)
        self.assertEqual(s.simplify(euclidean[0, 0] - induced[0, 0]),
                         2 * s.diff(radius, theta)**2)
        self.assertEqual(s.simplify(induced.det()), radius**4 * s.sin(theta)**2)

    def test_sine_mixed_member_roots_and_transversality(self):
        T, epsilon = 1.0, 0.2
        low, high = T / (1 + epsilon), T / (1 - epsilon)
        radii = []
        for first_component in [-1, -0.5, 0, 0.5, 1]:
            radius = brentq(lambda r: r - T - epsilon * math.sin(r * first_component),
                            low, high)
            radii.append(radius)
            radial_derivative = 1 - epsilon * first_component * math.cos(
                radius * first_component)
            self.assertGreaterEqual(radial_derivative, 1 - epsilon)
            self.assertGreater(radius, 0)
            self.assertLessEqual(low, radius)
            self.assertLessEqual(radius, high)
            # Unnormalized n.k is positive; normalizing preserves its sign.
            self.assertGreater(radial_derivative, 0)
        self.assertLess(radii[0], radii[-1])
        self.assertAlmostEqual(radii[2], T)

    def test_mixed_future_partner_geometry_samples(self):
        # Independent finite samples of the future-set containment argument.
        # y on the segment p--tip is an interior future partner for 0<q<1.
        T, epsilon = 1.0, 0.2
        for spatial in [np.array([0.0, 0.0, 0.0]), np.array([0.2, -0.1, 0.3]),
                        np.array([-0.4, 0.2, 0.1])]:
            height = T + epsilon * math.sin(spatial[0])
            time = -(height + np.linalg.norm(spatial)) / 2
            for q in [0.1, 0.5, 0.9]:
                y, yt = (1 - q) * spatial, (1 - q) * time
                self.assertGreater(yt, -T - epsilon * math.sin(y[0]))
                self.assertLess(yt, -np.linalg.norm(y))
                self.assertGreater(yt - time, np.linalg.norm(y - spatial))

    def test_torus_joint_is_regular_not_spherical(self):
        # Axis singularity is outside the closed positive set (R0>delta).
        a, major, minor = 0.25, 2.0, 0.5
        self.assertGreater(major - minor, 0)
        self.assertLess(2 * a * minor, 1)
        for theta in np.linspace(0, 2 * math.pi, 9):
            for phi in np.linspace(0, 2 * math.pi, 9):
                radial = major + minor * math.cos(theta)
                x, y, z = radial * math.cos(phi), radial * math.sin(phi), minor * math.sin(theta)
                r = math.hypot(x, y)
                h = a * (minor**2 - (r - major)**2 - z**2)
                grad = -2 * a * np.array([(r - major) * x / r, (r - major) * y / r, z])
                self.assertAlmostEqual(h, 0)
                self.assertAlmostEqual(np.linalg.norm(grad), 2 * a * minor)

    def test_extra_ridge_focusing_and_noncompact_negative_controls(self):
        x = s.symbols("x", real=True)
        upper = -s.Abs(x) / 4  # minimum of two individually spacelike planes
        self.assertEqual(s.limit(upper / x, x, 0, dir="-"), s.Rational(1, 4))
        self.assertEqual(s.limit(upper / x, x, 0, dir="+"), -s.Rational(1, 4))
        radius = s.symbols("r", positive=True)
        affine = s.symbols("a", nonnegative=True)
        focusing_jacobian = (radius - affine)**2
        self.assertEqual(focusing_jacobian.subs(affine, radius), 0)
        # Fixed-height slab: finite coordinate cutoffs do not give finite volume.
        L, H = s.symbols("L H", positive=True)
        self.assertEqual(s.limit(H * (2 * L)**3, L, s.oo), s.oo)


if __name__ == "__main__":
    unittest.main()
