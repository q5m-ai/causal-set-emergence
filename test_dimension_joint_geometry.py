"""Independent finite-geometry checks; no general admissibility or limit proof.

Use actual derivatives, timelike normals and tangent Gram matrices, including
zero-dimensional frames. No action evaluation supplies a joint target here.
"""

import unittest

from mpmath import mp

import dimension_joint_geometry as gj
from test_joint_geometry import joint_data as old_four_joint_data
from test_joint_geometry import gram_density as old_four_gram_density


def dot(v, w):
    return mp.fsum(a * b for a, b in zip(v, w))


def euclidean_density(frame):
    if not frame:
        return mp.mpf(1)
    return mp.sqrt(mp.det(mp.matrix([[dot(v, w) for w in frame] for v in frame])))


def circular_data(u, height, bend):
    """Actual derivative of the 3D ball/sine joint embedding."""
    x = (mp.cos(u), mp.sin(u))
    v = (-mp.sin(u), mp.cos(u))
    a = tuple(-2 * height * xi for xi in x)
    q = (bend * mp.cos(x[0]), mp.mpf(0))
    tangent = (q[0] * v[0], *v)
    return x, a, q, tangent


class DimensionJointGeometryTests(unittest.TestCase):
    def setUp(self):
        context = mp.workdps(45)
        context.__enter__()
        self.addCleanup(context.__exit__, None, None, None)

    def assertNear(self, actual, expected, tolerance="1e-38"):
        self.assertLess(abs(actual - expected),
                        mp.mpf(tolerance) * max(1, abs(expected)))

    def test_symbolic_discriminant_and_empty_determinant(self):
        gj.check_joint_identities()
        self.assertEqual(gj.induced_gram_density(2, ()), 1)

    def test_actual_normals_tangents_and_metric_in_dimensions_two_through_six(self):
        for d in range(2, 7):
            n = d - 1
            a = (mp.mpf("-0.5"),) + (mp.mpf(0),) * (n - 1)
            q = tuple(mp.mpf(i + 1) / 40 for i in range(n))
            data = gj.joint_point_geometry(d, a, q)
            with self.subTest(d=d):
                self.assertEqual(data.physical_dimension, d)
                for normal in (data.past_normal, data.future_normal):
                    self.assertGreater(normal[0], 0)
                    self.assertNear(gj.lorentz_inner(d, normal, normal), 1)
                self.assertGreater(data.cosh, 1)
                self.assertGreater(data.angle, 0)
                self.assertNear(data.weight, mp.coth(data.angle))
                self.assertNear(data.weight * data.area_density, data.target_density)
                frame = []
                for i in range(1, n):
                    v = tuple(mp.mpf(j == i) for j in range(n))
                    self.assertEqual(dot(a, v), 0)
                    tangent = gj.graph_tangent(d, q, v)
                    frame.append(tangent)
                    self.assertNear(gj.lorentz_inner(d, data.past_normal, tangent), 0)
                    self.assertNear(gj.lorentz_inner(d, data.future_normal, tangent), 0)
                density = gj.induced_gram_density(d, frame)
                self.assertNear(density, data.area_density)
                if d > 2:
                    self.assertLess(density, 1)
                    self.assertGreater(euclidean_density(frame), 1)
                else:
                    self.assertEqual(data.area_density, 1)

    def test_lorentz_parity_dilation_and_frame_changes(self):
        # Non-orthonormal frame changes and spatial parity are independent of
        # the projected formula. Scales include the reciprocal and d=2 exponent 0.
        for d in range(2, 7):
            n, m = d - 1, d - 2
            q = tuple(mp.mpf(i + 1) / 40 for i in range(n))
            a = (mp.mpf("-0.5"),) + (mp.mpf(0),) * m
            data = gj.joint_point_geometry(d, a, q)
            frame = [gj.graph_tangent(d, q, [mp.mpf(j == i) for j in range(n)])
                     for i in range(1, n)]
            density = gj.induced_gram_density(d, frame)
            axis = 1 if d > 2 else 0
            boosted = [gj.boost(d, v, mp.mpf("0.6"), axis) for v in frame]
            self.assertNear(gj.induced_gram_density(d, boosted), density)
            normals = [gj.boost(d, v, mp.mpf("0.6"), axis)
                       for v in (data.past_normal, data.future_normal)]
            self.assertNear(gj.lorentz_inner(d, *normals), data.cosh)
            self.assertTrue(all(v[0] > 0 for v in normals))
            parity = [v[:-1] + (-v[-1],) for v in boosted]
            self.assertNear(gj.induced_gram_density(d, parity), density)
            for scale in (mp.mpf(2), mp.mpf("0.5")):
                scaled = [tuple(scale * x for x in v) for v in boosted]
                self.assertNear(gj.induced_gram_density(d, scaled), scale**m * density)
            if m:
                change = mp.eye(m)
                change[0, 0] = -2
                if m > 1:
                    change[0, 1] = mp.mpf("0.3")
                changed = [tuple(mp.fsum(frame[j][k] * change[j, i] for j in range(m))
                                 for k in range(d)) for i in range(m)]
                self.assertNear(gj.induced_gram_density(d, changed), 2 * density)

    def test_nonlinear_chart_change_with_orientation_reversal(self):
        height, bend = mp.mpf("0.25"), mp.mpf("0.125")
        for sign in (1, -1):
            for parameter in map(mp.mpf, ("0.2", "0.7", "1.1")):
                u = sign * (parameter + parameter**3 / 10)
                du = sign * (1 + 3 * parameter**2 / 10)
                _, a, q, tangent = circular_data(u, height, bend)
                def embedding(v):
                    phi = sign * (v + v**3 / 10)
                    return (bend * mp.sin(mp.cos(phi)), mp.cos(phi), mp.sin(phi))
                derivative = tuple(mp.diff(lambda v: embedding(v)[i], parameter)
                                   for i in range(3))
                density = gj.induced_gram_density(3, [derivative])
                for actual, expected in zip(derivative, tangent):
                    self.assertNear(actual, du * expected)
                self.assertNear(density, abs(du) * gj.induced_gram_density(3, [tangent]))
                data = gj.joint_point_geometry(3, a, q)
                self.assertNear(data.weight * density, abs(du) * data.target_density)
        # Measure compatibility on an entire overlap interval, not just points.
        density = lambda u: gj.induced_gram_density(3, [circular_data(u, height, bend)[3]])
        lo, hi = mp.mpf("0.2"), mp.mpf("0.8")
        original = mp.quad(density, [lo + lo**3 / 10, hi + hi**3 / 10])
        changed = mp.quad(lambda v: density(v + v**3 / 10) * (1 + 3 * v**2 / 10), [lo, hi])
        self.assertNear(original, changed)

    def test_curved_three_dimensional_target_from_normals_and_grams(self):
        height, bend = mp.mpf("0.25"), mp.mpf("0.125")
        def integrand(u, transported=False, euclidean=False):
            _, a, q, tangent = circular_data(u, height, bend)
            # Normalize the two normals independently of the scalar target.
            past = gj.future_normal(3, [qi - ai for qi, ai in zip(q, a)])
            future = gj.future_normal(3, q)
            if transported:
                tangent, past, future = [gj.boost(3, v, mp.mpf("0.6"), 1)
                                        for v in (tangent, past, future)]
            C = gj.lorentz_inner(3, past, future)
            density = euclidean_density([tangent]) if euclidean else gj.induced_gram_density(3, [tangent])
            return C / mp.sqrt(C**2 - 1) * density
        expected = mp.pi / height * (1 - bend**2 * (1 + mp.besselj(0, 2)) / 2)
        intervals = [0, mp.pi / 2, mp.pi, 3 * mp.pi / 2, 2 * mp.pi]
        for transported in (False, True):
            actual = mp.quad(lambda u: integrand(u, transported), intervals)
            self.assertNear(actual, expected)
        wrong = mp.quad(lambda u: integrand(u, True, True), intervals)
        self.assertGreater(wrong, expected * mp.mpf("1.1"))
        self.assertLess(expected, mp.pi / height)  # genuinely different from planar
        with mp.workdps(55):
            refined = mp.quad(integrand, [0, mp.pi, 2 * mp.pi])
            self.assertNear(refined, expected)

    def test_disconnected_curved_three_dimensional_components(self):
        height, bend = mp.mpf("0.25"), mp.mpf("0.125")
        def raw_height(x, y):
            return height * max(1 - (x - 3)**2 - y*y, 1 - (x + 3)**2 - y*y)
        def integrand(u, center):
            x, y = center + mp.sin(u), mp.cos(u)
            # Differentiate the actual maximum: the local winning branch is
            # separated from the other one on each entire component.
            a = (mp.diff(lambda z: raw_height(z, y), x),
                 mp.diff(lambda z: raw_height(x, z), y))
            q = (0, bend * mp.cos(y))
            tangent = (-bend * mp.cos(y) * mp.sin(u), mp.cos(u), -mp.sin(u))
            data = gj.joint_point_geometry(3, a, q)
            return data.weight * gj.induced_gram_density(3, [tangent])
        total = mp.mpf(0)
        for center in (-3, 3):
            self.assertEqual(raw_height(center, 0), height)
            self.assertEqual(mp.diff(lambda z: raw_height(z, 0), center), 0)
            total += mp.quad(lambda u: integrand(u, center), [0, mp.pi, 2 * mp.pi])
        self.assertLess(raw_height(0, 0), 0)
        expected = 2 * mp.pi / height * (1 - bend**2 * (1 + mp.besselj(0, 2)) / 2)
        self.assertNear(total, expected)

    def test_planar_ellipses_and_exact_four_dimensional_compatibility(self):
        # 3D ellipse: integrate actual tangent length / actual gradient norm.
        height = mp.mpf("0.25")
        def ellipse(u):
            x = (mp.cos(u), 2 * mp.sin(u))
            a = (-2 * height * x[0], -2 * height * x[1] / 4)
            tangent = (0, -mp.sin(u), 2 * mp.cos(u))
            data = gj.joint_point_geometry(3, a, (0, 0))
            self.assertEqual(data.area_density, 1)
            return data.weight * gj.induced_gram_density(3, [tangent])
        self.assertNear(mp.quad(ellipse, [0, mp.pi, 2 * mp.pi]), 8 * mp.pi)
        # Reuse the old independent 4D actual parameterization, not a new action.
        for bend in (mp.mpf(0), mp.mpf("0.125")):
            for theta, phi in [("0.3", "0.7"), ("1.1", "2.4"), ("2.2", "4.8")]:
                v, w, past, future, a, q = old_four_joint_data(mp.mpf(theta), mp.mpf(phi), bend)
                data = gj.joint_point_geometry(4, a, q)
                for old, new in ((past, data.past_normal), (future, data.future_normal)):
                    for actual, expected in zip(old, new):
                        self.assertNear(actual, expected)
                self.assertNear(gj.induced_gram_density(4, [v, w]), old_four_gram_density(v, w))
                spatial = old_four_gram_density((0, *v[1:]), (0, *w[1:]))
                self.assertNear(data.area_density * spatial, gj.induced_gram_density(4, [v, w]))
        # The old whole-joint 48*pi regression remains in test_joint_geometry.

    def test_counting_measure_all_components_and_exterior_zeros(self):
        # Ball: two endpoints, not sphere area times two endpoint weights.
        region = gj.BallSineRegion(2, bend=0)
        total = 0
        for x in (-1, 1):
            h, f, a, q = region.data((x,))
            self.assertEqual(h, 0)
            self.assertEqual(region.stratum((f, x)), "joint")
            total += gj.joint_point_geometry(2, a, q).weight * gj.induced_gram_density(2, [])
        self.assertNear(total, 4)
        # Annulus in one spatial dimension: two components, FOUR endpoints.
        amplitude = mp.mpf("0.125")
        def raw_height(x):
            return amplitude * (x*x - mp.mpf("0.25")) * (1 - x*x) if abs(x) < 2 else mp.mpf(0)
        endpoints = tuple(map(mp.mpf, (-1, "-0.5", "0.5", 1)))
        total = mp.mpf(0)
        for x in endpoints:
            self.assertEqual(raw_height(x), 0)
            a = mp.diff(raw_height, x)
            self.assertNotEqual(a, 0)
            total += gj.joint_point_geometry(2, (a,), (0,)).weight
        self.assertNear(total, 4 / amplitude)
        critical = mp.sqrt(mp.mpf(5) / 8)
        self.assertGreater(raw_height(critical), 0)
        self.assertNear(mp.diff(raw_height, critical), 0)
        for exterior in (-3, -2, 2, 3):
            self.assertEqual(raw_height(exterior), 0)
            self.assertFalse(mp.mpf("0.5") <= abs(exterior) <= 1)

    def test_explicit_regions_strata_critical_point_and_causal_interval(self):
        for d in range(2, 7):
            region = gj.BallSineRegion(d)
            zero = (mp.mpf(0),) * (d - 1)
            h, f, a, _ = region.data(zero)
            self.assertGreater(h, 0)
            self.assertEqual(a, zero)
            self.assertTrue(region.contains((-h / 2, *zero)))
            self.assertEqual(region.stratum((f, *zero)), "future")
            self.assertEqual(region.stratum((f - h, *zero)), "past")
            for sign in (-1, 1):
                x = (mp.mpf(sign),) + zero[1:]
                h, f, *_ = region.data(x)
                self.assertEqual(region.stratum((f, *x)), "joint")
                self.assertFalse(region.contains((f, *x)))
            exterior = (mp.mpf(2),) + zero[1:]
            _, f, *_ = region.data(exterior)
            self.assertEqual(region.stratum((f, *exterior)), "exterior")
            # Actual null intermediate points in an interval between interior
            # endpoints, as well as the endpoints themselves. Not just chronology.
            p, q = (-mp.mpf("0.2"), *zero), (-mp.mpf("0.05"), *zero)
            for fraction in (mp.mpf(0), mp.mpf("0.25"), mp.mpf("0.5"), mp.mpf(1)):
                time = p[0] + fraction * (q[0] - p[0])
                radius = min(time - p[0], q[0] - time)
                for sign in (-1, 1):
                    event = (time, sign * radius, *zero[1:])
                    self.assertTrue(region.contains(event))
            # A translated nontrivial boost has a checked inverse on actual points.
            event = (-mp.mpf("0.1"), *zero)
            translation = tuple(mp.mpf(i + 1) / 3 for i in range(d))
            image = tuple(x + y for x, y in zip(gj.boost(d, event, "0.6"), translation))
            inverse = gj.boost(d, [x - y for x, y in zip(image, translation)], "-0.6")
            for actual, expected in zip(inverse, event):
                self.assertNear(actual, expected)
            self.assertTrue(region.contains(inverse))
        # A real curved-future witness inside the spatial unit ball.
        region = gj.BallSineRegion(3)
        self.assertNotEqual(mp.diff(lambda x: region.data((x, 0))[1], mp.mpf("0.5"), 2), 0)

    def test_invalid_geometry_is_not_silently_totalized(self):
        for d in (True, 1, 0, -1, 3.0):
            with self.assertRaises(ValueError):
                gj.BallSineRegion(d)
        for height, bend in ((0, 0), ("0.5", 0), ("0.4", "0.2"), ("0.25", -1)):
            with self.assertRaises(ValueError):
                gj.BallSineRegion(3, height, bend)
        for a, q in (((0, 0), (0, 0)), ((1, 0), (0, 0)), (("0.1", 0), (1, 0)),
                     (("0.5", 0), (0,)), ((mp.nan, 0), (0, 0))):
            with self.assertRaises(ValueError):
                gj.joint_point_geometry(3, a, q)
        for frame in ([], [(1, 0, 0)], [(0, 0, 0)], [(0, 1, 0), (0, 0, 1)]):
            with self.assertRaises(ValueError):
                gj.induced_gram_density(3, frame)
        with self.assertRaises(ValueError):
            gj.induced_gram_density(4, [(0, 1, 0, 0), (0, 2, 0, 0)])
        for velocity, axis in ((1, 0), (-1, 0), (mp.nan, 0), ("0.5", 2), ("0.5", True)):
            with self.assertRaises(ValueError):
                gj.boost(3, (1, 0, 0), velocity, axis)


if __name__ == "__main__":
    unittest.main()
