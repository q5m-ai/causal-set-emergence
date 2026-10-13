"""Finite geometric checks; not uniform estimates or complete-action numerics."""

import unittest
import numpy as np

import sphere_weighted_lenses as sw
import curved4_corrected_convergence as cc
from sphere_circle_focusing import interval_volume

P = np.array([0., 0., 1.])
N = np.array([1., 0., 0.])
AXIS = np.array([0.4, 0.7, 0.2])


def one(t, p, z):
    return np.ones(np.broadcast_shapes(np.shape(t), np.shape(p)[:-1], np.shape(z)))


def omega(t, p, z):
    return 1+0.025*t+0.08*np.sin(np.pi*z/10)+0.12*np.sum(p*AXIS, axis=-1)


def density(t, p, z):
    return omega(t, p, z)**4


class SphereWeightedLensTests(unittest.TestCase):
    def test_signed_map_has_actual_two_distances(self):
        for theta in (0., 1e-8, 0.8, 2.5, np.pi-0.01):
            x = theta*np.array([0.1, 0.4, 0.7, 0.9])
            y = min(0.02, np.sqrt(np.pi-theta)*0.05)*np.array([1., -1., 0.3, -0.2])
            point = sw.sphere_point(theta, x, y, P, N)
            target = np.cos(theta)*P+np.sin(theta)*N
            np.testing.assert_allclose(np.sum(point*point, axis=-1), 1, atol=4e-13)
            np.testing.assert_allclose(point@P, np.cos(np.hypot(x, y)), atol=3e-14)
            np.testing.assert_allclose(point@target, np.cos(np.hypot(x-theta, y)), atol=3e-14)
            np.testing.assert_array_equal(np.sign(point[:, 1]), np.sign(y))

    def test_axis_extension_is_exponential_map(self):
        x, y = np.array([0.1, -0.2, 0]), np.array([0.3, 0.1, 0])
        r = np.hypot(x, y)
        expected = (np.cos(r)[:, None]*P+np.sinc(r/np.pi)[:, None]
                    *(x[:, None]*N+y[:, None]*np.cross(P, N)))
        np.testing.assert_allclose(sw.sphere_point(0, x, y, P, N), expected, atol=1e-14)

    def test_each_orientation_has_the_area_ratio(self):
        theta, x, y, h = 2.1, 0.8, 0.13, 1e-5
        dx = (sw.sphere_point(theta, x+h, y, P, N)
              - sw.sphere_point(theta, x-h, y, P, N))/(2*h)
        dy = (sw.sphere_point(theta, x, y+h, P, N)
              - sw.sphere_point(theta, x, y-h, P, N))/(2*h)
        from sphere_circle_focusing import area_ratio
        expected = area_ratio(theta, np.hypot(x, y), np.hypot(x-theta, y))
        self.assertAlmostEqual(np.linalg.norm(np.cross(dx, dy))/expected, 1, delta=2e-9)

    def test_sphere_independent_factor_recovers_165(self):
        base = lambda t, z: (1+0.025*t+0.08*np.sin(np.pi*z/10))**4
        lifted = lambda t, p, z: base(t, z)
        for theta, b, q in ((0., 1.2, 0.15), (1.1, -0.8, 0.2), (3., 0.4, 0.02)):
            old = cc.regular_volume_factor(-1.7, 19.7, theta, b, q, base, 14)
            new = sw.regular_factor(-1.7, 19.7, theta, b, q, P, N, lifted, 14)
            self.assertAlmostEqual(new/old, 1, places=13)

    def test_independent_weighted_clock_and_diamond(self):
        for theta, b, q in ((0., 1.2, 0.3), (1.1, 0.7, 0.24), (2.3, -0.8, 0.3)):
            tau = np.sqrt(theta*theta+b*b+q)
            fixed = q*q*sw.regular_factor(-1.7, 19.7, theta, b, q, P, N, density, 16)
            clock = sw.clock_volume(-1.7, 19.7, tau, theta, b, P, N, density,
                                    order=48, circle_order=24)
            self.assertAlmostEqual(fixed/clock, 1, delta=7e-5)

    def test_orientations_are_not_interchangeable_for_the_weight(self):
        yplus = sw.sphere_point(2., 1., 0.1, P, N)
        yminus = sw.sphere_point(2., 1., -0.1, P, N)
        self.assertGreater(abs(density(0, yplus, 0)-density(0, yminus, 0)), 0.08)

    def test_rotation_of_geometry_without_density_changes_phase(self):
        first = sw.regular_factor(-1.7, 1, 2., 0.7, 0.2, P, N, density, 14)
        second = sw.regular_factor(-1.7, 1, 2., 0.7, 0.2, N, -P, density, 14)
        self.assertGreater(abs(first/second-1), 0.03)

    def test_covariance_requires_rotating_the_density_too(self):
        rotation = np.array([[0., 0., 1.], [1., 0., 0.], [0., 1., 0.]])
        rotated_density = lambda t, p, z: density(t, p@rotation, z)
        a = sw.regular_factor(-1.7, 1, 2., 0.7, 0.2, P, N, density, 14)
        b = sw.regular_factor(-1.7, 1, 2., 0.7, 0.2,
                              rotation@P, rotation@N, rotated_density, 14)
        self.assertAlmostEqual(a, b, places=13)

    def test_seam_and_both_signed_circle_directions(self):
        args = (2.7, 0.8, 0.1, P, N, density)
        a = sw.regular_factor(-1.8, 19.7, *args)
        b = sw.regular_factor(-1.8, -0.3, *args)
        self.assertAlmostEqual(a, b, places=13)
        c = sw.regular_factor(-1.8, 19.7, 2.7, -0.8, 0.1, P, N, density)
        self.assertGreater(abs(a/c-1), 0.05)

    def test_full_physical_transition_and_antipode(self):
        for theta, u in ((3., 3.25), (3., 2*np.pi-3), (3., 3.4), (np.pi, 3.45)):
            actual = sw.clock_volume(-1.8, 3, u, theta, 0, P, N, density, order=48,
                                     circle_order=24)
            base = interval_volume(u, theta, order=64, circle_order=28)
            self.assertGreater(actual, 0.76**4*base)
            self.assertLess(actual, 1.24**4*base)
        with self.assertRaises(ValueError):
            sw.regular_factor(-1.8, 3, 3, 0, 3.4**2-9, P, N, density)

    def test_weighted_antipodal_coefficient_is_not_frozen_at_source(self):
        coefficient = sw.antipodal_coefficient(-1.7, 1., 0.5, P, N, density)
        unweighted = sw.antipodal_coefficient(-1.7, 1., 0.5, P, N, one)
        self.assertGreater(abs(coefficient/(density(-1.7, P, 1)*unweighted)-1), 0.03)
        errors = []
        for e in (0.03, 0.015, 0.0075):
            tau = np.hypot(np.pi+e, 0.5)
            value = sw.clock_volume(-1.7, 1, tau, np.pi, 0.5, P, N, density,
                                    order=48, circle_order=24)
            errors.append(abs(value/e**1.5/coefficient-1))
        self.assertLess(errors[-1], 0.006)
        self.assertLess(errors[-1], errors[0]/2)

    def test_rationalized_clock_at_small_excess(self):
        # Regression for the subtractive-gap trap reported on #165. This new
        # representation uses ellipse-root products even when b is nonzero.
        coefficient = sw.antipodal_coefficient(-1.8, 0, 0., P, N, one)
        for e in (1e-6, 1e-8):
            actual = sw.clock_volume(-1.8, 0, np.pi+e, np.pi, 0, P, N, one,
                                     order=48, circle_order=20)
            self.assertAlmostEqual(actual/e**1.5/coefficient, 1, delta=2e-5)

    def test_rescaled_sphere_motion_is_not_order_sqrt_e_uniformly(self):
        points = []
        for a in (0.1, 0.02, 0.004):
            theta, e = np.pi-a, 0.1*a
            y = np.sqrt(e*(2*theta+e))*0.2
            point = sw.sphere_point(theta, theta/2, y, P, N)
            points.append(abs(point[1]))
        self.assertGreater(min(points), 0.15)
        self.assertLess(max(points)/min(points), 1.2)

    def test_finite_rescaled_cut_bounds(self):
        values = [np.sqrt(a)*sw.cut_factor(a, ratio*a, -0.7, 0.3, 3, P, N, density, 14)
                  for a in (0.2, 0.05, 0.01) for ratio in (0., 0.02, 0.1)]
        self.assertGreater(min(values), 0.5)
        self.assertLess(max(values), 30)
        # Sampling is not proof of the uniform derivative estimates.

    def test_moving_closing_and_both_endpoint_factors(self):
        p0 = sw.closing_data(0.1, 0, 0.7, 0.8, 19.7, P, N, density)
        p1 = sw.closing_data(0.1, 0.08, 0.7, 0.8, 19.7, P, N, density)
        self.assertLess(abs(p1['b']), abs(p0['b']))
        self.assertLess(p1['ts'], p0['ts'])
        self.assertGreater(abs(p1['amplitude']/p0['amplitude']-1), 0.02)
        for v in (-1., 1.):
            self.assertEqual(sw.closing_data(0.1, 0.02, v, 0.8, 1, P, N, density)['amplitude'], 0)
        c = 1.3
        weighted = lambda t, p, z: c**4*one(t, p, z)
        base = sw.closing_data(0.1, 0.02, 0.4, 0.3, 0, P, N, one)
        scaled = sw.closing_data(0.1, 0.02, 0.4, 0.3, 0, P, N, weighted)
        self.assertAlmostEqual(scaled['amplitude']/base['amplitude'], c**8)
        h0 = sw.cut_factor(0.1, 0.02, 0.4, 0.3, 0, P, N, one)
        h1 = sw.cut_factor(0.1, 0.02, 0.4, 0.3, 0, P, N, weighted)
        self.assertAlmostEqual(h1/h0, c**4)

    def test_nontrivial_sphere_target_independent_of_action(self):
        zero = lambda t, p, z: 0*one(t, p, z)
        for eps in (0., 0.15, 0.4):
            om = lambda t, p, z: 1+eps*p[..., 2]
            lap = lambda t, p, z: -2*eps*p[..., 2]
            actual = sw.independent_target(om, zero, zero, lap)
            self.assertAlmostEqual(actual/(320*np.pi), 1+7*eps*eps/3, places=12)
            # Dropping the sphere Laplacian gives the wrong independent target.
            wrong = sw.independent_target(om, zero, zero, zero)
            self.assertAlmostEqual((actual-wrong)/(320*np.pi), 2*eps*eps, places=12)

    def test_target_reduces_to_165(self):
        om = lambda t, z: 1+t*t/16+0.1*np.cos(np.pi*z/10)
        tt = lambda t, z: 0*t+1/8
        zz = lambda t, z: -0.1*(np.pi/10)**2*np.cos(np.pi*z/10)
        lift = lambda f: lambda t, p, z: f(t, z)
        zero = lambda t, p, z: 0*one(t, p, z)
        actual = sw.independent_target(lift(om), lift(tt), lift(zz), zero)
        self.assertAlmostEqual(actual/cc.independent_target(om, tt, zz), 1, places=12)

    def test_ordered_partition_restoration_not_same_label(self):
        a = np.array([0.3, 0.7])
        b = np.array([0.8, 0.2])
        phase = sw.regular_factor(-1.7, 0, 1.2, 0.4, 0.1, P, N, density)
        full = sum(x*y*phase for x in a for y in b)
        same = sum(x*y*phase for x, y in zip(a, b))
        self.assertAlmostEqual(full, phase)
        self.assertLess(same, phase/2)

    def test_invalid_requests(self):
        with self.assertRaises(ValueError):
            sw.frame(P, P)
        with self.assertRaises(ValueError):
            sw.sphere_point(np.pi, 1., 0., P, N)
        with self.assertRaises(ValueError):
            sw.cut_factor(0.1, 0.2, 0., 0.5, 0., P, N, density)
        with self.assertRaises(ValueError):
            sw.closing_data(0.1, 0., 2., 0.5, 0., P, N, density)
        with self.assertRaises(ValueError):
            sw.regular_factor(-1., 0., 1., 0., 0.1, P, N, lambda t, p, z: -1)
        self.assertEqual(sw.clock_volume(-1.8, 0, np.pi, np.pi, 0, P, N, density), 0)


if __name__ == '__main__':
    unittest.main()
