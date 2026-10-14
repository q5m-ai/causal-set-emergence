"""Finite algebra/geometry checks, not mathematical certification of PW-4."""

import unittest

import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad

from plane_wave_geometry import (
    average_inverse, cosine_profile, geometric_phase, interval_volume,
    joint_target, lens_point, phase_factor,
)


def rotating_profile(u):
    angle = .7*u
    c, s = np.cos(angle), np.sin(angle)
    rotation = np.array([[c, -s], [s, c]])
    return rotation@np.diag([1.4+.2*np.cos(u), .8+.15*np.sin(u)])@rotation.T


def path_cost(profile, u, length, d):
    # Separate adaptive physical-energy quadrature, not PW7's phase factor.
    b = np.array([[quad(lambda r: np.linalg.inv(profile(r))[i, j],
                        u, u+length, epsabs=1e-12)[0]
                   for j in range(2)] for i in range(2)])
    return d@np.linalg.solve(b, d)/2, b


def physical_clock_volume(profile, p, q, order=18):
    """Independent Cartesian clock integration of both actual causal costs."""
    length = q[0]-p[0]
    cost, b = path_cost(profile, p[0], length, q[2:]-p[2:])
    e = q[1]-p[1]-cost
    nodes, weights = leggauss(order)
    total = 0.
    for t, wt in zip((nodes+1)/2, weights/2):
        u = p[0]+t*length
        _, b0 = path_cost(profile, p[0], t*length, q[2:]-p[2:])
        _, b1 = path_cost(profile, u, (1-t)*length, q[2:]-p[2:])
        m = np.linalg.inv(b0)+np.linalg.inv(b1)
        center = p[2:]+b0@np.linalg.solve(b, q[2:]-p[2:])
        radius = np.sqrt(2*e/(m[0, 0]-m[0, 1]**2/m[1, 1]))
        slice_value = 0.
        # Adaptive x1 integration handles the closing chord's 3/2 power.
        def x1_integrand(dx1):
            middle = -m[0, 1]*dx1/m[1, 1]
            half = np.sqrt(max(0., (2*e-(m[0, 0]-m[0, 1]**2/m[1, 1])
                                           * dx1**2)/m[1, 1]))
            value = 0.
            for z2, wz2 in zip(nodes, weights):
                x = center+np.array([dx1, middle+half*z2])
                d0, d1 = x-p[2:], q[2:]-x
                width = (q[1]-p[1]-d0@np.linalg.solve(b0, d0)/2
                         - d1@np.linalg.solve(b1, d1)/2)
                value += wz2*half*width
            return value
        slice_value = quad(x1_integrand, -radius, radius, epsabs=1e-11)[0]
        total += wt*length*np.sqrt(np.linalg.det(profile(u)))*slice_value
    return total


class PlaneWaveGeometryTests(unittest.TestCase):
    def setUp(self):
        self.p = np.array([-.4, -.3, .2, -.1])
        self.q = np.array([1.1, .9, -.15, .35])

    def test_constant_anisotropic_metric_is_flat_control(self):
        g = np.array([[2., .3], [.3, .7]])
        profile = lambda u: g
        d = self.q[2:]-self.p[2:]
        phase = 2*1.5*1.2-d@g@d
        self.assertAlmostEqual(geometric_phase(self.p, self.q, profile), phase, places=13)
        for length in (0., 1e-9, .5, 3.):
            self.assertAlmostEqual(phase_factor(profile, -.4, length), np.pi/24, places=13)
        self.assertAlmostEqual(interval_volume(self.p, self.q, profile),
                               np.pi*phase**2/24, places=12)

    def test_matrix_averages_include_zero_and_negative_length(self):
        profile = cosine_profile(.2)
        np.testing.assert_allclose(average_inverse(profile, .3, 0),
                                   np.linalg.inv(profile(.3)), atol=1e-14)
        for length in (-.5, 0., 1e-12, .7):
            a = average_inverse(profile, .3, length)
            reference = np.array([[quad(lambda t: np.linalg.inv(profile(.3+t*length))[i, j],
                                         0, 1, epsabs=1e-13)[0]
                                   for j in range(2)] for i in range(2)])
            np.testing.assert_allclose(a, reference, atol=1e-13)

    def test_noncommuting_parallel_sum_and_completion_of_squares(self):
        p, q, t = self.p, self.q, .37
        length = q[0]-p[0]
        b0 = t*length*average_inverse(rotating_profile, p[0], t*length)
        b1 = (1-t)*length*average_inverse(rotating_profile, p[0]+t*length, (1-t)*length)
        self.assertGreater(np.linalg.norm(b0@b1-b1@b0), 1e-3)
        b = b0+b1
        c = b0-b0@np.linalg.solve(b, b0)
        np.testing.assert_allclose(c, np.linalg.inv(np.linalg.inv(b0)+np.linalg.inv(b1)), atol=1e-14)
        np.testing.assert_allclose(c, b0@np.linalg.solve(b, b1), atol=1e-14)
        x = np.array([.6, -.2])
        center = p[2:]+b0@np.linalg.solve(b, q[2:]-p[2:])
        d0, d1, d = x-p[2:], q[2:]-x, q[2:]-p[2:]
        defect = (d0@np.linalg.solve(b0, d0)+d1@np.linalg.solve(b1, d1)
                  - d@np.linalg.solve(b, d))/2
        self.assertAlmostEqual(defect, (x-center)@np.linalg.solve(c, x-center)/2, places=13)

    def test_actual_point_satisfies_both_orders_including_tip_collars(self):
        for t in (1e-8, .15, .8, 1-1e-8):
            for r in (0., .4, 1.):
                point, jac = lens_point(self.p, self.q, rotating_profile, t, [.35, -.6], r)
                self.assertGreaterEqual(jac, 0)
                self.assertGreaterEqual(geometric_phase(self.p, point, rotating_profile), -1e-13)
                self.assertGreaterEqual(geometric_phase(point, self.q, rotating_profile), -1e-13)

    def test_physical_map_jacobian_matches_finite_difference(self):
        params = np.array([.42, .24, -.31, .36])
        def mapped(a):
            return lens_point(self.p, self.q, rotating_profile, a[0], a[1:3], a[3])[0]
        columns = []
        for i in range(4):
            step = np.eye(4)[i]*1e-5
            columns.append((mapped(params+step)-mapped(params-step))/(2e-5))
        point, jac = lens_point(self.p, self.q, rotating_profile,
                                params[0], params[1:3], params[3])
        physical = abs(np.linalg.det(np.column_stack(columns)))*np.sqrt(np.linalg.det(rotating_profile(point[0])))
        self.assertAlmostEqual(jac, physical, delta=2e-9)

    def test_volume_matches_independent_cartesian_clock_integration(self):
        for profile in (cosine_profile(.25), rotating_profile):
            physical = physical_clock_volume(profile, self.p, self.q)
            derived = interval_volume(self.p, self.q, profile)
            self.assertAlmostEqual(derived, physical, delta=3e-10)

    def test_variable_profile_changes_phase_and_divided_volume(self):
        profile = cosine_profile(.3)
        frozen = lambda u: profile(self.p[0])
        self.assertGreater(abs(geometric_phase(self.p, self.q, profile)
                               - geometric_phase(self.p, self.q, frozen)), 1e-4)
        self.assertGreater(abs(phase_factor(profile, self.p[0], 1.5)-np.pi/24), 1e-4)
        self.assertGreater(abs(interval_volume(self.p, self.q, profile)
                               - interval_volume(self.p, self.q, frozen)), 1e-4)

    def test_varying_flat_rosen_coordinates_do_not_fake_weyl_curvature(self):
        profile = lambda u: np.diag([(1+.2*u)**2, 1.])
        self.assertAlmostEqual(phase_factor(profile, -.4, 1.5), np.pi/24, places=13)

    def test_parallel_null_collar_keeps_temporal_gap(self):
        profile = rotating_profile
        p = np.zeros(4)
        for length in (1e-2, 1e-4, 1e-6, 1e-9):
            q = np.array([length, 2., .4*np.sqrt(length), -.2*np.sqrt(length)])
            phase = geometric_phase(p, q, profile)
            self.assertGreater(phase, 0)
            self.assertGreater((q[0]+q[1])/np.sqrt(2), 1.)
            self.assertAlmostEqual(interval_volume(p, q, profile)/phase**2,
                                   phase_factor(profile, 0, length), places=14)
            self.assertAlmostEqual(phase_factor(profile, 0, length), np.pi/24, delta=1e-5)
        self.assertEqual(interval_volume(p, [0, 2, 0, 0], profile), 0)
        # At the generator, dQ/dL=2*dv, not zero.
        step = 1e-6
        derivative = (geometric_phase(p, [step, 2, 0, 0], profile)
                      - geometric_phase(p, [-step, 2, 0, 0], profile))/(2*step)
        self.assertAlmostEqual(derivative, 4., places=12)

    def test_tip_quotient_is_uniform_for_noncommuting_profile(self):
        for length in (1e-8, .5, 2.):
            a = average_inverse(rotating_profile, -.4, length)
            for t in (0., 1e-9, .3, 1-1e-9, 1.):
                a0 = average_inverse(rotating_profile, -.4, t*length)
                a1 = average_inverse(rotating_profile, -.4+t*length, (1-t)*length)
                quotient = a0@np.linalg.solve(a, a1)
                np.testing.assert_allclose(quotient, quotient.T, atol=1e-14)
                values = np.linalg.eigvalsh(quotient)
                self.assertGreater(values.min(), .5)
                self.assertLess(values.max(), 2.)

    def test_exact_signed_moments_and_critical_remainder_scaling(self):
        x = sp.symbols('x', positive=True)
        kernel = (1-9*x*x+8*x**4-sp.Rational(4, 3)*x**6)*sp.exp(-x*x)
        for j in range(3):
            self.assertEqual(sp.integrate(x**j*kernel, (x, 0, sp.oo)), 0)
        third = sp.integrate(x**3*kernel, (x, 0, sp.oo))
        self.assertEqual(third, -sp.Rational(1, 2))
        # rho^(3/2) dw*w^3 = rho^(-1/2) dz*z^3, not O(1).
        rho, z = sp.symbols('rho z', positive=True)
        self.assertEqual(sp.simplify(rho**sp.Rational(3, 2)*(z/sp.sqrt(rho))**3
                                     /sp.sqrt(rho)), z**3/sp.sqrt(rho))

    def test_independent_joint_normals_gram_and_sphere_integral(self):
        s, eta, eps = .32, .15, .2
        nodes, weights = leggauss(24)
        value = 0.
        for z, wz in zip(nodes, weights):
            for angle in 2*np.pi*(np.arange(48)+.5)/48:
                point = np.array([np.sqrt(1-z*z)*np.cos(angle),
                                  np.sqrt(1-z*z)*np.sin(angle), z])
                a = 1+eps*np.cos((eta-1)*z/np.sqrt(2))
                inverse = np.diag([a**-2, 1., 1.])
                lower = np.array([0., 0., eta])+s*point
                upper = np.array([0., 0., eta])-s*point
                c = (1-lower@inverse@upper)/np.sqrt((1-lower@inverse@lower)*(1-upper@inverse@upper))
                # Independent tangent Gram determinant relative to sphere area.
                e_phi = np.array([-np.sin(angle), np.cos(angle), 0.])
                e_mer = np.cross(e_phi, point)
                frame = np.column_stack([e_phi, e_mer])
                gram = frame.T@np.diag([a*a, 1., 1-eta*eta])@frame
                area = np.sqrt(np.linalg.det(gram))
                value += wz*(2*np.pi/48)*c/np.sqrt(c*c-1)*area
        self.assertAlmostEqual(value, joint_target(s, eta, eps), places=11)
        self.assertGreater(abs(value-joint_target(s, eta, 0)), 1.)
        self.assertAlmostEqual(joint_target(s, eta, 0), 2*np.pi*(1-eta*eta+s*s)/s, places=12)

    def test_scalar_zero_does_not_imply_conformal_flatness(self):
        u, eps = sp.symbols('u eps', real=True)
        a = 1+eps*sp.cos(u)
        # Tidal tracefree eigenvalue for G=diag(a^2,1); R_uu contracts with g^uu=0.
        tidal = sp.simplify(sp.diff(a, u, 2)/a)
        self.assertEqual(tidal, -eps*sp.cos(u)/(1+eps*sp.cos(u)))
        self.assertNotEqual(tidal.subs({u: 0, eps: sp.Rational(1, 4)}), 0)
        self.assertEqual(sp.diff(1+eps*u, u, 2), 0)

    def test_bad_inputs_and_unrelated_pairs(self):
        for profile in (lambda u: np.diag([1., 0.]), lambda u: np.ones((3, 3)),
                        lambda u: np.array([[1., .3], [0., 1.]])):
            with self.assertRaises(ValueError):
                phase_factor(profile, 0., 1.)
        with self.assertRaises(ValueError):
            phase_factor(rotating_profile, 0., float('nan'))
        with self.assertRaises(ValueError):
            cosine_profile(1.)
        with self.assertRaises(ValueError):
            joint_target(.8, .2, .1)
        with self.assertRaises(ValueError):
            lens_point(self.p, self.q, rotating_profile, 0., [0., 0.], .5)
        with self.assertRaises(ValueError):
            average_inverse(rotating_profile, 0., 1., order=1)
        self.assertEqual(interval_volume(self.q, self.p, rotating_profile), 0)
        self.assertEqual(interval_volume([0, 0, 0, 0], [1, 0, 1, 0], rotating_profile), 0)


if __name__ == '__main__':
    unittest.main()
