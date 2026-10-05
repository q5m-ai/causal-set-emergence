"""Independent finite regressions for the written #133 feasibility gate."""

import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

from two_face_diagnostics import bdg_kernel as kernel
from conformal_geometry import conformal_curvature
from general_metric_gate import (
    antipodal_coefficient, antipodal_scaled_volume, check_general_metric_identities,
    null_ray_phase, slab_phase_amplitude, thin_torus_interval,
    time_density_phase, torus_distance,
)


def pair_by_radius(rho, T, factor=lambda r: 1.0):
    """Original source/target time difference and spatial radius, per volume."""
    return 4 * np.pi * quad(lambda tau: (T - tau) * quad(
        lambda r: r**2 * factor(r) * kernel(rho * np.pi / 24 * (tau**2 - r**2)**2),
        0, tau, epsabs=2e-12, epsrel=2e-11)[0],
        0, T, epsabs=2e-12, epsrel=2e-11)[0]


class GeneralMetricGateTests(unittest.TestCase):
    def test_exact_certificates(self):
        check_general_metric_identities()

    def test_nonpolynomial_curvature_and_independent_targets(self):
        t, x, y, z = s.symbols("t x y z", real=True)
        omega = 1 / (1 - t)
        # Calculator uses the opposite Riemann sign from #90.
        scalar = -conformal_curvature(omega, (t, x, y, z))[3]
        self.assertEqual(scalar, 12)
        pilot_R = 3 * (1 - t**2 / 2) / (1 + t**2)**s.Rational(5, 2)
        self.assertNotEqual(s.simplify(s.diff(pilot_R, t)), 0)
        self.assertNotEqual(s.diff(omega**4, t, 3).subs(t, 0), 0)
        # Ellipsoid f=1/8: curvature target and area are not action fits.
        bulk = 48 * np.pi * quad(
            lambda t: (0.5 + 4 * t)**1.5 / (1 - t)**4, -0.125, 0.125)[0]
        self.assertGreater(bulk, 0)
        self.assertAlmostEqual(48 * np.pi / (1 - 0.125)**2, 3072 * np.pi / 49)
        self.assertEqual((2, 6), (1 / 0.5, 1 / (1 / 6)))

    def test_phase_recovers_polynomial_pilot_including_null(self):
        for t, u, v in ((-0.125, 0, 0.7), (0.1, 0.02, 0.4), (0, 0.3, 0.3)):
            expected = 1 + t*t + t*(u+v)/2 + 3*(u+v)**2/40 - u*v/30
            self.assertAlmostEqual(time_density_phase(lambda x: 1 + x*x, t, u, v),
                                   expected, places=13)

    def test_nonpolynomial_phase_matches_original_vertical_sections(self):
        q = lambda t: (1 - t)**-4
        t, T = -0.125, 0.25
        original = 4 * np.pi / 3 * (
            quad(lambda a: q(a) * (a-t)**3, t, t+T/2)[0]
            + quad(lambda a: q(a) * (t+T-a)**3, t+T/2, t+T)[0])
        pushed = np.pi / 24 * T**4 * time_density_phase(q, t, T, T)
        self.assertAlmostEqual(original, pushed, places=14)
        self.assertGreater(abs(original - np.pi / 24 * T**4 * q(t)), 1e-5)

    def test_null_phase_is_whole_ray_average_not_source_jet(self):
        q = lambda t: (1 - t)**-4
        t, v = -0.1, 0.6
        ray = null_ray_phase(q, t, v)
        self.assertAlmostEqual(time_density_phase(q, t, 0, v, order=40), ray, places=12)
        self.assertGreater(abs(ray - q(t)), 0.4)
        for u in (0, 0.02, 0.12):
            h = 1e-6
            F = lambda u: u*v*np.sqrt(time_density_phase(q, t, u, v))
            derivative = (F(u+h)-F(u-h))/(2*h)
            self.assertGreater(derivative, 0.4)

    def test_quotient_cross_seam_pair_and_validity_guard(self):
        p, q = np.array([0.98, 0.5, 0.5]), np.array([0.02, 0.5, 0.5])
        distance = torus_distance(p, q, 1)
        self.assertAlmostEqual(distance, 0.04)
        self.assertGreater(np.linalg.norm(p-q), 0.1)
        self.assertGreater(thin_torus_interval(0.1, distance, 1, 0.4), 0)
        self.assertAlmostEqual(torus_distance(p + [3, -2, 1], q, 1), distance)
        with self.assertRaises(ValueError):
            thin_torus_interval(0.1, distance, 1, 0.5)
        with self.assertRaises(ValueError):
            thin_torus_interval(0.1, 0.2, 1, 0.4)

    def test_full_slab_reduction_and_short_long_restoration(self):
        T = 0.4
        for rho in (10, 3000):
            original = pair_by_radius(rho, T)
            integrand = lambda w: slab_phase_amplitude(w, T) * kernel(np.pi*rho*w*w/24)
            pushed = quad(integrand, 0, T*T, epsabs=1e-13)[0]
            short = quad(integrand, 0, 0.03, epsabs=1e-13)[0]
            long = quad(integrand, 0.03, T*T, epsabs=1e-13)[0]
            # A phase partition for this exact reduction, not the pilot v split.
            self.assertAlmostEqual(original, pushed, places=11)
            self.assertAlmostEqual(short + long, pushed, places=11)
            self.assertNotAlmostEqual(short, pushed, places=7)

    def test_all_partition_pairs_and_point_once(self):
        # Smooth periodic weights chi_0=(1+cos(2*pi*x))/2, chi_1=1-chi_0.
        # After source and sphere averaging, diagonal label pairs have factor
        # 1/2 + sinc(2*r)/4. Off-diagonal pairs are genuinely nonzero.
        rho, T = 1, 0.4  # all intervals in a positive band of the signed kernel
        full = pair_by_radius(rho, T)
        same = pair_by_radius(rho, T, lambda r: 0.5 + np.sinc(2*r)/4)
        cross = pair_by_radius(rho, T, lambda r: 0.5 - np.sinc(2*r)/4)
        self.assertAlmostEqual(full, same + cross, places=13)
        self.assertGreater(cross, 0.25*full)
        full_action = 4/np.sqrt(6)*np.sqrt(rho)*(T-rho*full)
        diagonal_action = 4/np.sqrt(6)*np.sqrt(rho)*(0.75*T-rho*same)
        self.assertGreater(abs(full_action-diagonal_action), 0.1)

    def test_slab_density_against_independent_inner_integral(self):
        T = 0.7
        for w in (0, 1e-4, 0.12, T*T):
            original = 2*np.pi*quad(
                lambda tau: (T-tau)*np.sqrt(max(0, tau*tau-w)), np.sqrt(w), T)[0]
            self.assertAlmostEqual(slab_phase_amplitude(w, T), original, places=11)
        self.assertEqual(slab_phase_amplitude(T*T+0.1, T), 0)

    def test_focusing_actual_volume_and_refinement(self):
        coefficient = antipodal_coefficient()
        self.assertGreater(coefficient, 0)
        errors = []
        for eps in (0.04, 0.01, 0.0025):
            value = antipodal_scaled_volume(eps)
            fine = antipodal_scaled_volume(eps, order=160)
            self.assertLess(abs(value-fine)/fine, 1e-7)
            errors.append(abs(value/coefficient-1))
        self.assertTrue(errors[2] < errors[1] < errors[0])
        self.assertLess(errors[-1], 0.002)
        # Wrong regular-null eps^2 law is not uniformly comparable here.
        values = [antipodal_scaled_volume(e)/np.sqrt(e) for e in (0.01, 0.0025)]
        self.assertGreater(values[1]/values[0], 1.9)

    def test_focusing_scaling_and_jacobi_zero(self):
        eps = 0.01
        self.assertAlmostEqual(antipodal_scaled_volume(2*eps, radius=2)
                               / antipodal_scaled_volume(eps), 2**2.5, places=11)
        self.assertAlmostEqual(np.sin(np.pi)/np.pi, 0, places=15)
        self.assertGreater(np.sin(np.pi/2)/(np.pi/2), 0.6)
        # Independent bulk of the specified a=1, L=20, T=4 member; J is empty.
        self.assertAlmostEqual(0.5*2*(4*np.pi*20)*4, 320*np.pi)


if __name__ == "__main__":
    unittest.main()
