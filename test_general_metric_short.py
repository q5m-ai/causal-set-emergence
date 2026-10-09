"""Finite regressions for #150, not general-metric analytic estimates."""

import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.optimize import brentq

from dimension_kernels import (
    action_constants, cone_slice_moment, interval_coefficient, kernel_polynomial, Z,
)
from general_metric_short import (
    interval_corrections, joint_geometry, model_curvature_responses,
    rest_diamond_moments, ultrastatic_rest_volume,
)


def conformal_rest_volume(omega, center, duration):
    """Independent actual 4D interval, with endpoints at proper times +/-T/2."""
    def proper(t):
        return quad(omega, center, t, epsabs=1e-13, epsrel=1e-13)[0]

    lo = brentq(lambda t: proper(t) + duration / 2, center - 2 * duration, center)
    hi = brentq(lambda t: proper(t) - duration / 2, center, center + 2 * duration)
    midpoint = (lo + hi) / 2  # conformal-coordinate meeting of the two cones
    volume = 4 * np.pi / 3 * (
        quad(lambda t: omega(t)**4 * (t - lo)**3, lo, midpoint,
             epsabs=1e-15, epsrel=1e-12)[0]
        + quad(lambda t: omega(t)**4 * (hi - t)**3, midpoint, hi,
               epsabs=1e-15, epsrel=1e-12)[0]
    )
    return volume


def slab_pairs(d, rho, duration, temporal_cut, radial_cut, sector, labels=None):
    """Actual flat thin-quotient slab pair integral per spatial volume.

    The two cutoffs are t<temporal_cut and v=t+r<radial_cut, not phase cutoffs.
    Source and target time partition weights are integrated analytically.
    All radial directions, including both in d=2, are included.
    """
    from dimension_kernels import sphere_area
    kernel = s.lambdify(Z, kernel_polynomial(d) * s.exp(-Z), "numpy")
    c = float(interval_coefficient(d))
    sphere = float(sphere_area(d))

    def source_weight(tau):
        length = duration - tau
        if labels is None:
            return length
        both = length**3 / (3 * duration**2) + tau * length**2 / (2 * duration**2)
        left = length**2 / (2 * duration)
        right = left + tau * length / duration
        return {(0, 0): both, (0, 1): left - both,
                (1, 0): right - both, (1, 1): length - left - right + both}[labels]

    def time_integral(tau):
        def radial(r):
            e, other = tau < temporal_cut, tau + r < radial_cut
            factor = {"all": 1, "short": int(e), "long": int(not e),
                      "other_short": int(other), "other_long": int(not other),
                      "overlap": int(e) - int(other)}[sector]
            return factor * r**(d - 2) * kernel(rho * c * (tau*tau - r*r)**(d/2))

        breaks = sorted({0.0, tau, max(0.0, min(tau, radial_cut - tau))})
        inner = sum(quad(radial, a, b, epsabs=1e-13, epsrel=1e-11)[0]
                    for a, b in zip(breaks, breaks[1:]))
        return source_weight(tau) * sphere * inner

    breaks = sorted({0.0, duration, *(max(0.0, min(duration, x))
                                    for x in (temporal_cut, radial_cut / 2, radial_cut))})
    return sum(quad(time_integral, a, b, epsabs=1e-13, epsrel=1e-11)[0]
               for a, b in zip(breaks, breaks[1:]))


class GeneralMetricShortTests(unittest.TestCase):
    def test_rest_moments_against_section_integrals_all_dimensions(self):
        for d in (*range(2, 12), 20, 21):
            t, r = s.symbols("t r", nonnegative=True)
            # Sphere mass cancels. Integrate each numerator independently.
            denominator = 2 * s.integrate((s.Rational(1, 2) - t)**(d - 1) / (d - 1),
                                         (t, 0, s.Rational(1, 2)))
            time = 2 * s.integrate(t*t * (s.Rational(1, 2) - t)**(d - 1) / (d - 1),
                                  (t, 0, s.Rational(1, 2))) / denominator
            space = 2 * s.integrate((s.Rational(1, 2) - t)**(d + 1) / ((d - 1)*(d + 1)),
                                   (t, 0, s.Rational(1, 2))) / denominator
            self.assertEqual(rest_diamond_moments(d), (time, space))

    def test_interval_coefficients_density_and_cone_not_interchangeable(self):
        ric, scalar = s.symbols("ric scalar")
        for d in range(2, 12):
            density, cone = interval_corrections(d, ric, scalar)
            expected = -s.Rational(d, 24*(d+1)) * ric - s.Rational(d, 24*(d+1)*(d+2)) * scalar
            self.assertEqual(s.simplify(density + cone - expected), 0)
            self.assertNotEqual(s.expand(density - expected).coeff(ric), 0)
        # Both fixed-midpoint endpoint factors, not only the target factor.
        T = s.symbols("T")
        endpoint = 1 + ric*T*T/24
        self.assertEqual(s.expand(endpoint**2).coeff(T, 2), ric/12)
        self.assertNotEqual(s.expand(endpoint**2).coeff(T, 2), endpoint.coeff(T, 2))

    def test_canonical_signed_model_responses_all_dimensions(self):
        for d in (*range(2, 12), 20, 21):
            a, beta = action_constants(d)
            self.assertEqual(s.simplify(beta * cone_slice_moment(d, 0) - a), 0)
            self.assertEqual(cone_slice_moment(d, 1), 0)
            self.assertEqual(s.simplify(-beta * cone_slice_moment(d, 2)), 2)
            pieces = model_curvature_responses(d)
            self.assertEqual(s.simplify(sum(pieces)), s.Rational(1, 2))
            self.assertNotEqual(sum(pieces[1:]), s.Rational(1, 2))  # lost target measure
            self.assertNotEqual(pieces[0], s.Rational(1, 2))  # frozen phase
            if d != 4:
                self.assertNotEqual(pieces[1], model_curvature_responses(4)[1])

    def test_actual_flat_and_completed_conformal_rest_intervals(self):
        cases = [
            (lambda t: 1.0, 0.0, 0.0, 0.0),
            (lambda t: 1.7, 0.0, 0.0, 0.0),
            # q=1+t^2: independent Levi-Civita contractions in #90 convention.
            (lambda t: (1+t*t)**0.25, 0.2,
             3*(1-0.2**2)/(2*(1+0.2**2)**2.5),
             3*(1-0.2**2/2)/(1+0.2**2)**2.5),
            # q=(1-t)^-4: physical unit-time Ricci=3, scalar=12.
            (lambda t: 1/(1-t), 0.125, 3.0, 12.0),
        ]
        for omega, center, ric, scalar in cases:
            expected = float(sum(interval_corrections(4, ric, scalar)))
            errors = []
            for duration in (0.12, 0.06, 0.02):
                actual = conformal_rest_volume(omega, center, duration)
                coefficient = (actual/(np.pi/24*duration**4) - 1) / duration**2
                errors.append(abs(coefficient - expected))
            self.assertLess(errors[-1], 2e-5)
            if ric:
                self.assertLess(errors[-1], errors[0]/8)
                self.assertGreater(abs(expected), 0.01)

    def test_nonconformally_flat_actual_rest_interval(self):
        # R=2/a^2, Ric(U,U)=0 for dt^2-a^2*dS2^2-dz^2; nonzero Weyl.
        expected = float(sum(interval_corrections(4, 0, 2)))
        errors = []
        for duration in (0.4, 0.2, 0.1):
            value = ultrastatic_rest_volume(duration)
            finer = ultrastatic_rest_volume(duration, order=72)
            self.assertLess(abs(value-finer)/value, 1e-12)
            coefficient = (value/(np.pi/24*duration**4) - 1)/duration**2
            errors.append(abs(coefficient-expected))
        self.assertLess(errors[-1], 1e-6)
        self.assertLess(errors[-1], errors[0]/8)
        self.assertAlmostEqual(ultrastatic_rest_volume(0.4, radius=2, circle_length=40)
                               / ultrastatic_rest_volume(0.2), 16, places=11)
        with self.assertRaises(ValueError):
            ultrastatic_rest_volume(7)

    def test_intrinsic_joint_with_shift_anisotropy_and_variable_angle(self):
        # Smoothly varying ADM data, not a conformal metric assumption.
        targets = []
        for z in (-0.5, 0.0, 0.6):
            spatial = np.diag([1.2 + z*z, 0.9, 1.5])
            shift = np.array([0.12, -0.08, 0.05])
            g = np.zeros((4, 4))
            g[0, 0] = 1.7**2 - shift @ spatial @ shift
            g[0, 1:] = g[1:, 0] = -spatial @ shift
            g[1:, 1:] = -spatial
            p = np.array([0.15 + 0.04*z, -0.08, 0.05])
            a = np.array([0.35, 0.07 + 0.03*z, -0.04])
            data = joint_geometry(g, p, a)
            self.assertAlmostEqual(data["area"], data["coarea"], places=12)
            self.assertAlmostEqual(data["raw_model"] - data["flux"], data["target"], places=12)
            self.assertAlmostEqual(data["face_vector"] @ (-a/np.linalg.norm(a)),
                                   data["flux"], places=12)
            self.assertGreater(abs(data["flux"]), 0.02)
            self.assertGreater(data["coth"], 1)
            targets.append(data["coth"])
        self.assertGreater(max(targets) - min(targets), 0.05)

    def test_joint_flat_conformal_and_two_dimensional_counting(self):
        for d in (2, 3, 4, 5, 6):
            eta = np.diag([1.0] + [-1.0]*(d-1))
            p, a = np.zeros(d-1), np.zeros(d-1)
            p[0], a[0] = 0.1, 0.4
            for omega in (1.0, (1+0.125**2)**0.25, 1/(1-0.125)):
                data = joint_geometry(omega*omega*eta, p, a)
                expected = omega**(d-2) * (1 - p@p + p@a)/np.linalg.norm(a)
                self.assertAlmostEqual(data["target"], expected, places=12)
                if d == 2:
                    self.assertEqual(data["area"], 1.0)
                    self.assertAlmostEqual(data["coarea"], 1, places=12)
        with self.assertRaises(ValueError):
            joint_geometry(np.eye(3), [0, 0], [0.3, 0])
        with self.assertRaises(ValueError):
            joint_geometry(np.diag([1, -1]), [0.1], [0])

    def test_actual_indicator_restoration_including_overshoot(self):
        # A local flat representative tests the exact indicator algebra, not
        # the general-metric analytic estimate. h>0 is part of the integration.
        seen_corner = False
        f = lambda z: 0.1*z + 0.04*z*z
        lower = lambda z: f(z) - 0.2*z
        for z in (0.02, 0.15, 0.6):
            for t in np.linspace(f(z)-0.15, f(z)+0.03, 31):
                for dt, dz in ((0.03, 0.015), (0.08, -0.03), (0.12, 0.0)):
                    a, b, c = int(t > lower(z)), int(t < f(z)), int(t+dt < f(z+dz))
                    physical = a*b*int(t+dt > lower(z+dz))*c
                    corner = (1-a)*b*(1-c)
                    self.assertEqual(physical, a*b - b*(1-c) + corner)
                    if corner:
                        seen_corner = True
                        self.assertLessEqual(f(z)-lower(z), dt + 0.2*abs(dz) + 1e-14)
        self.assertTrue(seen_corner)

    def test_complete_ordered_partitions_point_once_and_cutoff_overlap(self):
        T, rho, dt, dv = 0.4, 300, 0.13, 0.23
        for d in (2, 4):
            values = {sector: slab_pairs(d, rho, T, dt, dv, sector)
                      for sector in ("all", "short", "long", "other_short", "other_long", "overlap")}
            self.assertAlmostEqual(values["short"] + values["long"], values["all"], places=12)
            self.assertAlmostEqual(values["other_short"] + values["other_long"], values["all"], places=12)
            self.assertAlmostEqual(values["short"] - values["other_short"], values["overlap"], places=12)
            self.assertAlmostEqual(values["long"] - values["other_long"], -values["overlap"], places=12)
            self.assertGreater(abs(values["overlap"]), 1e-8)  # not silently zero
            parts = {(i, j): slab_pairs(d, rho, T, dt, dv, "all", (i, j))
                     for i in range(2) for j in range(2)}
            self.assertAlmostEqual(sum(parts.values()), values["all"], places=12)
            self.assertGreater(abs(parts[0, 1]) + abs(parts[1, 0]), 1e-8)
            points = {(0, 0): T/3, (0, 1): T/6, (1, 0): T/6, (1, 1): T/3}
            a, beta = map(float, action_constants(d))
            assembled = sum(rho**(2/d)*(a*points[label] - beta*rho*pair)
                            for label, pair in parts.items())
            self.assertAlmostEqual(assembled, rho**(2/d)*(a*T-beta*rho*values["all"]), places=11)
            scale = -beta*rho**(1+2/d)
            self.assertAlmostEqual(scale*(values["short"]-values["other_short"]),
                                   scale*values["overlap"], places=11)

    def test_small_volume_is_not_coordinate_locality(self):
        v, delta = 0.6, 0.1
        for d in (2, 3, 4, 7):
            values = []
            for u in (1e-3, 1e-6, 1e-9):
                self.assertGreater((u+v)/2, delta)  # equality/large gap stays long
                self.assertGreater((v-u)/2, 0.29)
                values.append(float(interval_coefficient(d))*(u*v)**(d/2))
            self.assertTrue(values[2] < values[1] < values[0])

    def test_dimension_guards(self):
        for d in (True, 0, 1, 2.5):
            with self.assertRaises(ValueError):
                rest_diamond_moments(d)


if __name__ == "__main__":
    unittest.main()
