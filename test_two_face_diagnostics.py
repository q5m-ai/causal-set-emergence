"""Regression diagnostics, deliberately not assertions of a curved-face limit."""

import math
import unittest

import numpy as np
from mpmath import mp
from scipy.optimize import brentq

from calculations import ellipsoid_action, ellipsoid_limit, kernel
from reproduce_two_faces import planar_density_reference
from two_face_diagnostics import (
    AxialCap, RadialCap, C_INTERVAL, NORMALIZATION, action, axial_null_contact, axial_overlap, bdg_kernel,
    boosted_ellipsoid_action, contains, ellipsoid_overlap, joint_geometry,
    gauss_rule, overlap_density, quadratic_remainder_probe, quadrature, region_data,
)


def direct_radial_pair(cap, rho, order):
    """Independent unreduced (p,q,r,s) causal integral at moderate density.

    No proper-time density, long-cutoff formula or geometric target is used.
    The spatial pair measure is 8*pi^2*p*q*r dp dq dr; time overlap is L-s.
    """
    nodes, weights = gauss_rule(order)
    pieces = []
    for p, wp in zip(cap.radius * (nodes + 1) / 2, cap.radius * weights / 2):
        height = cap.depth * (1 - (p / cap.radius)**2)
        lo, hi = max(0, p - height / (1 - cap.lam)), min(cap.radius, p + height / (1 - cap.lam))

        def gap(q):
            return height + cap.shift(q) - cap.shift(p) - abs(p - q)

        if gap(lo) < 0:
            lo = brentq(gap, lo, p)
        if gap(hi) < 0:
            hi = brentq(gap, p, hi)
        for qa, qb in ((lo, p), (p, hi)):
            for q, wq in zip((qa + qb) / 2 + (qb - qa) / 2 * nodes, (qb - qa) / 2 * weights):
                L = height + cap.shift(q) - cap.shift(p)
                rlo, rhi = abs(p - q), min(p + q, L)
                if rhi <= rlo:
                    continue
                r = ((rlo + rhi) / 2 + (rhi - rlo) / 2 * nodes)[:, None]
                s = r + (L - r) * (nodes[None, :] + 1) / 2
                values = r * (L - s) * bdg_kernel(C_INTERVAL * rho * (s*s - r*r)**2)
                inner = np.sum(values * weights[:, None] * (rhi - rlo) / 2
                               * weights[None, :] * (L - r) / 2)
                pieces.append(wp * wq * p * q * inner)
    return 8 * math.pi**2 * math.fsum(pieces)


class TwoFaceDiagnosticsTest(unittest.TestCase):
    def assertNear(self, actual, expected, tolerance=1e-10):
        self.assertLessEqual(abs(float(actual) - float(expected)), tolerance * max(1, abs(float(expected))))

    def test_raw_profiles_envelopes_and_exact_volume(self):
        for cap in (AxialCap(), RadialCap()):
            outside = region_data(cap, (4, 0, 0))
            self.assertLess(outside["raw_height"], 0)
            self.assertGreater(outside["lower_raw"], outside["upper"])
            self.assertEqual(outside["lower_envelope"], outside["upper"])
            self.assertFalse(contains(cap, outside["upper"], (4, 0, 0)))
            inside = region_data(cap, (0, 0, 0))
            self.assertTrue(contains(cap, (inside["lower_raw"] + inside["upper"]) / 2, (0, 0, 0)))
            self.assertFalse(contains(cap, inside["upper"], (0, 0, 0)))
            # Integrate h over a scaled unit ball, independently of cap.volume.
            product = cap.radius**3 if isinstance(cap, RadialCap) else math.prod(cap.axes)
            volume = 4 * math.pi * product * quadrature(lambda r: r**2 * cap.depth * (1 - r**2), [0, 1], 12)
            self.assertNear(volume, cap.volume)
            self.assertNear(cap.dilated(1.7).volume, 1.7**4 * cap.volume)

    def test_strict_margins_and_matched_neighborhood(self):
        cap = RadialCap()
        self.assertLess(cap.slope_budget, 1)
        self.assertNear(abs(cap.shift_prime(cap.core / math.sqrt(7))), cap.lam)
        for r in (0.7, 0.9, 1, 1.1):
            self.assertEqual(cap.shift(r), 0)
            self.assertEqual(cap.shift_prime(r), 0)
        # Neither face is affine on the interior.
        self.assertNotEqual(cap.shift(0), cap.shift(0.2))
        for cap in (cap, AxialCap()):
            length = cap.radius if isinstance(cap, RadialCap) else cap.axes[0]
            for q in np.linspace(-length, length, 21):
                self.assertLessEqual(abs(cap.shift_prime(q)), cap.lam + 1e-15)
                for p in np.linspace(-length, length, 21):
                    self.assertLessEqual(abs(cap.shift(q) - cap.shift(p)), cap.lam * abs(q - p) + 1e-15)
        # Actual causal interval samples in the interior. Analytic convexity
        # follows from the global envelope slope bounds, not this finite grid.
        cap = AxialCap()
        for t in np.linspace(-0.19, -0.06, 7):
            for x in np.linspace(-0.01, 0.01, 5):
                self.assertTrue(contains(cap, t, (x, 0, 0)))

    def test_signed_kernel_and_transverse_control(self):
        self.assertLess(bdg_kernel(1), 0)
        for x in (0, 0.3, 1, 5, 20):
            self.assertNear(bdg_kernel(x), kernel(x), 1e-14)
        with mp.workdps(35):
            for j, expected in enumerate((0, 0, 0, -mp.mpf("0.5"))):
                integral = mp.quad(lambda z: z**j * kernel(z*z), [0, 1, 2, 4, 8, mp.inf])
                self.assertLess(abs(integral - expected), mp.mpf("1e-30"))

    def test_overlap_and_translated_tangency(self):
        base = AxialCap(bend=0)
        for s in (0, 0.1, 0.249, 0.25, 0.3):
            self.assertNear(axial_overlap(base, s, s / 2), ellipsoid_overlap(s, base.depth, base.axes), 1e-13)
        self.assertNear(axial_null_contact(base), base.depth, 1e-14)
        cap = AxialCap()
        contact = axial_null_contact(cap)
        self.assertGreater(contact, cap.depth)
        values = [axial_overlap(cap, contact * (1 - gap), contact * (1 - gap)) for gap in (0.01, 0.001)]
        self.assertGreater(values[1], 0)
        # A fractional-power contact exists; do NOT treat overlap as globally C3.
        self.assertNear(values[0] / values[1], 10**2.5, 0.001)
        self.assertEqual(axial_overlap(cap, contact * 1.001, contact * 1.001), 0)

    def test_actual_long_density_against_independent_high_precision_integral(self):
        for sigma in (0, 0.001, 0.01):
            with mp.workdps(40):
                low = planar_density_reference(str(sigma), "0.15")
            with mp.workdps(60):
                high = planar_density_reference(str(sigma), "0.15")
                self.assertLess(abs(low - high), mp.mpf("1e-39"))
            for cap, multiplier in ((AxialCap(bend=0), 1), (RadialCap(bend=0), 6)):
                self.assertNear(multiplier * overlap_density(cap, sigma, 0.15, 24), high, 2e-10)

    def test_density_support_cutoff_and_scaling(self):
        for cap in (AxialCap(), RadialCap()):
            full = overlap_density(cap, 0.001, order=20)
            long = overlap_density(cap, 0.001, 0.15, 20)
            self.assertTrue(0 < long < full)
            self.assertEqual(overlap_density(cap, cap.sigma_max, order=20), 0)
            self.assertEqual(overlap_density(cap, 0, 3 * cap.time_bound, 20), 0)
            s = 1.7
            self.assertNear(overlap_density(cap.dilated(s), 0.001 * s*s, 0.15 * s, 20), s**6 * long, 1e-12)

    def test_independent_joint_target_and_negative_control(self):
        base, bend = AxialCap(bend=0), AxialCap()
        geometry = joint_geometry(base, 24)
        self.assertNear(geometry["target"], ellipsoid_limit(0.25, (1, 2, 3)), 1e-12)
        low, high = joint_geometry(bend, 24), joint_geometry(bend, 40)
        self.assertNear(low["target"], high["target"], 1e-9)
        self.assertLess(high["target"], high["euclidean_wrong_target"])
        self.assertLess(high["area_lorentz"], geometry["area_lorentz"])
        self.assertGreater(high["sampled_angle_min"], 0)
        sphere = joint_geometry(RadialCap(), 16)
        self.assertNear(sphere["target"], 8 * math.pi, 1e-12)
        self.assertNear(sphere["area_lorentz"], 4 * math.pi, 1e-12)

    def test_finite_density_calibration_boost_and_regime_accounting(self):
        cap, rho = AxialCap(bend=0), 10000
        with mp.workdps(40):
            reference = ellipsoid_action(rho, cap.depth, cap.axes)
        result = action(cap, rho, 16)
        self.assertNear(result["action"], reference, 2e-8)
        self.assertNear(result["point"] - result["pair"], result["action"], 1e-13)
        self.assertNear(result["pair"], sum(result[k] for k in ("pair_diagonal", "pair_long_near_null", "pair_long_timelike")), 1e-13)
        self.assertGreater(result["absolute_pair"], abs(result["pair"]))
        self.assertGreater(result["cancellation_ratio"], 1)
        changed_cut = action(cap, rho, 16, delta=0.12, sigma_split=0.005)
        self.assertNear(changed_cut["action"], result["action"], 2e-8)
        for beta in (0, -0.6, 0.6):
            self.assertNear(boosted_ellipsoid_action(rho, beta=beta, order=24), reference, 2e-8)

    def test_curved_radial_pair_against_unreduced_causal_integral(self):
        cap, rho = RadialCap(), 10000
        reduced = action(cap, rho, 24)["action"]
        values = [NORMALIZATION * math.sqrt(rho) * (cap.volume - rho * direct_radial_pair(cap, rho, n))
                  for n in (24, 48)]
        self.assertLess(abs(values[1] - reduced), abs(values[0] - reduced))
        self.assertNear(values[1], reduced, 5e-8)

    def test_nonplanar_action_dilation_and_refinement(self):
        cap, s, rho = AxialCap(), 1.7, 1000
        low = action(cap, rho * s**4, 12)["action"]
        high = action(cap, rho * s**4, 20)["action"]
        self.assertNear(low, high, 2e-7)
        scaled = action(cap.dilated(s), rho, 20, delta=0.15*s, sigma_split=0.01*s*s)["action"]
        self.assertNear(scaled, s*s * high, 1e-12)

    def test_quadratic_probe_does_not_hide_log_obstruction(self):
        for h in (0.001, 0.0005, 0.00025):
            points = [k*h for k in range(4)]
            self.assertNear(quadratic_remainder_probe([2 - 3*s + 4*s*s for s in points], h), 0, 2e-8)
            self.assertNear(quadratic_remainder_probe([s**3 for s in points], h), 6*h, 1e-14)
            log_values = [0] + [s*s * math.log(s) for s in points[1:]]
            self.assertNear(quadratic_remainder_probe(log_values, h), 9*math.log(3) - 12*math.log(2), 1e-12)

    def test_invalid_parameters(self):
        for make in (lambda: AxialCap(depth=0), lambda: AxialCap(axes=(1, 2)),
                     lambda: AxialCap(bend=float("nan")), lambda: AxialCap(bend=0.5),
                     lambda: AxialCap(axes=(0.1, 1, 1)), lambda: RadialCap(core=1.1),
                     lambda: RadialCap(core=0.1), lambda: RadialCap(bend=float("inf"))):
            with self.assertRaises(ValueError):
                make()
        for call in (lambda: action(AxialCap(), 0), lambda: action(AxialCap(), 1, delta=0),
                     lambda: overlap_density(AxialCap(), -1), lambda: overlap_density(AxialCap(), 0, -1),
                     lambda: overlap_density(AxialCap(), 0, order=3), lambda: axial_overlap(AxialCap(), 0, 1),
                     lambda: boosted_ellipsoid_action(1, beta=1), lambda: AxialCap().dilated(0),
                     lambda: quadratic_remainder_probe([1, 2], 0.1)):
            with self.assertRaises(ValueError):
                call()


if __name__ == "__main__":
    unittest.main()
