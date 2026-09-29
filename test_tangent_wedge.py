"""Independent regressions; numerical evidence is not the Lean audit."""

import unittest

from mpmath import mp
import numpy as np

from calculations import kernel, plane_kernel
from tangent_wedge import pair_action, profile_action, regulator_height


class TangentWedgeTests(unittest.TestCase):
    def test_original_pairs_against_reduced_signed_profile(self):
        with mp.workdps(30):
            for rho, slope, radius, power in (
                (8, "0.6", 1, 1), (256, "0.6", 1, 1),
                (32, "0.3", 2, 2), (512, "0.8", 1, 3),
            ):
                with self.subTest(rho=rho, slope=slope, power=power):
                    reference = float(profile_action(rho, slope, radius, power))
                    coarse = pair_action(rho, slope, radius, power, order=48)
                    fine = pair_action(rho, slope, radius, power, order=80)
                    self.assertAlmostEqual(fine, reference, delta=2e-11)
                    self.assertAlmostEqual(coarse, fine, delta=2e-11)

    def test_density_limit_and_cutoff_independence(self):
        # Different fixed regulators approach the same value; geometry does
        # not vary with density within any one sequence.
        with mp.workdps(25):
            for slope, radius, power in (("0.3", 1, 1), ("0.6", 2, 2), ("0.8", 1, 3)):
                with self.subTest(slope=slope, radius=radius, power=power):
                    target = 1 / mp.mpf(slope)
                    low = abs(profile_action(10**4, slope, radius, power) - target)
                    high = abs(profile_action(10**12, slope, radius, power) - target)
                    self.assertLess(high, low / 100)
                    self.assertLess(high / target, mp.mpf("0.0002"))

    def test_precision_and_dilation(self):
        values = []
        for precision in (25, 40):
            with mp.workdps(precision):
                values.append(profile_action(10**6, "0.6", 1, 2))
        self.assertLess(abs(values[0] - values[1]), mp.mpf("1e-22"))
        with mp.workdps(30):
            for scale in (mp.mpf(2), mp.mpf("0.5")):
                # Tangential area has degree two. Both regulator lengths and
                # density transform, while the angle remains fixed.
                original = profile_action(81 * scale**4, "0.6", 1, 2)
                dilated = scale**2 * profile_action(81, "0.6", scale, 2)
                self.assertLess(abs(dilated - scale**2 * original), mp.mpf("1e-27"))

    def test_induced_area_and_positive_angle_under_tangential_boost(self):
        metric = np.diag([1., -1., -1., -1.])
        k = 0.6
        past = np.array([1., -k, 0., 0.]) / np.sqrt(1 - k*k)
        future = np.array([1., 0., 0., 0.])
        tangents = np.array([[0., 0., 1., 0.], [0., 0., 0., 1.]])
        boost = np.array([[1.25, 0, .75, 0], [0, 1, 0, 0],
                          [.75, 0, 1.25, 0], [0, 0, 0, 1]])
        np.testing.assert_allclose(boost.T @ metric @ boost, metric, atol=1e-15)
        moved = tangents @ boost.T
        area = np.sqrt(np.linalg.det(-moved @ metric @ moved.T))
        wrong_area = np.sqrt(np.linalg.det(moved @ moved.T))
        C = (boost @ past) @ metric @ (boost @ future)
        theta = np.arccosh(C)
        self.assertGreater(theta, 0)
        self.assertAlmostEqual(area * C / np.sqrt(C*C - 1), 1/k)
        self.assertGreater(wrong_area, 1.4)  # Euclidean spacetime area is wrong.
        self.assertAlmostEqual(1/np.tanh(theta), 1/k)

    def test_regulator_margin_and_cross_patch_partner(self):
        # Source in the unit cube; partner outside it, but inside the finite
        # tent. Deleting this partner is not first-endpoint localization.
        source = np.array([-.2, .8, .9, 0.])
        partner = np.array([-.05, .8, 1.02, 0.])
        for height in (2., 4.):
            for point in (source, partner):
                self.assertTrue(-regulator_height(point[1:], .5, height) < point[0] < 0)
        displacement = partner - source
        sigma = displacement[0]**2 - np.dot(displacement[1:], displacement[1:])
        self.assertGreater(sigma, 0)
        self.assertGreater(np.max(np.abs(partner[1:])), 1)
        self.assertGreater(kernel(mp.pi * sigma**2 / 24), 0)
        for spatial in ((.2, .8, -.4), (.9, -.7, .3)):
            self.assertEqual(regulator_height(spatial, .5, 2), .5 * spatial[0])
        # The exact null partner is retained by the same complete-slice law.
        null_partner = source + np.array([.1, 0., .1, 0.])
        self.assertTrue(-regulator_height(null_partner[1:], .5, 2) < null_partner[0] < 0)

    def test_negative_parts_are_not_removed(self):
        self.assertLess(kernel(1), 0)
        self.assertLess(plane_kernel(4), 0)
        with mp.workdps(25):
            # Clipping the signed reduced kernel is a strict positive bias,
            # not another discretization of the claimed action.
            upper = mp.mpf(12)
            negative = mp.quad(lambda u: min(0, plane_kernel(u)) * (1-u/upper), [4, 8, 12])
            self.assertLess(negative, -mp.mpf("0.01"))

    def test_invalid_parameters(self):
        for function in (pair_action, profile_action):
            for args in ((0, .5), (1, 0), (1, 1), (1, .5, 0),
                         (1, .5, 1, 0), (1, .5, 1, True), (float("nan"), .5)):
                with self.subTest(function=function.__name__, args=args):
                    with self.assertRaises(ValueError):
                        function(*args)
        with self.assertRaises(ValueError):
            pair_action(1, .5, order=1)
        with self.assertRaises(ValueError):
            regulator_height([1, 2], .5, 2)


if __name__ == "__main__":
    unittest.main()
