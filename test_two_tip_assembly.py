"""TT-B full-union regressions; not a Monte Carlo or asymptotic proof."""

import math
import unittest

import numpy as np

from mixed_poisson import discrete_action, layer_counts
from two_tip_lens import LensOverlap
from two_tip_assembly import TwoTipAssembly


class TwoTipAssemblyTests(unittest.TestCase):
    def setUp(self):
        self.assembly = TwoTipAssembly()

    def test_direct_union_overlap_all_contacts_and_ordinary_volumes(self):
        assembly = self.assembly
        for tau, xi in ((0, 0), (0.2, 0.15), (0.5, -0.2), (0.75, 0.3), (1.01, -0.02)):
            overlaps = {k: assembly.overlap(k, tau, xi) for k in ("union", "lens", "plus", "minus")}
            self.assertAlmostEqual(overlaps["union"], overlaps["plus"]+overlaps["minus"]-overlaps["lens"], places=13)
            self.assertAlmostEqual(overlaps["lens"], LensOverlap().overlap(tau, xi), places=13)
            if tau == 0.75:  # Translated section has TWO disconnected spatial lobes.
                self.assertEqual(overlaps["lens"], 0)
                self.assertGreater(overlaps["plus"], 0)
                self.assertGreater(overlaps["minus"], 0)
        for kind, volume in assembly.region.volumes().items():
            self.assertAlmostEqual(assembly.overlap(kind, 0, 0), volume, places=12)

    def test_independent_joint_target_and_no_automatic_crease_weight(self):
        areas = self.assembly.region.joint_areas()
        self.assertAlmostEqual(areas["union"], areas["plus"]+areas["minus"]-areas["lens"], places=12)
        self.assertGreater(abs(areas["plus"]-areas["minus"]), 1)
        a = self.assembly.region.a
        crease = 2*math.pi*a*(1-a)
        self.assertGreater(crease, 1)
        self.assertNotAlmostEqual(areas["union"]+crease, areas["plus"]+areas["minus"]-areas["lens"])

    def test_full_finite_density_union_layers_and_point_once(self):
        for rho in (1, 20, 100):
            results = {kind: self.assembly.pair_integrals(kind, rho, 20)
                       for kind in ("union", "lens", "plus", "minus")}
            full, plus, minus, lens = [results[k] for k in ("union", "plus", "minus", "lens")]
            np.testing.assert_allclose(full.layers, np.array(plus.layers)+minus.layers-np.array(lens.layers),
                                       atol=3e-16, rtol=1e-12)
            self.assertAlmostEqual(full.action, plus.action+minus.action-lens.action, places=10)
            self.assertGreater(abs(full.action-(plus.action+minus.action)), 0.1)
            signed = np.dot(full.layers, [1, -9, 16, -8])
            self.assertAlmostEqual(full.signed, signed, places=13)
            refined = self.assembly.pair_integrals("union", rho, 32)
            self.assertAlmostEqual(full.action, refined.action, delta=1e-7)

    def test_actual_configuration_layers_restriction_and_partners(self):
        points = np.array([[-0.95, -0.03, 0.01, 0], [-0.8, 0.02, 0.02, 0],
                           [-0.64, 0, 0, 0], [-0.18, 0.49, 0.01, 0],
                           [-0.16, -0.49, 0.01, 0]])
        plus, minus = self.assembly.region.cap_masks(points)
        self.assertTrue((plus | minus).all())
        lens = plus & minus
        np.testing.assert_array_equal(layer_counts(points), np.array(layer_counts(points[plus]))
                                      + layer_counts(points[minus])-np.array(layer_counts(points[lens])))
        for rho in (1, 20, 100):
            full = discrete_action(rho, points)
            self.assertAlmostEqual(full, discrete_action(rho, points[plus])
                                   + discrete_action(rho, points[minus])-discrete_action(rho, points[lens]))
            wrong = sum(discrete_action(rho, points[mask])
                        for mask in (lens, plus & ~minus, minus & ~plus))
            self.assertNotAlmostEqual(wrong, full)
        # Point allocation is literal inclusion-exclusion, not two physical copies.
        np.testing.assert_array_equal(plus.astype(int)+minus.astype(int)-lens.astype(int), np.ones(len(points)))

    def test_actual_tip_neighborhoods_are_exclusive_not_lens(self):
        a = self.assembly.region.a
        for delta in (0.05, 0.1, 0.2):
            for sign in (-1, 1):
                points = np.array([[-0.8*delta, sign*a+0.2*delta, 0.1*delta, 0],
                                   [-0.5*delta, sign*a, 0, 0]])
                plus, minus = self.assembly.region.cap_masks(points)
                self.assertTrue((plus | minus).all())
                self.assertFalse((plus & minus).any())
                self.assertEqual(plus.all(), sign == 1)
                self.assertEqual(minus.all(), sign == -1)

    def test_invalid_inputs(self):
        with self.assertRaises(ValueError):
            self.assembly.overlap("other", 0, 0)
        with self.assertRaises(ValueError):
            self.assembly.overlap("union", math.nan, 0)
        for rho in (0, -1, math.inf):
            with self.assertRaises(ValueError):
                self.assembly.pair_integrals("union", rho)
        for mu in (-2, math.nan):
            with self.assertRaises(ValueError):
                self.assembly.time_breaks(mu)


if __name__ == "__main__":
    unittest.main()
