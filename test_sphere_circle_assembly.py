"""Finite diagnostics for #153, not a numerical or probabilistic limit proof."""

import unittest

import numpy as np

from sphere_circle_assembly import (
    LAYER_WEIGHTS, NORMALIZATION, SECTORS, SLAB_MASS, SPATIAL_MASS,
    check_assembly_identities, layer_counts, original_pair_integral,
    pair_quadrature, related,
)
from sphere_circle_focusing import time_weight


class SphereCircleAssemblyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rule = pair_quadrature(order=22, volume_order=28)

    def test_exact_normalization_and_independent_curvature(self):
        check_assembly_identities()
        self.assertAlmostEqual(SLAB_MASS, 320*np.pi)
        self.assertAlmostEqual(SPATIAL_MASS, 80*np.pi)

    def test_full_pair_against_independent_original_time_and_circle_integral(self):
        # Finite density only. Both integrate the actual W, but the original
        # integral does not use G, reduced sector weights or an asymptotic jet.
        rho = .03
        full = self.rule.evaluate(rho)["pairs"]["full"]
        coarse = original_pair_integral(rho, order=8, volume_order=16)
        refined = original_pair_integral(rho, order=12, volume_order=24)
        self.assertLess(abs(refined-full), .04)
        self.assertLess(abs(refined-full), abs(coarse-full)/5)
        self.assertGreater(abs(full), 10000)

    def test_each_F20_sector_and_point_is_restored_at_finite_density(self):
        for rho in (.03, .4):
            result = self.rule.evaluate(rho)
            pairs, actions = result["pairs"], result["actions"]
            self.assertAlmostEqual(sum(pairs[s] for s in SECTORS), pairs["full"], places=9)
            self.assertAlmostEqual(sum(actions[s] for s in SECTORS), actions["full"], places=9)
            for name in SECTORS:
                self.assertGreater(abs(actions[name]), .005)
                # An omitted sector is a real error, even if its limit is zero.
                omitted = sum(actions[s] for s in SECTORS if s != name)
                self.assertAlmostEqual(actions["full"]-omitted, actions[name], places=9)
            point = NORMALIZATION*np.sqrt(rho)*SLAB_MASS
            long_pairs = sum(pairs[s] for s in ("offcut", "cut", "excess"))
            self.assertAlmostEqual(sum(actions[s] for s in ("offcut", "cut", "excess")),
                                   -NORMALIZATION*rho**1.5*long_pairs, places=9)
            self.assertGreater(abs(point), 100)
            for wrong in (sum(actions[s] for s in SECTORS)+3*point,
                          sum(actions[s] for s in SECTORS)-point,
                          actions["short"]-sum(actions[s] for s in ("offcut", "cut", "excess"))):
                self.assertGreater(abs(wrong-actions["full"]), 100)

    def test_same_full_action_with_different_fixed_artificial_boundaries(self):
        rho = .03
        first = self.rule.evaluate(rho)
        second = pair_quadrature(delta=.12, a0=.1, e0=.25, order=22,
                                 volume_order=28).evaluate(rho)
        # Independently split panels, NOT a full value defined as a sector sum.
        self.assertAlmostEqual(first["pairs"]["full"], second["pairs"]["full"], delta=3e-5)
        for name in SECTORS:
            self.assertGreater(abs(first["pairs"][name]-second["pairs"][name]), .5)
        self.assertAlmostEqual(sum(second["actions"][s] for s in SECTORS),
                               first["actions"]["full"], delta=3e-7)

    def test_positive_geometric_weights_keep_reduced_overlap(self):
        for weights in self.rule.weights.values():
            self.assertTrue(np.all(weights >= 0))
        np.testing.assert_allclose(sum(self.rule.weights[s] for s in SECTORS),
                                   self.rule.weights["full"], rtol=2e-15, atol=1e-13)
        self.assertTrue(np.all(self.rule.volumes > 0))
        self.assertTrue(np.all(self.rule.volumes < SLAB_MASS))
        # Long and short overlap in reduced coordinates, but not in original
        # tau/b. Treating this overlap as duplicate original partners is wrong.
        overlap = (self.rule.weights["short"] > 0) & (self.rule.weights["offcut"] > 0)
        self.assertGreater(np.count_nonzero(overlap), 100)
        self.assertGreater(self.rule.weights["offcut"][overlap].sum(), 1.)
        for u in (.001, .01):
            self.assertGreater(time_weight(u, .2), 0)
            self.assertAlmostEqual(time_weight(u, .2)+time_weight(u, .2, short=True),
                                   time_weight(u), places=14)

    def test_actual_layer_integrals_and_both_factorial_density_factors(self):
        # Finite coefficient/count-factor identity, not a new law simulation.
        for rho in (.03, .4):
            result = self.rule.evaluate(rho)
            pairs, layers = result["pairs"], result["layer_integrals"]
            self.assertTrue(np.all(layers > 0))
            self.assertAlmostEqual(LAYER_WEIGHTS @ layers, pairs["full"], places=9)
            mean_n = rho*SLAB_MASS
            mean_layers = rho*rho*layers
            mean_action = NORMALIZATION/np.sqrt(rho)*(mean_n-LAYER_WEIGHTS @ mean_layers)
            self.assertAlmostEqual(mean_action, result["actions"]["full"], places=9)
            wrong_brackets = (
                mean_n-LAYER_WEIGHTS @ mean_layers/rho,  # lost target density
                mean_n-LAYER_WEIGHTS @ mean_layers/2,    # unordered-pair error
                mean_n-LAYER_WEIGHTS @ mean_layers/SPATIAL_MASS,  # lost source volume
                mean_n-LAYER_WEIGHTS @ mean_layers/20,   # probability circle measure
            )
            for wrong in wrong_brackets:
                self.assertGreater(abs(NORMALIZATION/np.sqrt(rho)*wrong-mean_action), 10.)

    def test_selected_null_antipodal_order_and_only_endpoint_removal(self):
        north, equator, south = (0., 0., 1.), (1., 0., 0.), (0., 0., -1.)
        x, z, y = (-np.pi/2, north, 0.), (0., equator, 0.), (np.pi/2, south, 0.)
        self.assertTrue(all(-2 < p[0] < 2 for p in (x, z, y)))
        self.assertTrue(related(x, z) and related(z, y) and related(x, y))
        self.assertFalse(related(y, x))
        np.testing.assert_array_equal(layer_counts([x, y]), [1, 0, 0, 0])
        np.testing.assert_array_equal(layer_counts([x, z, y]), [2, 1, 0, 0])
        np.testing.assert_array_equal(layer_counts([y, x, z]), [2, 1, 0, 0])
        self.assertEqual(3-LAYER_WEIGHTS @ layer_counts([x, z, y]), 10)
        # Counting selected endpoints changes layers. Deleting the null-related
        # midpoint likewise destroys the genuine one-point interval.
        inclusive_count = sum(related(x, p) and related(p, y) for p in (x, z, y))
        self.assertEqual(inclusive_count, 3)
        self.assertNotEqual(inclusive_count, 1)
        # Chord distance 2 would incorrectly admit this noncausal antipodal pair.
        self.assertFalse(related((-1.1, north, 0.), (1.1, south, 0.)))

    def test_circle_seams_product_distance_and_cross_chart_pairs(self):
        north, equator = (0., 0., 1.), (1., 0., 0.)
        x, y = (-.5, north, 19.5), (.5, north, .5)
        self.assertTrue(related(x, y))  # actual seam-crossing circle distance 1
        np.testing.assert_array_equal(layer_counts([x, y]), [1, 0, 0, 0])
        np.testing.assert_array_equal(layer_counts([x, y], labels=[0, 1]), [0, 0, 0, 0])
        self.assertEqual(2-LAYER_WEIGHTS @ layer_counts([x, y]), 1)
        self.assertEqual(2-LAYER_WEIGHTS @ layer_counts([x, y], labels=[0, 1]), 2)
        # max(pi/2,1) < 1.8 < hypot(pi/2,1): rejects the max-metric surrogate.
        self.assertFalse(related((-.9, north, 0.), (.9, equator, 1.)))
        self.assertLess(max(np.pi/2, 1), 1.8)

    def test_invalid_diagnostic_parameters(self):
        for kwargs in ({"delta": 0}, {"delta": .25}, {"a0": 0}, {"e0": 4-np.pi}):
            with self.assertRaises(ValueError):
                pair_quadrature(**kwargs)
        for rho in (0, -1, np.inf, np.nan):
            with self.assertRaises(ValueError):
                self.rule.evaluate(rho)


if __name__ == "__main__":
    unittest.main()
