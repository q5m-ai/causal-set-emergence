"""Finite regressions of the first-cut written proof, not its certification."""

from itertools import product
import math
import unittest

import numpy as np
from scipy.integrate import quad

from dimension_kernels import interval_coefficient
from first_cut_flat_torus import (
    actual_interval, causal_lifts, circle_interval_distance, first_cut_geometry,
    null_excesses, overlap_leading, overlap_volume, quotient_distance,
    two_route_volume,
)
from full_partner_globalization import torus_long_density


class FirstCutFlatTorusTest(unittest.TestCase):
    def test_exact_band_and_no_silent_thin_or_higher_cut_fallback(self):
        self.assertEqual(first_cut_geometry(7, 1, .6), (1., .6))
        for d in (True, 1, 3.5):
            with self.assertRaises(ValueError):
                first_cut_geometry(d, 1, .6)
        for duration in (.4, .5, 1/math.sqrt(2), .8, math.inf):
            with self.assertRaises(ValueError):
                first_cut_geometry(4, 1, duration)
        for length in (0, -1, math.nan):
            with self.assertRaises(ValueError):
                first_cut_geometry(4, length, .6)
        # The existing thin theorem is not extended in place.
        with self.assertRaises(ValueError):
            torus_long_density(4, 1, .6, .1, .01)
        with self.assertRaises(ValueError):
            causal_lifts(3, 1, .72, [.5, .5])
        with self.assertRaises(ValueError):
            two_route_volume(4, 1, .5, .5)

    def test_complete_lift_enumeration_against_lattice_and_null_ties(self):
        rng = np.random.default_rng(149)
        for d in (2, 3, 4, 5, 7):
            for _ in range(8):
                a = rng.uniform(-.5, .5, d-1)
                tau = rng.uniform(.1, .7)
                brute = [a+np.array(m) for m in product((-1, 0, 1), repeat=d-1)
                         if np.linalg.norm(a+np.array(m)) <= tau]
                observed = causal_lifts(d, 1, tau, a)
                key = lambda b: tuple(np.round(b, 12))
                self.assertEqual({key(b) for b in observed}, {key(b) for b in brute})
                self.assertLessEqual(len(observed), 2)
                if len(observed) == 2:
                    self.assertAlmostEqual(np.linalg.norm(observed[0]-observed[1]), 1)
            self.assertEqual(len(causal_lifts(d, 1, .5, [.5]+[0.]*(d-2))), 2)
        # Beyond the approved upper bound an actual four-lift corner appears.
        corner = [np.array([.5, .5])+m for m in map(np.array, product((-1, 0), repeat=2))]
        self.assertEqual(sum(np.linalg.norm(b) < .72 for b in corner), 4)

    def test_null_excess_identities_and_true_common_overlap(self):
        nodes, weights = np.polynomial.legendre.leggauss(160)
        a = (nodes+1)/2
        weight = np.outer(weights, weights)/4
        for d in (2, 3, 4, 7):
            x, y = .11, .055
            u, v = null_excesses(1, x, y)
            self.assertAlmostEqual(u*(1+v), x)
            self.assertAlmostEqual(v*(1+u), y)
            aa, bb = np.meshgrid(a, a, indexing='ij')
            radius = np.minimum(aa*bb, np.minimum(
                (1-aa)*(1+1/v-bb), (1+1/u-aa)*(1-bb)))
            q = d/2
            vp = math.pi**(q-1)/math.gamma(q)
            independent = vp/2*(u*v)**q*np.sum(weight*radius**(q-1))
            h = overlap_volume(d, 1, x, y)
            self.assertAlmostEqual(h, independent, delta=2e-5*max(h, 1e-12))
            self.assertAlmostEqual(h, overlap_volume(d, 1, y, x), delta=2e-12*h)
            self.assertLessEqual(h, overlap_leading(d, 1, x, y))
        self.assertEqual(overlap_volume(5, 1, 0, .1), 0)
        self.assertEqual(overlap_volume(5, 1, .1, 0), 0)

    def test_both_overlap_components_against_literal_circle_interval(self):
        for tau in (.2, .49, .51, .6, .69):
            for a in (.01, .21, .4, .49, .5, .51, .8, 1.49):
                actual = actual_interval(2, 1, tau, [a])
                literal = circle_interval_distance(1, tau, a)
                self.assertAlmostEqual(actual, literal, delta=2e-15)
        tau, a = .64, .48
        phases = [tau*tau-float(b@b) for b in causal_lifts(2, 1, tau, [a])]
        c = float(interval_coefficient(2))
        summed = c*sum(phases)
        h = overlap_volume(2, 1, *phases)
        literal = circle_interval_distance(1, tau, a)
        self.assertAlmostEqual(summed-2*h, literal)
        self.assertGreater(abs(summed-h-literal), .005)
        self.assertGreater(abs(summed-literal), .01)
        self.assertGreater(abs(c*max(phases)-literal), .01)

    def test_actual_three_dimensional_distance_integral(self):
        tau, target = .68, np.array([.49, .06])
        actual = actual_interval(3, 1, tau, target)
        results = []
        for order in (96, 192):
            nodes, weights = np.polynomial.legendre.leggauss(order)
            xx, yy = np.meshgrid(nodes/2, nodes/2, indexing='ij')
            points = np.stack((xx, yy), axis=-1)
            r0 = np.linalg.norm(points, axis=-1)
            r1 = np.linalg.norm((points-target+.5) % 1-.5, axis=-1)
            results.append(np.sum(np.outer(weights, weights)/4*np.maximum(tau-r0-r1, 0)))
        self.assertAlmostEqual(actual, results[-1], delta=8e-6)
        self.assertLess(abs(results[-1]-actual), abs(results[0]-actual))

    def test_uniform_overlap_scaling_and_fractional_dimensions(self):
        for d in (2, 3, 4, 5, 8, 11):
            errors = []
            for w in (.01, .002, .0004):
                h = overlap_volume(d, 1, .7*w, .2*w)
                leading = overlap_leading(d, 1, .7*w, .2*w)
                ratio = h/leading
                self.assertGreater(ratio, 0)
                self.assertLessEqual(ratio, 1+1e-12)
                errors.append(1-ratio)
            self.assertLess(errors[2], errors[1])
            self.assertLess(errors[1], errors[0])
            self.assertLess(errors[2], .02)

    def test_measure_scaling_symmetry_single_lift_and_seams(self):
        for d in (2, 3, 4, 7):
            vector = [.49]+[.03]*(d-2)
            base = actual_interval(d, 1, .65, vector)
            self.assertAlmostEqual(actual_interval(d, 2, 1.3, np.array(vector)*2),
                                   base*2**d, delta=1e-11*base*2**d)
            self.assertAlmostEqual(actual_interval(d, 1, .65, -np.array(vector)),
                                   base, delta=1e-12*base)
            self.assertAlmostEqual(actual_interval(d, 1, .65, np.array(vector)+2),
                                   base, delta=1e-12*base)
            c = float(interval_coefficient(d))
            self.assertAlmostEqual(actual_interval(d, 1, .2, [.95]+[0]*(d-2)),
                                   c*(.2**2-.05**2)**(d/2))
            self.assertEqual(actual_interval(d, 1, .1, [.4]+[0]*(d-2)), 0)
        self.assertAlmostEqual(quotient_distance([.4, .4], 1), math.sqrt(.32))


if __name__ == '__main__':
    unittest.main()
