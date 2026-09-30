"""Finite-density assembly regressions, not proofs of a curved-face limit.

Independent geometry and direct overlaps test the signed normalization and
source partition. Neither quadrature refinement nor cutoff agreement certifies
an asymptotic bound. The conventional argument fixes the cutoff before rho.
"""

import math
import unittest

import numpy as np

from short_displacement import axial_jet, axial_short_density
from two_face_diagnostics import AxialCap, action, joint_geometry, overlap_density, quadrature


class TwoFaceAssemblyTest(unittest.TestCase):
    def test_overlapping_three_source_partition_and_independent_joint(self):
        cap = AxialCap()
        a, b, c = cap.axes
        weights = [lambda x: (1+x/a)**2/4, lambda x: (1-x/a)**2/4,
                   lambda x: (1-(x/a)**2)/2]
        derivatives = [lambda x: (1+x/a)/(2*a), lambda x: -(1-x/a)/(2*a),
                       lambda x: -x/a**2]
        pieces = [axial_jet(cap, weight=w, weight_prime=dw)
                  for w, dw in zip(weights, derivatives)]
        # Spatial projected coarea for this ellipsoid, with the two-normal
        # numerator. No action value or fitted jet enters this calculation.
        targets = [math.pi*b*c/cap.depth * quadrature(
            lambda x: w(x)*(1-cap.shift_prime(x)**2
                           -2*cap.depth*x/a**2*cap.shift_prime(x)), [-a, 0, a], 40)
                   for w in weights]
        self.assertGreater(max(abs(p['cutoff_derivative']) for p in pieces), 0.1)
        for piece, target in zip(pieces, targets):
            self.assertAlmostEqual(piece['joint_coefficient'], target, places=10)
            self.assertAlmostEqual(piece['short_limit_coefficient'],
                                   target+piece['cutoff_derivative'], places=10)
        self.assertAlmostEqual(math.fsum(p['cutoff_derivative'] for p in pieces), 0, places=12)
        self.assertAlmostEqual(math.fsum(targets), joint_geometry(cap, 40)['target'], places=9)
        np.testing.assert_allclose(sum(p['angular'] for p in pieces), axial_jet(cap)['angular'],
                                   rtol=2e-14, atol=2e-12)
        # Every weighted source retains its entire partner domain. We do NOT
        # integrate isolated chart regions and add their actions.
        sigma, delta = 0.0003, 0.08
        weighted = [axial_short_density(cap, sigma, delta, 16, weight=w) for w in weights]
        self.assertAlmostEqual(math.fsum(weighted),
                               axial_short_density(cap, sigma, delta, 16), places=12)

    def test_short_annulus_uses_the_same_long_density(self):
        cap = AxialCap()
        small, large = 0.07, 0.13
        # Include both sides of the smaller cutoff square: the max(delta,sqrt
        # sigma) endpoint must not be replaced unconditionally by delta.
        for sigma in (0.0003, small**2, 0.009):
            short_difference = (axial_short_density(cap, sigma, large, 24)
                                -axial_short_density(cap, sigma, small, 24))
            long_difference = (overlap_density(cap, sigma, small, 28)
                               -overlap_density(cap, sigma, large, 28))
            self.assertGreaterEqual(short_difference, 0)
            self.assertAlmostEqual(short_difference, long_difference, places=10)

    def test_fixed_cutoff_changes_pieces_not_full_action(self):
        cap = AxialCap()
        values = [action(cap, 10000, order=20, delta=d) for d in (0.07, 0.12, 0.2)]
        short = [r['point']-r['pair_diagonal'] for r in values]
        long = [r['pair_long_near_null']+r['pair_long_timelike'] for r in values]
        self.assertGreater(max(short)-min(short), 100)
        self.assertGreater(min(abs(x) for x in long), 10)
        for i in (1, 2):
            # Separate quadrature panels are chosen at each actual cutoff.
            # This tolerance is a regression threshold, not certified error.
            self.assertAlmostEqual(values[i]['action'], values[0]['action'], delta=2e-6)
            self.assertAlmostEqual(short[i]-short[0], long[i]-long[0], delta=2e-6)
        # Dropping the finite-density long contribution would fail badly.
        self.assertGreater(abs(short[0]-values[0]['action']), 100)


if __name__ == '__main__':
    unittest.main()
