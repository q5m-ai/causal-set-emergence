"""Required curved-null continuation: exact identities, not a limit claim."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from curved_null_contacts import full_action, independent_target, pair_integral, point_volume, source_gaussian_mismatch
from null_mixed import SineMixedCap


class CurvedNullContactTests(unittest.TestCase):
    def test_null_face_clearance_and_rank_do_not_inherit_spacelike_proof(self):
        r, small = 0.8, 0.3
        omega = np.array([1.0, 0, 0])
        for eps in (1e-2, 1e-4, 1e-6):
            p, q = np.r_[-r-2*eps, r*omega], np.r_[-small-eps, small*omega]
            self.assertGreater(p[0], -1)
            self.assertGreater(q[0], -1)
            self.assertLess(p[0]+np.linalg.norm(p[1:]), 0)
            self.assertLess(q[0]+np.linalg.norm(q[1:]), 0)
            displacement = q-p
            self.assertGreater(displacement[0], 0.49)  # fixed macroscopic partner
            self.assertGreater(displacement[0]**2-np.dot(displacement[1:], displacement[1:]), 0)
        conormal = np.r_[1, omega]
        generator = np.r_[1, -omega]
        self.assertEqual(np.dot(conormal, generator), 0)
        self.assertNotEqual(np.dot([1, 0, 0, 0], generator), 0)

    def test_exact_curved_source_moment_refutes_only_gaussian_shortcut(self):
        u, r, D, b = s.symbols("u r D b", positive=True)
        sigma = u*u-r*r
        h = 1+b*(D*D-D*u+s.Rational(3, 10)*u*u-sigma/30)
        primitive = s.integrate(4*s.pi*r*r*(1+b*(u-D)**2)*(s.pi/24)*sigma*sigma*h, r)
        moment = s.factor(s.integrate(primitive.subs(r, u), (u, 0, D/2))
                          + s.integrate(primitive.subs(r, D-u), (u, D/2, D)))
        volume = s.pi/24*D**4*(1+s.Rational(4, 15)*b*D*D)
        # K(z)=1-10z+..., NOT 1-9z: the exponential also differentiates.
        expected = s.pi**2*D**10*b*(2400-439*D*D*b)/58060800
        self.assertEqual(s.factor(10*moment-volume*volume/2-expected), 0)
        for depth in (0.25, 0.5, 0.9):
            self.assertAlmostEqual(source_gaussian_mismatch(depth), float(expected.subs({D: depth, b: 1})), places=16)
            self.assertGreater(source_gaussian_mismatch(depth), 0)
        self.assertEqual(s.simplify(expected.subs(b, 0)), 0)

    def test_exact_full_pair_reduction_flat_calibration_and_refinement(self):
        flat = SineMixedCap(epsilon=0)
        for rho in (1, 20, 100):
            actual = full_action(rho, b=0, order=32)
            self.assertAlmostEqual(actual, flat.action(rho, 16), delta=1e-8)
            low, high = full_action(rho, order=32), full_action(rho, order=48)
            self.assertAlmostEqual(low, high, delta=1e-8)
            self.assertGreater(high, 0)
        self.assertAlmostEqual(point_volume(), 5*math.pi/9, places=14)

    def test_independent_curved_bulk_and_joint_target(self):
        bulk = math.pi*quad(lambda u: u**3*(2-u*u)/(1+u*u)**1.5, 0, 1)[0]
        joint = 4*math.pi*math.sqrt(2)
        self.assertAlmostEqual(bulk+joint, independent_target(), places=12)
        self.assertGreater(bulk, 0)
        # A finite-density action is not identified with the candidate target.
        self.assertGreater(abs(full_action(20)-independent_target()), 1)

    def test_fixed_cutoff_complement_retained_not_set_to_zero(self):
        rho = 20
        whole = pair_integral(rho, order=40)
        long = pair_integral(rho, order=40, min_gap=0.2)
        self.assertGreater(abs(long), 1e-4)
        self.assertGreater(abs(whole-long), 1e-5)
        # The exact inverse phase is regular for fixed gap, not uniformly at 0.
        for v, gap, sigma in ((0, 0.2, 0), (0.3, 0.4, 0.1), (0.1, 0.8, 0.6)):
            h = 1+v*v+v*gap+0.3*gap*gap-sigma/30
            derivative = math.sqrt(h)-sigma/(60*math.sqrt(h))
            self.assertGreater(derivative, 0.9)

    def test_invalid_inputs(self):
        for rho, b, cutoff in ((0, 1, 0), (1, -1, 0), (1, 1, 1), (math.nan, 1, 0)):
            with self.assertRaises(ValueError):
                pair_integral(rho, b, min_gap=cutoff)
        for depth in (0, 1, math.nan):
            with self.assertRaises(ValueError):
                source_gaussian_mismatch(depth)


if __name__ == "__main__":
    unittest.main()
