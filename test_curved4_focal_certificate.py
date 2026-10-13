"""Certificate components and arithmetic replay, NOT a physical-action proof.

The full nodal regeneration is the separate documented CLI gate. These tests
replay the saved enclosure and independently exercise representative nodes.
"""
import copy
from fractions import Fraction as F
import json
import math
from pathlib import Path
import unittest
from unittest.mock import patch

from flint import arb, ctx
import numpy as np
from scipy.integrate import quad

import curved4_focal_certificate as c
from curved4_focal_geometry import model_averaged_profile, model_profile


class ExactHeadBoundsTest(unittest.TestCase):
    def test_all_explicit_rational_head_and_tail_bounds(self):
        checks = c.head_bound_checks()
        self.assertEqual(len(checks), 25)
        self.assertTrue(all(checks.values()))

    def test_primary_coefficients_and_beta_majorants(self):
        self.assertEqual(c.primary_coefficient(1), [-F(1, 4), 0, F(5)])
        self.assertEqual(c.primary_coefficient(2),
                         [F(35, 128), 0, -F(315, 16), 0, F(1155, 8)])
        self.assertEqual(c.primary_majorant(5), F(138567, 64))
        for j in range(1, 20):
            self.assertLess(c.primary_majorant(j+1), 16*c.primary_majorant(j))

    def test_machin_enclosure_and_binomial_tail(self):
        lo, hi = c.arctan_bounds(F(1, 5))
        self.assertLess(float(lo), math.atan(.2)+1e-16)
        self.assertGreater(float(hi), math.atan(.2)-1e-16)
        for n in (4, 8, 32):
            partial = sum(abs(c.binomial(F(3, 2), j)) for j in range(2, n+1))
            self.assertEqual(c.binomial_tail(n), F(1, 2)-partial)


class BallEnclosureTest(unittest.TestCase):
    def setUp(self):
        self.precision = ctx.prec
        ctx.prec = c.PRECISION

    def tearDown(self):
        ctx.prec = self.precision

    def test_gaussian_polynomial_exactness(self):
        n = 8
        rule = c.gaussian_rule(n)
        mass = 3*arb.pi()/128
        for degree in range(2*n):
            moment = mass
            for j in range(degree):
                moment *= (arb(5)/2+j)/(5+j)
            numerical = sum(w*t**degree for t, w in rule)
            self.assertTrue(numerical.overlaps(moment), degree)
            self.assertLess(float(numerical.rad()), 1e-20)

    def test_bad_gaussian_seed_fails_closed(self):
        c.gaussian_rule.cache_clear()
        with patch.object(c, 'roots_jacobi', return_value=(np.zeros(6), np.zeros(6))):
            with self.assertRaises(c.CertificateFailure):
                c.gaussian_rule(6)
        c.gaussian_rule.cache_clear()

    def test_all_wells_enclosed_against_independent_diagnostic(self):
        for e, r in ((F(3, 1000), F(0)), (F(1, 2500), F(49999, 100000)),
                     (F(7, 100), F(49, 100))):
            value, derivative = c.profile_and_derivative(e, r)
            diagnostic = model_profile(float(e), float(r), 256)
            self.assertLessEqual(float(value.lower()), diagnostic+1e-12)
            self.assertGreaterEqual(float(value.upper()), diagnostic-1e-12)
            self.assertLess(float(value.rad()), 1e-5*diagnostic)
            self.assertTrue(derivative == 0 if r == 0 else derivative > 0)

    def test_double_saddle_exact_value_and_derivative(self):
        value, derivative = c.profile_and_derivative(F(1, 16), F(1, 2))
        self.assertTrue(value.overlaps(1/(70*arb(2).sqrt())))
        self.assertTrue(derivative.overlaps(17/(20*arb(2).sqrt())))
        direct = quad(lambda u: -6*u**3*math.sqrt(max(0, 1/16-u*u-2*u**3-u**4)),
                      -.5-1/math.sqrt(2), -.5+1/math.sqrt(2), points=[-.5], epsabs=1e-12)[0]
        self.assertAlmostEqual(float(derivative.mid()), direct, delta=1e-11)
        for r in (-.5, .5):
            self.assertAlmostEqual(model_profile(1/16, r), 1/(70*math.sqrt(2)), delta=1e-16)

    def test_transition_energies_use_real_variable_bounds(self):
        for e in (F(1, 16), F(7, 100), F(1, 12)):
            value, count = c.certify_phi(e, relative_goal=1e-4)
            diagnostic = model_averaged_profile(float(e), 96)
            self.assertLess(float(value.lower()), diagnostic)
            self.assertGreater(float(value.upper()), diagnostic)
            self.assertGreater(count, 2)

    def test_energy_error_and_refinement(self):
        for lo, hi in ((F(1, 100), F(1, 50)), (F(3, 50), F(9, 100)), (F(1), F(2))):
            mid = (lo+hi)/2
            parent = c.energy_error(lo, hi)
            children = c.energy_error(lo, mid)+c.energy_error(mid, hi)
            self.assertTrue(parent > 0)
            self.assertTrue(children < parent/3)

    def test_outward_fixed_point_roundtrip(self):
        value = arb('1.23456789 +/- 0.0001')
        lo, hi = c.fixed_enclosure(value)
        decoded = (arb(lo)*arb(2)**-c.FIXED_BITS).union(arb(hi)*arb(2)**-c.FIXED_BITS)
        self.assertTrue(decoded.contains(value))

    def test_work_cap_fails_closed_if_positivity_is_unresolved(self):
        with self.assertRaises(c.CertificateFailure):
            c.certify_phi(F(1, 10), max_nodes=2)

    def test_guards_and_precision_restoration(self):
        for operation in (lambda: c.profile_and_derivative(0, 0),
                          lambda: c.profile_and_derivative(1, F(3, 5)),
                          lambda: c.gaussian_rule(3),
                          lambda: c.energy_error(F(1), F(0)),
                          lambda: c.energy_partition(float('nan'))):
            with self.assertRaises(c.CertificateFailure):
                operation()
        before = ctx.prec
        c.profile_and_derivative(F(1, 10), 0)
        self.assertEqual(ctx.prec, before)


class SavedModelEvidenceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = json.loads(Path('certificates/curved4-focal-model.json').read_text())

    def test_arithmetic_replay_not_nodal_regeneration(self):
        result = c.replay(self.receipt)
        self.assertTrue(result['matched_model_I'] > arb(1)/4)
        self.assertTrue(result['matched_model_I'] < arb(3)/2)
        self.assertTrue(result['energy_quadrature_error'] < arb('0.081'))
        self.assertEqual(self.receipt['scope'], c.SCOPE)
        self.assertEqual(self.receipt['python_flint'], '0.8.0')
        self.assertEqual(len(self.receipt['nodes']), 2527)

    def test_replay_rejects_bad_scope_duplicate_or_incomplete_domain(self):
        variants = []
        wrong = copy.deepcopy(self.receipt)
        wrong['scope'] = 'complete physical action'
        variants.append(wrong)
        duplicate = copy.deepcopy(self.receipt)
        duplicate['nodes'][1] = duplicate['nodes'][0]
        variants.append(duplicate)
        missing = copy.deepcopy(self.receipt)
        missing['nodes'].pop()
        variants.append(missing)
        for receipt in variants:
            with self.assertRaises(c.CertificateFailure):
                c.replay(receipt)


if __name__ == '__main__':
    unittest.main()
