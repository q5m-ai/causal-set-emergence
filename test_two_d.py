"""Independent algebra and numerical diagnostics, not Lean limit proofs."""

import math
import unittest
from unittest.mock import patch

import sympy as sp

from two_d import (
    action_from_density, causal_fibre_length, density, disconnected_fixture,
    fibre_length, interval_fixture, kernel, overlap, overlap_jet,
)


class TwoDAlgebraTests(unittest.TestCase):
    def test_actual_signed_moments_including_both_logs(self):
        # Gamma(n+1) and its derivative, not moments imported from 3D or 4D.
        coefficients = (sp.Integer(1), sp.Integer(-2), sp.Rational(1, 2))
        moments = []
        logs = []
        for j in (0, 1):
            moments.append(sum(c*sp.factorial(j+n) for n, c in enumerate(coefficients)))
            logs.append(sp.simplify(sum(c*sp.factorial(j+n)
                        * (sp.harmonic(j+n)-sp.EulerGamma)
                        for n, c in enumerate(coefficients))))
        self.assertEqual(moments, [0, 0])
        self.assertEqual(logs, [-sp.Rational(1, 2), sp.Rational(1, 2)])
        self.assertLess(kernel(1), 0)
        self.assertGreater(kernel(0), 0)
        self.assertGreater(kernel(4), 0)

    def test_independent_normal_identity(self):
        p, q = sp.symbols("p q", real=True)
        self.assertEqual(sp.expand((1-p*q)**2-(1-p*p)*(1-q*q)-(p-q)**2), 0)
        for model in (interval_fixture(), interval_fixture(0, .2),
                      disconnected_fixture(), disconnected_fixture(0)):
            self.assertAlmostEqual(model.target(), model.target_slopes(), places=10)

    def test_null_jacobian_and_sharp_short_responses(self):
        v, sigma, delta = sp.symbols("v sigma delta", positive=True)
        t, r = (v+sigma/v)/2, (v-sigma/v)/2
        jac = sp.det(sp.Matrix([t, r]).jacobian([sigma, v]))
        self.assertEqual(sp.simplify(jac), 1/(2*v))
        responses = [
            (1, sp.log(delta/sp.sqrt(sigma))),
            (t, (delta-sigma/delta)/2),
            (t*t+r*r, (delta*delta-sigma*sigma/(delta*delta))/4),
            (t*t-r*r, sigma*sp.log(delta/sp.sqrt(sigma))),
        ]
        for mode, answer in responses:
            actual = sp.integrate(mode/v, (v, sp.sqrt(sigma), delta))
            self.assertEqual(sp.simplify(sp.expand_log(actual-answer, force=True)), 0)

    def test_empty_gram_normalization_and_all_endpoints(self):
        self.assertEqual(sp.det(sp.zeros(0, 0)), 1)
        model = disconnected_fixture(0)
        self.assertEqual(model.endpoints, (-1.0, -.5, .5, 1.0))
        self.assertAlmostEqual(model.target(), 32, places=10)
        outer_only = sum(1/abs(model.height_derivative(x)) for x in (-1, 1))
        self.assertGreater(abs(model.target()-outer_only), 20)

    def test_nonempty_curved_critical_examples(self):
        for model in (interval_fixture(), disconnected_fixture()):
            self.assertLess(model.height_lipschitz+model.future_lipschitz, 1)
            for lo, hi in model.components:
                x = (lo+hi)/2
                self.assertGreater(model.height(x), 0)
            for e in model.endpoints:
                self.assertEqual(model.height(e), 0)
                self.assertNotEqual(model.height_derivative(e), 0)
        self.assertEqual(interval_fixture().height_derivative(0), 0)
        for x in (-math.sqrt(5/8), math.sqrt(5/8)):
            self.assertAlmostEqual(disconnected_fixture().height_derivative(x), 0)
            self.assertGreater(disconnected_fixture().height(x), 0)
        self.assertNotEqual(-math.sin(.5)/8, 0)  # actual future second derivative


class TwoDActualOverlapTests(unittest.TestCase):
    def test_full_time_fibre_keeps_all_partner_constraints(self):
        for model in (interval_fixture(), disconnected_fixture()):
            # Includes source gaps, exterior zeros, nulls, diagonal and both directions.
            for x in (-2.2, -1, -.8, -.5, 0, .5, .8, 1, 2.2):
                for r in (-1.2, -.08, 0, .08, 1.2):
                    for excess in (0, .01, .15):
                        t = abs(r)+excess
                        self.assertAlmostEqual(fibre_length(model, x, t, r),
                                               causal_fibre_length(model, x, t, r), places=12)
        with self.assertRaises(ValueError):
            causal_fibre_length(interval_fixture(), 0, .1, .2)

    def test_quadratic_planar_overlap_calibration(self):
        model = interval_fixture(0, .2)
        for t, r in ((0, 0), (.02, .01), (.1, -.04), (.3, 0)):
            # Exact integration of the actual quadratic positive part.
            expected = (1/3)*max(0, 1-4*(t-.2*r))**1.5
            self.assertAlmostEqual(overlap(model, t, r), expected, places=11)

    def test_actual_origin_jet_all_endpoints_and_both_directions(self):
        for model in (interval_fixture(), disconnected_fixture()):
            for sign in (-1, 1):
                errors = []
                for t in (.0004, .0002, .0001):
                    r = sign*.6*t
                    errors.append(abs(overlap(model, t, r)-overlap_jet(model, t, r)))
                self.assertGreater(errors[0], 0)
                self.assertLess(errors[1], .2*errors[0])
                self.assertLess(errors[2], .2*errors[1])

    def test_density_split_uses_one_fixed_cutoff_and_both_directions(self):
        model = interval_fixture()
        delta = .12
        for sigma in (.0003, .005, .02):
            self.assertAlmostEqual(density(model, sigma),
                                   density(model, sigma, delta)
                                   + density(model, sigma, delta, long=True), places=8)
        self.assertEqual(density(model, delta*delta, delta), 0)
        self.assertEqual(density(model, model.null_support_bound**2*2), 0)

    def test_actual_long_density_right_derivative(self):
        model = interval_fixture()
        cutoff = .12
        base = density(model, 0, cutoff, long=True)
        slopes = [(density(model, s, cutoff, long=True)-base)/s
                  for s in (4e-5, 2e-5, 1e-5)]
        self.assertLess(abs(slopes[2]-slopes[1]), .6*abs(slopes[1]-slopes[0]))
        self.assertLess(abs(slopes[2]-slopes[1]), .001)
        with self.assertRaises(ValueError):
            density(model, 0)  # Full density is logarithmically singular.

    def test_log_coefficient_comes_from_actual_density_not_a_fitted_target(self):
        model = interval_fixture()
        predicted = -model.target()/8
        estimates = []
        for s in (2e-5, 2e-6):
            values = [density(model, k*s)+model.volume*math.log(k*s)/2 for k in (1, 2, 3)]
            estimates.append((values[2]-2*values[1]+values[0])
                             / (s*(3*math.log(3)-4*math.log(2))))
        self.assertLess(abs(estimates[-1]-predicted), .015)
        self.assertLess(abs(estimates[-1]-predicted), abs(estimates[0]-predicted))

    def test_signed_full_action_planar_curved_and_disconnected(self):
        for model, densities, tolerance in (
            (interval_fixture(0), (4096, 16384), .04),
            (interval_fixture(0, .2), (4096, 16384), .04),
            (interval_fixture(), (4096, 16384), .04),
            (disconnected_fixture(), (262144, 1048576), .25),
        ):
            target = model.target()
            # Fail if the action evaluator ever tries to read either target API.
            with patch.object(type(model), "target", side_effect=AssertionError("target-fed action")), \
                 patch.object(type(model), "target_slopes", side_effect=AssertionError("target-fed action")):
                values = [action_from_density(model, rho, order=64) for rho in densities]
            self.assertLess(abs(values[-1]-target), tolerance)
            self.assertLess(abs(values[-1]-target), abs(values[0]-target))

    def test_quadrature_refinement_is_separate_from_density_limit(self):
        model = interval_fixture()
        low = action_from_density(model, 4096, order=64)
        high = action_from_density(model, 4096, order=128)
        self.assertLess(abs(high-low), .002)
        # Finite-density action is NOT simply defined as its endpoint target.
        self.assertGreater(abs(high-model.target()), .01)


if __name__ == "__main__":
    unittest.main()
