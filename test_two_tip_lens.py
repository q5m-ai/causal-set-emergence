"""TT-A regressions: formulas and full finite-density action, not proof by samples."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT
from two_tip_null import TwoTipMixed
from two_tip_lens import LensOverlap, layer_primitive, rule, signed_primitive


class LensProducerTests(unittest.TestCase):
    def setUp(self):
        self.lens = LensOverlap()

    def test_actual_axial_overlap_and_volume(self):
        lens = self.lens
        self.assertAlmostEqual(lens.overlap(0, 0), lens.region.volumes()["lens"], places=13)
        # Independent radial integral of the actual time interval, not Phi.
        for tau, xi in ((0.1, 0.06), (0.2, -0.12), (0.49, 0.1)):
            low, high = lens.roots(tau, xi)
            def spatial(y):
                top = float(lens.region.height(y-xi))-tau
                d = lens.region.a+abs(y)
                rmax = math.sqrt(max(0, top*top-d*d))
                return quad(lambda r: 2*math.pi*r*(top-math.sqrt(d*d+r*r)),
                            0, rmax, epsabs=1e-13)[0]
            actual = sum(quad(spatial, lo, hi, epsabs=1e-12)[0]
                         for lo, hi in ((low, 0), (0, high)))
            self.assertAlmostEqual(lens.overlap(tau, xi), actual, places=12)
        # The selected source-dependent translated cutoff is genuinely asymmetric.
        self.assertGreater(abs(lens.overlap(0.2, 0.15)-lens.overlap(0.2, -0.15)), 1e-3)

    def test_flat_calibration_overlap_not_substituted_for_selected_floor(self):
        flat = LensOverlap(TwoTipMixed(b=0))
        for tau in (0, 0.1, 0.49, 0.5, 0.7):
            expected = math.pi/3*max(0, 0.5-tau)**3*(1.5-tau)
            for xi in (-0.2, 0, 0.2):
                self.assertAlmostEqual(flat.overlap(tau, xi), expected, places=13)
        self.assertGreater(abs(flat.overlap(0.1, 0.06)-self.lens.overlap(0.1, 0.06)), 1e-4)

    def test_closing_contact_cubic_derived_from_both_moving_roots(self):
        lens, xi = self.lens, 0.17
        closing = float(lens.region.height(-xi))-lens.region.a
        for height in (1e-2, 5e-3, 1e-3):
            tau = closing-height
            low, high = lens.roots(tau, xi)
            self.assertLessEqual(max(-low, high), height/(1-lens.region.b)+1e-14)
            for y in (low, high):
                self.assertAlmostEqual(float(lens.region.height(y-xi))-tau,
                                       lens.region.a+abs(y), places=13)
            # Local coefficient: Phi ~ pi*a*gap²; integrate both slopes.
            hp = lens.region.b*math.cos(-xi)
            leading = math.pi*lens.region.a/3*(1/(1-hp)+1/(1+hp))
            self.assertAlmostEqual(lens.overlap(tau, xi)/height**3, leading,
                                   delta=0.02)
        self.assertEqual(lens.overlap(closing+1e-8, xi), 0)

    def test_actual_time_cutoff_not_constant(self):
        ends = [self.lens.time_end(mu) for mu in (-1, -0.3, 0, 0.5, 1)]
        self.assertGreater(max(ends)-min(ends), 0.08)
        for mu, end in zip((-1, -0.3, 0, 0.5, 1), ends):
            self.assertAlmostEqual(end+self.lens.region.a,
                                   float(self.lens.region.height(-end*mu)), places=13)
            self.assertEqual(self.lens.overlap(end+1e-6, (end+1e-6)*mu), 0)

    def test_mellin_log_moments_and_physical_point_normalization(self):
        q = s.symbols("q", real=True)
        a = (q+1)/2
        polynomial = 1-9*a+8*a*(a+1)-s.Rational(4, 3)*a*(a+1)*(a+2)
        self.assertEqual(s.factor(polynomial+q*(q-1)*(q-2)/6), 0)
        moment = -q*(q-1)*(q-2)*s.gamma((q+1)/2)/12
        for n in (0, 1, 2):
            self.assertEqual(moment.subs(q, n), 0)
        self.assertEqual(s.simplify(s.diff(moment, q).subs(q, 1)), s.Rational(1, 12))
        self.assertEqual(s.simplify(s.diff(moment, q).subs(q, 2)), -s.sqrt(s.pi)/12)
        c, C = s.pi/24, 4/s.sqrt(6)
        self.assertEqual(s.simplify(s.pi/(24*c)), 1)
        self.assertEqual(s.simplify(C*s.pi*s.sqrt(s.pi)/(48*c**s.Rational(3, 2))), 4)

    def test_quadrant_density_keeps_analytic_and_logarithmic_terms(self):
        x, y, z = s.symbols("x y z", positive=True)
        f = (1-x)**3*(1-y)**3  # C² compact extension on the quadrant.
        density = s.expand(s.pi/2*s.integrate(s.integrate(f, (y, z/x, 1)), (x, z, 1)))
        expected_logs = s.pi/2*z*s.log(z)+9*s.pi/4*z*z*s.log(z)
        residual = s.expand(density-expected_logs)
        # Neither the volume-like constant nor the long analytic s,s² terms is zero.
        series = sum(residual.coeff(z, n)*z**n for n in (0, 1, 2))
        for n in (0, 1, 2):
            self.assertNotEqual(series.coeff(z, n), 0)
        self.assertFalse(series.has(s.log(z)))
        self.assertEqual(s.limit((residual-series)/z**2, z, 0, dir="+"), 0)

    def test_hessian_target_and_nonzero_opposite_crease_flux(self):
        lens = self.lens
        coefficient = lens.coefficient()
        target = lens.region.joint_areas()["lens"]
        self.assertAlmostEqual(coefficient["hessian"], target, places=11)
        self.assertNotEqual(coefficient["left_crease_flux"], 0)
        self.assertEqual(coefficient["left_crease_flux"]+coefficient["right_crease_flux"], 0)
        h = 1e-3
        f00 = lens.overlap(0, 0)
        ftt = (lens.overlap(h, 0)-2*f00+lens.overlap(-h, 0))/(h*h)
        fzz = (lens.overlap(0, h)-2*f00+lens.overlap(0, -h))/(h*h)
        self.assertAlmostEqual(ftt-fzz, target, delta=3e-6)
        # Removing the floor Hessian is NOT the target identification.
        low, high = lens.roots()
        wrong = quad(lambda z: 2*math.pi*float(lens.region.height(z))
                     *(1-(lens.region.b*math.cos(z))**2), low, high)[0]
        self.assertGreater(abs(wrong-target), 1e-4)

    def test_positive_layers_and_signed_radial_primitive(self):
        for rho in (0.5, 20, 1000):
            for top in (0, 0.01, 0.2, 1):
                layers = layer_primitive(rho, top)
                actual = quad(lambda x: math.exp(-INTERVAL_CONSTANT*rho*x*x)
                              *(1-9*INTERVAL_CONSTANT*rho*x*x
                                +8*(INTERVAL_CONSTANT*rho*x*x)**2
                                -4*(INTERVAL_CONSTANT*rho*x*x)**3/3), 0, top)[0]
                self.assertAlmostEqual(float(signed_primitive(rho, top)), actual, places=13)
                self.assertAlmostEqual(float(np.dot(layers, [1, -9, 16, -8])), actual, places=13)
                self.assertTrue((layers >= 0).all())

    def test_complete_finite_density_pair_integrals_and_layer_factorials(self):
        for rho in (1, 20, 100, 1000):
            low = self.lens.pair_integrals(rho, 20)
            high = self.lens.pair_integrals(rho, 32)
            np.testing.assert_allclose(low.layers, high.layers, rtol=2e-9, atol=1e-14)
            self.assertAlmostEqual(low.action, high.action, delta=2e-7)
            signed = np.dot(high.layers, [1, -9, 16, -8])
            self.assertAlmostEqual(high.signed, signed, delta=1e-17)
            self.assertAlmostEqual(high.action, ACTION_CONSTANT*math.sqrt(rho)
                                   *(high.volume-rho*signed), places=12)
            wrong = np.dot(high.layers, [1, -9, 8, -4/3])
            self.assertGreater(abs(high.signed-wrong), 1e-10)

    def test_independent_all_source_all_partner_coordinates(self):
        reference = np.array(self.lens.pair_integrals(20, 24).layers)
        low = self.lens.independent_pairs(20, 8, 12)
        high = self.lens.independent_pairs(20, 12, 16)
        np.testing.assert_allclose(low, reference, rtol=1e-6, atol=1e-14)
        np.testing.assert_allclose(high, reference, rtol=2e-10, atol=1e-17)
        # Also match #134's older CENTRAL fibre implementation; not only that fibre.
        for depth in (0.6, 0.8, 0.95):
            actual = self.lens.axial_partners(20, depth, 0, 16)
            old = self.lens.region.central_partners(20, depth, 20).layers
            np.testing.assert_allclose(actual, old, rtol=1e-10, atol=1e-17)
        asymmetric = self.lens.axial_partners(20, 0.9, 0.17, 16)
        central = self.lens.axial_partners(20, 0.9, 0, 16)
        self.assertGreater(abs(asymmetric[0]-central[0]), 1e-4)

    def test_finite_density_source_dependent_split_and_all_ordered_chart_pairs(self):
        # A finite quadrature of the actual two-endpoint integrand: separate
        # positive volume weights at BOTH endpoints, not a region-action sum.
        points = np.array([[-0.97, -0.03, 0.02, 0], [-0.85, 0.02, 0, 0],
                           [-0.70, -0.01, 0.03, 0], [-0.57, 0.01, 0, 0]])
        plus, minus = self.lens.region.cap_masks(points)
        self.assertTrue((plus & minus).all())
        weights = np.array([0.02, 0.04, 0.03, 0.01])
        # Overlapping partition, applied independently at both endpoints.
        phi = np.array([[0.8, 0.3, 0.2, 0.6], [0.2, 0.7, 0.8, 0.4]])
        for rho in (1, 20, 100):
            delta = points[None, :, :]-points[:, None, :]
            sigma = delta[:, :, 0]**2-np.sum(delta[:, :, 1:]**2, axis=2)
            causal = (delta[:, :, 0] > 0) & (sigma >= 0)
            phase = INTERVAL_CONSTANT*rho*sigma*sigma
            kernel = (1-9*phase+8*phase**2-4*phase**3/3)*np.exp(-phase)*causal
            measure = weights[:, None]*weights[None, :]
            pair = np.sum(measure*kernel)
            point = weights.sum()
            full = ACTION_CONSTANT*math.sqrt(rho)*(point-rho*pair)
            chart_pair = sum(np.sum(measure*kernel*left[:, None]*right[None, :])
                             for left in phi for right in phi)
            self.assertAlmostEqual(chart_pair, pair, places=15)
            wrong = sum(np.sum(measure*kernel*row[:, None]*row[None, :]) for row in phi)
            self.assertGreater(abs(wrong-pair), 1e-4)
            # Genuine source-dependent sharp partner cutoff, with its complement.
            cutoff = delta[:, :, 0] <= 0.10-0.2*points[:, 0, None]
            short = ACTION_CONSTANT*math.sqrt(rho)*(point-rho*np.sum(measure*kernel*cutoff))
            long = -ACTION_CONSTANT*rho**1.5*np.sum(measure*kernel*(~cutoff))
            self.assertAlmostEqual(short+long, full, places=13)
            self.assertGreater(abs(long), 1e-4)
            self.assertNotAlmostEqual(short+long+ACTION_CONSTANT*math.sqrt(rho)*point, full)

    def test_invalid_inputs(self):
        for rho in (0, -1, math.nan, math.inf):
            with self.assertRaises(ValueError):
                self.lens.pair_integrals(rho)
        for n in (True, 3, 4.5):
            with self.assertRaises(ValueError):
                rule(n)
        for top in (-1, math.nan, math.inf):
            with self.assertRaises(ValueError):
                layer_primitive(1, top)
            with self.assertRaises(ValueError):
                signed_primitive(1, top)
            with self.assertRaises(ValueError):
                self.lens.density(top)
        for mu in (-2, 2, math.nan):
            with self.assertRaises(ValueError):
                self.lens.time_end(mu)
        for depth, axial in ((0.5, 0), (0.7, 0.3), (math.nan, 0)):
            with self.assertRaises(ValueError):
                self.lens.axial_partners(1, depth, axial)


if __name__ == "__main__":
    unittest.main()
