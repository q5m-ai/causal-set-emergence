"""Formula/geometry regressions for #83; not machine proofs of density limits."""

import math
import unittest

from mpmath import mp
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
import sympy as s

import calculations
import null_mixed as nm


def direct_source_action(cap, rho, order=64):
    """Independent time/radius integration, with no coarea primitive or slices.

    Integrates (NM3) on r<R(mu), r<w<H(r*mu), t=-w. Used only at moderate
    densities where refinement resolves the layer; not an asymptotic solver.
    """
    nodes, weights = leggauss(order)
    unit, unit_weights = (nodes + 1) / 2, weights / 2
    total = 0.0
    for mu, angular_weight in zip(nodes, weights):
        radius = cap.joint_radius(mu)
        r = radius * unit[:, None]
        height = cap.T + cap.epsilon * np.sin(r * mu)
        w = r + (height - r) * unit[None, :]
        jacobian = radius * (height - r) * r**2
        values = jacobian * np.exp(-nm.INTERVAL_CONSTANT * rho * (w**2 - r**2)**2)
        total += angular_weight * np.sum(values * unit_weights[:, None]
                                         * unit_weights[None, :])
    return 2 * math.pi * nm.ACTION_CONSTANT * math.sqrt(rho) * total


class NullMixedTests(unittest.TestCase):
    def test_signed_interval_series_coefficient(self):
        n = s.Symbol("n", integer=True, nonnegative=True)
        q = 1 + 9 * n + 8 * n * (n - 1) + s.Rational(4, 3) * n * (n - 1) * (n - 2)
        self.assertEqual(s.factor(q), (n + 1) * (2 * n + 1) * (2 * n + 3) / 3)
        # Multiplication by the interval moment leaves c/(n+1), producing
        # (1-exp(-c*rho*D^4))/rho after summing the signed series.
        moment = s.pi / ((2 * n + 1) * (2 * n + 2) * (2 * n + 3) * (4 * n + 4))
        self.assertEqual(s.simplify(q * moment - s.pi / (24 * (n + 1))), 0)
        z = s.Symbol("z")
        kernel = (1 - 9 * z + 8 * z**2 - s.Rational(4, 3) * z**3) * s.exp(-z)
        coefficients = s.series(kernel, z, 0, 7).removeO()
        for j in range(7):
            self.assertEqual(coefficients.coeff(z, j), (-1)**j * q.subs(n, j) / s.factorial(j))
        self.assertLess(float(calculations.kernel(0.2)), 0)

    def test_actual_signed_partner_split_retains_nonlocal_term(self):
        rho, duration, cutoff = 100.0, 1.0, 0.35

        def spatial(t, absolute=False):
            def integrand(r):
                z = nm.INTERVAL_CONSTANT * rho * (t**2 - r**2)**2
                kernel = (1 - 9 * z + 8 * z**2 - 4 * z**3 / 3) * math.exp(-z)
                return 4 * math.pi * r**2 * (abs(kernel) if absolute else kernel)
            return quad(integrand, 0, min(t, duration - t), epsabs=1e-11)[0]

        short = quad(spatial, 0, cutoff, epsabs=1e-10)[0]
        long = quad(spatial, cutoff, duration, points=[duration / 2], epsabs=1e-10)[0]
        expected = math.exp(-nm.INTERVAL_CONSTANT * rho * duration**4)
        self.assertAlmostEqual(1 - rho * (short + long), expected, delta=1e-9)
        self.assertGreater(abs(rho * long), 0.01)  # no permission to omit it
        absolute = quad(lambda t: spatial(t, True), 0, duration,
                        points=[duration / 2], epsabs=1e-8, limit=150)[0]
        self.assertGreater(absolute, abs(short + long))
        self.assertGreater(abs(1 - rho * absolute - expected), 0.1)

    def test_gaussian_mass_and_radial_primitive(self):
        rho, sigma = s.symbols("rho sigma", positive=True)
        mass = 4 / s.sqrt(6) * s.sqrt(rho) * s.integrate(
            s.exp(-s.pi * rho * sigma**2 / 24), (sigma, 0, s.oo))
        self.assertEqual(s.simplify(mass), 4)
        r = s.Symbol("r", positive=True)
        primitive = (r * s.sqrt(r**2 + sigma) - sigma * s.asinh(r / s.sqrt(sigma))) / 4
        self.assertEqual(s.simplify(s.diff(primitive, r) - r**2 / (2 * s.sqrt(r**2 + sigma))), 0)
        for radius, sig in [(0.7, 0.01), (1, 0.3), (1e-5, 2), (0, 0.1), (1, 0)]:
            if sig:
                expected = quad(lambda x: x**2 / (2 * math.sqrt(x**2 + sig)), 0, radius,
                                epsabs=1e-25)[0]
            else:
                expected = radius**2 / 4
            self.assertAlmostEqual(nm.coarea_primitive(radius, sig), expected,
                                   delta=max(1e-27, abs(expected) * 2e-13))

    def test_round_mixed_weight_volume_and_new_target(self):
        for T in (0.7, 1.0, 1.3):
            cap = nm.SineMixedCap(T=T, epsilon=0)
            self.assertAlmostEqual(cap.joint_area(), 4 * math.pi * T**2, places=11)
            self.assertAlmostEqual(cap.volume(), math.pi * T**4 / 3, places=11)
            volume = quad(lambda sig: nm.round_weight(sig, T), 0, T**2, epsabs=1e-10)[0]
            self.assertAlmostEqual(volume, cap.volume(), places=9)
            for sig in (0, T**2 / 100, T**2 / 2, T**2, 2 * T**2):
                self.assertAlmostEqual(cap.weight(sig, 16), nm.round_weight(sig, T), places=10)
            # This mixed cap is not a diamond with the same time extent T.
            self.assertNotAlmostEqual(cap.joint_area(), float(calculations.null_cap_area(T, T)))

    def test_sine_slices_include_annuli_above_origin_duration(self):
        cap = nm.SineMixedCap()
        self.assertGreater(cap.joint_radius(1), cap.joint_radius(-1))
        for mu in (-1, -0.2, 0, 0.5, 1):
            R = cap.joint_radius(mu)
            self.assertAlmostEqual(R, cap.height(R, mu), places=11)
            self.assertLessEqual(cap.T / (1 + cap.epsilon), R)
            self.assertLessEqual(R, cap.T / (1 - cap.epsilon))
        self.assertIsNone(cap.radial_slice(1.01, -1))
        low, high = cap.radial_slice(1.01, 1)
        self.assertGreater(low, 0)
        self.assertGreater(high, low)
        self.assertAlmostEqual(cap.squared_duration(low, 1), 1.01, places=11)
        self.assertAlmostEqual(cap.squared_duration(high, 1), 1.01, places=11)
        self.assertGreater(cap.squared_duration((low + high) / 2, 1), 1.01)
        self.assertGreater(cap.weight(1.01), 0)
        self.assertLess(-cap.epsilon * math.sin(0.5), 0)  # nonzero lower-face second jet

    def test_sine_weight_volume_against_ordinary_coordinates(self):
        cap = nm.SineMixedCap()
        self.assertAlmostEqual(4 * cap.weight(0), cap.joint_area(), places=12)
        volume = quad(lambda sig: cap.weight(sig, 48), 0,
                      (cap.T / (1 - cap.epsilon))**2, points=[cap.T**2],
                      epsabs=3e-8, epsrel=3e-8, limit=150)[0]
        self.assertAlmostEqual(volume, cap.volume(), delta=1e-7)
        for rho in (10, 100):
            direct_low = direct_source_action(cap, rho, 24)
            direct_high = direct_source_action(cap, rho, 48)
            self.assertAlmostEqual(direct_low, direct_high, delta=2e-8)
            self.assertAlmostEqual(cap.action(rho, 48), direct_high, delta=2e-7)

    def test_explicit_moving_endpoint_bound_including_time_weights(self):
        for cap in (nm.SineMixedCap(epsilon=0), nm.SineMixedCap()):
            for sig in (1e-6, 1e-4, 0.01, 0.1, 0.25):
                W0, W = cap.weight(0), cap.weight(sig)
                self.assertGreaterEqual(W0, W)
                self.assertLessEqual(W0 - W,
                                     nm.continuity_bound(sig, cap.T, cap.epsilon))
        # Independent time-weight primitive for H=1 and phi=t, M=L=1.
        for sig in (1e-6, 0.01, 0.25):
            weighted = -2 * math.pi * (1 - sig)**1.5 / 3
            at_zero = -2 * math.pi / 3
            self.assertLessEqual(abs(weighted - at_zero), nm.continuity_bound(sig, 1, 0, 1, 1))
        cap = nm.SineMixedCap()
        for rho in (100, 1e4, 1e6):
            self.assertLessEqual(abs(cap.action(rho, 32) - cap.joint_area()),
                                 nm.action_error_bound(rho, 0.01, 1, 0.2))

    def test_generator_derivative_and_artificial_cutoff_terms(self):
        r, R, alpha, a, h = s.symbols("r R alpha a h", positive=True)
        # phi=t has cone trace -r; a spatial derivative alone would give zero.
        actual = s.integrate(2 * r * (-r), (r, 0, R))
        joint = R**2 * (-R)
        compensator = -s.integrate(r**2 * (-1), (r, 0, R))
        self.assertEqual(s.simplify(actual - joint - compensator), 0)
        self.assertNotEqual(actual, joint)
        # An affine rescaling of the marked null normal changes the parameter,
        # not the response, including its derivative term.
        transported = s.integrate(2 * alpha**2 * a * (-alpha * a), (a, 0, R / alpha))
        self.assertEqual(s.simplify(transported - actual), 0)
        scaled_derivative = s.integrate(alpha**2 * a**2 * (-alpha), (a, 0, R / alpha))
        self.assertEqual(s.simplify(scaled_derivative + compensator), 0)
        collar = s.integrate(2 * r, (r, R - h, R))
        complement = s.integrate(2 * r, (r, 0, R - h))
        self.assertEqual(s.simplify(collar + complement), R**2)
        self.assertEqual(s.limit(collar, h, 0), 0)
        self.assertEqual(s.limit(complement, h, 0), R**2)
        # Smooth partition: phi=r/R and 1-phi have nonzero compensators
        # individually, but the total derivative term cancels exactly.
        derivatives = [s.diff(r / R, r), s.diff(1 - r / R, r)]
        terms = [s.integrate(r**2 * derivative, (r, 0, R)) for derivative in derivatives]
        self.assertNotEqual(terms[0], 0)
        self.assertEqual(sum(terms), 0)

    def test_uniform_tip_bound_on_actual_finite_density_round_weight(self):
        delta = 0.2
        for rho in (1, 100, 1e6):
            scale = math.sqrt(nm.INTERVAL_CONSTANT * rho)

            def integrand(u):
                sig = u / scale
                upper = min(delta, math.sqrt(max(0, 1 - sig)))
                return 4 * math.pi * nm.coarea_primitive(upper, sig) * math.exp(-u**2)

            end = min(10, scale)
            transition = scale * (1 - delta**2)
            points = [transition] if 0 < transition < end else None
            action = 8 / math.sqrt(math.pi) * quad(integrand, 0, end, points=points)[0]
            self.assertGreater(action, 0)
            self.assertLessEqual(action, 4 * math.pi * delta**2)
        self.assertAlmostEqual(4 * (4 * math.pi * delta**2 / 4), 4 * math.pi * delta**2)

    def test_existing_null_cap_and_diamond_calibrations(self):
        T, cut = 1.3, 0.4
        transition = 2 * cut / T - 1
        area = 2 * math.pi * quad(lambda mu: min(T / 2, cut / (1 + mu))**2,
                                 -1, 1, points=[transition], epsabs=1e-11)[0]
        self.assertAlmostEqual(area, float(calculations.null_cap_area(T, cut)), places=10)
        self.assertAlmostEqual(4 * math.pi * (T / 2)**2,
                               float(calculations.null_cap_area(T, T)), places=12)
        with mp.workdps(30):
            for a in (mp.mpf('0.4'), mp.mpf('1.3')):
                for sigma in (mp.mpf('0.01'), mp.mpf('0.3')):
                    closed = calculations.null_cap_weight(sigma, mp.mpf('1.3'), a)
                    geometric = calculations.null_cap_weight_geometric(sigma, mp.mpf('1.3'), a)
                    self.assertLess(abs(closed - geometric), mp.mpf('1e-27'))
                low = calculations.null_cap_action(100, mp.mpf('1.3'), a)
                high = calculations.null_cap_action(1000000, mp.mpf('1.3'), a)
                target = calculations.null_cap_area(mp.mpf('1.3'), a)
                self.assertLess(abs(high - target), abs(low - target))

    def test_invalid_domains(self):
        for parameters in ((0, 0), (1, -0.2), (1, 1), (10, 0.2), (math.nan, 0.2)):
            with self.assertRaises(ValueError):
                nm.SineMixedCap(*parameters)
        for args in ((-1, 1, 0), (0.3, 1, 0.2), (0.1, 1, 1), (0.1, -1, 0),
                     (0.1, 1, 0, -1), (0.1, 1, 0, 1, -1)):
            with self.assertRaises(ValueError):
                nm.continuity_bound(*args)
        for rho in (0, -1, math.inf, math.nan):
            with self.assertRaises(ValueError):
                nm.SineMixedCap().action(rho)
        for sig in (-1, math.inf, math.nan):
            with self.assertRaises(ValueError):
                nm.SineMixedCap().weight(sig)
        for order in (2, 8.5, True):
            with self.assertRaises(ValueError):
                nm.SineMixedCap().joint_area(order)
        for mu in (-2, 2, math.nan):
            with self.assertRaises(ValueError):
                nm.SineMixedCap().joint_radius(mu)
        self.assertEqual(nm.continuity_bound(0, 1, 0.2), 0)


if __name__ == "__main__":
    unittest.main()
