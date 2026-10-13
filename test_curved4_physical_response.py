"""Diagnostics, NOT general geometric cancellation or a 4D counterexample.

Physical fibre tests consume known actual interval formulas. Scalar measures
and the quartic positive-part model are explicitly not claimed G-SS examples.
"""

import math
import unittest

import mpmath as mp
import numpy as np
import sympy as s
from scipy.integrate import quad

from curved4_physical_response import (
    clock_sublevel_integral, constants4, dilation_response, kernel4,
    kernel4_prime, stieltjes_response,
)
from dimension_kernels import action_constants, interval_coefficient, transverse_moment
from full_partner_globalization import primitive_response
from sphere_circle_focusing import interval_volume, polar_volume


class PhysicalClockTest(unittest.TestCase):
    def test_two_endpoint_measures_signed_fields_and_closing_contacts(self):
        # Actual flat 4D interval in clock tau=log(1+physical_time), on a
        # thin compact torus slab 0<t<T<L/2. Each time measure is exp(tau).
        # Fixing the spatial displacement tests CP5's time fibres, not a new
        # full torus action theorem. Spatial pair measures are unchanged.
        duration, radius = .9, .28
        top = math.log1p(duration)
        c = float(interval_coefficient(4))
        anti = lambda tau: math.expm1(tau)-math.expm1(tau)**2
        # Target field 1-2t is genuinely signed on this slab.
        for cutoff in (.12, .41, 1.1):
            for w in (.008, .12, 1.3):
                cap = c*w*w

                def source_clock(source):
                    physical_source = math.expm1(source)
                    arrival = math.log1p(physical_source+radius)
                    lower = max(arrival, source+cutoff)
                    volume = lambda target: c*((math.expm1(target)
                                              - physical_source)**2-radius**2)**2
                    target = clock_sublevel_integral(volume, lower, top, cap, anti)
                    return math.exp(source)*(1+.3*physical_source)*target

                pushed = quad(source_clock, 0, top, epsabs=2e-11,
                              epsrel=2e-11, limit=200)[0]
                max_gap = math.sqrt(radius*radius+w)

                def physical_source_integral(source):
                    lower = max(source+radius, math.exp(cutoff)*(1+source)-1)
                    upper = min(duration, source+max_gap)
                    if lower >= upper:
                        return 0.
                    # Independent original target integration with physical
                    # measure dt, not the clock antiderivative used above.
                    return (1+.3*source)*quad(lambda target: 1-2*target,
                                             lower, upper, epsabs=1e-13)[0]

                direct = quad(physical_source_integral, 0, duration,
                              epsabs=2e-11, epsrel=2e-11, limit=200)[0]
                self.assertAlmostEqual(pushed, direct, delta=2e-9)
                if cutoff == .12 and w == 1.3:
                    wrong = quad(lambda source: source_clock(source)/math.exp(source),
                                 0, top, epsabs=2e-11, limit=200)[0]
                    self.assertGreater(abs(wrong-pushed), 1e-4)

    def test_signed_antiderivative_is_not_positive_part(self):
        volume = lambda t: t*t
        anti = lambda t: -3*t
        self.assertAlmostEqual(clock_sublevel_integral(volume, 1, 3, 4, anti), -3)
        self.assertEqual(clock_sublevel_integral(volume, 3, 3, 100, anti), 0)
        self.assertEqual(clock_sublevel_integral(volume, 4, 3, 100, anti), 0)
        self.assertEqual(clock_sublevel_integral(volume, 1, 3, 1, anti), 0)
        self.assertAlmostEqual(clock_sublevel_integral(volume, 1, 3, 20, anti), -6)

    def test_short_long_and_shell_restoration_at_moving_arrival(self):
        c = float(interval_coefficient(4))
        anti = lambda t: t-.4*t*t
        for source, radius in ((.0, .2), (.31, .18), (.73, .09)):
            arrival, upper = source+radius, .95
            volume = lambda t: c*((t-source)**2-radius**2)**2
            for cap in (.00001, .002, .3):
                def piece(lo, hi):
                    return clock_sublevel_integral(volume, lo, hi, cap, anti)
                full = piece(arrival, upper)
                longs = []
                for cutoff in (.1, .36, .85):
                    boundary = min(upper, max(arrival, source+cutoff))
                    short, long = piece(arrival, boundary), piece(boundary, upper)
                    self.assertAlmostEqual(short+long, full, delta=2e-13)
                    longs.append((boundary, long))
                for (lo, left), (hi, right) in zip(longs, longs[1:]):
                    self.assertAlmostEqual(left-right, piece(lo, hi), delta=2e-13)

    def test_actual_focusing_volume_inverse_through_secondary_transition(self):
        # Accepted physical union formula, not a sum of meridian diamonds.
        # Both sides of u=2*pi-theta, plus a nonzero circle partner, are kept.
        theta, b = np.pi-.10, .43
        arrival = math.hypot(theta, b)
        upper = 3.65
        anti = lambda t: t+.17*t*t
        volume = lambda t: interval_volume(math.sqrt(t*t-b*b), theta, order=64)
        for u in (np.pi-.04, np.pi+.16):
            target = math.hypot(u, b)
            cap = polar_volume(target, theta, b, order=96, circle_order=40)
            pushed = clock_sublevel_integral(volume, arrival+1e-5, upper, cap, anti)
            expected = anti(target)-anti(arrival+1e-5)
            self.assertAlmostEqual(pushed, expected, delta=3e-5)
            wrong = clock_sublevel_integral(
                lambda t: volume(t)/2, arrival+1e-5, upper, cap, anti)
            self.assertGreater(abs(wrong-expected), .015)

    def test_input_guards(self):
        for args in ((0, 1, -1), (0, math.inf, 1), (math.nan, 1, 1)):
            with self.assertRaises(ValueError):
                clock_sublevel_integral(lambda t: t, *args, lambda t: t)


class SignedResponseTest(unittest.TestCase):
    def test_exact_normalization_and_log_moment(self):
        c = interval_coefficient(4)
        a, beta = action_constants(4)
        self.assertEqual(s.simplify(a-4/s.sqrt(6)), 0)
        self.assertEqual(s.simplify(a-beta), 0)
        j = s.Symbol("j", real=True)
        moment = -j*(j-1)*(j-2)*s.gamma((j+1)/2)/12
        self.assertEqual(s.simplify(transverse_moment(4, j)-moment), 0)
        self.assertEqual(s.simplify(-s.Rational(3, 2)*s.diff(moment, j).subs(j, 2)
                                   - s.sqrt(s.pi)/8), 0)
        self.assertEqual(s.simplify(beta*c**(-s.Rational(3, 2))*s.sqrt(s.pi)/4
                                   - 48/s.pi), 0)
        with mp.workdps(55):
            self.assertLess(abs(dilation_response(lambda z: mp.mpf(1))), mp.mpf("1e-48"))
            self.assertLess(abs(dilation_response(mp.log)-48/mp.pi), mp.mpf("1e-48"))
            self.assertLess(abs(mp.quad(lambda z: z**4*kernel4_prime(z*z)*mp.log(z),
                                       [0, 1, mp.inf])-mp.sqrt(mp.pi)/8), mp.mpf("1e-50"))

    def test_atomic_stieltjes_and_dilation_identity_without_jet(self):
        with mp.workdps(65):
            c, beta = constants4()
            atoms = [(mp.mpf(".13"), mp.mpf(".7")),
                     (mp.mpf(".39"), mp.mpf("-.2")),
                     (mp.mpf(".81"), mp.mpf(".9"))]
            primitive = lambda w: sum(m for a, m in atoms if a <= w)
            for rho in (mp.mpf(3), mp.mpf(41)):
                h = 1/mp.sqrt(c*rho)
                breaks = [a/h for a, _ in atoms]
                direct = -beta*rho**mp.mpf("1.5")*sum(
                    mass*kernel4(c*rho*a*a) for a, mass in atoms)
                pushed = stieltjes_response(primitive, rho, breaks)
                self.assertLess(abs(pushed-direct), mp.mpf("1e-53"))
                for b1, b2, b3 in ((0, 0, 0), (2, -3, 4)):
                    F = lambda w: (primitive(w)-b1*w-b2*w*w)/w**3-b3
                    dilation = dilation_response(lambda z: F(h*z)-F(h), breaks)
                    self.assertLess(abs(dilation-direct), mp.mpf("1e-52"))
                # Incorrect zero continuation loses the cumulative tail.
                wrong = stieltjes_response(
                    lambda w: primitive(w) if w <= atoms[-1][0] else 0,
                    rho, breaks)
                self.assertGreater(abs(wrong-direct), mp.mpf(".001"))

    def test_nonjet_slow_dilation_control_really_differs_from_cubic_jet(self):
        # Positive finite scalar measure, NOT a geometric primitive.
        with mp.workdps(55):
            w0 = mp.mpf(".25")
            responses, scaled_errors = [], []
            for ell in (8, 32, 128):
                h = w0*mp.exp(-ell)
                def F(w):
                    return (mp.log1p(mp.log(w0/w)) if w <= w0 else
                            (w0-w)/w**3)
                response = dilation_response(lambda z: F(h*z)-F(h))
                responses.append(abs(response))
                self.assertGreater(F(h), 2)  # quotient is unbounded as h -> 0
                self.assertLess(response, 0)
                scaled_errors.append(abs(response*(ell+1)/(48/mp.pi)+1))
            self.assertTrue(all(x > y for x, y in zip(responses, responses[1:])))
            self.assertTrue(all(x > y for x, y in zip(scaled_errors, scaled_errors[1:])))
            # Finite diagnostics only; no asserted asymptotic error rate.
            self.assertLess(scaled_errors[-1], mp.mpf(".02"))
            self.assertLess(responses[-1], mp.mpf(".13"))

    def test_capped_positive_log_control_has_nonzero_response(self):
        # Another positive O(w) finite primitive, but not a G-SS instance.
        with mp.workdps(60):
            c, _ = constants4()
            w0, h = mp.mpf(".25"), mp.mpf(".004")
            def primitive(w):
                return w+w**3*mp.log(w0/w) if w <= w0 else w0
            F = lambda w: (primitive(w)-w)/w**3
            direct = stieltjes_response(primitive, 1/(c*h*h))
            signed = dilation_response(lambda z: F(h*z)-F(h))
            self.assertLess(abs(signed+48/mp.pi), mp.mpf("1e-47"))
            self.assertLess(abs(direct-signed), mp.mpf("1e-45"))
            for w in (w0/100, w0/10, w0):
                derivative = 1+w*w*(3*mp.log(w0/w)-1)
                self.assertGreaterEqual(derivative, 1-w0*w0)

    def test_fractional_mode_retains_actual_signed_power(self):
        # G7 scalar basis normalization, not a fitted geometric coefficient.
        r, rho = s.Rational(5, 2), s.Symbol("rho", positive=True)
        beta = action_constants(4)[1]
        c = interval_coefficient(4)
        expected = -s.Rational(5, 64)*beta*c**(-s.Rational(5, 4))*s.gamma(s.Rational(5, 4))
        self.assertEqual(s.simplify(primitive_response(4, r, rho)/rho**s.Rational(1, 4)
                                   - expected), 0)

    def test_precision_not_frozen_by_kernel_cache(self):
        with mp.workdps(15):
            constants4()
        with mp.workdps(70):
            c, beta = constants4()
            self.assertLess(abs(c-mp.pi/24), mp.mpf("1e-69"))
            self.assertLess(abs(beta-4/mp.sqrt(6)), mp.mpf("1e-69"))

    def test_degenerate_optical_model_is_only_a_homogeneity_check(self):
        # CP11 is a scalar positive-part integral, NOT a produced metric lens.
        with mp.workdps(50):
            coefficient = mp.beta(mp.mpf(1)/4, mp.mpf(5)/2)/2
            direct = mp.quad(lambda u: (1-u**4)**mp.mpf("1.5"), [-1, 0, 1])
            self.assertLess(abs(direct-coefficient), mp.mpf("1e-48"))
        for scale in (.16, .63, 1.7):
            E, A, B = .8, -.22, .11
            def model(e, a, b):
                roots = np.roots([1, 0, a, b, -e])
                real = sorted(r.real for r in roots if abs(r.imag) < 1e-10)
                return sum(quad(lambda u: max(0, e-u**4-a*u*u-b*u)**1.5,
                                lo, hi, epsabs=1e-12)[0]
                           for lo, hi in zip(real, real[1:]))
            self.assertAlmostEqual(model(scale*E, scale**.5*A, scale**.75*B),
                                   scale**1.75*model(E, A, B), delta=3e-11)
        # Restricted-sector power counts do not determine a matched coefficient.
        exponent = s.Rational(9, 4)/s.Rational(7, 4)
        self.assertEqual(s.Rational(3, 2)-exponent, s.Rational(3, 14))


if __name__ == "__main__":
    unittest.main()
