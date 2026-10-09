"""Finite diagnostics, plus exact rational sign arithmetic, for #151's O3."""

from fractions import Fraction
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.optimize import brentq

from dimension_kernels import Z, action_constants, interval_coefficient, kernel_polynomial
from general_metric_gate import gauss_rule
from seven_dimensional_focusing import (
    ANTIPODAL_COEFFICIENT as D, OPENING_COEFFICIENT, PAIR_FACTOR, SPATIAL_VOLUME,
    boosted_flat_section, cut_primitive_diagnostic, flat_section, interval_volume,
    inverse_excess, matched_coefficient_quadrature, polar_volume, primitive_coefficients,
    regular_phase, regular_phase_jet, sign_certificate, time_weight, transition_profile,
)


class SevenDimensionalFocusingTests(unittest.TestCase):
    def test_exact_rational_sign_certificate_not_floating_acceptance(self):
        lower, upper = sign_certificate()
        self.assertIsInstance(lower, Fraction)
        self.assertIsInstance(upper, Fraction)
        self.assertLess(Fraction(1, 400), lower)
        self.assertLess(lower, upper)
        self.assertLess(upper, Fraction(13, 5000))
        self.assertLess(upper-lower, Fraction(1, 1_000_000))
        independent = matched_coefficient_quadrature()
        self.assertTrue(float(lower) < independent < float(upper))
        self.assertAlmostEqual(independent, .002559559862229218, delta=2e-10)

    def test_profile_from_independent_active_angle_integral(self):
        for S in (-.98, -.6, 0., .9, 1., 1.1, 3.):
            top = np.arccos(-S) if S < 1 else np.pi
            original = quad(lambda phi: max(0, S+np.cos(phi))**3, 0, top,
                            epsabs=1e-13, epsrel=1e-12)[0]/np.pi
            self.assertAlmostEqual(transition_profile(S), original, delta=2e-12)
        self.assertEqual(transition_profile(-1), 0)
        self.assertAlmostEqual(transition_profile(1), 2.5)
        # This includes the regular-side opening, not only S bounded away from -1.
        h = .001
        self.assertLess(abs(transition_profile(-1+h)/h**3.5/OPENING_COEFFICIENT-1), .00003)

    def test_flat_section_against_original_radial_and_boosted_integrals(self):
        for u, r, ss, b in ((3.3, 1.4, 1.7, 1.1), (3.6, .2, 2.7, .9)):
            radius = brentq(lambda z: u-np.hypot(r, z)-np.hypot(ss, z), 0, u)
            original = 2*np.pi**2*quad(
                lambda z: z**3*(u-np.hypot(r, z)-np.hypot(ss, z)), 0, radius,
                epsabs=1e-12, epsrel=1e-12)[0]
            actual = flat_section(u, r, ss, order=48)
            self.assertAlmostEqual(actual, original, places=11)
            boosted = boosted_flat_section(np.hypot(u, b), b, r, ss, order=56)
            self.assertAlmostEqual(boosted, original, delta=2e-8)

    def test_actual_intervals_on_both_sides_of_secondary_transition(self):
        a = .12
        for S in (-.6, 0., .9, 1., 1.1, 2.):
            u, theta = np.pi+a*S, np.pi-a
            actual = interval_volume(u, theta, order=56, flat_order=32)
            refined = interval_volume(u, theta, order=80, flat_order=40)
            independent = polar_volume(u, theta, order=80, flat_order=40)
            self.assertGreater(actual, 0)
            self.assertLess(abs(actual/refined-1), 3e-7)
            self.assertLess(abs(independent/refined-1), 2e-6)
            # Removing one orientation is not allowed even past the transition.
            self.assertGreater(abs((actual/2)/independent-1), .49)

    def test_actual_antipodal_and_transverse_cubic_scaling(self):
        independent_D = 4*np.pi/3*quad(
            lambda r: np.sin(r)*r*r*(np.pi-r)**2, 0, np.pi, epsabs=1e-12)[0]
        self.assertAlmostEqual(D, independent_D, places=11)
        for S in (-.6, 0., 1., 1.4):
            errors = []
            for a in (.1, .025, .00625):
                actual = interval_volume(np.pi+a*S, np.pi-a, order=72, flat_order=40)
                errors.append(abs(actual/(D*a**3*transition_profile(S))-1))
            self.assertTrue(errors[2] < errors[1] < errors[0])
            self.assertLess(errors[-1], .006)
        errors = [abs(interval_volume(np.pi+e, np.pi, order=160, flat_order=48)/e**3/D-1)
                  for e in (.02, .005, .00125)]
        self.assertTrue(errors[2] < errors[1] < errors[0])
        self.assertLess(errors[-1], .002)

    def test_fixed_diamond_regular_side_and_flat_origin_normalization(self):
        for a in (.3, .1, .03):
            theta, e = np.pi-a, a/40
            actual = interval_volume(theta+e, theta, order=72, flat_order=32)/e**3.5
            fixed_domain = regular_phase(theta, e, order=36)
            self.assertLess(abs(actual/fixed_domain-1), 2e-6)
        errors = [abs(np.sqrt(a)*regular_phase(np.pi-a, 0, order=40)
                      /(D*OPENING_COEFFICIENT)-1) for a in (.012, .003, .00075)]
        self.assertTrue(errors[2] < errors[1] < errors[0])
        self.assertLess(errors[-1], .001)
        theta, e = .015, .01
        actual = interval_volume(theta+e, theta, order=72, flat_order=32)
        minkowski = float(interval_coefficient(7))*((theta+e)**2-theta**2)**3.5
        self.assertLess(abs(actual/minkowski-1), .0001)
        with self.assertRaises(ValueError):
            regular_phase(3., 2*(np.pi-3.)+1e-12)

    def test_complete_time_contacts_and_temporal_masks(self):
        delta = 2.9
        for u in (.02, .8, 2.8, delta, np.pi, 3.8):
            top = np.sqrt(16-u*u)
            original = 2*np.pi**2*quad(
                lambda b: b**3*(4-np.hypot(u, b))*u/np.hypot(u, b), 0, top,
                epsabs=1e-11)[0]
            self.assertAlmostEqual(time_weight(u), original, delta=2e-10)
            lo = np.sqrt(delta*delta-u*u) if u < delta else 0
            long = 2*np.pi**2*quad(
                lambda b: b**3*(4-np.hypot(u, b))*u/np.hypot(u, b), lo, top)[0]
            self.assertAlmostEqual(time_weight(u, delta), long, delta=2e-10)
            self.assertAlmostEqual(time_weight(u, delta)+time_weight(u, delta, short=True),
                                   original, delta=2e-10)
        self.assertEqual(time_weight(delta, delta, short=True), 0)
        self.assertGreater(time_weight(np.pi), 0)

    def test_full_flat_partner_reduction_at_finite_density(self):
        theta, rho = 2.9, .3
        nodes, weights = gauss_rule(28)
        kernel = s.lambdify(Z, kernel_polynomial(7)*s.exp(-Z), "numpy")
        original = 0.
        for t, wt in zip(nodes, weights):
            tau = theta+(4-theta)*t
            top = np.sqrt(tau*tau-theta*theta)
            for z, wz in zip(nodes, weights):
                b = top*z
                u = np.sqrt(tau*tau-b*b)
                original += ((4-theta)*wt*2*np.pi**2*top**4*wz*z**3*(4-tau)
                             * kernel(rho*interval_volume(u, theta, order=32, flat_order=20)))
        reduced = quad(lambda u: time_weight(u)*kernel(
            rho*interval_volume(u, theta, order=48, flat_order=28)), theta, 4,
            points=[2*np.pi-theta], epsabs=2e-7)[0]
        self.assertAlmostEqual(original, reduced, delta=2e-6)

    def test_signed_moment_physical_point_and_short_contact_coefficient(self):
        kernel = s.Poly(kernel_polynomial(7), Z)
        moment = sum(coefficient*s.factorial(power[0]) for power, coefficient in kernel.terms())
        self.assertEqual(moment, -s.Rational(5, 128))
        a, beta = action_constants(7)
        self.assertEqual(s.simplify(a-8*beta), 0)
        c = interval_coefficient(7)
        self.assertEqual(c, s.pi**3/2688)
        # Divide primitive coefficients by VolM to check the complete physical point.
        point_primitive = -2*s.pi*(4*s.pi**2/3)/(35*c)
        self.assertEqual(point_primitive, -s.Rational(1024, 5))
        self.assertEqual(point_primitive*moment, 8)
        self.assertEqual(s.simplify(a-beta*point_primitive*moment), 0)
        # Negative controls: omitting the point or half the endpoint measure
        # leaves a leading local term, not the claimed pure focusing coefficient.
        omitted_point = s.simplify(-beta*point_primitive*moment)
        half_pair = s.simplify(a-beta*point_primitive*moment/2)
        self.assertNotEqual(omitted_point, 0)
        self.assertNotEqual(half_pair, 0)
        self.assertEqual(s.simplify(omitted_point/a), -1)
        self.assertEqual(s.simplify(half_pair/a), s.Rational(1, 2))
        u, tau, delta, T = s.symbols("u tau delta T", positive=True)
        full = s.expand(s.pi**2*u*(T-u)**3*(T+3*u)/6)
        short = s.expand(2*s.pi**2*u*s.integrate((T-tau)*(tau*tau-u*u), (tau, u, delta)))
        self.assertEqual(full.coeff(u, 4), 4*s.pi**2*T/3)
        self.assertEqual(short.coeff(u, 4), full.coeff(u, 4))
        self.assertEqual(set(s.Poly(full-short, u).monoms()), {(1,), (3,)})
        lower, _ = sign_certificate()
        cut = PAIR_FACTOR*time_weight(np.pi)/(3*D)*float(lower)
        self.assertGreater(float(beta)*5/128*cut, 0)
        self.assertGreater(SPATIAL_VOLUME, 0)

    def test_matching_identity_restores_the_entire_opening_wedge(self):
        # O11 with D scaled to one: two genuinely different integration orders.
        # This is not an action asymptotic or a fit of the finite-part constant.
        def root(t):
            value = 1/t**3
            upper = max(2., value**(1/3)+1)
            return brentq(lambda S: transition_profile(S)-value, -1, upper, xtol=1e-13)
        for m in (.5, 2., 6.):
            contact = 2.5**(-1/3)
            direct = quad(lambda t: t*t*(1+root(t)), 0, m, epsabs=1e-11,
                          epsrel=1e-11, points=[contact] if contact < m else [])[0]
            split = root(m)
            tail = (np.log1p(1.5/split**2)/3 if split >= 1 else
                    quad(lambda S: 1/transition_profile(S), split, 1,
                         epsabs=1e-11, epsrel=1e-11)[0]+np.log(2.5)/3)
            restored = (m**3*(split+1)+tail)/3
            self.assertAlmostEqual(direct, restored, delta=2e-9)
            self.assertGreater(abs(restored-tail/3), .01)

    def test_actual_derivative_jet_and_inverse_without_fitting(self):
        for a in (.3, .1, .03):
            theta = np.pi-a
            jet = regular_phase_jet(theta, order=28)
            self.assertAlmostEqual(jet[0], regular_phase(theta, 0, order=28), places=12)
            errors = []
            for e in (a/30, a/60):
                value = regular_phase(theta, e, order=28)
                errors.append(abs(value-jet@[1, e, e*e/2]))
            self.assertGreater(errors[0]/errors[1], 7.7)
            self.assertLess(errors[0]/errors[1], 8.5)
            # The f jet retains G, G' and G'', not a frozen endpoint weight.
            c = primitive_coefficients(a, order=28)
            residuals = []
            for e in (a/30, a/60):
                v = e**3.5*regular_phase(theta, e, order=28)
                E = inverse_excess(a, v, e0=.2, order=28)
                self.assertAlmostEqual(E, e, delta=3e-14)
                f = quad(lambda z: time_weight(theta+z), 0, E,
                         epsabs=1e-13, epsrel=1e-13)[0]
                residuals.append(abs(f-c@(v**(2/7))**np.arange(1, 4)))
            self.assertGreater(residuals[0]/residuals[1], 14.)
            self.assertLess(residuals[0]/residuals[1], 18.)

    def test_actual_subtracted_cut_primitive_fixed_neighborhoods(self):
        # This is O9's ACTUAL primitive, unlike the limiting-model O11 test.
        # a0/e0 remain fixed as v changes. No tail is replaced by a profile.
        target = matched_coefficient_quadrature()/(3*D)
        finest = None
        for a0, e0 in ((.06, .10), (.12, .16), (.18, .22)):
            errors = []
            for lam in (.004, .001, .00025):
                v = lam**3
                result = cut_primitive_diagnostic(v, a0, e0, order=12,
                                                 diamond_order=24, volume_order=48)
                residual, panels = result['scaled_residual'], result['panels']
                errors.append(abs(residual-target))
                reconstructed = (result['primitive']-result['coefficients']
                                 @ (v**(2/7))**np.arange(1, 4))/(v*time_weight(np.pi))
                self.assertAlmostEqual(residual, reconstructed, delta=5e-9)
                self.assertEqual(panels[0][0], 0)
                self.assertAlmostEqual(panels[-1][1], a0/lam, places=9)
                self.assertTrue(all(left[1] == right[0]
                                    for left, right in zip(panels, panels[1:])))
                self.assertGreater(panels[0][2], 6e-5)  # Unbounded-meridian side.
                self.assertLess(panels[-1][2], -1e-6)  # Not a negligible tail here.
            self.assertTrue(errors[2] < errors[1] < errors[0])
            self.assertLess(errors[-1], 6e-6)  # Finite regression, not a sign proof.
            # Removing either tail fails this broad finite comparison.
            without_meridians = residual-panels[0][2]
            without_opening = residual-sum(value for lo, _, value in panels if lo >= 4)
            self.assertGreater(abs(without_meridians-target), 3e-5)
            self.assertGreater(abs(without_opening-target), 9e-6)
            if a0 == .12:
                finest = result
        fine = cut_primitive_diagnostic(.00025**3, .12, .16, order=16,
                                        diamond_order=32, volume_order=64)
        self.assertAlmostEqual(fine['scaled_residual'], finest['scaled_residual'], delta=2e-8)
        # Omitting an INTERVAL sphere sheet means W -> W/2, hence N(v) -> N(2v),
        # with the derivative-derived coefficients scaled by 2^(2j/7) as well.
        half_sheet = cut_primitive_diagnostic(2*.00025**3, .12, .16, order=12,
                                              diamond_order=24, volume_order=48)
        self.assertGreater(abs(2*half_sheet['scaled_residual']-target), 2e-5)

    def test_exact_local_short_coefficients_from_diamond_moments(self):
        # Independent finite algebra from the metric ratio, not fitted volumes
        # and not an import of PR #158's theorem (comparison pin stays in the note).
        t, r, ss, theta = s.symbols('t r ss theta', real=True)
        c7 = interval_coefficient(7)
        ball6 = s.pi**3/6
        moment_a = s.integrate(2*t*t*ball6*(s.Rational(1, 2)-t)**6,
                               (t, 0, s.Rational(1, 2)))/c7
        moment_b = s.integrate(2*ball6*(s.Rational(1, 2)-t)**8/8,
                               (t, 0, s.Rational(1, 2)))/c7
        self.assertEqual(moment_a, s.Rational(1, 144))
        self.assertEqual(moment_b, s.Rational(7, 288))
        # Expand the FOUR denominator sincs and the TWO numerator sincs of O7.
        arguments = ((r+ss+theta)/2, (r+ss-theta)/2,
                     (theta+r-ss)/2, (theta-r+ss)/2)
        q2 = s.expand(-(r*r+ss*ss)/6+sum(arg**2 for arg in arguments)/12)
        self.assertEqual(q2, (theta**2-r*r-ss*ss)/12)
        X, Y, w = s.symbols('X Y w')
        rsum = Y/2+2*Y*moment_a+2*X*moment_b+2*(X-Y)*moment_b
        b2 = s.expand((Y-rsum)/12)
        self.assertEqual(b2, -7*X/864+77*Y/1728)
        yjet = X-w+s.Rational(2, 7)*w*b2.subs(Y, X-w)
        density = s.Poly(s.expand(-(1-yjet/6)*s.diff(yjet, w)/2), X, w)
        density = sum(coef*X**i*w**j for (i, j), coef in density.terms() if i+j <= 1)
        self.assertEqual(density, s.Rational(1, 2)-17*X/192+83*w/864)
        xmin_correction = -s.Rational(2, 7)*b2.coeff(X)
        self.assertEqual(xmin_correction, s.Rational(1, 432))
        fractional = s.simplify(xmin_correction/4+density.coeff(X)/7+density.coeff(w)/5)
        self.assertEqual(fractional, s.Rational(1, 140))
        self.assertNotEqual(s.simplify(density.coeff(X)/7+density.coeff(w)/5), fractional)
        # Integrate the ACTUAL polynomial K7 against this fractional density mode.
        polynomial = s.Poly(kernel_polynomial(7), Z)
        critical = s.simplify(sum(coef*s.rf(s.Rational(9, 7), power[0])
                                 for power, coef in polynomial.terms())
                              *s.Rational(2, 7)*s.gamma(s.Rational(9, 7)))
        self.assertEqual(s.simplify(critical-5*s.gamma(s.Rational(9, 7))/64), 0)
        _, beta = action_constants(7)
        finite_per_volume = s.simplify(beta*(2*s.pi)*(4*s.pi**2/3)*fractional
                                      *c7**s.Rational(-9, 7)*critical)
        self.assertEqual(finite_per_volume, 1)
        # Existing exact short-weight test checks that g4 is cutoff-independent.

    def test_primary_layer_formula_and_independent_curvature(self):
        # Glaser (15) rather than the implementation's Euler recurrence.
        layers = [s.simplify(sum((-1)**k*s.binomial(i-1, k)
                  *s.gamma(s.Rational(7, 2)*k+5)/(24*s.gamma(s.Rational(7, 2)*k+1))
                  for k in range(i))) for i in range(1, 6)]
        self.assertEqual(layers, [1, -s.Rational(6307, 128), s.Rational(14749, 64),
                                 -s.Rational(10633, 32), s.Rational(2401, 16)])
        source_polynomial = sum(layers[k]*Z**k/s.factorial(k) for k in range(5))
        self.assertEqual(s.expand(source_polynomial-kernel_polynomial(7)), 0)
        coords = s.symbols('t r phi b1 b2 b3 b4', real=True)
        r = coords[1]
        metric = s.diag(1, -1, -s.sin(r)**2, -1, -1, -1, -1)
        inverse = metric.inv()
        self.assertEqual(s.simplify(metric.det()), s.sin(r)**2)
        gamma = [[[s.simplify(sum(inverse[a, e]*(s.diff(metric[e, c], coords[b])
                     +s.diff(metric[e, b], coords[c])-s.diff(metric[b, c], coords[e]))/2
                     for e in range(7))) for c in range(7)] for b in range(7)] for a in range(7)]
        ricci = s.Matrix(7, 7, lambda b, d: s.simplify(sum(
            s.diff(gamma[a][a][b], coords[d])-s.diff(gamma[a][d][b], coords[a])
            +sum(gamma[a][d][e]*gamma[e][a][b]-gamma[a][a][e]*gamma[e][d][b]
                 for e in range(7)) for a in range(7))))
        difference = ricci-s.diag(0, -1, -s.sin(r)**2, 0, 0, 0, 0)
        self.assertTrue(all(s.trigsimp(s.expand_trig(value)) == 0 for value in difference))
        self.assertEqual(s.simplify(s.trace(inverse*ricci)), 2)

    def test_no_invalid_geometry_fallback(self):
        for u in (-.1, 4.1, np.nan):
            with self.assertRaises(ValueError):
                time_weight(u)
        with self.assertRaises(ValueError):
            time_weight(2., short=True)
        with self.assertRaises(ValueError):
            time_weight(2., cutoff=4.)
        with self.assertRaises(ValueError):
            flat_section(3., -1., 2.)
        with self.assertRaises(ValueError):
            interval_volume(2., 3.)
        self.assertEqual(interval_volume(3., 3.), 0)
        for args in ((0, .1, .2), (-1, .1, .2), (.01, 0, .2), (.01, .1, 1)):
            with self.assertRaises(ValueError):
                cut_primitive_diagnostic(*args)
        with self.assertRaises(ValueError):
            primitive_coefficients(0)
        with self.assertRaises(ValueError):
            regular_phase_jet(np.pi)
        self.assertEqual(inverse_excess(.1, 0), 0)
        self.assertEqual(inverse_excess(.1, 1e6, e0=.2), .2)
        with self.assertRaises(ValueError):
            cut_primitive_diagnostic(1e6, .1, .2, order=2, diamond_order=8, volume_order=16)


if __name__ == "__main__":
    unittest.main()
