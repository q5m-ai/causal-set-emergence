"""Finite IU diagnostics, not certification of analytic continuation or limits."""
import math
import unittest
from fractions import Fraction

import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import (
    Z, action_constants, factor_count, kernel_polynomial, mellin_factor,
)
from intrinsic_union_response import (
    D, filter_coefficients, filter_constant, filtered_pair, filtered_power,
    focal_growth, geometric_filter, laplace_weight, physical_closing_weight,
    point_primitive, projective_profile, resolved_interval,
)
from null_singular_ends import closing_weight, matched_profile_parts
from seven_dimensional_focusing import (
    OPENING_COEFFICIENT, interval_volume, regular_phase, transition_profile,
)


def kernel(d, value):
    return s.lambdify(Z, kernel_polynomial(d)*s.exp(-Z), 'numpy')(value)


class IntrinsicUnionTests(unittest.TestCase):
    def test_actual_projective_interval_both_orientations_and_ends(self):
        for y in (.08, .4, 2/3, .85, 1.):
            r = .09
            expected = interval_volume(math.pi+r*(2*y-1), math.pi-r*(1-y),
                                       order=48, flat_order=28)
            actual = resolved_interval(r, y, order=44)
            self.assertAlmostEqual(actual/expected, 1., delta=2e-7)

    def test_normalized_regular_edge_is_actual_not_frozen(self):
        for r in (.12, .03):
            edge = math.sqrt(r)*regular_phase(math.pi-r, 0, order=32)
            actual = resolved_interval(r, 0, order=48, divided=True)
            self.assertAlmostEqual(actual/edge, 1., delta=2e-8)
            self.assertNotAlmostEqual(actual, projective_profile(0, divided=True), places=3)
            self.assertEqual(resolved_interval(r, 0), 0.)
            near = resolved_interval(r, 1e-7, order=48, divided=True)
            self.assertAlmostEqual(near/actual, 1., delta=2e-7)

    def test_radial_error_samples_not_a_uniformity_certificate(self):
        for r in (.08, .02, .005):
            for y in (0., .03, .4, .65, 2/3, .68, .93, 1.):
                actual = resolved_interval(r, y, order=44, divided=True)
                model = projective_profile(y, divided=True)
                self.assertGreater(actual, 0.)
                self.assertLess(abs(actual-model)/r, 18.)

    def test_full_tangent_profile_and_meridian_tail(self):
        for y in (.04, .4, 2/3, .9, .999):
            expected = D*(1-y)**3*transition_profile((2*y-1)/(1-y))
            self.assertAlmostEqual(projective_profile(y)/expected, 1., delta=2e-12)
        self.assertEqual(projective_profile(0), 0.)
        self.assertEqual(projective_profile(1), D)
        opening, matching, meridian = matched_profile_parts()
        self.assertAlmostEqual(meridian, math.log(2.5)/3)
        self.assertGreater(math.fsum((opening, matching, meridian)), .0025)
        self.assertLess(opening+matching, 0.)

    def test_seven_halves_term_is_not_smoothly_discarded(self):
        for h in (.08, .03, .01):
            S = 1-h
            deficit = transition_profile(S)-(S**3+1.5*S)
            self.assertGreater(deficit, 0.)
            self.assertAlmostEqual(deficit/h**3.5, OPENING_COEFFICIENT, delta=.002)

    def test_real_closing_cap_crosses_both_projective_sectors(self):
        r = .1
        for T in (math.pi-.03, math.pi, math.pi+.03, math.pi+.12):
            for y in (.2, .49, .51, 2/3, .8, 1.):
                U = math.pi+r*(2*y-1)
                actual = physical_closing_weight(U, T)
                self.assertEqual(actual > 0, U < T)
                if U < T:
                    self.assertAlmostEqual(actual, closing_weight(U, T), places=13)
        self.assertEqual(physical_closing_weight(math.pi, math.pi), 0.)

    def test_growth_is_geometric_and_opens_with_nine_halves_weight(self):
        self.assertEqual(focal_growth(math.pi-.1), 0.)
        self.assertEqual(focal_growth(math.pi), 0.)
        beta = float(action_constants(7)[1])
        I = math.fsum(matched_profile_parts())
        endpoint = 256*math.pi**2*math.sqrt(2*math.pi)/945
        expected = 5*beta/128*(2*math.pi*(4*math.pi*20**3)/(3*D))*I*endpoint
        for h in (.01, .002):
            ratio = focal_growth(math.pi+h)/h**4.5
            self.assertGreater(ratio, 0.)
            self.assertAlmostEqual(ratio/expected, 1., delta=.012)

    def test_continuation_strip_reaches_past_action_critical_order(self):
        w = s.Rational(13, 10)
        self.assertGreater(w, s.Rational(9, 7))
        self.assertLess(w, s.Rational(4, 3))
        self.assertLess(w, s.Rational(10, 7))
        self.assertEqual(s.Rational(9, 7)-w, -s.Rational(1, 70))
        self.assertGreater(3-3*w, -1)  # radial difference after leading subtraction
        self.assertGreater(4-7*w/2, -1)  # fourth angular Taylor remainder
        for j in range(1, 5):
            self.assertEqual(mellin_factor(7, s.Rational(2*j, 7)), 0)
            self.assertNotEqual(s.Rational(2*j, 7), 1)

    def test_exact_annihilator_and_all_dimensional_moments(self):
        p = s.symbols('p')
        for d in range(2, 10):
            coefficients = filter_coefficients(d)
            m = factor_count(d)
            lhs = sum(s.Rational(c.numerator, c.denominator)/(p+1)**(k+1)
                      for k, c in enumerate(coefficients))
            expected = s.prod(p-s.Rational(2*j, d) for j in range(1, m+1))/(p+1)**(m+1)
            self.assertEqual(s.cancel(lhs-expected), 0)
            C = filter_constant(d)
            ratio = s.Rational(C.numerator, C.denominator)*expected*(p+1)**(m+1)
            self.assertEqual(s.expand(ratio-mellin_factor(d, p)), 0)
            for j in range(1, m+1):
                self.assertAlmostEqual(filtered_power(d, 2*j/d), 0., places=13)
        self.assertEqual(filter_constant(7), Fraction(2401, 384))
        self.assertAlmostEqual(filtered_power(7, 1), -15/76832, places=15)

    def test_laplace_adjoint_and_logarithmic_modes(self):
        p = s.symbols('p')
        for d in (2, 3, 4, 7, 8):
            m = factor_count(d)
            value = s.exp(-Z)
            for _ in range(m+1):
                value = s.expand(-Z*s.diff(value, Z))
            numeric = s.lambdify(Z, value, 'numpy')
            for z in (.07, 1., 3., 9.):
                self.assertAlmostEqual(laplace_weight(d, z), float(numeric(z)), delta=2e-10)
            f = s.prod(p-s.Rational(2*j, d) for j in range(1, m+1))/(p+1)**(m+1)
            for j in range(1, m+1):
                self.assertNotEqual(s.diff(f, p).subs(p, s.Rational(2*j, d)), 0)

    def test_direct_signed_identity_without_expanding_primitive(self):
        volumes = np.array([.05, .3, 1.2])
        weights = np.array([.7, -.4, 1.])
        for d in (2, 3, 4, 7, 8):
            for rho in (.7, 2.3):
                expected = float(weights@kernel(d, rho*volumes))
                self.assertAlmostEqual(filtered_pair(d, rho, volumes, weights),
                                       expected, delta=3e-9)

    def test_point_subtraction_uses_even_log_moment(self):
        for d in range(2, 9):
            derivative = s.lambdify(Z, s.diff(kernel_polynomial(d)*s.exp(-Z), Z), 'numpy')
            a, beta = map(float, action_constants(d))
            for rho in (.7, 9.):
                value = quad(lambda z: -float(derivative(z))*point_primitive(d, z/rho, mass=1.7),
                             0, np.inf, epsabs=1e-10)[0]
                self.assertAlmostEqual(value, a/beta*1.7/rho, delta=2e-9)
            self.assertEqual(point_primitive(d, 0), 0.)

    def test_all_ordered_labels_fixed_temporal_masks_and_point_once(self):
        # Finite quadrature bookkeeping, not a new spacetime or asymptotic model.
        volumes = np.linspace(.01, .51, 9).reshape(3, 3)
        measure = np.arange(1., 10.).reshape(3, 3)/20
        time = np.array([[.03, .11, .4], [.2, .04, .7], [.18, .16, .05]])
        short = time < .16  # one fixed temporal split, independent of phase/rho
        h = np.array([.2, .7, .4])
        fields = (h, 1-h)
        point_weights = np.array([.3, .2, .5])
        for v in (.04, .3, 2.):
            phase = geometric_filter(7, volumes/v)
            total = float(np.sum(measure*phase))
            restored = math.fsum(float(np.sum(measure*a[:, None]*b[None, :]*mask*phase))
                                for a in fields for b in fields for mask in (short, ~short))
            self.assertAlmostEqual(total, restored, places=14)
        self.assertAlmostEqual(sum(point_weights@(a*b) for a in fields for b in fields),
                               sum(point_weights), places=14)

    def test_non_common_tip_overlap_and_point_incidence(self):
        # Exact membership identity on quadrature nodes; overlaps are indispensable.
        sets = (np.array([1., 1., 0., 0.]), np.array([0., 1., 1., 0.]))
        overlap = sets[0]*sets[1]
        union = np.maximum(*sets)
        values = kernel(7, np.array([.02, .1, .4, 2.]))
        correct = sum(float(x@values) for x in sets)-float(overlap@values)
        self.assertAlmostEqual(correct, float(union@values), places=12)
        self.assertNotAlmostEqual(sum(float(x@values) for x in sets), correct, places=4)
        self.assertEqual(2-1, 1)  # both active tips represent one physical point

    def test_whole_union_enters_before_nonlinear_kernel(self):
        volume = resolved_interval(.1, .8)
        phase = .8/volume
        correct = kernel(7, phase*volume)
        route_replacement = kernel(7, phase*volume/2)
        self.assertGreater(abs(correct-route_replacement), .1)

    def test_geometric_filter_endpoints_and_focal_survival(self):
        for d in (2, 3, 4, 7, 8):
            self.assertEqual(geometric_filter(d, 1), 0.)
            self.assertEqual(geometric_filter(d, 2), 0.)
            self.assertAlmostEqual(geometric_filter(d, 0)*float(filter_constant(d)), 1.)
            self.assertAlmostEqual(geometric_filter(d, 1e-30), geometric_filter(d, 0), places=12)
        moment = quad(lambda z: z*laplace_weight(7, z), 0, np.inf)[0]
        self.assertAlmostEqual(moment, 32., delta=2e-9)
        self.assertAlmostEqual(float(filter_constant(7))*moment*filtered_power(7, 1),
                               -5/128, places=11)

    def test_cs_audit_zero_times_pole_and_two_sector_majorant(self):
        slope = -s.Rational(3, 2)*s.gamma(-s.Rational(3, 2))*s.gamma(s.Rational(3, 2))
        self.assertEqual(s.simplify(slope), -s.pi)
        self.assertEqual(s.simplify(slope*(-s.Rational(2, 3))), 2*s.pi/3)
        residue = -s.pi/(3*(s.pi/12))*(1/(1-s.Rational(3, 2)))
        self.assertEqual(residue, 8)
        for L in (0., 2., 10.):
            value = quad(lambda z: (1+z)**-1.5, L, np.inf)[0]
            self.assertAlmostEqual(value, 2/math.sqrt(1+L), places=10)

    def test_invalid_inputs(self):
        calls = [lambda: resolved_interval(0, .4), lambda: resolved_interval(.5, .4),
                 lambda: resolved_interval(.1, -.1), lambda: resolved_interval(.1, 1.1),
                 lambda: resolved_interval(.1, .2, order=1),
                 lambda: projective_profile(math.nan), lambda: focal_growth(10),
                 lambda: physical_closing_weight(0, 3), lambda: filter_coefficients(1),
                 lambda: filter_coefficients(True), lambda: filtered_power(7, -1),
                 lambda: geometric_filter(7, [-.1, 0]), lambda: laplace_weight(7, math.inf),
                 lambda: filtered_pair(7, 0, [1.], [1.]),
                 lambda: filtered_pair(7, 1, [0.], [1.]),
                 lambda: filtered_pair(7, 1, [1.], [1., 2.]),
                 lambda: point_primitive(4, -.1)]
        for call in calls:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
