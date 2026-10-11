"""Diagnostics for notes/finite-lift-flat-reduction.md, not a theorem checker.

The circle is used only to check exact physical-union bookkeeping, including
self-overlap outside the first-cut band. Rank tests refute tempting proof
shortcuts, not the complete action conjecture. The closing-fibre model tests
signed matching; it is not claimed to be a complete geometric action.
"""

import itertools
import math
import unittest

import sympy as s
from scipy.integrate import quad

from dimension_kernels import Z, interval_coefficient, kernel_polynomial
from full_partner_globalization import primitive_response


def _union_length(intervals):
    """Lebesgue length of the physical union, never a multiplicity sum."""
    total = 0.0
    left = right = None
    for a, b in sorted((a, b) for a, b in intervals if b > a):
        if left is None:
            left, right = a, b
        elif a > right:
            total += right - left
            left, right = a, b
        else:
            right = max(right, b)
    return total if left is None else total + right - left


def _circle_pieces(length, tau, target, intermediate):
    """All (target lift, intermediate lift, temporal interval) at one point.

    Finite bounds are derived from each causal path's spatial-length bound.
    This test helper is deliberately separate from the thin/first-cut APIs.
    """
    result = []
    for m in range(math.ceil((-tau - target) / length),
                   math.floor((tau - target) / length) + 1):
        for n in range(math.ceil((-tau - intermediate) / length),
                       math.floor((tau - intermediate) / length) + 1):
            start = abs(intermediate + n * length)
            end = tau - abs(target + m * length - intermediate - n * length)
            if start <= end:
                result.append((m, n, (start, end)))
    return result


def _circle_distance(a, length):
    return abs((a + length / 2) % length - length / 2)


def _intersection_length(intervals):
    return max(0.0, min(b for _, b in intervals) - max(a for a, _ in intervals))


class FiniteLiftFlatReductionTest(unittest.TestCase):
    def test_finite_lift_union_against_independent_quotient_distances(self):
        for length in (0.7, 1.0, 2.3):
            for ratio in (0.2, 0.6, 1.3, 3.2):
                tau = ratio * length
                for target_ratio in (0.0, 0.19, 0.5, 0.83):
                    target = target_ratio * length
                    for z_ratio in (0.0, 0.07, 0.23, 0.5, 0.79, 0.99):
                        z = z_ratio * length
                        pieces = _circle_pieces(length, tau, target, z)
                        actual = _union_length([piece for _, _, piece in pieces])
                        independent = max(0.0, tau - _circle_distance(z, length)
                                          - _circle_distance(z - target, length))
                        self.assertAlmostEqual(actual, independent, delta=3e-14 * length)

    def test_individual_projection_can_self_overlap(self):
        pieces = _circle_pieces(1.0, 3.2, 0.0, 0.1)
        one_diamond = [piece for m, _, piece in pieces if m == 0]
        self.assertGreaterEqual(sum(a < 1.5 < b for a, b in one_diamond), 3)
        counted = sum(b - a for a, b in one_diamond)
        physical = _union_length(one_diamond)
        self.assertGreater(counted, physical + 1.0)
        self.assertAlmostEqual(physical, 3.0)
        # A first-cut negative control still needs both target routes.
        pieces = _circle_pieces(1.0, 0.6, 0.5, 0.75)
        self.assertAlmostEqual(_union_length([p for _, _, p in pieces]), 0.1)
        self.assertEqual(_union_length([p for m, _, p in pieces if m == 0]), 0.0)

    def test_all_intersection_orders_not_pairwise_inclusion_exclusion(self):
        pieces = _circle_pieces(1.0, 2.4, 0.31, 0.23)
        intervals = [p for _, _, p in pieces if p[0] < 1.2 < p[1]][:6]
        self.assertGreaterEqual(len(intervals), 4)
        exact = sum((-1) ** (size + 1) * sum(
            _intersection_length(subset)
            for subset in itertools.combinations(intervals, size))
            for size in range(1, len(intervals) + 1))
        physical = _union_length(intervals)
        pair_only = sum(b - a for a, b in intervals) - sum(
            _intersection_length(pair) for pair in itertools.combinations(intervals, 2))
        self.assertAlmostEqual(exact, physical, places=12)
        self.assertGreater(abs(pair_only - physical), 0.1)
        # The pairwise OVERCOUNT BOUND used in FL5 is nevertheless valid.
        overcount = sum(b - a for a, b in intervals) - physical
        pair_bound = sum(_intersection_length(pair)
                         for pair in itertools.combinations(intervals, 2))
        self.assertTrue(0 <= overcount <= pair_bound)

    def test_physical_volume_not_sum_or_selected_diamond_kernel(self):
        length, tau, target = 1.0, 2.4, 0.31
        def fibre(z):
            return _union_length([p for _, _, p in _circle_pieces(
                length, tau, target, z)])
        actual = quad(fibre, 0, length, points=[0.31, 0.5, 0.81],
                      epsabs=1e-12, epsrel=1e-12)[0]
        self.assertAlmostEqual(actual, length * tau - length ** 2 / 2, places=12)
        lifts = range(math.ceil((-tau - target) / length),
                      math.floor((tau - target) / length) + 1)
        volumes = [(tau ** 2 - (target + m * length) ** 2) / 2 for m in lifts]
        self.assertGreater(sum(volumes), actual)
        kernel = s.lambdify(Z, kernel_polynomial(2) * s.exp(-Z), 'math')
        self.assertGreater(abs(kernel(actual) - kernel(sum(volumes))), 0.01)
        self.assertGreater(abs(kernel(actual) - sum(kernel(v) for v in volumes)), 0.01)

    def test_affine_lorentz_phase_and_endpoint_covectors(self):
        eta = s.diag(1, -1)
        boost = s.Matrix([[s.Rational(5, 4), s.Rational(3, 4)],
                          [s.Rational(3, 4), s.Rational(5, 4)]])
        self.assertEqual(boost.T * eta * boost, eta)
        self.assertEqual(boost.det(), 1)
        xt, xs, yt, ys = s.symbols('xt xs yt ys', real=True)
        x, y = s.Matrix([xt, xs]), s.Matrix([yt, ys])
        displacement = boost * y + s.Matrix([2, -3]) - x
        phase = (displacement.T * eta * displacement)[0]
        self.assertEqual(s.simplify(s.Matrix([s.diff(phase, v) for v in x])
                                   + 2 * eta * displacement), s.zeros(2, 1))
        self.assertEqual(s.simplify(s.Matrix([s.diff(phase, v) for v in y])
                                   - 2 * boost.T * eta * displacement), s.zeros(2, 1))

    def test_pairwise_ranks_do_not_imply_simultaneous_face_rank(self):
        xt, xs, yt, ys = s.symbols('xt xs yt ys', real=True)
        length = s.Symbol('L', positive=True)
        gap, displacement = yt - xt, ys - xs
        u = gap ** 2 - (length / 2 + displacement) ** 2
        v = gap ** 2 - (-length / 2 + displacement) ** 2
        a, b = xt + length / 4, length / 4 - yt
        variables = [xt, xs, yt, ys]
        point = {xt: -length / 4, yt: length / 4, xs: 0, ys: 0}
        rows = s.Matrix([u, v, a, b]).jacobian(variables).subs(point)
        self.assertEqual(rows.rank(), 3)
        self.assertEqual(rows[:2, :2].rank(), 2)
        self.assertEqual(rows[:2, 2:].rank(), 2)
        for selected in ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)):
            self.assertEqual(rows[list(selected), :].rank(), 3)
        self.assertEqual(s.simplify(rows[0, :] + rows[1, :]
                                   + 2 * length * (rows[2, :] + rows[3, :])),
                         s.zeros(1, 4))

    def test_four_route_corner_has_only_three_phase_coordinates(self):
        tau, x, y = s.symbols('tau x y', real=True)
        length = s.Symbol('L', positive=True)
        phases = [tau ** 2 - (x + i * length / 2) ** 2
                  - (y + j * length / 2) ** 2
                  for i, j in itertools.product((-1, 1), repeat=2)]
        self.assertEqual(s.expand(phases[0] + phases[3] - phases[1] - phases[2]), 0)
        point = {tau: length / s.sqrt(2), x: 0, y: 0}
        self.assertTrue(all(s.simplify(p.subs(point)) == 0 for p in phases))
        rows = s.Matrix(phases).jacobian([tau, x, y]).subs(point)
        self.assertEqual(rows.rank(), 3)
        for pair in itertools.combinations(range(4), 2):
            self.assertEqual(rows[list(pair), :].rank(), 2)

    def test_two_null_form_cone_box_bound_in_each_dimension(self):
        u, v = s.symbols('u v', nonnegative=True)
        upper_u, upper_v = s.symbols('U W', positive=True)
        for d in range(2, 10):
            q = s.Rational(d, 2)
            ball = s.pi ** s.Rational(d - 2, 2) / s.gamma(q)
            integral = ball / 2 * s.integrate(s.integrate(
                (u * v) ** (q - 1), (v, 0, upper_v)), (u, 0, upper_u))
            expected = ball / (2 * q ** 2) * (upper_u * upper_v) ** q
            self.assertEqual(s.simplify(integral - expected), 0)
            self.assertEqual(expected.subs(upper_u, 0), 0)
            self.assertEqual(expected.subs(upper_v, 0), 0)

    def test_exact_two_route_matching_with_unequal_signed_weights(self):
        u, v, w = s.symbols('u v w', real=True)
        amplitude = (u - s.Rational(1, 4)) * (v + s.Rational(1, 7))
        def integral(u0, u1, v0, v1):
            return s.integrate(s.integrate(amplitude, (v, v0, v1)), (u, u0, u1))
        reference = integral(0, w, -s.Rational(1, 2), s.Rational(3, 2))
        reference += integral(-1, 2, 0, w)
        first_strip = integral(0, w, 0, s.Rational(3, 2))
        second_strip = integral(0, 2, 0, w)
        corner = integral(0, w, 0, w - u)
        physical = integral(0, w, -s.Rational(1, 2), 0)
        physical += integral(-1, 0, 0, w) + corner
        matched = reference + corner - first_strip - second_strip
        self.assertEqual(s.expand(matched - physical), 0)
        self.assertNotEqual(s.expand(first_strip - second_strip), 0)
        self.assertNotEqual(s.expand(reference + corner - first_strip - physical), 0)

    def test_closing_fibre_keeps_fractional_term_and_both_strips(self):
        # Integral_{-1}^1 [z^2-t]_+ dz for 0 <= t <= 1.
        # This is an exact contact model, not an asserted full-region action.
        t, w, z = s.symbols('t w z', positive=True)
        fibre = s.Rational(2, 3) - 2 * t + s.Rational(4, 3) * t ** s.Rational(3, 2)
        independent = 2 * s.integrate(z ** 2 - t, (z, s.sqrt(t), 1))
        self.assertEqual(s.simplify(fibre - independent), 0)
        corner = s.integrate(t * fibre, (t, 0, w))
        u = s.Symbol('u', positive=True)
        strip = s.integrate(s.integrate(fibre, (t, u, 1)), (u, 0, w))
        matched = s.simplify(corner - 2 * strip)
        expected = -2 * w / 5 + w ** 2 - 4 * w ** 3 / 3 + s.Rational(24, 35) * w ** s.Rational(7, 2)
        self.assertEqual(s.simplify(matched - expected), 0)
        remainder = matched + 2 * w / 5 - w ** 2
        self.assertEqual(s.limit(remainder / w ** 2, w, 0, dir='+'), 0)
        self.assertEqual(s.limit(s.diff(fibre, t, 2), t, 0, dir='+'), s.oo)
        self.assertNotEqual(s.simplify(corner - strip - expected), 0)

    def test_directional_contact_derivative_need_not_be_linear(self):
        # F(u,v)=1+min(u,v) comes from two coincident moving lower bounds.
        # Its directional derivative is nonlinear, but its q=2 corner has
        # an exact integer cubic coefficient after the full angular integral.
        derivative = lambda a, b: min(a, b)
        self.assertEqual(derivative(1, 0), 0)
        self.assertEqual(derivative(0, 1), 0)
        self.assertEqual(derivative(1, 1), 1)
        coefficient = (2 - math.sqrt(2)) / 3
        for w in (0.01, 0.07, 0.2):
            direct = quad(lambda theta: quad(
                lambda radius: radius * (1 + min(radius * math.cos(theta),
                                                  radius * math.sin(theta))),
                0, w, epsabs=1e-14)[0], 0, math.pi / 2,
                points=[math.pi / 4], epsabs=1e-14)[0]
            self.assertAlmostEqual(direct, math.pi * w ** 2 / 4 + coefficient * w ** 3,
                                   delta=1e-13)
        self.assertEqual(primitive_response(4, 2, 19), 0)
        self.assertEqual(primitive_response(4, 3, 19), 0)

    def test_dependent_fourth_phase_uses_three_scaled_coordinates(self):
        # Exact rank-three homogeneous sector: v4=v1+v3-v2 >= 0.
        # For q=1 its sum is 2*(v1+v3), NOT four independent coordinates.
        u, v, w = s.symbols('u v w', positive=True)
        volume = s.integrate(s.integrate(u + v, (v, 0, w / 2 - u)),
                             (u, 0, w / 2))
        self.assertEqual(s.simplify(volume - w ** 3 / 24), 0)
        self.assertNotEqual(s.simplify(volume - w ** 4 / s.factorial(4)), 0)
        # A cubic primitive is at or above critical order through 4D, but
        # that fact supplies no bound on the higher-dimensional remainder.
        for d in (2, 3, 4):
            rho = s.Symbol('rho', positive=True)
            self.assertEqual(s.limit(primitive_response(d, 3, rho), rho, s.oo), 0)

    def test_cubic_jet_does_not_remove_higher_dimensional_critical_modes(self):
        rho = s.Symbol('rho', positive=True)
        exponent = s.Symbol('r', positive=True)
        # Actual G7 signs: odd critical pure modes and even critical logs
        # cannot be discarded just because all lower integer modes cancel.
        odd = primitive_response(5, s.Rational(7, 2), rho)
        self.assertNotEqual(s.simplify(odd), 0)
        self.assertEqual(s.diff(odd, rho), 0)
        even_log = s.diff(primitive_response(6, exponent, rho), exponent).subs(exponent, 4)
        self.assertNotEqual(s.simplify(even_log), 0)
        self.assertEqual(s.simplify(s.diff(even_log, rho)), 0)

    def test_signed_critical_roots_and_retained_contact_response(self):
        rho = s.Symbol('rho', positive=True)
        self.assertEqual(primitive_response(2, 1, rho), 0)
        self.assertEqual(primitive_response(2, 2, rho), 0)
        for r in (s.Integer(3), s.Rational(7, 2)):
            response = primitive_response(2, r, rho)
            self.assertNotEqual(response, 0)
            self.assertEqual(s.limit(response, rho, s.oo), 0)
            # Direct signed integration after scaling; no absolute-kernel substitution.
            c = float(interval_coefficient(2))
            kernel = s.lambdify(Z, kernel_polynomial(2) * s.exp(-Z), 'math')
            direct = -4 * float(r) * c ** (-float(r)) * 11 ** (2 - float(r)) * quad(
                # z=t^2 removes the fractional endpoint from this independent
                # quadrature (QUADPACK underestimates its error without it).
                lambda t: 2 * t ** (2 * float(r) - 1) * kernel(t * t),
                0, math.inf, epsabs=2e-13, epsrel=2e-13)[0]
            self.assertAlmostEqual(direct, float(response.subs(rho, 11)), delta=2e-11)


if __name__ == '__main__':
    unittest.main()
