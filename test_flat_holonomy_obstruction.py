"""Focused checks of the WRITTEN complete-action argument, not a proof checker.

The geometric counterexample and all-sector asymptotics are proved in
notes/flat-holonomy-obstruction.md. These controls test exact group/phase
algebra, the product pushforward, all fifteen matching sectors, positivity
and the signed response. No fitted isolated-sector response is a theorem.
"""

import itertools
import math
import unittest

import sympy as s
from scipy.integrate import quad

from dimension_kernels import action_constants, interval_coefficient
from full_partner_globalization import primitive_response


def _q_ball_moment(q, powers):
    q = s.sympify(q)
    return (s.prod(s.gamma((a + 1) / q) for a in powers)
            / q ** len(powers) / s.gamma(1 + sum(a + 1 for a in powers) / q))


def _matched_coefficient(q):
    return (_q_ball_moment(q, [0, 0, 0, 0]) - 4 * _q_ball_moment(q, [1, 0, 0])
            - 2 * _q_ball_moment(q, [2, 0]) + 6 * _q_ball_moment(q, [1, 1])
            + s.Rational(1, 6))


def _compose(first, second):
    a, b = first
    c, d = second
    return a * c, a * d + b


class FlatHolonomyObstructionTest(unittest.TestCase):
    def test_group_generators_and_translation_subgroup(self):
        identity, reflection = s.eye(3), s.diag(1, 1, -1)
        first = reflection, s.Matrix([1, 0, 0])
        second = reflection, s.Matrix([0, 1, 0])
        third = identity, s.Matrix([0, 0, 10])
        self.assertEqual(_compose(first, second), _compose(second, first))
        self.assertEqual(_compose(first, second), (identity, s.Matrix([1, 1, 0])))
        self.assertEqual(_compose(first, first), (identity, s.Matrix([2, 0, 0])))
        inverse_first = reflection, s.Matrix([-1, 0, 0])
        self.assertEqual(_compose(_compose(first, third), inverse_first),
                         (identity, s.Matrix([0, 0, -10])))
        # A nontrivial group element has a nonzero translation in a direction
        # fixed by its linear part; it cannot have a spatial fixed point.
        for m, n, k in itertools.product(range(-2, 3), repeat=3):
            if (m, n, k) == (0, 0, 0):
                continue
            linear = s.diag(1, 1, (-1) ** (m + n))
            translation = s.Matrix([m, n, 10 * k])
            augmented = (identity - linear).row_join(translation)
            self.assertGreater(augmented.rank(), (identity - linear).rank())

    def test_actual_four_lifts_against_finite_group_enumeration(self):
        for center in (0.0, 5.0):
            for source_y, target_y in ((0.0, 0.0), (0.06, -0.04), (-0.03, -0.08)):
                x, z, tau = 0.01, -0.02, 0.78
                b_squared = 0.02
                phases = []
                for m, n, k in itertools.product(range(-2, 3), range(-2, 3), range(-1, 2)):
                    distance_squared = ((0.5 + x + m) ** 2 + (0.5 + z + n) ** 2
                                        + ((-1) ** (m + n) * (center + target_y)
                                           + 10 * k - center - source_y) ** 2 + b_squared)
                    if distance_squared <= tau ** 2:
                        phases.append(tau ** 2 - distance_squared)
                predicted = [tau ** 2 - (epsilon / 2 + x) ** 2 - (eta / 2 + z) ** 2
                             - (epsilon * eta * target_y - source_y) ** 2 - b_squared
                             for epsilon, eta in itertools.product((-1, 1), repeat=2)]
                self.assertEqual(len(phases), 4)
                for observed, expected in zip(sorted(phases), sorted(predicted)):
                    self.assertAlmostEqual(observed, expected, places=13)

    def test_walsh_phases_product_coordinate_and_rank_drop(self):
        tau, x, z, y, w, b2 = s.symbols('tau x z y w b2', real=True)
        signs = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
        phases = s.Matrix([tau ** 2 - (epsilon / 2 + x) ** 2
                           - (eta / 2 + z) ** 2 - (epsilon * eta * w - y) ** 2 - b2
                           for epsilon, eta in [(s.Integer(e), s.Integer(f)) for e, f in signs]])
        mean = tau ** 2 - s.Rational(1, 2) - x ** 2 - z ** 2 - y ** 2 - w ** 2 - b2
        walsh = s.Matrix([[1, epsilon, eta, epsilon * eta] for epsilon, eta in signs])
        self.assertEqual(abs(walsh.det()), 16)
        self.assertEqual(s.simplify(phases - walsh * s.Matrix([mean, -x, -z, 2 * y * w])),
                         s.zeros(4, 1))
        self.assertEqual(s.simplify((s.Matrix([[1, -1, -1, 1]]) * phases)[0]), 8 * y * w)
        jacobian = phases.jacobian([tau, x, z, y, w])
        null = {tau: s.sqrt(2) / 2, x: 0, z: 0, y: 0, w: 0, b2: 0}
        self.assertEqual(phases.subs(null), s.zeros(4, 1))
        self.assertEqual(jacobian.subs(null).rank(), 3)
        for y_value, w_value in ((s.Rational(1, 10), 0), (0, s.Rational(1, 10))):
            nearby = {tau: s.sqrt(s.Rational(1, 2) + y_value ** 2 + w_value ** 2),
                      x: 0, z: 0, y: y_value, w: w_value, b2: 0}
            self.assertEqual(phases.subs(nearby), s.zeros(4, 1))
            self.assertEqual(jacobian.subs(nearby).rank(), 4)

    def test_closing_face_critical_values_are_not_the_slab_width(self):
        h = s.Symbol('h', real=True)
        a, b, c = s.symbols('a b c', real=True)
        # Three corners other than --: u=v=-h, so X=Z=h.
        weights = s.solve([a + b + c - 1,
                           a + b - c + 2 * h,
                           a - b + c + 2 * h], [a, b, c])
        parity = s.simplify((a - b - c).subs(weights))
        self.assertEqual(parity, -1 - 4 * h)
        y = s.Symbol('Y', positive=True)
        # W=Y would require parity=1, impossible for h=2Y^2.
        self.assertTrue(s.simplify(1 - parity.subs(h, 2 * y ** 2)).is_positive)
        # W=-Y requires parity=-1, forcing h=0 and hence Y=W=0.
        self.assertEqual(s.solve(parity + 1, h), [0])
        # Adjacent corners force X=-1/2, Z=h, B=-2h; the two
        # nonzero choices W=+/-Y would require 1+4Y^2=0.
        self.assertTrue((1 + 4 * y ** 2).is_positive)
        tau2_adjacent, tau2_diagonal = s.Rational(1, 4), s.Rational(1, 2)
        self.assertNotEqual(s.Rational(4, 5) ** 2, tau2_adjacent)
        self.assertNotEqual(s.Rational(4, 5) ** 2, tau2_diagonal)

    def test_product_pushforward_keeps_both_source_signs(self):
        radius, a, b = 0.4, 0.7, 1.3
        for h in (0.00001, 0.002, 0.03, -0.003):
            lower, upper = math.log(abs(h) / (2 * radius)), math.log(radius)
            # Both Y signs have combined density dY/|Y|, so logarithmic
            # coordinates give this integral with NO extra factor two.
            actual = quad(lambda t: 1 + a * (math.exp(2 * t) + h ** 2 / (4 * math.exp(2 * t)))
                          + b * h ** 2 / 4, lower, upper, epsabs=2e-13, epsrel=2e-13)[0]
            log_part = math.log(2 * radius ** 2 / abs(h))
            expected = log_part + a * (radius ** 2 - h ** 2 / (4 * radius ** 2))
            expected += b * h ** 2 / 4 * log_part
            self.assertAlmostEqual(actual, expected, delta=3e-13)
            self.assertGreater(abs(actual / 2 - expected), 0.1)

    def test_fifteen_sector_matching_by_independent_multinomial_expansion(self):
        lambdas = [1, -1, -1, 1]
        for q in (s.Integer(3), s.Rational(7, 2), s.Integer(4), s.Rational(11, 2)):
            pieces = []
            for size in range(1, 5):
                for active in itertools.combinations(range(4), size):
                    inactive = [i for i in range(4) if i not in active]
                    variables = s.symbols(f'u:{size}')
                    power = 4 - size
                    polynomial = s.Poly(sum(lambdas[i] * u for i, u in zip(active, variables)) ** power,
                                        *variables)
                    value = sum(coefficient * _q_ball_moment(q, degrees)
                                for degrees, coefficient in polynomial.terms())
                    value /= s.factorial(power) * s.prod(lambdas[i] for i in inactive)
                    pieces.append(value)
            self.assertEqual(len(pieces), 15)
            total = sum(pieces)
            self.assertEqual(s.simplify(s.expand_func(total - _matched_coefficient(q))), 0)
            self.assertGreater(float(total), 0)
            four_only = _q_ball_moment(q, [0] * 4)
            self.assertGreater(abs(float(total - four_only)), 0.1)

    def test_positive_fourth_moment_identity_not_a_fitted_sign(self):
        z = s.symbols('z:4')
        moments = [s.Integer(1)] + list(s.symbols('m1:5'))
        polynomial = s.Poly((z[0] + z[1] - z[2] - z[3]) ** 4, *z)
        fourth = s.expand(sum(coefficient * s.prod(moments[a] for a in degrees)
                              for degrees, coefficient in polynomial.terms()))
        m1, m2, m3, m4 = moments[1:]
        identity = m1 ** 4 - 2 * m2 * m1 ** 2 - s.Rational(2, 3) * m3 * m1
        identity += s.Rational(3, 2) * m2 ** 2 + m4 / 6
        self.assertEqual(s.expand(fourth / 24 - identity), 0)
        for q in (s.Integer(3), s.Rational(7, 2), s.Integer(4), s.Integer(8)):
            substitution = {moments[k]: s.gamma(1 + k / q) for k in range(1, 5)}
            positive_expression = (fourth / (24 * m4)).subs(substitution)
            self.assertEqual(s.simplify(s.expand_func(
                positive_expression - _matched_coefficient(q))), 0)
            self.assertGreater(float(positive_expression), 0)

    def test_closing_fibre_rescaling_and_positive_amplitude(self):
        duration, base = 0.8, 0.5
        for d in (6, 7, 8, 11):
            p, q = d - 4, d / 2
            area = 2 * math.pi ** (p / 2) / math.gamma(p / 2)
            depth = duration ** 2 - base
            direct = area / 2 * quad(
                lambda r: r ** (p - 1) * (duration - math.sqrt(base + r * r)) / math.sqrt(base + r * r),
                0, math.sqrt(depth), epsabs=1e-14)[0]
            scaled = depth ** (p / 2 + 1) * area / 2 * quad(
                lambda r: r ** (p - 1) * (1 - r * r)
                / (math.sqrt(base + depth * r * r) * (duration + math.sqrt(base + depth * r * r))),
                0, 1, epsabs=1e-14)[0]
            self.assertAlmostEqual(direct, scaled, delta=1e-14)
            self.assertGreater(direct, 0)
            amplitude = 10 ** p / 8 * direct
            coefficient = amplitude * float(_matched_coefficient(s.Rational(d, 2)))
            self.assertGreater(coefficient, 0)
            self.assertEqual(p / 2 + 1, q - 1)

    def test_signed_log_response_and_full_scale(self):
        exponent = s.Symbol('r', positive=True)
        rho = s.Symbol('rho', positive=True)
        for d in (6, 7, 8, 9, 12):
            q = s.Rational(d, 2)
            remainder_product = s.prod(1 - s.Rational(4, k) for k in range(5, d // 2 + 2))
            c, beta = interval_coefficient(d), action_constants(d)[1]
            exact = s.diff(primitive_response(d, exponent, rho), exponent).subs(exponent, 4)
            expected = -beta / q * c ** (-4 / q) * s.gamma(4 / q) * remainder_product * rho ** (1 - 3 / q)
            self.assertEqual(s.simplify(s.expand_func(exact - expected)), 0)
            self.assertEqual(primitive_response(d, 4, rho), 0)
            self.assertGreater(float(-exact.subs(rho, 1)), 0)
            self.assertEqual(s.limit(rho ** (-1 / q) * s.log(rho), rho, s.oo), 0)
        # Six-dimensional response is finite/nonzero; higher dimensions grow.
        self.assertEqual(1 - s.Rational(6, 6), 0)
        self.assertGreater(1 - s.Rational(6, 7), 0)


if __name__ == '__main__':
    unittest.main()
