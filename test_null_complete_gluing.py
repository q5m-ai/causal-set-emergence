"""Finite NG/FL/DL diagnostics; these do not certify asymptotic estimates."""

import itertools
import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import action_constants, factor_count, mellin_factor
from null_cartesian_pushforward import kernel, time_density_average
from null_complete_gluing import (
    box_pair, curved_rectangle_action, finite_null_action, flat_bicone_target,
    floor_tail, floor_tail_mass, future_tip_cross_pair,
    positive_quadratic_constant, rectangle_action, rectangle_density,
)


class CompleteGluingTests(unittest.TestCase):
    def test_exact_normal_green_identity_with_actual_conformal_phase(self):
        p, q = s.symbols('p q', real=True)
        pt, qt, sigma = (p-1)/2, (q+1)/2, 2*(q-p)
        # Actual d=2 diamond average of A(t)=1+t^2; no fitted endpoint phase.
        average = 1+qt**2-(qt-pt)*qt+(qt-pt)**2/3-sigma/24
        xi, epsilon = sigma*average, s.Rational(2, 3)
        Z = xi**2*s.exp(-xi/epsilon)/2
        xp, xq, xpq = s.diff(xi, p), s.diff(xi, q), s.diff(xi, p, q)
        rhs = s.diff(Z, p, q)/(xp*xq)-xpq*s.diff(Z, p)/(xp**2*xq)
        z = xi/epsilon
        expected = (1-2*z+z*z/2)*s.exp(-z)
        self.assertEqual(s.simplify(s.expand((rhs-expected)*s.exp(z))), 0)
        value = {p: s.Rational(1, 5), q: s.Rational(2, 5)}
        # In d=2 the actual rectangular volume is separately affine in
        # endpoint differentiation: this particular mixed derivative is zero.
        self.assertEqual(s.simplify(xpq), 0)
        self.assertAlmostEqual(float(average.subs(value)),
                               time_density_average(2, -.4, .7, .4), places=14)

    def test_curved_four_dimensional_normal_chain_correction_is_nonzero(self):
        p, q = s.symbols('p q', real=True)
        pt, qt, sigma = (p-1)/2, (q+1)/2, 2*(q-p)
        average = 1+qt**2-(qt-pt)*qt+s.Rational(3, 10)*(qt-pt)**2-sigma/30
        xi, epsilon = sigma*s.sqrt(average), s.Rational(2, 3)
        z = xi**2/epsilon**2
        # Genuine G_4(x)=x^2*(3-2*x^2)*exp(-x^2)/6.
        Z = xi**2*(3-2*z)*s.exp(-z)/6
        xp, xq, xpq = s.diff(xi, p), s.diff(xi, q), s.diff(xi, p, q)
        value = {p: s.Rational(1, 5), q: s.Rational(2, 5)}
        without_second = (s.diff(Z, p, q)/(xp*xq)).subs(value)
        corrected = without_second-(xpq*s.diff(Z, p)/(xp**2*xq)).subs(value)
        expected = ((1-9*z+8*z*z-s.Rational(4, 3)*z**3)*s.exp(-z)).subs(value)
        self.assertEqual(s.simplify(corrected-expected), 0)
        self.assertGreater(abs(float(without_second-expected)), 1e-4)
        self.assertAlmostEqual(float(average.subs(value)),
                               time_density_average(4, -.4, .7, .4), places=14)

    def test_all_four_normal_boundary_and_bulk_terms_are_needed(self):
        v, upper, epsilon = 2., .7, .3
        a = lambda p: 1+p+p*p
        ap = lambda p: 1+2*p
        b = lambda q: 1+.3*q+.2*q*q
        bp = lambda q: .3+.4*q
        Z = lambda p, q: v*v*(q-p)**2/2*math.exp(-v*(q-p)/epsilon)
        direct = quad(lambda p: quad(lambda q: a(p)*b(q)/4*
                      kernel(2, v*(q-p)/epsilon), p, upper, epsabs=1e-12)[0],
                      0, upper, epsabs=1e-12)[0]
        face = a(0)*b(upper)*Z(0, upper)/(4*v*v)
        source = quad(lambda p: ap(p)*b(upper)*Z(p, upper)/(4*v*v), 0, upper)[0]
        target = -quad(lambda q: a(0)*bp(q)*Z(0, q)/(4*v*v), 0, upper)[0]
        bulk = -quad(lambda p: quad(lambda q: ap(p)*bp(q)*Z(p, q)/(4*v*v),
                                    p, upper)[0], 0, upper)[0]
        self.assertAlmostEqual(direct, face+source+target+bulk, delta=2e-12)
        self.assertTrue(all(abs(term) > 1e-5 for term in (face, source, target, bulk)))
        self.assertGreater(abs(direct-face), 1e-4)

    def test_physical_point_and_all_ordered_labels_once(self):
        for hp, hq in itertools.product((0., .2, .6, 1.), repeat=2):
            p, q = (hp, 1-hp), (hq, 1-hq)
            self.assertAlmostEqual(sum(p[a]*q[b] for a, b in itertools.product(range(2), repeat=2)), 1)
            self.assertAlmostEqual(sum(p[a]*p[b] for a, b in itertools.product(range(2), repeat=2)), 1)
        h = .3
        self.assertNotAlmostEqual(h*h+(1-h)**2, 1)  # Mixed point terms are not optional.

    def test_whole_rectangle_kernel_and_overlap_density(self):
        U, V = 1.3, 1.7
        box = ((0., U), (0., V))
        for rho in (.7, 5., 30.):
            pair = box_pair(rho, box, box, order=48)
            pushed = quad(lambda z: rectangle_density(z, U, V)*kernel(2, rho*z),
                          0, U*V/2, epsabs=2e-12)[0]
            self.assertAlmostEqual(pair, pushed, delta=2e-11)
            self.assertAlmostEqual(2*rho*U*V/2-4*rho*rho*pair,
                                   rectangle_action(rho, U, V), delta=2e-9)
        self.assertEqual(action_constants(2), (s.Integer(2), s.Integer(4)))

    def test_real_physical_short_split_and_both_logarithms(self):
        U, V, cutoff, rho = 1.8, 1.6, .35, 7.
        short = quad(lambda z: rectangle_density(z, U, V, temporal_cutoff=cutoff)
                     *kernel(2, rho*z), 0, cutoff*cutoff/2, epsabs=1e-12)[0]
        direct = quad(lambda u: quad(lambda v: (U-u)*(V-v)*kernel(2, rho*u*v/2)/4,
                                     0, 2*cutoff-u, epsabs=1e-12)[0],
                      0, 2*cutoff, epsabs=1e-12)[0]
        self.assertAlmostEqual(short, direct, delta=2e-11)
        full = box_pair(rho, ((0, U), (0, V)), ((0, U), (0, V)))
        self.assertGreater(abs(full-short), .001)
        z = s.symbols('z', positive=True)
        expansion = s.series((1+z)*s.log((1+s.sqrt(1-2*z))**2/(2*z))
                             -3*s.sqrt(1-2*z), z, 0, 3).removeO().expand()
        self.assertEqual(expansion.coeff(s.log(z)), -1-z)

    def test_genuine_logarithmic_moments_and_source_kernel(self):
        exponent = s.symbols('exponent', positive=True)
        transform = s.gamma(exponent)*mellin_factor(2, exponent)
        self.assertEqual(s.diff(transform, exponent).subs(exponent, 1), -s.Rational(1, 2))
        self.assertEqual(s.diff(transform, exponent).subs(exponent, 2), s.Rational(1, 2))
        self.assertAlmostEqual(quad(lambda z: (1-z)*math.exp(-z), 0, np.inf)[0], 0)
        self.assertAlmostEqual(quad(lambda z: (1-z)*math.exp(-z)*math.log(z),
                                   0, np.inf)[0], -1)

    def test_tip_internal_and_all_incoming_cross_partners(self):
        U, V, radius, rho = 1.6, 1.3, .4, 9.
        tip = ((U-radius, U), (V-radius, V))
        left = ((0, U-radius), (0, V))
        bottom_right = ((U-radius, U), (0, V-radius))
        actual = box_pair(rho, left, tip)+box_pair(rho, bottom_right, tip)
        self.assertAlmostEqual(actual, future_tip_cross_pair(rho, U, V, radius), delta=2e-11)
        self.assertEqual(box_pair(rho, tip, left), 0)
        self.assertEqual(box_pair(rho, tip, bottom_right), 0)
        L_action = (rectangle_action(rho, U-radius, V)+rectangle_action(rho, U, V-radius)
                    -rectangle_action(rho, U-radius, V-radius))
        self.assertAlmostEqual(rectangle_action(rho, U, V), L_action+
                               rectangle_action(rho, radius, radius)-4*rho*rho*actual,
                               delta=2e-9)
        rho = 1000.
        internal = rectangle_action(rho, radius, radius)
        incoming = -4*rho*rho*future_tip_cross_pair(rho, U, V, radius)
        self.assertAlmostEqual(internal, 2)
        self.assertAlmostEqual(incoming, -2)

    def test_all_membership_subsets_and_actual_pinch_components(self):
        rho = 3.
        # L-shaped past front, with its nonempty intersection retained.
        value = finite_null_action(rho, [(0, 0)], [(1, 2), (2, 1)])
        self.assertAlmostEqual(value, 2*rectangle_action(rho, 1, 2)-rectangle_action(rho, 1, 1))
        # F=(u>0 or v>0), P=(u<0 or v<0), clipped by a fixed outer box.
        value = finite_null_action(rho, [(0, -1), (-1, 0)], [(0, 1), (1, 0)])
        self.assertAlmostEqual(value, 2*rectangle_action(rho, 1, 1))
        self.assertEqual(box_pair(rho, ((0, 1), (-1, 0)), ((-1, 0), (0, 1))), 0)
        self.assertEqual(finite_null_action(rho, [(2, 2)], [(1, 1)]), 0)
        # Duplicate labels do not duplicate physical points or pairs.
        self.assertAlmostEqual(finite_null_action(rho, [(0, 0), (0, 0)], [(1, 1), (1, 1)]),
                               rectangle_action(rho, 1, 1))

    def test_two_direction_boolean_local_domains(self):
        points = tuple(itertools.product((0, 1), repeat=2))
        upsets = [frozenset(p for p, bit in zip(points, bits) if bit)
                  for bits in itertools.product((0, 1), repeat=4)
                  if all(not bits[i] or bits[j] for i, p in enumerate(points)
                         for j, q in enumerate(points) if p[0] <= q[0] and p[1] <= q[1])]
        self.assertEqual(len(upsets), 6)
        domains = {F & (frozenset(points)-Q) for F in upsets for Q in upsets}
        self.assertIn(frozenset(((0, 1), (1, 0))), domains)
        self.assertNotIn(frozenset(((0, 0), (1, 1))), domains)
        self.assertNotIn(frozenset(((0, 0), (1, 1), (0, 1))), domains)

    def test_true_curved_rectangle_two_complete_pair_domains(self):
        for amplitude in (-.4, .7):
            endpoint = curved_rectangle_action(12., amplitude, order=22)
            displacement = curved_rectangle_action(12., amplitude, order=22,
                                                    representation='displacements')
            self.assertAlmostEqual(endpoint, displacement, delta=3e-10)
        self.assertAlmostEqual(curved_rectangle_action(12., 0., order=22),
                               rectangle_action(12., 1., 1.), delta=3e-10)
        self.assertGreater(abs(curved_rectangle_action(12., .7)-rectangle_action(12., 1., 1.)), .01)

    def test_floor_signed_height_majorant_is_integrable_in_both_parities(self):
        for d in (2, 3, 4, 7):
            m = factor_count(d)
            actual_mass = quad(lambda z: z**(d+1)/(1+z**d)**(2*(m+1)/d),
                               0, np.inf, epsabs=2e-10)[0]
            self.assertAlmostEqual(actual_mass, floor_tail_mass(d), delta=2e-9)
            tail = floor_tail(d, 20.)
            power = 3 if d % 2 == 0 else 2
            self.assertAlmostEqual(tail*20**power, 1/power, delta=.002)

    def test_floor_flux_and_two_coincidence_traces(self):
        hN, hT = .3, .4
        k = math.sqrt(1-hT*hT)
        determinant = 1-hN*hN-hT*hT
        plus, minus = determinant/(k+hN), determinant/(k-hN)
        self.assertAlmostEqual(plus+hN, k)
        self.assertAlmostEqual(minus-hN, k)
        self.assertAlmostEqual(plus+minus, 2*k)
        for gN in (k, -k):
            self.assertAlmostEqual(gN*gN+hT*hT, 1)
        self.assertNotAlmostEqual(plus+minus, k)

    def test_dyadic_joint_point_and_cross_scale_summability(self):
        for codimension in (3, 4, 7):
            a = (codimension-2)/2
            values = []
            for first in (4, 8, 12):
                value = sum(2.**(-j*(codimension-2))+
                            sum(2.**(-i*(codimension-2))*2.**(-(j-i)*a)
                                for i in range(j+1))
                            for j in range(first, first+70))
                values.append(value/2.**(-first*a))
            self.assertLess(max(values), 12)
        # Codimension two gives no summable decay from this absolute bound.
        self.assertEqual(sum(1 for _ in range(40)), 40)

    def test_full_bicone_independent_coefficient_and_odd_signs(self):
        for T in (.5, 1., 2.):
            local, nonlocal_term, total = flat_bicone_target(3, T)
            self.assertAlmostEqual(local, 2*math.pi*T, places=10)
            self.assertAlmostEqual(total, (math.pi+2)*T, places=9)
            self.assertGreater(nonlocal_term, 0)
        for d in (4, 6, 8):
            self.assertEqual(positive_quadratic_constant(d), 0)
            local, term, total = flat_bicone_target(d, 1.)
            self.assertEqual(term, 0)
            self.assertEqual(total, local)
        self.assertLess(flat_bicone_target(5, 1.)[1], 0)

    def test_null_cusp_actual_determinant_and_boost_scaling(self):
        pv, qv, a, b, yp, yq, r = s.symbols('pv qv a b yp yq r', positive=True)
        B = (qv-pv)*(yq*yq/(qv+b)-yp*yp/(pv+a))-(yq-yp)**2
        matrix = s.hessian(B, (yp, yq))/2
        self.assertEqual(s.factor(matrix.det()+(a-b)*(qv-pv)/((pv+a)*(qv+b))), 0)
        self.assertEqual(s.simplify(B.subs({yp: r*yp, yq: r*yq})-r*r*B), 0)
        for pv0, qv0 in ((1., 1.001), (1., 2.), (2., 4.)):
            coeff = np.array([-(pv0+1)/(qv0+1), 2., -(qv0+2)/(pv0+2)])
            roots = np.roots(coeff)
            self.assertTrue(np.isreal(roots).all())
            self.assertTrue((roots > 0).all())

    def test_invalid_inputs_do_not_assign_divergent_formula_a_value(self):
        bad = (lambda: rectangle_action(0, 1, 1),
               lambda: rectangle_density(0, 1, 1),
               lambda: rectangle_density(.1, 1, 1, temporal_cutoff=1),
               lambda: future_tip_cross_pair(1, 1, 1, 1),
               lambda: box_pair(1, ((0, 0), (0, 1)), ((0, 1), (0, 1))),
               lambda: finite_null_action(1, [], [(1, 1)]),
               lambda: curved_rectangle_action(1, -1),
               lambda: curved_rectangle_action(1, 0, order=True),
               lambda: floor_tail(3, -1),
               lambda: flat_bicone_target(2, 1))
        for call in bad:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
