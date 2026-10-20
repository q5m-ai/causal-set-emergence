"""Adversarial finite NF/NT/NP regressions, not asymptotic certificates."""

from fractions import Fraction
import itertools
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

from dimension_kernels import (
    Z, action_constants, factor_count, interval_coefficient, kernel_polynomial,
    mellin_factor, sphere_area,
)
from general_metric_gate import gauss_rule
from null_front_accounting import (
    closed_causal_order, cone_memberships, layers_on_subset, nonempty_subsets,
    null_overlap, null_short_weight, null_time_weight, null_time_weight_closed,
    null_time_weight_unreduced, ramp_remainder,
)
from seven_dimensional_focusing import (
    ANTIPODAL_COEFFICIENT, interval_volume, sign_certificate,
)


class NullFrontAccountingTests(unittest.TestCase):
    def test_every_nested_membership_pattern_not_just_two_tips(self):
        for count in range(1, 8):
            for state in itertools.product(range(3), repeat=count):
                # 0: neither; 1: source only; 2: both. Future-only is impossible.
                p, q = np.array(state) > 0, np.array(state) == 2
                actual = int(np.any(p) and np.any(q))
                restored = sum(sign * int(np.all(p[list(ids)]) and np.all(q[list(ids)]))
                               for ids, sign in nonempty_subsets(count))
                self.assertEqual(restored, actual)
        # Truncating at pairwise intersections gives zero, not one, here.
        self.assertEqual(3 - 3, 0)
        self.assertEqual(3 - 3 + 1, 1)

    def test_actual_causal_pairs_and_exclusive_layers_with_all_intersections(self):
        centers = np.array([[-.6, 0., 0.], [.6, 0., 0.], [0., .6, 0.],
                            [0., -.6, 0.], [0., 0., .6]])
        points = np.array([[-2., 0., 0., 0.], [-1.5, .1, 0., 0.],
                           [-1., 0., 0., 0.], [-.7, .1, 0., 0.],
                           [-.4, .6, 0., 0.], [-.4, -.6, 0., 0.],
                           [-.3, 0., .6, 0.], [-.2, 0., 0., .6]])
        labels = cone_memberships(points, centers)
        order = closed_causal_order(points)
        union = np.any(labels, axis=1)
        restored = np.zeros(4, dtype=int)
        point_count = 0
        pair_count = 0
        for ids, sign in nonempty_subsets(len(centers)):
            selected = np.all(labels[:, ids], axis=1)
            restored += sign * layers_on_subset(order, selected)
            point_count += sign * np.count_nonzero(selected)
            pair_count += sign * np.count_nonzero(order & selected[:, None] & selected[None, :])
        np.testing.assert_array_equal(restored, layers_on_subset(order, union))
        self.assertEqual(point_count, np.count_nonzero(union))
        self.assertEqual(pair_count, np.count_nonzero(order & union[:, None] & union[None, :]))
        self.assertGreater(np.sum(restored), 0)
        # There really are common-to-exclusive partners, not disjoint caps.
        self.assertTrue(order[0, 4] and np.all(labels[0]) and not np.all(labels[4]))

    def test_nonpast_family_rejects_the_additivity_shortcut(self):
        # Related exclusive endpoints in arbitrary sets defeat the pair valuation.
        p, q = [True, False], [False, True]
        restored = sum(sign * int(all(p[i] and q[i] for i in ids))
                       for ids, sign in nonempty_subsets(2))
        self.assertEqual(restored, 0)
        self.assertTrue(any(p) and any(q))

    def test_dependent_high_multiplicity_contact_has_the_proved_rank(self):
        for count in (3, 7, 13, 29):
            angles = np.arange(count)*2*np.pi/count
            centers = np.column_stack((np.cos(angles), np.sin(angles), np.zeros(count)))
            x = np.array([0., 0., np.sqrt(3.)])
            # Q_i=t^2-|x-c_i|^2 at t=-2; arbitrary multiplicity on a crease curve.
            normals = np.column_stack((-4*np.ones(count), -2*(x-centers)))
            self.assertEqual(np.linalg.matrix_rank(normals), 3)
            augmented = np.vstack((normals, [1., 0., 0., 0.]))
            self.assertEqual(np.linalg.matrix_rank(augmented), 4)
            # At the minimum-radius vertex H=1 the floor instead fails the rank.
            tangent_normals = np.column_stack((-2*np.ones(count), 2*centers))
            self.assertEqual(np.linalg.matrix_rank(np.vstack((tangent_normals, [1., 0., 0., 0.]))), 3)

    def test_dimensional_kernel_beta_residues_both_parities(self):
        for d in (*range(2, 12), 19, 20):
            m = factor_count(d)
            c = interval_coefficient(d)
            a, beta = action_constants(d)
            area = sphere_area(d)
            e0 = s.gamma(s.Rational(d-1, 2))/s.factorial(m) * s.gamma(m+1-s.Rational(d, 2))/s.gamma(s.Rational(1, 2))
            e2 = (s.gamma(1+s.Rational(2, d))*s.gamma(s.Rational(d-1, 2))/s.factorial(m)
                  * s.gamma(m-s.Rational(d, 2))/s.gamma(-s.Rational(1, 2)))
            self.assertEqual(s.simplify(beta*area/(2*d*c)*e0-a), 0)
            self.assertEqual(s.simplify(beta*area/(2*d)*c**(-1-s.Rational(2, d))*e2), -2)
            self.assertTrue(1-2*s.Rational(m, d) < 0)
            self.assertTrue(min(1+s.Rational(3, d), s.Rational(2*(m+1), d)) > 1+s.Rational(2, d))
            # Genuine recurrence, not reusing K4 or a Gaussian response.
            for j in range(1, m+1):
                self.assertEqual(mellin_factor(d, s.Rational(2*j, d)), 0)
        self.assertNotEqual(kernel_polynomial(7), kernel_polynomial(4))

    def test_dimensional_conformal_coefficient_is_independent_curvature(self):
        d = s.symbols('d', integer=True, positive=True)
        omega, box, norm = s.symbols('omega box norm', positive=True)
        # After A=Omega^d, isolate coefficients of Box Omega and its gradient norm.
        scalar = (d-1)*omega**(d-3)*box + ((d-1)**2-(d+2)*(d-1)/2)*omega**(d-4)*norm
        geometric = (d-1)*omega**(d-3)*box + (d-1)*(d-4)/2*omega**(d-4)*norm
        self.assertEqual(s.simplify(scalar-geometric), 0)
        self.assertEqual(s.simplify(2-(1+2/d)), (d-2)/d)

    def test_endpoint_overlap_from_actual_source_null_coordinates(self):
        for tau, z in ((.4, .1), (2.5, 1.2), (3., 1.), (3.5, .7)):
            # Integrate over original source t; z-source is intersection of intervals.
            def width(t):
                lo = max(-2+abs(t), -z-2+abs(t+tau))
                hi = min(2-abs(t), -z+2-abs(t+tau))
                return max(0., hi-lo)
            original = quad(width, -2, 2-tau, points=[q for q in (0., -tau) if -2 < q < 2-tau],
                            epsabs=1e-10, limit=200)[0]
            self.assertAlmostEqual(null_overlap(tau, z), original, delta=2e-8)
        self.assertEqual(null_overlap(3., 1.), 0.)
        self.assertGreater(null_overlap(3., 0.), 0.)

    def test_complete_null_weight_against_unreduced_partners_and_antiderivative(self):
        for u in (.02, .4, 1.3, np.pi, 3.8):
            positive = null_time_weight(u)
            self.assertGreater(positive, 0)
            self.assertAlmostEqual(positive, null_time_weight_unreduced(u), delta=4e-8)
            self.assertAlmostEqual(positive, null_time_weight_closed(u), delta=4e-8)
        self.assertEqual(null_time_weight(4.), 0.)
        self.assertGreater(null_time_weight(3.999), 0.)

    def test_physical_temporal_split_not_a_reduced_u_split(self):
        delta = .7
        for u in (.03, .2, .65, delta, np.pi):
            short = null_short_weight(u, delta)
            raw_short = null_time_weight_unreduced(u, cutoff=delta, short=True)
            raw_long = null_time_weight_unreduced(u, cutoff=delta)
            self.assertAlmostEqual(short, raw_short, delta=2e-9)
            self.assertAlmostEqual(short+raw_long, null_time_weight(u), delta=4e-8)
        self.assertGreater(null_time_weight_unreduced(.2, cutoff=delta), 0.)
        self.assertEqual(null_short_weight(delta, delta), 0.)

    def test_exact_origin_short_target_and_physical_point_normalization(self):
        u, tau, delta, T, vy = s.symbols('u tau delta T VY', positive=True)
        gs = s.expand(s.pi**2*u*s.integrate(((T-tau)**2-(tau*tau-u*u)/4)*(tau*tau-u*u), (tau, u, delta)))
        g4, g6 = 2*s.pi**2*T*T/3, 4*s.pi**2/15
        self.assertEqual(gs.coeff(u, 4), g4)
        self.assertEqual(gs.coeff(u, 6), g6)
        c = interval_coefficient(7)
        a, beta = action_constants(7)
        C, mass = 2*s.pi*vy, vy*T*T/2
        origin = s.simplify(-C*g4/(35*c))
        self.assertEqual(s.simplify(origin/mass), -s.Rational(1024, 5))
        moment = sum(coef*s.factorial(power[0]) for power, coef in s.Poly(kernel_polynomial(7), Z).terms())
        self.assertEqual(moment, -s.Rational(5, 128))
        self.assertEqual(s.simplify(a*mass-beta*origin*moment), 0)
        finite = beta*C*(g4/140+g6/14)*c**(-s.Rational(9, 7))*s.Rational(5, 64)*s.gamma(s.Rational(9, 7))
        self.assertEqual(s.simplify(finite-(mass+2*vy)), 0)
        self.assertNotEqual(s.simplify(a*mass-beta*origin*moment/2), 0)

    def test_matched_focusing_sign_uses_the_complete_existing_certificate(self):
        lo, hi = sign_certificate()
        self.assertLess(Fraction(1, 400), lo)
        self.assertLess(hi, Fraction(13, 5000))
        G = null_time_weight(np.pi)
        self.assertGreater(G, 0.)
        _, beta = action_constants(7)
        C = 2*np.pi*(4*np.pi*20**3)
        factor = 5*float(beta)/128*C*G/(3*ANTIPODAL_COEFFICIENT)
        self.assertGreater(factor*float(lo), 0.)
        self.assertLess(factor*float(lo), factor*float(hi))

    def test_complete_finite_density_pair_domain_two_independent_integrals(self):
        # Full theta domain, actual W on both transition sides; no asymptotic fit.
        rho = .015
        kernel = s.lambdify(Z, kernel_polynomial(7)*s.exp(-Z), 'numpy')

        def reduced(order):
            nodes, weights = gauss_rule(order)
            total = 0.
            for x, wx in zip(nodes, weights):
                theta = np.pi*x
                edges = sorted(set((theta, 4., min(4., 2*np.pi-theta))))
                for lo, hi in zip(edges, edges[1:]):
                    for y, wy in zip(nodes, weights):
                        u = lo+(hi-lo)*y
                        total += np.pi*wx*np.sin(theta)*(hi-lo)*wy*null_time_weight(u)*kernel(
                            rho*interval_volume(u, theta, order=20, flat_order=16))
            return total

        def original(order):
            nodes, weights = gauss_rule(order)
            total = 0.
            for x, wx in zip(nodes, weights):
                theta = np.pi*x
                edges = (theta, (16+theta*theta)/8, 4.)
                for lo, hi in zip(edges, edges[1:]):
                    for y, wy in zip(nodes, weights):
                        tau = lo+(hi-lo)*y
                        ztop = min(4-tau, np.sqrt(max(0., tau*tau-theta*theta)))
                        for zz, wz in zip(nodes, weights):
                            z = ztop*zz
                            rtop = np.sqrt(max(0., tau*tau-theta*theta-z*z))
                            for rr, wr in zip(nodes, weights):
                                r = rtop*rr
                                u = np.sqrt(tau*tau-z*z-r*r)
                                total += (np.pi*wx*np.sin(theta)*(hi-lo)*wy*2*ztop*wz
                                          *4*np.pi*rtop*wr*r*r*null_overlap(tau, z)
                                          *kernel(rho*interval_volume(u, theta, order=16, flat_order=12)))
            return total

        full = reduced(18)
        raw = original(10)
        self.assertGreater(full, 0)
        self.assertLess(abs(raw/full-1), .004)
        # Omitting an orientation or an endpoint-measure factor is not innocuous.
        self.assertGreater(abs(raw/(2*full)-1), .49)

    def test_ramp_bound_keeps_zero_levels_and_arbitrary_contact_order(self):
        h = np.array([-1., 0., .001, .03, .4, 1.])
        a = np.array([1., 2., .7, 1.5, .2, .6])
        eps = .05
        remainder = ramp_remainder(h, eps, a)
        bound = eps**2*np.max(a)**2*((h > 0) & (h <= eps*np.max(a)))
        self.assertTrue(np.all(np.abs(remainder) <= bound+1e-15))
        self.assertEqual(remainder[1], 0.)
        for m in (1, 2, 5, 11):
            eps = .02
            root = eps**(1/(2*m))
            actual = 2*quad(lambda y: (y**(2*m)-eps)**2, root, 1)[0]
            exact = (2/(4*m+1)-4*eps/(2*m+1)+2*eps**2
                     -16*m*m/((2*m+1)*(4*m+1))*eps**(2+1/(2*m)))
            self.assertAlmostEqual(actual, exact, places=13)

    def test_characteristic_rank_failure_and_input_guards(self):
        self.assertEqual(-1+np.sqrt(1-0.)*1., 0.)
        for theta in (.1, .03, .01):
            self.assertLess(abs((1-np.cos(theta))/(theta*theta/2)-1), .001)
        for operation in (lambda: null_time_weight(-1), lambda: null_short_weight(.2, 3),
                          lambda: null_overlap(1, 2), lambda: list(nonempty_subsets(0))):
            with self.assertRaises(ValueError):
                operation()


if __name__ == '__main__':
    unittest.main()
