"""Adversarial finite C2 diagnostics; these do not certify its universal theorem."""

import unittest

import numpy as np
import sympy as sp
from scipy.integrate import quad

from curved_two_d import (
    CircleMetric, GraphRegion, PolynomialMetric, circle_action,
    circle_interval_below_period, circle_interval_slices, circle_interval_union,
    circle_rectangles, circle_target, cut_primitive, graph_pair, graph_point,
    graph_target, kernel, line_interval_slices, one, source_field,
    source_partition, target_field, target_partition, temporal_short_mask,
)


class CurvedTwoDTests(unittest.TestCase):
    def test_genuine_kernel_moments_logs_and_layer_factorials(self):
        z = sp.symbols('z', positive=True)
        K = (1-2*z+z*z/2)*sp.exp(-z)
        for power in (0, 1):
            self.assertEqual(sp.integrate(z**power*K, (z, 0, sp.oo)), 0)
        # Integrate each exponential monomial via Gamma'; avoid SymPy's
        # very slow unrestricted logarithmic-integral heuristic.
        coefficients = [1, -2, sp.Rational(1, 2)]
        for power, expected in ((0, -sp.Rational(1, 2)), (1, sp.Rational(1, 2))):
            log_moment = sum(c*sp.factorial(k+power)*sp.polygamma(0, k+power+1)
                             for k, c in enumerate(coefficients))
            self.assertEqual(sp.simplify(log_moment), expected)
        layer = [1, -2, 1]
        self.assertEqual(sum(layer[k]*z**k/sp.factorial(k) for k in range(3)), 1-2*z+z*z/2)
        for rho in (.7, 3.2, 17.):
            self.assertAlmostEqual(quad(lambda x: kernel(rho*x)*np.log(x),
                                        0, np.inf, epsabs=2e-11)[0], -1/(2*rho), places=10)
            self.assertAlmostEqual(quad(lambda x: x*kernel(rho*x)*np.log(x),
                                        0, np.inf, epsabs=2e-11)[0], 1/(2*rho*rho), places=10)

    def test_variable_rectangle_against_independent_physical_slices(self):
        metric = PolynomialMetric()
        for source, target in [((-.4, -.3), (.8, .6)), ((.2, -.7), (.7, -.21)),
                               ((-.1, .2), (.9, -.4)), ((0., 0.), (.5, .5))]:
            t, x = source
            T, X = target
            exact = metric.rectangle(t+x, t-x, T+X, T-X)
            self.assertAlmostEqual(exact, line_interval_slices(metric, source, target), places=12)
        # A frozen endpoint phase is not the actual weighted rectangle.
        actual = metric.rectangle(-.7, -.1, 1.4, .2)
        frozen = metric.density(-.4, -.3)*(2.1*.3/2)
        self.assertGreater(abs(actual-frozen), 1e-4)

    def test_null_edge_phase_uses_the_whole_variable_density_rectangle(self):
        metric = PolynomialMetric()
        u, v, length = -.4, .2, 1.3
        leading = quad(lambda s: metric.density((s+v)/2, (s-v)/2)/2,
                       u, u+length, epsabs=1e-13)[0]
        errors = [abs(metric.rectangle(u, v, u+length, v+e)/e-leading)
                  for e in (.02, .01, .005)]
        self.assertLess(errors[1], .51*errors[0])
        self.assertLess(errors[2], .51*errors[1])
        frozen = length*metric.density((u+v)/2, (u-v)/2)/2
        self.assertGreater(abs(frozen-leading), .005)

    def test_curvature_from_christoffel_contraction_with_repository_sign(self):
        t, x = sp.symbols('t x', real=True)
        f = 1+sp.Rational(2, 5)*t*t+sp.Rational(1, 5)*x*x+t*x/10
        coords = [t, x]
        g = sp.diag(f, -f)
        inv = g.inv()
        gamma = [[[sp.simplify(sum(inv[a, e]*(sp.diff(g[e, c], coords[b])
                   + sp.diff(g[e, b], coords[c])-sp.diff(g[b, c], coords[e]))/2
                   for e in range(2))) for c in range(2)] for b in range(2)] for a in range(2)]
        ric = sp.zeros(2)
        # R^a_bcd = d_d Gamma^a_cb - d_c Gamma^a_db + Gamma^a_de Gamma^e_cb
        #           - Gamma^a_ce Gamma^e_db; Ric_bd = R^a_bad.
        for b in range(2):
            for d in range(2):
                ric[b, d] = sum(sp.diff(gamma[a][a][b], coords[d])
                                 - sp.diff(gamma[a][d][b], coords[a])
                                 + sum(gamma[a][d][e]*gamma[e][a][b]
                                       - gamma[a][a][e]*gamma[e][d][b] for e in range(2))
                                 for a in range(2))
        scalar = sp.simplify(sum(inv[b, d]*ric[b, d] for b in range(2) for d in range(2)))
        expected = (f*(sp.diff(f, t, 2)-sp.diff(f, x, 2))
                    - sp.diff(f, t)**2+sp.diff(f, x)**2)/f**3
        self.assertEqual(sp.simplify(scalar-expected), 0)
        self.assertNotEqual(sp.diff(scalar, x), 0)
        self.assertAlmostEqual(float(scalar.subs({t: .3, x: -.4})),
                               PolynomialMetric().curvature(.3, -.4), places=14)
        u, v = sp.symbols('u v', real=True)
        w = f.subs({t: (u+v)/2, x: (u-v)/2})/2
        self.assertEqual(sp.simplify((scalar*f/2).subs({t: (u+v)/2, x: (u-v)/2})
                                    - 2*sp.diff(sp.log(w), u, v)), 0)

    def test_two_unequal_joint_atoms_and_actual_spacelike_faces(self):
        region = GraphRegion()
        x = np.linspace(-1, 1, 201)
        self.assertLess(max(abs(region.top_prime(x))), 1)
        self.assertLess(max(abs(region.top_prime(x)-region.height_prime(x))), 1)
        self.assertGreater(min(region.height(x[1:-1])), 0)
        self.assertAlmostEqual(region.height(-1), 0)
        self.assertAlmostEqual(region.height(1), 0)
        weights = region.joint_weights()
        self.assertGreater(abs(weights[0]-weights[1]), 1)
        self.assertAlmostEqual(sum(weights), 5.743111111111111, places=12)
        for point, target in zip((-1., 1.), weights):
            q = region.top_prime(point)
            p = q-region.height_prime(point)
            C = (1-p*q)/np.sqrt((1-p*p)*(1-q*q))
            self.assertAlmostEqual(C/np.sqrt(C*C-1), target, places=12)
        self.assertGreater(abs(graph_target(PolynomialMetric(), region)-sum(weights)), .04)

    def test_circle_union_vs_independent_slices_all_route_multiplicities(self):
        metric = CircleMetric()
        cases = [((0., .1), (.4, .4)), ((0., .1), (.8, .55)),
                 ((.2, .9), (1.6, .2)), ((.1, .95), (2.4, .37)),
                 ((0., .9), (.15, .05)), ((0., 0.), (.5, .5))]
        for source, target in cases:
            with self.subTest(source=source, target=target):
                self.assertAlmostEqual(circle_interval_union(metric, source, target),
                                       circle_interval_slices(metric, source, target), places=10)
        self.assertEqual(len(circle_rectangles(*cases[2], metric.period)), 3)
        self.assertEqual(len(circle_rectangles(*cases[3], metric.period)), 4)
        # Thick intervals include individually self-overlapping rectangles.
        lifts = circle_rectangles(*cases[3], metric.period)
        self.assertTrue(any(U-u > 1 and V-v > 1 for u, v, U, V in lifts))
        self.assertGreater(sum(metric.rectangle(*r) for r in lifts),
                           2*circle_interval_union(metric, *cases[3]))

    def test_circle_deck_seams_and_no_physical_lift_multiplicity(self):
        metric = CircleMetric()
        source, target = (.1, .94), (.86, .41)
        expected = circle_interval_union(metric, source, target)
        for n, m in [(-3, 2), (4, -2), (1, 1)]:
            self.assertAlmostEqual(expected, circle_interval_union(metric,
                                   (source[0], source[1]+n), (target[0], target[1]+m)), places=12)
        self.assertGreater(sum(metric.rectangle(*r) for r in circle_rectangles(source, target, 1.))
                           - expected, .01)

    def test_both_overlap_corners_and_both_endpoint_densities(self):
        metric = CircleMetric(a=.7, b=.23)
        u, v, p, q = .22, -.08, .035, .051
        source = ((u+v)/2, (u-v)/2)
        target = ((u+v+1+p+q)/2, (u-v+1+p-q)/2)
        A = metric.rectangle(u, v, u+1+p, v+q)
        B = metric.rectangle(u, v, u+p, v+1+q)
        Cx = metric.rectangle(u, v, u+p, v+q)
        Cy = metric.rectangle(u+1, v, u+1+p, v+q)
        actual = circle_interval_union(metric, source, target)
        self.assertAlmostEqual(actual, A+B-Cx-Cy, places=13)
        self.assertGreater(min(Cx, Cy), 0)
        self.assertGreater(abs(Cx-Cy), 1e-6)
        self.assertGreater(abs(actual-(A+B-Cx)), 1e-4)
        endpoint_product = metric.density(*source)*metric.density(*target)
        self.assertGreater(abs(endpoint_product-metric.density(*source)**2), .01)

    def test_fast_volume_against_unrestricted_physical_sweep(self):
        metric = CircleMetric()
        for t in (-.2, .3):
            for x in (.05, .87):
                for tau in (.12, .48, .51, .81, .97):
                    for r in (-min(.49, tau*.9), 0., min(.47, tau*.8)):
                        actual = circle_interval_below_period(metric, t, x, tau, r)
                        self.assertAlmostEqual(float(actual), circle_interval_union(
                            metric, (t, x), (t+tau, x+r)), places=12)

    def test_physical_union_primitive_correction_is_cubic_not_discarded(self):
        metric = CircleMetric(a=.6, b=.21)
        ratios = []
        for s in (.008, .004, .002):
            physical = cut_primitive(metric, s)
            summed = cut_primitive(metric, s, sum_phase=True)
            self.assertGreater(physical-summed, 0)
            ratios.append((physical-summed)/s**3)
        self.assertGreater(min(ratios), .2)
        self.assertLess(max(ratios)/min(ratios), 1.1)
        # Actual primitive has a linear+quadratic expansion: a finite diagnostic only.
        values = [cut_primitive(metric, s)/s for s in (.008, .004, .002)]
        self.assertLess(abs(values[0]-3*values[1]+2*values[2]), .001)

    def test_complete_graph_pair_two_independent_integration_orders(self):
        metric, region = PolynomialMetric(), GraphRegion()
        for rho in (3., 37., 211.):
            a = graph_pair(metric, region, rho, source_field, target_field, order=26)
            b = graph_pair(metric, region, rho, source_field, target_field,
                           ordering="displacement", order=28)
            self.assertAlmostEqual(a, b, places=12)
        self.assertGreater(abs(graph_pair(metric, region, 37., order=24)
                               - graph_pair(PolynomialMetric(0, 0, 0), region, 37., order=24)), 1e-5)

    def test_full_ordered_partitions_cutoff_conversion_point_once(self):
        metric, region, rho = PolynomialMetric(), GraphRegion(), 23.
        points = np.empty((2, 2))
        for i in range(2):
            for j in range(2):
                chi = lambda t, x, i=i: source_field(t, x)*(source_partition(t, x) if i == 0
                                                          else 1-source_partition(t, x))
                phi = lambda t, x, j=j: target_field(t, x)*(target_partition(t, x) if j == 0
                                                          else 1-target_partition(t, x))
                points[i, j] = graph_point(metric, region, chi, phi)
        point = graph_point(metric, region, source_field, target_field)
        self.assertAlmostEqual(points.sum(), point, places=14)
        pair = graph_pair(metric, region, rho, source_field, target_field, order=22)
        pieces = []
        for delta in (.09, .19):
            cells = graph_pair(metric, region, rho, source_field, target_field,
                               order=22, cutoff=delta, partitions=True)
            short = 2*rho*points-4*rho*rho*cells[0]
            long = -4*rho*rho*cells[1]
            pieces.append((short, long))
            self.assertAlmostEqual((short+long).sum(), 2*rho*point-4*rho*rho*pair, places=11)
            self.assertGreater(abs(cells[:, 0, 1].sum())+abs(cells[:, 1, 0].sum()), 1e-4)
        difference = pieces[0][0]-pieces[1][0]
        np.testing.assert_allclose(difference, -(pieces[0][1]-pieces[1][1]), atol=2e-13)
        self.assertGreater(abs(difference.sum()), .1)
        np.testing.assert_array_equal(temporal_short_mask([.08, .09, .1], .09), [True, False, False])

    def test_complete_curved_graph_response_and_nonzero_endpoint_fields(self):
        metric, region = PolynomialMetric(), GraphRegion()
        for weighted in (False, True):
            chi, phi = (source_field, target_field) if weighted else (one, one)
            target = graph_target(metric, region, weighted=weighted)
            errors = []
            for rho, order in ((1280., 40), (5120., 64)):
                action = (2*rho*graph_point(metric, region, chi, phi)
                          - 4*rho*rho*graph_pair(metric, region, rho, chi, phi, order=order))
                errors.append(abs(action-target))
            self.assertLess(errors[1], .4*errors[0])
            self.assertLess(errors[1], .06)
        # Nonzero field/flux terms change the independently calculated target.
        self.assertGreater(abs(graph_target(metric, region, True)-graph_target(metric, region)), .02)

    def test_complete_compact_cauchy_slab_and_closing_cut_contact(self):
        metric = CircleMetric()
        for duration in (.4, .5, .8):
            target = circle_target(metric, duration)
            low = circle_action(metric, duration, 320., order=30)
            high = circle_action(metric, duration, 1280., order=48)
            self.assertGreater(target, .1)  # Nonzero curvature; J is empty.
            self.assertLess(abs(high-target), .3*abs(low-target))
            self.assertLess(abs(high-target), .031)
        self.assertAlmostEqual(circle_target(CircleMetric(a=0, b=0), .8), 0.)
        self.assertLess(abs(circle_action(CircleMetric(a=0, b=0), .8, 1280., order=48)), .02)

    def test_diagnostic_domains_are_not_silent_geometry_extensions(self):
        with self.assertRaises(ValueError):
            PolynomialMetric(a=.1, b=.1, c=1.)
        with self.assertRaises(ValueError):
            CircleMetric(period=0)
        with self.assertRaises(ValueError):
            circle_action(CircleMetric(), 1.2, 20.)
        with self.assertRaises(ValueError):
            cut_primitive(CircleMetric(), .5)
        with self.assertRaises(ValueError):
            graph_pair(PolynomialMetric(), GraphRegion(), 0.)


if __name__ == '__main__':
    unittest.main()
