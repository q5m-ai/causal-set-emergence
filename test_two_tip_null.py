"""Focused #134 geometry/finite-density regressions, not a global limit proof."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from mixed_poisson import discrete_action, layer_counts
from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT
from two_tip_null import TwoTipMixed


def causal(p, q):
    delta = np.asarray(q) - np.asarray(p)
    return delta[0] >= 0 and np.dot(delta[1:], delta[1:]) <= delta[0]**2


class TwoTipTests(unittest.TestCase):
    def setUp(self):
        self.region = TwoTipMixed()

    def test_distinct_strata_and_failed_single_tip_fibre(self):
        region, a = self.region, self.region.a
        p = [-0.8, 0, 0, 0]
        qplus, qminus = [-0.1, a, 0, 0], [-0.1, -a, 0, 0]
        plus, minus = region.cap_masks([p, qplus, qminus])
        np.testing.assert_array_equal(plus, [True, True, False])
        np.testing.assert_array_equal(minus, [True, False, True])
        self.assertTrue(causal(p, qplus) and causal(p, qminus))
        self.assertFalse(causal(qminus, [0, a, 0, 0]))
        self.assertFalse(causal(qplus, qminus) or causal(qminus, qplus))
        # Future crease center is a regular point of a two-dimensional disk.
        # The normal perturbations detect BOTH null faces, not a third cone tip.
        for transverse in (0, 0.3, 0.7):
            depth = math.hypot(a, transverse)
            below = [-depth-1e-6, 0, transverse, 0]
            above = [-depth+1e-6, 0, transverse, 0]
            p_mask, m_mask = region.cap_masks([below, above])
            np.testing.assert_array_equal(p_mask & m_mask, [True, False])
        # All tips are excluded from the open set, approached from U but not L.
        for sign in (-1, 1):
            masks = region.cap_masks([[0, sign*a, 0, 0], [-1e-5, sign*a, 0, 0]])
            np.testing.assert_array_equal(masks[0] | masks[1], [False, True])
            self.assertFalse(np.any(masks[0] & masks[1]))
        # Triple circle has t=-1 despite the nonplanar floor; r_plus=r_minus=1.
        for angle in (0, 0.7, 2.1):
            w = math.sqrt(1-a*a)*np.array([math.cos(angle), math.sin(angle)])
            x = np.r_[0, w]
            self.assertAlmostEqual(np.linalg.norm(x-[a, 0, 0]), region.height(x[0]))
            self.assertAlmostEqual(np.linalg.norm(x+[a, 0, 0]), 1)
        self.assertNotEqual(region.height(a), region.height(-a))

    def test_sampled_closed_containment_and_no_exclusive_cross_pairs(self):
        rng = np.random.default_rng(134)
        points = rng.uniform([-1.1, -1.6, -1.1, -1.1], [0, 1.6, 1.1, 1.1], (500, 4))
        plus, minus = self.region.cap_masks(points)
        checked = 0
        regions = ((plus, lambda a, b: a), (minus, lambda a, b: b),
                   (plus | minus, lambda a, b: a | b), (plus & minus, lambda a, b: a & b))
        for membership, combine in regions:
            inside = points[membership]
            for p, q in zip(inside[:-1], inside[1:]):
                if causal(p, q):
                    # Include the endpoints of the closed interval explicitly.
                    z = np.array([p, 0.25*p+0.75*q, q])
                    a, b = self.region.cap_masks(z)
                    self.assertTrue(combine(a, b).all())
                    checked += 1
        self.assertGreater(checked, 0)
        for p in points[plus & ~minus]:
            for q in points[minus & ~plus]:
                self.assertFalse(causal(p, q) or causal(q, p))

    def test_induced_crease_metric_and_marked_normals_symbolically(self):
        a, y, z = s.symbols("a y z", positive=True)
        depth = s.sqrt(a*a+y*y+z*z)
        tangent = s.Matrix([[-y/depth, -z/depth], [0, 0], [1, 0], [0, 1]])
        screen = s.simplify(tangent.T*s.diag(-1, 1, 1, 1)*tangent)
        self.assertEqual(s.simplify(screen.det()-a*a/depth**2), 0)
        kp, km = s.Matrix([1, a/depth, -y/depth, -z/depth]), s.Matrix([1, -a/depth, -y/depth, -z/depth])
        metric = s.diag(1, -1, -1, -1)
        self.assertEqual(s.simplify((kp.T*metric*kp)[0]), 0)
        self.assertEqual(s.simplify((kp.T*metric*km)[0]-2*a*a/depth**2), 0)
        alpha, beta = s.symbols("alpha beta", positive=True)
        self.assertEqual(s.simplify(((alpha*kp).T*metric*(beta*km))[0]
                                   - alpha*beta*2*a*a/depth**2), 0)
        # SN metric is intrinsic, not Euclidean spacetime surface area.
        R, dr1, dr2 = s.symbols("R dr1 dr2", positive=True)
        cone_tangent = s.Matrix([[-dr1, -dr2], [dr1, dr2], [R, 0], [0, R]])
        self.assertEqual(cone_tangent.T*(-metric)*cone_tangent, s.diag(R*R, R*R))
        self.assertNotEqual(s.expand((cone_tangent.T*cone_tangent).det()), R**4)

    def test_independent_joint_cuts_areas_and_flat_floor_calibration(self):
        areas = self.region.joint_areas()
        self.assertAlmostEqual(areas["union"]+areas["lens"], areas["plus"]+areas["minus"], places=11)
        self.assertGreater(areas["lens"], 0)
        for sign in (-1, 1):
            self.assertAlmostEqual(self.region.joint_radius(sign, -sign*self.region.a), 1)
            for mu in np.linspace(-1, 1, 41):
                r = self.region.joint_radius(sign, float(mu))
                axial = sign*self.region.a+r*mu
                self.assertAlmostEqual(r, self.region.height(axial), places=12)
                self.assertGreater(1-self.region.b*mu*math.cos(axial), 0)
                if abs(mu+sign*self.region.a) > 1e-8:
                    self.assertEqual(sign*axial > 0, sign*(mu+sign*self.region.a) > 0)
        flat = TwoTipMixed(b=0)
        flat_areas, volumes = flat.joint_areas(), flat.volumes()
        self.assertAlmostEqual(flat_areas["union"], 4*math.pi*(1+flat.a))
        self.assertAlmostEqual(flat_areas["lens"], 4*math.pi*(1-flat.a))
        self.assertAlmostEqual(volumes["lens"], math.pi/3*(1-flat.a)**3*(1+flat.a))
        self.assertAlmostEqual(volumes["plus"], math.pi/3)
        self.assertGreater(abs(areas["union"]-flat_areas["union"]), 1e-4)
        # Independent time-slice integration for the flat lens volume.
        slices = quad(lambda v: 2*math.pi/3*(v-flat.a)**2*(2*v+flat.a), flat.a, 1)[0]
        self.assertAlmostEqual(slices, volumes["lens"], places=12)
        self.assertGreater(self.region.volumes()["lens"], 0)

    def test_full_configuration_valuation_and_cross_chart_negative_controls(self):
        points = np.array([[-0.9, 0, 0, 0], [-0.7, 0, 0, 0],
                           [-0.1, 0.5, 0, 0], [-0.1, -0.5, 0, 0]])
        plus, minus = self.region.cap_masks(points)
        self.assertTrue((plus | minus).all())
        self.assertEqual(layer_counts(points), (3, 2, 0, 0))
        # Counts of the same endpoints agree: restriction loses no interval points.
        np.testing.assert_array_equal(np.array(layer_counts(points)),
                                      np.array(layer_counts(points[plus]))
                                      + np.array(layer_counts(points[minus]))
                                      - np.array(layer_counts(points[plus & minus])))
        for rho in (0.5, 12, 100):
            action = lambda mask: discrete_action(rho, points[mask])
            full = discrete_action(rho, points)
            self.assertAlmostEqual(full, action(plus)+action(minus)-action(plus & minus))
            self.assertNotAlmostEqual(full, action(plus)+action(minus))  # missing overlap
            # A genuinely disjoint partition has common-to-exclusive causal pairs.
            wrong = action(plus & minus)+action(plus & ~minus)+action(minus & ~plus)
            self.assertNotAlmostEqual(full, wrong)
        # Separate an intermediate point into another chart: layer indices change,
        # not just the number of endpoint pairs. All three are in the full lens.
        chain = np.array([[-0.9, 0, 0, 0], [-0.75, 0, 0, 0], [-0.6, 0, 0, 0]])
        self.assertEqual(layer_counts(chain), (2, 1, 0, 0))
        self.assertEqual(layer_counts(chain[[0, 2]]), (1, 0, 0, 0))

    def test_central_partner_domain_volume_and_missing_interval_symbolically(self):
        a, u, v, z = s.symbols("a u v z", positive=True)
        v0, v1 = (u*u+a*a)/(2*u), (u+a)/2
        z0 = (2*u*v-u*u-a*a)/(2*a)
        lens, ball = v*v-(z+a)**2, (u-v)**2-z*z
        volume = 2*s.pi*(s.integrate(s.integrate(lens, (z, 0, v-a)), (v, a, v0))
                         + s.integrate(s.integrate(ball, (z, 0, z0))
                                       + s.integrate(lens, (z, z0, v-a)), (v, v0, v1))
                         + s.integrate(s.integrate(ball, (z, 0, u-v)), (v, v1, u)))
        expected = s.pi*(u-a)**4*(u+2*a)/(24*u)
        self.assertEqual(s.factor(volume-expected), 0)
        omitted = s.pi*a*(u-a)**2*(u*u+2*a*u-a*a)/(12*u)
        self.assertEqual(s.factor(s.pi*(u*u-a*a)**2/24-volume-omitted), 0)
        for depth in (0.6, 0.8, 0.95):
            integrated = self.region.central_partners(0, depth, 4)
            self.assertAlmostEqual(integrated.volume, self.region.central_volume(depth), places=13)
            self.assertEqual(integrated.layers[1:], (0, 0, 0))
            self.assertAlmostEqual(integrated.signed, integrated.volume, places=14)

    def test_positive_layers_signed_fibre_and_refinement_not_global_limit(self):
        u, a = 0.8, self.region.a
        for rho in (0.5, 20, 100, 1000):
            low = self.region.central_partners(rho, u, 16)
            high = self.region.central_partners(rho, u, 24)
            np.testing.assert_allclose(low.layers, high.layers, atol=2e-14, rtol=2e-10)
            self.assertAlmostEqual(low.signed, high.signed, delta=2e-13)
            self.assertTrue(all(x > 0 for x in high.layers))
            self.assertAlmostEqual(high.signed, np.dot(high.layers, [1, -9, 16, -8]), delta=2e-14)
            wrong_factorials = np.dot(high.layers, [1, -9, 8, -4/3])
            self.assertGreater(abs(wrong_factorials-high.signed), 1e-12)
            self.assertLessEqual(sum(high.layers), high.volume + 2e-17)  # roundoff
            single_interval = -math.expm1(-INTERVAL_CONSTANT*rho*(u*u-a*a)**2)/rho
            if rho == 0.5:  # positivity witness, NOT an asymptotic obstruction
                self.assertGreater(high.signed, 0)
                self.assertGreater(single_interval-high.signed, 0)
                complete_union = 2*single_interval-high.signed
                self.assertGreater(complete_union, single_interval)

    def test_true_tip_neighborhood_exclusivity_and_normalized_bound(self):
        delta = 0.05
        for sign in (-1, 1):
            for r in (0, delta/4, delta/2):
                point = [-(delta+r)/2, sign*self.region.a+r, 0, 0]
                plus, minus = self.region.cap_masks([point])
                self.assertEqual(bool(plus[0]), sign == 1)
                self.assertEqual(bool(minus[0]), sign == -1)
        # Exact round Gaussian response on a local tip cap of height delta.
        # Integrate the genuine reduced Jacobian, not the bound itself.
        for rho in (1, 1e4):
            value = 4*math.pi*ACTION_CONSTANT*math.sqrt(rho)*quad(
                lambda r: r*r*quad(lambda t: math.exp(-INTERVAL_CONSTANT*rho*(t*t-r*r)**2),
                                   r, delta)[0], 0, delta)[0]
            self.assertGreater(value, 0)
            self.assertLess(value, 4*math.pi*delta**2)

    def test_invalid_inputs(self):
        for a, b in ((0, 0.1), (1, 0), (0.5, -0.1), (0.5, 0.5), (math.nan, 0), (0.5, math.inf)):
            with self.assertRaises(ValueError):
                TwoTipMixed(a, b)
        for sign, mu in ((0, 0), (True, 0), (1, 2), (-1, math.nan)):
            with self.assertRaises(ValueError):
                self.region.joint_radius(sign, mu)
        for rho, u, order in ((-1, 0.8, 8), (math.nan, 0.8, 8), (1, 0.5, 8),
                              (1, 1, 8), (1, math.inf, 8), (1, 0.8, True), (1, 0.8, 3), (1, 0.8, 4.5)):
            with self.assertRaises(ValueError):
                self.region.central_partners(rho, u, order)
        for points in ([[0, 0]], [[0, math.inf, 0, 0]]):
            with self.assertRaises(ValueError):
                self.region.cap_masks(points)


if __name__ == "__main__":
    unittest.main()
