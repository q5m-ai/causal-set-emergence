"""Adversarial finite CT diagnostics, not proof certificates or human review."""

import math
import unittest

import numpy as np
from scipy.optimize import brentq, root
import sympy as sp

from conformal_two_tip import (TwoTipConformal, _lens_coordinates, _sobol,
                               axial_generator_terms, complete_action, field,
                               future_pairs, lens_target, residue_diagnostic,
                               short_amplitude, source_pairs)
from geometric_cancellation import conformal_diamond_factor
from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT


class ConformalTwoTipTests(unittest.TestCase):
    def test_actual_nonaxial_floor_joint_and_crease_ranks(self):
        model = TwoTipConformal()
        for theta in np.linspace(0, 2*np.pi, 23, endpoint=False):
            direction = np.array([0., np.cos(theta), np.sin(theta)])
            radius = brentq(lambda r: float(model.floor(r*direction))-np.hypot(model.a, r), 0, 2)
            x = radius*direction
            grad = model.gradient(x)[1:]-x[1:]/np.hypot(model.a, radius)
            self.assertGreater(np.linalg.norm(grad), .7)
            # Three independent physical conormals, not null-generator rank.
            normals = []
            for sign in (1, -1):
                vec = x-np.array([sign*model.a, 0., 0.])
                normals.append(np.r_[1, vec/np.linalg.norm(vec)])
            normals.append(np.r_[1, model.gradient(x)])
            self.assertEqual(np.linalg.matrix_rank(normals), 3)
        self.assertNotEqual(model.floor(np.array([.2, .3, 0.])), model.floor(np.array([.2, -.3, 0.])))

    def test_whole_weighted_interval_against_independent_interior_cubature(self):
        model = TwoTipConformal()
        p, n = np.array([-.9, .1, -.2, .08]), np.array([2., 1., -2.])/3
        for sigma in (0., 1e-8, .1):
            radius = .3
            q = p+np.r_[np.sqrt(radius*radius+sigma), radius*n]
            actual = conformal_diamond_factor(
                p, radius, n, sigma,
                lambda t, x: model.density(np.column_stack((t, x))), 12)
            self.assertAlmostEqual(actual, INTERVAL_CONSTANT*model.interval_factor(p, q), delta=2e-12)
            self.assertGreater(abs(model.interval_factor(p, q)-model.density(p)), .05)

    def test_translated_floor_can_be_tangent_to_crease_but_phase_floor_inverse_survives(self):
        model = TwoTipConformal()
        w0 = brentq(lambda w: model.transverse*np.cos(w)-w/np.hypot(model.a, w), 0, .2, xtol=1e-15)
        depth = np.hypot(model.a, w0)
        ell0 = brentq(lambda ell: model.floor(np.array([-ell, w0, 0.]))-ell-depth, .1, 1)
        q = np.array([-depth, 0., w0, 0.])
        n = np.array([1., 0., 0.])
        self.assertAlmostEqual(model.transverse*np.cos(w0)-w0/depth, 0, places=13)
        # This is an actual long translated closing contact, not the original Gamma.
        self.assertGreater(ell0, .3)
        def coordinates(values):
            ell, xi = values
            p = q-np.r_[ell, ell*np.sqrt(1-xi)*n]
            r = p[0]+model.floor(p[1:])
            h = model.interval_factor(p, q)
            return np.array([r, ell*ell*xi*np.sqrt(h)])
        h0 = model.interval_factor(q-np.r_[ell0, ell0*n], q)
        determinant = (-1-model.axial*np.cos(ell0))*ell0**2*np.sqrt(h0)
        self.assertLess(determinant, -.2)
        for physical_w in (1e-5, 1e-4, 1e-3):
            solution = root(lambda v: coordinates(v)-[0, physical_w], [ell0, physical_w/(ell0**2*np.sqrt(h0))])
            self.assertTrue(solution.success)
            np.testing.assert_allclose(coordinates(solution.x), [0, physical_w], atol=1e-10)
        # The invalid spacelike-to-generator argument remains invalid.
        omega = np.array([1., 0., 0.])
        self.assertEqual(np.r_[1, omega]@np.r_[1, -omega], 0)

    def test_actual_lens_clock_domain_and_moving_floor(self):
        model, s = TwoTipConformal(), _sobol(12, 6).copy()
        direction = np.broadcast_to(np.array([.4, -.3, .2]), (len(s), 3))
        # At upper clock endpoint the SOURCE floor, not the target floor, closes.
        s[:, 3] = 1
        q, jac = _lens_coordinates(model, s, .02, direction)
        p = q-np.column_stack((np.full(len(s), .02), .02*direction))
        np.testing.assert_allclose(p[:, 0]+model.floor(p[:, 1:]), 0, atol=1e-14)
        rp, rm = model.radii(q[:, 1:])
        self.assertTrue(np.all(-q[:, 0] >= np.maximum(rp, rm)-1e-14))
        self.assertTrue(np.all(jac > 0))
        self.assertGreater(np.max(q[:, 0]+model.floor(q[:, 1:])), .01)

    def test_flat_lens_volume_and_independent_screen_area_calibration(self):
        m = TwoTipConformal(axial=0, transverse=0, bt=0, bx=0)
        _, jac = _lens_coordinates(m, _sobol(17, 4))
        # Spatial ball-intersection volume integrated over the physical clock.
        expected_volume = np.pi/3*(m.T-m.a)**3*(m.T+m.a)
        self.assertAlmostEqual(jac.mean(), expected_volume, delta=3e-7)
        bulk, joint = lens_target(m, 17)
        self.assertEqual(bulk, 0)
        self.assertAlmostEqual(joint, 4*np.pi*m.T*(m.T-m.a), delta=5e-4)
        self.assertAlmostEqual(residue_diagnostic(m, power=15), joint, delta=7e-4)

    def test_complete_nonaxial_actions_two_independent_pair_domains(self):
        model = TwoTipConformal()
        for region in ('lens', 'union'):
            future = complete_action(model, 2, region, 17)
            source = complete_action(model, 2, region, 17, 'source')
            np.testing.assert_allclose(future, source, atol=.0015, rtol=0)
            self.assertGreater(future.sum(), 1)
        bulk, joint = lens_target(model, 17)
        self.assertLess(bulk, -.05)
        self.assertGreater(joint, 10)
        self.assertGreater(abs(complete_action(model, 2, power=17).sum()-bulk-joint), 5)

    def test_refined_full_pair_domains_not_a_target_evaluator(self):
        model = TwoTipConformal()
        f = complete_action(model, .25, 'union', 18)
        s = complete_action(model, .25, 'union', 18, 'source')
        np.testing.assert_allclose(f, s, atol=.00025, rtol=0)
        self.assertGreater(abs(f.sum()-complete_action(model, 2, 'union', 17).sum()), 1)

    def test_weighted_physical_valuation_retains_common_to_exclusive_pairs(self):
        model, rho = TwoTipConformal(), .5
        results = {v: source_pairs(model, rho, v, 17) for v in ('lens', 'union', 'plus', 'minus')}
        # Different source-time maps make these independent cubature checks,
        # not pointwise arithmetic of one constructed union response.
        point_residual = results['union'][0]+results['lens'][0]-results['plus'][0]-results['minus'][0]
        pair_residual = results['union'][1]+results['lens'][1]-results['plus'][1]-results['minus'][1]
        self.assertLess(abs(point_residual).max(), .0002)
        self.assertLess(abs(pair_residual).max(), .001)
        self.assertGreater(abs(results['plus'][1].sum()-results['lens'][1].sum()), .02)
        omitted_lens = results['plus'][1].sum()+results['minus'][1].sum()-results['union'][1].sum()
        self.assertGreater(abs(omitted_lens), .001)
        self.assertAlmostEqual(omitted_lens, results['lens'][1].sum(), delta=.001)

    def test_full_ordered_partitions_temporal_complements_and_point_once(self):
        model, rho = TwoTipConformal(), .5
        point, short, long = future_pairs(model, rho, 'union', 17, cutoff=.2)
        point0, whole, empty = future_pairs(model, rho, 'union', 17)
        np.testing.assert_allclose(point, point0, atol=0)
        np.testing.assert_allclose(short+long, whole, atol=1e-14)
        self.assertEqual(empty.sum(), 0)
        self.assertGreater(abs(short.sum()), .001)
        self.assertGreater(abs(long.sum()), .01)
        self.assertGreater(abs(whole[0, 1]), .01)
        self.assertGreater(abs(whole[1, 0]), .01)
        action = ACTION_CONSTANT*np.sqrt(rho)*(point-rho*(short+long))
        self.assertGreater(abs(action.sum()-np.trace(action)), .2)
        wrong_point = ACTION_CONSTANT*np.sqrt(rho)*(4*point.sum()-rho*whole.sum())
        self.assertGreater(abs(wrong_point-action.sum()), 1)

    def test_actual_nonaxial_moving_floor_residue_and_independent_target(self):
        model = TwoTipConformal()
        target = sum(lens_target(model, 19))
        low = residue_diagnostic(model, power=15)
        high = residue_diagnostic(model, power=17)
        self.assertAlmostEqual(high, target, delta=.0002)
        self.assertLess(abs(high-target), abs(low-target))
        self.assertAlmostEqual(residue_diagnostic(model, step=.007, power=17), high, delta=2e-7)

    def test_weighted_generator_and_nonzero_crease_endpoints(self):
        model = TwoTipConformal(transverse=0)
        bulk, joint, generator, crease = axial_generator_terms(model)
        actual = residue_diagnostic(model, power=17, source_field=lambda p: p[:, 0])
        self.assertGreater(abs(crease), 2)
        self.assertGreater(abs(generator), 2)
        self.assertAlmostEqual(actual, bulk+joint+generator, delta=.0005)
        self.assertGreater(abs(actual-(bulk+joint)), 2)

    def test_matched_mellin_algebra_and_actual_corner_jacobian(self):
        s, xi = sp.symbols('s xi')
        mult = (1-2*s)*(1-s)*(1-2*s/3)
        self.assertEqual(sp.expand(mult-(1-9*s+8*s*(s+1)-4*s*(s+1)*(s+2)/3)), 0)
        beta = sp.gamma(1-2*s)*sp.gamma(sp.Rational(3, 2))/sp.gamma(sp.Rational(5, 2)-2*s)
        self.assertEqual(sp.limit(beta, s, sp.Rational(5, 4)), 0)
        X, Y, Z = sp.symbols('X Y Z')
        coefficient = sp.series(sp.sqrt(1-xi)*(X+(1-xi)*Y/3+xi*Z), xi, 0, 3).removeO().expand().coeff(xi, 2)
        self.assertEqual(coefficient, (-X+Y-4*Z)/8)
        self.assertEqual(sp.simplify((4/sp.sqrt(6))*sp.pi**sp.Rational(3, 2)/(12*(sp.pi/24)**sp.Rational(3, 2))), 16)
        a, y, z = sp.symbols('a y z', positive=True)
        r = sp.sqrt(a*a+y*y+z*z)
        gram = sp.eye(2)-sp.Matrix([y, z])*sp.Matrix([[y, z]])/(r*r)
        self.assertEqual(sp.simplify(gram.det()), a*a/(r*r))

    def test_invalid_inputs_are_not_silent_zero_observables(self):
        for kwargs in ({'a': 0}, {'T': .7}, {'bt': -1}, {'transverse': .4}, {'bx': math.nan}):
            with self.assertRaises(ValueError):
                TwoTipConformal(**kwargs)
        model = TwoTipConformal()
        for rho in (0, -1, math.inf, math.nan):
            with self.assertRaises(ValueError):
                complete_action(model, rho)
        for region in ('', 'target'):
            with self.assertRaises(ValueError):
                source_pairs(model, 1, region)
        with self.assertRaises(ValueError):
            complete_action(model, 1, method='target')
        for cutoff in (0, -.1, math.inf):
            with self.assertRaises(ValueError):
                future_pairs(model, 1, cutoff=cutoff)
        for step in (0, -.1, .5, math.inf):
            with self.assertRaises(ValueError):
                residue_diagnostic(model, step=step)
        with self.assertRaises(ValueError):
            short_amplitude(model, 0, 1.1)
        with self.assertRaises(ValueError):
            model.interval_factor([0, 0, 0, 0], [1, 2, 0, 0])
        with self.assertRaises(ValueError):
            axial_generator_terms(model)


if __name__ == '__main__':
    unittest.main()
