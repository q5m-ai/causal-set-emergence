"""Independent finite regressions for CC1--CC14, not asymptotic certificates."""

import math
import unittest

import numpy as np
import sympy as s

from conformal_cone import (QuadraticCone, complete_action, cone_ball_pairs,
                            partition, point_and_target, residue_target_diagnostic,
                            short_amplitude, source_tip_pairs, _polar_diamond)
from curved_null_contacts import full_action, source_gaussian_mismatch
from geometric_cancellation import conformal_diamond_factor
from mixed_poisson import _unit_rule
from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT


class ConformalConeTests(unittest.TestCase):
    def test_rest_diamond_moments_derive_both_phase_coefficients(self):
        t, r = s.symbols('t r', nonnegative=True)
        volume = 2*s.integrate(4*s.pi*(s.Rational(1, 2)-t)**3/3, (t, 0, s.Rational(1, 2)))
        temporal = 2*s.integrate(4*s.pi*t*t*(s.Rational(1, 2)-t)**3/3, (t, 0, s.Rational(1, 2)))
        spatial = 2*s.integrate(4*s.pi*(s.Rational(1, 2)-t)**5/15, (t, 0, s.Rational(1, 2)))
        self.assertEqual(volume, s.pi/24)
        self.assertEqual(temporal/volume, s.Rational(1, 60))
        self.assertEqual(spatial/volume, s.Rational(1, 30))
        # mean displacement^a displacement^b = 3 u^a u^b/10 - xi eta^ab/30
        self.assertEqual(s.Rational(1, 4)+s.Rational(1, 20), s.Rational(3, 10))

    def test_actual_interval_against_interior_point_cubature(self):
        model = QuadraticCone()
        p = np.array([-0.85, 0.11, -0.09, 0.04])
        n = np.array([2., -1., 2.])/3
        for radius, sigma in ((0.12, 0.18), (0.3, 1e-5), (0.3, 0.0)):
            q = p+np.r_[np.sqrt(radius*radius+sigma), radius*n]
            actual = conformal_diamond_factor(
                p, radius, n, sigma,
                lambda t, x: model.density(t, np.sum(x*x, axis=-1)), order=12)
            predicted = INTERVAL_CONSTANT*model.interval_factor(p, q)
            self.assertAlmostEqual(actual, predicted, delta=2e-12)
        self.assertGreater(abs(float(model.interval_factor(p, q))-model.density(p[0], p[1:]@p[1:])), .05)
        # The prior finite-density counterexample to a weighted Gaussian survives.
        self.assertGreater(source_gaussian_mismatch(.8), 0)

    def test_anisotropic_spacetime_density_and_nonpolynomial_short_jet(self):
        q = np.array([-.55, .1, -.16, .08])
        n = np.array([1., 2., -2.])/3
        covector = np.array([.2, .1, -.07, .03])
        eta = np.diag([1., -1., -1., -1.])
        Q = np.outer([1., .3, -.2, .1], [1., .3, -.2, .1]) + np.diag([0., .1, .2, .3])
        for xi in (0., .2, .9):
            u = np.r_[1, np.sqrt(1-xi)*n]
            gap = .3
            p = q-gap*u
            midpoint = (p+q)/2
            def quadratic(t, x):
                points = np.column_stack((t, x))
                return 1+np.einsum('ni,ij,nj->n', points, Q, points)
            actual = conformal_diamond_factor(p, gap*np.sqrt(1-xi), n, gap*gap*xi, quadratic, 12)/INTERVAL_CONSTANT
            expected = 1+midpoint@Q@midpoint+gap*gap*(u@Q@u)/20-gap*gap*xi*np.trace(Q@eta)/30
            self.assertAlmostEqual(actual, expected, delta=2e-11)
            errors = []
            for gap in (.04, .02):
                p = q-gap*u
                def nonpolynomial(t, x):
                    return 1+np.exp(covector[0]*t+x@covector[1:])
                actual = conformal_diamond_factor(p, gap*np.sqrt(1-xi), n, gap*gap*xi, nonpolynomial, 12)/INTERVAL_CONSTANT
                exponential = np.exp(covector@q)
                prediction = (1+exponential-gap*exponential*(covector@u)/2
                              + gap*gap*exponential*(.15*(covector@u)**2-xi*(covector@eta@covector)/60))
                errors.append(abs(actual-prediction))
            self.assertGreater(errors[0], 6*errors[1])
            self.assertLess(errors[0], 10*errors[1])

    def test_future_ball_domain_retains_null_sheet_floor_contacts_and_tip(self):
        model = QuadraticCone(epsilon=-.23)
        n = np.array([.6, .8, 0.])
        for xi in (0, 1e-9, .4, 1):
            b = np.sqrt(1-xi)
            L = float(model.root(-b*n[0]))
            self.assertAlmostEqual(L, model.floor(-L*b*n[0]), places=14)
            for fraction in (0, .5, 1):
                ell = fraction*L
                for z in (np.array([.3, -.2, .1]), -n, n):
                    U = float(model.root(z[0], ell*b*n[0], ell))
                    self.assertGreaterEqual(U, -1e-14)
                    self.assertAlmostEqual(U+ell, model.floor(U*z[0]-ell*b*n[0]), places=14)
                    self.assertGreaterEqual(1-model.epsilon*np.cos(U*z[0]-ell*b*n[0])*z[0], 1-abs(model.epsilon))
                    q = np.r_[-U, U*z]
                    p = q-np.r_[ell, ell*b*n]
                    self.assertLessEqual(p[0]+np.linalg.norm(p[1:]), 1e-13)
                    self.assertAlmostEqual(p[0]+model.floor(p[1]), 0, places=13)
            self.assertAlmostEqual(float(model.root(.7, L*b*n[0], L)), 0, places=13)
        # The map did not fix the false generator-transversality premise.
        self.assertAlmostEqual(np.r_[1, n]@np.r_[1, -n], 0, places=14)

    def test_source_tip_boost_is_physical_and_has_the_actual_jacobian(self):
        time, longitudinal, transverse, r2, weights = _polar_diamond(6)
        depth, r = .8, .35
        sigma = depth*depth-r*r
        qt = -depth+depth*time+r*longitudinal
        qlong = r*(1-time)-depth*longitudinal
        qspace2 = qlong*qlong+sigma*(r2-longitudinal*longitudinal)
        separation2 = (qlong-r)**2+sigma*(r2-longitudinal*longitudinal)
        self.assertTrue(np.all(qt < 0))
        self.assertTrue(np.all(qt*qt >= qspace2-1e-14))
        self.assertTrue(np.all((qt+depth)**2 >= separation2-1e-14))
        np.testing.assert_allclose((qt+depth)**2-separation2, sigma*(time*time-r2), atol=3e-16)
        self.assertAlmostEqual(float(weights.sum()*sigma*sigma), INTERVAL_CONSTANT*sigma*sigma, places=14)

    def test_kernel_zeros_beta_face_cancellation_and_residue_signs(self):
        z = s.symbols('z')
        multiplier = (1-2*z)*(1-z)*(1-s.Rational(2, 3)*z)
        # Direct Mellin transform of the original polynomial-exponential kernel.
        direct = 1-9*z+8*z*(z+1)-s.Rational(4, 3)*z*(z+1)*(z+2)
        self.assertEqual(s.expand(direct-multiplier), 0)
        for zero in (s.Rational(1, 2), 1, s.Rational(3, 2)):
            self.assertEqual(multiplier.subs(z, zero), 0)
        beta = s.gamma(1-2*z)*s.gamma(s.Rational(3, 2))/s.gamma(s.Rational(5, 2)-2*z)
        self.assertEqual(s.limit(beta, z, s.Rational(5, 4)), 0)
        self.assertEqual(s.diff(multiplier, z).subs(z, 1)*s.gamma(1), s.Rational(1, 3))
        self.assertEqual(s.diff(multiplier, z).subs(z, s.Rational(3, 2))*s.gamma(s.Rational(3, 2)), -s.sqrt(s.pi)/3)
        c, C = s.pi/24, 4/s.sqrt(6)
        # Right contour shift subtracts residues: point response is +mu/rho.
        self.assertEqual(s.simplify(-(-s.pi/(8*c))*s.Rational(1, 3)), 1)
        self.assertEqual(s.simplify(C*s.pi**s.Rational(3, 2)/(12*c**s.Rational(3, 2))), 16)

    def test_critical_coefficient_includes_all_cross_terms(self):
        z, xi, ell = s.symbols('z xi ell')
        a, da, dda, boxa, A, dA, ddA = s.symbols('a da dda boxa A dA ddA', positive=True)
        h1 = -da/2
        h2 = s.Rational(3, 20)*dda-xi*boxa/60
        phase = 1-z*ell*h1/a+ell**2*(-z*h2/a+z*(z+1)*h1*h1/(2*a*a))
        coefficient = s.expand((A-ell*dA+ell*ell*ddA/2)*phase).coeff(ell, 2)
        expected = ddA/2-z*dA*da/(2*a)-3*z*A*dda/(20*a)+z*xi*A*boxa/(60*a)+z*(z+1)*A*da*da/(8*a*a)
        self.assertEqual(s.simplify(coefficient-expected), 0)
        X, Y, Z = s.symbols('X Y Z')
        f2 = s.sqrt(1-xi)*(X+(1-xi)*Y/3+xi*Z)
        self.assertEqual(s.expand(s.series(f2, xi, 0, 3).removeO()).coeff(xi, 2), (-X+Y-4*Z)/8)

    def test_curvature_and_floor_divergence_are_derived_not_fitted(self):
        O, square, box, f, boxf, cross = s.symbols('O square box f boxf cross', positive=True)
        a, boxa, squarea = O**4, 4*O**3*box+12*O**2*square, 16*O**6*square
        expression = (O**2*boxf + s.Rational(1, 2)*O**(-2)*4*O**3*cross
                      + s.Rational(3, 4)*O**(-2)*f*boxa
                      - s.Rational(9, 16)*O**(-6)*f*squarea)
        self.assertEqual(s.expand(expression-(3*O*box*f+O**2*boxf+2*O*cross)), 0)
        # Independently differentiate this diagnostic's nonconstant factor.
        t, x, y, z = s.symbols('t x y z', real=True)
        aa = 1+s.Rational(7, 10)*t*t+s.Rational(1, 5)*(x*x+y*y+z*z)
        omega = aa**s.Rational(1, 4)
        actual = 3*omega*(s.diff(omega, t, 2)-sum(s.diff(omega, u, 2) for u in (x, y, z)))
        numeric = s.lambdify((t, x, y, z), actual, 'numpy')
        self.assertAlmostEqual(float(numeric(-.6, .1, .2, .3)), QuadraticCone().bulk_density(-.6, .14), places=14)

    def test_nonplanar_spacetime_factor_complete_action_two_independent_domains(self):
        model = QuadraticCone()
        point, bulk, joint = point_and_target(model)
        self.assertLess(bulk, -.2)
        self.assertGreater(joint, 17)
        self.assertGreater(abs(float(model.root(1))-float(model.root(-1))), .25)
        for rho in (1, 12):
            low = complete_action(model, rho, 6)
            cone = complete_action(model, rho, 10)
            source = complete_action(model, rho, 10, 'source')
            np.testing.assert_allclose(cone, source, atol=3e-8, rtol=0)
            self.assertLess(np.max(abs(cone-source)), np.max(abs(low-source)))
            # A true complete action, not a target-valued or zero solver.
            self.assertGreater(cone.sum(), 0)
            self.assertGreater(abs(cone.sum()-(bulk+joint)), 1)
            self.assertGreater(abs(cone.sum()-ACTION_CONSTANT*np.sqrt(rho)*point.sum()), .01)

    def test_finite_density_all_ordered_partitions_and_point_once(self):
        model, rho = QuadraticCone(), 3
        point, _, _ = point_and_target(model)
        pairs = cone_ball_pairs(model, rho, 10)
        independent = source_tip_pairs(model, rho, 10)
        np.testing.assert_allclose(pairs, independent, atol=1e-10, rtol=0)
        action = ACTION_CONSTANT*np.sqrt(rho)*(point-rho*pairs)
        self.assertGreater(abs(pairs[0, 1]), .001)
        self.assertGreater(abs(pairs[1, 0]), .001)
        self.assertGreater(abs(action.sum()-np.trace(action)), .1)
        # Allocating a full physical point to every ordered pair is also wrong.
        wrong = ACTION_CONSTANT*np.sqrt(rho)*(4*point.sum()-rho*pairs.sum())
        self.assertGreater(abs(wrong-action.sum()), 10)

    def test_fixed_temporal_cutoff_terms_are_nonzero_and_restore(self):
        model, rho, delta = QuadraticCone(), 3, .17
        whole = cone_ball_pairs(model, rho, 10)
        short = cone_ball_pairs(model, rho, 10, max_gap=delta)
        long = cone_ball_pairs(model, rho, 10, min_gap=delta)
        np.testing.assert_allclose(short+long, whole, atol=2e-10, rtol=0)
        self.assertGreater(abs(short.sum()), 1e-4)
        self.assertGreater(abs(long.sum()), 1e-4)
        self.assertGreater(abs(cone_ball_pairs(model, rho, 8, min_gap=.25).sum()-long.sum()), 1e-4)

    def test_moving_floor_residue_matches_independent_target(self):
        for model in (QuadraticCone(), QuadraticCone(epsilon=-.22, bt=.1, bx=.8)):
            _, bulk, joint = point_and_target(model, 28)
            actual = residue_target_diagnostic(model, order=12)
            refined = residue_target_diagnostic(model, step=.006, order=14)
            self.assertAlmostEqual(actual, bulk+joint, delta=2e-7)
            self.assertAlmostEqual(refined, bulk+joint, delta=2e-7)
            self.assertAlmostEqual(actual, refined, delta=2e-7)

    def test_generator_derivative_and_all_weighted_residues(self):
        model = QuadraticCone()
        nodes, weights = _unit_rule(26)
        bulk, joint, generator = 0., 0., 0.
        for mu, wm in zip(2*nodes-1, 2*weights):
            R = float(model.root(mu))
            r = R*nodes[:, None]
            H = model.floor(r*mu)
            depth = r+(H-r)*nodes[None, :]
            measure = 2*np.pi*wm*R*r*r*(H-r)*weights[:, None]*weights[None, :]
            bulk += np.sum(measure*partition(-depth, r*mu)*model.bulk_density(-depth, r*r))
            joint += 2*np.pi*wm*R*R*np.sqrt(model.density(-R, R*R))*partition(-R, R*mu)
            rr = R*nodes
            derivative = .2*(mu-1)/np.cosh(rr*(mu-1))**2
            generator -= 2*np.pi*wm*R*np.sum(weights*rr*rr*np.sqrt(model.density(-rr, rr*rr))*derivative)
        actual = residue_target_diagnostic(model, order=12, source_field=partition)
        self.assertGreater(abs(generator), .1)
        self.assertAlmostEqual(actual, bulk+joint+generator, delta=3e-7)
        complement = lambda t, x: 1-partition(t, x)
        residues = sum(residue_target_diagnostic(model, order=10, source_field=p, target_field=q)
                       for p in (partition, complement) for q in (partition, complement))
        _, bulk0, joint0 = point_and_target(model)
        self.assertAlmostEqual(residues, bulk0+joint0, delta=3e-7)

    def test_round_time_only_and_flat_are_calibrations(self):
        for bt in (0, 1):
            model = QuadraticCone(epsilon=0, bt=bt, bx=0)
            self.assertAlmostEqual(complete_action(model, 20, 10).sum(), full_action(20, b=bt, order=40), delta=4e-7)
        flat = QuadraticCone(epsilon=0, bt=0, bx=0)
        point, bulk, joint = point_and_target(flat)
        self.assertAlmostEqual(point.sum(), np.pi/3, places=13)
        self.assertEqual(bulk, 0)
        self.assertAlmostEqual(joint, 4*np.pi, places=13)

    def test_bad_inputs_do_not_become_zero_observables(self):
        for kwargs in ({'bt': -1}, {'bx': math.nan}, {'epsilon': .5}, {'T': 0}):
            with self.assertRaises(ValueError):
                QuadraticCone(**kwargs)
        model = QuadraticCone()
        for density in (0, -1, math.inf, math.nan):
            with self.assertRaises(ValueError):
                cone_ball_pairs(model, density)
        with self.assertRaises(ValueError):
            complete_action(model, 1, method='target')
        for lower, upper in ((-1, None), (0, 0), (1, .5)):
            with self.assertRaises(ValueError):
                cone_ball_pairs(model, 1, min_gap=lower, max_gap=upper)
        with self.assertRaises(ValueError):
            model.root(1.01)
        with self.assertRaises(ValueError):
            model.interval_factor([0, 0, 0, 0], [1, 2, 0, 0])
        with self.assertRaises(ValueError):
            short_amplitude(model, .001, -1)
        with self.assertRaises(ValueError):
            residue_target_diagnostic(model, step=0)


if __name__ == '__main__':
    unittest.main()
