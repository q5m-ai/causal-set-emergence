"""Finite geometric/algebraic diagnostics, NOT certification of theorem HO-4."""

import unittest

import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad, solve_ivp

from hadamard_optical import (
    independent_target, optical_volume, reference_factor, spatial_distance,
    surface_distance, surface_geodesic, tube_radius_squared,
)


class HadamardOpticalTests(unittest.TestCase):
    def test_whole_ellipsoid_envelope_including_both_caps(self):
        for length in (.1, 1., 7.):
            for excess in (1e-6, .03, .5):
                for fraction in np.linspace(.001, .999, 21):
                    s = -excess/2+(length+excess)*fraction
                    r2 = tube_radius_squared(length, excess, s)
                    broken = np.hypot(s, np.sqrt(r2))+np.hypot(length-s, np.sqrt(r2))
                    self.assertAlmostEqual(broken, length+excess, places=12)
                    # Both clock bounds lie in s <= t <= s+e, even outside [0,L].
                    self.assertGreaterEqual(np.hypot(s, np.sqrt(r2))-s, -1e-13)
                    self.assertLessEqual(length+excess-np.hypot(length-s, np.sqrt(r2))-s,
                                         excess+1e-13)
                self.assertGreater(tube_radius_squared(length, excess, -excess/4), 0)
                self.assertGreater(tube_radius_squared(length, excess, length+excess/4), 0)

    def test_tip_scale_is_e_not_sqrt_e(self):
        for excess in (1e-2, 1e-4, 1e-6):
            for s in (-excess/4, excess/2, 1-excess/2, 1+excess/4):
                self.assertLess(tube_radius_squared(1., excess, s), 3*excess**2)
        # Central-only s(L-s) would falsely remove these positive cap widths.
        self.assertLess((-1e-3)*(1+1e-3), 0)
        self.assertGreater(tube_radius_squared(1., .01, -1e-3), 0)

    def test_comparison_algebra_not_just_sampled_inequality(self):
        L, e, s = sp.symbols('L e s', positive=True)
        r2 = e*(2*L+e)*(s+e/2)*(L+e/2-s)/(L+e)**2
        a2, b2, tau = s*s+r2, (L-s)**2+r2, L+e
        self.assertEqual(sp.factor((tau*tau-a2-b2)**2-4*a2*b2), 0)

    def test_actual_nonlinear_geodesic_and_metric_speed(self):
        p, q, k = np.array([-.3, -.2]), np.array([.9, .4]), .7
        sol = surface_geodesic(p, q, k, tolerance=1e-10)
        u = np.linspace(0, 1, 101)
        x, y, vx, vy = sol.sol(u)
        speed2 = vx*vx+(1+k*x*x)**2*vy*vy
        self.assertLess(np.ptp(speed2), 2e-9)
        np.testing.assert_allclose(sol.sol(0)[:2], p, atol=1e-13)
        np.testing.assert_allclose(sol.sol(1)[:2], q, atol=1e-13)
        # This is not the straight-coordinate or frozen-metric path.
        self.assertGreater(np.max(np.abs(x-(p[0]+u*(q[0]-p[0])))), .003)
        distance = surface_distance(p, q, k)
        self.assertGreater(distance, np.linalg.norm(q-p))
        straight = quad(lambda t: np.hypot(q[0]-p[0],
                        (1+k*(p[0]+t*(q[0]-p[0]))**2)*(q[1]-p[1])), 0, 1)[0]
        self.assertLess(distance, straight)
        self.assertAlmostEqual(distance, surface_distance(q, p, k), places=9)
        self.assertAlmostEqual(spatial_distance([*p, -.2], [*q, .5], k),
                               np.hypot(distance, .7), places=9)

    def test_turning_path_at_longitudinal_tip_is_not_excluded(self):
        sol = surface_geodesic([.7, 0], [.7, .2], .6, tolerance=1e-10)
        mid = sol.sol(.5)
        self.assertLess(mid[0], .7)
        self.assertAlmostEqual(mid[2], 0., places=8)
        # A monotone-x shooting solver would miss this actual minimizing path.
        self.assertLess(surface_distance([.7, 0], [.7, .2], .6), (1+.6*.7**2)*.2)

    def test_exact_rescaled_metric_and_actual_jacobian(self):
        s, v, y, z, eta, k = sp.symbols('s v y z eta k', real=True)
        coords = sp.Matrix([s+eta**2*v, s, eta*y, eta*z])
        jac = coords.jacobian([s, v, y, z])
        metric = sp.diag(1, -1, -(1+k*s*s)**2, -1)
        pulled = sp.simplify(jac.T*metric*jac/eta**2)
        expected = sp.Matrix([[0, 1, 0, 0], [1, eta**2, 0, 0],
                              [0, 0, -(1+k*s*s)**2, 0], [0, 0, 0, -1]])
        self.assertEqual(pulled, expected)
        self.assertEqual(sp.expand(jac.det()**2), eta**8)
        self.assertEqual(sp.factor(pulled.det()), -(1+k*s*s)**2)

    def test_noncommuting_defocusing_jacobi_frame(self):
        def matrix(s):
            c, t = np.cos(.8*s), np.sin(.8*s)
            r = np.array([[c, -t], [t, c]])
            return r@np.diag([.2+.1*np.sin(s)**2, 1.1+.2*np.cos(s)**2])@r.T

        def ode(s, state):
            b, bp = state[:4].reshape(2, 2), state[4:].reshape(2, 2)
            return np.r_[bp.ravel(), (matrix(s)@b).ravel()]

        sol = solve_ivp(ode, [0, 2], np.r_[np.eye(2).ravel(), np.zeros(4)],
                        rtol=2e-11, atol=1e-12, dense_output=True)
        self.assertTrue(sol.success)
        frames = []
        for s in np.linspace(0, 2, 17):
            state = sol.sol(s)
            b, bp = state[:4].reshape(2, 2), state[4:].reshape(2, 2)
            self.assertGreaterEqual(np.linalg.svd(b, compute_uv=False).min(), 1-1e-10)
            np.testing.assert_allclose(b.T@bp, bp.T@b, atol=2e-10)
            # Cancellation of the ds^2 term in the Rosen transformation.
            bpp = matrix(s)@b
            np.testing.assert_allclose((bp.T@bp+b.T@bpp)-bp.T@bp-b.T@matrix(s)@b,
                                       np.zeros((2, 2)), atol=1e-13)
            frames.append(b.T@b)
        self.assertGreater(np.linalg.norm(frames[5]@frames[-1]-frames[-1]@frames[5]), .1)

    def test_vertical_reference_generator_and_cone_seam_rank(self):
        # For A=0, reference g0=2 ds dv-|dZ|^2. The seam includes s=0,L,
        # but neither is an apex of these timelike-separated two cones.
        length = 1.3
        for s, v, y in [(0., 1., 0.), (length, 0., 0.),
                         (length/2, .5, np.sqrt(length/2))]:
            forward = np.array([2*v, 2*s, -2*y, 0.])
            backward = np.array([-2*(1-v), -2*(length-s), -2*y, 0.])
            self.assertEqual(np.linalg.matrix_rank([forward, backward]), 2)
        self.assertGreater(np.linalg.norm(np.array([2., 0., 0., 0.])), 0)

    def test_actual_clock_flat_calibration_with_nonzero_caps(self):
        length, e = 1., .06
        pieces = optical_volume(.2, length, e, 0., order=18, return_parts=True)
        exact = np.pi/24*(e*(2*length+e))**2
        self.assertLess(abs(sum(pieces)/exact-1), 4e-7)
        self.assertGreater(min(pieces), 0)
        self.assertAlmostEqual(pieces[0], pieces[2], places=14)
        self.assertGreater(abs(pieces[1]/exact-1), 1e-3)

    def test_variable_curvature_whole_volume_and_near_null_reference(self):
        leading = reference_factor(.2, 1., .6)
        results = [optical_volume(.2, 1., e, .6, order=12)/e**2
                   for e in (.08, .04, .02)]
        self.assertGreater(abs(leading-np.pi/6), .01)
        self.assertGreater(results[0], results[1])
        self.assertGreater(results[1], results[2])
        # Richardson differences are finite diagnostics, not a smoothness proof.
        first, second = 2*results[1]-results[0], 2*results[2]-results[1]
        self.assertLess(abs(second-leading), abs(first-leading)/2)
        self.assertLess(abs(second-leading), 2e-4)
        refined = optical_volume(.2, 1., .04, .6, order=18)/.04**2
        self.assertLess(abs(refined-results[1]), 1e-6)
        # Original metric is NOT its exact quadratic reference at finite e.
        self.assertGreater(abs(refined-leading), .015)

    def test_variable_caps_retained_and_different(self):
        pieces = optical_volume(.2, 1., .05, .6, order=12, return_parts=True)
        self.assertGreater(pieces[0], 0.)
        self.assertGreater(pieces[2], 0.)
        self.assertGreater(abs(pieces[0]-pieces[2]), 1e-8)
        self.assertGreater(sum(pieces), pieces[1])

    def test_variable_scalar_curvature_and_nonconformal_control(self):
        x, k = sp.symbols('x k', real=True, positive=True)
        a = 1+k*x*x
        gaussian = -sp.diff(a, x, 2)/a
        self.assertEqual(gaussian, -2*k/a)
        self.assertNotEqual(sp.diff(gaussian, x), 0)
        # Product curvature contractions: Riem^2=4K^2, Ric^2=2K^2, R=2K.
        self.assertEqual(sp.simplify(4*gaussian**2-2*2*gaussian**2
                                    +(2*gaussian)**2/3), 4*gaussian**2/3)

    def test_independent_bulk_and_joint_gram_not_fitted_action(self):
        k, s, eps = .7, .3, .2
        volume, bulk, joint = independent_target(k, s, eps)
        # Separate radial/angular integration of the actual spatial density.
        vref = quad(lambda r: 4*np.pi*r*r*s*(1-r*r)*(1+k*r*r/3), 0, 1)[0]
        bref = quad(lambda r: -8*np.pi*k*s*r*r*(1-r*r), 0, 1)[0]
        self.assertAlmostEqual(volume, vref, places=12)
        self.assertAlmostEqual(bulk, bref, places=12)
        nodes, weights = leggauss(32)
        total, angles = 0., []
        for x, wx in zip(nodes, weights):
            a = 1+k*x*x
            metric = np.diag([1., a*a, 1.])
            inv = np.linalg.inv(metric)
            for phi in np.linspace(0, 2*np.pi, 64, endpoint=False):
                r = np.sqrt(1-x*x)
                pos = np.array([x, r*np.cos(phi), r*np.sin(phi)])
                tangent1 = np.array([1., -x/r*np.cos(phi), -x/r*np.sin(phi)])
                tangent2 = np.array([0., -r*np.sin(phi), r*np.cos(phi)])
                tangents = np.array([tangent1, tangent2])
                induced = metric-np.diag([0., 0., eps*eps])
                area = np.sqrt(np.linalg.det(tangents@induced@tangents.T))
                slopes = [np.array([0., 0., eps])+sign*s*pos for sign in (-1, 1)]
                norms = [1-p@inv@p for p in slopes]
                c = (1-slopes[0]@inv@slopes[1])/np.sqrt(norms[0]*norms[1])
                coth = c/np.sqrt(c*c-1)
                angles.append(coth)
                total += wx*2*np.pi/64*coth*area
        self.assertAlmostEqual(total, joint, places=10)
        self.assertGreater(np.ptp(angles), .03)
        self.assertLess(bulk, 0.)
        self.assertGreater(abs(joint-independent_target(0., s, eps)[2]), 1.)

    def test_nonempty_joint_envelope_containment_and_shell_rank(self):
        s, eps = .3, .2
        # Use an actual causal chain: speed in h is 1 on the x axis.
        x0, x1 = -.1, .1
        floor = lambda x: -s*(1-x*x)/2
        ceiling = lambda x: s*(1-x*x)/2
        self.assertLess(floor(x0), -.12)
        self.assertLess(.12, ceiling(x1))
        for t in np.linspace(-.12, .12, 31):
            x = x0+(x1-x0)*(t+.12)/.24
            self.assertLess(floor(x), t)
            self.assertLess(t, ceiling(x))
        # At the joint x=(1,0,0), independent face conormals and shell.
        minus = np.array([1., -s, 0., -eps])
        plus = np.array([1., s, 0., -eps])
        for n in ([1., 0., 0.], [-1., 0., 0.], [0., 1., 0.]):
            null = np.r_[1., n]
            rows = [np.r_[minus, 0.], np.r_[plus, plus@null], np.r_[np.zeros(4), 1.]]
            self.assertEqual(np.linalg.matrix_rank(rows), 3)
        self.assertGreater(1-s-eps, 0.)

    def test_signed_moments_and_critical_remainder_normalization(self):
        z = sp.symbols('z', positive=True)
        kernel = (1-9*z*z+8*z**4-sp.Rational(4, 3)*z**6)*sp.exp(-z*z)
        for j in range(3):
            self.assertEqual(sp.integrate(z**j*kernel, (z, 0, sp.oo)), 0)
        self.assertEqual(sp.integrate(z**3*kernel, (z, 0, sp.oo)), -sp.Rational(1, 2))
        # rho^(3/2) * dw * w^3 with z=sqrt(rho)w is rho^(-1/2).
        rho = sp.symbols('rho', positive=True)
        self.assertEqual(sp.simplify(rho**sp.Rational(3, 2)
                         *rho**(-sp.Rational(1, 2))*rho**(-sp.Rational(3, 2))),
                         1/sp.sqrt(rho))

    def test_actual_finite_pair_partition_and_cutoff_accounting(self):
        # Finite weighted quadrature atoms, not a purported full-action solver.
        # All phases below come from physical nonlinear clock integration.
        rho, beta = 23., 4/np.sqrt(6)
        data = [(-.2, .2, .03, .7), (.1, .35, .05, .7)]
        phases = np.array([optical_volume(x, L, e, k, order=8) for x, L, e, k in data])
        measures = np.array([(1+k*x*x)*(1+k*(x+L)**2) for x, L, e, k in data])
        gaps = np.array([L+e for x, L, e, k in data])
        v = rho*phases
        kernel = (1-9*v+8*v*v-4/3*v**3)*np.exp(-v)
        pair = measures*kernel
        # Distinct endpoint fields, both partitions and all four ordered terms.
        source = np.array([.2, .7])
        target = np.array([.6, .3])
        terms = [pair*a*b for a in (source, 1-source) for b in (target, 1-target)]
        np.testing.assert_allclose(sum(terms), pair, atol=1e-15)
        self.assertGreater(np.linalg.norm(terms[1]+terms[2]), .01)
        point_mass = .37
        full = beta*np.sqrt(rho)*point_mass-beta*rho**1.5*pair.sum()
        for delta in (.1, gaps[0], .3, .6):
            short = beta*np.sqrt(rho)*point_mass-beta*rho**1.5*pair[gaps < delta].sum()
            long = -beta*rho**1.5*pair[gaps >= delta].sum()
            self.assertAlmostEqual(full, short+long, places=11)
        self.assertTrue((gaps >= gaps[0])[0])  # Equality is long.

    def test_invalid_diagnostic_data_fail_explicitly(self):
        for args in [(0., .1, 0.), (1., -.1, 0.), (1., .1, np.nan)]:
            with self.assertRaises(ValueError):
                tube_radius_squared(*args)
        for args in [(.1, 1., 0., .5), (.1, -1., .1, .5), (.1, 1., .1, -.5)]:
            with self.assertRaises(ValueError):
                optical_volume(*args)
        with self.assertRaises(ValueError):
            surface_distance([0, 0], [1, np.nan], .2)
        with self.assertRaises(ValueError):
            independent_target(.2, .8, .3)


if __name__ == '__main__':
    unittest.main()
