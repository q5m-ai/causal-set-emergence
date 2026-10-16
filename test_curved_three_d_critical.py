"""Scalar/algebraic adversarial checks, not a complete G-SS action audit."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad, solve_ivp
from scipy.optimize import minimize_scalar

import curved_three_d_critical as c
from curved_three_d_union import aggregate_inverse


class SupportLensTests(unittest.TestCase):
    def test_flat_step_and_cap_collars(self):
        self.assertEqual(c.smooth_switch_jet(0), (0., 0., 0.))
        self.assertEqual(c.smooth_switch_jet(1), (1., 0., 0.))
        self.assertEqual(c.cap_metric_jet(.1, 1., 2.), (.1, 1., 0.))
        self.assertEqual(c.cap_metric_jet(1., 1., 2.), (2., -1., 0.))
        for x in np.linspace(.05, .95, 19):
            value, first, _ = c.smooth_switch_jet(float(x))
            self.assertTrue(0 < value < 1)
            self.assertGreater(first, 0)
            self.assertAlmostEqual(value+c.smooth_switch_jet(1-x)[0], 1.)
        for radius in (.3, 2., 5.):
            for r in np.linspace(.001, 1, 101):
                self.assertGreater(c.cap_metric_jet(float(r), 1., radius)[0], 0)

    def test_support_boundary_and_exact_collar_metric(self):
        a, r, r0, R = s.symbols('a r r0 R', real=True)
        F = s.Function('F')(a)
        n, tangent = s.Matrix([s.cos(a), s.sin(a)]), s.Matrix([-s.sin(a), s.cos(a)])
        p = (r-r0-R-F)*n-s.diff(F, a)*tangent
        pr, pa = p.diff(r), p.diff(a)
        self.assertEqual(s.trigsimp(pr.dot(pr)), 1)
        self.assertEqual(s.trigsimp(pr.dot(pa)), 0)
        expected = r0+R+F+s.diff(F, a, 2)-r
        self.assertEqual(s.simplify(s.trigsimp(pa.dot(pa))-expected**2), 0)

    def test_scalar_curvature_of_angularly_dependent_polar_metric(self):
        r, a = s.symbols('r a', real=True)
        j = s.Function('j')(r, a)
        coordinates = [r, a]
        metric, inverse = s.diag(1, j*j), s.diag(1, j**-2)
        gamma = [[[s.simplify(sum(inverse[i, m]*(s.diff(metric[m, k], coordinates[l])+
                    s.diff(metric[m, l], coordinates[k])-s.diff(metric[k, l], coordinates[m]))
                    for m in range(2))/2) for l in range(2)] for k in range(2)] for i in range(2)]
        # Standard positive Riemannian curvature; the contract's Lorentzian
        # sign conversion gives this same scalar for dt^2-h.
        ricci = s.zeros(2)
        for b in range(2):
            for d in range(2):
                ricci[b, d] = sum(s.diff(gamma[i][d][b], coordinates[i])-
                    s.diff(gamma[i][i][b], coordinates[d])+
                    sum(gamma[i][i][e]*gamma[e][d][b]-gamma[i][d][e]*gamma[e][i][b]
                        for e in range(2)) for i in range(2))
        scalar = s.simplify(sum(inverse[b, d]*ricci[b, d] for b in range(2) for d in range(2)))
        self.assertEqual(s.simplify(scalar+2*s.diff(j, r, 2)/j), 0)

    def test_curvature_integral_and_independent_slab_target(self):
        for boundary_radius in (.3, 2., 5.):
            integral = quad(lambda r: -c.cap_metric_jet(r, 1., boundary_radius)[2],
                            1/3, 2/3, epsabs=1e-10)[0]
            self.assertAlmostEqual(integral, 2., places=9)
            T = 5.
            self.assertAlmostEqual(T*2*math.pi*integral, 4*math.pi*T, places=8)

    def test_actual_boundary_distance_matches_support_minimum(self):
        R, eps = 2., .03
        p = np.array([.04, -.02])

        def data(a):
            return eps*(1-math.cos(3*a)), 3*eps*math.sin(3*a), 9*eps*math.cos(3*a)

        def support(a):
            return R+data(a)[0]+p@np.array([math.cos(a), math.sin(a)])

        def boundary(a):
            return np.linalg.norm(p-c.support_boundary(a, *data(a), R)[0])

        # Finite optimization checks, not certified global distance enclosures.
        edges = np.linspace(-math.pi, math.pi, 73)
        minima = [min(minimize_scalar(f, bounds=(lo, hi), method='bounded',
                      options={'xatol': 1e-13}).fun for lo, hi in zip(edges, edges[1:]))
                  for f in (support, boundary)]
        self.assertAlmostEqual(*minima, places=11)

    def test_fixed_middle_stiffness_is_not_full_endpoint_inverse(self):
        values = [c.proper_stiffness(j, .05, 1., 2.) for j in (0., .001, .01, .1)]
        self.assertEqual(values[0], 0)
        self.assertTrue(all(a < b for a, b in zip(values, values[1:])))
        # k = j_end/(2*(1+C*j_end)): a regular, increasing proper-coordinate
        # transform even though the full endpoint Jacobi value tends to zero.
        j1, j2 = .01, .1
        C1 = (j1/(2*values[2])-1)/j1
        C2 = (j2/(2*values[3])-1)/j2
        self.assertAlmostEqual(C1, C2, places=10)

    def test_cut_jet_uses_the_stationary_equations(self):
        u = s.symbols('u', real=True)
        a, r, speed = (s.Function(name)(u) for name in ('a', 'r', 'speed'))
        theta = u-a
        rules = {s.diff(a, u): -speed, s.diff(r, u): -r*speed*s.cos(theta/2)/s.sin(theta/2)}
        F = -r*(1-s.cos(theta))
        first = s.diff(F, u).subs(rules)
        self.assertEqual(s.trigsimp(s.expand_trig(first+r*s.sin(theta))), 0)
        second = s.diff(-r*s.sin(theta), u).subs(rules)
        self.assertEqual(s.trigsimp(s.factor(second+r*s.cos(theta)-r*speed)), 0)

    def test_global_two_contact_support_inequalities(self):
        lo, hi = 1., 1.5
        speed = lambda u: .1+.04*math.sin(3*u)

        def ode(u, z):
            a, r = z
            return [-speed(u), -r*speed(u)/math.tan((u-a)/2)]

        grid = np.linspace(lo, hi, 61)
        result = solve_ivp(ode, (lo, hi), [.05, .2], t_eval=grid,
                           rtol=2e-12, atol=2e-13)
        self.assertTrue(result.success)
        a, r = result.y
        F = np.array([c.cut_support_jet(u-aa, rr, speed(u))['value']
                      for u, aa, rr in zip(grid, a, r)])
        supporting = -r[:, None]*(1-np.cos(grid[None, :]-a[:, None]))
        defects = F[None, :]-supporting
        self.assertGreaterEqual(defects.min(), -2e-12)
        np.testing.assert_allclose(np.diag(defects), 0, atol=1e-14)
        for u, aa, rr in zip(grid, a, r):
            jet = c.cut_support_jet(u-aa, rr, speed(u))
            self.assertAlmostEqual((jet['second']+rr*math.cos(u-aa))/2,
                                   jet['secondary'])

    def test_singular_curvature_weight_is_positive(self):
        a = s.symbols('a', real=True)
        k, u = s.Function('k')(a), s.Function('u')(a)
        derivative = s.diff(k*s.cos((u-a)/2)/s.sin((u-a)/2), a)
        # Expand first: u' also occurs inside the (u'-1) factor.
        coefficient = s.simplify(s.expand(derivative).coeff(s.diff(u, a)))
        self.assertEqual(s.trigsimp(coefficient+k/(2*s.sin((u-a)/2)**2)), 0)
        for theta in (.4, 1., 2.5):
            self.assertGreater(c.cut_support_jet(theta, .2, 0)['singular_weight'], 0)

    def test_cantor_concentration_control_retains_physical_weight(self):
        # Finite residual sets/floors diagnose concentration; the note proves
        # the infinite smooth Cantor construction, not this finite test.
        weight = c.cut_support_jet(1.2, .2, 0)['singular_weight']
        for level in range(1, 9):
            residual = .5+2**(-level-1)
            for floor in (1e-2, 1e-4, 1e-6):
                image_length = floor*residual
                curvature_density = weight/floor
                self.assertAlmostEqual(image_length*curvature_density, weight*residual)
                self.assertGreaterEqual(weight*residual, weight/2)


class CriticalBudgetTests(unittest.TestCase):
    def test_equal_minimum_factorization_and_quartic_dichotomy(self):
        z, d, g0, g1, g2 = s.symbols('z d g0 g1 g2', real=True)
        G = g0+g1*z+g2*z*z/2
        D = z*z*(z-d)**2*G
        self.assertEqual(s.diff(D, z, 2).subs(z, 0)/2, d*d*g0)
        self.assertEqual(s.expand(s.diff(D, z, 4).subs(z, 0)/24),
                         g0-2*d*g1+d*d*g2/2)
        self.assertEqual(s.simplify(s.diff(D, z, 2).subs(z, d)/2-d*d*G.subs(z, d)), 0)

    def test_reciprocal_cut_measure_cancels_soft_denominator(self):
        stiff, soft, P, theta = s.symbols('stiff soft P theta', positive=True)
        head = theta*soft**s.Rational(3, 2)/(s.sqrt(P)*stiff**s.Rational(1, 3))
        coefficient = stiff**s.Rational(5, 3)/theta**2
        budget = coefficient/s.sqrt(head)*soft/stiff
        expected = stiff**s.Rational(5, 6)*soft**s.Rational(1, 4)*P**s.Rational(1, 4)/theta**s.Rational(5, 2)
        self.assertEqual(s.simplify(budget-expected), 0)
        for soft_value in (.1, .01, 1e-4):
            h, b = c.two_state_head_and_budget(.2, soft_value, .3, .5)
            self.assertAlmostEqual(b/(.2**(5/3)/.5**2/h**.5*soft_value/.2), 1.)

    def test_quartic_and_flat_budget_powers(self):
        for d in (.1, .03, .01):
            q = .7
            k = d*d*q
            _, quartic = c.two_state_head_and_budget(k, k, q, d)
            self.assertAlmostEqual(quartic/(k**(-1/6)*q**1.5), 1.)
            _, flat = c.two_state_head_and_budget(d**4, d**6, d*d, d)
            self.assertAlmostEqual(flat/d**(17/6), 1.)

    def test_three_gap_jacobian_has_all_three_chords(self):
        for a, b, c0 in ((0., .2, .3), (-.1, .01, .8), (0., 1., 2.)):
            normals = np.array([[math.cos(t), math.sin(t)] for t in (a, b, c0)])
            determinant = abs(np.linalg.det(np.array([normals[1]-normals[0], normals[2]-normals[0]])))
            product = np.linalg.norm(normals[1]-normals[0])*np.linalg.norm(normals[2]-normals[0])*np.linalg.norm(normals[2]-normals[1])/2
            self.assertAlmostEqual(determinant, product, places=14)

    def test_three_realizable_equal_minima_cannot_be_dropped_pointwise(self):
        eps = .03
        for angle in (0., 2*math.pi/3, 4*math.pi/3):
            self.assertAlmostEqual(eps*(1-math.cos(3*angle)), 0.)
            self.assertGreater(9*eps*math.cos(3*angle)/2, 0)
        # Symmetry makes the three physical leading amplitudes equal. Absorb
        # their common factor only in this inverse diagnostic.
        for count in (3, 8, 32):
            phase = .02
            aggregate = aggregate_inverse(phase, np.zeros(count), np.ones(count))
            proxy = c.two_state_proxy(phase, np.zeros(count), np.ones(count))
            self.assertAlmostEqual((proxy-aggregate)/phase, 2**(-2/3)-count**(-2/3))
            self.assertGreater(proxy, aggregate)

    def test_signed_moments_do_not_supply_an_extra_half_order(self):
        self.assertAlmostEqual(c.ramp_kernel_moment(2), 0., places=13)
        self.assertAlmostEqual(c.ramp_kernel_moment(3), 0., places=13)
        self.assertNotEqual(c.ramp_kernel_moment(3.5), 0.)
        step = 1e-5
        derivative = (c.ramp_kernel_moment(3+step)-c.ramp_kernel_moment(3-step))/(2*step)
        self.assertAlmostEqual(derivative, 2*math.gamma(4/3), places=8)
        self.assertGreater(c.ramp_kernel_moment(3.25), 0)

    def test_invalid_inputs(self):
        cases = [lambda: c.smooth_switch_jet(float('nan')),
                 lambda: c.cap_metric_jet(.2, 0, 2),
                 lambda: c.cap_metric_jet(2, 1, 2),
                 lambda: c.support_boundary(0, -2, 0, 0, 1),
                 lambda: c.proper_stiffness(.1, 0, 1, 2),
                 lambda: c.proper_stiffness(2, .1, 1, 2),
                 lambda: c.cut_support_jet(0, .2, .1),
                 lambda: c.cut_support_jet(1, .2, -.1),
                 lambda: c.two_state_head_and_budget(.1, .2, .3, .4),
                 lambda: c.ramp_kernel_moment(1),
                 lambda: c.two_state_proxy(.1, [0, 1], [1, -1])]
        for case in cases:
            with self.assertRaises(ValueError):
                case()


if __name__ == '__main__':
    unittest.main()
