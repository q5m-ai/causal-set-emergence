"""Finite cluster-audit regressions, not proof of the universal action limit."""

import math
import unittest

import mpmath as mp
import numpy as np
import sympy as s
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq

import curved_three_d_clusters as c


class FoundationAuditTests(unittest.TestCase):
    def test_variable_scalar_jacobi_wronskian(self):
        rhs = lambda t, y: [y[1], -(1+.2*math.sin(t))*y[0]]
        forward = solve_ivp(rhs, [0, 4], [0, 1], dense_output=True,
                            rtol=2e-12, atol=2e-13)
        focal = brentq(lambda x: forward.sol(x)[0], 2.5, 3.5)
        self.assertGreater(abs(forward.sol(focal)[1]), .5)
        for length in (2., focal):
            backward = solve_ivp(rhs, [length, 0], [0, -1], dense_output=True,
                                 rtol=2e-12, atol=2e-13)
            middle = length/2
            j, jp = forward.sol(middle)
            z, zp = backward.sol(middle)
            self.assertGreater(j*z, .1)
            self.assertAlmostEqual(jp*z-j*zp, forward.sol(length)[0], places=10)

    def test_actual_round_sphere_flat_minimum_has_two_control_rank(self):
        a, X, Y = s.symbols('a X Y', real=True)
        U = s.pi/2+s.acos(X*s.cos(a)+Y*s.sin(a))
        matrix = s.Matrix([[s.diff(U, a, n, p).subs({X: 0, Y: 0})
                            for p in (X, Y)] for n in (1, 2)])
        self.assertEqual(s.simplify(matrix.det()), 1)
        self.assertEqual(s.simplify(U.subs({X: 0, Y: 0})), s.pi)

    def test_actual_clock_scaling_and_k_weight(self):
        k, clock, a = s.symbols('k clock a', positive=True)
        r = 2*clock*k/s.sqrt(1+4*clock**2*k**2)
        p = s.Matrix([r*s.cos(a), r*s.sin(a)])
        det_m = (1+4*clock**2*k**2)**2/clock**2
        self.assertEqual(s.simplify(p.jacobian([a, k]).det()+4*k/det_m), 0)

    def test_negative_quartic_is_not_removed_from_the_true_jet(self):
        u, r = s.symbols('u r', real=True)
        U = s.acos(r*s.cos(u))
        fourth = s.diff(U, u, 4).subs(u, 0)/24
        k = s.symbols('k', positive=True)
        self.assertEqual(s.simplify(fourth.subs(r, 2*k/s.sqrt(1+4*k*k))+
                                    k/12+k**3), 0)

    def test_actual_antipodal_interval_not_a_branch_sum(self):
        # Exact spherical ball intersections at the antipodal pair, including
        # both end intervals. The continuum of minimizing rays is counted once.
        for h in (.01, .2, .7):
            first = quad(lambda t: 2*math.pi*(1-math.cos(t)), 0, h)[0]
            central = quad(lambda t: 2*math.pi*(math.cos(t-h)-math.cos(t)),
                           h, math.pi)[0]
            last = quad(lambda t: 2*math.pi*(1+math.cos(t-h)),
                        math.pi, math.pi+h)[0]
            self.assertAlmostEqual(first+central+last, 4*math.pi*h, places=11)
            self.assertGreater(first+last, 0)


class PhysicalScaleTests(unittest.TestCase):
    def test_projection_annihilates_fifth_jet_not_cubic(self):
        u = s.symbols('u')
        eta = u**3-s.Rational(11, 9)*u**5
        self.assertEqual(s.integrate(u**5*eta, (u, -1, 1)), 0)
        self.assertEqual(s.integrate(u**3*eta, (u, -1, 1)), s.Rational(8, 567))
        for power in (0, 2, 4):
            self.assertEqual(s.integrate(u**power*eta, (u, -1, 1)), 0)

    def test_integrated_negative_part_controls_nonminimum_cubic(self):
        for k in (0., .001, .1):
            for cubic in (-.4, .3):
                for quartic in (-.1, .2):
                    coefficients = [0, 0, k, cubic, quartic, -.07, .5]
                    negative = c.screen_integral(coefficients, 0, .4)
                    bound = c.cubic_negative_part_bound(k, quartic, .5, negative, .4)
                    self.assertLessEqual(abs(cubic), bound)
        self.assertGreater(c.screen_integral([0, 0, 0, 1], 0), 0)
        self.assertEqual(c.cubic_negative_part_bound(0, 0, 0, 0, 1), 0)
        # Discarding negative defect would incorrectly bound the cubic by zero.

    def test_screen_quadrature_keeps_all_components(self):
        coefficients = [.0625, 0, -.5, 0, 1]
        direct = quad(lambda z: max(.01-(z*z-.25)**2, 0), -1, 1,
                      points=[-.6, -.5, -.4, .4, .5, .6], epsabs=1e-11)[0]
        self.assertAlmostEqual(c.screen_integral(coefficients, .01), direct, places=9)
        self.assertGreater(direct, 0)

    def test_two_radius_odd_jet_coefficients(self):
        k, q, M, r = s.symbols('k q M r', positive=True)
        first = k/r+q*r+M*r**3
        second = k/(2*r)+2*q*r+8*M*r**3
        self.assertEqual(s.expand((4*first+second)/3),
                         3*k/(2*r)+2*q*r+4*M*r**3)
        self.assertEqual(s.expand((first+second)/(3*r*r)),
                         k/(2*r**3)+q/r+3*M*r)

    def test_scale_equation_across_flat_and_quartic_regimes(self):
        for v in np.geomspace(1e-50, .01, 8):
            for q in (0., 1e-20, .001, 1.):
                R, H, K = c.phase_scales(v, q)
                self.assertAlmostEqual(q*R**5/v+R**7/v, 1, places=11)
                self.assertAlmostEqual(H*R/v, 1, places=11)
                self.assertAlmostEqual(K*R**3/v, 1, places=11)

    def test_scale_homogeneity(self):
        base = c.phase_scales(.003, .04)
        for factor in (.01, 2., 13.):
            scaled = c.phase_scales(.003*factor**7, .04*factor**2)
            np.testing.assert_allclose(scaled, np.array(base)*factor**np.array([1, 6, 4]),
                                       rtol=2e-13)

    def test_all_scales_monotone_in_actual_volume(self):
        for q in (0., 1e-5, .1):
            values = np.array([c.phase_scales(v, q) for v in np.geomspace(1e-12, .01, 40)])
            self.assertTrue(np.all(np.diff(values, axis=0) > 0))

    def test_infinite_flat_reference_powers(self):
        for v in (1e-3, 1e-10, 1e-30):
            np.testing.assert_allclose(c.phase_scales(v, 0),
                                       [v**(1/7), v**(6/7), v**(4/7)], rtol=2e-14)

    def test_uniform_dyadic_power_and_critical_margin(self):
        v, u = s.symbols('v u', positive=True)
        H, K = v**s.Rational(4, 5)*u**s.Rational(1, 5), v**s.Rational(2, 5)*u**s.Rational(3, 5)
        band = v**s.Rational(1, 5)*u**s.Rational(4, 5)
        self.assertEqual(s.simplify(H*K*K*band/u**2),
                         v**s.Rational(9, 5)*u**s.Rational(1, 5))
        self.assertEqual(s.Rational(5, 3)-s.Rational(9, 5), -s.Rational(2, 15))
        self.assertEqual(s.Rational(9, 5)*s.Rational(3, 2)+1, s.Rational(37, 10))
        self.assertLess(sum(2**(-j/5) for j in range(500)), 1/(1-2**(-1/5))+1e-13)

    def test_even_sector_alone_misses_a_losing_cubic_well(self):
        k, b, q, h = 1e-4, .1, 1., 1e-9
        self.assertGreater(k, math.sqrt(q*h)+h**(2/3))
        self.assertGreater(h, k**3/b**2)
        # The full screen panel contains its lower competing well. Its volume,
        # not the selected well's excess, detects the bad phase scale.
        volume = c.screen_integral([0, 0, k, b, q], h)
        self.assertLess(k, c.phase_scales(volume, q)[2])

    def test_good_side_normalized_jet_powers(self):
        for stiffness in (10., 100., 10000.):
            t = stiffness**(1/3)
            self.assertLessEqual((stiffness+1)*math.sqrt(t)/stiffness**1.5,
                                 2*stiffness**(-1/3))
            self.assertLessEqual((stiffness+1)*t/stiffness**2,
                                 2*stiffness**(-2/3))
            self.assertLessEqual((stiffness+1)*t**1.5/stiffness**2.5,
                                 2/stiffness)


class MatchingBoundaryTests(unittest.TestCase):
    def test_joint_contact_bound_is_not_product_of_separate_bounds(self):
        for K in (1e-2, 1e-4, 1e-6):
            eps = K/10
            # Compatible quartic minimum coordinates: angular width sqrt(k).
            mass = 2/5*((K/2+eps)**2.5-(K/2)**2.5)
            self.assertLess(mass, eps*K**1.5)
            self.assertGreater(mass/(eps*K**2.5), .3/K)

    def test_normalized_gap_uses_one_control_for_all_states(self):
        a, z, k, u = s.symbols('a z k u')
        F = u**6+u**8/3
        A = k-s.diff(F, u, 2).subs(u, a)/2
        B = -s.diff(F, u).subs(u, a)-2*A*a
        U = F+A*u*u+B*u
        defect = U.subs(u, a+z)-U.subs(u, a)
        self.assertEqual(s.simplify(s.diff(defect, k)), z*z)

    def test_central_transport_is_exact_but_not_uniform_at_tip(self):
        for length in (1., 2.):
            for fraction in (.001, .2, .5):
                ss = fraction*length
                theta = .15
                distance = math.sqrt(length**2+ss**2-2*length*ss*math.cos(theta))
                cosine = (length*math.cos(theta)-ss)/distance
                us = 1-cosine
                ua = length*ss*math.sin(theta)/distance
                coefficient = 1/(ss*ss*(1+cosine))
                self.assertAlmostEqual(us, coefficient*ua*ua, places=13)
                self.assertGreaterEqual(coefficient, 1/(2*ss*ss))

    def test_primary_fractional_budget_integrable_not_cubic(self):
        self.assertEqual(-s.Rational(7, 6)+s.Rational(3, 8), -s.Rational(19, 24))
        self.assertGreater(-s.Rational(19, 24), -1)
        self.assertLess(-2+s.Rational(1, 2), -1)

    def test_fixed_accumulating_profile_has_strict_flattening_wells(self):
        self.assertEqual(c.accumulating_profile(0), 0)
        with mp.workdps(70):
            for n in (4, 8, 12):
                point = mp.mpf(1)/n
                curvature = mp.diff(c.accumulating_profile, point, 2)
                exact = c.accumulating_zero_curvature(n)
                self.assertLess(abs(curvature/exact-1), mp.mpf('1e-60'))
                self.assertGreater(exact, 0)

    def test_unbounded_count_shortcut_fails_on_compatible_finite_blocks(self):
        previous = 0
        for n in (4, 8, 12, 16):
            result = c.accumulating_well_diagnostic(n)
            self.assertGreater(result['active_wells'], previous)
            self.assertGreater(result['min_log10_good_ratio'], 20)
            self.assertLess(result['max_log10_excess_barrier_ratio'], -50)
            previous = result['active_wells']

    def test_invalid_diagnostic_inputs_are_explicit(self):
        calls = [lambda: c.phase_scales(0, 1), lambda: c.phase_scales(1, -1),
                 lambda: c.phase_scales(math.inf, 0),
                 lambda: c.screen_integral([], 1),
                 lambda: c.screen_integral([0, math.nan], 1),
                 lambda: c.cubic_negative_part_bound(-1, 0, 1, 1, 1),
                 lambda: c.accumulating_zero_curvature(True),
                 lambda: c.accumulating_profile(math.inf),
                 lambda: c.accumulating_well_diagnostic(100)]
        for call in calls:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
