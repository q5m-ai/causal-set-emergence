"""Finite diagnostics, explicitly distinct from C3/F3's written estimates."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq

import curved_three_d as c
from dimension_kernels import (Z, kernel_polynomial, layer_coefficients,
                               mellin_factor, transverse_moment)


class NormalizationTests(unittest.TestCase):
    def test_actual_three_dimensional_recurrence_and_factorials(self):
        self.assertEqual(kernel_polynomial(3), 1-27*Z/8+9*Z**2/8)
        self.assertEqual(layer_coefficients(3), (1, -s.Rational(27, 8), s.Rational(9, 4)))
        self.assertEqual(transverse_moment(3, 0), 0)
        self.assertEqual(transverse_moment(3, 1), 0)
        self.assertEqual(transverse_moment(3, s.Rational(3, 2)), s.gamma(s.Rational(2, 3))/6)
        self.assertAlmostEqual(c.A3, c.BETA3)
        self.assertAlmostEqual(c.C3, math.pi/12)

    def test_kernel_moments_by_independent_quadrature(self):
        for power in (s.Rational(2, 3), s.Rational(4, 3), s.Rational(5, 3)):
            # Remove the integrable origin singularity with z=u^3.
            value = quad(lambda u: 3*u**(3*float(power)-1)*c.kernel3(u**3),
                         0, 5, epsabs=1e-11)[0]
            expected = float(s.gamma(power)*mellin_factor(3, power))
            self.assertAlmostEqual(value, expected, places=10)

    def test_critical_cusp_threshold_not_four_dimensional(self):
        z = s.symbols('z')
        self.assertEqual(s.solve(s.Rational(7, 2)-s.Rational(5, 2)*z+1, z), [s.Rational(9, 5)])
        self.assertGreater(s.Rational(9, 5), s.Rational(5, 3))
        self.assertEqual(s.Rational(3, 2)+2-s.Rational(5, 3)*s.Rational(5, 2), -s.Rational(2, 3))
        self.assertEqual(s.Rational(3, 2)+2-s.Rational(5, 3)*3, -s.Rational(3, 2))


class ConformalIntervalTests(unittest.TestCase):
    def test_boosted_volume_matches_exact_variable_time_density(self):
        for source_time, gap, radius in ((-.3, 1.2, .7), (.4, .9, .899)):
            lam = .8
            result = c.boosted_interval([source_time, 0, 0], [source_time+gap, radius, 0],
                                        lambda t, x, y: 1+lam*t*t, order=12)
            exact = c.time_density_interval(source_time, gap, radius, lam)
            self.assertAlmostEqual(result/exact, 1, places=12)
            frozen = c.C3*((gap-radius)*(gap+radius))**1.5*(1+lam*source_time**2)
            self.assertGreater(abs(result/frozen-1), .02)

    def test_independent_time_disk_domain_nonpolynomial_density(self):
        density = lambda t, x, y: 1+.2*t*t+.07*x+.1*y*y+.03*np.sin(t+2*x-y)
        for gap, radius in ((1.1, .6), (.9, .87)):
            boost = c.boosted_interval([-.2, 0, 0], [gap-.2, radius, 0], density, order=18)
            coarse = c.slice_interval(-.2, gap, radius, density, order=14)
            fine = c.slice_interval(-.2, gap, radius, density, order=28)
            self.assertLess(abs(fine/boost-1), 8e-5)
            self.assertLess(abs(fine-boost), abs(coarse-boost))

    def test_curvature_and_induced_curve_are_independent(self):
        b, slope, tilt = .35, .3, .22
        bulk, joint = c.cap_targets(b, slope, tilt)
        closed = 4*math.pi*slope*(1-b/2-(1+b)/b*math.log1p(b))
        self.assertAlmostEqual(bulk, closed, places=12)
        def direct(theta):
            xx = np.array([math.cos(theta), math.sin(theta)])
            lower, upper = np.array([tilt, 0])+slope*xx, np.array([tilt, 0])-slope*xx
            dot = (1-np.dot(lower, upper))/math.sqrt((1-np.dot(lower, lower))*(1-np.dot(upper, upper)))
            angle = dot/math.sqrt(dot*dot-1)
            length = (1+b)*math.sqrt(1-tilt*tilt*math.sin(theta)**2)
            return angle*length, angle
        self.assertAlmostEqual(quad(lambda th: direct(th)[0], 0, 2*math.pi)[0], joint, places=11)
        self.assertNotAlmostEqual(direct(0)[1], direct(math.pi/2)[1], places=4)
        self.assertLess(bulk, 0)
        self.assertGreater(joint, 0)

    def test_scalar_curvature_from_connection_not_target(self):
        # Christoffel contraction in the repository's Riemann sign, for a
        # nonconstant spatial conformal factor. No action enters this calculation.
        t, x, y, b = s.symbols('t x y b', real=True)
        coords = (t, x, y)
        omega = 1+b*(x*x+y*y)
        g = s.diag(omega**2, -omega**2, -omega**2)
        gi = g.inv()
        ch = [[[s.simplify(sum(gi[a, e]*(s.diff(g[e, d], coords[c0])+
                 s.diff(g[e, c0], coords[d])-s.diff(g[c0, d], coords[e]))/2
                 for e in range(3))) for d in range(3)] for c0 in range(3)] for a in range(3)]
        ric = s.zeros(3)
        for bb in range(3):
            for dd in range(3):
                ric[bb, dd] = sum(s.diff(ch[a][a][bb], coords[dd])-s.diff(ch[a][dd][bb], coords[a])+
                    sum(ch[a][dd][e]*ch[e][a][bb]-ch[a][a][e]*ch[e][dd][bb] for e in range(3))
                    for a in range(3))
        scalar = s.simplify(sum(gi[i, j]*ric[i, j] for i in range(3) for j in range(3)))
        self.assertEqual(s.simplify(scalar+16*b/omega**3-8*b*b*(x*x+y*y)/omega**4), 0)

    def test_complete_thin_torus_pair_orders_and_cutoff(self):
        for rho in (1., 12.):
            a = c.thin_torus_action(rho, order=24, cutoff=.19)
            b = c.thin_torus_action(rho, order=24, cutoff=.37, pair_order='radius')
            self.assertAlmostEqual(a[0], a[1]+a[2], places=12)
            self.assertAlmostEqual(b[0], b[1]+b[2], places=12)
            self.assertAlmostEqual(a[0], b[0], delta=3e-6)
            self.assertGreater(abs(a[1]-b[1]), .01)
            self.assertAlmostEqual(a[1]-b[1], -(a[2]-b[2]), delta=3e-6)

    def test_complete_phase_quadrature_resolves_cancellation(self):
        direct = c.thin_torus_action(12, order=30)
        phase = c.thin_torus_action_phase(12, order=20)
        np.testing.assert_allclose(direct, phase, rtol=2e-7, atol=3e-6)
        # Finite convergence diagnostic against independently integrated curvature.
        target = 16*quad(lambda t: (2/3)*(1+.5*t*t)**(-2/3)-
                         (5/9)*t*t*(1+.5*t*t)**(-5/3), -.3, .3)[0]
        low = c.thin_torus_action_phase(1e4, order=20)
        high = c.thin_torus_action_phase(1e6, order=20)
        refined = c.thin_torus_action_phase(1e6, order=30)
        np.testing.assert_allclose(high, refined, rtol=1e-6, atol=1e-7)
        self.assertLess(abs(high[0]-target), abs(low[0]-target))
        self.assertLess(abs(high[0]-target), .3)
        self.assertAlmostEqual(high[0], high[1]+high[2], places=9)

    def test_all_ordered_partitions_nonzero_endpoint_fields_and_point_once(self):
        chis = (lambda t: .3+.1*t, lambda t: .7-.1*t)
        phis = (lambda t: .4-.05*t, lambda t: .6+.05*t)
        values = [c.thin_torus_action(2., order=12, fields=(chi, phi))
                  for chi in chis for phi in phis]
        whole = c.thin_torus_action(2., order=12)
        np.testing.assert_allclose(np.sum(values, axis=0), whole, rtol=3e-14, atol=3e-14)
        self.assertGreater(abs(values[1][0]), .01)
        self.assertGreater(abs(values[2][0]), .01)
        self.assertGreater(abs(values[0][0]+values[3][0]-whole[0]), .01)


class FocalGeometryTests(unittest.TestCase):
    def test_mechanical_action_against_independent_ode(self):
        length, target = 1.3, .15
        def shoot(velocity):
            return solve_ivp(lambda t, z: [z[1], -.25*math.sin(4*z[0]),
                .5*(z[1]**2-.25*math.sin(2*z[0])**2)], [0, length], [0, velocity, 0],
                rtol=2e-11, atol=2e-13).y[:, -1]
        velocity = brentq(lambda v: shoot(v)[0]-target, 0, 1, xtol=1e-12)
        self.assertAlmostEqual(shoot(velocity)[2], c.physical_segment_action(length, target), places=10)

    def test_actual_regular_interval_coefficient(self):
        length = 2.4
        leading = c.regular_axis_leading(length)
        coarse = c.physical_axis_volume(length, .0004, order=16)/.0004**1.5
        fine = c.physical_axis_volume(length, .0001, order=24)/.0001**1.5
        self.assertLess(abs(fine/leading-1), .003)
        self.assertLess(abs(fine-leading), abs(coarse-leading))

    def test_actual_focal_interval_not_four_dimensional_scaling(self):
        lead = c.focal_axis_leading()
        v1 = c.physical_axis_volume(math.pi, .0004, order=20)
        v2 = c.physical_axis_volume(math.pi, .0001, order=24)
        self.assertLess(abs(v2/.0001**1.25/lead-1), .025)
        self.assertLess(abs(v2/.0001**1.25-lead), abs(v1/.0004**1.25-lead))
        self.assertLess(abs(math.log(v1/v2)/math.log(4)-1.25), .025)
        self.assertGreater(abs(math.log(v1/v2)/math.log(4)-1.75), .4)

    def test_model_all_wells_and_moving_opening(self):
        for energy, r in ((.001, 0.), (.001, .4999), (.01, .5), (.0625, .5), (3., -.2)):
            # Independent whole real-line positive-part quadrature.
            roots = sorted(z.real for z in np.roots([1, 4*r, 1, 0, -energy]) if abs(z.imag)<1e-7)
            expected = quad(lambda u: max(0, energy-u*u-4*r*u**3-u**4),
                            roots[0], roots[-1], points=roots[1:-1], epsabs=1e-12)[0]
            self.assertAlmostEqual(c.quartic_profile(energy, r), expected, places=10)
        self.assertGreater(c.quartic_profile(.001, .5), 1.9*c.quartic_profile(.001, 0))
        self.assertLess(c.quartic_profile(.001, .49), 1.1*c.quartic_profile(.001, 0))

    def test_model_quartic_measure_jacobian(self):
        k, r, ee = s.symbols('k r E', positive=True)
        a = s.sqrt(k)*r
        aa, bb = k-6*a*a, 8*a**3-2*k*a
        energy = a**4+aa*a*a+bb*a+k*k*ee
        jac = s.Matrix([aa, bb, energy]).jacobian([k, r, ee]).det()
        self.assertEqual(s.simplify(abs(jac)/k**s.Rational(7, 2)), 2)

    def test_nonzero_cubic_inverse_coefficient_not_only_a_bad_majorant(self):
        u = s.symbols('u', positive=True)
        energy = u+u*u/5-4*u**3/25
        # (f/(4/3))^(2/3) = E*(1-E/5+6*E^2/25)+O(E^4).
        self.assertEqual(s.series(energy*(1-energy/5+6*energy**2/25)-u,
                                 u, 0, 4).removeO(), 0)
        for ee in (.001, .0001):
            expected = 4/3*ee**1.5-2/5*ee**2.5+.5*ee**3.5
            self.assertLess(abs(c.quartic_profile(ee, 0)/expected-1), 3*ee**3)

    def test_physical_union_overlap_and_kernel_nonlinearity(self):
        e, velocity = .002, 1.3
        union, added = c.quadratic_tube_union(e, velocity, e)
        self.assertGreater(added-union, 0)
        self.assertNotAlmostEqual(float(c.kernel3(100*union)), float(2*c.kernel3(50*added)), places=3)
        apart = c.quadratic_tube_union(e, velocity, 10*e)
        self.assertAlmostEqual(apart[0], apart[1], places=14)
        # Exact homogeneity of the integrated endpoint overlap: O(e^3).
        def overlap(excess):
            top = 8*excess/velocity**2
            return quad(lambda ss: c.quadratic_tube_union(excess, velocity, ss)[1]-
                         c.quadratic_tube_union(excess, velocity, ss)[0], 0, top, epsabs=1e-13)[0]
        self.assertAlmostEqual(overlap(e)/overlap(e/2), 8, places=8)

    def test_both_endpoint_times_closing_and_cutoff_equality(self):
        for length, energy in ((.4, .1), (math.pi, 0), (2., .8)):
            tau = length/2+energy
            # Direct source-time integration with actual target membership.
            expected = max(0, min(c.DURATION/2, c.DURATION/2-tau)+c.DURATION/2)
            self.assertAlmostEqual(c.focal_time_weight(length, energy), expected)
            for delta in (.3, 1.):
                short = c.focal_time_weight(length, energy, delta, short=True)
                long = c.focal_time_weight(length, energy, delta)
                self.assertAlmostEqual(short+long, expected)
        self.assertEqual(c.focal_time_weight(.4, .1, .30000000000000004, short=True), 0)
        self.assertGreater(c.focal_time_weight(.4, .1, .30000000000000004), 0)

    def test_invalid_diagnostic_domains_are_not_silent_extensions(self):
        for call in (lambda: c.physical_axis_volume(math.pi+.1, .001),
                     lambda: c.physical_axis_volume(math.pi, .1),
                     lambda: c.thin_torus_action(1, duration=2, period=3),
                     lambda: c.quartic_profile(.1, .6),
                     lambda: c.focal_time_weight(1, -.7),
                     lambda: c.rule(True)):
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
