"""Finite CS arithmetic/domain regressions, not analytic remainder proofs."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

import curved_cusp_response as cs
from null_singular_ends import cusp_contains, cusp_action as flat_cusp_action


class CurvedCuspResponseTests(unittest.TestCase):
    def test_joint_map_metric_jacobian_and_curvature_scaling(self):
        T, R, z = s.symbols('T R z', positive=True)
        L = s.Matrix([[T, R, 0], [R, T, 0], [0, 0, z]])
        eta = s.diag(1, -1, -1)
        result = L.T*eta*L-(T*T-R*R)*eta
        self.assertEqual(result.subs(z*z, T*T-R*R), s.zeros(3))
        self.assertEqual(s.expand(L.det()-z*(T*T-R*R)), 0)
        for T, squared in ((.3, .04), (.75, .02), (.8, .64)):
            for representation in ('cone', 'balls'):
                time, x, sigma, weights = cs._diamond_nodes(24, representation)
                self.assertAlmostEqual(float(weights.sum()), cs.C, places=13)
                ell = T*(1-time)-math.sqrt(max(0., T*T-squared))*x
                self.assertTrue(np.all(ell > 0))
                self.assertTrue(np.all(squared*sigma <= ell*ell+1e-14))
                self.assertTrue(np.all(time > 0))

    def test_actual_interval_average_from_rest_moments(self):
        for qt, ell, sigma in ((.25, .7, .3), (-.2, .2, .01), (.4, .8, .6)):
            actual = 1+(qt-ell/2)**2+ell*ell/40+3*(ell*ell-sigma)/80
            self.assertAlmostEqual(float(cs.interval_average(qt, ell, sigma)), actual, places=14)
        ell, sigma = s.symbols('ell sigma')
        actual = s.expand(ell**2/4+ell**2/40+3*(ell**2-sigma)/80)
        self.assertEqual(actual, 5*ell**2/16-3*sigma/80)

    def test_two_complete_partner_integrations(self):
        for rho, T, squared in ((3., .3, .04), (50., .8, .2), (300., .75, .01)):
            a = cs.partner_response(rho, T, squared, order=40)
            b = cs.partner_response(rho, T, squared, order=40, representation='balls')
            self.assertLess(abs(a-b), 9e-10)
        self.assertAlmostEqual(cs.partner_response(50, .8, .2, kappa=0, order=40),
                               cs.BETA*math.exp(-cs.C*50*.2**1.5), delta=3e-9)

    def test_fixed_physical_time_split_and_point_once(self):
        rho, T, squared = 50, .8, .02
        whole = cs.partner_response(rho, T, squared, order=24)
        for cutoff in (.0625, .15, .3):
            short = cs.partner_response(rho, T, squared, order=24, cutoff=cutoff, side='short')
            long = cs.partner_response(rho, T, squared, order=24, cutoff=cutoff, side='long')
            self.assertAlmostEqual(short+long, whole, places=13)
        # Reference l is not the physical gap. The boost is retained at fixed s.
        t, x, _, weights = cs._diamond_nodes(24, 'cone')
        ell = T*(1-t)-math.sqrt(T*T-squared)*x
        self.assertGreater(float(weights@abs(ell-(1-t))), .03)
        full = cs.cusp_action(2, order=6, partner_order=12)
        parts = sum(cs.cusp_action(2, order=6, partner_order=12, cutoff=.0625, side=side)
                    for side in ('short', 'long'))
        self.assertAlmostEqual(full, parts, places=12)

    def test_actual_cusp_angular_masks_both_transition_sides(self):
        angles = 2*math.pi*(np.arange(4096)+.5)/4096
        for T, squared in ((.4, .03), (.51, .01), (.75, .1), (.75, .52), (.99, .97)):
            radius = math.sqrt(T*T-squared)
            qt = T-.5
            points = [(qt+.5+radius*math.cos(phi),
                       qt-.5-radius*math.cos(phi), radius*math.sin(phi)) for phi in angles]
            sampled = sum(cusp_contains(point) for point in points)*2*math.pi/len(points)
            self.assertLess(abs(sampled-cs.angular_measure(T, squared)), 4*math.pi/len(points))
        self.assertAlmostEqual(cs.angular_measure(.75, .5), 2*math.pi)
        self.assertLess(cs.angular_measure(.75, .49), 2*math.pi)
        self.assertAlmostEqual(cs.angular_measure(.75, .53), 2*math.pi)

    def test_both_endpoint_measures_and_geometric_volume(self):
        volume = math.fsum(w for _, _, w in cs._target_nodes(32))
        self.assertAlmostEqual(volume, cs.C*(2**1.5-1), delta=5e-9)
        weighted = math.fsum(w*(1+(T-.5)**2) for T, _, w in cs._target_nodes(32))
        direct = sum(quad(lambda t:cs.slice_area(t)*(1+t*t), lo, hi,
                          epsabs=1e-11)[0] for lo, hi in ((-.5, 0), (0, .5)))
        self.assertAlmostEqual(weighted, direct, delta=6e-9)
        self.assertGreater(abs(weighted-volume), .015)

    def test_complete_curved_quadrature_refinement_and_flat_control(self):
        coarse = cs.cusp_action(20, order=10)
        refined = cs.cusp_action(20, order=14)
        self.assertLess(abs(coarse-refined), 3e-6)
        self.assertAlmostEqual(refined, 1.99142135, delta=4e-7)
        flat = cs.cusp_action(20, order=12, kappa=0)
        self.assertAlmostEqual(flat, flat_cusp_action(20, order=48), delta=2e-7)
        self.assertGreater(abs(refined-flat), .05)

    def test_signed_point_and_curvature_residues(self):
        w = s.symbols('w')
        A, At, Att, lap, grad = s.symbols('A At Att lap grad')
        kernel = s.gamma(w)*(1-3*w/2)*(1-3*w/4)
        self.assertEqual(kernel.subs(w, 1), -s.Rational(1, 8))
        self.assertEqual(s.simplify(kernel.subs(w, s.Rational(5, 3))/s.gamma(s.Rational(5, 3))),
                         s.Rational(3, 8))
        coefficient = s.Rational(1, 2)-5*w/32
        X = coefficient*Att+w*(w-3)*At*At/(8*A)
        Y = coefficient*lap+w*(w-3)*grad/(8*A)
        Z = 3*w*(Att-lap)/160
        integral = (X+Y/2)/(1-3*w/2)+(Z-Y/2)/(2-3*w/2)
        critical = s.simplify(integral.subs(w, s.Rational(5, 3)))
        self.assertEqual(s.simplify(critical+s.Rational(2, 9)*(Att-lap)
                                   -s.Rational(5, 27)*(At*At-grad)/A), 0)
        self.assertEqual(8*kernel.subs(w, 1), -1)  # Rightward shift subtracts residue.

    def test_cubic_angular_jet_has_no_double_pole_at_two(self):
        w, A, b, nx, ny, xi = s.symbols('w A b nx ny xi')
        Et, Ex, Ey, Ett, Etx, Ety, Exx, Exy, Eyy = s.symbols('Et Ex Ey Ett Etx Ety Exx Exy Eyy')
        ttt, ttx, tty, txx, txy, tyy, xxx, xxy, xyy, yyy = s.symbols('ttt ttx tty txx txy tyy xxx xxy xyy yyy')
        D1 = Et+b*(nx*Ex+ny*Ey)
        D2 = Ett+2*b*(nx*Etx+ny*Ety)+b*b*(nx*nx*Exx+2*nx*ny*Exy+ny*ny*Eyy)
        D3 = (ttt+3*b*(nx*ttx+ny*tty)+3*b*b*(nx*nx*txx+2*nx*ny*txy+ny*ny*tyy)
              +b**3*(nx**3*xxx+3*nx*nx*ny*xxy+3*nx*ny*ny*xyy+ny**3*yyy))
        box = Ett-Exx-Eyy
        dbox = ttt-txx-tyy+b*(nx*(ttx-xxx-xyy)+ny*(tty-xxy-yyy))
        h1, h2, h3 = -D1/2, 5*D2/32-3*xi*box/160, -7*D3/192+3*xi*dbox/320
        cubic = (-D3/6-D2*w*h1/(2*A)
                 -D1*(-w*h2/A+w*(w+1)*h1*h1/(2*A*A))
                 -w*h3+w*(w+1)*h1*h2/A-w*(w+1)*(w+2)*h1**3/(6*A*A))
        polynomial = s.Poly(s.expand(cubic), nx, ny)
        averaged = polynomial.coeff_monomial(1)+(polynomial.coeff_monomial(nx*nx)
                                                +polynomial.coeff_monomial(ny*ny))/2
        averaged = s.expand(averaged).subs(b*b, 1-xi)
        self.assertLessEqual(s.Poly(s.expand(averaged), xi).degree(), 1)
        self.assertNotEqual(s.simplify(averaged.subs(w, 2)), 0)

    def test_null_profile_is_limit_of_actual_weighted_diamonds(self):
        T, squared = .75, 1e-6
        for lam in (1, 10, 100):
            profile = cs.null_profile(lam, T, order=96)
            actual = cs.partner_response(lam/squared**1.5, T, squared, order=64)
            self.assertAlmostEqual(actual, profile, delta=6e-8)
        self.assertGreater(cs.null_profile(100, T, order=96), .002)
        self.assertLess(math.exp(-100*cs.C), 1e-10)  # A true algebraic tail, not this exponential.

    def test_mass_uses_zero_times_pole_and_retains_upper_tail(self):
        u = s.symbols('u')
        beta = (s.gamma(-s.Rational(1, 2)-3*u/2)*s.gamma(s.Rational(3, 2))
                /s.gamma(1-3*u/2))
        slope = s.limit(beta/(u-s.Rational(2, 3)), u, s.Rational(2, 3))
        self.assertEqual(s.simplify(slope), -s.pi)
        self.assertEqual(s.simplify(slope*(-s.Rational(2, 3))), 2*s.pi/3)
        T, top = .75, 40.
        lower = quad(lambda z:cs.null_profile(z**1.5, T, order=112), 0, top, epsabs=2e-8)[0]
        upper = 2*cs.profile_tail(T)/math.sqrt(top)
        self.assertGreater(abs(lower-cs.profile_mass(T)), .09)
        self.assertLess(abs(lower+upper-cs.profile_mass(T)), .0019)
        self.assertAlmostEqual(cs.profile_tail(T), .305911680431469, places=12)
        self.assertEqual(cs.profile_tail(T, kappa=0), 0.)

    def test_nonpolynomial_signed_ray_profile(self):
        T = .75
        polynomial = lambda e:1+(T-.5-T*e)**2
        self.assertAlmostEqual(cs.ray_profile(10, polynomial), cs.null_profile(10, T), places=12)
        # The proven structural class is not limited to polynomial/time-only A.
        # This finite ray check also prevents assuming profile positivity.
        self.assertLess(cs.ray_profile(10, lambda e:np.exp(4*e), order=80), -.03)
        self.assertAlmostEqual(cs.ray_profile(3, lambda e:np.ones_like(e), order=64),
                               cs.BETA*math.exp(-3*cs.C), delta=2e-10)

    def test_independent_curvature_and_screen_target(self):
        t = s.symbols('t')
        omega = (1+t*t)**s.Rational(1, 3)
        bulk = 2*s.diff(omega,t,2)-s.diff(omega,t)**2/omega
        self.assertEqual(s.simplify(bulk-(12-8*t*t)/(9*(1+t*t)**s.Rational(5, 3))), 0)
        geometric = cs.geometric_target()
        self.assertAlmostEqual(geometric[0], .5762798189516913, places=11)
        self.assertAlmostEqual(geometric[1], 4.574132601400751, places=11)
        self.assertAlmostEqual(sum(geometric), 5.150412420352442, places=11)
        self.assertAlmostEqual(sum(cs.geometric_target(kappa=0)), math.pi*math.sqrt(2), places=11)
        for T in (.2, .75, .99):
            qt = T-.5;A = 1+qt*qt
            ray_derivative = A**(1/3)+T*2*qt/(3*A**(2/3))
            self.assertAlmostEqual(A*cs.profile_mass(T)/2, ray_derivative, places=13)

    def test_invalid_inputs(self):
        calls = (lambda:cs.partner_response(0,.5,.1),
                 lambda:cs.partner_response(1,.5,.3),
                 lambda:cs.partner_response(1,.5,.1,kappa=-1),
                 lambda:cs.partner_response(1,.5,.1,representation='omitted'),
                 lambda:cs.partner_response(1,.5,.1,side='short'),
                 lambda:cs.partner_response(1,.5,.1,cutoff=0),
                 lambda:cs.angular_measure(1,.5),
                 lambda:cs.angular_measure(.5,-.1),
                 lambda:cs.interval_average(0,.2,.3),
                 lambda:cs.null_profile(1,2),
                 lambda:cs.profile_mass(2),
                 lambda:cs.profile_tail(2),
                 lambda:cs.geometric_target(kappa=float('nan')),
                 lambda:cs.slice_area(1),
                 lambda:cs.ray_profile(1,lambda e:-np.ones_like(e)),
                 lambda:cs.ray_profile(1, None),
                 lambda:cs.cusp_action(1,order=True))
        for call in calls:
            with self.subTest(call=call), self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
