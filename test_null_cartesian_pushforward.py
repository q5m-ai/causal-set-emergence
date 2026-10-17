"""Finite arithmetic and actual-domain regressions, not limit certificates."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.special import beta, gamma, k0

from dimension_kernels import factor_count, interval_coefficient, transverse_moment
from null_cartesian_pushforward import (
    cone_gap, kernel, plane_graph, signed_ramp, time_density_average, triangle_pair,
)


class CartesianPushforwardTests(unittest.TestCase):
    def test_signed_ramp_against_original_triangle_and_kept_tail(self):
        for d in (2, 3, 4, 5, 7):
            for h in (.07, .4, 1.2, 2.):
                actual = quad(lambda u: (h-u)*kernel(d, u**(d/2)), 0, h,
                              epsabs=3e-12)[0]
                tail = quad(lambda u: (u-h)*kernel(d, u**(d/2)), h, np.inf,
                            epsabs=3e-12)[0]
                self.assertAlmostEqual(signed_ramp(d, h), actual, delta=2e-10)
                self.assertAlmostEqual(actual, tail, delta=2e-10)
        self.assertEqual(signed_ramp(4, 0), 0)
        self.assertEqual(signed_ramp(4, -2), 0)

    def test_genuine_primitive_moments_and_fourier_integrability(self):
        for d in (*range(2, 12), 20, 21):
            m, nu = factor_count(d), s.Rational(d-2, 2)
            for j in range(m-1):
                for k in range(m-j-2):
                    self.assertEqual(transverse_moment(d, j+k+2), 0)
            low_frequency_power = m-2-nu
            self.assertEqual(low_frequency_power, 0 if d % 2 == 0 else -s.Rational(1, 2))
            self.assertGreater(m-1-nu, 0)
            self.assertLess(-3-nu, -1)

    def test_exact_odd_and_logarithmic_critical_constants(self):
        j = s.symbols('j', real=True)
        positive_3d = transverse_moment(3, s.Rational(3, 2))/s.Rational(3, 4)
        self.assertEqual(s.simplify(positive_3d-s.gamma(s.Rational(5, 3))/3), 0)
        saddle_4d = -s.diff(transverse_moment(4, j), j).subs(j, 2)/2
        self.assertEqual(s.simplify(saddle_4d-s.sqrt(s.pi)/24), 0)
        for d in (4, 6, 8, 10):
            self.assertEqual(transverse_moment(d, s.Rational(d, 2)), 0)
        ordinary = quad(lambda u: signed_ramp(4, u), 0, np.inf, epsabs=1e-11)[0]
        logarithm = quad(lambda u: signed_ramp(4, u)*math.log(u), 0, np.inf,
                         epsabs=1e-11)[0]
        self.assertAlmostEqual(ordinary, 0, delta=2e-11)
        self.assertAlmostEqual(logarithm, -math.sqrt(math.pi)/24, delta=2e-11)

    def test_direct_positive_quadratic_response(self):
        target = float(gamma(5/3)/3)
        errors = []
        for epsilon in (.15, .06, .02):
            direct = 2/math.sqrt(epsilon)*quad(
                lambda z: math.exp(-z*z)*signed_ramp(3, z*z/epsilon),
                0, 3, points=[math.sqrt(epsilon)], epsabs=1e-11)[0]
            errors.append(abs(direct-target))
        self.assertLess(errors[-1], errors[0])
        self.assertLess(errors[-1], .012)

    def test_saddle_keeps_critical_logarithm_not_a_smooth_density(self):
        target = math.sqrt(math.pi)/24
        errors = []
        for epsilon in (.2, .07, .02):
            response = quad(lambda u: signed_ramp(4, u)*k0(epsilon*u), 0, np.inf,
                            epsabs=2e-11)[0]
            errors.append(abs(response-target))
        self.assertLess(errors[-1], errors[0])
        self.assertLess(errors[-1], .001)
        # A constant-density replacement gives zero, not the actual saddle value.
        self.assertGreater(target, .07)

    def test_real_null_saddle_germs_and_exact_mixed_hessian(self):
        v, y1, y2 = s.symbols('v y1 y2', real=True)
        front = y1*y1/v+y2*y2/(v+3)
        self.assertEqual(s.simplify(s.diff(front, v)+(s.diff(front, y1)**2+s.diff(front, y2)**2)/4), 0)
        p1, p2, q1, q2 = s.symbols('p1 p2 q1 q2', real=True)
        f = front.subs({v: -1, y1: p1, y2: p2})
        g = front.subs({v: 1, y1: q1, y2: q2})
        B = s.expand(2*(g-f)-(q1-p1)**2-(q2-p2)**2)
        self.assertEqual(s.expand(B-((p1+q1)**2-2*(p2-q2/2)**2)), 0)
        mixed = s.Matrix([[s.diff(B, p, q) for q in (q1, q2)] for p in (p1, p2)])
        self.assertEqual(mixed, 2*s.eye(2))
        self.assertEqual(s.hessian(B, (p1, p2, q1, q2)).rank(), 2)

    def test_actual_null_triangle_and_true_conformal_phase_inversion(self):
        for d in (3, 4, 7):
            yp = np.linspace(.05, .18, d-2)
            yq = np.linspace(.08, .13, d-2)
            for curved in (False, True):
                original = triangle_pair(d, 50., 1., 1.3, yp, yq, curved=curved,
                                         representation='normals', order=44)
                inverted = triangle_pair(d, 50., 1., 1.3, yp, yq, curved=curved,
                                         representation='phase', order=44)
                self.assertAlmostEqual(original, inverted, delta=2e-9)
        yp, yq = [.2, -.1], [.3, .1]
        flat = triangle_pair(4, 20., 1., 1., yp, yq, curved=False)
        curved = triangle_pair(4, 20., 1., 1., yp, yq, curved=True)
        self.assertGreater(abs(flat-curved), 1e-5)

    def test_physical_temporal_complements_not_a_v_cutoff(self):
        d, a, b = 4, 1., 1.3
        yp, yq = np.array([.2, -.1]), np.array([.3, .1])
        v, f, g = a+b, -float(yp@yp)/a, float(yq@yq)/b
        h = cone_gap(a, b, yp, yq)/v
        cutoff = (v+g-f-h/2)/2
        for representation in ('normals', 'phase'):
            full = triangle_pair(d, 20., a, b, yp, yq, representation=representation)
            short = triangle_pair(d, 20., a, b, yp, yq, representation=representation,
                                  cutoff=cutoff, side='short')
            long = triangle_pair(d, 20., a, b, yp, yq, representation=representation,
                                 cutoff=cutoff, side='long')
            self.assertAlmostEqual(full, short+long, delta=1e-11)
            self.assertGreater(abs(short), 1e-6)
            self.assertGreater(abs(long), 1e-6)
        self.assertGreater(v, cutoff)  # This would incorrectly put ALL pairs in long.

    def test_null_trace_is_the_whole_ray_density_average(self):
        for d in (2, 3, 4, 7, 10):
            pt, qt = -.8, .7
            average = quad(lambda u: (u*(1-u))**(d/2-1)*(1+(pt+u*(qt-pt))**2),
                           0, 1, epsabs=1e-12)[0]/beta(d/2, d/2)
            self.assertAlmostEqual(time_density_average(d, pt, qt, 0), average, delta=1e-11)
            self.assertNotAlmostEqual(average, 1+qt*qt, places=3)

    def test_all_multi_sheet_selectors_not_an_unmasked_pair_sum(self):
        lower = [([0., 0.], -.3), ([.4, 0.], -.2), ([-.2, .3], -.25)]
        upper = [([0., 0.], .4), ([.1, -.3], .45), ([-.4, .2], .5), ([.2, .1], .4)]
        v, epsilon = 1.4, .2
        errors = []
        for yp in ([0., 0.], [.2, -.1], [-.3, .2]):
            for yq in ([.1, .2], [-.2, -.1]):
                fs = [plane_graph(-.6, yp, slope, c) for slope, c in lower]
                gs = [plane_graph(.8, yq, slope, c) for slope, c in upper]
                i, j = int(np.argmax(fs)), int(np.argmin(gs))
                values = np.array([[epsilon**2/(4*v*v)*signed_ramp(
                    4, (v*(g-f)-float(np.sum((np.array(yq)-yp)**2)))/epsilon)
                                    for g in gs] for f in fs])
                direct = epsilon**2/(4*v*v)*signed_ramp(
                    4, (v*(min(gs)-max(fs))-float(np.sum((np.array(yq)-yp)**2)))/epsilon)
                masked = sum(values[ii, jj]*(ii == i)*(jj == j)
                             for ii in range(len(fs)) for jj in range(len(gs)))
                self.assertAlmostEqual(masked, direct, places=14)
                errors.append(abs(float(values.sum())-direct))
        self.assertGreater(max(errors), 1e-5)
        # Positive-measure equal sheets must be tie-broken, not counted twice.
        self.assertEqual(sum(i == int(np.argmax([0., 0., -1.])) for i in range(3)), 1)

    def test_cone_tip_rank_and_integrable_uniform_envelope(self):
        a, b, p, q = s.symbols('a b p q', positive=True)
        B = (a+b)*(q*q/b+p*p/a)-(q-p)**2
        self.assertEqual(s.factor(B-(b*p+a*q)**2/(a*b)), 0)
        self.assertEqual(s.hessian(B, (p, q)).det(), 0)
        for n in (1, 2, 3, 5):
            radius = .4
            direct = quad(lambda R: quad(lambda u: R**(n-1)*(u*(1-u))**(n/2),
                                        0, 1, epsabs=1e-11)[0], 0, radius)[0]
            expected = radius**n/n*beta(1+n/2, 1+n/2)
            self.assertAlmostEqual(direct, expected, delta=2e-11)
        # In d=2 this bound really is logarithmic, despite the vanishing constant.
        self.assertAlmostEqual(quad(lambda r: 1/r, .001, .1)[0], math.log(100), places=10)

    def test_invalid_diagnostic_inputs(self):
        for call in (lambda: signed_ramp(1, 1), lambda: signed_ramp(4, math.nan),
                     lambda: cone_gap(0, 1, [0], [0]),
                     lambda: triangle_pair(4, 0, 1, 1, [0, 0], [0, 0]),
                     lambda: triangle_pair(4, 1, 1, 1, [0], [0]),
                     lambda: triangle_pair(4, 1, 1, 1, [0, 0], [0, 0], side='short')):
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
