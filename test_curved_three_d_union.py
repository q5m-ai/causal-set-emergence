"""Finite union diagnostics; none certifies the arbitrary-metric limit."""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

import curved_three_d_union as u
from curved_three_d import C3, kernel3, physical_axis_volume, regular_axis_leading
from curved_three_d_clusters import phase_scales


class NaturalAndTipTests(unittest.TestCase):
    def test_good_natural_scale_comparisons(self):
        for stiffness in (1., 10., 1e3, 1e6):
            for y in (0., .01, 1., 1e3, 1e8):
                denominator = y+math.sqrt(stiffness*(1+y))
                volume = stiffness**2.5*(1+y)**1.5/denominator**1.5
                height = stiffness**2*(1+y)/denominator
                self.assertGreaterEqual(volume, 2**(-1.5)*stiffness**1.75)
                self.assertGreaterEqual(height, .5*stiffness**1.5)

    def test_inner_null_domain_and_actual_prefix_cancellation(self):
        k, r, zeta, X, T, xi, m = s.symbols('k r zeta X T xi m', positive=True)
        # A flat proper prefix, with a bounded normalized terminal potential.
        uu, xx, vv, a = k*zeta, k*r*X, k*r*r*T, r*xi
        potential = k*a*a+k*a**4/r**2
        phi = potential+vv+(m*a-xx)**2/(2*(m-uu))-m*a*a/2
        normalized = s.cancel(phi/(k*r*r))
        self.assertEqual(s.simplify(s.limit(normalized, k, 0)-
                                   (xi**2+xi**4+T+zeta*xi**2/2-xi*X)), 0)
        self.assertEqual(s.simplify((2*uu*vv-xx*xx)/(k*k*r*r)), 2*zeta*T-X*X)
        quadratic = xi**2+X**2/(2*zeta)+zeta*xi**2/2-xi*X
        reduced = quadratic.subs(xi, X/(2+zeta))
        self.assertEqual(s.simplify(reduced), X**2/(zeta*(2+zeta)))

    def test_outer_penalty_inverse_has_uniform_determinant(self):
        alpha, beta, C, v = s.symbols('alpha beta C v', positive=True)
        matrix = s.Matrix([[alpha*v, beta**2], [2, -C*alpha*v]])
        self.assertEqual(s.expand(-matrix.det()), C*alpha**2*v**2+2*beta**2)
        for angle in np.linspace(0, math.pi/2, 31):
            value = .7*math.cos(angle)**2+2*math.sin(angle)**2
            self.assertGreaterEqual(value, .7-1e-14)

    def test_actual_flat_caps_cannot_be_deleted_as_higher_order(self):
        L = 1.3
        leading = C3*(2*L)**1.5
        previous = math.inf
        for h in (.04, .02, .01, .005):
            full = C3*(h*(2*L+h))**1.5
            remainder = (full-leading*h**1.5-leading*3/(4*L)*h**2.5)/h**3
            cap = math.pi*h**3/24  # source time 0 < t < h/2, full disk
            self.assertAlmostEqual(cap/h**3, math.pi/24)
            self.assertLess(abs(remainder), previous)
            previous = abs(remainder)
        self.assertLess(previous, .01)

    def test_actual_focal_metric_regular_tubes_keep_both_tips(self):
        # Physical circle-path actions, not the quadratic cap or Morse model.
        for k in (.08, .04, .02):
            length = 2*math.atan(1/k)
            leading = regular_axis_leading(length)*math.sqrt(k)
            values = [physical_axis_volume(length, k*k*E, order=28)*
                      math.sqrt(k)/(k*k*E)**1.5 for E in (.02, .01, .005)]
            self.assertLess(abs(leading-8/3), .04)
            self.assertTrue(all(.3 < abs((value-leading)/E) < .7
                                for value, E in zip(values, (.02, .01, .005))))
            self.assertLess(abs(values[0]-3*values[1]+2*values[2])/.02**2, 2.)

    def test_union_keeps_overlaps_and_disjoint_components(self):
        single, total = u.cap_union_slice(.1, [0], [1], [.01])
        duplicate, doubled = u.cap_union_slice(.1, [0, 0], [1, 1], [.01, .01])
        self.assertAlmostEqual(single, total)
        self.assertAlmostEqual(duplicate, single)
        self.assertAlmostEqual(doubled, 2*single)
        union, total = u.cap_union_slice(1., [-2, 2], [1, 1], [.01, .01])
        self.assertAlmostEqual(union, total)

    def test_count_free_tip_packing_and_unequal_tubes(self):
        for count in (2, 6, 12):
            radii = np.full(count, 1/(4*count))
            centers = np.arange(count)/count
            k = radii**2
            h = .01*k*radii*radii/count**2
            result = u.tip_packing_diagnostic(centers, k, h, radii)
            self.assertGreater(result['deficit'], 0)
            self.assertLess(result['ratio'], 1.)
        radii = np.array([.15, .025, .02, .015])
        centers = np.array([0., .3, .4, .5])
        k = radii**2
        h = k*radii*radii*np.array([.01, .001, .02, .005])
        result = u.tip_packing_diagnostic(centers, k, h, radii)
        self.assertGreater(result['deficit'], 0)
        self.assertLess(result['ratio'], 1.)

    def test_critical_majorants_and_cut_graph_sum(self):
        k, P = s.symbols('k P', positive=True)
        r = s.sqrt(k/P)
        H = k*k/P
        w0 = k**s.Rational(5, 3)/P
        self.assertEqual(s.simplify(k**s.Rational(7, 3)/r**3),
                         k**s.Rational(5, 6)*P**s.Rational(3, 2))
        self.assertEqual(s.simplify(k*H*w0**(-s.Rational(5, 2))),
                         k**(-s.Rational(7, 6))*P**s.Rational(3, 2))
        self.assertEqual(s.simplify(P*H**2*w0**(-s.Rational(5, 2))),
                         k**(-s.Rational(1, 6))*P**s.Rational(3, 2))
        self.assertEqual(-s.Rational(1, 6)+s.Rational(3, 8), s.Rational(5, 24))
        self.assertLess(sum(2**(-j*5/24) for j in range(1000)), 8.)


class AggregateEnvelopeTests(unittest.TestCase):
    def test_variational_identity_and_inactive_wells(self):
        arrivals = np.array([0., .07, .11, 4.])
        amplitudes = np.array([1., 3., .2, 5.])
        data = u.affine_inverse_data(.3, arrivals, amplitudes,
                                     [[1, 0], [0, 1], [-1, 0], [0, -1]])
        clock = data['clock']
        self.assertAlmostEqual(u.morse_volume(clock, arrivals, amplitudes), .3**1.5)
        self.assertEqual(data['probability'][-1], 0.)
        self.assertAlmostEqual(u.variational_value(.3, arrivals, amplitudes,
                                                  data['probability']), clock)
        rng = np.random.default_rng(177)
        for _ in range(50):
            trial = rng.dirichlet(np.ones(4))
            self.assertGreaterEqual(u.variational_value(.3, arrivals, amplitudes, trial),
                                    clock-1e-13)

    def test_inverse_of_sum_is_not_individual_inverse(self):
        for count in (1, 2, 8, 64):
            clock = u.aggregate_inverse(.2, np.zeros(count), np.ones(count))
            self.assertAlmostEqual(clock, .2/count**(2/3), places=12)
        self.assertLess(u.aggregate_inverse(.2, [0, 0], [1, 1]), .2)

    def test_covariance_matches_finite_differences(self):
        phase = .4
        arrivals = np.array([0., .06, .09])
        angles = np.array([-.3, .2, .7])
        normals = np.column_stack((np.cos(angles), np.sin(angles)))
        amplitudes = np.array([1.2, .8, 2.])
        data = u.affine_inverse_data(phase, arrivals, amplitudes, normals)
        eps = 2e-5
        basis = np.eye(3)

        def f(z):
            return u.aggregate_inverse(phase+z[2], arrivals+normals@z[:2], amplitudes)

        for i in range(3):
            ei = basis[i]*eps
            self.assertAlmostEqual((f(ei)-f(-ei))/(2*eps), data['gradient'][i], places=7)
            for j in range(3):
                ej = basis[j]*eps
                numerical = (f(ei+ej)-f(ei-ej)-f(-ei+ej)+f(-ei-ej))/(4*eps*eps)
                self.assertAlmostEqual(numerical, data['hessian'][i, j], delta=2e-6)
        self.assertLessEqual(np.linalg.eigvalsh(data['hessian']).max(), 1e-12)

    def test_null_covector_variance_not_a_realization_claim(self):
        angles = np.linspace(-.4, .7, 9)
        normals = np.column_stack((np.cos(angles), np.sin(angles)))
        lam = np.arange(1, 10, dtype=float)
        lam /= lam.sum()
        mean = lam@normals
        differences = normals[:, None, :]-normals[None, :, :]
        variance = .5*np.einsum('i,j,ijk,ijk->', lam, lam, differences, differences)
        self.assertAlmostEqual(1-mean@mean, variance, places=14)

    def test_accumulating_curvature_weights_do_not_require_fixed_count(self):
        # Finite abstract Morse heads with increasingly small curvatures and
        # well-separated natural radii. No global potential/metric is inferred.
        for count in (2, 4, 8):
            indices = np.arange(8, 8+count, dtype=float)
            k = np.exp(-indices**2)
            h = 1e-8*min(k)**1.5/count**2
            deficits = h*np.linspace(.6, 1., count)
            amplitudes = 1/np.sqrt(k)
            volume = np.dot(amplitudes, deficits**1.5)
            phase = volume**(2/3)
            self.assertGreater(min(k)/phase_scales(volume, 0)[2], 1000.)
            normals = np.column_stack((np.cos(1/indices), np.sin(1/indices)))
            data = u.affine_inverse_data(phase, -deficits, amplitudes, normals)
            self.assertLess(abs(data['clock'])/h, 2e-12)
            value = u.variational_value(phase, -deficits, amplitudes, data['probability'])
            self.assertLess(abs(value)/h, 2e-12)

    def test_coalescing_good_wells_defeat_unweighted_coarea(self):
        previous = 0.
        scaled = []
        for epsilon in (.1, .03, .01, .003):
            k, h = epsilon**2, epsilon**4*1e-10
            deficits = np.array([h, h/4])
            amplitudes = [1/epsilon]*2
            volume = np.dot(amplitudes, deficits**1.5)
            phase = volume**(2/3)
            self.assertGreater(k/phase_scales(volume, 1)[2], 10000.)
            normals = np.array([[math.cos(epsilon), math.sin(epsilon)],
                                [math.cos(epsilon), -math.sin(epsilon)]])
            data = u.affine_inverse_data(phase, -deficits, amplitudes, normals)
            H = data['hessian']
            ratio = H[2, 2]/np.trace(H[:2, :2])
            expected = (deficits[0]-deficits[1])**2/phase**2/np.sum((normals[0]-normals[1])**2)
            self.assertAlmostEqual(ratio/expected, 1., places=11)
            self.assertGreater(ratio, previous)
            scaled.append(ratio*epsilon**(2/3))
            previous = ratio
        self.assertLess(max(scaled)/min(scaled), 1.01)

    def test_global_null_stiffness_and_cut_graph_coarea(self):
        z, k, b = s.symbols('z k b', real=True)
        chord = s.Matrix([s.cos(z)-1, s.sin(z)])
        pa, pk = s.Matrix([6*b, -2*k]), s.Matrix([-2, 0])
        self.assertEqual(s.expand(chord.dot(pk)), 2-2*s.cos(z))
        slope = -chord.dot(pa)/chord.dot(pk)
        self.assertEqual(s.trigsimp(slope-3*b-k*s.sin(z)/(1-s.cos(z))), 0)
        self.assertEqual(s.det(s.Matrix.hstack(pa, pk)), -4*k)
        for z0 in (.01, .2, 1., 2.):
            self.assertGreater(2*(1-math.cos(z0)), 0)
            self.assertLess(z0*z0/(2*(1-math.cos(z0))), 2.)

    def test_coupled_gap_head_and_genuine_signed_zero(self):
        for ratio in (.01, 1., 100.):
            coefficient = u.opening_coefficient(1., ratio)
            self.assertLess(coefficient, 0.)
            self.assertGreaterEqual(coefficient, -1.)
        for power in (s.Rational(2, 3), s.Rational(4, 3)):
            self.assertEqual((1-3*power/2)*(1-3*power/4), 0)
        self.assertEqual((1-3*s.Integer(2)/2)*(1-3*s.Integer(2)/4), 1)
        # Absolute convergent radial test after d=h*y, not a divergent head.
        for amplitude in (1., 3.):
            value = quad(lambda z: z**(1/3)*float(kernel3(amplitude*z)),
                         0, np.inf, epsabs=2e-11, epsrel=2e-11)[0]
            self.assertAlmostEqual(value, 0., delta=2e-11)

    def test_smooth_threshold_cantor_control_has_positive_residual_measure(self):
        intervals = [(s.Rational(0), s.Rational(1))]
        for level in range(1, 9):
            gap = s.Rational(1, 4**level)
            updated = []
            for lo, hi in intervals:
                middle = (lo+hi)/2
                self.assertGreater(hi-lo, gap)
                updated.extend([(lo, middle-gap/2), (middle+gap/2, hi)])
            intervals = updated
            self.assertEqual(len(intervals), 2**level)
            self.assertEqual(sum(hi-lo for lo, hi in intervals),
                             s.Rational(1, 2)+s.Rational(1, 2**(level+1)))
        # Fixed derivative orders of the gap bumps decay faster than scaling
        # losses. This finite check is not a numerical singular-measure proof.
        for derivative in (0, 4, 10, 20):
            logs = [-1/ell**2-derivative*math.log(ell) for ell in (.1, .05, .025)]
            self.assertTrue(all(x > y for x, y in zip(logs, logs[1:])))

    def test_invalid_inputs_are_rejected(self):
        calls = [lambda: u.aggregate_inverse(-1, [0], [1]),
                 lambda: u.aggregate_inverse(1, [], []),
                 lambda: u.morse_volume(math.inf, [0], [1]),
                 lambda: u.variational_value(1, [0, 1], [1, 1], [.2, .2]),
                 lambda: u.affine_inverse_data(0, [0], [1], [[1, 0]]),
                 lambda: u.cap_union_slice(0, [0], [1], [1]),
                 lambda: u.tip_packing_diagnostic([0, .01], [1, 1], [.001, .001], [.1, .1]),
                 lambda: u.opening_coefficient(0, 1)]
        for call in calls:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
