"""Diagnostics for the written Klein-bottle proof, not proof certification."""

import itertools
import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as sp

from dimension_kernels import (
    Z, action_constants, interval_coefficient, kernel_polynomial,
)
from full_partner_globalization import primitive_response


T = 21 / 20


def images(point, radius=3):
    x, y = point
    return np.array([(x + m, (-1) ** m * y + 2 * n)
                     for m in range(-radius, radius + 1)
                     for n in range(-radius, radius + 1)])


def phases(tau, x, y, w, b2=0):
    return np.array([
        tau * tau - (1 + x) ** 2 - (w - y) ** 2 - b2,
        tau * tau - (-1 + x) ** 2 - (w - y) ** 2 - b2,
        tau * tau - x * x - (1 - w - y) ** 2 - b2,
        tau * tau - x * x - (-1 - w - y) ** 2 - b2,
    ])


class FlatKleinBottleObstructionTest(unittest.TestCase):
    def test_group_and_complete_four_lift_enumeration(self):
        rng = np.random.default_rng(175)
        for _ in range(100):
            point = rng.normal(size=2)
            g = lambda a: np.array([a[0] + 1, -a[1]])
            h = lambda a: a + [0, 2]
            gi = lambda a: np.array([a[0] - 1, -a[1]])
            np.testing.assert_allclose(g(h(gi(point))), point + [0, -2])
            np.testing.assert_allclose(g(g(point)), point + [2, 0])
        for center in (.5, 1.5):
            source = np.array([.17, center])
            target = np.array([1.17, center])
            distances = np.linalg.norm(images(target) - source, axis=1)
            self.assertEqual(np.count_nonzero(distances < T), 4)
            np.testing.assert_allclose(np.sort(distances)[:4], np.ones(4))
        for _ in range(300):
            source = rng.uniform([0, 0], [1, 2])
            target = rng.uniform([0, 0], [1, 2])
            distances = np.linalg.norm(images(target) - source, axis=1)
            self.assertLessEqual(np.count_nonzero(distances < T), 4)

    def test_exact_phase_jacobian_and_fold_not_product(self):
        tau, x, y, w = sp.symbols('tau x y w', real=True)
        ss = sp.Matrix([
            tau**2 - (1+x)**2 - (w-y)**2,
            tau**2 - (-1+x)**2 - (w-y)**2,
            tau**2 - x**2 - (1-w-y)**2,
            tau**2 - x**2 - (-1-w-y)**2,
        ])
        jac = ss.jacobian([tau, x, y, w])
        self.assertEqual(sp.factor(jac.det()), -128 * tau * (y-w))
        self.assertEqual(jac.subs({tau: 1, x: 0, y: 0, w: 0}).rank(), 3)
        lam = sp.Matrix([[1, 1, -1, -1]])
        self.assertEqual(sp.expand((lam * ss)[0]), 8*y*w)
        # Holding the third linear phase coordinate fixes w=-y.
        self.assertEqual(sp.expand((lam * ss)[0].subs(w, -y)), -8*y*y)

    def test_exact_density_both_branches_and_both_centers(self):
        rng = np.random.default_rng(190)
        for _ in range(100):
            # Near the fold, D subtracts nearly equal phase sums. Retain
            # guard digits rather than weakening the density tolerance.
            x, y, w = rng.uniform(-.015, .015, size=3).astype(np.longdouble)
            if abs(y-w) < 1e-4:
                continue
            tau = np.longdouble('1.02')
            ss = phases(tau, x, y, w)
            disc = (ss[2]-ss[3])**2/8 - (ss[0]+ss[1]-ss[2]-ss[3])
            self.assertAlmostEqual(disc, 2*(y-w)**2, delta=1e-15)
            aa = (1+(ss[2]+ss[3])/2
                  + ((ss[0]-ss[1])**2+(ss[2]-ss[3])**2)/16)
            self.assertAlmostEqual(aa, tau*tau, delta=1e-15)
            # Before spectator integration, F=(T-tau)/(2*tau).
            direct = 2 * 2 * (T-tau)/(128*tau*abs(y-w))
            pushed = (T-tau)/(2*tau)/(8*math.sqrt(2))*disc**(-.5)
            self.assertAlmostEqual(direct, pushed, delta=2e-10*direct)
            self.assertNotAlmostEqual(direct, pushed/2, delta=.2*direct)

    def test_closing_fibres_retain_both_endpoint_times(self):
        for p in (2, 3, 6):
            area = 2 * math.pi**(p/2) / math.gamma(p/2)
            for a in (.99, 1, 1.01):
                radius = math.sqrt(T*T-a)
                direct = area/2 * quad(
                    lambda r: r**(p-1)*(T/math.sqrt(a+r*r)-1),
                    0, radius, epsabs=1e-15)[0]
                rescaled = area/2*(T*T-a)**(p/2+1)*quad(
                    lambda z: z**(p-1)*(1-z*z)
                    / (math.sqrt(a+(T*T-a)*z*z)
                       * (T+math.sqrt(a+(T*T-a)*z*z))),
                    0, 1, epsabs=1e-15)[0]
                self.assertGreater(direct, 0)
                self.assertAlmostEqual(direct, rescaled, delta=1e-11*direct)
                omitted = area/2 * quad(
                    lambda r: r**(p-1)*T/math.sqrt(a+r*r),
                    0, radius, epsabs=1e-15)[0]
                self.assertGreater(omitted, 10*direct)

    def test_all_fifteen_sectors_against_independent_gamma_difference(self):
        alpha = sp.Rational(7, 2)
        lam = (1, 1, -1, -1)
        t = sp.symbols('t', positive=True)
        total = 0
        all_positive = None
        for k in range(1, 5):
            for active in itertools.combinations(range(4), k):
                inactive = [i for i in range(4) if i not in active]
                m = 4-k
                a = sum(lam[i] == 1 for i in active)
                b = k-a
                exponent = sp.Rational(2*m-1, 2)
                if b == 0:
                    integral = 0
                elif a == 0:
                    integral = 1/(sp.factorial(k-1)*alpha)
                else:
                    poly = sp.Poly(sp.expand((1-t)**(a-1)*(1+t)**(b-1)), t)
                    integral = sum(coef/(exponent+power[0]+1)
                                   for power, coef in poly.terms())
                    integral /= 2**(k-1)*sp.factorial(a-1)*sp.factorial(b-1)*alpha
                coefficient = ((-1)**m * sp.gamma(sp.Rational(1, 2))
                               / sp.gamma(m+sp.Rational(1, 2))
                               / math.prod(lam[i] for i in inactive))
                total += coefficient*integral
                if k == 4:
                    all_positive = integral
        self.assertEqual(sp.simplify(total), sp.Rational(22, 105))
        self.assertEqual(all_positive, sp.Rational(2, 35))
        p_alpha = math.prod(alpha-i for i in range(4))
        gamma_difference = (sp.gamma(alpha+2)+sp.gamma(alpha+1))/4
        independent = gamma_difference/(p_alpha*sp.gamma(alpha+1))
        self.assertEqual(sp.simplify(total-independent), 0)
        self.assertNotEqual(total, all_positive)

    def test_signed_fractional_response_at_and_above_dimension_five(self):
        alpha = 3.5
        for d in (5, 6, 7, 8, 11):
            q = d/2
            rho = 11.
            c = float(interval_coefficient(d))
            beta = float(action_constants(d)[1])
            product = math.prod(1-alpha/k for k in range(1, d//2+2))
            self.assertLess(product, 0)
            expected = (-beta*c**(-alpha/q)*math.gamma(1+alpha/q)
                        * product*rho**(1-5/d))
            actual = float(primitive_response(d, alpha, rho))
            self.assertAlmostEqual(actual, expected, delta=2e-12*expected)
            self.assertGreater(actual, 0)
            ratio = float(primitive_response(d, alpha, 2*rho))/actual
            self.assertAlmostEqual(ratio, 2**(1-5/d), places=12)
        # Independent signed-kernel integration at the new critical dimension.
        d = 5
        q = 2.5
        c = float(interval_coefficient(d))
        beta = float(action_constants(d)[1])
        kernel = sp.lambdify(Z, kernel_polynomial(d)*sp.exp(-Z), 'math')
        integral = quad(lambda t: 2*t**6*kernel(t**d), 0, 150**(1/d),
                        epsabs=2e-12, epsrel=2e-12, limit=200)[0]
        direct = -beta*alpha*c**(-alpha/q)*integral
        self.assertAlmostEqual(direct, float(primitive_response(d, alpha, 11)),
                               delta=2e-10*abs(direct))

    def test_physical_union_against_independent_quotient_distances(self):
        source = np.array([.17, .5])
        target = np.array([1.17, .5])
        tau = 1.02
        targets = images(target)
        targets = targets[np.linalg.norm(targets-source, axis=1) <= tau]
        self.assertEqual(len(targets), 4)
        rng = np.random.default_rng(211)
        points = [(source, .01)]
        points += [(rng.uniform([0, 0], [1, 2]), rng.uniform(0, tau))
                   for _ in range(150)]
        multiplicities = []
        physical_flags = []
        for point, time in points:
            lifts = images(point)
            left = np.linalg.norm(lifts-source, axis=1) <= time
            route = [np.any(left & (np.linalg.norm(lifts-end, axis=1) <= tau-time))
                     for end in targets]
            physical = (np.min(np.linalg.norm(images(point)-source, axis=1)) <= time
                        and np.min(np.linalg.norm(images(target)-point, axis=1))
                        <= tau-time)
            self.assertEqual(any(route), physical)
            multiplicities.append(sum(route))
            physical_flags.append(physical)
        count = multiplicities[0]
        self.assertEqual(count, 4)
        self.assertNotEqual(count, int(physical_flags[0]))
        self.assertNotEqual(count-math.comb(count, 2), int(physical_flags[0]))


if __name__ == '__main__':
    unittest.main()
