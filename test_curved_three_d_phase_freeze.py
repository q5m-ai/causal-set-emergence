"""Finite identity/calibration checks for PF3, not physical action convergence.

The atomic and logarithmic ramps below are abstract finite measures. Neither
is asserted to be an interval distribution of an admitted spacetime.
"""

import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

from curved_three_d_union import aggregate_inverse


def _kernel(z):
    v = z**1.5
    return (1-27*v/8+9*v*v/8)*math.exp(-v)


def _kernel_second(z):
    v = z**1.5
    return 3/32*z**-.5*math.exp(-v)*(-35+285*v-198*v*v+27*v**3)


class CollectiveMatchingChecks(unittest.TestCase):
    def test_softer_circular_cut_second_derivative(self):
        a = s.symbols('a', real=True)
        k, ell, b, u = (s.Function(name)(a) for name in ('k', 'ell', 'b', 'u'))
        c = s.symbols('c', real=True)
        d = u-a
        slope = 3*b+k*s.cot(d/2)
        derivative = s.diff(slope, a).subs({
            s.diff(k, a): slope, s.diff(b, a): 4*c+k/3,
            s.diff(u, a): -k/ell})
        expected = 12*c+3*b*s.cot(d/2)+(3*k/2+k*k/(2*ell))/s.sin(d/2)**2
        self.assertEqual(s.trigsimp(s.factor(derivative-expected)), 0)
        # Verify the reciprocal speed from the secondary stationary equation.
        secondary_tangent = s.Matrix([-s.sin(d), s.cos(d)])
        endpoint_speed = -2*k*s.Matrix([s.cot(d/2), 1])
        self.assertEqual(s.trigsimp(s.expand_trig(
            (secondary_tangent.dot(endpoint_speed)-2*k).rewrite(s.sin))), 0)

    def test_six_root_equal_global_minima_stiffness(self):
        z, a, b = s.symbols('z a b', real=True)
        G = 1+z*z
        D = z*z*(z-a)**2*(z-b)**2*G
        for root, expected in ((0, a*a*b*b*G.subs(z, 0)),
                               (a, a*a*(a-b)**2*G.subs(z, a)),
                               (b, b*b*(b-a)**2*G.subs(z, b))):
            self.assertEqual(s.simplify(D.subs(z, root)), 0)
            self.assertEqual(s.simplify(s.diff(D, z).subs(z, root)), 0)
            self.assertEqual(s.simplify(s.diff(D, z, 2).subs(z, root)/2-expected), 0)
        # A nonzero losing defect destroys the double-root premise.
        self.assertNotEqual((D+z*z).subs(z, a), 0)

    def test_conditional_vertex_budget_algebra(self):
        k0, k1, k2, a, b, c = s.symbols('k0 k1 k2 a b c', positive=True)
        coefficient = (k0*k1*k2)**s.Rational(1, 3)/(a*b*c)
        jumps = (k0*c/(a*b), k1*b/(a*c), k2*a/(b*c))
        self.assertEqual(s.simplify(coefficient**3/s.prod(jumps)-(a*b*c)**-2), 0)
        # Only conditional scale arithmetic, not a derived physical head or
        # allocation. With a<=b~c and a,b<=1, the six-root upper scale fits.
        for small, large in ((.01, .1), (.03, .03), (.1, .7)):
            self.assertLessEqual((small*large)**(7/3), (small*large*large)**(4/3))

    def test_pairwise_openings_overcount_collective_inverse(self):
        w = .02
        for count in (3, 8, 32):
            whole = aggregate_inverse(w, np.zeros(count), np.ones(count))-w
            pair_sum = (count-1)*(aggregate_inverse(w, [0, 0], [1, 1])-w)
            self.assertAlmostEqual(whole/w, count**(-2/3)-1)
            self.assertLess(pair_sum, whole)
            # Telescoping is exact only when the increment sees the aggregate
            # built so far, rather than repeatedly starting with one primary.
            telescoped = sum(w*((n+1)**(-2/3)-n**(-2/3))
                             for n in range(1, count))
            self.assertAlmostEqual(telescoped, whole)
        self.assertLess(pair_sum, -w)


class CompleteSignedIdentityChecks(unittest.TestCase):
    def test_signed_increment_identity_retains_linear_tail(self):
        phases = np.array([.04, .11, .23])
        masses = np.array([.2, .7, .4])
        t = .13

        def ramp(w):
            return float(masses@np.maximum(w-phases, 0))

        edges = [0., *(phases/t), np.inf]

        def integral(f):
            return sum(quad(f, lo, hi, epsabs=2e-10, epsrel=2e-10)[0]
                       for lo, hi in zip(edges, edges[1:]))

        direct = sum(m*_kernel(p/t) for p, m in zip(phases, masses))
        ramp_integral = integral(lambda z: ramp(t*z)*_kernel_second(z))
        self.assertAlmostEqual(ramp_integral, t*direct, places=11)
        # The zero polynomial moments permit any fixed finite subtraction.
        # No first-coefficient claim about this atomic control is needed.
        for b1 in (0., .3, 1.):
            def E(w):
                return (ramp(w)-b1*w*w/2)/w**3
            increment = integral(lambda z: z**3*_kernel_second(z)*(E(t*z)-E(t)))
            self.assertAlmostEqual(increment, direct/t**2, places=8)
        omitted_tail = quad(lambda z: ramp(t*z)*_kernel_second(z),
                            phases[-1]/t, np.inf, epsabs=1e-11)[0]
        self.assertGreater(abs(omitted_tail), 1e-4)

    def test_log_moment_not_annihilated(self):
        z = s.symbols('z', positive=True)
        v = z**s.Rational(3, 2)
        F = (1-27*v/8+9*v*v/8)*s.exp(-v)
        explicit = s.Rational(3, 32)*z**-s.Rational(1, 2)*s.exp(-v)*(
            -35+285*v-198*v*v+27*v**3)
        self.assertEqual(s.simplify(s.diff(F, z, 2)-explicit), 0)
        # Log-coordinate quadrature checks PF3.7. Finite panels are a
        # diagnostic, not the proof of the infinite-tail asymptotics.
        def H(logz):
            return math.exp(4*logz)*_kernel_second(math.exp(logz))
        mass = quad(H, -20, 4, epsabs=1e-11)[0]
        first = quad(lambda x: x*H(x), -20, 4, epsabs=1e-11)[0]
        self.assertAlmostEqual(mass, 0., places=10)
        self.assertAlmostEqual(first, 2*math.gamma(4/3), places=10)
        errors = []
        for u in (20., 40., 80., 160.):
            inc = quad(lambda x: H(x)*(1/(u-x)-1/u), -20, 4, epsabs=1e-12)[0]
            errors.append(abs(u*u*inc-first))
        self.assertTrue(all(a > b for a, b in zip(errors, errors[1:])))
        self.assertLess(errors[-1], .05)

    def test_positive_finite_log_ramp(self):
        w = s.symbols('w', positive=True)
        L = s.log(1/w)
        expression = w*w/2+w**3/L
        density = 1+w*(6/L+5/L**2+2/L**3)
        self.assertEqual(s.simplify(s.diff(expression, w, 2)-density), 0)
        w0 = math.exp(-4)
        q0 = w0*w0/2+w0**3/4
        slope = w0+3*w0*w0/4+w0*w0/16

        def q(w):
            return w*w/2+w**3/math.log(1/w) if w <= w0 else q0+(w-w0)*slope

        def density_at(v):
            if v == 0:
                return 1.
            log = math.log(1/v)
            return 1+v*(6/log+5/log**2+2/log**3)

        for v in np.linspace(0, w0, 101):
            self.assertGreater(density_at(v), 0)
        self.assertAlmostEqual(quad(density_at, 0, w0, epsabs=1e-13,
                                   epsrel=1e-12)[0], slope, places=11)
        for w in (w0/2, w0, 2*w0, 1.):
            actual_ramp = quad(lambda v: (w-v)*density_at(v), 0, min(w, w0),
                               epsabs=1e-12)[0]
            self.assertAlmostEqual(actual_ramp, q(w), places=11)


if __name__ == '__main__':
    unittest.main()
