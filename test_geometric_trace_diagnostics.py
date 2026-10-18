"""Finite GT identities and abstract controls; not geometric limit certificates."""
from fractions import Fraction
from functools import lru_cache
import math
import unittest

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
import sympy as s

from dimension_kernels import Z, factor_count, interval_coefficient, kernel_polynomial, mellin_factor
from geometric_trace_diagnostics import (
    clock_volume_jet, density_jet_exponent, first_filter_slope,
    ramp_log_derivative, slow_control, slow_control_filter,
)
from intrinsic_union_response import (
    filter_coefficients, filter_constant, filtered_pair, filtered_power,
    geometric_filter, laplace_weight,
)


@lru_cache(maxsize=None)
def kernel(d):
    return s.lambdify(Z, kernel_polynomial(d)*s.exp(-Z), 'numpy')


class GeometricTraceTests(unittest.TestCase):
    def test_ramp_derivative_and_its_actual_endpoint_sides(self):
        for d in (2, 3, 4, 7, 8):
            for r in (.0001, .07, .4, .9):
                h = 1e-5
                numeric = (geometric_filter(d, r*math.exp(h))
                           -geometric_filter(d, r*math.exp(-h)))/(2*h)
                self.assertAlmostEqual(ramp_log_derivative(d, r), numeric, delta=3e-9)
            self.assertAlmostEqual(ramp_log_derivative(d, 1-1e-8), -1., delta=1e-6)
            self.assertEqual(ramp_log_derivative(d, 1), 0.)  # assigned a.e. value
            self.assertEqual(ramp_log_derivative(d, 0), 0.)
            self.assertEqual(ramp_log_derivative(d, 2), 0.)

    def test_critical_trace_normalization_includes_full_laplace_moment(self):
        for d in range(2, 10):
            b, m = 1+2/d, factor_count(d)
            moment = quad(lambda z: z**b*laplace_weight(d, z), 0, np.inf,
                          epsabs=2e-9, epsrel=2e-11)[0]
            exact = (b+1)**(m+1)*math.gamma(b+1)
            self.assertAlmostEqual(moment/exact, 1., delta=2e-10)
            T, beta = 2.7, 1.3
            L = -T/(beta*float(filter_constant(d))*exact)
            self.assertAlmostEqual(-beta*float(filter_constant(d))*moment*L, T, delta=1e-9)

    def test_logarithmic_modes_at_and_away_from_simple_zeros(self):
        x = s.symbols('x', positive=True)
        rho, reference = 1.7, 2.3
        for d in (2, 3, 4, 7):
            expression = s.gamma(x+1)*mellin_factor(d, x)
            for power in (s.Rational(7, 10), s.Rational(2, d)):
                p = float(power)
                for degree in (0, 1, 2):
                    moments = [float(s.diff(expression, x, j).subs(x, power))
                               for j in range(degree+1)]
                    expected = rho**(-p)*sum(math.comb(degree, j)*moments[j]
                               *(-math.log(rho*reference))**(degree-j)
                               for j in range(degree+1))
                    def integrand(z):
                        log = math.log(z/(rho*reference))
                        derivative = p*log**degree
                        if degree:
                            derivative += degree*log**(degree-1)
                        return rho**(-p)*z**(p-1)*derivative*kernel(d)(z)
                    actual = math.fsum(quad(integrand, lo, hi, epsabs=1e-9,
                                          epsrel=1e-9)[0] for lo, hi in ((0, 1), (1, np.inf)))
                    self.assertAlmostEqual(actual, expected, delta=3e-7)

    def test_even_point_reference_change_is_a_true_null_power(self):
        x = s.symbols('x')
        for d in (2, 4, 6, 8):
            m = factor_count(d)
            f = s.prod(x-s.Rational(2*j, d) for j in range(1, m+1))/(x+1)**(m+1)
            self.assertEqual(f.subs(x, 1), 0)
            self.assertNotEqual(s.diff(f, x).subs(x, 1), 0)
            self.assertEqual(mellin_factor(d, 1), 0)
            self.assertNotEqual(s.diff(mellin_factor(d, x), x).subs(x, 1), 0)
            self.assertEqual(mellin_factor(d, 1+s.Rational(2, d)), 0)

    def test_constant_primitive_tail_cannot_be_truncated_at_pair_support(self):
        for d in (2, 3, 7):
            rho, volume = .8, .3
            full = filtered_pair(d, rho, [volume], [1.])
            truncated = quad(lambda z: laplace_weight(d, z)
                             *geometric_filter(d, rho*volume/z), 0, rho*volume)[0]
            self.assertEqual(truncated, 0.)
            self.assertAlmostEqual(full, float(kernel(d)(rho*volume)), delta=1e-10)
            self.assertGreater(abs(full-truncated), .02)

    def test_null_index_form_coefficient_matches_flat_normalization(self):
        # Arithmetic check of the general screen integral, not a new example theorem.
        for d in range(2, 10):
            p = s.Rational(d, 2)
            omega = s.pi**((s.Integer(d)-2)/2)/s.gamma(p)
            beta = s.gamma(p)**2/s.gamma(2*p)
            coefficient = omega*beta/d
            self.assertEqual(s.simplify(coefficient-interval_coefficient(d)), 0)
            L, eta = 1.4, .7
            A = float(2**p*coefficient)*(L*eta)**float(p)
            rescaled = float(2**p*coefficient)*((3*L)*(eta/3))**float(p)
            self.assertAlmostEqual(A, rescaled, places=12)

    def test_clock_coarea_keeps_route_switch_openings_and_physical_cap(self):
        # Finite scalar clock control only; not a claimed Lorentzian realization.
        arrivals = np.array([.05, .15, .2])
        offsets = np.array([0., .03, .08])
        weights = np.array([.3, .4, .7])
        derivatives = np.array([1+arrivals, np.ones(3)])
        def departure(t):
            return np.maximum(t, 1.4*t-.25)-offsets
        def volume(t):
            return clock_volume_jet(arrivals, departure(t), derivatives, weights)
        def slope(t):
            b = departure(t)
            return float(weights@((b > arrivals)*(1+b)))*(1 if t < .625 else 1.4)
        lo, hi, rho = .12, .9, 2.1
        times = [lo, .18, .28, .625, hi]
        phases = list(map(volume, times))
        def inverse(v):
            return brentq(lambda t: volume(t)-v, lo, hi, xtol=2e-14)
        def density(v):
            if not phases[0] < v < phases[-1]:
                return 0.
            t = inverse(v)
            return (1+t)/slope(t)
        direct = math.fsum(quad(lambda t: (1+t)*kernel(4)(rho*volume(t)), a, b)[0]
                           for a, b in zip(times, times[1:]))
        coarea = math.fsum(quad(lambda v: kernel(4)(rho*v)*density(v), a, b)[0]
                           for a, b in zip(phases, phases[1:]))
        mass = math.fsum(quad(density, a, b)[0] for a, b in zip(phases, phases[1:]))
        self.assertAlmostEqual(coarea, direct, delta=2e-12)
        self.assertAlmostEqual(mass, hi+hi**2/2-lo-lo**2/2, delta=2e-12)
        self.assertEqual(density(phases[-1]+.1), 0.)
        self.assertGreater(slope(.625+1e-8), slope(.625-1e-8))

    def test_density_jet_is_whole_width_not_sum_of_route_volumes(self):
        a, w = [.1, .2], [.4, .7]
        routes = np.array([[.5, .7], [.6, .4]])
        derivatives = np.array([[1.1, 1.2], [1., 1.]])
        united = clock_volume_jet(a, routes.max(axis=0), derivatives, w)
        separate = sum(clock_volume_jet(a, b, derivatives, w) for b in routes)
        self.assertGreater(separate, united)
        self.assertEqual(clock_volume_jet(a, [0., .1], derivatives, w), 0.)

    def test_interior_density_taylor_error_and_critical_margin(self):
        a, weights = np.array([-.2, .1, .5]), np.array([.3, .4, .7])
        for d in range(2, 10):
            k = d//2
            eta = density_jet_exponent(d)
            self.assertGreater(eta, 1)
            self.assertEqual(eta, Fraction(2*(k+1), d))
            for h in (.2, .07):
                width = h*np.array([.3, .8, 1.])
                exact = float(weights@(np.exp(a)*np.expm1(width)))
                jet = clock_volume_jet(a, a+width, np.tile(np.exp(a), (k+1, 1)), weights)
                self.assertGreater(exact, jet)
                self.assertLess((exact-jet)/exact, h**(k+1))

    def test_signed_scale_increment_formula_not_unsigned_bound(self):
        for d in (2, 3, 4, 7):
            alpha, v, extra = 2/d, .08, .37
            base = lambda x: geometric_filter(d, math.exp(-x))*math.exp(-alpha*x)
            full = v**alpha*quad(lambda x: base(x)*(1+.2*v**extra*math.exp(-extra*x)),
                                 0, np.inf, epsabs=1e-11)[0]
            increment = .2*v**(alpha+extra)*quad(lambda x: base(x)*(math.exp(-extra*x)-1),
                                                0, np.inf, epsabs=1e-11)[0]
            expected = .2*v**(alpha+extra)*filtered_power(d, alpha+extra)/(alpha+extra)
            self.assertAlmostEqual(full, increment, delta=2e-11)
            self.assertAlmostEqual(full, expected, delta=2e-11)

    def test_critical_phase_stability_samples_include_moving_filter_edge(self):
        # Continuous positive phase measure with its first-order bound; not spacetime data.
        for d in (2, 3, 7):
            alpha, eta = 2/d, float(density_jet_exponent(d))
            for v in (.03, .01, .003):
                scale = v**eta
                def difference(x):
                    r = math.exp(-x)
                    return alpha*math.exp(-alpha*x)*(geometric_filter(d, r*(1+.3*scale*r**eta))
                                                    -geometric_filter(d, r))/scale
                ratio = quad(difference, 0, np.inf, epsabs=3e-9, epsrel=3e-8)[0]
                self.assertLess(abs(ratio), 1.)
                self.assertGreater(ramp_log_derivative(d, .3)**2, 0.)

    def test_slow_control_is_increasing_concave_with_exact_nonzero_slope(self):
        x = s.symbols('x')
        for d in (2, 3, 4, 7, 12):
            m = factor_count(d)
            f = s.prod(x-s.Rational(2*j, d) for j in range(1, m+1))/(x+1)**(m+1)
            expected = s.diff(f, x).subs(x, s.Rational(2, d))
            actual = first_filter_slope(d)
            self.assertEqual(s.Rational(actual.numerator, actual.denominator), expected)
            self.assertNotEqual(actual, 0)
            for L in (9., 20., 50.):
                u, first, second = slow_control(d, math.exp(-L))
                self.assertGreater(u, 0)
                self.assertGreater(first, 0)
                self.assertLess(second, 0)

    def test_slow_filter_matches_repeated_averages_not_a_fitted_power(self):
        for d in (2, 3, 7):
            v, alpha = math.exp(-12), 2/d
            sign, L = (-1 if d == 2 else 1), -math.log(v)
            coefficients = filter_coefficients(d)
            direct = math.fsum(float(c)*quad(lambda y: math.exp(-(1+alpha)*y)*y**k
                               /math.factorial(k)/(L+y), 0, np.inf,
                               epsabs=1e-12, epsrel=1e-12)[0]
                               for k, c in enumerate(coefficients))
            actual = slow_control_filter(d, v)/(sign*v**alpha)
            self.assertAlmostEqual(actual, direct, delta=3e-12)
            ratios = [slow_control_filter(d, math.exp(-q))*q**2
                      /(sign*math.exp(-q*alpha)*float(first_filter_slope(d))) for q in (80., 300.)]
            self.assertLess(abs(ratios[1]-1), abs(ratios[0]-1))
            self.assertLess(abs(ratios[1]-1), .12)

    def test_invalid_inputs_and_nonpositive_jet_rejected(self):
        calls = [lambda: ramp_log_derivative(1, .3), lambda: ramp_log_derivative(3, -.1),
                 lambda: ramp_log_derivative(3, np.nan), lambda: density_jet_exponent(True),
                 lambda: clock_volume_jet([0], [1], [[1], [-4]], [1]),
                 lambda: clock_volume_jet([0], [1], [[0]], [1]),
                 lambda: clock_volume_jet([0], [1, 2], [[1]], [1]),
                 lambda: clock_volume_jet([0], [1], [[1]], [-1]),
                 lambda: clock_volume_jet([0], [np.inf], [[1]], [1]),
                 lambda: slow_control(3, 0), lambda: slow_control(3, .1),
                 lambda: slow_control_filter(3, np.nan), lambda: first_filter_slope(1)]
        for call in calls:
            with self.assertRaises(ValueError):
                call()


if __name__ == '__main__':
    unittest.main()
