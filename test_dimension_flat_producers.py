"""Finite regressions, NOT proof certificates for the written geometric theorem."""

import math
import unittest

from scipy.integrate import quad
import sympy as s

from dimension_flat_producers import (
    basis_responses, capsule_angular_jet, capsule_density, capsule_geometric_terms,
    capsule_overlap, constant_singular_coefficient, log_moment, short_bases,
    short_monomial, sphere_monomial, sufficient_regularity,
)
from dimension_kernels import (
    Z, action_constants, interval_coefficient, kernel_polynomial, sphere_area,
    transverse_moment,
)
from dimension_short_56 import short_basis56_symbolic


class DimensionFlatProducerTest(unittest.TestCase):
    def test_regularity_and_invalid_inputs(self):
        self.assertEqual([sufficient_regularity(d) for d in range(2, 11)],
                         [3, 3, 3, 4, 4, 5, 5, 6, 6])
        for d in (True, 1, 2.5, "4"):
            with self.assertRaises(ValueError):
                sufficient_regularity(d)
        with self.assertRaises(ValueError):
            short_monomial(5, -1, 0, 0.1, 1)
        with self.assertRaises(ValueError):
            log_moment(4, -1)
        with self.assertRaises(ValueError):
            sphere_monomial(3, (2,))
        for args in ((2, 0.1, (0.2,)), (3, 0.2, (0.1,))):
            with self.assertRaises(ValueError):
                capsule_overlap(*args)
        for slope in (0, 1, math.nan):
            with self.assertRaises(ValueError):
                capsule_overlap(2, 0, (0,), steepness=slope)
        with self.assertRaises(ValueError):
            capsule_density(2, 0, 0.1)

    def test_full_sphere_moments_including_two_atoms(self):
        for d in (*range(2, 10), 20, 21):
            n = d-1
            self.assertEqual(sphere_monomial(d, (0,)*n), sphere_area(d))
            self.assertEqual(sphere_monomial(d, (1,)+(0,)*(n-1)), 0)
            self.assertEqual(s.simplify(sphere_monomial(d, (2,)+(0,)*(n-1))
                                       - sphere_area(d)/n), 0)
            if n > 1:
                self.assertEqual(sphere_monomial(d, (1, 1)+(0,)*(n-2)), 0)
        self.assertEqual(sphere_monomial(2, (4,)), 2)

    def test_all_dimension_laurent_algorithm_and_both_endpoints(self):
        x, L, v = s.symbols("sigma delta v", positive=True)
        t, r = (v+x/v)/2, (v-x/v)/2
        for d in (*range(2, 10), 12, 13):
            basis = short_bases(d, x, L)
            for actual, monomial in zip(basis, (1, t, t*t, r*r)):
                primitive = s.integrate(s.expand(r**(d-2)/(2*v)*monomial), v)
                independent = primitive.subs(v, L)-primitive.subs(v, s.sqrt(x))
                self.assertEqual(s.simplify(actual-independent), 0, (d, monomial))
                self.assertEqual(s.simplify(actual.subs(x, L**2)), 0)
            self.assertEqual(s.simplify(basis[1]-(L-x/L)**(d-1)/(2**d*(d-1))), 0)
            self.assertEqual(s.simplify(basis[2]-basis[3]-x*basis[0]), 0)
            self.assertEqual(s.simplify((d-1)*basis[2]+basis[3]
                                       -(L+x/L)*(L-x/L)**(d-1)/2**(d+1)), 0)
            alpha = constant_singular_coefficient(d)
            singular = alpha*x**s.Rational(d-2, 2)
            if not d % 2:
                singular *= s.log(x)
            self.assertTrue(s.expand(basis[0]-singular).is_polynomial(x))
        for d in (5, 6):
            for actual, old in zip(short_bases(d, x, L), short_basis56_symbolic(d, x, L)):
                self.assertEqual(s.simplify(actual-old), 0)
        self.assertEqual(short_bases(2, x, L)[0], s.log(L)/2-s.log(x)/4)

    def test_signed_recurrence_moments_and_physical_normalization(self):
        a = s.Symbol("a", positive=True)
        for d in (*range(2, 11), 15, 16, 25, 26):
            polynomial = kernel_polynomial(d)
            # Independently integrate each polynomial coefficient with Gamma(a+k).
            gamma_multiplier = s.expand(sum(polynomial.coeff(Z, k)*s.rf(a, k)
                                             for k in range(d//2+2)))
            for j in range(d//2+1):
                self.assertEqual(gamma_multiplier.subs(a, s.Rational(2*(j+1), d)), 0)
            q = s.Rational(d, 2)
            if not d % 2:
                for order in (q-1, q):
                    exponent = 2*(order+1)/d
                    direct_log = (s.Rational(4, d*d)*s.gamma(exponent)
                                  * s.diff(gamma_multiplier, a).subs(a, exponent))
                    self.assertEqual(s.simplify(direct_log-log_moment(d, order)), 0)
            else:
                direct = (s.Rational(2, d)*s.gamma(1+s.Rational(2, d))
                          * gamma_multiplier.subs(a, 1+s.Rational(2, d)))
                self.assertEqual(s.simplify(direct-transverse_moment(d, q)), 0)
            point, time2, radius2 = basis_responses(d)
            ad, beta = action_constants(d)
            self.assertEqual(s.simplify(point-ad/beta), 0)
            self.assertEqual(s.simplify(time2-2/sphere_area(d)), 0)
            self.assertEqual(s.simplify(radius2+2*(d-1)/sphere_area(d)), 0)
        self.assertNotEqual(action_constants(2)[0], action_constants(2)[1])
        self.assertEqual(basis_responses(5)[0], s.Rational(8, 3))
        self.assertEqual(basis_responses(6)[0], s.Rational(5, 2))

    def test_actual_probe_subtraction_keeps_moving_endpoint(self):
        x, L, v = s.symbols("sigma delta v", positive=True)
        t, r = (v+x/v)/2, (v-x/v)/2
        for d in (*range(2, 10), 14, 15):
            for power in (3, 4):
                integrand = s.expand(r**(d-2)/(2*v)*t**power)
                probes = [s.diff(integrand, x, j).subs(x, 0)/s.factorial(j)
                          for j in range(d//2+1)]
                P = sum(x**j*s.integrate(probe, (v, 0, L))
                        for j, probe in enumerate(probes))
                B = short_monomial(d, power, 0, x, L)
                error = s.expand(B-P)
                # No surviving critical/subcritical monomial or logarithm.
                for term in s.Add.make_args(error):
                    if term:
                        self.assertGreaterEqual(term.as_powers_dict().get(x, 0),
                                                s.Rational(d+1, 2))
                moving = sum(x**j*s.integrate(probe, (v, 0, s.sqrt(x)))
                             for j, probe in enumerate(probes))
                fixed_primitive = s.integrate(integrand-sum(
                    x**j*probe for j, probe in enumerate(probes)), v)
                fixed = fixed_primitive.subs(v, L)-fixed_primitive.subs(v, s.sqrt(x))
                self.assertEqual(s.simplify(error-fixed+moving), 0)
                self.assertNotEqual(s.simplify(moving), 0)
        # Directly omitting the first moving boundary term already fails in 2D.
        integrand = t**3/(2*v)
        boundary = -integrand.subs(v, s.sqrt(x))/(2*s.sqrt(x))
        self.assertEqual(s.simplify(boundary), -s.sqrt(x)/4)
        # The 5D/6D higher terms are genuinely present, though supercritical.
        self.assertEqual(s.expand(short_monomial(5, 4, 0, x, L)).coeff(x**s.Rational(7, 2)),
                         s.Rational(1, 35))
        self.assertEqual(s.expand(short_monomial(6, 4, 0, x, L)).coeff(s.log(x)),
                         -3*x**4/512)

    def test_steep_actual_overlap_against_literal_time_fibre_intersection(self):
        slope = 0.75  # independent faces spacelike; old combined budget fails
        for tau, b in ((0, 0), (0.04, 0.04), (0.12, -0.08), (0.8, 0.2)):
            def actual(x, weight):
                if abs(x+b) >= 1:
                    return 0.0
                f, translated_f = slope*(1-x*x)/2, slope*(1-(x+b)**2)/2
                length = max(0, min(f, translated_f-tau)-max(-f, -translated_f-tau))
                return weight(x)*length
            for name, w in (("one", lambda x: 1), ("axis-square", lambda x: x*x),
                            ("height", lambda x: 1-x*x)):
                direct = quad(lambda x: actual(x, w), -1, 1,
                              epsabs=1e-10, epsrel=1e-10, limit=150)[0]
                self.assertAlmostEqual(capsule_overlap(2, tau, (b,), weight=name), direct,
                                       delta=2e-9)

    def test_independent_target_hessian_source_flux_and_actual_two_jet(self):
        for d in (*range(2, 10), 14, 15):
            for weight in ("one", "axis-square", "height"):
                C, L, Q, U = capsule_angular_jet(d, weight=weight)
                joint, flux = capsule_geometric_terms(d, weight=weight)
                coefficient = 2*(Q-(d-1)*U)/sphere_area(d)
                self.assertEqual(s.simplify(coefficient-joint-flux), 0)
                if weight != "one":
                    self.assertNotEqual(flux, 0)
                if weight == "height":
                    self.assertEqual(joint, 0)
                # An ordinary full-sphere second-moment rule exactly averages
                # the b_1^2 dependence of the actual weighted capsule overlap.
                n = d-1
                errors = []
                for eps in (0.01, 0.005):
                    tau, radius = eps, 0.6*eps
                    average = sum(capsule_overlap(
                        d, tau, tuple(radius if i == k else 0 for i in range(n)),
                        weight=weight) for k in range(n))/n
                    model = float((C+L*tau+Q*tau*tau+U*radius*radius)/sphere_area(d))
                    errors.append(abs(average-model))
                self.assertLess(errors[1], 0.16*errors[0])
            # Nonzero future Hessian: Delta(f)=-n*s; omitting it changes target.
            slope = s.Rational(3, 4)
            integrated_hessian = -slope*sphere_area(d)
            self.assertNotEqual(integrated_hessian, 0)
            one = capsule_geometric_terms(d)
            axis = capsule_geometric_terms(d, weight="axis-square")
            signed_first = tuple(2*x for x in axis)
            signed_second = tuple(x-2*y for x, y in zip(one, axis))
            self.assertEqual(s.simplify(signed_first[1]+signed_second[1]), 0)
            self.assertEqual(s.simplify(signed_first[0]+signed_second[0]-one[0]), 0)

    def test_actual_short_and_long_density_two_coordinate_laws(self):
        for d in (2, 3, 4, 7, 8, 15, 16):
            for sigma in (0.0003, 0.008, 0.01, 0.02):
                for long in (False, True):
                    by_time = capsule_density(d, sigma, 0.1, long=long)
                    by_null = capsule_density(d, sigma, 0.1, long=long, coordinates="null")
                    self.assertAlmostEqual(by_time, by_null, delta=3e-10)
                    if not long and sigma >= 0.1**2:
                        self.assertEqual(by_time, 0)

    def test_pair_space_rank_and_parallel_cutoff_negative_control(self):
        for d in range(2, 9):
            n = d-1
            sigma_covector = [-2, 2]+[0]*(n-1)
            cutoff_covector = [-1, -1]+[0]*(n-1)
            past = [1, -s.Rational(3, 4)]+[0]*(n-1)
            future = [1, s.Rational(3, 4)]+[0]*(n-1)
            rows = [sigma_covector+[-v for v in sigma_covector],
                    cutoff_covector+[-v for v in cutoff_covector],
                    past+[0]*d, [0]*d+future]
            self.assertEqual(s.Matrix(rows).rank(), 4)
            rows[-1] = [0]*d+past
            self.assertEqual(s.Matrix(rows).rank(), 3)
            self.assertEqual(s.Matrix([rows[0], rows[2], rows[3]]).rank(), 3)

    def test_complete_ordered_partitions_point_once_and_cut_conversion(self):
        # Finite quadrature identity, not an asymptotic or geometric proof.
        points = [(s.Rational(t, 20), s.Rational(x, 20))
                  for t, x in ((0, 0), (4, 2), (-2, -4), (1, 12))]
        rho, delta = s.Integer(3), s.Rational(3, 10)
        a, beta = action_constants(2)
        chi = (lambda p: 1+p[1], lambda p: -p[1])
        phi = (lambda p: 2+p[0], lambda p: -1-p[0])
        unit = lambda p: s.Integer(1)

        def pieces(w, z, radial=True):
            point = a*rho*sum(w(p)*z(p) for p in points)
            short = long = s.Integer(0)
            for i, p in enumerate(points):
                for j, q in enumerate(points):
                    t, r = q[0]-p[0], abs(q[1]-p[1])
                    if i == j or t < r:
                        continue
                    sigma = t*t-r*r
                    phase = interval_coefficient(2)*rho*sigma
                    pair = -beta*rho**2*w(p)*z(q)*kernel_polynomial(2).subs(Z, phase)*s.exp(-phase)
                    ell = t+r if radial else t
                    if ell < delta:
                        short += pair
                    else:
                        long += pair
            return point+short, long

        full = pieces(unit, unit)
        ordered = [pieces(w, z) for w in chi for z in phi]
        for k in (0, 1):
            self.assertEqual(s.simplify(sum(p[k] for p in ordered)-full[k]), 0)
        same_label = [pieces(chi[i], phi[i]) for i in range(2)]
        self.assertNotEqual(s.simplify(sum(sum(p) for p in same_label)-sum(full)), 0)
        alternate = pieces(unit, unit, radial=False)
        conversion = s.simplify(full[0]-alternate[0])
        self.assertNotEqual(conversion, 0)
        self.assertEqual(s.simplify(conversion+full[1]-alternate[1]), 0)
        # First positive pair lies exactly on the radial cutoff and is long.
        self.assertEqual(points[1][0]-points[0][0]+abs(points[1][1]-points[0][1]), delta)


if __name__ == "__main__":
    unittest.main()
