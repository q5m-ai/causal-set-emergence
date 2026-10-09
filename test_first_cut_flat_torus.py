"""Finite regressions of the first-cut written proof, not its certification."""

from itertools import product
import math
import unittest

import numpy as np
import sympy as s
from scipy.integrate import quad

from dimension_kernels import action_constants, interval_coefficient, layer_coefficients
from first_cut_flat_torus import (
    actual_interval, causal_lifts, circle_full_pair, circle_interval_distance,
    circle_long_primitive, first_cut_geometry, null_excesses, overlap_leading,
    overlap_primitive_coefficient, overlap_primitive_scaled,
    overlap_signed_coefficient, overlap_volume, phase_weight,
    primitive_components, quotient_distance, two_route_volume,
)
from full_partner_globalization import _kernel, primitive_response, torus_long_density


class FirstCutFlatTorusTest(unittest.TestCase):
    def test_exact_band_and_no_silent_thin_or_higher_cut_fallback(self):
        self.assertEqual(first_cut_geometry(7, 1, .6), (1., .6))
        for d in (True, 1, 3.5):
            with self.assertRaises(ValueError):
                first_cut_geometry(d, 1, .6)
        for duration in (.4, .5, 1/math.sqrt(2), .8, math.inf):
            with self.assertRaises(ValueError):
                first_cut_geometry(4, 1, duration)
        for length in (0, -1, math.nan):
            with self.assertRaises(ValueError):
                first_cut_geometry(4, length, .6)
        # The existing thin theorem is not extended in place.
        with self.assertRaises(ValueError):
            torus_long_density(4, 1, .6, .1, .01)
        with self.assertRaises(ValueError):
            causal_lifts(3, 1, .72, [.5, .5])
        with self.assertRaises(ValueError):
            two_route_volume(4, 1, .5, .5)

    def test_complete_lift_enumeration_against_lattice_and_null_ties(self):
        rng = np.random.default_rng(149)
        for d in (2, 3, 4, 5, 7):
            for _ in range(8):
                a = rng.uniform(-.5, .5, d-1)
                tau = rng.uniform(.1, .7)
                brute = [a+np.array(m) for m in product((-1, 0, 1), repeat=d-1)
                         if np.linalg.norm(a+np.array(m)) <= tau]
                observed = causal_lifts(d, 1, tau, a)
                key = lambda b: tuple(np.round(b, 12))
                self.assertEqual({key(b) for b in observed}, {key(b) for b in brute})
                self.assertLessEqual(len(observed), 2)
                if len(observed) == 2:
                    self.assertAlmostEqual(np.linalg.norm(observed[0]-observed[1]), 1)
            self.assertEqual(len(causal_lifts(d, 1, .5, [.5]+[0.]*(d-2))), 2)
        # Beyond the approved upper bound an actual four-lift corner appears.
        corner = [np.array([.5, .5])+m for m in map(np.array, product((-1, 0), repeat=2))]
        self.assertEqual(sum(np.linalg.norm(b) < .72 for b in corner), 4)

    def test_null_excess_identities_and_true_common_overlap(self):
        nodes, weights = np.polynomial.legendre.leggauss(160)
        a = (nodes+1)/2
        weight = np.outer(weights, weights)/4
        for d in (2, 3, 4, 7):
            x, y = .11, .055
            u, v = null_excesses(1, x, y)
            self.assertAlmostEqual(u*(1+v), x)
            self.assertAlmostEqual(v*(1+u), y)
            aa, bb = np.meshgrid(a, a, indexing='ij')
            radius = np.minimum(aa*bb, np.minimum(
                (1-aa)*(1+1/v-bb), (1+1/u-aa)*(1-bb)))
            q = d/2
            vp = math.pi**(q-1)/math.gamma(q)
            independent = vp/2*(u*v)**q*np.sum(weight*radius**(q-1))
            h = overlap_volume(d, 1, x, y)
            self.assertAlmostEqual(h, independent, delta=2e-5*max(h, 1e-12))
            self.assertAlmostEqual(h, overlap_volume(d, 1, y, x), delta=2e-12*h)
            self.assertLessEqual(h, overlap_leading(d, 1, x, y))
        self.assertEqual(overlap_volume(5, 1, 0, .1), 0)
        self.assertEqual(overlap_volume(5, 1, .1, 0), 0)

    def test_both_overlap_components_against_literal_circle_interval(self):
        for tau in (.2, .49, .51, .6, .69):
            for a in (.01, .21, .4, .49, .5, .51, .8, 1.49):
                actual = actual_interval(2, 1, tau, [a])
                literal = circle_interval_distance(1, tau, a)
                self.assertAlmostEqual(actual, literal, delta=2e-15)
        tau, a = .64, .48
        phases = [tau*tau-float(b@b) for b in causal_lifts(2, 1, tau, [a])]
        c = float(interval_coefficient(2))
        summed = c*sum(phases)
        h = overlap_volume(2, 1, *phases)
        literal = circle_interval_distance(1, tau, a)
        self.assertAlmostEqual(summed-2*h, literal)
        self.assertGreater(abs(summed-h-literal), .005)
        self.assertGreater(abs(summed-literal), .01)
        self.assertGreater(abs(c*max(phases)-literal), .01)

    def test_actual_three_dimensional_distance_integral(self):
        tau, target = .68, np.array([.49, .06])
        actual = actual_interval(3, 1, tau, target)
        results = []
        for order in (96, 192):
            nodes, weights = np.polynomial.legendre.leggauss(order)
            xx, yy = np.meshgrid(nodes/2, nodes/2, indexing='ij')
            points = np.stack((xx, yy), axis=-1)
            r0 = np.linalg.norm(points, axis=-1)
            r1 = np.linalg.norm((points-target+.5) % 1-.5, axis=-1)
            results.append(np.sum(np.outer(weights, weights)/4*np.maximum(tau-r0-r1, 0)))
        self.assertAlmostEqual(actual, results[-1], delta=8e-6)
        self.assertLess(abs(results[-1]-actual), abs(results[0]-actual))

    def test_uniform_overlap_scaling_and_fractional_dimensions(self):
        for d in (2, 3, 4, 5, 8, 11):
            errors = []
            for w in (.01, .002, .0004):
                h = overlap_volume(d, 1, .7*w, .2*w)
                leading = overlap_leading(d, 1, .7*w, .2*w)
                ratio = h/leading
                self.assertGreater(ratio, 0)
                self.assertLessEqual(ratio, 1+1e-12)
                errors.append(1-ratio)
            self.assertLess(errors[2], errors[1])
            self.assertLess(errors[1], errors[0])
            self.assertLess(errors[2], .02)

    def test_measure_scaling_symmetry_single_lift_and_seams(self):
        for d in (2, 3, 4, 7):
            vector = [.49]+[.03]*(d-2)
            base = actual_interval(d, 1, .65, vector)
            self.assertAlmostEqual(actual_interval(d, 2, 1.3, np.array(vector)*2),
                                   base*2**d, delta=1e-11*base*2**d)
            self.assertAlmostEqual(actual_interval(d, 1, .65, -np.array(vector)),
                                   base, delta=1e-12*base)
            self.assertAlmostEqual(actual_interval(d, 1, .65, np.array(vector)+2),
                                   base, delta=1e-12*base)
            c = float(interval_coefficient(d))
            self.assertAlmostEqual(actual_interval(d, 1, .2, [.95]+[0]*(d-2)),
                                   c*(.2**2-.05**2)**(d/2))
            self.assertEqual(actual_interval(d, 1, .1, [.4]+[0]*(d-2)), 0)
        self.assertAlmostEqual(quotient_distance([.4, .4], 1), math.sqrt(.32))

    def test_exact_phase_jacobian_closing_root_and_two_dimensional_union(self):
        length, duration = s.symbols('L T', positive=True)
        x, y, b = s.symbols('x y b', real=True)
        a = length**2/4+(x+y)/2+(y-x)**2/(4*length**2)
        tau = s.sqrt(a+b*b)
        coordinate = (y-x)/(2*length)
        jacobian = s.Matrix([tau, coordinate]).jacobian([x, y]).det()
        self.assertEqual(s.simplify(jacobian-1/(4*length*tau)), 0)
        upper = x-length**2+2*length*s.sqrt(duration**2-x)
        self.assertEqual(s.simplify(a.subs(y, upper)-duration**2), 0)
        t, z = s.symbols('t z', real=True)
        phase1, phase2 = t*t-z*z, t*t-(z-length)**2
        common_overlap = (t-z)*(t+z-length)/2
        union = (phase1+phase2)/2-2*common_overlap
        self.assertEqual(s.expand(union-length*(t-length/2)), 0)

    def test_transverse_measure_and_closing_time_contact(self):
        for d in (2, 3, 4, 7, 10):
            p = d-2
            for a in (.25, .3, .359):
                if p == 0:
                    direct = (.6/math.sqrt(a)-1)/4
                else:
                    area = 2*math.pi**(p/2)/math.gamma(p/2)
                    direct = area/4*quad(lambda r: r**(p-1)*(.6/math.sqrt(a+r*r)-1),
                                         0, math.sqrt(.36-a), epsabs=1e-14)[0]
                self.assertAlmostEqual(phase_weight(d, 1, .6, a), direct,
                                       delta=max(1e-17, 3e-12*direct))
            self.assertEqual(phase_weight(d, 1, .6, .36), 0)
            f1 = phase_weight(d, 1, .6, .36-1e-4)
            f2 = phase_weight(d, 1, .6, .36-1e-5)
            self.assertAlmostEqual(f1/f2, 10**(d/2), delta=.002*10**(d/2))

    def test_complete_actual_primitive_and_regular_complement(self):
        for duration in (.55, .6, .68):
            for w in (.001, .003):
                pieces = primitive_components(2, 1, duration, .1, w)
                direct = circle_long_primitive(1, duration, .1, w)
                self.assertAlmostEqual(pieces['actual'], direct, delta=3e-15)
                exact_corner = (duration-.5)*w*w/4-w**3/12
                self.assertAlmostEqual(pieces['corner']+pieces['overlap'], exact_corner,
                                       delta=3e-18)
                # Omitting either reference strip is not exact restoration.
                wrong = pieces['reference']+pieces['corner']-pieces['strip']+pieces['overlap']
                self.assertGreater(abs(wrong-direct), 1e-8)
                self.assertGreater(abs(pieces['reference']-direct), 1e-8)
        for d in (2, 3, 6):
            self.assertEqual(primitive_components(d, 1, .6, .1, 0)['actual'], 0)
        with self.assertRaises(ValueError):
            primitive_components(4, 1, .6, .1, .1)
        with self.assertRaises(ValueError):
            primitive_components(4, 1, .6, .5, .001)

    def test_actual_fractional_shell_refinement_and_missing_overlap_controls(self):
        for d in (2, 3, 4, 5, 7, 8, 11):
            coefficient = overlap_primitive_coefficient(d, 1, .6)
            self.assertGreater(coefficient, 0)
            ratios = [overlap_primitive_scaled(d, 1, .6, w, order=24)/coefficient
                      for w in (.004, .001, .00025)]
            self.assertTrue(0 < ratios[0] < ratios[1] < ratios[2] < 1.001)
            self.assertGreater(ratios[-1], .98)
        d, w = 7, .00025
        coefficient = overlap_primitive_coefficient(d, 1, .6)
        coarse = overlap_primitive_scaled(d, 1, .6, w, order=16)
        fine = overlap_primitive_scaled(d, 1, .6, w, order=32)
        self.assertAlmostEqual(coarse, fine, delta=2e-6*coefficient)
        missing = overlap_primitive_scaled(d, 1, .6, w, order=24, overlap_copies=1)
        self.assertAlmostEqual(missing/fine, .5, delta=.0001)
        self.assertEqual(overlap_primitive_scaled(d, 1, .6, w, overlap_copies=0), 0)
        with self.assertRaises(ValueError):
            overlap_primitive_scaled(d, 1, .6, 0)

    def test_signed_fractional_response_uses_actual_dimensional_constants(self):
        for d in (2, 3, 4, 5, 7, 10):
            q = s.Rational(d, 2)
            kappa = overlap_primitive_coefficient(d, 1, .6)
            coefficient = overlap_signed_coefficient(d, 1, .6)
            self.assertEqual(math.copysign(1, coefficient), (-1)**(d//2))
            for rho in (4, 25):
                response = float(primitive_response(d, q+2, rho))*(d-1)*kappa
                self.assertAlmostEqual(response, coefficient*rho**(-2/d),
                                       delta=2e-12*abs(response))
        # Independently integrate the d=3 signed mode; do not take |K| first.
        d, q, rho = 3, 1.5, 9.
        c, pair = float(interval_coefficient(d)), float(action_constants(d)[1])
        amplitude = 2*overlap_primitive_coefficient(d, 1, .6)
        kernel = _kernel(d)
        integral = quad(lambda z: z**(q+1)*kernel(z**q), 0, np.inf,
                        epsabs=2e-11, epsrel=2e-11)[0]
        direct = -pair*(q+2)*amplitude*c**(-(q+2)/q)*rho**(-1/q)*integral
        self.assertAlmostEqual(direct, overlap_signed_coefficient(d, 1, .6)*rho**(-1/q),
                               delta=2e-11*abs(direct))

    def test_finite_density_full_action_includes_point_and_all_partners(self):
        kernel = _kernel(2)
        duration = .6
        for rho in (5, 40, 160):
            reference = 2*quad(lambda tau: (duration-tau)*quad(
                lambda r: kernel(rho*(tau*tau-r*r)/2), 0, tau,
                epsabs=3e-13, epsrel=3e-12)[0], 0, duration,
                epsabs=3e-13, epsrel=3e-12)[0]

            def outer(x):
                upper = x-1+2*math.sqrt(duration*duration-x)
                def inner(y):
                    a = .25+(x+y)/2+(y-x)**2/4
                    return phase_weight(2, 1, duration, a)*(kernel(
                        rho*two_route_volume(2, 1, x, y))-kernel(rho*x/2)-kernel(rho*y/2))
                return quad(inner, 0, upper, epsabs=3e-13, epsrel=3e-12)[0]

            correction = quad(outer, 0, 2*duration-1, epsabs=3e-13, epsrel=3e-12)[0]
            direct = circle_full_pair(1, duration, rho)
            self.assertAlmostEqual(reference+correction, direct, delta=3e-13)
            self.assertGreater(abs(correction), 1e-8)
        # Finite numerical consistency, not a rate or asymptotic certificate.
        values = [2*rho*duration-4*rho*rho*circle_full_pair(1, duration, rho)
                  for rho in (80, 320, 1280)]
        self.assertTrue(0 < values[2] < values[1] < values[0] < .2)
        rho = 320
        pair_only = -4*rho*rho*circle_full_pair(1, duration, rho)
        self.assertGreater(abs(pair_only-values[1]), 300)

    def test_common_cutoff_and_complete_signed_endpoint_partition(self):
        d, rho = 3, 11.
        point, pair = map(float, action_constants(d))
        kernel = _kernel(d)
        taus = np.array([.1, .2, .5, .6, .65])
        gaps = np.array([[.03, .01], [.04, .02], [.5, 0], [.49, .02], [.48, .04]])
        sources = np.array([.07, .19, .24, .41, .83])
        targets = (sources+gaps[:, 0]) % 1
        chi = np.array([2*np.cos(2*np.pi*sources), 1-2*np.cos(2*np.pi*sources)])
        phi = np.array([.7+np.sin(2*np.pi*targets), .3-np.sin(2*np.pi*targets)])
        point_phi = np.array([.7+np.sin(2*np.pi*sources), .3-np.sin(2*np.pi*sources)])
        pair_weights = np.array([.2, .15, .04, .11, .08])
        point_weights = np.array([.12, .14, .05, .09, .2])
        kernels = np.array([kernel(rho*actual_interval(d, 1, tau, a))
                            for tau, a in zip(taus, gaps)])
        normalized = -pair*rho**(1+2/d)*pair_weights*kernels
        physical_point = point*rho**(2/d)*point_weights.sum()
        full = physical_point+normalized.sum()
        short, long, diagonal_only = 0., 0., 0.
        for i, j in product(range(2), repeat=2):
            p = point*rho**(2/d)*np.dot(point_weights, chi[i]*point_phi[j])
            sterm = p+np.sum(normalized*(taus < .2)*chi[i]*phi[j])
            lterm = np.sum(normalized*(taus >= .2)*chi[i]*phi[j])
            short += sterm
            long += lterm
            if i == j:
                diagonal_only += sterm+lterm
        self.assertAlmostEqual(short+long, full, delta=2e-13)
        self.assertGreater(abs(diagonal_only-full), .1)
        self.assertGreater(abs(normalized[taus == .2].sum()), .01)
        short2 = physical_point+np.sum(normalized*(taus < .55))
        long2 = np.sum(normalized*(taus >= .55))
        conversion = np.sum(normalized*((taus < .2).astype(int)-(taus < .55).astype(int)))
        self.assertAlmostEqual(short-short2, conversion)
        self.assertAlmostEqual(long-long2, -conversion)
        self.assertGreater(abs(conversion), .01)

    def test_all_dimension_poisson_layer_generating_identity_at_actual_volume(self):
        for d in (2, 3, 4, 5, 8, 11):
            gap = [.49]+[.01]*(d-2)
            volume = actual_interval(d, 1, .6, gap)
            self.assertGreater(volume, 0)
            for rho in (3, 19):
                rate = rho*volume
                layers = sum(float(weight)*math.exp(-rate)*rate**j/math.factorial(j)
                             for j, weight in enumerate(layer_coefficients(d)))
                self.assertAlmostEqual(layers, _kernel(d)(rate), delta=2e-13)
            c = float(interval_coefficient(d))
            chosen = c*max(.6**2-float(a@a) for a in causal_lifts(d, 1, .6, gap))**(d/2)
            self.assertGreater(volume, chosen)


if __name__ == '__main__':
    unittest.main()
