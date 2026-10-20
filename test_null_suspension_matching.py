"""Finite SM checks; not certification of geometric remainders or acceptance."""

import math
import unittest

import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import (
    Z, action_constants, interval_coefficient, kernel_polynomial,
)
from full_partner_globalization import primitive_response
from intrinsic_union_response import focal_growth
from null_suspension import (
    cap_weight, diamond_action, physical_section, rapidity_weight, short_weight,
)
from null_suspension_matching import (
    curvature_mellin, fold_cap_weight, klein_charge_prefactor, moment_pairing,
    normal_profile, origin_mellin,
)


class NullSuspensionMatchingTests(unittest.TestCase):
    def test_exact_four_truncated_moments_and_reference_length(self):
        for t, scale in ((.7, .3), (1.8, 2.4)):
            # Signed finite data, not an assumed asymptotic density.
            f = lambda u: math.cos(7*u)-.3
            moments = [quad(lambda u: u**j*f(u), 0, t)[0]
                       for j in (1, 3)]
            logs = [quad(lambda u: u**j*math.log(u/scale)*f(u), 0, t)[0]
                    for j in (1, 3)]
            paired = moment_pairing(t, moments[0], logs[0],
                                    moments[1], logs[1], scale)
            direct = quad(lambda u: cap_weight(u, t)*f(u), 0, t)[0]
            self.assertAlmostEqual(paired, direct, delta=2e-11)
            new_scale = scale*3
            new_logs = [value-math.log(3)*moment
                        for value, moment in zip(logs, moments)]
            self.assertAlmostEqual(moment_pairing(
                t, moments[0], new_logs[0], moments[1], new_logs[1],
                new_scale), direct, delta=2e-11)

    def test_mellin_expression_on_original_absolute_strip(self):
        for d in (3, 4, 5, 7, 8):
            power = s.Rational(3, 2)-d
            z = float((power+d-1)/d)
            c = float(interval_coefficient(d))
            kernel = s.lambdify(Z, kernel_polynomial(d)*s.exp(-Z), 'math')
            # t = Z**z removes the integrable lower-end singularity.
            kernel_moment = quad(lambda t: kernel(t**(1/z))/z,
                                 0, 90**z, epsabs=3e-11)[0]
            n = d-2
            angular = (math.gamma(n/2)*math.gamma(1-d*z/2)
                       / math.gamma(1+n/2-d*z/2))/2
            sphere = 2*math.pi**(n/2)/math.gamma(n/2)
            independent = sphere/d*c**(-z)*kernel_moment*angular
            self.assertAlmostEqual(float(origin_mellin(d, power)), independent,
                                   delta=3e-9*abs(independent))

    def test_zero_powers_do_not_kill_point_or_screen_logarithms(self):
        x = s.Symbol('x', real=True)
        for d in range(2, 15):
            phi = origin_mellin(d, x)
            a, beta = action_constants(d)
            self.assertEqual(s.simplify(phi.subs(x, 1)), 0)
            self.assertEqual(s.simplify(phi.subs(x, 3)), 0)
            first = s.diff(phi, x).subs(x, 1)
            third = s.diff(phi, x).subs(x, 3)
            self.assertEqual(s.simplify(first+a/(2*beta)), 0)
            self.assertEqual(s.simplify(third-2/beta), 0)
            self.assertLess(float(first), 0)
            self.assertGreater(float(third), 0)

    def test_curvature_reference_coefficient_is_independent_of_target(self):
        x = s.Symbol('x', real=True)
        for d in range(3, 12):
            n = d-2
            a = s.Rational(d, 24*(d+1))
            b = a/(d+2)
            z = (x+d+1)/d
            extra_r2 = -n*origin_mellin(d, x+2)/(x+1)
            extra_sigma = (x+d-1)*origin_mellin(d, x+2)/(x+1)
            direct = -extra_r2/(6*n)-z*(a*extra_r2/n-b*extra_sigma)
            psi = curvature_mellin(d, x)
            self.assertEqual(s.simplify(psi-direct), 0)
            beta = action_constants(d)[1]
            self.assertEqual(s.simplify(psi.subs(x, 1)), 0)
            self.assertEqual(s.simplify(s.diff(psi, x).subs(x, 1)
                                        -1/(4*beta)), 0)
        self.assertEqual(curvature_mellin(2, 1), 0)

    def test_profile_quadrature_against_other_radial_coordinates(self):
        for d in (3, 4, 5):
            n = d-2
            sphere = 2*math.pi**(n/2)/math.gamma(n/2)
            c = float(interval_coefficient(d))
            kernel = s.lambdify(Z, kernel_polynomial(d)*s.exp(-Z), 'math')
            derivative = s.lambdify(
                Z, (s.diff(kernel_polynomial(d), Z)-kernel_polynomial(d))
                * s.exp(-Z), 'math')
            a, b = d/(24*(d+1)), d/(24*(d+1)*(d+2))
            for u in (.2, 1.1, 2.4):
                def integrand(r, curved):
                    sigma = u*u-r*r
                    z = c*sigma**(d/2)
                    value = kernel(z)
                    if curved:
                        value = (-r*r*value/(6*n)
                                 + (a*r*r/n-b*sigma)*z*derivative(z))
                    return sphere*r**(n-1)*value
                for curved in (False, True):
                    direct = quad(lambda r: integrand(r, curved), 0, u,
                                  epsabs=2e-11)[0]
                    self.assertAlmostEqual(normal_profile(d, u, curved), direct,
                                           delta=3e-10)

    def test_even_reference_log_moments_by_ordered_profile_integration(self):
        d = 4
        x = s.Symbol('x', real=True)
        for curved, power in ((False, 1), (False, 3), (True, 1)):
            mellin = curvature_mellin(d, x) if curved else origin_mellin(d, x)
            actual = quad(lambda u: u**power*math.log(u)
                          * normal_profile(d, u, curved), 0, 6,
                          epsabs=2e-9, limit=160)[0]
            expected = float(s.diff(mellin, x).subs(x, power))
            self.assertAlmostEqual(actual, expected, delta=2e-8)

    def test_real_sphere_triangle_integral_has_the_curvature_phase_sign(self):
        # d=4, Y=S^2, coincident Y endpoints: this is actual IN5, not a fit
        # to an action or a substitution of the averaged triangle potential.
        c = float(interval_coefficient(4))
        for u in (.2, .1):
            actual = 2*math.pi*quad(
                lambda r: math.sin(r)*physical_section(u, r, r),
                0, u/2, epsabs=2e-14, epsrel=2e-11)[0]
            coefficient = (actual/(c*u**4)-1)/u**2
            self.assertAlmostEqual(coefficient, -1/90, delta=4e-6)

    def test_moving_diagonal_contacts_are_not_discarded(self):
        # Algebraic control of the Leibniz terms, not a spacetime model.
        lam, v, w = s.symbols('lam v w', positive=True)
        nu = s.sqrt(w)*(1+lam**2*w)
        a = 1+lam*v+lam**2*v**2
        integral = s.integrate(a, (v, nu, 2))
        dot, ddot, dddot = [s.diff(nu, lam, j) for j in (1, 2, 3)]
        contacts = [a*dot,
                    2*s.diff(a, lam)*dot+s.diff(a, v)*dot**2+a*ddot,
                    3*s.diff(a, lam, 2)*dot
                    +3*s.diff(a, lam, v)*dot**2+s.diff(a, v, 2)*dot**3
                    +3*s.diff(a, lam)*ddot+3*s.diff(a, v)*dot*ddot+a*dddot]
        for order, contact in enumerate(contacts, 1):
            interior = s.integrate(s.diff(a, lam, order), (v, nu, 2))
            self.assertEqual(s.simplify(s.diff(integral, lam, order)
                                        -interior+contact.subs(v, nu)), 0)
        self.assertNotEqual(contacts[1].subs({v: nu, lam: 0}), 0)

    def test_full_diamond_moments_retain_homogeneous_boundary_and_upper_tail(self):
        d, t = 2, 1.2
        a, beta = map(float, action_constants(d))
        for rho in (.8, 7.0):
            f = lambda u: normal_profile(d, math.sqrt(rho)*u)
            moments = [quad(lambda u: u**j*f(u), 0, t)[0]
                       for j in (1, 3)]
            logs = [quad(lambda u: u**j*math.log(u)*f(u), 0, t)[0]
                    for j in (1, 3)]
            pair = moment_pairing(t, moments[0], logs[0], moments[1], logs[1])
            action = a*rho*t*t/2-beta*rho**2*pair
            self.assertAlmostEqual(action, diamond_action(rho, t), delta=2e-9)
            # Setting the finite truncated pure moments to their zero
            # full-half-line values is NOT an exact finite-density identity.
            dropped = a*rho*t*t/2-beta*rho**2*moment_pairing(
                t, 0, logs[0], 0, logs[1])
            self.assertGreater(abs(dropped-action), 1e-3)

    def test_auxiliary_and_physical_partitions_recombine_before_estimation(self):
        t, delta = 1.0, .2
        f = lambda u: normal_profile(3, u)
        for u in (.04, .14, .4, .8):
            chi = math.exp(-(u/.3)**2)
            gs = short_weight(u, delta, t)
            gl = rapidity_weight(u, t, delta)
            terms = [weight*mask*f(u) for weight in (chi, 1-chi)
                     for mask in (gs, gl)]
            self.assertAlmostEqual(sum(terms), cap_weight(u, t)*f(u), places=12)
        self.assertGreater(rapidity_weight(.14, t, delta), 0)

    def test_circle_antipode_has_regular_two_phase_density_and_both_zeros(self):
        u, theta, length = s.symbols('u theta L', positive=True)
        phases = s.Matrix([u*u-theta*theta, u*u-(length-theta)**2])
        self.assertEqual(s.factor(phases.jacobian([u, theta]).det()), 4*u*length)
        self.assertEqual(phases.subs({u: length/2, theta: length/2}), s.zeros(2, 1))
        # Finite constant-density two-phase control: retain BOTH inactive
        # strips and the active q-ball. This is not a geometric remainder test.
        q, w = 1.5, .2
        area = quad(lambda x: (1-x**q)**(1/q), 0, 1)[0]
        expected = math.gamma(1+1/q)**2/math.gamma(1+2/q)
        self.assertAlmostEqual(area, expected, delta=2e-10)
        primitive = 2*w+area*w*w
        self.assertGreater(primitive, area*w*w)
        for power in (1, 2):
            self.assertEqual(s.simplify(primitive_response(3, power, 1)), 0)
        t = s.Symbol('T', positive=True)
        cap = u*((t*t+u*u)*s.log(t/u)-t*t+u*u)
        for derivative in range(3):
            self.assertEqual(s.diff(cap, u, derivative).subs(u, t), 0)

    def test_actual_null_cap_coefficient_not_the_spacelike_slab_weight(self):
        t = 21/20
        for p in (1, 2, 4):
            sphere = 2*math.pi**(p/2)/math.gamma(p/2)
            for aa in (.99, 1., 1.01):
                radius = math.sqrt(t*t-aa)
                direct = sphere/2*quad(
                    lambda r: r**(p-1)*cap_weight(math.sqrt(aa+r*r), t)
                    /math.sqrt(aa+r*r), 0, radius, epsabs=1e-15)[0]
                actual = fold_cap_weight(p, aa, t)
                self.assertGreater(actual, 0)
                self.assertAlmostEqual(actual, direct, delta=2e-11*actual)
                slab = sphere/2*quad(
                    lambda r: r**(p-1)*(t/math.sqrt(aa+r*r)-1),
                    0, radius, epsabs=1e-15)[0]
                self.assertGreater(slab, 100*actual)
        self.assertEqual(fold_cap_weight(1, t*t, t), 0)
        self.assertEqual(fold_cap_weight(1, 1.3, t), 0)

    def test_new_fold_density_counts_both_branches_centers_and_endpoint_weights(self):
        rng = np.random.default_rng(156188)
        t = 21/20
        for _ in range(30):
            x, y, w = rng.uniform(-.01, .01, 3).astype(np.longdouble)
            if abs(y-w) < 1e-4:
                continue
            u = np.longdouble('1.02')
            phases = np.array([u*u-(1+x)**2-(w-y)**2,
                               u*u-(-1+x)**2-(w-y)**2,
                               u*u-x*x-(1-w-y)**2,
                               u*u-x*x-(-1-w-y)**2])
            disc = (phases[2]-phases[3])**2/8-sum(phases[:2])+sum(phases[2:])
            direct = 4*cap_weight(float(u), t)/(128*u*abs(y-w))
            pushed = cap_weight(float(u), t)/(2*u)/(8*math.sqrt(2)*math.sqrt(disc))
            self.assertAlmostEqual(direct, pushed, delta=2e-10*direct)

    def test_positive_nonlocal_charge_prefactor_and_true_signed_normalization(self):
        t, alpha = 21/20, s.Rational(7, 2)
        for d in (5, 6, 7, 8, 11):
            prefactor = klein_charge_prefactor(d, t)
            self.assertGreater(prefactor, 0)
            density = 10**(d-4)/(8*math.sqrt(2))*fold_cap_weight(d-4, 1., t)
            # Set the auxiliary moment to one ONLY to compare its multiplier.
            c_q_per_moment = 1/(math.prod(float(alpha-i) for i in range(4))
                                *math.gamma(1+7/d))
            independent = (density*c_q_per_moment
                           *float(primitive_response(d, alpha, 1)))
            self.assertAlmostEqual(prefactor, independent,
                                   delta=3e-12*prefactor)
            self.assertEqual(s.simplify(1+s.Rational(2, d)-s.Rational(7, d)),
                             1-s.Rational(5, d))
        self.assertGreater(klein_charge_prefactor(5, 1.08),
                           klein_charge_prefactor(5, 1.02))

    def test_local_spherical_finite_term_does_not_erase_full_focal_growth(self):
        d, t, volume = 7, 4., 4*math.pi*20**3
        x = s.Symbol('x', real=True)
        beta = float(action_constants(d)[1])
        curvature = float(s.diff(curvature_mellin(d, x), x).subs(x, 1))
        screen = float(s.diff(origin_mellin(d, x), x).subs(x, 3))
        local = beta*(t*t*(2*volume)*curvature+volume*screen)
        self.assertAlmostEqual(local, volume*(t*t/2+2), delta=1e-8)
        self.assertEqual(focal_growth(3.0), 0)
        self.assertGreater(focal_growth(t), 0)

    def test_divergent_uncut_moments_are_not_assigned_finite_values(self):
        for d in (3, 5, 7):
            with self.assertRaises(ValueError):
                origin_mellin(d, 4)
            with self.assertRaises(ValueError):
                curvature_mellin(d, 3)
        self.assertTrue(origin_mellin(4, 4).is_finite)
        self.assertTrue(curvature_mellin(4, -1).is_finite)

    def test_invalid_inputs(self):
        for d in (1, True, 3.0):
            with self.assertRaises(ValueError):
                origin_mellin(d, 1)
        for power in (-3, s.I, s.oo):
            with self.assertRaises(ValueError):
                origin_mellin(4, power)
        for args in ((0, 1, 1), (True, 1, 1), (1, 0, 1), (1, 1, math.inf)):
            with self.assertRaises(ValueError):
                fold_cap_weight(*args)
        for args in ((4, 1.05), (5, 1), (5, 1.2), (5, math.nan)):
            with self.assertRaises(ValueError):
                klein_charge_prefactor(*args)
        for u in (-1, math.inf, math.nan):
            with self.assertRaises(ValueError):
                normal_profile(3, u)
        with self.assertRaises(ValueError):
            normal_profile(3, .2, curvature=1)
        with self.assertRaises(ValueError):
            moment_pairing(1, 0, 0, 0, 0, log_scale=0)
        with self.assertRaises(ValueError):
            moment_pairing(1, 0, math.nan, 0, 0)


if __name__ == '__main__':
    unittest.main()
