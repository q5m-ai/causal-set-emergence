"""Independent checks of #66's algebra/diagnostics, not an asymptotic proof."""

import math
import unittest

import numpy as np
from mpmath import mp
import sympy as sp

from short_displacement import axial_jet, axial_short_density, jet_short_action, short_monomials
from two_face_diagnostics import (
    AxialCap, RadialCap, action, joint_geometry,
    overlap_density, quadrature,
)


class ShortDisplacementTest(unittest.TestCase):
    def assertNear(self, actual, expected, tolerance=1e-10):
        self.assertLessEqual(abs(float(actual)-float(expected)), tolerance*max(1, abs(float(expected))))

    def test_four_monomials_against_original_jacobian(self):
        for delta in (0.07, 0.2, 1.3):
            for ratio in (0, 0.001, 0.1, 0.7, 0.9):
                sigma = ratio*delta**2
                exact = short_monomials(sigma, delta)
                for j in range(4):
                    def integrand(v):
                        s, r = (v+sigma/v)/2, (v-sigma/v)/2
                        return (v-sigma/v)**2/(8*v)*(1, s, s*s, r*r)[j]
                    direct = quadrature(integrand, [math.sqrt(sigma), delta], 80)
                    self.assertNear(exact[j], direct, 1e-13)
        self.assertTrue(np.all(short_monomials(0.2**2, 0.2) == 0))
        self.assertTrue(np.all(short_monomials(1, 0.2) == 0))

    def test_near_cutoff_densities_do_not_lose_five_orders_to_subtraction(self):
        x = math.nextafter(1.0, 0.0)
        actual = short_monomials(x, 1)
        self.assertTrue(np.all(actual > 0))
        with mp.workdps(110):
            y = mp.mpf(x)
            reference = [(1-y*y+2*y*mp.log(y))/16, (1-y)**3/48,
                         (1-y**4+4*y*y*mp.log(y))/128,
                         (1-8*y+8*y**3-y**4-12*y*y*mp.log(y))/128]
            for value, expected in zip(actual, reference):
                self.assertLess(abs(mp.mpf(float(value))/expected-1), mp.mpf("1e-13"))

    def test_symbolic_lower_endpoint_and_cutoff_terms(self):
        v, q, d = sp.symbols("v q d", positive=True)
        sigma = q*q
        jac = (v-sigma/v)**2/(8*v)
        s, r = (v+sigma/v)/2, (v-sigma/v)/2
        expected = [
            d*d/16-sigma*sp.log(d)/4-sigma**2/(16*d*d)+sigma*sp.log(sigma)/8,
            d**3/48-sigma*d/16+sigma**2/(16*d)-sigma**3/(48*d**3),
            d**4/128-sigma**2*sp.log(d)/16-sigma**4/(128*d**4)+sigma**2*sp.log(sigma)/32,
            d**4/128-sigma*d*d/16+3*sigma**2*sp.log(d)/16+sigma**3/(16*d*d)
            -sigma**4/(128*d**4)-3*sigma**2*sp.log(sigma)/32,
        ]
        for monomial, reference in zip((1, s, s*s, r*r), expected):
            primitive = sp.integrate(sp.expand(jac*monomial), v)
            result = primitive.subs(v, d)-primitive.subs(v, q)
            self.assertEqual(sp.simplify(sp.expand_log(result-reference, force=True)), 0)

    def test_third_density_derivative_keeps_moving_endpoint(self):
        # A C3 cubic remainder. Even here deleting the endpoint term is wrong.
        v, sigma, delta = sp.symbols("v sigma delta", positive=True)
        s = (v+sigma/v)/2
        integrand = (v-sigma/v)**2/(8*v)*s**3
        primitive = sp.integrate(sp.expand(integrand), v)
        density = primitive.subs(v, delta)-primitive.subs(v, sp.sqrt(sigma))
        endpoint = sp.diff(integrand, sigma, 2).subs(v, sp.sqrt(sigma))/(2*sp.sqrt(sigma))
        differentiated = sp.integrate(sp.expand(sp.diff(integrand, sigma, 3)), v)
        missing_endpoint = differentiated.subs(v, delta)-differentiated.subs(v, sp.sqrt(sigma))
        self.assertEqual(sp.simplify(endpoint-1/(8*sp.sqrt(sigma))), 0)
        self.assertEqual(sp.simplify(missing_endpoint-endpoint-sp.diff(density, sigma, 3)), 0)
        self.assertNotEqual(sp.simplify(missing_endpoint-sp.diff(density, sigma, 3)), 0)

    def test_logarithmic_moments_and_unchanged_normalization(self):
        with mp.workdps(45):
            def kernel(z):
                x = z*z
                return (1-9*x+8*x*x-mp.mpf(4)/3*x**3)*mp.exp(-x)
            for j, expected in ((1, mp.mpf(1)/12), (2, -mp.sqrt(mp.pi)/12)):
                value = mp.quad(lambda z: z**j*mp.log(z)*kernel(z), [0, 1, 2, 4, 8, mp.inf])
                self.assertLess(abs(value-expected), mp.mpf("1e-39"))
            c = mp.pi/24
            self.assertLess(abs((mp.pi/2)/(12*c)-1), mp.mpf("1e-40"))
            self.assertLess(abs((4/mp.sqrt(6))*(mp.pi/16)*c**(-mp.mpf(3)/2)
                                *mp.sqrt(mp.pi)/12-1), mp.mpf("1e-40"))
            # Full pair prefactor, not merely sqrt(rho): sigma^(5/2) -> rho^(-1/4).
            for rho in (10, 1000):
                raw = rho**mp.mpf("1.5")*(c*rho)**(-mp.mpf("1.75"))
                self.assertLess(abs(raw-c**(-mp.mpf("1.75"))*rho**(-mp.mpf("0.25"))), mp.mpf("1e-40"))

    def test_quadratic_coefficient_from_geometry_not_fitted_action(self):
        for cap in (AxialCap(bend=0), AxialCap(), AxialCap(axes=(2, 3, 4), bend=-0.04)):
            jet = axial_jet(cap)
            self.assertNear(jet["weighted_volume"], cap.volume, 1e-13)
            self.assertNear(jet["joint_coefficient"], joint_geometry(cap, 40)["target"], 1e-10)
            self.assertEqual(jet["cutoff_derivative"], 0)
        # Two curved faces but unchanged joint neighborhood: f and gradient vanish there.
        radial = RadialCap()
        self.assertNear(joint_geometry(radial, 20)["target"], 8*math.pi, 1e-12)

    def test_nonzero_single_face_hessian_is_not_dropped(self):
        class CosineCap(AxialCap):
            # The same strict slope/curvature bounds hold. Use only the exact
            # axial overlap here, NOT the full-density solver which assumes
            # a monotone shift on the entire axial interval.
            def shift(self, x):
                return self.bend*np.cos(x/self.axes[0])

            def shift_prime(self, x):
                return -self.bend/self.axes[0]*np.sin(x/self.axes[0])

            def shift_second(self, x):
                return -self.bend/self.axes[0]**2*np.cos(x/self.axes[0])

        cap = CosineCap()
        jet = axial_jet(cap)
        target = joint_geometry(cap, 40)["target"]
        self.assertLess(jet["single_face_laplacian"], -1)
        self.assertNear(jet["short_limit_coefficient"], target, 1e-10)
        # Omitting the volume integral of the future Hessian gives a wrong
        # coefficient even though both faces and the joint are nondegenerate.
        without_face_term = jet["short_limit_coefficient"]+jet["single_face_laplacian"]
        self.assertGreater(abs(without_face_term-target), 1)
        errors = []
        for delta in (0.08, 0.04):
            sigma = 0.04*delta**2
            actual = axial_short_density(cap, sigma, delta, 20)
            errors.append(abs(actual-float(jet["angular"] @ short_monomials(sigma, delta))))
        self.assertLess(errors[1], errors[0]/20)

    def test_nonzero_cutoff_derivative_cancels_only_in_partition(self):
        cap = AxialCap()
        a = cap.axes[0]
        left = axial_jet(cap, weight=lambda x: x/a, weight_prime=lambda x: np.ones_like(x)/a)
        right = axial_jet(cap, weight=lambda x: 1-x/a, weight_prime=lambda x: -np.ones_like(x)/a)
        whole = axial_jet(cap)
        self.assertGreater(left["cutoff_derivative"], 0.1)
        # Direct ellipsoid surface reduction for this odd weight; the even
        # terms integrate to zero, leaving p*grad(h)'s axial component.
        surface = -2*math.pi*cap.axes[1]*cap.axes[2]/a**3 * quadrature(
            lambda x: x*x*cap.shift_prime(x), [-a, 0, a], 40)
        self.assertNear(left["joint_coefficient"], surface, 1e-12)
        # A sign-changing weight is deliberate; no positivity is required.
        self.assertGreater(left["short_limit_coefficient"], 0)
        self.assertLess(left["joint_coefficient"], 0)
        for key in ("weighted_volume", "short_limit_coefficient", "joint_coefficient",
                    "cutoff_derivative", "single_face_laplacian"):
            self.assertNear(left[key]+right[key], whole[key], 1e-12)
        np.testing.assert_allclose(left["angular"]+right["angular"], whole["angular"], atol=1e-12)
        sigma, delta = 0.0003, 0.08
        values = [axial_short_density(cap, sigma, delta, 12, weight=w)
                  for w in (lambda x: x/a, lambda x: 1-x/a, None)]
        self.assertNear(values[0]+values[1], values[2], 1e-13)

    def test_actual_short_density_independent_of_long_subtraction(self):
        for cap in (AxialCap(bend=0), AxialCap()):
            for sigma in (0.0003, 0.003):
                delta = 0.08
                direct = axial_short_density(cap, sigma, delta, 20)
                difference = overlap_density(cap, sigma, order=24)-overlap_density(cap, sigma, delta, 24)
                self.assertGreater(direct, 0)
                self.assertNear(direct, difference, 2e-10)
                # Comparison is a finite small-displacement diagnostic, not a theorem.
                jet = axial_jet(cap)["angular"]
                errors = []
                for scale in (1, 0.5):
                    d, sig = scale*delta, scale**2*sigma
                    value = axial_short_density(cap, sig, d, 20)
                    errors.append(abs(value-float(jet @ short_monomials(sig, d))))
                self.assertLess(errors[1], errors[0]/20)

    def test_boosted_unequal_axis_jet_and_lab_cutoff(self):
        cap = AxialCap(bend=0)
        base = axial_jet(cap)["angular"]
        for beta in (-0.6, 0.6):
            gamma = 1/math.sqrt(1-beta*beta)
            jet = base.copy()
            jet[1] *= gamma
            jet[2] *= gamma**2
            jet[3] = base[2]*gamma**2*beta**2/3
            self.assertNear((jet[2]-3*jet[3])/(2*math.pi), joint_geometry(cap, 24)["target"])
            errors = []
            for delta in (0.08, 0.04):
                sigma = 0.04*delta**2
                actual = axial_short_density(cap, sigma, delta, 24, beta=beta)
                errors.append(abs(actual-float(jet @ short_monomials(sigma, delta))))
            self.assertLess(errors[1], errors[0]/20)

    def test_quadratic_model_density_limit_and_negative_weight(self):
        jet = axial_jet(AxialCap())["angular"]
        target = (jet[2]-3*jet[3])/(2*math.pi)
        for sign in (1, -1):
            values = [jet_short_action(sign*jet, rho, 0.15) for rho in (1e6, 1e9)]
            self.assertLess(abs(values[1]-sign*target), abs(values[0]-sign*target))
            self.assertLess(abs(values[1]-sign*target), 0.04*target)

    def test_curved_radial_full_short_long_identity(self):
        result = action(RadialCap(), 10000, order=16, delta=0.08)
        short = result["point"]-result["pair_diagonal"]
        long = result["pair_long_near_null"]+result["pair_long_timelike"]
        self.assertNear(short-long, result["action"], 1e-12)
        self.assertGreater(abs(long), 0.001)  # finite density: never silently discard it

    def test_invalid_parameters(self):
        for call in (lambda: short_monomials(-1, 1), lambda: short_monomials(0, 0),
                     lambda: short_monomials(float("nan"), 1),
                     lambda: axial_jet(AxialCap(), weight=lambda x: x),
                     lambda: axial_jet(RadialCap()),
                     lambda: axial_short_density(AxialCap(), 0, 1, beta=0.5),
                     lambda: axial_short_density(AxialCap(), 0, 1, beta=1),
                     lambda: jet_short_action([1, 2], 1, 1),
                     lambda: jet_short_action([1, 2, 3, 4], 0, 1)):
            with self.assertRaises((ValueError, TypeError)):
                call()


if __name__ == "__main__":
    unittest.main()
