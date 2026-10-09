"""Diagnostics for the derived #150 null-edge/face/joint remainder proof.

The analytic estimates are in notes/general-metric-short-remainders.md. These
finite tests are not substitutes for that proof or independent human review.
"""

import math
import unittest

import mpmath as mp
import numpy as np
import sympy as s
from scipy.optimize import brentq

from general_metric_short import (
    lapse_face_gap, product_interval_ratio, product_null_rescaled_metric,
    ultrastatic_rest_volume,
)


def comparison_density(d, k, w, epsilon=mp.mpf("0.4"), c=mp.mpf("0.7")):
    """Nontrivial analytic test family for S9, not a proposed geometric H.

    Phi(e,R)=(1+c*e^2)*R, amplitude exp(e)*(1-U)^(d-2)/Phi_R.
    Return actual-minus-entire-jet, its actual zero-probe polynomial, and the
    2D second-jet moving-diagonal term. Integrate with arbitrary precision to
    distinguish a critical contact from a higher-order remainder.
    """
    p, m, N = 3-k, d-2, d//2
    nu = mp.sqrt(2*w/(1+mp.sqrt(1+4*c*w)))
    reference = mp.sqrt(w)

    def actual(v):
        scale = 1+c*v*v
        return v**(d-3+k)*(1-w/(v*v*scale))**m*mp.exp(v)/scale

    def jet(v):
        zeta = w/(v*v)
        base = (1-zeta)**m
        value = base
        if p >= 2:
            value += v*base
        if p == 3:
            derivative = m*zeta*(1-zeta)**(m-1) if m else 0
            value += v*v*(base/2+c*(derivative-base))
        return v**(d-3+k)*value

    contact = c*w/2 if d == 2 and k == 0 else mp.mpf(0)
    difference = mp.quad(actual, [nu, epsilon]) - mp.quad(jet, [reference, epsilon]) - contact
    polynomial = mp.mpf(0)
    for j in range(min(m, N)+1):
        # Integrate the zero probe by its convergent analytic series. Direct
        # exp(v)-Taylor subtraction times v^-3 is ill-conditioned even at high
        # precision near the quadrature endpoint. From (1+c*v^2)F' =
        # (1+c*v^2-2*(j+1)*c*v)F obtain these exact coefficient recurrences.
        coefficients = [mp.mpf(1)]
        for n in range(180):
            previous = coefficients[n-1] if n >= 1 else 0
            before = coefficients[n-2] if n >= 2 else 0
            coefficients.append((coefficients[n]-c*(2*(j+1)+n-1)*previous+c*before)/(n+1))
        probe_integral = mp.fsum(
            coefficients[n]*epsilon**(d-2+k-2*j+n)/(d-2+k-2*j+n)
            for n in range(p, len(coefficients)))
        coefficient = (-1)**j * math.comb(m, j) * probe_integral
        polynomial += coefficient*w**j
    return difference, polynomial, contact


class GeneralMetricShortRemainderTests(unittest.TestCase):
    def test_exact_null_rescaling_of_nonconformally_flat_metric(self):
        point = np.array([0.37, 0.46, 0.2, -0.1])
        v = 0.3
        for e in (1.0, 0.2, 0.02, 0.002):
            longitudinal, other, transverse, _ = point
            spatial = np.array([v*(longitudinal-e*e*other)/2, v*e*transverse])
            radius = np.linalg.norm(spatial)
            sinc2 = np.sinc(radius/np.pi)**2
            metric = np.diag([1.0, -1.0, -1.0, -1.0])
            metric[1:3, 1:3] = -sinc2*np.eye(2)-(1-sinc2)*np.outer(spatial, spatial)/radius**2
            jacobian = v*np.array([[0.5, e*e/2, 0, 0],
                                   [0.5, -e*e/2, 0, 0],
                                   [0, 0, e, 0], [0, 0, 0, e]])
            actual = jacobian.T @ metric @ jacobian / (v*v*e*e)
            regular = product_null_rescaled_metric(v, e, point)
            np.testing.assert_allclose(actual, regular, atol=1e-10, rtol=1e-10)
        null = product_null_rescaled_metric(v, 0, point)
        flat = product_null_rescaled_metric(0, 0, point)
        self.assertGreater(np.linalg.norm(null-flat), 1e-4)
        errors = [np.linalg.norm(product_null_rescaled_metric(v, e, point)-null)
                  for e in (0.1, 0.01, 0.001)]
        self.assertLess(errors[-1], errors[0]/1000)
        self.assertEqual(np.count_nonzero(np.linalg.eigvalsh(null) > 0), 1)
        np.testing.assert_allclose(product_null_rescaled_metric(v, -0.1, point),
                                   product_null_rescaled_metric(v, 0.1, point))

    def test_actual_nearly_null_interval_with_directional_curvature(self):
        # Ric(Delta,Delta)=-(1-R)^2/4 and scalar=2, independently of the volume.
        for ratio in (0.02, 0.3, 1.0):
            h2 = (1-ratio)**2/120 - ratio/90
            errors = []
            for v in (0.3, 0.15):
                phase = product_interval_ratio(v, ratio, order=28)
                finer = product_interval_ratio(v, ratio, order=40)
                self.assertLess(abs(phase-finer), 2e-8)
                errors.append(abs((finer-1)/v**2-h2))
            self.assertLess(errors[-1], 3e-5)
            self.assertLess(errors[-1], errors[0]/2)
        # The direction term survives at the null edge; scalar-only is wrong.
        near_null = product_interval_ratio(0.2, 0.002, order=40)
        self.assertGreater(near_null-1, 2e-4)
        self.assertAlmostEqual(product_interval_ratio(0.2, 1, order=40),
                               ultrastatic_rest_volume(0.2)/(np.pi/24*0.2**4), places=9)
        with self.assertRaises(ValueError):
            product_interval_ratio(0.2, 0)
        with self.assertRaises(ValueError):
            product_interval_ratio(2, 1)

    def test_all_three_moving_contact_formulas(self):
        lam, v, upper = s.symbols("lam v upper")
        nu = s.Rational(1, 5)+lam/7+lam**2/11+lam**3/13
        amplitude = (1+lam*v+lam**2*v**2+lam**3*v**3)*(1+v+v*v)
        primitive = s.integrate(amplitude, v)
        integral = primitive.subs(v, upper)-primitive.subs(v, nu)
        dot, ddot, dddot = [s.diff(nu, lam, j) for j in (1, 2, 3)]
        contacts = [
            amplitude*dot,
            2*s.diff(amplitude, lam)*dot+s.diff(amplitude, v)*dot**2+amplitude*ddot,
            3*s.diff(amplitude, lam, 2)*dot+3*s.diff(amplitude, lam, v)*dot**2
            +s.diff(amplitude, v, 2)*dot**3+3*s.diff(amplitude, lam)*ddot
            +3*s.diff(amplitude, v)*dot*ddot+amplitude*dddot,
        ]
        for p, contact in enumerate(contacts, 1):
            bulk_primitive = s.integrate(s.diff(amplitude, lam, p), v)
            bulk = bulk_primitive.subs(v, upper)-bulk_primitive.subs(v, nu)
            self.assertEqual(s.expand(s.diff(integral, lam, p)-bulk+contact.subs(v, nu)), 0)
            self.assertNotEqual(contact.subs({v: s.Rational(1, 3), lam: 0}), 0)

    def test_dimension_indexed_remainder_bounds_and_low_dimensional_contact(self):
        with mp.workdps(65):
            for d in range(2, 10):
                for k in range(3):
                    quotients = []
                    for value in ("0.0001", "0.00001", "0.000001"):
                        w = mp.mpf(value)
                        difference, polynomial, contact = comparison_density(d, k, w)
                        power = mp.mpf(d//2) + (mp.mpf("0.5") if d % 2 == 0 else 1)
                        bound = w**power * (1 if d % 2 == 0 else 1+abs(mp.log(w)))
                        quotients.append(abs(difference-polynomial)/bound)
                        # Constants depend on dimension and amplitude derivatives;
                        # the theorem asserts no dimension-independent constant.
                        self.assertLess(quotients[-1], 2**d, (d, k, value))
                        if d == 2 and k == 0:
                            self.assertGreater(contact, 0)
                            # Omitting the actual second-jet contact leaves a critical
                            # w term, not the established O(w^(3/2)) remainder.
                            self.assertGreater(abs(difference+contact-polynomial)/w,
                                               mp.mpf("0.3"))
                    self.assertLess(quotients[-1], 3*quotients[0]+mp.mpf("1e-20"))

    def test_actual_source_dependent_face_and_corner_roots(self):
        v, ratio, s0, beta = 0.2, 0.3, 0.04, 0.6
        def face_root(beta):
            return brentq(lambda depth: depth-beta*lapse_face_gap(s0, depth, v, ratio)[0],
                          0, 2*v, xtol=1e-15)
        depth = face_root(beta)
        gap, _, gap_a = lapse_face_gap(s0, depth, v, ratio)
        h = 1e-5
        actual_derivative = (face_root(beta+h)-face_root(beta-h))/(2*h)
        self.assertAlmostEqual(actual_derivative, gap/(1-beta*gap_a), places=9)
        self.assertGreater(abs(actual_derivative-gap), 1e-3)

        def corner_map(beta, gamma):
            alpha = beta+(1-beta)*gamma
            root = brentq(lambda b: b-lapse_face_gap(beta*b, alpha*b, v, ratio)[0],
                          0, 2*v, xtol=1e-15)
            return np.array([beta*root, alpha*root]), root, alpha
        beta, gamma = 0.35, 0.6
        (height, depth), root, alpha = corner_map(beta, gamma)
        gap, ds, da = lapse_face_gap(height, depth, v, ratio)
        jacobian = np.column_stack((
            (corner_map(beta+h, gamma)[0]-corner_map(beta-h, gamma)[0])/(2*h),
            (corner_map(beta, gamma+h)[0]-corner_map(beta, gamma-h)[0])/(2*h)))
        actual = np.linalg.det(jacobian)
        expected = (1-beta)*root**2/(1-beta*ds-alpha*da)
        self.assertAlmostEqual(root, gap, places=13)
        self.assertAlmostEqual(actual, expected, places=11)
        self.assertGreater(abs(actual-(1-beta)*root**2/(1-beta*ds)), 1e-4)
        self.assertTrue(0 < height < depth < gap)

    def test_general_face_flux_algebra_keeps_metric_and_both_field_derivatives(self):
        t, z = s.symbols("t z")
        w, chi, phi, n0, n1 = [s.Function(name)(t, z) for name in ("w", "chi", "phi", "n0", "n1")]
        f = s.Function("f")(z)
        Q = w*chi*phi
        norm = n0-s.diff(f, z)*n1
        boxF = (s.diff(w*n0, t)+s.diff(w*n1, z))/w
        normal = lambda field: n0*s.diff(field, t)+n1*s.diff(field, z)
        trace_divergence = s.diff(Q*n1, z)+s.diff(f, z)*s.diff(Q*n1, t)
        actual_jet_response = -Q*boxF+s.diff(Q*norm, t)-2*w*chi*normal(phi)
        independent_flux = w*(phi*normal(chi)-chi*normal(phi))-trace_divergence
        self.assertEqual(s.expand(actual_jet_response-independent_flux), 0)
        # Freezing the source density would remove a generically nonzero term.
        self.assertNotEqual(s.expand(actual_jet_response.subs(s.diff(w, t), 0)-independent_flux), 0)


if __name__ == "__main__":
    unittest.main()
