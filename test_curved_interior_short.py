"""Finite certificates and independent quadrature for the written #74 proof.

The full-cone fixtures lie in the original unit-ball, height-1/4 region with
future face t=1/8. These tests do not certify a universal limit or a rate.
The production observable and the already proved long theorem are unchanged.
"""

from functools import lru_cache
import unittest

import mpmath as mp
import numpy as np
import sympy as s

from conformal_geometry import conformal_curvature
from curved_bulk_pilot import scalar_curvature, second_jet_response
from curved_interior_short import (
    angular_density_jet, check_interior_short_identities,
    interpolated_phase_factor, third_lower_boundary_derivative,
)

LD = np.longdouble
PI = LD("3.1415926535897932384626433832795028841971693993751")
C = 4/np.sqrt(LD(6))
VOLUME_CONSTANT = PI/24


@lru_cache(maxsize=None)
def gauss_nodes(order):
    """Generate weights above float64 precision before long-double evaluation."""
    with mp.workdps(45):
        nodes, weights = mp.gauss_quadrature(order, "legendre")
        return (np.array([LD(mp.nstr((z+1)/2, 40)) for z in nodes]),
                np.array([LD(mp.nstr(w/2, 40)) for w in weights]))


def actual_h(t, u, v):
    return 1+t*t+t*(u+v)/2+3*(u+v)**2/40-u*v/30


def kernel(z):
    return (1-9*z+8*z*z-LD(4)/3*z**3)*np.exp(-z)


def field_value(field, time, radius):
    # Sphere averages at source spatial position zero, not a partner restriction.
    if field == "one":
        return np.ones_like(time+radius)
    if field == "time2":
        return time*time
    if field == "space2":
        return radius*radius
    raise ValueError("unknown regression field")


def short_probe(t, rho, delta=1/16, order=48, field="one", *,
                frozen_phase=False, target_measure=True):
    """Actual, full finite-cutoff jet and derived limiting responses at (t,0).

    Actual integral: solve the curved phase and its diagonal independently.
    Jet integral: use the entire (C11)/(C12), not an assumed target amplitude.
    Subtract only exact zero-moment constants before numerical cancellation.
    Integrate z=sqrt(c*rho)*w to 12 (Gaussian tail), requiring the actual and
    jet upper supports to exceed 12. This is high-density diagnostic code.
    The two flags are deliberately WRONG-observable negative controls.
    """
    t, rho, delta = map(lambda value: LD(str(value)), (t, rho, delta))
    if not (-LD(1)/8 < t and t+delta < LD(1)/8):
        raise ValueError("closed short cone must be inside the fixture")
    ns, ws = gauss_nodes(order)
    q = 1+t*t
    h = (lambda u, v: np.ones_like(u+v)*q) if frozen_phase else lambda u, v: actual_h(t, u, v)
    scale = np.sqrt(VOLUME_CONSTANT*rho)
    if min(delta**2*np.sqrt(h(delta, delta))*scale,
           delta**2*np.sqrt(q)*scale) <= 12:
        raise ValueError("density too small for the diagnostic's fixed Gaussian tail")
    edges = list(map(LD, ("0", ".000001", ".0001", ".01", ".1", ".5", "1", "2", "4", "8", "12")))
    z = np.concatenate([a+(b-a)*ns for a, b in zip(edges, edges[1:])])
    zw = np.concatenate([(b-a)*ws for a, b in zip(edges, edges[1:])])
    w = z/scale
    nu = np.sqrt(w)/q**LD(".25")
    for _ in range(8):
        hd = h(nu, nu)
        hd_prime = 0 if frozen_phase else t+LD(8)/15*nu
        nu -= (nu*nu*np.sqrt(hd)-w)/(nu*(4*hd+nu*hd_prime)/(2*np.sqrt(hd)))
    log_range = np.log(delta/nu)[:, None]
    v = nu[:, None]*np.exp(ns[None, :]*log_range)
    u = w[:, None]/v/np.sqrt(h(0, v))
    for _ in range(8):
        hu = 0 if frozen_phase else t/2+3*u/20+7*v/60
        fu = v*(2*h(u, v)+u*hu)/(2*np.sqrt(h(u, v)))
        u -= (u*v*np.sqrt(h(u, v))-w[:, None])/fu
    hu = 0 if frozen_phase else t/2+3*u/20+7*v/60
    fu = v*(2*h(u, v)+u*hu)/(2*np.sqrt(h(u, v)))
    T, r = (u+v)/2, (v-u)/2
    density = lambda time: 1+time*time if target_measure else np.ones_like(time)
    amplitude = density(t+T)*field_value(field, t+T, r)*(v-u)**2/(8*fu)

    def null_amplitude(v0):
        return density(t+v0/2)*field_value(field, t+v0/2, v0/2)*v0/(8*np.sqrt(h(0, v0)))

    # B(w)-B(0), subtracting under the radial integral to avoid catastrophic
    # near-null constant quadrature error. Its original signed integral is
    # identical on the whole half-line since integral K(z^2) dz = 0.
    difference = 4*PI*(
        np.sum(ws[None, :]*(amplitude-null_amplitude(v))*v*log_range, axis=1)
        - np.sum(ws[None, :]*nu[:, None]*null_amplitude(nu[:, None]*ns[None, :]), axis=1))
    pair = np.sum(zw*kernel(z*z)*difference)/scale
    phi0, pt, ptt, lap = {
        "one": (LD(1), LD(0), LD(0), LD(0)),
        "time2": (t*t, 2*t, LD(2), LD(0)),
        "space2": (LD(0), LD(0), LD(0), LD(6)),
    }[field]
    actual = C*np.sqrt(rho)*(phi0-rho*pair)

    # Independent model quadrature of the original K, K', K'' terms.
    a, d = 2*t/q, 2/q
    flat_scale = np.sqrt(VOLUME_CONSTANT*rho*q)
    sigma, zz = z/flat_scale, z*z
    log_sigma = np.log(sigma/delta**2)
    # Only constants of J0,J1,J2 are subtracted. Their respective signed
    # moments (including sigma*J0 and the K'/K'' terms) are exactly zero.
    j0 = -sigma**2/(8*delta**2)+sigma*log_sigma/4
    j1 = ((delta-sigma/delta)**3-delta**3)/24
    j2 = -sigma**4/(64*delta**4)+sigma**2*log_sigma/16
    k = kernel(zz)
    kp = (-10+25*zz-12*zz**2+LD(4)/3*zz**3)*np.exp(-zz)
    kpp = (35-49*zz+16*zz**2-LD(4)/3*zz**3)*np.exp(-zz)
    correction = (j1*(pt*k+a*phi0*(k+zz*kp/2))
                  + (ptt*j2/2+lap*(j2-sigma*j0)/6)*k
                  + a*pt*j2*(k+zz*kp/2)
                  + phi0*d*(j2*k/2+zz*(3*j2/20-sigma*j0/60)*kp)
                  + phi0*a*a*j2*(zz*kp/2+zz*zz*kpp/8))
    # The constant flat-density/constant-field part is integrated exactly.
    model = (phi0*C*np.sqrt(rho)*np.exp(-VOLUME_CONSTANT*rho*q*delta**4)
             - C*rho**LD("1.5")*2*PI*q/flat_scale*np.sum(zw*correction))
    target = (ptt-lap+a*pt/2+(3*d/4-9*a*a/16)*phi0)/np.sqrt(q)
    return np.array((actual, model, target), dtype=LD)


def original_short_probe(t, rho, delta=1/16, order=64):
    """Independent untransformed u,v quadrature; no phase push or model jet."""
    t, rho, delta = map(lambda value: LD(str(value)), (t, rho, delta))
    ns, ws = gauss_nodes(order)
    v = delta*ns[:, None]
    u = v*ns[None, :]
    T = (u+v)/2
    values = ((v-u)**2/8*(1+(t+T)**2)
              * kernel(VOLUME_CONSTANT*rho*(u*v)**2*actual_h(t, u, v)))
    pair = 4*PI*np.sum(ws[:, None]*ws[None, :]*delta*v*values)
    return C*np.sqrt(rho)*(1-rho*pair)


class InteriorShortCertificates(unittest.TestCase):
    def test_exact_certificates(self):
        check_interior_short_identities()

    def test_interpolation_endpoints_are_not_frozen(self):
        t, u, v = map(s.Rational, ("1/20", "1/64", "1/16"))
        self.assertEqual(interpolated_phase_factor(t, u, v, 0), 1+t*t)
        self.assertEqual(interpolated_phase_factor(t, u, v, 1), actual_h(t, u, v))
        self.assertNotEqual(interpolated_phase_factor(t, u, v, 1), 1+t*t)

    def test_full_jet_field_and_kernel_derivatives(self):
        q = s.Symbol("q", positive=True)
        q1, q2, T, sigma, z, phi, pt, ptt, lap, k0, k1, k2 = s.symbols(
            "q1 q2 T sigma z phi pt ptt lap k0 k1 k2")
        jet = angular_density_jet(q, q1, q2, T, sigma, z, phi, pt, ptt, lap, k0, k1, k2)
        self.assertEqual(s.expand(jet[2]).coeff(k2), phi*q1*q1*T*T*z*z/(8*q))
        self.assertEqual(s.expand(s.diff(jet[2], lap)-q*(T*T-sigma)*k0/6), 0)
        self.assertEqual(s.expand(s.diff(jet[2], pt)-q1*T*T*(k0+z*k1/2)), 0)

    def test_moving_diagonal_terms_cannot_be_dropped(self):
        # Every term is nonzero. Distinguishes the formula from a fixed-domain
        # integral derivative and from omitting the endpoint acceleration.
        values = third_lower_boundary_derivative(1000, 2, 3, 5, 7, 11, 13, 17, 19, 23)
        terms = (3*7*17, 3*11*17**2, 13*17**3, 3*3*19, 3*5*17*19, 2*23)
        self.assertEqual(values, 1000-sum(terms))
        for term in terms:
            self.assertNotEqual(values, 1000-sum(terms)+term)
        # For j=0,1,2, all six contacts scale as nu^(5-2*j);
        # the interior third-lambda derivative scales as v^(4-2*j).
        for j in range(3):
            powers = (1+2-2*j+2, 1+1-1-2*j+4, 1-2-2*j+6,
                      1+1-2*j+3, 1-1-2*j+5, 1-2*j+4)
            self.assertEqual(set(powers), {5-2*j})
            self.assertGreaterEqual(4-2*j, 0)

    def test_independent_metric_contraction_and_box(self):
        t, x, y, z = s.symbols("t x y z", real=True)
        coordinates = (t, x, y, z)
        q = 1+t*t
        metric, _, _, scalar_opposite = conformal_curvature(q**s.Rational(1, 4), coordinates)
        # The geometry calculator deliberately uses the opposite Riemann sign.
        scalar = -scalar_opposite
        self.assertEqual(s.simplify(scalar-scalar_curvature(t)), 0)
        self.assertEqual(scalar.subs(t, 0), 3)
        phi = 1+2*t+3*t*t+5*x+7*x*x+11*y*y+13*z*z+17*t*x+19*t**3
        inverse = metric.inv()
        box = sum(s.diff(q*inverse[i, j]*s.diff(phi, coordinates[j]), coordinates[i])
                  for i in range(4) for j in range(4))/q
        response = second_jet_response(q, 2*t, 2, phi, s.diff(phi, t), s.diff(phi, t, 2),
                                       sum(s.diff(phi, v, 2) for v in (x, y, z)))
        self.assertEqual(s.simplify(response-box-scalar*phi/2), 0)
        self.assertNotEqual(s.simplify(response-scalar*phi/2), 0)

    def test_field_angular_average(self):
        # Direct sphere integration for an anisotropic field with a mixed term.
        lam, T, r, t, mu, theta = s.symbols("lam T r t mu theta", real=True)
        n1, n2, n3 = s.sqrt(1-mu*mu)*s.cos(theta), s.sqrt(1-mu*mu)*s.sin(theta), mu
        phi = (1+2*(t+lam*T)+3*(t+lam*T)**2+5*lam*r*n1
               +7*(lam*r*n1)**2+11*(lam*r*n2)**2+13*(lam*r*n3)**2
               +17*(t+lam*T)*lam*r*n1)
        average = s.integrate(phi, (theta, 0, 2*s.pi), (mu, -1, 1))/(4*s.pi)
        self.assertEqual(s.expand(average-(1+2*t+3*t*t+lam*T*(2+6*t)
                                          +lam**2*(3*T*T+31*r*r/3))), 0)


class InteriorShortQuadrature(unittest.TestCase):
    def test_original_coordinate_and_phase_integrals_agree(self):
        phase = short_probe(.05, 1e8)[0]
        original = original_short_probe(.05, 1e8)
        refined = original_short_probe(.05, 1e8, order=80)
        self.assertLess(abs(original-refined), 2e-7)
        self.assertLess(abs(phase-refined), 2e-7)

    def test_actual_signed_remainder_and_nonconstant_fields(self):
        for t in (0, .05):
            for field in ("one", "time2", "space2"):
                with self.subTest(t=t, field=field):
                    low = short_probe(t, 1e8, field=field)
                    high = short_probe(t, 1e12, field=field)
                    self.assertLess(abs(high[0]-high[1]), 5e-5)
                    self.assertLess(abs(high[0]-high[1]), abs(low[0]-low[1]))
                    self.assertLess(abs(high[0]-high[2]), .011)
                    self.assertLess(abs(high[0]-high[2]), abs(low[0]-low[2])/20)

    def test_high_density_quadrature_refinement(self):
        for field in ("one", "time2", "space2"):
            with self.subTest(field=field):
                ordinary = short_probe(.05, 1e12, field=field)
                refined = short_probe(.05, 1e12, field=field, order=64)
                self.assertLess(np.max(np.abs(ordinary-refined)), 2e-7)

    def test_fixed_cutoffs_retain_finite_terms(self):
        # Each cutoff is held fixed while density increases; no cutoff limit.
        for delta in (1/16, .1):
            low = short_probe(0, 1e8, delta, field="space2")
            high = short_probe(0, 1e12, delta, field="space2")
            self.assertGreater(abs(low[1]-low[2]), .3)
            self.assertLess(abs(high[0]-high[1]), 5e-5)
            self.assertLess(abs(high[0]-high[2]), .011)
        self.assertGreater(abs(short_probe(0, 1e8, 1/16, field="space2")[1]
                               - short_probe(0, 1e8, .1, field="space2")[1]), .5)

    def test_negative_controls_for_phase_and_measure(self):
        physical = short_probe(0, 1e10)[0]
        frozen = short_probe(0, 1e10, frozen_phase=True)[0]
        self.assertLess(abs(physical-LD("1.5")), .01)
        self.assertGreater(abs(frozen-LD("1.5")), .4)
        missing_measure = short_probe(.05, 1e10, target_measure=False)[0]
        self.assertGreater(abs(missing_measure), 100)

    def test_compact_source_outer_measure_and_nonzero_bulk(self):
        # chi(t,z)=beta(t/epsilon)*psi(z), normalized separately in dt and dz;
        # psi is any normalized smooth bump in |z|<epsilon. Translation
        # invariance of the inner phi=1 integral makes its spatial integral 1.
        # The actual outer metric measure still contributes q(t), not 1.
        ns, ws = gauss_nodes(24)
        epsilon = LD(1)/64
        times = epsilon*(2*ns-1)
        weights = ws*np.exp(-1/(1-(times/epsilon)**2))
        weights /= np.sum(weights)
        q = 1+times*times
        results = []
        for rho in (1e8, 1e12):
            values = np.array([short_probe(t, rho) for t in times])
            results.append(np.sum(weights[:, None]*q[:, None]*values, axis=0))
        low, high = results
        with mp.workdps(40):
            ep = mp.mpf(1)/64
            beta = lambda t: mp.exp(-1/(1-(t/ep)**2))
            independent = mp.quad(lambda t: beta(t)*3*(1-t*t/2)/(2*(1+t*t)**mp.mpf("1.5")),
                                  [-ep, 0, ep])/mp.quad(beta, [-ep, 0, ep])
        self.assertLess(abs(high[2]-LD(str(independent))), 2e-8)
        self.assertGreater(high[2], 1)
        self.assertLess(abs(high[0]-high[1]), 3e-5)
        self.assertLess(abs(high[0]-high[2]), .001)
        self.assertLess(abs(high[0]-high[1]), abs(low[0]-low[1]))
        without_outer_measure = np.sum(weights*values[:, 2])
        self.assertGreater(high[2]-without_outer_measure, 1e-5)


if __name__ == "__main__":
    unittest.main()
