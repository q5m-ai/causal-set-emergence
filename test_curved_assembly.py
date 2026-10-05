"""Integrated finite diagnostics for #76, not a proof by convergence fitting.

The planar-future unequal-axis pilot permits an independent whole-pair integral
in source time, target time and spatial radius. Its future cone is not cut into
isolated chart regions. All quadratures are finite-density regression evidence;
refinement tolerances are not certified error bounds or asymptotic rates.
"""

import math
import unittest

import mpmath as mp
import numpy as np
import sympy as s
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad

from calculations import ellipsoid_action
from conformal_geometry import conformal_curvature
from curved_assembly import (
    bulk_time_primitive, check_curved_assembly_identities, ordered_layer_kernel,
)
from curved_bulk_pilot import scalar_curvature
from curved_joint_corner import future_normal, minkowski_inner
from test_curved_boundary_collar import face_original, planar_corner


DEPTH, FUTURE, AXES = .25, .125, (1, 2, 3)
SPATIAL_VOLUME = 4*math.pi*math.prod(AXES)/3
C = 4/math.sqrt(6)


def pilot_integrals(rho, *, delta=None, part="full", order=32, curved=True,
                    omega=1, chi=lambda t: 1, phi=lambda t: 1,
                    measures="both", freeze_phase=False):
    """Independent original-coordinate quadrature of this fixed pilot only.

    At time t=f-H*(1-a**2), the source slice volume is V_spatial*a**3.
    The lower causal envelope admits every future partner with T < f-t;
    the future plane is the only remaining restriction. The angular integral
    is exactly 4*pi. No phase straightening, jet, or proposed limit is used.
    `full_cone` includes the auxiliary outside-region partners of H3; its
    interval law is ambient, not asserted equal to their restricted volume.
    Wrong-measure/frozen-phase options are deliberate negative controls.
    """
    if part not in ("full", "short", "long", "full_cone"):
        raise ValueError("unknown pair domain")
    if rho <= 0 or omega <= 0:
        raise ValueError("positive density and conformal factor required")
    if part != "full" and (delta is None or not 0 < delta < DEPTH):
        raise ValueError("a fixed cutoff in (0,depth) is required for this diagnostic")
    if measures not in ("both", "source", "target"):
        raise ValueError("unknown endpoint measure control")
    ns, ws = leggauss(order)
    ns, ws = (ns+1)/2, ws/2
    density = lambda t: omega**4*(1+t*t if curved else np.ones_like(t))
    # Split the source variable wherever a sharp-cutoff panel changes type.
    source_edges = [0., 1.]
    if delta is not None:
        source_edges += [math.sqrt(1-delta/DEPTH), math.sqrt(1-delta/(2*DEPTH))]
    point, pair = 0., 0.
    layers = np.zeros(4)
    for lo, hi in zip(sorted(source_edges), sorted(source_edges)[1:]):
        for a, aw in zip(lo+(hi-lo)*ns, (hi-lo)*ws):
            t = FUTURE-DEPTH*(1-a*a)
            source_jac = SPATIAL_VOLUME*2*DEPTH*a**4*aw
            point += source_jac*density(t)*chi(t)*phi(t)
            upper = delta if part == "full_cone" else FUTURE-t
            edges = [0., upper]
            if part != "full":
                edges += [p for p in (delta/2, delta) if 0 < p < upper]
            edges = sorted(set(edges))
            for left, right in zip(edges, edges[1:]):
                T = (left+(right-left)*ns)[:, None]
                rlo, rhi = np.zeros_like(T), T.copy()
                if part in ("short", "full_cone"):
                    rhi = np.minimum(T, np.maximum(0., delta-T))
                elif part == "long":
                    rlo = np.minimum(T, np.maximum(0., delta-T))
                r = rlo+(rhi-rlo)*ns[None, :]
                jac = (right-left)*(rhi-rlo)*ws[:, None]*ws[None, :]*4*math.pi*r*r
                # Independent midpoint interval formula, rather than calling
                # the upstream null-coordinate H helper.
                sigma = T*T-r*r
                H = omega**4*(1+(t+T/2)**2+T*T/20-sigma/30 if curved else 1)
                if freeze_phase:
                    H = density(t)
                z = math.pi/24*rho*sigma*sigma*H
                source_density = density(t) if measures != "target" else 1
                target_density = density(t+T) if measures != "source" else 1
                weight = source_jac*jac*source_density*target_density*chi(t)*phi(t+T)
                kernel = (1-9*z+8*z*z-4*z**3/3)*np.exp(-z)
                pair += np.sum(weight*kernel)
                for k in range(4):
                    layers[k] += np.sum(weight*np.exp(-z)*z**k/math.factorial(k))
    if part == "long":
        point = 0.  # The single point term belongs to short only.
    return {"point": point, "pair": pair, "layers": layers,
            "action": C*math.sqrt(rho)*(point-rho*pair)}


class CurvedAssemblyTests(unittest.TestCase):
    def test_exact_assembly_and_layer_certificates(self):
        check_curved_assembly_identities()

    def test_independent_curvature_and_nonzero_whole_bulk(self):
        coordinates = s.symbols("t x y z", real=True)
        t = coordinates[0]
        metric, _, _, opposite_scalar = conformal_curvature((1+t*t)**s.Rational(1, 4), coordinates)
        self.assertEqual(s.simplify(metric.det()+(1+t*t)**2), 0)
        self.assertEqual(s.simplify(opposite_scalar+scalar_curvature(t)), 0)
        self.assertGreater(float(scalar_curvature(0)-scalar_curvature(s.Rational(1, 16))), 0)
        primitive = s.lambdify(t, bulk_time_primitive(t), "numpy")
        # Spatial radial integration of an exact time primitive, versus an
        # independent source-time slicing of the whole region.
        radial_bulk = 4*math.pi*math.prod(AXES)*quad(
            lambda r: r*r*(primitive(FUTURE)-primitive(FUTURE-DEPTH*(1-r*r))), 0, 1,
            epsabs=1e-12)[0]
        time_bulk = quad(lambda t: SPATIAL_VOLUME*(1-(FUTURE-t)/DEPTH)**1.5
                         *1.5*(1-t*t/2)/(1+t*t)**1.5, FUTURE-DEPTH, FUTURE,
                         epsabs=1e-12, epsrel=1e-12)[0]
        self.assertAlmostEqual(radial_bulk, time_bulk, places=11)
        flat_volume = 8*math.pi*math.prod(AXES)*DEPTH/15
        lower_bound = flat_volume*1.5*(1-1/128)/(65/64)**1.5
        self.assertGreater(time_bulk, lower_bound)
        self.assertGreater(lower_bound, 3.6)
        # An interior-only calculation cannot stand in for the whole bulk.
        interior = quad(lambda t: SPATIAL_VOLUME*(1-(FUTURE-t)/DEPTH)**1.5
                        *1.5*(1-t*t/2)/(1+t*t)**1.5, -.04, .04)[0]
        self.assertGreater(time_bulk-interior, 2.)

    def test_variable_angle_and_independently_induced_joint(self):
        q = s.Rational(65, 64)
        for k, expected in ((s.Rational(1, 2), 2), (s.Rational(1, 6), 6)):
            future = future_normal((0, 0, 0), q)
            past = future_normal((k, 0, 0), q)
            gamma = s.sqrt(q)*minkowski_inner(future, past)
            self.assertEqual(s.simplify(gamma/s.sqrt(gamma*gamma-1)), expected)
        # Ellipsoid sphere parametrization: Euclidean spatial area density
        # abc*|B^-1 n|; the conformal induced area is sqrt(q) times this.
        ns, ws = leggauss(24)
        target = 0.
        for mu, w in zip(ns, ws):
            for az in (np.arange(48)+.5)*2*math.pi/48:
                n = np.array([mu, math.sqrt(1-mu*mu)*math.cos(az),
                              math.sqrt(1-mu*mu)*math.sin(az)])
                gradient_norm = 2*DEPTH*np.linalg.norm(n/AXES)
                gamma = 1/math.sqrt(1-gradient_norm**2)
                induced = math.sqrt(float(q))*math.prod(AXES)*np.linalg.norm(n/AXES)
                target += w*2*math.pi/48*induced*gamma/math.sqrt(gamma*gamma-1)
        self.assertAlmostEqual(target, 48*math.pi*math.sqrt(65/64), places=10)
        self.assertGreater(target-48*math.pi, 1.)  # Flat area would be wrong.

    def test_full_action_short_long_and_fixed_cutoff_accounting(self):
        rho = 200000.
        full = pilot_integrals(rho, order=48)
        refined = pilot_integrals(rho, order=60)
        self.assertAlmostEqual(full["action"], refined["action"], delta=2e-8)
        short_values = []
        for delta in (.07, .14):
            short = pilot_integrals(rho, delta=delta, part="short", order=48)
            long = pilot_integrals(rho, delta=delta, part="long", order=48)
            self.assertAlmostEqual(short["action"]+long["action"], full["action"], delta=2e-8)
            self.assertAlmostEqual(short["point"], full["point"], places=12)
            self.assertEqual(long["point"], 0)
            self.assertGreater(abs(long["action"]), 1.)
            short_values.append(short["action"])
        self.assertGreater(abs(short_values[0]-short_values[1]), 1.)

    def test_full_face_corner_restores_actual_short_domain(self):
        rho, delta = 200000., .08
        actual = pilot_integrals(rho, delta=delta, part="short")
        auxiliary = pilot_integrals(rho, delta=delta, part="full_cone")
        face = SPATIAL_VOLUME*float(face_original(0, rho, delta, epsilon=0, order=32))
        corner = float(planar_corner(rho, delta, order=32))
        self.assertAlmostEqual(auxiliary["action"]+face+corner, actual["action"], delta=2e-8)
        self.assertGreater(abs(corner), .1)
        self.assertGreater(abs(face), 1.)
        self.assertGreater(abs(auxiliary["action"]-actual["action"]), 1.)

    def test_both_endpoint_partitions_need_cross_chart_pairs(self):
        rho = 30000.
        sources = (lambda t: 1+2*t, lambda t: -2*t)  # Signed overlapping weights.
        targets = (lambda t: .4+3*t, lambda t: .6-3*t)
        pieces = [[pilot_integrals(rho, chi=chi, phi=phi, order=20)
                   for phi in targets] for chi in sources]
        full = pilot_integrals(rho, order=20)
        for key in ("point", "pair", "action"):
            self.assertAlmostEqual(sum(p[key] for row in pieces for p in row), full[key], places=10)
        self.assertGreater(abs(pieces[0][1]["pair"]+pieces[1][0]["pair"]), 1e-5)
        self.assertGreater(abs(sum(pieces[i][i]["action"] for i in range(2))-full["action"]), 1.)

    def test_curved_expectation_normalization_and_wrong_observables(self):
        rho = 30000.
        actual = pilot_integrals(rho)
        expected_n = rho*actual["point"]
        layer_means = rho*rho*actual["layers"]
        signed_pairs = np.dot([1, -9, 16, -8], layer_means)
        expected_action = C/math.sqrt(rho)*(expected_n-signed_pairs)
        self.assertAlmostEqual(expected_action, actual["action"], places=9)
        # This checks finite coefficients, not a new probabilistic theorem.
        for wrong in (C/math.sqrt(rho)*(expected_n-signed_pairs/rho),
                      C/math.sqrt(rho)*(expected_n-signed_pairs/2)):
            self.assertGreater(abs(wrong-expected_action), 1.)
        for kwargs in ({"measures": "source"}, {"measures": "target"}, {"freeze_phase": True}):
            wrong = pilot_integrals(rho, **kwargs)
            self.assertGreater(abs(wrong["action"]-actual["action"]), .05)
        self.assertEqual(ordered_layer_kernel(0), 1)  # Exclusive, not inclusive layers.

    def test_flat_and_nonunit_constant_factor_calibrations(self):
        rho = 30000.
        flat = pilot_integrals(rho, curved=False)["action"]
        with mp.workdps(30):
            reference = float(ellipsoid_action(rho, DEPTH, AXES))
        self.assertAlmostEqual(flat, reference, delta=2e-8)
        for omega in (.7, 1.4):
            scaled = pilot_integrals(rho, curved=False, omega=omega)["action"]
            density_changed = pilot_integrals(rho*omega**4, curved=False)["action"]
            self.assertAlmostEqual(scaled, omega**2*density_changed, delta=2e-8)


if __name__ == "__main__":
    unittest.main()
