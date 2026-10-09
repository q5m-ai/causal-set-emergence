"""Finite accounting diagnostics for the written #153 assembly.

Uses #139's actual full interval integral, including both sphere sheets and
secondary transition. No phase jet, asymptotic coefficient or target is used
in the quadrature. This is not a new production action or probability law.
Finite cubature errors and observed refinements are not certified bounds.
"""

from dataclasses import dataclass
from functools import lru_cache
from math import factorial

import numpy as np
import sympy as sp

from general_metric_gate import gauss_rule, product_curvature
from sphere_circle_focusing import PAIR_FACTOR, interval_volume, time_weight
from two_face_diagnostics import bdg_kernel

SPATIAL_MASS = 4 * np.pi * 20
SLAB_MASS = 4 * SPATIAL_MASS
NORMALIZATION = 4 / np.sqrt(6)
SECTORS = ("short", "offcut", "cut", "excess")
LAYER_WEIGHTS = np.array([1., -9., 16., -8.])


@dataclass(frozen=True)
class PairQuadrature:
    """Geometric positive quadrature weights before applying a signed kernel."""

    volumes: np.ndarray
    weights: dict[str, np.ndarray]

    def evaluate(self, rho):
        if not np.isfinite(rho) or rho <= 0:
            raise ValueError("positive finite density required")
        z = rho * self.volumes
        kernel = bdg_kernel(z)
        pairs = {name: weights @ kernel for name, weights in self.weights.items()}
        # Integrate the actual Poisson count factors, not the signed polynomial.
        layers = np.array([self.weights["full"] @ (np.exp(-z) * z**k / factorial(k))
                           for k in range(4)])
        actions = {name: NORMALIZATION * np.sqrt(rho) * (
            (SLAB_MASS if name in ("full", "short") else 0) - rho * pair)
                   for name, pair in pairs.items()}
        return {"pairs": pairs, "actions": actions, "layer_integrals": layers}


@lru_cache(maxsize=8)
def pair_quadrature(delta=.2, a0=.15, e0=.2, order=12, volume_order=24):
    """Full F2 and all F20 pieces on boundary-split quadrature panels.

    The full column is evaluated directly from G, not defined by summing
    sectors. The short and long columns may overlap after b integration;
    they represent disjoint ORIGINAL time domains. Numerical cutoff choices
    here do not certify the analytic smallness ranges in the written proof.
    """
    if not (0 < delta < .25 and 0 < a0 < np.pi-delta and 0 < e0 < 4-np.pi):
        raise ValueError("requires 0<delta<1/4, 0<a0<pi-delta, 0<e0<4-pi")
    if order < 2 or volume_order < 2:
        raise ValueError("quadrature orders must be at least two")
    d = np.pi-a0
    nn, wn = gauss_rule(order)
    # Include where the secondary transition enters the slab or crosses the
    # excess boundary; these are numerical panels, not deleted partner sets.
    theta_edges = sorted({0., delta, d, 2*np.pi-4, np.pi-e0/2, np.pi})
    volumes, weights = [], {name: [] for name in ("full", *SECTORS)}
    for left, right in zip(theta_edges, theta_edges[1:]):
        for theta, wt in zip(left+(right-left)*nn, (right-left)*wn):
            edges = [theta, 4.]
            edges += [p for p in (delta, 2*np.pi-theta) if theta < p < 4]
            if theta >= d:
                edges.append(theta+e0)
            edges = sorted(set(edges))
            for lo, hi in zip(edges, edges[1:]):
                for u, wu in zip(lo+(hi-lo)*nn, (hi-lo)*wn):
                    volumes.append(interval_volume(u, theta, order=volume_order,
                                                   circle_order=volume_order))
                    measure = PAIR_FACTOR * wt * wu * np.sin(theta)
                    full = time_weight(u)
                    short = time_weight(u, delta, short=True)
                    values = {"full": full, "short": short,
                              "offcut": time_weight(u, delta) if theta < d else 0.,
                              "cut": full if theta >= d and u < theta+e0 else 0.,
                              "excess": full if theta >= d and u >= theta+e0 else 0.}
                    for name, value in values.items():
                        weights[name].append(measure * value)
    return PairQuadrature(np.array(volumes),
                          {name: np.array(value) for name, value in weights.items()})


def original_pair_integral(rho, order=12, volume_order=24):
    """Independent full pair integral in original tau, theta and circle b.

    No G time-weight formula, sector sum or phase-density expansion is used.
    The two endpoint times are integrated to their actual length 4-tau.
    """
    if not np.isfinite(rho) or rho <= 0:
        raise ValueError("positive finite density required")
    nn, wn = gauss_rule(order)
    total = 0.
    for tlo, thi in ((0., np.pi), (np.pi, 4.)):
        for tau, wt in zip(tlo+(thi-tlo)*nn, (thi-tlo)*wn):
            edges = [0., min(tau, np.pi)]
            if tau > np.pi:
                edges.append(2*np.pi-tau)
            edges.sort()
            for lo, hi in zip(edges, edges[1:]):
                alo, ahi = np.arcsin(lo/tau), np.arcsin(hi/tau)
                for alpha, wa in zip(alo+(ahi-alo)*nn, (ahi-alo)*wn):
                    theta = tau*np.sin(alpha)
                    wtheta = wa*tau*np.cos(alpha)
                    bmax = tau*np.cos(alpha)
                    bedges = [0., bmax]
                    if tau > 2*np.pi-theta:
                        bedges.append(np.sqrt(tau*tau-(2*np.pi-theta)**2))
                    bedges.sort()
                    for blo, bhi in zip(bedges, bedges[1:]):
                        for b, wb in zip(blo+(bhi-blo)*nn, (bhi-blo)*wn):
                            u = np.sqrt(tau*tau-b*b)
                            volume = interval_volume(u, theta, order=volume_order,
                                                     circle_order=volume_order)
                            total += (2*PAIR_FACTOR*wt*wtheta*wb*(4-tau)
                                      * np.sin(theta)*bdg_kernel(rho*volume))
    return total


def related(x, y):
    """Actual selected order on diagnostic (time, unit sphere vector, circle) data.

    No epsilon-expanded cones; tests use exactly representable axis vectors.
    Coordinates on the circle are read modulo circumference 20.
    """
    theta = np.arccos(np.clip(np.dot(x[1], y[1]), -1., 1.))
    b = (y[2]-x[2]+10) % 20-10
    return bool(np.hypot(theta, b) <= y[0]-x[0])


def layer_counts(points, labels=None):
    """Finite ordered layers; labels deliberately omit cross-chart pairs.

    The labels option is only a WRONG-observable negative control. It never
    changes the interval, whose every other point, including null points,
    is still counted. No Poisson simulation or alternate law is introduced.
    """
    result = np.zeros(4, dtype=int)
    for i, x in enumerate(points):
        for j, y in enumerate(points):
            if i == j or not related(x, y):
                continue
            if labels is not None and labels[i] != labels[j]:
                continue
            k = sum(related(x, z) and related(z, y) for n, z in enumerate(points)
                    if n not in (i, j))
            if k < 4:
                result[k] += 1
    return result


def check_assembly_identities():
    """Exact finite algebra; the analytic remainders are NOT proved by this check."""
    rho = sp.symbols("rho", positive=True)
    rs, ro, rc, re = sp.symbols("r_s r_o r_c r_e", real=True)
    volume = 4 * (4*sp.pi*20)
    pair = volume/rho - 80*sp.sqrt(6)*sp.pi/rho**sp.Rational(3, 2)
    pair += (rs+ro+rc+re)/rho**sp.Rational(3, 2)
    action = 4/sp.sqrt(6)*sp.sqrt(rho)*(volume-rho*pair)
    assert sp.simplify(action-(320*sp.pi-4/sp.sqrt(6)*(rs+ro+rc+re))) == 0
    z = sp.symbols("z", nonnegative=True)
    count_kernel = sum(weight*z**k/sp.factorial(k)
                       for k, weight in enumerate((1, -9, 16, -8)))
    assert sp.expand(count_kernel-(1-9*z+8*z*z-sp.Rational(4, 3)*z**3)) == 0
    radius, scalar, weyl_squared = product_curvature()
    assert scalar.subs(radius, 1) == 2
    assert weyl_squared.subs(radius, 1) == sp.Rational(4, 3)
    assert sp.simplify(scalar.subs(radius, 1)/2*volume-320*sp.pi) == 0
    print("PASS: #153 full normalized assembly, original layer weights, independent target")


if __name__ == "__main__":
    check_assembly_identities()
