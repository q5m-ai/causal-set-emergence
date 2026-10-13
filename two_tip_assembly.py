"""Independent finite-density U/cap/lens assembly diagnostics for TT-B.

No expectation is defined by returning an action. The written original-law
transfer is in notes/two-tip-null-limit.md. Quadrature is not certified.
"""

from dataclasses import dataclass
import math

import numpy as np
from scipy.optimize import brentq

from null_mixed import ACTION_CONSTANT
from two_tip_null import TwoTipMixed
from two_tip_lens import LensIntegrals, LensOverlap, layer_primitive, rule, signed_primitive


@dataclass(frozen=True)
class TwoTipAssembly:
    region: TwoTipMixed = TwoTipMixed()

    def overlap(self, kind, tau, xi, order=20):
        """Direct spatial overlap using the physical union/intersection distance.

        Splitting every affine-distance piece keeps opening holes and disconnected
        translated sections; 'union' is NOT computed as a sum of cap values.
        """
        if kind not in ("union", "lens", "plus", "minus"):
            raise ValueError("unknown region")
        if not all(math.isfinite(x) for x in (tau, xi)):
            raise ValueError("displacement must be finite")
        nodes, weights = rule(order)
        a, b = self.region.a, self.region.b
        distances = {"union": lambda y: np.abs(np.abs(y)-a),
                     "lens": lambda y: np.abs(y)+a,
                     "plus": lambda y: np.abs(y-a),
                     "minus": lambda y: np.abs(y+a)}
        distance = distances[kind]
        bound = a+1+b+abs(tau)+1
        breaks = [-bound, -a, 0, a, bound]
        gap = lambda y: float(self.region.height(y-xi)-tau-distance(y))
        total = 0.0
        for lo, hi in zip(breaks[:-1], breaks[1:]):
            gl, gh = gap(lo), gap(hi)
            if gl <= 0 and gh <= 0:
                continue
            if gl < 0:
                lo = brentq(gap, lo, hi, xtol=5e-15)
            elif gh < 0:
                hi = brentq(gap, lo, hi, xtol=5e-15)
            y = lo+(hi-lo)*nodes
            top, d = self.region.height(y-xi)-tau, distance(y)
            total += math.pi/3*(hi-lo)*np.dot(weights, np.maximum(top-d, 0)**2*(top+2*d))
        return float(total)

    def time_breaks(self, mu):
        if not math.isfinite(mu) or not -1 <= mu <= 1:
            raise ValueError("require -1<=mu<=1")
        ends = [brentq(lambda t: t-float(self.region.height(sign*self.region.a-t*mu)),
                       0, 2+self.region.b, xtol=5e-15) for sign in (-1, 1)]
        return sorted(set([0.0, LensOverlap(self.region).time_end(mu), *ends]))

    def pair_integrals(self, kind, rho, order=24):
        if not math.isfinite(rho) or rho <= 0:
            raise ValueError("density must be positive and finite")
        nodes, weights = rule(order)
        layers, signed = np.zeros(4), 0.0
        for mu, wm in zip(2*nodes-1, 2*weights):
            breaks = self.time_breaks(float(mu))
            for lo, hi in zip(breaks[:-1], breaks[1:]):
                times = lo+(hi-lo)*nodes
                overlap = np.array([self.overlap(kind, float(t), float(t*mu)) for t in times])
                smax = times*times*(1-mu*mu)
                measure = math.pi*wm*(hi-lo)*weights*times*overlap
                layers += layer_primitive(rho, smax) @ measure
                signed += np.dot(signed_primitive(rho, smax), measure)
        volume = self.overlap(kind, 0, 0)
        action = ACTION_CONSTANT*math.sqrt(rho)*(volume-rho*signed)
        return LensIntegrals(volume, tuple(float(x) for x in layers), float(signed), float(action))
