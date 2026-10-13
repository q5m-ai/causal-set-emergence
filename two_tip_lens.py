"""TT-A full-lens diagnostics, not certified quadrature or a Lean proof.

The written proof is notes/two-tip-lens-limit.md. These evaluators keep the
selected axial, nonplanar floor. Neither finite-density values nor a fitted
coefficient is used to define the independent target.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gammainc, gamma

from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT
from two_tip_null import TwoTipMixed


@lru_cache(maxsize=16)
def rule(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    x, w = leggauss(order)
    return (x + 1) / 2, w / 2


def _density(rho):
    if not math.isfinite(rho) or rho <= 0:
        raise ValueError("density must be positive and finite")


def layer_primitive(rho, s):
    """Integral from 0 to s of exp(-c*rho*x²)*(c*rho*x²)^k/k!, k=0..3."""
    _density(rho)
    s = np.asarray(s, dtype=float)
    if not np.isfinite(s).all() or np.any(s < 0):
        raise ValueError("proper-time squared must be finite and nonnegative")
    lam = math.sqrt(INTERVAL_CONSTANT * rho)
    return np.array([gamma(k + 0.5) * gammainc(k + 0.5, (lam*s)**2)
                     / (2*lam*math.factorial(k)) for k in range(4)])


def signed_primitive(rho, s):
    """Exact signed radial primitive; independent of positive layer summation."""
    _density(rho)
    s = np.asarray(s, dtype=float)
    if not np.isfinite(s).all() or np.any(s < 0):
        raise ValueError("proper-time squared must be finite and nonnegative")
    phase = INTERVAL_CONSTANT * rho * s*s
    return s * (1 - 7*phase/3 + 2*phase*phase/3) * np.exp(-phase)


@dataclass(frozen=True)
class LensIntegrals:
    """Unnormalized ordered pair integrals; layers are positive, not means."""

    volume: float
    layers: tuple[float, float, float, float]
    signed: float
    action: float


@dataclass(frozen=True)
class LensOverlap:
    # Other parameters are diagnostic inputs only, not additional theorem scope.
    region: TwoTipMixed = TwoTipMixed()

    def roots(self, tau=0.0, xi=0.0):
        if not all(math.isfinite(x) for x in (tau, xi)):
            raise ValueError("displacement must be finite")
        a, b = self.region.a, self.region.b
        h = float(self.region.height(-xi)) - tau - a
        if h <= 0:
            return (0.0, 0.0)
        bound = h/(1-b) + 1
        gap = lambda y: float(self.region.height(y-xi)) - tau - a - abs(y)
        return (brentq(gap, -bound, 0, xtol=5e-15),
                brentq(gap, 0, bound, xtol=5e-15))

    def overlap(self, tau, xi, order=20):
        """LA3's full source overlap; independent of transverse displacement."""
        nodes, weights = rule(order)
        low, high = self.roots(tau, xi)
        total = 0.0
        for lo, hi in ((low, 0.0), (0.0, high)):
            y = lo + (hi-lo)*nodes
            d = self.region.a + np.abs(y)
            top = self.region.height(y-xi) - tau
            integrand = math.pi/3 * np.maximum(top-d, 0)**2 * (top+2*d)
            total += (hi-lo)*np.dot(weights, integrand)
        return float(total)

    def time_end(self, mu):
        if not math.isfinite(mu) or not -1 <= mu <= 1:
            raise ValueError("require -1<=mu<=1")
        a, b = self.region.a, self.region.b
        return brentq(lambda tau: tau+a-float(self.region.height(-tau*mu)),
                      0, (1-a)/(1-b)+1, xtol=5e-15)

    def coefficient(self):
        """Actual overlap Hessian and flux; target is computed elsewhere."""
        low, high = self.roots()
        a, b = self.region.a, self.region.b
        def hessian(z):
            h = float(self.region.height(z))
            hp, hpp = b*math.cos(z), -b*math.sin(z)
            d = a+abs(z)
            return 2*math.pi*h*(1-hp*hp)-math.pi*(h*h-d*d)*hpp
        value = sum(quad(hessian, lo, hi, epsabs=2e-12)[0]
                    for lo, hi in ((low, 0), (0, high)))
        # Both one-sided flux values are the same; oriented contributions differ.
        flux = math.pi*(1-a*a)*b
        return {"hessian": value, "left_crease_flux": -flux,
                "right_crease_flux": flux}

    def pair_integrals(self, rho, order=32):
        """LA4, with xi=tau*mu and the exact moving closing endpoint.

        Radial positive layers and the signed kernel are integrated separately.
        This includes ALL partners; no high-density accuracy is promised.
        """
        _density(rho)
        nodes, weights = rule(order)
        layers, signed = np.zeros(4), 0.0
        for mu, wm in zip(2*nodes-1, 2*weights):
            end = self.time_end(float(mu))
            times = end*nodes
            overlaps = np.array([self.overlap(float(t), float(t*mu)) for t in times])
            smax = times*times*(1-mu*mu)
            measure = math.pi*wm*end*weights*times*overlaps
            layers += layer_primitive(rho, smax) @ measure
            signed += np.dot(signed_primitive(rho, smax), measure)
        volume = self.overlap(0, 0)
        action = ACTION_CONSTANT*math.sqrt(rho)*(volume-rho*signed)
        return LensIntegrals(volume, tuple(float(x) for x in layers), float(signed), float(action))

    def density(self, s, order=32):
        """Full D(s), for positive s, using the actual compact overlap support."""
        if not math.isfinite(s) or s < 0:
            raise ValueError("s must be nonnegative and finite")
        nodes, weights = rule(order)
        result = 0.0
        # D(s)=pi*integral f(t,xi)*1_{t²-xi²>=s} dt dxi.
        for mu, wm in zip(2*nodes-1, 2*weights):
            end = self.time_end(float(mu))
            start = math.sqrt(s/(1-mu*mu))
            if start >= end:
                continue
            times = start+(end-start)*nodes
            values = np.array([self.overlap(float(t), float(t*mu)) for t in times])
            result += math.pi*wm*(end-start)*np.dot(weights, times*values)
        return float(result)

    def axial_partners(self, rho, depth, axial, order=24):
        """Independent ordinary-coordinate partner integral for p=(-depth,axial,0,0).

        q=(-v,z,r*cos(theta),r*sin(theta)). Integrate theta and y=r²,
        retaining both sphere constraints and every switch of the active one.
        The floor is automatic for a future partner, NOT removed from sources.
        """
        _density(rho)
        a = self.region.a
        if not all(math.isfinite(x) for x in (depth, axial)) or depth <= a+abs(axial):
            raise ValueError("source must lie strictly in both past cones")
        nodes, weights = rule(order)
        out = np.zeros(4)
        # Changes of which causal/upper axial endpoint is active.
        vbreaks = sorted(set([a, depth, (depth+a-axial)/2, (depth+a+axial)/2,
                             (depth*depth-axial*axial+a*a)/(2*depth)]))
        for vlo, vhi in zip(vbreaks[:-1], vbreaks[1:]):
            for v, wv in zip(vlo+(vhi-vlo)*nodes, (vhi-vlo)*weights):
                lo, hi = max(-(v-a), axial-(depth-v)), min(v-a, axial+(depth-v))
                cuts = [lo, hi]
                if lo < 0 < hi:
                    cuts.append(0.0)
                for sign in (-1, 1):
                    denom = 2*(axial+sign*a)
                    if denom:
                        root = (2*depth*v-depth*depth+axial*axial-a*a)/denom
                        if lo < root < hi and sign*root > 0:
                            cuts.append(root)
                cuts.sort()
                for zlo, zhi in zip(cuts[:-1], cuts[1:]):
                    z = zlo+(zhi-zlo)*nodes
                    future_ball = (depth-v)**2-(z-axial)**2
                    past_lens = v*v-(np.abs(z)+a)**2
                    ymax = np.maximum(0, np.minimum(future_ball, past_lens))
                    top = np.maximum(future_ball, 0)
                    bottom = np.maximum(top-ymax, 0)
                    integrals = layer_primitive(rho, top)-layer_primitive(rho, bottom)
                    out += math.pi*wv*(zhi-zlo)*(integrals @ weights)
        return out

    def independent_pairs(self, rho, order=12, partner_order=24):
        """Second full pair evaluator: boost only the partner fibre, integrate sources.

        A Lorentz transformation in (t,w) fixes both tips and maps a source to
        (-h,z,0,0), h=sqrt(u²-|w|²). The source measure after integrating
        h<u<H(z) is 2*pi*h*(H(z)-h) dh dz. This is independent of LA3/LA4.
        Moderate-density diagnostic only; compare successive quadrature orders.
        """
        _density(rho)
        nodes, weights = rule(order)
        low, high = self.roots()
        out = np.zeros(4)
        for lo, hi in ((low, 0.0), (0.0, high)):
            for z, wz in zip(lo+(hi-lo)*nodes, (hi-lo)*weights):
                top = float(self.region.height(z))
                bottom = self.region.a+abs(z)
                for h, wh in zip(bottom+(top-bottom)*nodes, (top-bottom)*weights):
                    out += (2*math.pi*h*(top-h)*wz*wh
                            * self.axial_partners(rho, float(h), float(z), partner_order))
        return out


def main():
    lens = LensOverlap()
    print("TT-A: actual fixed a=1/2, b=1/10; diagnostics, not certified errors")
    print("Independent SN area:", lens.region.joint_areas()["lens"])
    print("Derived overlap Hessian / oriented crease flux:", lens.coefficient())
    print("rho  full action (32)  full action (64)  positive-layer recombination (64)")
    for rho in (1, 20, 100, 1000, 10000):
        low, high = lens.pair_integrals(rho, 32), lens.pair_integrals(rho, 64)
        signed = np.dot(high.layers, [1, -9, 16, -8])
        action = ACTION_CONSTANT*math.sqrt(rho)*(high.volume-rho*signed)
        print(f"{rho:5g} {low.action:17.10g} {high.action:17.10g} {action:17.10g}")


if __name__ == "__main__":
    main()
