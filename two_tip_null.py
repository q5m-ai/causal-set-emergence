"""Finite-density diagnostics for #134, NOT a global two-tip action solver.

See notes/two-tip-null-feasibility.md. The selected geometry is a=1/2, b=1/10.
Other supported parameters (including the flat-floor b=0 calibration) are
regression inputs, not an asserted enlargement of a proved limit theorem.
Central-source partner quadrature is not the full source integral. Neither
quadrature refinement nor symbolic tests certify an asymptotic error bound.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.optimize import brentq

from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT


def _finite(*values):
    if not all(math.isfinite(value) for value in values):
        raise ValueError("parameters must be finite")


def _sign(sign):
    if isinstance(sign, bool) or sign not in (-1, 1):
        raise ValueError("tip sign must be -1 or +1")


@lru_cache(maxsize=8)
def _unit_rule(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    nodes, weights = leggauss(order)
    return (nodes + 1) / 2, weights / 2


@dataclass(frozen=True)
class CentralPartners:
    """Unnormalized integrals over I(p,v+) intersect I(p,v-), not all sources."""

    volume: float
    layers: tuple[float, float, float, float]
    signed: float


@dataclass(frozen=True)
class TwoTipMixed:
    a: float = 0.5
    b: float = 0.1

    def __post_init__(self):
        _finite(self.a, self.b)
        if not (0 < self.a < 1 and 0 <= self.b < 1 - self.a):
            raise ValueError("require 0<a<1 and 0<=b<1-a")

    def height(self, axial):
        return 1 + self.b * np.sin(axial)

    def cap_masks(self, points):
        """Strict region membership; no tolerance alters the boundary/order."""
        p = np.asarray(points, dtype=float)
        if p.ndim != 2 or p.shape[1] != 4 or not np.isfinite(p).all():
            raise ValueError("points must be a finite N-by-4 array")
        above = p[:, 0] > -self.height(p[:, 1])
        result = []
        for sign in (1, -1):
            displacement = p[:, 1:] - np.array([sign*self.a, 0, 0])
            result.append(above & (p[:, 0] < -np.linalg.norm(displacement, axis=1)))
        return tuple(result)

    def joint_radius(self, sign, mu):
        _sign(sign)
        _finite(mu)
        if not -1 <= mu <= 1:
            raise ValueError("require -1<=mu<=1")
        if self.b == 0:
            return 1.0
        return brentq(lambda r: r - self.height(sign*self.a + r*mu),
                      1-self.b, 1+self.b, xtol=5e-15)

    def joint_areas(self):
        """Induced SN areas, independently of any action or proposed limit."""
        def area(sign, low, high):
            return 2*math.pi * quad(lambda mu: self.joint_radius(sign, mu)**2,
                                    low, high, epsabs=2e-11, epsrel=2e-11)[0]
        lens = area(1, -1, -self.a) + area(-1, self.a, 1)
        union = area(1, -self.a, 1) + area(-1, -1, self.a)
        return {"union": union, "lens": lens,
                "plus": area(1, -1, 1), "minus": area(-1, -1, 1)}

    def _axial_volume(self, distance, center):
        # At fixed z: integrate pi*(u^2-distance(z)^2) for d<u<H(z).
        width = 1 + self.b + self.a
        low = brentq(lambda z: self.height(z) - distance(z), center-width, center)
        high = brentq(lambda z: self.height(z) - distance(z), center, center+width)
        def fibre(z):
            h, d = self.height(z), distance(z)
            return math.pi/3 * (h-d)**2 * (h+2*d)
        return sum(quad(fibre, lo, hi, epsabs=2e-12)[0]
                   for lo, hi in ((low, center), (center, high)))

    def volumes(self):
        """Ordinary geometric volumes, not normalized action estimates."""
        lens = self._axial_volume(lambda z: abs(z)+self.a, 0)
        plus = self._axial_volume(lambda z: abs(z-self.a), self.a)
        minus = self._axial_volume(lambda z: abs(z+self.a), -self.a)
        return {"union": plus+minus-lens, "lens": lens, "plus": plus, "minus": minus}

    def central_volume(self, u):
        """Exact TT6 volume for p=(-u,0); require this source to lie in L."""
        self._central_source(u)
        return math.pi * (u-self.a)**4 * (u+2*self.a) / (24*u)

    def _central_source(self, u):
        _finite(u)
        if not self.a < u < 1:
            raise ValueError("central source must satisfy a<u<1")

    def central_partners(self, rho, u, order=20):
        """TT8 quadrature of four positive layers AND the signed kernel.

        Includes every partner in the lens fibre, not just the nearest sheet.
        rho=0 is allowed only as the volume calibration. For rho>0, multiply
        `signed` by rho to obtain Q_rho(p); this is not A_rho(L).
        The source floor drops out of this fibre by future-set monotonicity,
        but NOT from the global source integral TT7.
        """
        _finite(rho)
        self._central_source(u)
        if rho < 0:
            raise ValueError("density must be nonnegative")
        nodes, weights = _unit_rule(order)
        a = self.a
        v0, v1 = (u*u+a*a)/(2*u), (u+a)/2
        volume, signed = 0.0, 0.0
        layers = np.zeros(4)
        for vlow, vhigh in ((a, v0), (v0, v1), (v1, u)):
            for v, wv in zip(vlow+(vhigh-vlow)*nodes, (vhigh-vlow)*weights):
                zmax = min(v-a, u-v)
                contact = np.clip((2*u*v-u*u-a*a)/(2*a), 0, zmax)
                for zlow, zhigh in ((0, contact), (contact, zmax)):
                    if zhigh <= zlow:
                        continue
                    z = zlow + (zhigh-zlow)*nodes[:, None]
                    ymax = np.minimum(v*v-(z+a)**2, (u-v)**2-z*z)
                    y = ymax * nodes[None, :]
                    # 2*pi includes the source-axis reflection and r dr=dy/2.
                    measure = (2*math.pi*wv*(zhigh-zlow)*ymax
                               * weights[:, None]*weights[None, :])
                    delta = (u-v)**2-z*z-y
                    phase = INTERVAL_CONSTANT*rho*delta**2
                    pmf = np.exp(-phase)
                    volume += np.sum(measure)
                    signed += np.sum(measure*(1-9*phase+8*phase**2-4*phase**3/3)*pmf)
                    for k in range(4):
                        if k:
                            pmf = pmf * phase/k
                        layers[k] += np.sum(measure*pmf)
        return CentralPartners(float(volume), tuple(float(x) for x in layers), float(signed))


def main():
    region = TwoTipMixed()
    print("#134 fixed a=1/2, b=1/10; diagnostics only, NOT a full-action limit")
    print("Independent SN areas:", region.joint_areas())
    print("Ordinary volumes:", region.volumes())
    u = 0.8
    print("Central source p=(-0.8,0); partner response, NOT source-integrated action")
    print("rho   lens Q/rho (order 16)   lens Q/rho (order 24)   single interval")
    for rho in (0.5, 20, 100):
        low = region.central_partners(rho, u, 16)
        high = region.central_partners(rho, u, 24)
        complete = -math.expm1(-INTERVAL_CONSTANT*rho*(u*u-region.a**2)**2)/rho
        print(f"{rho:5g} {low.signed:23.15g} {high.signed:23.15g} {complete:18.12g}")
    delta = 0.05
    print(f"Each all-partner tip bound at delta={delta}: {4*math.pi*delta**2:.12g}")
    print(f"Action normalization C4={ACTION_CONSTANT:.12g}; no fitted target/coefficient")


if __name__ == "__main__":
    main()
