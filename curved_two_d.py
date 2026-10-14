"""Finite diagnostics for C2; NOT a numerical proof of its universal remainder.

Coordinates: u=t+x, v=t-x, g=Omega^2(dt^2-dx^2), dmu=(Omega^2/2)du dv.
All interval routines integrate physical volume, not a curvature/phase jet.
The circle sweep works at arbitrary finite width; the fast pair quadrature
explicitly restricts itself to slab duration < period and is only a diagnostic.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.optimize import brentq


def kernel(z):
    return (1 - 2*z + z*z/2)*np.exp(-z)


@lru_cache(maxsize=None)
def rule(order):
    x, w = leggauss(order)
    return (x+1)/2, w/2


@dataclass(frozen=True)
class PolynomialMetric:
    """Globally positive variable curved density; parameters must be positive definite."""

    a: float = .4
    b: float = .2
    c: float = .1

    def __post_init__(self):
        if self.a < 0 or self.b < 0 or self.c**2 > 4*self.a*self.b:
            raise ValueError("The quadratic density must be positive semidefinite")

    def density(self, t, x):
        return 1 + self.a*t*t + self.b*x*x + self.c*t*x

    def curvature(self, t, x):
        f = self.density(t, x)
        ft, fx = 2*self.a*t+self.c*x, 2*self.b*x+self.c*t
        return (2*(self.a-self.b)*f-ft*ft+fx*fx)/f**3

    def rectangle(self, u, v, U, V):
        """Exact integral of dmu over an ordered null rectangle (broadcastable)."""
        du, dv = U-u, V-v
        tc, xc = (u+U+v+V)/4, (u+U-v-V)/4
        t2, x2 = tc*tc+(du*du+dv*dv)/48, xc*xc+(du*du+dv*dv)/48
        tx = tc*xc+(du*du-dv*dv)/48
        return du*dv/2*(1+self.a*t2+self.b*x2+self.c*tx)


@dataclass(frozen=True)
class CircleMetric:
    """A smooth positive time- and space-dependent conformal cylinder."""

    period: float = 1.
    a: float = .3
    b: float = .2

    def __post_init__(self):
        if self.period <= 0 or self.a < 0 or abs(self.b) >= 1:
            raise ValueError("Require L>0, a>=0 and |b|<1")

    def density(self, t, x):
        return 1+self.a*t*t+self.b*np.cos(2*np.pi*x/self.period)

    def curvature(self, t, x):
        k = 2*np.pi/self.period
        f = self.density(t, x)
        ft, fx = 2*self.a*t, -self.b*k*np.sin(k*x)
        return (f*(2*self.a+self.b*k*k*np.cos(k*x))-ft*ft+fx*fx)/f**3

    def rectangle(self, u, v, U, V):
        du, dv = U-u, V-v
        tc, xc = (u+U+v+V)/4, (u+U-v-V)/4
        # np.sinc(z)=sin(pi*z)/(pi*z), including its continuous zero value.
        cosine = (np.cos(2*np.pi*xc/self.period)
                  * np.sinc(du/(2*self.period))*np.sinc(dv/(2*self.period)))
        return du*dv/2*(1+self.a*(tc*tc+(du*du+dv*dv)/48)+self.b*cosine)


def line_interval_slices(metric, source, target):
    """Independent physical t-slice integral, not the rectangle antiderivative."""
    t, x = source
    T, X = target
    if T-t < abs(X-x):
        return 0.

    def slice_volume(s):
        lo, hi = max(x-(s-t), X-(T-s)), min(x+s-t, X+T-s)
        if hi <= lo:
            return 0.
        return quad(lambda z: metric.density(s, z), lo, hi, epsabs=2e-12)[0]

    switches = [(t+T+(X-x))/2, (t+T-(X-x))/2]
    return quad(slice_volume, t, T, points=switches, epsabs=2e-12)[0]


def circle_rectangles(source, target, period):
    """All causal lifts, without a thinness/unique-route assumption."""
    t, x = source
    T, X = target
    u, v, U, V = t+x, t-x, T+X, T-X
    first, last = math.ceil((u-U)/period), math.floor((V-v)/period)
    return [(u, v, U+n*period, V-n*period) for n in range(first, last+1)]


def rectangle_union_volume(metric, rectangles):
    """Exact disjoint sweep of rectangles in one covering coordinate plane."""
    rectangles = [r for r in rectangles if r[2] > r[0] and r[3] > r[1]]
    edges = sorted({r[i] for r in rectangles for i in (0, 2)})
    total = 0.
    for left, right in zip(edges, edges[1:]):
        mid = (left+right)/2
        intervals = sorted((b, B) for a, b, A, B in rectangles if a < mid < A)
        merged = []
        for low, high in intervals:
            if merged and low <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(high, merged[-1][1]))
            else:
                merged.append((low, high))
        total += sum(metric.rectangle(left, low, right, high) for low, high in merged)
    return total


def circle_interval_union(metric, source, target):
    """C2.5 physical union in 0<=u<L, including large-rectangle self-overlap."""
    L = metric.period
    physical = []
    for u, v, U, V in circle_rectangles(source, target, L):
        for k in range(math.ceil(-U/L), math.floor((L-u)/L)+1):
            left, right = max(0., u+k*L), min(L, U+k*L)
            if right > left:
                physical.append((left, v-k*L, right, V-k*L))
    return rectangle_union_volume(metric, physical)


def _circle_arcs(center, radius, period):
    if radius < 0:
        return []
    if 2*radius >= period:
        return [(0., period)]
    center %= period
    low, high = center-radius, center+radius
    if low < 0:
        return [(0., high), (low+period, period)]
    if high > period:
        return [(0., high-period), (low, period)]
    return [(low, high)]


def circle_interval_slices(metric, source, target):
    """Independent metric-density integral over intersected physical circle arcs."""
    t, x = source
    T, X = target
    if T <= t:
        return 0.
    L, k = metric.period, 2*np.pi/metric.period

    def slice_volume(s):
        total = 0.
        for a, A in _circle_arcs(x, s-t, L):
            for b, B in _circle_arcs(X, T-s, L):
                low, high = max(a, b), min(A, B)
                if high > low:
                    total += ((1+metric.a*s*s)*(high-low)
                              + metric.b/k*(np.sin(k*high)-np.sin(k*low)))
        return total

    # Includes all arc wrapping, saturation, and endpoint-switching times.
    points = [t, T, t+L/2, T-L/2]
    for center, base, sign in ((x % L, t, 1), (X % L, T, -1)):
        points += [base+sign*center, base+sign*(L-center)]
    for n in range(-math.ceil((T-t)/L)-2, math.ceil((T-t)/L)+3):
        points += [(t+T+X-x+n*L)/2, (t+T-X+x+n*L)/2]
    points = sorted({p for p in points if t < p < T})
    return quad(slice_volume, t, T, points=points, epsabs=2e-11, limit=200)[0]


def circle_interval_below_period(metric, t, x, tau, displacement):
    """Broadcastable exact union for 0<=|displacement|<=L/2 and tau<L."""
    L = metric.period
    r = displacement
    u, v = t+x, t-x
    U, V = u+tau+r, v+tau-r
    main = metric.rectangle(u, v, U, V)
    sign = np.where(np.asarray(r) >= 0, 1., -1.)
    other_U, other_V = U-sign*L, V+sign*L
    cut = tau+np.abs(r) > L
    # Safe degenerate rectangles outside the two-route sector.
    other_U, other_V = np.maximum(u, other_U), np.maximum(v, other_V)
    other = metric.rectangle(u, v, other_U, other_V)
    source_overlap = metric.rectangle(u, v, np.minimum(U, other_U), np.minimum(V, other_V))
    low_u = np.where(sign > 0, u+L, u)
    low_v = np.where(sign > 0, v, v+L)
    target_overlap = metric.rectangle(low_u, low_v, U, V)
    return main+np.where(cut, other-source_overlap-target_overlap, 0.)


def cut_primitive(metric, volume, source=(.05, .12), box=.08, order=28,
                  sum_phase=False):
    """Actual weighted 2-route primitive at fixed source; diagnostic, not a jet.

    Both one-positive strips and the positive-positive corner are integrated.
    Source and target w=Omega^2/2 factors are included. This is a localized
    endpoint integral, explicitly NOT the complete action or a counterexample.
    """
    L = metric.period
    if not 0 < box < L/4 or not 0 < volume < (1-abs(metric.b))*box*(L-box)/4:
        raise ValueError("Require a fixed small box and a sublevel inside it")
    t, x = source
    u, v = t+x, t-x
    z, w = rule(order)

    def phase(p, q):
        result = 0.
        if q > 0:
            result += metric.rectangle(u, v, u+L+p, v+q)
        if p > 0:
            result += metric.rectangle(u, v, u+p, v+L+q)
        if p > 0 and q > 0 and not sum_phase:
            result -= (metric.rectangle(u, v, u+p, v+q)
                       + metric.rectangle(u+L, v, u+L+p, v+q))
        return result

    def amplitude(p, q):
        return (metric.density(t, x)*metric.density(t+(L+p+q)/2,
                                                   x+(L+p-q)/2)/4)

    total = 0.
    for inactive, wi in zip(-box+box*z, box*w):
        qmax = brentq(lambda q: phase(inactive, q)-volume, 0., box, xtol=1e-15)
        pmax = brentq(lambda p: phase(p, inactive)-volume, 0., box, xtol=1e-15)
        total += wi*(qmax*np.sum(w*amplitude(inactive, qmax*z))
                     + pmax*np.sum(w*amplitude(pmax*z, inactive)))
    pmax = brentq(lambda p: phase(p, 0.)-volume, 0., box, xtol=1e-15)
    for p, wp in zip(pmax*z, pmax*w):
        qmax = brentq(lambda q: phase(p, q)-volume, 0., box, xtol=1e-15)
        total += wp*qmax*np.sum(w*amplitude(p, qmax*z))
    return total


def temporal_short_mask(gap, cutoff):
    """The equality surface belongs to long, including diagnostic atoms."""
    return np.asarray(gap) < cutoff


@dataclass(frozen=True)
class GraphRegion:
    """One diagnostic smooth G-SS region, not the hypotheses of theorem C2."""

    a: float = .18
    skew: float = .25
    tilt: float = .1
    bend: float = .03

    def top(self, x):
        return self.tilt*x+self.bend*x*x

    def top_prime(self, x):
        return self.tilt+2*self.bend*x

    def height(self, x):
        return self.a*(1-x*x)*(1+self.skew*x)

    def height_prime(self, x):
        return self.a*(-2*x+self.skew*(1-3*x*x))

    def bottom(self, x):
        return self.top(x)-self.height(x)

    def joint_weights(self):
        x = np.array([-1., 1.])
        q = self.top_prime(x)
        p = q-self.height_prime(x)
        return (1-p*q)/np.abs(p-q)

    def reach(self, x, t, direction):
        edge = 1-x if direction == 1 else x+1
        return brentq(lambda r: self.top(x+direction*r)-t-r, 0., edge, xtol=1e-14)


def one(t, x):
    return np.ones_like(t+x)


def source_field(t, x):
    return 1+.15*t+.2*x


def target_field(t, x):
    return 1+.1*t*t+.13*np.sin(x)


def source_partition(t, x):
    return .5+.2*np.sin(x+2*t)


def target_partition(t, x):
    return .5+.25*np.cos(2*x-t)


def graph_point(metric, region, chi=one, phi=one, order=32):
    z, w = rule(order)
    x = (2*z-1)[:, None]
    t = region.bottom(x)+region.height(x)*z[None, :]
    return np.sum(2*w[:, None]*w[None, :]*region.height(x)
                  * metric.density(t, x)*chi(t, x)*phi(t, x))


def graph_pair(metric, region, rho, chi=one, phi=one, order=28,
               ordering="source", cutoff=None, partitions=False):
    """Entire causal pair integral in two independently ordered domains.

    source: x, source time, spatial displacement, target time.
    displacement: x, spatial displacement, source time, target time.
    cutoff returns (strict-short, equality-long). partitions returns the full
    ordered 2x2 matrix rather than silently dropping its off-diagonal cells.
    """
    if rho <= 0 or ordering not in ("source", "displacement"):
        raise ValueError("Require rho>0 and a recognized integration ordering")
    z, w = rule(order)
    total = np.zeros((2, 2, 2))  # short/long, source label, target label
    for x, wx in zip(2*z-1, 2*w):
        for direction in (-1, 1):
            if ordering == "source":
                outer = region.bottom(x)+region.height(x)*z
                outer_weights = region.height(x)*w
            else:
                reach = region.reach(x, region.bottom(x), direction)
                outer, outer_weights = reach*z, reach*w
            for value, weight in zip(outer, outer_weights):
                if ordering == "source":
                    t = value
                    reach = region.reach(x, t, direction)
                    r, wr = reach*z, reach*w
                    t = np.full_like(r, t)
                else:
                    r = np.full_like(z, value)
                    span = region.top(x+direction*r)-r-region.bottom(x)
                    t, wr = region.bottom(x)+span*z, span*w
                y = x+direction*r
                gap = region.top(y)-t-r
                tau = r[:, None]+gap[:, None]*z[None, :]
                T = t[:, None]+tau
                X = np.broadcast_to(y[:, None], T.shape)
                t, x_grid = np.broadcast_arrays(t[:, None], np.full_like(T, x))
                volume = metric.rectangle(t+x_grid, t-x_grid, T+X, T-X)
                integrand = (wx*weight*wr[:, None]*gap[:, None]*w[None, :]
                             * metric.density(t, x_grid)*metric.density(T, X)
                             * chi(t, x_grid)*phi(T, X)*kernel(rho*volume))
                source = source_partition(t, x_grid) if partitions else np.ones_like(T)
                target = target_partition(T, X) if partitions else np.ones_like(T)
                short = np.ones_like(T, dtype=bool) if cutoff is None else temporal_short_mask(tau, cutoff)
                for k, mask in enumerate((short, ~short)):
                    for i, a in enumerate((source, 1-source)):
                        for j, b in enumerate((target, 1-target)):
                            total[k, i, j] += np.sum(integrand*mask*a*b)
    if not partitions:
        total = total.sum(axis=(1, 2))
    return total if cutoff is not None else total.sum(axis=0)


def graph_target(metric, region, weighted=False, order=36):
    """Independent R/2 + face-field flux + counting target, never an action fit."""
    z, w = rule(order)
    x = (2*z-1)[:, None]
    t = region.bottom(x)+region.height(x)*z[None, :]
    chi, phi = (source_field, target_field) if weighted else (one, one)
    bulk = metric.curvature(t, x)*metric.density(t, x)*phi(t, x)/2
    if weighted:
        bulk += .2+.13*np.sin(x)  # flat Box(phi); conformal q cancels dmu
    result = np.sum(2*w[:, None]*w[None, :]*region.height(x)*chi(t, x)*bulk)
    if weighted:
        x = 2*z-1
        t, slope = region.top(x), region.top_prime(x)
        flux = (phi(t, x)*(.15+.2*slope)
                - chi(t, x)*(.2*t+.13*slope*np.cos(x)))
        result += np.sum(2*w*flux)
    x = np.array([-1., 1.])
    return result+np.sum(region.joint_weights()*chi(region.top(x), x)*phi(region.top(x), x))


def circle_target(metric, duration, order=40):
    z, w = rule(order)
    t, x = duration*z[:, None], metric.period*z[None, :]
    return np.sum(duration*metric.period*w[:, None]*w[None, :]
                  * metric.curvature(t, x)*metric.density(t, x)/2)


def circle_action(metric, duration, rho, order=24):
    """Complete unit-field finite-density diagnostic, including both cut sectors.

    Only duration<L is supported by this fast routine. The general physical
    interval sweep above has no such width restriction.
    """
    L = metric.period
    if not 0 < duration < L or rho <= 0:
        raise ValueError("The fast quadrature requires 0<T<L and rho>0")
    z, w = rule(order)
    x = L*z[:, None, None]
    point = L*(duration+metric.a*duration**3/3)
    pair = 0.
    time_edges = sorted({0., min(duration, L/2), duration})
    for lower, upper in zip(time_edges, time_edges[1:]):
        for tau, wt in zip(lower+(upper-lower)*z, (upper-lower)*w):
            t = (duration-tau)*z[None, :, None]
            radial_edges = sorted({0., min(tau, L/2), min(max(L-tau, 0.), min(tau, L/2))})
            for ra, rb in zip(radial_edges, radial_edges[1:]):
                r = (ra+(rb-ra)*z)[None, None, :]
                weights = (L*(duration-tau)*(rb-ra)*wt
                           * w[:, None, None]*w[None, :, None]*w[None, None, :])
                for sign in (-1, 1):
                    volume = circle_interval_below_period(metric, t, x, tau, sign*r)
                    pair += np.sum(weights*metric.density(t, x)*metric.density(t+tau, x+sign*r)
                                   * kernel(rho*volume))
    return 2*rho*point-4*rho*rho*pair
