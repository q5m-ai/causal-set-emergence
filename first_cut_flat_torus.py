"""Diagnostics for the written first-cut torus theorem, not a proof checker.

The actual interval is a union, not a selected lift or a sum of lift volumes.
Only the cubic first-cut regime tau < L/sqrt(2) is implemented here. Existing
thin-torus and production action/probability definitions are left unchanged.
"""

from functools import lru_cache
import math

import numpy as np
from scipy.integrate import quad
from scipy.special import gamma

from dimension_kernels import _dimension, interval_coefficient


def _positive(value, name):
    value = float(value)
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"positive finite {name} required")
    return value


def first_cut_geometry(d, length, duration):
    """Validate exactly the approved slab family, not arbitrary flat topology."""
    _dimension(d)
    length = _positive(length, "length")
    duration = _positive(duration, "duration")
    if not length / 2 < duration < length / math.sqrt(2):
        raise ValueError("requires L/2 < T < L/sqrt(2)")
    return length, duration


@lru_cache(maxsize=None, typed=True)
def _constants(d):
    _dimension(d)
    q = d / 2
    return float(interval_coefficient(d)), math.pi**(q-1) / gamma(q)


def quotient_distance(displacement, length):
    """Actual Euclidean quotient distance, not the maximum product metric."""
    length = _positive(length, "length")
    a = np.asarray(displacement, dtype=float)
    if a.ndim != 1 or not a.size or not np.all(np.isfinite(a)):
        raise ValueError("finite nonempty displacement vector required")
    nearest = (a + length/2) % length - length/2
    return float(np.linalg.norm(nearest))


def causal_lifts(d, length, tau, displacement):
    """All causal target lifts in the first-cut band, including null lifts.

    A nearest representative and its one-axis neighbours exhaust the lattice:
    a lift with two nonnearest coordinates has length at least L/sqrt(2).
    Do not use this enumeration outside its checked geometric domain.
    """
    _dimension(d)
    length = _positive(length, "length")
    tau = float(tau)
    if not math.isfinite(tau) or not 0 <= tau < length / math.sqrt(2):
        raise ValueError("requires 0 <= tau < L/sqrt(2)")
    a = np.asarray(displacement, dtype=float)
    if a.shape != (d-1,) or not np.all(np.isfinite(a)):
        raise ValueError("displacement must have d-1 finite coordinates")
    a = (a + length/2) % length - length/2
    candidates = [a]
    for i in range(d-1):
        for sign in (-1, 1):
            b = a.copy()
            b[i] += sign*length
            candidates.append(b)
    return tuple(b for b in candidates if np.dot(b, b) <= tau*tau)


def null_excesses(length, x, y):
    """Stable FC5 values; x,y are the two branch squared proper times."""
    length = _positive(length, "length")
    x, y = float(x), float(y)
    if not all(math.isfinite(t) and t >= 0 for t in (x, y)):
        raise ValueError("nonnegative finite branch phases required")
    s = (y-x)/(2*length)
    h = math.sqrt(length*length/4 + (x+y)/2 + s*s)
    # Rationalized differences retain tiny phases without cancellation.
    return x/(h+length/2+s), y/(h+length/2-s)


@lru_cache(maxsize=8)
def _gauss(order):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    return (nodes+1)/2, weights/2


def overlap_volume(d, length, x, y):
    """Actual common-source overlap H in FC6 (one of TWO equal overlaps).

    The transverse radius is the minimum of all three cone constraints.
    Integrate the first angular strip exactly in the inner variable, then
    retain the three positive pieces on the small closing strip. No limiting
    overlap profile is substituted for the finite-phase volume.
    """
    _, vp = _constants(d)
    u, v = null_excesses(length, x, y)
    if u == 0 or v == 0:
        return 0.
    length = float(length)
    q = d/2
    if d == 2:
        return u*v/2
    alpha = (length+u)/(length+u+v)
    ratio = u/(length+u)
    first = quad(lambda a: (a*(1-ratio*a))**(q-1)/q,
                 0, alpha, epsabs=2e-13, epsrel=2e-12)[0]
    nodes, weights = _gauss(24)
    width = v/(length+u+v)

    def last_strip(r):
        # 1-a = width*r is calculated directly, never by subtracting a ~ 1.
        gap = width*r
        a = 1-gap
        ba = (length+v)/(length+u+v)*r
        bd = 1-u/(length+u+v)*r
        one_minus_bd = u/(length+u+v)*r
        term1 = a**(q-1)*ba**q/q
        # This positive integral avoids subtracting two large powers.
        b = ba+(bd-ba)*nodes
        term2 = (bd-ba)*np.dot(weights, (gap*(1+length/v-b))**(q-1))
        term3 = (length/u+gap)**(q-1)*one_minus_bd**q/q
        return term1+term2+term3

    last = width*quad(last_strip, 0, 1, epsabs=2e-13, epsrel=2e-12)[0]
    return vp/2*(u*v)**q*(first+last)


def overlap_leading(d, length, x, y):
    """FC7 upper bound/leading term, deliberately separate from actual H."""
    _, vp = _constants(d)
    length = _positive(length, "length")
    null_excesses(length, x, y)  # Validate both phases.
    q = d/2
    return vp/(2*q*q*length**(2*q))*(float(x)*float(y))**q


def two_route_volume(d, length, x, y):
    """Actual volume in the two-route region, with both overlaps subtracted."""
    c, _ = _constants(d)
    length = _positive(length, "length")
    null_excesses(length, x, y)
    x, y = float(x), float(y)
    a = length*length/4 + (x+y)/2 + (y-x)**2/(4*length*length)
    if a >= length*length/2:
        raise ValueError("two-route phases exceed the first-cut geometric band")
    return c*(x**(d/2)+y**(d/2))-2*overlap_volume(d, length, x, y)


def actual_interval(d, length, tau, displacement):
    """Actual projected-union volume, or zero for an acausal endpoint pair."""
    lifts = causal_lifts(d, length, tau, displacement)
    c, _ = _constants(d)
    phases = tuple(max(0., tau*tau-float(np.dot(a, a))) for a in lifts)
    if not phases:
        return 0.
    if len(phases) == 1:
        return c*phases[0]**(d/2)
    if len(phases) != 2:
        raise AssertionError("the first-cut lift theorem was violated")
    return two_route_volume(d, length, *phases)


def circle_interval_distance(length, tau, displacement):
    """Independent 2D FC2 distance integral, with all distance breakpoints."""
    length = _positive(length, "length")
    if not math.isfinite(tau) or tau < 0:
        raise ValueError("nonnegative finite time gap required")
    a = float(displacement) % length
    points = sorted({0., length, length/2, a, (a+length/2) % length})
    f = lambda z: max(0., tau-quotient_distance([z], length)
                     -quotient_distance([z-a], length))
    # On each distance-linear interval, retain the positive-part root too.
    value = 0.
    for left, right in zip(points[:-1], points[1:]):
        raw_left = tau-quotient_distance([left], length)-quotient_distance([left-a], length)
        raw_right = tau-quotient_distance([right], length)-quotient_distance([right-a], length)
        knots = [left, right]
        if raw_left*raw_right < 0:
            knots.insert(1, left+(right-left)*raw_left/(raw_left-raw_right))
        for lo, hi in zip(knots[:-1], knots[1:]):
            value += (hi-lo)*(f(lo)+f(hi))/2
    return value
