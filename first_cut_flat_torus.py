"""Diagnostics for the written first-cut torus theorem, not a proof checker.

The actual interval is a union, not a selected lift or a sum of lift volumes.
Only the cubic first-cut regime tau < L/sqrt(2) is implemented here. Existing
thin-torus and production action/probability definitions are left unchanged.
"""

from functools import lru_cache
import math

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import beta, gamma, roots_jacobi

from dimension_kernels import (
    _dimension, action_constants, interval_coefficient, transverse_moment,
)
from full_partner_globalization import _kernel


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


def phase_weight(d, length, duration, a):
    """Actual FC10 transverse and closing-time integral F(A).

    FC11's rationalized integrand retains the closing contact and avoids
    subtracting nearly equal square roots. In d=2 the transverse space has
    one point of mass one, rather than a fictitious zero-area sphere.
    """
    length, duration = first_cut_geometry(d, length, duration)
    a = _positive(a, "squared transverse-free time")
    depth = duration*duration-a
    if depth <= 0:
        return 0.
    if d == 2:
        root = math.sqrt(a)
        return depth/(4*length*root*(duration+root))
    _, vp = _constants(d)
    p = d-2
    nodes, weights = _gauss(32)
    root = np.sqrt(a+depth*nodes*nodes)
    integrand = nodes**(p-1)*(1-nodes*nodes)/(root*(duration+root))
    return p*vp*depth**(d/2)/(4*length)*np.dot(weights, integrand)


def _phase_a(length, x, y):
    return length*length/4+(x+y)/2+(y-x)**2/(4*length*length)


def _small_phase(d, length, duration, w):
    length, duration = first_cut_geometry(d, length, duration)
    w = float(w)
    if not math.isfinite(w) or not 0 <= w < (duration*duration-length*length/4)/4:
        raise ValueError("phase must lie in the fixed first-cut small-phase neighbourhood")
    return length, duration, w


@lru_cache(maxsize=16)
def _quarter_rule(d, order, extra_power=0):
    _dimension(d)
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    exponent = 2/d-1+extra_power
    nodes, weights = roots_jacobi(order, exponent, exponent)
    return (nodes+1)/2, weights/2**(2*exponent+1)


def reference_primitive(d, length, duration, cutoff, w):
    """FC9 unfolded lift-counted reference, NOT the thick-torus primitive."""
    length, duration = first_cut_geometry(d, length, duration)
    cutoff = _positive(cutoff, "temporal cutoff")
    w = float(w)
    if not cutoff < length/2 or not math.isfinite(w) or w < 0:
        raise ValueError("requires delta < L/2 and nonnegative finite phase")
    k = d-1
    area = 2*math.pi**(k/2)/gamma(k/2)

    def shell(tau):
        difference = tau**k if w >= tau*tau else tau**k*(-math.expm1(k/2*math.log1p(-w/(tau*tau))))
        return (duration-tau)*difference

    points = [math.sqrt(w)] if cutoff**2 < w < duration**2 else None
    return length**k*area/k*quad(shell, cutoff, duration, points=points,
                               epsabs=2e-13, epsrel=2e-12)[0]


def strip_primitive(d, length, duration, w):
    """One of the TWO reference strips removed in FC10, with its true Y(x)."""
    length, duration, w = _small_phase(d, length, duration, w)

    def inner(x):
        upper = x-length*length+2*length*math.sqrt(duration*duration-x)
        return upper*quad(lambda v: phase_weight(
            d, length, duration, _phase_a(length, x, upper*v)),
            0, 1, epsabs=2e-13, epsrel=2e-12)[0]

    return w*quad(lambda u: inner(w*u), 0, 1, epsabs=2e-13, epsrel=2e-12)[0]


def sum_corner_primitive(d, length, duration, w, order=24):
    """Actual sum-volume corner C0, before projected-overlap correction."""
    length, duration, w = _small_phase(d, length, duration, w)
    if w == 0:
        return 0.
    q = d/2
    ts, tw = _quarter_rule(d, order)
    rs, rw = _gauss(20)
    total = 0.
    for t, weight in zip(ts, tw):
        a, b = t**(1/q), (1-t)**(1/q)
        inner = sum(rweight*r*phase_weight(
            d, length, duration, _phase_a(length, w*r*a, w*r*b))
            for r, rweight in zip(rs, rw))
        total += weight*inner
    return w*w/q*total


def overlap_primitive_scaled(d, length, duration, w, order=24, overlap_copies=2):
    """(C-C0)/w^(q+2) from the ACTUAL finite-phase shell, not its limit.

    Solve the exact union-volume root in scaled excess coordinates so tiny
    root shifts are not lost to subtraction. overlap_copies=0 or 1 is an
    explicitly incorrect diagnostic control, never an alternative action.
    """
    length, duration, w = _small_phase(d, length, duration, w)
    if w <= 0:
        raise ValueError("positive phase required for the scaled shell")
    if isinstance(overlap_copies, bool) or overlap_copies not in (0, 1, 2):
        raise ValueError("overlap_copies must be the actual 2 or a named 0/1 control")
    if overlap_copies == 0:
        return 0.
    q = d/2
    c, _ = _constants(d)
    wq = w**q
    ts, tw = _quarter_rule(d, order, extra_power=1)
    rs, rw = _gauss(10)
    total = 0.
    for t, weight in zip(ts, tw):
        a, b = t**(1/q), (1-t)**(1/q)

        def equation(eta):
            excess = wq*eta
            r = w*(1+excess)
            phase_increment = math.expm1(q*math.log1p(excess))/wq
            overlap_increment = overlap_copies/c*overlap_volume(
                d, length, r*a, r*b)/(wq*wq)
            return phase_increment-overlap_increment

        upper = (1/max(a, b)-1)/wq
        eta = brentq(equation, 0, upper, xtol=2e-13, rtol=2e-13)
        inner = sum(rweight*(1+wq*eta*z)*phase_weight(
            d, length, duration,
            _phase_a(length, w*(1+wq*eta*z)*a, w*(1+wq*eta*z)*b))
            for z, rweight in zip(rs, rw))
        total += weight*eta/(t*(1-t))*inner
    return total/q


def overlap_primitive_coefficient(d, length, duration):
    """Derived kappa in FC16, excluding source volume and axis count."""
    length, duration = first_cut_geometry(d, length, duration)
    c, vp = _constants(d)
    q = d/2
    lam = vp/(c*q*q*length**d)
    return phase_weight(d, length, duration, length*length/4)*lam/(q*q)*beta(1+1/q, 1+1/q)


def primitive_components(d, length, duration, cutoff, w, order=24):
    """Actual near-zero full long primitive, retaining the regular complement."""
    length, duration, w = _small_phase(d, length, duration, w)
    ref = reference_primitive(d, length, duration, cutoff, w)
    strip = strip_primitive(d, length, duration, w)
    corner = sum_corner_primitive(d, length, duration, w, order)
    overlap = 0. if w == 0 else w**(d/2+2)*overlap_primitive_scaled(
        d, length, duration, w, order)
    multiplier = length**(d-1)*(d-1)
    return dict(reference=ref, strip=strip, corner=corner, overlap=overlap,
                axis_source_factor=multiplier,
                actual=ref+multiplier*(corner-2*strip+overlap))


def circle_long_primitive(length, duration, cutoff, w):
    """Independent 2D actual sublevel integral, not reference subtraction.

    The double-route interval volume is L*(tau-L/2). Integrate its full
    plateau and the single-route shell, including their exact time contacts.
    """
    length, duration = first_cut_geometry(2, length, duration)
    cutoff = _positive(cutoff, "temporal cutoff")
    if cutoff >= length/2 or not math.isfinite(w) or w < 0:
        raise ValueError("requires delta < L/2 and nonnegative finite phase")

    def integrand(tau):
        upper = min(tau, length-tau, length/2)
        lower = math.sqrt(max(0., tau*tau-w))
        single = max(0., upper-lower)
        double = max(0., tau-length/2) if 2*length*tau-length*length <= w else 0.
        return (duration-tau)*2*(single+double)

    contacts = sorted({cutoff, duration} | {v for v in (
        length/2, math.sqrt(w), (length*length+w)/(2*length))
        if cutoff < v < duration})
    return length*sum(quad(integrand, lo, hi, epsabs=2e-14, epsrel=2e-12)[0]
                      for lo, hi in zip(contacts[:-1], contacts[1:]))


def circle_full_pair(length, duration, rho):
    """Actual full 2D pair integral from single-route and plateau domains."""
    length, duration = first_cut_geometry(2, length, duration)
    rho = _positive(rho, "density")
    kernel = _kernel(2)

    def temporal(tau):
        upper = min(tau, length-tau, length/2)
        single = quad(lambda a: kernel(rho*(tau*tau-a*a)/2),
                      0, upper, epsabs=2e-12, epsrel=2e-11)[0]
        double = max(0., tau-length/2)*kernel(rho*length*(tau-length/2))
        return 2*(duration-tau)*(single+double)

    return length*sum(quad(temporal, lo, hi, epsabs=2e-12, epsrel=2e-11)[0]
                      for lo, hi in ((0, length/2), (length/2, duration)))


def overlap_signed_coefficient(d, length, duration):
    """Coefficient of rho^(-2/d) for the overlap SECTOR, not the full action."""
    import sympy as s
    length, duration = first_cut_geometry(d, length, duration)
    c, _ = _constants(d)
    q = d/2
    _, pair = action_constants(d)
    moment = float(transverse_moment(d, s.Rational(d, 2)+1))
    coefficient = length**(d-1)*(d-1)*overlap_primitive_coefficient(d, length, duration)
    return -float(pair)*(q+2)*coefficient*c**(-(q+2)/q)*moment
