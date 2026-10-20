"""Finite domain/arithmetic diagnostics for NG, FL and DL.

Not a limit solver or a certificate of uniform gluing. Production observables,
canonical coefficients, probability APIs and dependencies are unchanged.
"""

from itertools import combinations
import math

import numpy as np
from scipy.integrate import quad
from scipy.special import beta as beta_function
import sympy as s

from dimension_kernels import (
    action_constants, factor_count, interval_coefficient, sphere_area,
    transverse_moment,
)
from null_cartesian_pushforward import coefficients


def _positive(*values):
    if any(isinstance(x, bool) or not math.isfinite(x) or x <= 0 for x in values):
        raise ValueError("positive finite parameters required")


def _order(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")


def rectangle_action(rho, U, V):
    """Exact flat d=2 whole action, including its one physical point."""
    _positive(rho, U, V)
    return -2*math.expm1(-rho*U*V/2)


def rectangle_density(z, U, V, *, temporal_cutoff=None):
    """Actual pair pushforward, optionally at physical (du+dv)/2 < cutoff."""
    _positive(z, U, V)
    Q = U*V/2
    if temporal_cutoff is None:
        if z >= Q:
            return 0.0
        return (Q+z)*math.log(Q/z)-2*(Q-z)
    r = temporal_cutoff
    _positive(r)
    if 2*r >= min(U, V):
        raise ValueError("diagnostic cutoff must be below both half side lengths")
    if z >= r*r/2:
        return 0.0
    root = math.sqrt(r*r-2*z)
    upper = r+root
    lower = 2*z/upper  # Avoid subtraction of nearly equal numbers.
    return (Q+z)*math.log(upper/lower)-(U+V)*root


def future_tip_cross_pair(rho, U, V, radius):
    """All incoming partners from the L-shaped complement, with true intervals."""
    _positive(rho, U, V, radius)
    if radius >= min(U, V):
        raise ValueError("tip radius must be smaller than both sides")
    areas = ((U-radius)*V/2, U*(V-radius)/2,
             (U-radius)*(V-radius)/2, radius*radius/2, U*V/2)
    terms = [math.expm1(-rho*q) for q in areas]
    return math.fsum(c*x for c, x in zip((-1, -1, 1, -1, 1), terms))/(2*rho*rho)


def _box(box):
    if (len(box) != 2 or any(len(axis) != 2 for axis in box)
            or any(not math.isfinite(x) for axis in box for x in axis)
            or any(axis[0] >= axis[1] for axis in box)):
        raise ValueError("two nonempty finite coordinate intervals required")
    return tuple(tuple(float(x) for x in axis) for axis in box)


def _overlap_nodes(source, target, order):
    """Integrate the actual one-coordinate source/target displacement overlap."""
    top = max(0., target[1]-source[0])
    breaks = sorted({0., top, *(max(0., min(top, b-a))
                               for a in source for b in target)})
    nodes, weights = np.polynomial.legendre.leggauss(order)
    values, measures = [], []
    for lo, hi in zip(breaks, breaks[1:]):
        x = lo+(hi-lo)*(nodes+1)/2
        overlap = np.maximum(0., np.minimum(source[1], target[1]-x)
                             -np.maximum(source[0], target[0]-x))
        values.extend(x)
        measures.extend(weights*(hi-lo)/2*overlap)
    return np.array(values), np.array(measures)


def box_pair(rho, source, target, *, order=36):
    """Finite flat ordered pair integral for two endpoint boxes.

    Uses the original ambient interval even if their union is not causally
    convex. It is not the action of a new region with a restricted interval.
    """
    _positive(rho)
    _order(order)
    source, target = _box(source), _box(target)
    du, wu = _overlap_nodes(source[0], target[0], order)
    dv, wv = _overlap_nodes(source[1], target[1], order)
    phase = rho*np.outer(du, dv)/2
    signed = np.polynomial.polynomial.polyval(phase, coefficients(2))*np.exp(-phase)
    return float(wu@signed@wv/4)


def _subsets(items):
    for size in range(1, len(items)+1):
        for subset in combinations(items, size):
            yield subset, (-1)**(size+1)


def finite_null_action(rho, lower_corners, upper_corners):
    """Exact double membership valuation, not arbitrary bilocal additivity."""
    _positive(rho)
    lower, upper = tuple(lower_corners), tuple(upper_corners)
    if not lower or not upper or any(len(p) != 2 or not all(math.isfinite(x) for x in p)
                                    for p in lower+upper):
        raise ValueError("nonempty finite corner lists required")
    terms = []
    for I, left_sign in _subsets(lower):
        a = tuple(max(p[k] for p in I) for k in range(2))
        for J, right_sign in _subsets(upper):
            b = tuple(min(p[k] for p in J) for k in range(2))
            if all(a[k] < b[k] for k in range(2)):
                terms.append(left_sign*right_sign*rectangle_action(rho, b[0]-a[0], b[1]-a[1]))
    return math.fsum(terms)


def curved_rectangle_action(rho, amplitude, *, order=24, representation="endpoints"):
    """Complete finite d=2 quadrature for A(u,v)=1+amplitude*u*v on (0,1)^2.

    The actual weighted diamond volume and both endpoint measures are used.
    No large-density accuracy or limit certification is promised.
    """
    _positive(rho)
    _order(order)
    if (not math.isfinite(amplitude) or amplitude <= -1
            or representation not in ("endpoints", "displacements")):
        raise ValueError("positive density and known representation required")
    nodes, weights = np.polynomial.legendre.leggauss(order)
    nodes, weights = (nodes+1)/2, weights/2
    a, b = np.repeat(nodes, order), np.tile(nodes, order)
    if representation == "endpoints":
        p, q = a, a+(1-a)*b
    else:
        p, q = (1-a)*b, (1-a)*b+a
    weight = np.repeat(weights, order)*np.tile(weights, order)*(1-a)
    parts = []
    for pu, qu, wu in zip(p, q, weight):
        volume = (qu-pu)*(q-p)/2*(1+amplitude*(qu+pu)*(q+p)/4)
        phase = rho*volume
        signed = np.polynomial.polynomial.polyval(phase, coefficients(2))*np.exp(-phase)
        endpoints = (1+amplitude*pu*p)*(1+amplitude*qu*q)
        parts.append(wu*float(weight@(endpoints*signed))/4)
    return 2*rho*(.5+amplitude/8)-4*rho*rho*math.fsum(parts)


def floor_tail(d, height):
    """FL3's signed-after-integration majorant, not the signed response itself."""
    m = factor_count(d)
    if not math.isfinite(height) or height < 0:
        raise ValueError("nonnegative finite height required")
    return quad(lambda v: v**d/(1+v**d)**(2*(m+1)/d),
                height, np.inf, epsabs=1e-11)[0]


def floor_tail_mass(d):
    m = factor_count(d)
    return float(beta_function((d+2)/d, (2*m-d)/d)/d)


def positive_quadratic_constant(d):
    factor_count(d)
    if d == 2:
        raise ValueError("the positive quadratic formula requires d > 2")
    n = s.Rational(d-2, 2)
    return s.simplify(s.pi**n/s.gamma(n)*transverse_moment(d, s.Rational(d, 2))
                      /(n*(n+1)))


def flat_bicone_target(d, T):
    """NG8's independent flat geometry: local target, nonlocal term, full target."""
    _positive(T)
    C = positive_quadratic_constant(d)
    n = (d-2)/2
    radial = 2*(T/2)**(d-2)/(d-2)*quad(
        lambda z: z**n/(1+z)**2, 0, 1, epsabs=1e-12)[0]
    area = float(sphere_area(d))*T**(d-2)
    nonlocal_term = float(action_constants(d)[1]*interval_coefficient(d)**(-1-s.Rational(2, d))
                          *C*sphere_area(d)/4)*radial
    return area, nonlocal_term, area-nonlocal_term
