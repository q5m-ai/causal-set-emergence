"""Diagnostics for notes/curved4-focal-research.md, not an action solver.

Physical routines use the explicit compact pp-wave metric and its actual
pendulum action. Model routines are separately named: their matching integral
is NOT asserted to be the coefficient of the complete physical action.
"""

from functools import lru_cache
import math

import numpy as np
import sympy as sym
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import beta, ellipj, ellipeinc, roots_jacobi, roots_legendre

DURATION = 7 / 4
SOURCE_RZ_VOLUME = 400


@lru_cache(maxsize=None)
def _legendre(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    return roots_legendre(order)


def physical_time_weight(length, excess, cutoff=None, short=False):
    """CR8/CR9, with BOTH endpoint times and all lifted z partners.

    excess is Delta(v)-b^2/(2*length), not excess above a chosen geodesic.
    The actual causal test excess >= S_length(p,q) remains the caller's job.
    """
    if not math.isfinite(length) or length <= 0 or not math.isfinite(excess):
        raise ValueError("finite positive length and finite excess required")
    if cutoff is not None and not 0 < cutoff < DURATION:
        raise ValueError("cutoff must lie strictly between 0 and duration")
    if short and cutoff is None:
        raise ValueError("short requires a cutoff")
    arrival = length / 2 + excess
    full = 4 / 3 * math.sqrt(2 * length) * max(0, DURATION-arrival)**1.5
    if cutoff is None:
        return full
    gap = max(0, cutoff-arrival)
    removed = 2*math.sqrt(2*length)*((DURATION-arrival)*math.sqrt(gap)-gap**1.5/3)
    return removed if short else full-removed


def pendulum_endpoint_action(length, k):
    """Actual x(length), S for initial x=0 and x'=k/2.

    Both oscillating and rotating paths are supported. The caller selects the
    unique sub-pi boundary solution before identifying this with a minimum.
    """
    if not 0 < length < math.pi or not math.isfinite(k) or k < 0:
        raise ValueError("requires 0 < length < pi and finite k >= 0")
    if k == 0:
        return 0., 0.
    if abs(k-1) < 1e-12:
        # Separatrix: sin(2*x)=tanh(length).
        x = math.asin(math.tanh(length))/2
        action = -length/8 + math.tanh(length)/4
        return x, action
    if k < 1:
        sn, _, _, amplitude = ellipj(length, k*k)
        x = math.asin(np.clip(k*sn, -1, 1))/2
        if k < .002:
            action = k*k/8*quad(lambda t: 1-2*ellipj(t, k*k)[0]**2,
                                0, length, epsabs=1e-13, epsrel=1e-13)[0]
        else:
            action = ((k*k-2)*length+2*ellipeinc(amplitude, k*k))/8
    else:
        _, _, _, amplitude = ellipj(k*length, 1/(k*k))
        x = amplitude/2
        action = k*ellipeinc(amplitude, 1/(k*k))/4-k*k*length/8
    return float(x), float(action)


def physical_segment_action(length, target):
    """Actual S_length(0,target) for length < pi, |target| < pi/4.

    Poincare proves strict convexity in the selected lift; the winding-gap
    argument in the note proves that no other circle lift lowers its action.
    Not a general S_L(p,q) implementation beyond this guarded regime.
    """
    if not 0 < length < math.pi or not abs(target) < math.pi/4:
        raise ValueError("requires 0 < length < pi and |target| < pi/4")
    target = abs(target)
    if target == 0:
        return 0.
    high = 1.
    while pendulum_endpoint_action(length, high)[0] < target:
        high *= 2
    k = brentq(lambda t: pendulum_endpoint_action(length, t)[0]-target,
               0, high, xtol=2e-14, rtol=2e-14)
    return pendulum_endpoint_action(length, k)[1]


def physical_focal_volume(excess, order=28):
    """Actual CR7 at (L,p,q)=(pi,0,0), not the quartic profile.

    Coercivity excludes every other winding/sublevel component in this small
    range. Both physical tips and both x signs are integrated. Gauss rules
    are diagnostics and do not certify quadrature error or the limit.
    """
    if not 0 < excess <= .001:
        raise ValueError("requires 0 < excess <= .001")
    nodes, weights = _legendre(order)
    # Coercive bound on the sine coefficient and complementary derivative norm.
    amplitude = math.sqrt(4/math.sqrt(math.pi)*math.sqrt(excess)+8/math.pi*excess)
    answer = 0.
    for ss, sw in zip(math.pi/4*(1+nodes), math.pi/4*weights):
        def cost(x):
            return physical_segment_action(ss, x)+physical_segment_action(math.pi-ss, x)
        bound = amplitude*math.sin(ss)+math.sqrt(8*excess*ss/3)
        top = min(math.pi/4-1e-8, 1.01*bound)
        end = brentq(lambda x: cost(x)-excess, 0, top, xtol=2e-13, rtol=2e-13)
        xs = end/2*(1+nodes)
        inner = end*np.dot(weights, [max(0, excess-cost(x))**1.5 for x in xs])
        # inner already counts both signs, factor 2 below counts both tips.
        answer += sw*math.sqrt(2*ss*(math.pi-ss)/math.pi)*inner
    return 8/3*answer


def focal_constants():
    """Derived constants C,J,D in CR10/CR11."""
    quartic = math.pi/4
    longitudinal = quad(lambda t: math.sqrt(2*t*(math.pi-t)/math.pi)*math.sin(t),
                        0, math.pi, epsabs=1e-12, epsrel=1e-12)[0]
    d = 4/3*longitudinal*quartic**(-.25)*beta(.25, 2.5)/2
    return quartic, longitudinal, d


def segment_jet(length, order=36):
    """Actual coefficients x^2,x^4,x^6 of S_length(0,x).

    The sixth coefficient includes the minimizing-path Green correction,
    not just the Taylor coefficient of the potential.
    """
    if not 0 < length < math.pi:
        raise ValueError("requires 0 < length < pi")
    nodes, weights = _legendre(order)
    t = length/2*(nodes+1)
    w = length/2*weights
    g = np.sin(t)/math.sin(length)
    # Ordered triangle integration avoids the derivative kink of the Green
    # kernel on its diagonal. The symmetric second triangle contributes 2.
    green_term = 0.
    for hi, whi, ghi in zip(t, w, g):
        lo = hi/2*(nodes+1)
        kernel = np.sin(lo)*math.sin(length-hi)/math.sin(length)
        green_term += whi*ghi**3*hi*np.dot(weights, (np.sin(lo)/math.sin(length))**3*kernel)
    return np.array([.5/math.tan(length),
                     2/3*np.dot(w, g**4),
                     -16/45*np.dot(w, g**6)-32/9*green_term])


def physical_regular_volume_jet(length, order=36):
    """Actual coefficients H0,H1,H2 in W(L,0,0,e)=e^2*(H0+H1*e+H2*e^2+...)."""
    if not 0 < length < math.pi:
        raise ValueError("requires 0 < length < pi")
    nodes, weights = _legendre(order)
    result = np.zeros(3)
    for ss, sw in zip(length/4*(1+nodes), length/4*weights):
        _, q4, q6 = segment_jet(ss, order)+segment_jet(length-ss, order)
        q2 = math.sin(length)/(2*math.sin(ss)*math.sin(length-ss))
        factor = math.sqrt(2*ss*(length-ss)/length)/math.sqrt(q2)
        result += sw*factor*np.array([1, -q4/(4*q2*q2),
                                     35*q4*q4/(128*q2**4)-5*q6/(32*q2**3)])
    return math.pi*result  # 4/3 * (3*pi/8) * 2 symmetric tips


def inverse_jet(volume_jet):
    h0, h1, h2 = volume_jet
    return np.array([h0**(-.5), -h1/(2*h0*h0),
                     5*h1*h1/(8*h0**3.5)-h2/(2*h0**2.5)])


# The remaining routines refer only to the normalized optical model.
MODEL_POWER = 9/7
MODEL_C = 3*math.pi/8


@lru_cache(maxsize=None)
def _jacobi(order):
    _legendre(order)
    return roots_jacobi(order, 1.5, 1.5)


def model_profile(excess, r, order=32):
    """All wells of f_r(E) in CR15, not a physical interval-volume solver."""
    if not math.isfinite(excess) or excess <= 0 or not abs(r) <= .5:
        raise ValueError("requires finite excess > 0 and |r| <= 1/2")
    nodes, weights = _jacobi(order)
    if excess == 1/16 and abs(r) == .5:
        # The double saddle root can appear as a tiny complex pair. Testing
        # only the midpoint of the outer interval then incorrectly drops both
        # wells. The exact integral of |u+1/2|^3*(1/2-(u+1/2)^2)^(3/2)
        # is known at this contact; this remains a model diagnostic.
        return 1/(70*math.sqrt(2))
    roots = np.roots([1, 4*r, 1, 0, -excess])
    real = sorted(z.real for z in roots if abs(z.imag) < 1e-9)
    total = 0.
    for lo, hi in zip(real, real[1:]):
        mid, half = (lo+hi)/2, (hi-lo)/2
        if mid**4+4*r*mid**3+mid*mid >= excess:
            continue
        # Factor the two endpoint roots; the Jacobi weight integrates their
        # exact 3/2 powers. The remaining quadratic stays nonnegative here.
        z = mid+half*nodes
        cc = 4*r+lo+hi
        dd = 1+cc*(lo+hi)-lo*hi
        total += half**4*np.dot(weights, np.maximum(z*z+cc*z+dd, 0)**1.5)
    return total


def model_averaged_profile(excess, order=24):
    """Phi(E), resolving both opening/saddle contacts instead of dropping a well."""
    if excess <= 0:
        raise ValueError("positive excess required")
    edges = [0., .5]
    if excess <= 1/12:
        root = math.sqrt(1-12*excess)
        for square in (6*excess/(1+root), (1+root)/2):
            r = (2*square+1)/(6*math.sqrt(square))
            if 0 < r < .5:
                edges.append(r)
    edges = sorted(set(edges))
    nodes, weights = _legendre(order)
    return sum((hi-lo)*np.dot(weights, [model_profile(excess, r, order)**(-MODEL_POWER)
               for r in (hi+lo)/2+(hi-lo)*nodes/2])
               for lo, hi in zip(edges, edges[1:]))


def model_subtractions():
    j = quad(lambda t: (1+t*t)**(-MODEL_POWER), 0, 1, epsabs=1e-13)[0]
    a0 = MODEL_C**(-MODEL_POWER)
    return a0, a0*(-MODEL_POWER/6+(j-1)/2)


def model_matched_truncation(epsilon=.001, top=10000., order=24):
    """Finite CR18 truncation; neither a sign certificate nor fitted coefficient.

    Integrates Phi from epsilon to top and subtracts its exact two divergent
    powers. The missing low/high integrals are NOT filled by an assumed model
    coefficient. Compare cutoffs/refinements explicitly.
    """
    if not 0 < epsilon < .01 or top < 100:
        raise ValueError("requires 0 < epsilon < .01 and top >= 100")
    edges = sorted(set([epsilon, .01, .04, 1/16, 1/12, .15, 1,
                        *np.geomspace(1, top, 7)]))
    nodes, weights = _legendre(order)
    value = 0.
    for lo, hi in zip(edges, edges[1:]):
        left, right = math.log(lo), math.log(hi)
        xs = (right+left)/2+(right-left)/2*nodes
        value += (right-left)/2*np.dot(weights,
            [model_averaged_profile(math.exp(x), order)*math.exp(x) for x in xs])
    a0, a1 = model_subtractions()
    return value-7*a0/11*epsilon**(-11/7)-7*a1/4*epsilon**(-4/7)


def symbolic_metric_data():
    """Direct connection/Ricci calculation in the repository's sign convention."""
    u, v, x, z = coords = sym.symbols("u v x z", real=True)
    h = sym.sin(2*x)**2/4
    metric = sym.Matrix([[h, 1, 0, 0], [1, 0, 0, 0],
                         [0, 0, -1, 0], [0, 0, 0, -1]])
    inv = metric.inv()
    connection = [[[sym.simplify(sum(inv[a, k]*(sym.diff(metric[k, c], coords[b])
        +sym.diff(metric[k, b], coords[c])-sym.diff(metric[b, c], coords[k]))/2
        for k in range(4))) for c in range(4)] for b in range(4)] for a in range(4)]
    ricci = sym.Matrix(4, 4, lambda b, d: sym.simplify(sum(
        sym.diff(connection[a][a][b], coords[d])-sym.diff(connection[a][d][b], coords[a])
        +sum(connection[a][d][e]*connection[e][a][b]
             -connection[a][a][e]*connection[e][d][b] for e in range(4))
        for a in range(4))))
    scalar = sym.simplify(sum(inv[a, b]*ricci[a, b] for a in range(4) for b in range(4)))
    return metric, ricci, scalar, coords
