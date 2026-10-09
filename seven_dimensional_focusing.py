"""Diagnostics and an exact sign certificate for the written #151 obstruction.

Fixed geometry: R x (unit S^2 x T^4_20), slab duration 4, physical dimension 7.
These are not replacement production action APIs. Quadratures are finite
regressions; sign_certificate() alone uses exact rational bounds throughout.
"""

from fractions import Fraction as F
from functools import lru_cache
from math import factorial

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import hyp2f1

from general_metric_gate import gauss_rule
from sphere_circle_focusing import (
    _log_sinc_derivatives, _sphere_rule, area_ratio, circle_section,
)

DURATION = 4.0
CIRCUMFERENCE = 20.0
SPATIAL_VOLUME = 4*np.pi*CIRCUMFERENCE**4
PAIR_FACTOR = 2*np.pi*SPATIAL_VOLUME
ANTIPODAL_COEFFICIENT = 16*np.pi/3*(12-np.pi**2)
OPENING_COEFFICIENT = 32/(35*np.sqrt(2)*np.pi)


def time_weight(u, cutoff=None, short=False):
    """O4/O16: integrate BOTH times and all four flat partner directions."""
    if not np.isfinite(u) or not 0 <= u <= DURATION:
        raise ValueError("requires 0 <= u <= 4")
    if cutoff is not None and (not np.isfinite(cutoff) or not 0 < cutoff < DURATION):
        raise ValueError("requires 0 < cutoff < 4")
    if short and cutoff is None:
        raise ValueError("short weight requires a cutoff")
    full = np.pi**2/6*u*(DURATION-u)**3*(DURATION+3*u)
    if cutoff is None:
        return full
    gap = max(0., cutoff-u)
    # Integrate (T-tau)*(tau^2-u^2) with tau=u+x; stable at the contact.
    removed = 2*np.pi**2*u*(u*(DURATION-u)*gap**2
                           + (DURATION-3*u)*gap**3/3-gap**4/4)
    return removed if short else full-removed


def flat_section(u, r, ss, order=24):
    """Actual integral over R^4 of (u-hypot(r,z)-hypot(s,z))_+."""
    if not np.isfinite(u) or not 0 < u <= DURATION:
        raise ValueError("requires 0 < u <= 4")
    r, ss = np.broadcast_arrays(r, ss)
    if np.any(~np.isfinite(r)) or np.any(~np.isfinite(ss)) or np.any(r < 0) or np.any(ss < 0):
        raise ValueError("nonnegative finite distances required")
    radius2 = np.where(r+ss < u,
                       np.maximum(0, (u-r-ss)*(u+r+ss)*(u-r+ss)*(u+r-ss))/(4*u*u), 0)
    nodes, weights = gauss_rule(order)
    radius = np.sqrt(radius2)
    z = radius[..., None]*nodes
    rr, sss = r[..., None], ss[..., None]
    gap = ((u-r-ss)[..., None]
           - z*z/np.maximum(np.hypot(rr, z)+rr, 1e-300)
           - z*z/np.maximum(np.hypot(sss, z)+sss, 1e-300))
    return 2*np.pi**2*radius**4*np.sum(weights*nodes**3*np.maximum(0, gap), axis=-1)


def boosted_flat_section(tau, b, r, ss, order=40):
    """Independent nonzero flat displacement: integrate R^3 then the last axis.

    Reuses the actual one-axis ellipse integral, not the claimed boost identity.
    """
    if not abs(b) < tau <= DURATION:
        raise ValueError("requires |b| < tau <= 4")
    u = np.sqrt(tau*tau-b*b)
    if u <= r+ss:
        return 0.
    radius = np.sqrt((u*u-(r+ss)**2)*(u*u-(r-ss)**2))/(2*u)
    nodes, weights = gauss_rule(order)
    z = radius*nodes
    return 4*np.pi*radius**3*np.sum(weights*nodes**2*circle_section(
        tau, b, np.hypot(r, z), np.hypot(ss, z), order=order))


def interval_volume(u, theta, order=48, flat_order=24):
    """Actual O4/O5 interval, including both sphere sheets and all flat points."""
    if not 0 <= theta <= np.pi or not theta <= u <= DURATION:
        raise ValueError("requires 0 <= theta <= pi and theta <= u <= 4")
    if u == theta:
        return 0.
    if theta in (0, np.pi):
        nodes, weights = gauss_rule(order)
        top = np.pi if theta == np.pi else min(np.pi, u/2)
        r = top*nodes
        ss = np.pi-r if theta == np.pi else r
        return 2*np.pi*top*np.sum(weights*np.sin(r)*flat_section(u, r, ss, flat_order))
    x, y, measure = _sphere_rule(theta, u, order)
    return np.sum(measure*flat_section(u, (x+y)/2, (x-y)/2, flat_order))


def polar_volume(u, theta, order=64, flat_order=32):
    """Independent north-pole sphere cubature; no two-distance Jacobian."""
    if not 0 < theta < np.pi or not theta < u <= DURATION:
        raise ValueError("requires 0 < theta < pi and theta < u <= 4")
    nodes, weights = gauss_rule(order)
    edges = sorted(set([0., np.pi, min(np.pi, (u-theta)/2), min(np.pi, (u+theta)/2)]))
    total = 0.
    for lo, hi in zip(edges, edges[1:]):
        r = (lo+(hi-lo)*nodes)[:, None]
        allowed = u-r
        threshold = ((np.cos(np.clip(allowed, 0, np.pi))-np.cos(r)*np.cos(theta))
                     / (np.sin(r)*np.sin(theta)))
        phi_max = np.where(allowed >= np.pi, np.pi,
                           np.where(allowed <= 0, 0, np.arccos(np.clip(threshold, -1, 1))))
        phi = phi_max*nodes[None, :]
        ss = np.arccos(np.clip(np.cos(r)*np.cos(theta)
                              + np.sin(r)*np.sin(theta)*np.cos(phi), -1, 1))
        total += 2*(hi-lo)*np.sum(weights[:, None]*weights[None, :]*np.sin(r)*phi_max
                                 * flat_section(u, r, ss, flat_order))
    return total


@lru_cache(maxsize=4)
def _diamond_rule(order):
    """Fixed O7 quadrature shared by phase values and analytic derivatives."""
    nodes, weights = gauss_rule(order)
    rules = []
    for sign in (-1, 1):
        A = sign*nodes[:, None, None]/2
        radius = .5-np.abs(A)
        B1 = radius*(2*nodes[None, :, None]-1)
        height = np.sqrt(np.maximum(0, radius*radius-B1*B1))
        eta = np.pi*(nodes[None, None, :]-.5)
        B2 = height*np.sin(eta)
        ell = .5+A+B1
        # Integrate B3,...,B6 as the actual four-ball, volume pi^2*R^4/2.
        measure = (np.pi**3/2*radius*height**5*np.cos(eta)**5
                   * weights[:, None, None]*weights[None, :, None]*weights[None, None, :])
        rules.append((B1, B2, ell, measure))
    return tuple(rules)


def regular_phase(theta, e, order=28):
    """O7's exact W/e^(7/2) on the regular side, never across e=2*a."""
    if not 0 < theta < np.pi or not 0 <= e < 2*(np.pi-theta):
        raise ValueError("requires 0 < theta < pi and 0 <= e < 2*(pi-theta)")
    total = 0.
    for B1, B2, ell, measure in _diamond_rule(order):
        phase = 2*theta*e+e*e
        r = np.sqrt((theta*ell+e*B1)**2+phase*B2*B2)
        ss = np.sqrt((theta*(1-ell)-e*B1)**2+phase*B2*B2)
        total += np.sum(measure*area_ratio(theta, r, ss))
    return (2*theta+e)**3.5*total


def regular_phase_jet(theta, order=28):
    """H0, dH0/de, d2H0/de2 at zero by differentiating O7, never fitting W.

    Differentiate the same fixed-diamond quadrature used by regular_phase.
    Root/jet quadrature errors then do not masquerade as an unsubtracted
    zeroth-order term in a small residual. Refinement remains a diagnostic.
    """
    if not 0 < theta < np.pi:
        raise ValueError("requires 0 < theta < pi")
    integrals = np.zeros(3)
    for B1, B2, ell, measure in _diamond_rule(order):
        r, ss = theta*ell, theta*(1-ell)
        rp, sp = B1+B2*B2/ell, -B1+B2*B2/(1-ell)
        rpp = (B1*B1+B2*B2-rp*rp)/r
        spp = (B1*B1+B2*B2-sp*sp)/ss
        lr, lrr = _log_sinc_derivatives(r)
        ls, lss = _log_sinc_derivatives(ss)
        first = lr*rp+ls*sp
        second = lrr*rp*rp+lr*rpp+lss*sp*sp+ls*spp
        for arg, ap, app in (
            (theta, (rp+sp)/2, (rpp+spp)/2),
            (0., (rp+sp)/2, (rpp+spp)/2),
            (r, (rp-sp)/2, (rpp-spp)/2),
            (ss, (sp-rp)/2, (spp-rpp)/2),
        ):
            l1, l2 = _log_sinc_derivatives(arg)
            first -= l1*ap/2
            second -= (l2*ap*ap+l1*app)/2
        q0 = area_ratio(theta, r, ss)
        for j, value in enumerate((q0, q0*first, q0*(second+first*first))):
            integrals[j] += np.sum(measure*value)
    q, length = 3.5, 2*theta
    i0, i1, i2 = integrals
    return np.array([length**q*i0,
                     q*length**(q-1)*i0+length**q*i1,
                     q*(q-1)*length**(q-2)*i0+2*q*length**(q-1)*i1+length**q*i2])


def time_weight_derivatives(u):
    """Exact derivatives of the O4 polynomial; its T-tau contacts stay intact."""
    if not np.isfinite(u) or not 0 <= u <= DURATION:
        raise ValueError("requires 0 <= u <= 4")
    coefficients = [0., DURATION**4, 0., -6*DURATION**2, 8*DURATION, -3.]
    return np.array([np.pi**2/6*sum(
        coefficients[k]*factorial(k)/factorial(k-j)*u**(k-j)
        for k in range(j, 6)) for j in range(6)])


def primitive_coefficients(a, order=28):
    """Actual c1,c2,c3 in O10 for zeta=v^(2/7), without the pair factor C."""
    if not np.isfinite(a) or not 0 < a < np.pi:
        raise ValueError("requires 0 < a < pi")
    theta, p = np.pi-a, 2/7
    h0, h1, h2 = regular_phase_jet(theta, order)
    alpha1 = h0**(-p)
    alpha2 = -p*h1*h0**(-2*p-1)
    alpha3 = p*(3*p+1)/2*h1*h1*h0**(-3*p-2)-p*h2*h0**(-3*p-1)/2
    g0, g1, g2 = time_weight_derivatives(theta)[:3]
    return np.array([g0*alpha1,
                     g0*alpha2+g1*alpha1**2/2,
                     g0*alpha3+g1*alpha1*alpha2+g2*alpha1**3/6])


def inverse_excess(a, v, e0=.2, order=28, volume_order=56):
    """Actual O9 inverse, capped at the fixed e0; not a profile inverse.

    Near-null roots use the exact regular-side representation. Near antipodal
    endpoints a polar cubature avoids ill-conditioned two-distance edges;
    that is the actual O4 integral, not deletion/replacement by the a=0 fibre.
    """
    if (not np.isfinite(a) or not 0 <= a < np.pi or not np.isfinite(v) or v < 0
            or not np.isfinite(e0) or not 0 < e0 < DURATION-np.pi):
        raise ValueError("requires 0 <= a < pi, v >= 0, 0 < e0 < 4-pi")
    if v == 0:
        return 0.
    theta = np.pi-a

    def volume(e):
        if e == 0:
            return 0.
        if e < a:
            return e**3.5*regular_phase(theta, e, order)
        if 0 < a < 1e-6:
            return polar_volume(theta+e, theta, volume_order, flat_order=28)
        return interval_volume(theta+e, theta, volume_order, flat_order=28)

    if volume(e0) <= v:
        return e0
    return brentq(lambda e: volume(e)/v-1, 0, e0, xtol=2e-15, rtol=4*np.finfo(float).eps)


def cut_primitive_diagnostic(v, a0=.12, e0=.2, order=16, diamond_order=28,
                             volume_order=56):
    """Actual O9 primitive AND its derivative-subtracted residual.

    All pieces integrate actual roots and c_j, including 0<a<a0. No model
    replaces a tail. Return N/C, b_j/C, (N-sum b_j*v^(2j/7))/(C*G(pi)*v),
    plus additive contributions from every rescaled t-panel. The constants
    a0,e0 are fixed geometric neighborhoods, not density-dependent cutoffs.
    Floating results and panel refinements are diagnostics, never a dominator
    or an error certificate. Rounding/cancellation eventually limit small-v
    probes. v must be small enough that no e0 cap is active.
    """
    if (not np.isfinite(v) or v <= 0 or not np.isfinite(a0) or not 0 < a0 < .5
            or not np.isfinite(e0) or not 0 < e0 < DURATION-np.pi):
        raise ValueError("requires v > 0, 0 < a0 < 1/2, 0 < e0 < 4-pi")
    lam, zeta = v**(1/3), v**(2/7)
    upper = a0/lam
    contact = (1/(ANTIPODAL_COEFFICIENT*transition_profile(1)))**(1/3)
    edges = sorted({0., upper, *(x for x in (.02, .1, contact, 1., 4., 16., 64., 256.)
                               if x < upper)})
    nodes, weights = gauss_rule(order)
    primitive, coefficients, panels = 0., np.zeros(3), []
    powers = zeta**np.arange(1, 4)
    for lo, hi in zip(edges, edges[1:]):
        # The t^(-4/7) endpoint power becomes bounded under this substitution.
        if lo == 0:
            ts, ws = hi*nodes**(7/3), weights*hi*(7/3)*nodes**(4/3)
        else:
            ts, ws = lo+(hi-lo)*nodes, (hi-lo)*weights
        panel = 0.
        for t, weight in zip(ts, ws):
            a = lam*t
            E = inverse_excess(a, v, e0, diamond_order, volume_order)
            if E == e0:
                raise ValueError("phase is too large for the uncapped O9 diagnostic")
            derivatives = time_weight_derivatives(np.pi-a)
            f = sum(derivatives[j]*E**(j+1)/factorial(j+1) for j in range(6))
            c = primitive_coefficients(a, diamond_order)
            measure = weight*lam*np.sin(a)
            primitive += measure*f
            coefficients += measure*c
            panel += measure*(f-c@powers)/(v*time_weight(np.pi))
        panels.append((lo, hi, panel))
    return {"primitive": primitive, "coefficients": coefficients,
            "scaled_residual": sum(value for _, _, value in panels), "panels": panels}


def transition_profile(S):
    """F of O6, with no factor D; includes the entire active circle."""
    if not np.isfinite(S):
        raise ValueError("finite profile argument required")
    if S <= -1:
        return 0.
    if S >= 1:
        return S**3+1.5*S
    h = S+1
    return OPENING_COEFFICIENT*h**3.5*hyp2f1(.5, .5, 4.5, h/2)


def _hypergeometric_coefficients(n):
    coefficients = [F(1)]
    for k in range(1, n+1):
        coefficients.append(coefficients[-1]*F((2*k-1)**2, 2*k*(2*k+7)))
    return coefficients


def _product(left, right):
    result = [F(0)]*(len(left)+len(right)-1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] += a*b
    return result


def _atan_bounds(inverse, terms=24):
    x = F(1, inverse)
    partial = sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
    next_term = (-1)**terms*x**(2*terms+1)/F(2*terms+1)
    return min(partial, partial+next_term), max(partial, partial+next_term)


@lru_cache(maxsize=1)
def sign_certificate():
    """Exact rational enclosure of O12 from O13; no floating point/quadrature.

    Returns (lower, upper). The inequalities are proved in the note; these
    arithmetic values can be inspected or compared as Fractions independently.
    """
    atan5, atan239 = _atan_bounds(5), _atan_bounds(239)
    pi_lo = 16*atan5[0]-4*atan239[1]
    pi_hi = 16*atan5[1]-4*atan239[0]
    x, terms = F(3, 7), 24
    log_lo = 2*sum((x**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
    log_hi = log_lo+2*x**(2*terms+1)/(F(2*terms+1)*(1-x*x))
    coefficients = _hypergeometric_coefficients(32)
    A = [F(0), *coefficients[1:]]
    Q, power = [F(1)]+[F(0)]*128, [F(1)]
    for k in range(1, 5):
        power = _product(power, A)
        for j, value in enumerate(power):
            Q[j] += (-1)**k*value
    assert Q[:3] == [F(1), F(-1, 18), F(-59, 7128)]
    J = sum((2*value/F(2*j-5) for j, value in enumerate(Q)), F(0))
    a = F(3, 40)
    tail = F(175, 512)*pi_hi-sum(coefficients)
    assert 0 < tail and F(175, 512)*pi_hi-1 < a and pi_hi*pi_hi < 12
    error = a**5/F(5, 2)+tail/F(61, 2)
    assert J-error < J < 0
    lower = log_lo/3+F(35, 128)*pi_hi*(J-error)
    upper = log_hi/3+F(35, 128)*pi_lo*J
    return lower, upper


def matched_coefficient_quadrature():
    """Independent floating evaluation of the convergent O12, NOT a sign proof."""
    coefficients = _hypergeometric_coefficients(18)
    reciprocal = [F(1)]
    for n in range(1, len(coefficients)):
        reciprocal.append(-sum(coefficients[k]*reciprocal[n-k] for k in range(1, n+1)))
    b = np.array([float(value) for value in reciprocal])

    def remainder(x):
        if x < .1:
            return sum(b[j]*x**(j-3.5) for j in range(3, len(b)))
        return (1/hyp2f1(.5, .5, 4.5, x)-1-b[1]*x-b[2]*x*x)/x**3.5

    integral = quad(remainder, 0, 1, points=[.1], epsabs=2e-11, epsrel=2e-11)[0]
    return np.log(2.5)/3+35*np.pi/128*(integral-.4-b[1]*2/3-2*b[2])
