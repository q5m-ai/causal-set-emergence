"""Finite CS diagnostics for the actual SE6 cusp, not remainder certificates.

All partner integrals use the whole rest diamond and its true quadratic
weighted interval volume. No production action, law or coefficient changes.
"""

from functools import lru_cache
import math

import numpy as np
from scipy.integrate import quad
from scipy.special import expit, roots_jacobi

from dimension_kernels import action_constants, interval_coefficient
from null_cartesian_pushforward import coefficients
from null_complete_gluing import _order, _positive

C = float(interval_coefficient(3))
BETA = float(action_constants(3)[1])


def _amplitude(kappa):
    if isinstance(kappa, bool) or not math.isfinite(kappa) or kappa < 0:
        raise ValueError("nonnegative finite diagnostic amplitude required")


@lru_cache(maxsize=16)
def _rule(order):
    _order(order)
    x, w = np.polynomial.legendre.leggauss(order)
    return (x+1)/2, w/2


def _kernel(z):
    return np.polynomial.polynomial.polyval(z, coefficients(3))*np.exp(-z)


def interval_average(target_time, ell, sigma, *, kappa=1.):
    """Actual CS1 mean; arrays are supported for ell and sigma."""
    _amplitude(kappa)
    if not math.isfinite(target_time):
        raise ValueError("finite target time required")
    ell, sigma = np.asarray(ell), np.asarray(sigma)
    if (not np.isfinite(ell).all() or not np.isfinite(sigma).all()
            or np.any(ell < 0) or np.any(sigma < 0)
            or np.any(sigma > ell*ell+1e-13)):
        raise ValueError("causal squared displacement required")
    return 1+kappa*(target_time**2-ell*target_time+5*ell*ell/16-3*sigma/80)


@lru_cache(maxsize=24)
def _diamond_nodes(order, representation):
    """Independent cone and time-ball parametrizations of I(0,(1,0,0))."""
    nodes, weights = _rule(order)
    angle = 2*math.pi*(np.arange(2*order)+.5)/(2*order)
    cosine = np.cos(angle)[None, None, :]
    angular_weight = 2*math.pi/(2*order)
    if representation == "cone":
        b = nodes[:, None, None]
        length = nodes[None, :, None]/(1+b)
        time = np.broadcast_to(1-length, (order, order, 2*order))
        x = np.broadcast_to(length*b*cosine, time.shape)
        sigma = np.broadcast_to(length**2*(1-b*b), time.shape)
        measure = np.broadcast_to(
            b*length**2/(1+b)*weights[:, None, None]*weights[None, :, None]
            *angular_weight, time.shape)
    elif representation == "balls":
        t = np.concatenate((nodes/2, (1+nodes)/2))[:, None, None]
        wt = np.tile(weights/2, 2)[:, None, None]
        radius = np.minimum(t, 1-t)
        r = radius*np.sqrt(nodes[None, :, None])
        time = np.broadcast_to(t, (2*order, order, 2*order))
        x = np.broadcast_to(r*cosine, time.shape)
        sigma = np.broadcast_to((1-t)**2-r*r, time.shape)
        measure = np.broadcast_to(radius**2/2*wt*weights[None, :, None]
                                  *angular_weight, time.shape)
    else:
        raise ValueError("representation must be cone or balls")
    return tuple(np.asarray(a).ravel() for a in (time, x, sigma, measure))


def partner_integral(rho, T, s, *, kappa=1., order=24,
                     representation="cone", cutoff=None, side="all"):
    """rho times the entire physical past-partner integral, with optional split.

    T is q_t-a_t; s is sigma(a,q). The geometry stays SE1 with a_t=-1/2.
    The point belongs to short when side is used by partner_response.
    """
    _positive(rho, T, s)
    _amplitude(kappa)
    if T > 1 or s > T*T or side not in ("all", "short", "long"):
        raise ValueError("requires 0<T<=1, 0<s<=T^2 and an actual side")
    if cutoff is not None:
        _positive(cutoff)
    if side != "all" and cutoff is None:
        raise ValueError("a fixed physical temporal cutoff is required")
    time, x, sigma0, measure = _diamond_nodes(order, representation)
    radius = math.sqrt(max(0., T*T-s))
    ell = T*(1-time)-radius*x
    sigma = s*sigma0
    target_time = T-.5
    density = 1+kappa*(target_time-ell)**2
    phase = rho*C*sigma**1.5*interval_average(target_time, ell, sigma, kappa=kappa)
    weight = np.ones_like(ell)
    if side != "all":
        # One C-infinity transition on the SAME physical ell in both terms.
        z = 2*ell/cutoff-1
        short = np.where(z <= 0, 1., 0.)
        middle = (z > 0) & (z < 1)
        short[middle] = expit(1/z[middle]-1/(1-z[middle]))
        weight = short if side == "short" else 1-short
    return float(rho*s**1.5*np.sum(measure*density*_kernel(phase)*weight))


def partner_response(rho, T, s, **kwargs):
    """Complete point/all-partner response; only short owns the point."""
    point = 0. if kwargs.get("side", "all") == "long" else 1.
    return BETA*(point-partner_integral(rho, T, s, **kwargs))


def angular_measure(T, s):
    """Both exact CS11 cusp transition sectors, not a fitted endpoint mask."""
    if (not math.isfinite(T) or not math.isfinite(s) or not 0 < T < 1
            or not 0 <= s <= T*T):
        raise ValueError("requires 0<T<1 and 0<=s<=T^2")
    if T <= .5 or s >= 2*T-1:
        return 2*math.pi
    radius = math.sqrt(T*T-s)
    lower = np.clip((s-T)/radius, -1., 1.)
    upper = np.clip((2-3*T+s)/radius, -1., 1.)
    return float(2*(math.acos(lower)-math.acos(upper)))


def _target_nodes(order):
    """Retain T=1/2 and s=2T-1 transitions, with square-root edge resolution."""
    nodes, weights = _rule(order)
    for T, wt in zip(nodes/2, weights/2):
        for z, wz in zip(nodes, weights):
            yield T, T*T*z, wt*T*T*wz*math.pi
    # Sine squares resolve both angular aperture endpoints without deleting them.
    angles, aw = math.pi*nodes/2, math.pi*weights/2
    for theta, wtheta in zip(angles, aw):
        T = .5+.5*math.sin(theta)**2
        wt = wtheta*math.sin(theta)*math.cos(theta)
        split = 2*T-1
        for phi, wphi in zip(angles, aw):
            s = split*math.sin(phi)**2
            ws = 2*split*math.sin(phi)*math.cos(phi)*wphi
            yield T, s, wt*ws*angular_measure(T, s)/2
        for z, wz in zip(nodes, weights):
            s = split+(T*T-split)*z
            yield T, s, wt*(T*T-split)*wz*math.pi


def cusp_action(rho, *, kappa=1., order=14, partner_order=None,
                representation="cone", cutoff=None, side="all"):
    """Complete curved CS11 finite action, not a high-density certificate."""
    _positive(rho)
    _amplitude(kappa)
    _order(order)
    if partner_order is None:
        partner_order = 2*order
    _order(partner_order)
    parts = []
    for T, s, measure in _target_nodes(order):
        response = partner_response(rho, T, s, kappa=kappa, order=partner_order,
                                    representation=representation,
                                    cutoff=cutoff, side=side)
        parts.append(measure*(1+kappa*(T-.5)**2)*response)
    return rho**(2/3)*math.fsum(parts)


def null_profile(lam, T, *, kappa=1., order=64):
    """Actual CS6 degenerate-interval profile after signed partner integration."""
    _positive(lam, T)
    _amplitude(kappa)
    _order(order)
    if T > 1:
        raise ValueError("T must be at most one for the SE1 diagnostic")
    # e weight sqrt(e*(1-e)); z weight sqrt(1-z).
    e, we = roots_jacobi(order, .5, .5)
    z, wz = roots_jacobi(order, .5, 0.)
    e, we = (e+1)/2, we/4
    z, wz = (z+1)/2, wz/2**1.5
    qt = T-.5
    f = 1+kappa*(qt-T*e)**2
    H = 1+kappa*(qt*qt-T*qt*e+5*T*T*e*e/16)
    phase = C*lam*H[:, None]*(e[:, None]*z[None, :])**1.5
    return float(BETA*(1-lam*((we*f)@_kernel(phase)@wz)))


def ray_profile(lam, ray_density, *, order=64):
    """CS6 with a vectorized positive smooth ray density f(e), not a polynomial.

    The beta integral is evaluated independently; finite node checks do not
    certify the caller's global positivity or regularity hypotheses.
    """
    _positive(lam)
    _order(order)
    if not callable(ray_density):
        raise ValueError("ray density must be callable")
    e, we = roots_jacobi(order, .5, .5)
    z, wz = roots_jacobi(order, .5, 0.)
    e, we = (e+1)/2, we/4
    z, wz = (z+1)/2, wz/2**1.5
    f = np.broadcast_to(np.asarray(ray_density(e), dtype=float), e.shape)
    samples = np.broadcast_to(np.asarray(ray_density(e[:, None]*e[None, :]),
                                        dtype=float), (order, order))
    endpoints = np.asarray(ray_density(np.array([0., 1.])), dtype=float)
    if any(not np.isfinite(a).all() or np.any(a <= 0)
           for a in (f, samples, endpoints)):
        raise ValueError("positive finite sampled density required")
    H = samples@(8*we/math.pi)
    phase = C*lam*H[:, None]*(e[:, None]*z[None, :])**1.5
    return float(BETA*(1-lam*((we*f)@_kernel(phase)@wz)))


def profile_mass(T, *, kappa=1.):
    """Independently derived CS7 mass, not an integral fitted to null_profile."""
    _positive(T)
    _amplitude(kappa)
    if T > 1:
        raise ValueError("T must be at most one")
    qt = T-.5
    A = 1+kappa*qt*qt
    return 2*A**(-2/3)*(1+2*kappa*T*qt/(3*A))


def profile_tail(T, *, kappa=1., order=48):
    """CS8a's independent whole-ray tail coefficient, with exact subtraction."""
    _positive(T)
    _amplitude(kappa)
    _order(order)
    if T > 1:
        raise ValueError("T must be at most one")
    qt = T-.5
    value, first, second = 1+kappa*qt*qt, -2*kappa*T*qt, kappa*T*T
    e, weights = roots_jacobi(order, .5, -.5)
    e, weights = (e+1)/2, weights/2
    H = value+first*e/2+5*second*e*e/16
    numerator = (3*value*second/8-first*first/4
                 -5*first*second*e/16-25*second*second*e*e/256)
    integral = float(weights@(numerator/(value*H*H)))
    return BETA*integral/(12*C*C)


def _lens_area(r, R, distance=.5):
    if distance <= abs(r-R):
        return math.pi*min(r, R)**2
    if distance >= r+R:
        return 0.
    x = np.clip((distance**2+r*r-R*R)/(2*distance*r), -1., 1.)
    y = np.clip((distance**2+R*R-r*r)/(2*distance*R), -1., 1.)
    root = (-distance+r+R)*(distance+r-R)*(distance-r+R)*(distance+r+R)
    return r*r*math.acos(x)+R*R*math.acos(y)-math.sqrt(max(0., root))/2


def slice_area(t):
    """Independent spatial area of the actual SE1 endpoint domain."""
    if not math.isfinite(t) or not -.5 <= t <= .5:
        raise ValueError("requires -1/2 <= t <= 1/2")
    return math.pi*(t+.5)**2 if t <= 0 else _lens_area(t+.5, 1-t)-math.pi*t*t


def geometric_target(*, kappa=1.):
    """Independent bulk and actual conformal outer screen; no action input."""
    _amplitude(kappa)
    def curvature(t):
        return (12*kappa-8*kappa*kappa*t*t)/(9*(1+kappa*t*t)**(5/3))
    bulk = math.fsum(quad(lambda t: slice_area(t)*curvature(t), lo, hi,
                         epsabs=2e-11)[0] for lo, hi in ((-.5, 0.), (0., .5)))
    def screen(phi):
        radius = 2/(3+math.cos(phi))
        return radius*(1+kappa*(radius-.5)**2)**(1/3)
    area = quad(screen, 0., 2*math.pi, epsabs=2e-11)[0]
    return bulk, area
