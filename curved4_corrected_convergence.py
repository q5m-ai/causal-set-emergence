"""Finite diagnostics for the corrected curved-4D theorem.

Scope: g = Omega(t,z)^2 (dt^2 - h_S2 - dz^2), on the width-4,
circumference-20 slab. Density callbacks return Omega^4, not Omega.
The integrals count physical interval points; no geodesic volumes are summed.
Floating cubature/root finding is NOT a certificate or a full-action solver.
See notes/curved4-corrected-convergence.md for the written estimates.
"""

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache

import numpy as np
from scipy.optimize import brentq

from general_metric_gate import gauss_rule
from sphere_circle_focusing import area_ratio

DURATION = 4.0
CIRCUMFERENCE = 20.0
SPHERE_PAIR_FACTOR = 8 * np.pi**2


def _density_value(density, t, z):
    value = np.asarray(density(t, z))
    if np.any(~np.isfinite(value)) or np.any(value <= 0):
        raise ValueError("density must be finite and strictly positive")
    return value


@lru_cache(maxsize=6)
def diamond_rule(order=12):
    """All four coordinates of D0, including the previously unused circle one."""
    if not isinstance(order, int) or order < 2:
        raise ValueError("quadrature order must be an integer at least two")
    n, w = gauss_rule(order)
    arrays = [[] for _ in range(5)]
    for sign in (-1, 1):
        a = sign * n[:, None, None, None] / 2
        radius = 0.5 - np.abs(a)
        b1 = radius * (2*n[None, :, None, None]-1)
        height = np.sqrt(np.maximum(0, radius**2-b1**2))
        eta = np.pi * (n[None, None, :, None]-0.5)
        b2 = height * np.sin(eta)
        b3 = height * np.cos(eta) * (2*n[None, None, None, :]-1)
        measure = (2*np.pi*radius*height**2*np.cos(eta)**2
                   * w[:, None, None, None] * w[None, :, None, None]
                   * w[None, None, :, None] * w[None, None, None, :])
        for dest, value in zip(arrays, np.broadcast_arrays(a, b1, b2, b3, measure)):
            dest.append(value.ravel())
    result = tuple(np.concatenate(parts) for parts in arrays)
    for value in result:
        value.flags.writeable = False
    return result


def regular_volume_factor(t_source, z_source, theta, b, q, density, order=12):
    """Actual V/q^2, including q=0, on the regular two-distance domain.

    q = tau^2-theta^2-b^2. The full spatial boost avoids the spurious
    singularity of the time/circle boost at theta=q=0 with long b.
    t_source is the actual source time, not the time-fraction parameter.
    """
    if not all(np.isfinite(v) for v in (t_source, z_source, theta, b, q)):
        raise ValueError("parameters must be finite")
    r = np.hypot(theta, b)
    if not 0 <= theta < np.pi or q < 0 or r == 0:
        raise ValueError("requires 0<=theta<pi, q>=0 and nonzero spatial length")
    tau = np.sqrt(r*r+q)
    u = np.sqrt(theta*theta+q)
    if tau > DURATION+1e-12 or u >= 2*np.pi-theta:
        raise ValueError("outside the regular-side slab domain")
    a, b1, b2, b3, weights = diamond_rule(order)
    ell = 0.5+a
    root = np.sqrt(q)
    x = theta*ell + tau*theta/r*b1 - b/r*root*b3
    y = root*b2
    z = z_source + b*ell + tau*b/r*b1 + theta/r*root*b3
    t = t_source + tau*ell + r*b1
    rs = np.hypot(x, y)
    ss = np.hypot(x-theta, y)
    return float(np.sum(weights * area_ratio(theta, rs, ss)
                        * _density_value(density, t, z)))


def _weighted_circle_section(t_source, z_source, tau, b, r, ss, density,
                             circle_order, time_order):
    """Integrate the actual clock fibres over their resolved ellipse support."""
    r, ss = np.broadcast_arrays(r, ss)
    u2 = tau*tau-b*b
    active = r+ss < np.sqrt(u2)
    discriminant = np.maximum(0, (u2-(r+ss)**2)*(u2-(r-ss)**2))
    half = np.where(active, tau/(2*u2)*np.sqrt(discriminant), 0)
    center = b*(u2+r*r-ss*ss)/(2*u2)
    n, w = gauss_rule(circle_order)
    tn, tw = gauss_rule(time_order)
    z = center[..., None]+half[..., None]*(2*n-1)
    lower = np.hypot(r[..., None], z)
    upper = tau-np.hypot(ss[..., None], z-b)
    gap = np.maximum(0, upper-lower)
    t = t_source+lower[..., None]+gap[..., None]*tn
    averaged = np.sum(tw*_density_value(density, t, z_source+z[..., None]), axis=-1)
    return 2*half*np.sum(w*gap*averaged, axis=-1)


def weighted_clock_volume(t_source, z_source, tau, theta, b, density,
                          order=40, circle_order=20, time_order=12):
    """Independent physical polar/clock cubature, including both transitions.

    Unlike regular_volume_factor this representation also covers theta=pi
    and u>=2*pi-theta. Sphere points and clock fibres are integrated once.
    """
    if not all(np.isfinite(v) for v in (t_source, z_source, tau, theta, b)):
        raise ValueError("parameters must be finite")
    if not abs(b) < tau <= DURATION or not 0 <= theta <= np.pi:
        raise ValueError("requires |b|<tau<=4 and 0<=theta<=pi")
    u = np.sqrt(tau*tau-b*b)
    if u <= theta:
        return 0.0
    n, w = gauss_rule(order)
    if theta in (0, np.pi):
        top = np.pi if theta == np.pi else min(np.pi, u/2)
        r = top*n
        ss = np.pi-r if theta == np.pi else r
        section = _weighted_circle_section(t_source, z_source, tau, b, r, ss,
                                            density, circle_order, time_order)
        return float(2*np.pi*top*np.sum(w*np.sin(r)*section))
    edges = sorted(set((0.0, np.pi, min(np.pi, (u-theta)/2),
                        min(np.pi, (u+theta)/2))))
    result = 0.0
    for lo, hi in zip(edges, edges[1:]):
        r = (lo+(hi-lo)*n)[:, None]
        allowed = u-r
        threshold = ((np.cos(np.clip(allowed, 0, np.pi))-np.cos(r)*np.cos(theta))
                     / (np.sin(r)*np.sin(theta)))
        phi_max = np.where(allowed >= np.pi, np.pi, np.where(
            allowed <= 0, 0, np.arccos(np.clip(threshold, -1, 1))))
        phi = phi_max*n[None, :]
        ss = np.arccos(np.clip(np.cos(r)*np.cos(theta)
                              + np.sin(r)*np.sin(theta)*np.cos(phi), -1, 1))
        section = _weighted_circle_section(t_source, z_source, tau, b, r, ss,
                                            density, circle_order, time_order)
        result += 2*(hi-lo)*np.sum(w[:, None]*w[None, :]*np.sin(r)*phi_max*section)
    return float(result)


@dataclass(frozen=True)
class ClosingPair:
    u: float
    b: float
    tau: float
    source_time: float
    target_time: float
    amplitude: float  # excludes 8*pi^2*sin(theta)


def closing_pair(theta, e, v, xi, z_source, density):
    """Straighten the ACTUAL closing b fibres before a phase expansion."""
    u = theta+e
    if not all(np.isfinite(x) for x in (theta, e, v, xi, z_source)):
        raise ValueError("parameters must be finite")
    if not 0 <= theta <= np.pi or e < 0 or not 0 < u < DURATION:
        raise ValueError("requires 0<=theta<=pi, e>=0 and 0<theta+e<4")
    if not -1 <= v <= 1 or not 0 <= xi <= 1:
        raise ValueError("requires |v|<=1 and 0<=xi<=1")
    width = np.sqrt(DURATION**2-u*u)
    b = width*v
    tau = np.hypot(u, b)
    gap = width**2*(1-v*v)/(DURATION+tau)
    source = -DURATION/2+xi*gap
    target = source+tau
    amplitude = (gap*u*width/tau
                 * _density_value(density, source, z_source)
                 * _density_value(density, target, z_source+b))
    return ClosingPair(u, b, tau, source, target, float(amplitude))


def cut_volume_factor(a, e, v, xi, z_source, density, order=12):
    """The actual H=V/e^2 on the regular cut wedge, with its moving b/time."""
    if not 0 < a < np.pi or not 0 <= e < 2*a:
        raise ValueError("requires 0<a<pi and 0<=e<2*a")
    theta = np.pi-a
    pair = closing_pair(theta, e, v, xi, z_source, density)
    q = e*(2*theta+e)
    return (2*theta+e)**2 * regular_volume_factor(
        pair.source_time, z_source, theta, pair.b, q, density, order)


def time_contact_radius(duration, m, xi, z_source, w, density, order=10):
    """Small-phase R_duration; both time roots use the actual weighted volume.

    This bounded diagnostic refuses a phase outside its regular collar.
    It is not a claim of a global inverse through a caustic.
    """
    if not all(np.isfinite(v) for v in (duration, m, xi, z_source, w)):
        raise ValueError("parameters must be finite")
    if not 0 < duration <= 4 or not -1 <= m <= 1 or not 0 <= xi <= 1 or w < 0:
        raise ValueError("invalid time-root parameters")
    theta0 = duration*np.sqrt(1-m*m)
    if theta0 >= np.pi:
        raise ValueError("time root is outside the regular sphere chart")
    source = -2+xi*(4-duration)

    def phase(q):
        r = np.sqrt(duration**2-q)
        h = regular_volume_factor(source, z_source, r*np.sqrt(1-m*m), r*m,
                                  q, density, order)
        return q*np.sqrt(h)

    if w == 0:
        return duration
    cap = min(duration**2/2, 2*np.pi*(np.pi-theta0))
    hi = min(cap, 2*w/np.sqrt(regular_volume_factor(
        source, z_source, theta0, duration*m, 0, density, order)))
    while phase(hi) < w and hi < cap:
        hi = min(2*hi, cap)
    if phase(hi) < w:
        raise ValueError("phase exceeds the diagnostic regular collar")
    q = brentq(lambda q: phase(q)-w, 0, hi, xtol=1e-300, rtol=2e-14)
    return float(np.sqrt(duration**2-q))


def primitive_coefficients(h0, h1, h2, j0, j1, j2):
    """Cubic primitive coefficients from ACTUAL V=e^2 H and pair-density jets.

    h1,h2,j1,j2 are derivatives, not Taylor coefficients. No fitting occurs here.
    """
    if h0 <= 0 or not all(np.isfinite(v) for v in (h0, h1, h2, j0, j1, j2)):
        raise ValueError("requires finite jets and H(0)>0")
    a1 = h0**-0.5
    a2 = -h1/(2*h0**2)
    a3 = 5*h1*h1/(8*h0**3.5)-h2/(4*h0**2.5)
    return np.array((j0*a1, j0*a2+j1*a1*a1/2,
                     j0*a3+j1*a1*a2+j2*a1**3/6))


def critical_exponents(nu, beta, sigma):
    """Exact arithmetic for the sufficient lens-scaling lemma, not its premises."""
    nu, beta, sigma = map(Fraction, (nu, beta, sigma))
    lam = beta-sigma/2
    if beta <= 0 or lam <= 0 or beta >= 3*lam:
        raise ValueError("lemma requires 0<beta<3*(beta-sigma/2)")
    exponent = nu+beta-3*lam
    return {"lambda": lam, "cubic_majorant": exponent,
            "transition_w_power": (nu+beta+1)/lam,
            "transition_volume_power": (nu+beta+1)/(2*lam),
            "summable": exponent > -1}


def independent_target(omega, omega_tt, omega_zz, order=32):
    """Independent half-curvature integral; the joint is empty.

    R_g = 2/Omega^2 + 6*(Omega_tt-Omega_zz)/Omega^3 in the repo convention.
    """
    n, w = gauss_rule(order)
    t, z = (-2+4*n)[:, None], (20*n)[None, :]
    om = _density_value(omega, t, z)
    integrand = om*om+3*om*(omega_tt(t, z)-omega_zz(t, z))
    return float(4*np.pi*80*np.sum(w[:, None]*w[None, :]*integrand))


def spacetime_mass(density, order=32):
    n, w = gauss_rule(order)
    t, z = (-2+4*n)[:, None], (20*n)[None, :]
    return float(4*np.pi*80*np.sum(w[:, None]*w[None, :]
                                 * _density_value(density, t, z)))
