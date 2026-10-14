"""Actual dimensional cone-ending responses, with diagnostic quadratures.

Written proof: notes/null-cone-dimensions.md. The finite numerical routines
are not certified for arbitrarily large density or dimension. Canonical
coefficients are imported, never fitted or redefined.
"""

from functools import lru_cache
import math

import numpy as np
from scipy.optimize import brentq
from scipy.special import roots_jacobi

from dimension_kernels import action_constants, factor_count, interval_coefficient, kernel_polynomial, sphere_area
from two_tip_lens import rule


@lru_cache(maxsize=32)
def constants(d):
    # Existing helper rejects bools and nonphysical dimensions.
    a, beta = action_constants(d)
    return float(a), float(beta), float(interval_coefficient(d))


def response(d, z, order=64):
    """Complete source response B_d(z), NOT merely exp(-z) above dimension four."""
    a, beta, _ = constants(d)
    z = np.asarray(z, dtype=float)
    if not np.isfinite(z).all() or np.any(z < 0):
        raise ValueError("phase must be nonnegative and finite")
    rule(order)  # Validate the shared numerical order convention.
    if d == 2:
        return 2*(1-z)*np.exp(-z)
    if d in (3, 4):
        return a*np.exp(-z)
    q, m = d/2, factor_count(d)
    ell = d-1-m
    nodes, weights = roots_jacobi(order, ell-1, m-q)
    t = (nodes+1)/2
    weights = weights / 2**(ell+m-q)
    coefficient = beta*math.gamma(d)/(math.factorial(m)*math.gamma(ell))
    values = np.exp(-z[..., None]*t**q)
    return coefficient*(values @ weights)


def interval_response(d, z, order=32):
    """Independent signed integration in the full unit proper-time diamond.

    Relative to the source p=0, 0<t<1, 0<r<min(t,1-t). This includes ALL
    partners and directly integrates the original polynomial-exponential kernel.
    """
    a, beta, c = constants(d)
    if not math.isfinite(z) or z < 0:
        raise ValueError("phase must be nonnegative and finite")
    nodes, weights = rule(order)
    coefficients = np.array([float(x) for x in reversed(kernel_polynomial(d).as_poly().all_coeffs())])
    integral = 0.0
    for lo, hi in ((0.0, 0.5), (0.5, 1.0)):
        t = (lo+(hi-lo)*nodes)[:, None]
        rmax = np.minimum(t, 1-t)
        r = rmax*nodes[None, :]
        phase = z*(t*t-r*r)**(d/2)
        kernel = np.polynomial.polynomial.polyval(phase, coefficients)*np.exp(-phase)
        measure = (hi-lo)*rmax*r**(d-2)*weights[:, None]*weights[None, :]
        integral += float(np.sum(measure*kernel))
    return a-beta*(z/c)*float(sphere_area(d))*integral


def angular_rule(d, order):
    constants(d)
    rule(order)
    if d == 2:
        return np.array([-1.0, 1.0]), np.ones(2)
    exponent = (d-4)/2
    nodes, weights = roots_jacobi(order, exponent, exponent)
    transverse_sphere = 2*math.pi**((d-2)/2)/math.gamma((d-2)/2)
    return nodes, transverse_sphere*weights


def height(kind, r, mu):
    if kind == "diamond":
        return 1-r
    if kind == "round":
        return np.ones_like(r)
    if kind == "sine":
        return 1+0.2*np.sin(r*mu)
    raise ValueError("unknown geometric diagnostic member")


def radius(kind, mu):
    return brentq(lambda r: r-float(height(kind, r, mu)), 0, 2, xtol=5e-15)


def joint_area(d, kind="sine", order=32):
    """Independent induced screen area; S^0 is exactly two counting atoms."""
    mus, angular = angular_rule(d, order)
    return float(sum(w*radius(kind, mu)**(d-2) for mu, w in zip(mus, angular)))


def source_action(d, rho, kind="sine", order=24):
    """Full source integral in ordinary (t,r,omega) coordinates, not a small-s jet.

    All source-to-tip partners are incorporated by response(). Lower and upper
    time endpoints remain r and H(r*omega); geometry is fixed as rho varies.
    """
    _, _, c = constants(d)
    if not math.isfinite(rho) or rho <= 0:
        raise ValueError("density must be positive and finite")
    nodes, weights = rule(order)
    mus, angular = angular_rule(d, order)
    total = 0.0
    for mu, wm in zip(mus, angular):
        end = radius(kind, mu)
        r = (end*nodes)[:, None]
        top = height(kind, r, mu)
        t = r+(top-r)*nodes[None, :]
        z = c*rho*np.maximum(t*t-r*r, 0)**(d/2)
        measure = end*(top-r)*r**(d-2)*weights[:, None]*weights[None, :]
        total += wm*np.sum(measure*response(d, z))
    return float(rho**(2/d)*total)
