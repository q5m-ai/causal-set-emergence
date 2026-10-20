"""Finite diagnostics for NX's actual normal triangle and signed primitive.

These routines do not certify the Fourier remainder, singular-end gluing, or
any complete-action asymptotic. Canonical coefficients are imported unchanged.
"""

from functools import lru_cache
import math

import numpy as np
from scipy.optimize import brentq
from scipy.special import gamma, gammainc, gammaincc

from dimension_kernels import factor_count, interval_coefficient, kernel_polynomial


@lru_cache(maxsize=32)
def coefficients(d):
    return tuple(float(x) for x in reversed(kernel_polynomial(d).as_poly().all_coeffs()))


def kernel(d, z):
    return float(np.polynomial.polynomial.polyval(z, coefficients(d))*math.exp(-z))


def signed_ramp(d, value):
    """G_d(s): both equivalent signed integrals, with stable upper tails."""
    factor_count(d)
    if not math.isfinite(value):
        raise ValueError("finite phase argument required")
    if value <= 0:
        return 0.0
    q = d/2
    z = value**q
    terms = []
    for k, coefficient in enumerate(coefficients(d)):
        a, b = k+1/q, k+2/q
        if value <= 1:
            term = value*gamma(a)*gammainc(a, z)-gamma(b)*gammainc(b, z)
        else:
            term = gamma(b)*gammaincc(b, z)-value*gamma(a)*gammaincc(a, z)
        terms.append(coefficient*term/q)
    return math.fsum(terms)


def time_density_average(d, past_time, future_time, sigma):
    """Actual diamond average of A(t)=1+t^2, not a phase fitted at closing."""
    factor_count(d)
    ell = future_time-past_time
    return (1+future_time**2-ell*future_time
            +(d+2)*ell**2/(4*(d+1))-d*sigma/(4*(d+1)*(d+2)))


def cone_gap(a, b, past_y, future_y):
    """Exact boundary squared displacement for the two origin-cone germs."""
    p, q = np.asarray(past_y, dtype=float), np.asarray(future_y, dtype=float)
    if (not math.isfinite(a) or not math.isfinite(b) or a <= 0 or b <= 0
            or p.ndim != 1 or p.shape != q.shape
            or not np.isfinite(p).all() or not np.isfinite(q).all()):
        raise ValueError("positive endpoints and equal finite transverse vectors required")
    return float((b*p+a*q)@(b*p+a*q)/(a*b))


def triangle_pair(d, rho, a, b, past_y, future_y, *, curved=True,
                  representation="normals", cutoff=None, side="all", order=36):
    """The complete localized normal triangle, including both endpoint measures.

    Fronts are the actual past/future cones of the origin in a common Cartesian
    collar. Curved uses the genuine conformal A(t)=1+t^2 interval; flat uses A=1.
    A temporal split is in ell, never in v. This is NOT a complete-region action.
    """
    factor_count(d)
    if (not math.isfinite(rho) or rho <= 0 or isinstance(order, bool)
            or not isinstance(order, int) or order < 4
            or representation not in ("normals", "phase")
            or side not in ("all", "short", "long")
            or (side != "all" and (cutoff is None or not math.isfinite(cutoff) or cutoff <= 0))):
        raise ValueError("invalid diagnostic integration parameters")
    B = cone_gap(a, b, past_y, future_y)
    yp, yq = np.asarray(past_y, dtype=float), np.asarray(future_y, dtype=float)
    if len(yp) != d-2:
        raise ValueError("transverse dimension must be d-2")
    v, f, g = a+b, -float(yp@yp)/a, float(yq@yq)/b
    h = B/v
    if h == 0:
        return 0.0
    lo, hi = 0.0, h
    if side != "all":
        closing = min(h, max(0.0, v+g-f-2*cutoff))
        if side == "short":
            lo = closing
        else:
            hi = closing
    if hi <= lo:
        return 0.0
    nodes, weights = np.polynomial.legendre.leggauss(order)
    nodes, weights = (nodes+1)/2, weights/2
    c = float(interval_coefficient(d))
    C, D = (d+2)/(4*(d+1)), d/(4*(d+1)*(d+2))
    result = 0.0
    for alpha, wa in zip(nodes, weights):
        def data(r):
            pt, qt = (-a+f+alpha*r)/2, (b+g-(1-alpha)*r)/2
            ell, sigma = qt-pt, max(0.0, B-v*r)
            if curved:
                average = time_density_average(d, pt, qt, sigma)
                derivative = (-(1-alpha)/2*(2*qt-ell)+qt/2-C*ell+D*v)
                endpoints = (1+pt*pt)*(1+qt*qt)
            else:
                average, derivative, endpoints = 1.0, 0.0, 1.0
            phase = sigma*average**(2/d)
            phase_prime = (-v*average**(2/d)
                           +sigma*(2/d)*average**(2/d-1)*derivative)
            return phase, phase_prime, endpoints

        if representation == "normals":
            value = 0.0
            for node, weight in zip(nodes, weights):
                r = lo+(hi-lo)*node
                phase, _, endpoints = data(r)
                value += weight*r*endpoints*kernel(d, c*rho*phase**(d/2))
            value *= hi-lo
        else:
            if any(data(r)[1] >= 0 for r in np.linspace(lo, hi, 9)):
                raise ValueError("outside the diagnostic monotone closing collar")
            bottom, top = data(hi)[0], data(lo)[0]
            value = 0.0
            for node, weight in zip(nodes, weights):
                phase = bottom+(top-bottom)*node
                r = brentq(lambda rr: data(rr)[0]-phase, lo, hi, xtol=1e-14)
                _, prime, endpoints = data(r)
                value += weight*r*endpoints*kernel(d, c*rho*phase**(d/2))/(-prime)
            value *= top-bottom
        result += wa*value/4
    return float(result)


def plane_graph(v, y, slope, intercept=0.0):
    """A genuine null hyperplane u=b.y-|b|^2*v/4+c."""
    y, slope = np.asarray(y, dtype=float), np.asarray(slope, dtype=float)
    if y.shape != slope.shape or y.ndim != 1:
        raise ValueError("matching transverse vectors required")
    return float(slope@y-float(slope@slope)*v/4+intercept)
