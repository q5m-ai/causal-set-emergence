"""Finite diagnostics for IU's two intrinsic physical-union approaches.

No production action/law is replaced. The projective cubature integrates the
actual O5 sphere Jacobian and time primitive, not the limiting profile. The
logarithmic-ramp identity works on finite quadrature measures; neither those
checks nor fitted slopes certify the written critical remainder.
"""
from fractions import Fraction
from functools import lru_cache
import math

import numpy as np
from scipy.integrate import quad
from scipy.special import gammainc, hyp2f1

from dimension_kernels import action_constants, factor_count
from null_complete_gluing import _order, _positive
from null_singular_ends import closing_weight, matched_profile_parts
from seven_dimensional_focusing import (
    ANTIPODAL_COEFFICIENT as D, OPENING_COEFFICIENT,
)


@lru_cache(maxsize=12)
def _rule(order):
    _order(order)
    x, w = np.polynomial.legendre.leggauss(order)
    return (x+1)/2, w/2


def _fraction(value):
    if not math.isfinite(value) or not 0 <= value <= 1:
        raise ValueError("fraction must lie in [0,1]")


def projective_profile(fraction, *, divided=False):
    """Actual O6 tangent profile Phi(y), or Phi(y)/y^(7/2), at both ends."""
    _fraction(fraction)
    if not isinstance(divided, bool):
        raise ValueError("divided must be boolean")
    y = fraction
    if y <= 2/3:
        h = D*OPENING_COEFFICIENT/math.sqrt(1-y)*hyp2f1(
            .5, .5, 4.5, y/(2*(1-y)))
    else:
        h = D*((2*y-1)**3+1.5*(2*y-1)*(1-y)**2)/y**3.5
    return float(h if divided else y**3.5*h)


def resolved_interval(radius, fraction, *, order=36, divided=False):
    """Entire physical W(pi+r(2y-1), pi-r(1-y)), or W/(r^3 y^(7/2)).

    The a=0 meridian limit is retained. For y=0 the divided value is the
    actual regular-edge limit, obtained from the same Jacobian, not Phi.
    """
    _positive(radius)
    _fraction(fraction)
    _order(order)
    if radius >= .5 or not isinstance(divided, bool):
        raise ValueError("requires 0 < radius < 1/2 and boolean divided")
    n, w = _rule(order)
    r, y = radius, fraction
    a = r*(1-y)
    eta = math.pi*(n-.5)
    sine, cosine = np.sin(eta), np.cos(eta)
    B = np.sqrt(cosine*cosine+math.sin(a/2)**2*sine*sine)
    Y = 2*np.arctan2(math.cos(a/2)*sine, B)
    if y == 0:
        theta = math.pi-r
        measure = 2*(B-math.sin(a/2)**2/B)/math.sqrt(np.sinc(a/math.pi))
        psi = math.pi**2/(24*theta**2)*((theta-Y)*(theta+Y))**2
        h = math.sqrt(2)*16/35*math.pi*float(w@(measure*psi))
        return h if divided else 0.
    top = math.pi if y >= 2/3 else 2*math.asin(math.sqrt(y/(2*(1-y))))
    phi = top*n
    t = 2*np.sin(phi/2)**2
    q = np.maximum(0., 1-(1-y)/y*t)
    x = math.pi+a*(t-1)
    gap = r*y*q
    denom = np.sqrt(np.sinc(a*t/(2*math.pi))*np.sinc(a*(2-t)/(2*math.pi)))
    measure = 2*(B[None, :]-np.sin(a*(1-t[:, None])/2)**2/B[None, :])/denom[:, None]
    u = x[:, None, None]+gap[:, None, None]*n[None, None, :]
    difference = (u-Y[None, :, None])*(u+Y[None, :, None])
    integrand = (n[None, None, :]**2*(2*x[:, None, None]
                 + gap[:, None, None]*n[None, None, :])**2*difference**2/u**4)
    psi = math.pi**2/32*(integrand@w)
    h = top/math.sqrt(y)*math.pi*float((w*q**3)@(measure*psi)@w)
    return h if divided else r**3*y**3.5*h


def physical_closing_weight(U, T, *, order=32):
    """IF2 weight extended by its physical zero above the closing cap."""
    _positive(U, T)
    _order(order)
    return 0. if U >= T else closing_weight(U, T, order=order)


def focal_growth(T, *, circumference=20., order=32):
    """IU full-family growth coefficient; O13, not this float, certifies sign."""
    _positive(T, circumference)
    _order(order)
    if T >= circumference/2:
        raise ValueError("requires the original whole-flat-lift margin T < L/2")
    if T <= math.pi:
        return 0.
    VY = 4*math.pi*circumference**3
    I = math.fsum(matched_profile_parts())
    beta = float(action_constants(7)[1])
    return 5*beta/128*(2*math.pi*VY*closing_weight(math.pi, T, order=order)/(3*D))*I


@lru_cache(maxsize=None)
def filter_coefficients(d):
    """Exact coefficients of H product_j [I-(1+2j/d)H]."""
    m = factor_count(d)
    coefficients = [Fraction(1)]
    for j in range(1, m+1):
        b = 1+Fraction(2*j, d)
        result = [Fraction(0)]*(len(coefficients)+1)
        for k, value in enumerate(coefficients):
            result[k] += value
            result[k+1] -= b*value
        coefficients = result
    return tuple(coefficients)


def filter_constant(d):
    m = factor_count(d)
    return Fraction((-1)**m, 1)/math.prod(Fraction(2*j, d) for j in range(1, m+1))


def filtered_power(d, exponent):
    """Eigenvalue of the geometric log-ramp filter on v^exponent."""
    m = factor_count(d)
    if not math.isfinite(exponent) or exponent <= -1:
        raise ValueError("power must be finite and greater than -1")
    return math.prod(exponent-2*j/d for j in range(1, m+1))/(exponent+1)**(m+1)


def geometric_filter(d, ratio):
    """Explicit bounded Phi_d(V/v); zero above one, with its true zero limit."""
    coefficients = filter_coefficients(d)
    x = np.asarray(ratio, dtype=float)
    if np.any(~np.isfinite(x)) or np.any(x < 0):
        raise ValueError("volume ratios must be finite and nonnegative")
    out = np.zeros_like(x)
    out[x == 0] = float(sum(coefficients))
    active = (x > 0) & (x < 1)
    log = -np.log(x[active])
    out[active] = sum(float(c)*gammainc(k+1, log) for k, c in enumerate(coefficients))
    return float(out) if out.ndim == 0 else out


@lru_cache(maxsize=None)
def _laplace_coefficients(d):
    coefficients = np.array([1.])
    for _ in range(factor_count(d)+1):
        derivative = np.polynomial.polynomial.polyder(coefficients)
        difference = np.polynomial.polynomial.polysub(coefficients, derivative)
        coefficients = np.r_[0., difference]
    return coefficients


def laplace_weight(d, z):
    """(-z*d/dz)^(m+1) exp(-z); all signed moments are retained."""
    x = np.asarray(z, dtype=float)
    if np.any(~np.isfinite(x)) or np.any(x < 0):
        raise ValueError("Laplace arguments must be finite and nonnegative")
    value = np.polynomial.polynomial.polyval(x, _laplace_coefficients(d))*np.exp(-x)
    return float(value) if value.ndim == 0 else value


def filtered_pair(d, rho, volumes, weights):
    """Direct IU identity on a finite signed quadrature measure, not a limit."""
    factor_count(d)
    _positive(rho)
    v, w = np.asarray(volumes, dtype=float), np.asarray(weights, dtype=float)
    if (v.ndim != 1 or w.shape != v.shape or len(v) == 0
            or np.any(~np.isfinite(v)) or np.any(v <= 0) or np.any(~np.isfinite(w))):
        raise ValueError("matching finite 1D weights and positive volumes required")
    edges = sorted(set([0., *(rho*v).tolist()]))
    def integrand(z):
        if z == 0:
            return 0.
        return laplace_weight(d, z)*float(w@geometric_filter(d, rho*v/z))
    value = math.fsum(quad(integrand, lo, hi, epsabs=2e-11, epsrel=2e-11)[0]
                     for lo, hi in zip(edges, edges[1:]+[np.inf]))
    return float(filter_constant(d))*value


def point_primitive(d, v, *, mass=1.):
    """Exact algebraic point subtraction: v (odd), v log(v) (even).

    This does not assert that geometry supplies this sublevel coefficient.
    """
    m = factor_count(d)
    x = np.asarray(v, dtype=float)
    if np.any(~np.isfinite(x)) or np.any(x < 0) or not math.isfinite(mass):
        raise ValueError("nonnegative finite phase and finite mass required")
    a, beta = map(float, action_constants(d))
    if d % 2:
        moment = math.prod(1-d/(2*j) for j in range(1, m+1))
        value = a/(beta*moment)*mass*x
    else:
        n = d//2
        moment = -math.prod(1-d/(2*j) for j in range(1, m+1) if j != n)
        safe = np.where(x > 0, x, 1.)
        value = a/(beta*moment)*mass*x*np.log(safe)
    return float(value) if value.ndim == 0 else value
