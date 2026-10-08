"""Finite diagnostics for notes/full-partner-globalization.md (#151).

Not production action definitions or a general geometric producer. The torus
integrals below use the proved unique-lift regime, ordinary sphere measure and
both endpoint volumes. Arbitrary manifold intervals are NOT replaced by them.
"""

from functools import lru_cache

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.special import gamma, jv

from dimension_kernels import (
    Z, action_constants, interval_coefficient, kernel_polynomial, sphere_area,
    transverse_moment,
)


@lru_cache(maxsize=None, typed=True)
def _kernel(d):
    # Reuse the dimension-indexed recurrence, not four-dimensional coefficients.
    polynomial = s.lambdify(Z, kernel_polynomial(d), "numpy")
    return lambda z: polynomial(z) * np.exp(-z)


@lru_cache(maxsize=None, typed=True)
def _dimension_data(d):
    # Preserve the original strict dimension validation before caching.
    return float(interval_coefficient(d)), float(sphere_area(d))


def _geometry(d, length, duration, cutoff):
    c, area = _dimension_data(d)
    if not np.isfinite(length) or not np.isfinite(duration):
        raise ValueError("finite length and duration required")
    if not 0 < duration < length / 2:
        raise ValueError("requires the unique-lift regime 0 < T < L/2")
    if not np.isfinite(cutoff) or cutoff <= 0:
        raise ValueError("fixed positive temporal cutoff required")
    return c, area * length ** (d - 1)


def angular_cosine(d, z):
    """Mean of cos(z*omega_1) for ordinary S^(d-2), including S^0."""
    _dimension_data(d)  # Validate, including bool/noninteger rejection.
    z = abs(float(z))
    if d == 2:
        return np.cos(z)
    if z == 0:
        return 1.0
    order = (d - 3) / 2
    return gamma(order + 1) * (2 / z) ** order * jv(order, z)


def periodic_correlation(d, length, duration, tau, r,
                         source_time=0., target_time=0.,
                         source_cos=0., target_cos=0.):
    """Actual normalized time/source/angular average of two endpoint fields.

    chi(t,p)=1+source_time*t+source_cos*cos(2*pi*p_1/L), and similarly
    phi(t+tau,p+r*omega) with target coefficients. Both fields can change
    sign. No endpoint is frozen at the other endpoint.
    """
    if not np.isfinite(length) or length <= 0:
        raise ValueError("positive finite torus length required")
    angular = angular_cosine(d, 2 * np.pi * r / length)
    return (
        1 + (target_time - source_time) * tau / 2
        + source_time * target_time * ((duration - tau)**2 / 12 - tau**2 / 4)
        + source_cos * target_cos * angular / 2
    )


def torus_long_density(d, length, duration, cutoff, w,
                       correlation=lambda tau, r: 1.):
    """Actual G8 density for a supplied normalized endpoint correlation.

    correlation is the time/source/angular mean of chi(x)*phi(y), not a
    replacement interval phase. Unit fields and periodic_correlation are
    derived instances. w=tau^2-r^2; temporal equality belongs to long.
    The radial form of the inner integral resolves the integrable d=2 edge.
    """
    _, measure = _geometry(d, length, duration, cutoff)
    if not np.isfinite(w) or w < 0:
        raise ValueError("nonnegative finite phase required")
    if cutoff >= duration or w >= duration**2:
        return 0.
    lo = np.sqrt(max(0., cutoff**2 - w))
    hi = np.sqrt(duration**2 - w)

    def integrand(r):
        tau = np.sqrt(w + r*r)
        return r**(d - 2) * (duration - tau) / tau * correlation(tau, r)

    return measure / 2 * quad(integrand, lo, hi, epsabs=2e-12, epsrel=2e-11)[0]


def torus_long_pair_radial(d, length, duration, cutoff, rho,
                           correlation=lambda tau, r: 1.):
    """Original causal time/radius integral, before the phase substitution."""
    c, measure = _geometry(d, length, duration, cutoff)
    if not np.isfinite(rho) or rho <= 0:
        raise ValueError("positive finite density required")
    if cutoff >= duration:
        return 0.
    kernel = _kernel(d)
    return measure * quad(lambda tau: (duration-tau) * quad(
        lambda r: r**(d-2) * correlation(tau, r)
        * kernel(c*rho*(tau*tau-r*r)**(d/2)),
        0, tau, epsabs=2e-12, epsrel=2e-11)[0],
        cutoff, duration, epsabs=2e-12, epsrel=2e-11)[0]


def torus_long_pair_phase(d, length, duration, cutoff, rho,
                          correlation=lambda tau, r: 1.):
    """G8 at finite density, not a density-limit evaluator/certificate."""
    c, _ = _geometry(d, length, duration, cutoff)
    if not np.isfinite(rho) or rho <= 0:
        raise ValueError("positive finite density required")
    if cutoff >= duration:
        return 0.
    kernel = _kernel(d)
    return quad(lambda w: kernel(c*rho*w**(d/2)) * torus_long_density(
        d, length, duration, cutoff, w, correlation),
        0, duration**2, points=[cutoff**2], epsabs=2e-11, epsrel=2e-10)[0]


def primitive_response(d, exponent, rho):
    """Exact whole-half-line signed response for N(w)=w^exponent (G7).

    This analytic basis mode is NOT the primitive of a general region.
    Symbolic positive exponents are permitted; no divergent continuation.
    """
    r = s.sympify(exponent)
    rho = s.sympify(rho)
    if r.is_number and (r.is_real is not True or r <= 0):
        raise ValueError("primitive exponent must be real and positive")
    if rho.is_number and (rho.is_real is not True or rho <= 0):
        raise ValueError("positive density required")
    q = s.Rational(d, 2)
    _, beta = action_constants(d)
    c = interval_coefficient(d)
    return -beta * r * c**(-r/q) * rho**(1+(1-r)/q) * transverse_moment(d, r-1)
