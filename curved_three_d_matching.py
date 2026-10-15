"""Diagnostics for M3: signed averaging and minimum-coordinate matching.

The oscillatory primitive, quartic panel and polygon fan are explicitly
NON-GEOMETRIC analytic controls, not G-SS examples or action counterexamples.
No routine here decides the arbitrary curved-3D limit or changes its action.
"""

import math

import mpmath as mp
import numpy as np
from scipy.integrate import quad

from curved_three_d import BETA3, C3, quartic_profile


def phase_kernel_second(z):
    """Actual second derivative of F(z)=K3(z**(3/2)), for positive z."""
    z = np.asarray(z, dtype=float)
    if np.any(~np.isfinite(z)) or np.any(z <= 0):
        raise ValueError("finite positive phase required")
    q = z**1.5
    first = (-35 + 45*q - 9*q*q)/8
    second = (80 - 63*q + 9*q*q)/8
    return np.exp(-q) * (2.25*z*second + .75*z**-.5*first)


def ramp_response(rho, phases, weights):
    """M3.1 on a finite signed phase measure, with its LINEAR Q tail.

    This tests the identity/normalization, not geometric small-phase bounds.
    Quadrature is split at every actual ramp opening.
    """
    if not math.isfinite(rho) or rho <= 0:
        raise ValueError("finite positive density required")
    phases = np.asarray(phases, dtype=float)
    weights = np.asarray(weights, dtype=float)
    if (phases.ndim != 1 or phases.shape != weights.shape or
            np.any(~np.isfinite(phases)) or np.any(phases <= 0) or
            np.any(~np.isfinite(weights))):
        raise ValueError("equal finite vectors with positive phases required")
    t = (C3*rho)**(-2/3)
    openings = phases/t
    edges = [0., *sorted(set(openings)), math.inf]

    def integrand(z):
        q = np.dot(weights, np.maximum(t*z-phases, 0))
        return q*phase_kernel_second(z)

    integral = sum(quad(integrand, lo, hi, epsabs=2e-12, epsrel=2e-12)[0]
                   for lo, hi in zip(edges, edges[1:]))
    return -BETA3*C3**(-5/3)*t**(-3.5)*integral


def oscillatory_q_remainder(w, exponent=.75):
    """Integral_0^w s^2 sin(s^-a) ds, via the upper incomplete gamma.

    Analytic control only. Positivity of N' is guaranteed only on a
    separately chosen sufficiently small interval, as in M3.3.
    """
    if not math.isfinite(w) or w <= 0 or not .5 < exponent < 1:
        raise ValueError("requires w>0 finite and 1/2<a<1")
    with mp.workdps(40):
        w, a = mp.mpf(w), mp.mpf(exponent)
        power = 3/a + 1
        lower = w**(-a)
        tail = (-mp.j)**(power-1)*mp.gammainc(1-power, -mp.j*lower, mp.inf)
        return float(mp.im(tail)/a)


def quartic_matching_bounds(w):
    """Four EXACT elementary integrals in M3.5, unit matching constants.

    They are remainder majorants, not the actual focal primitive itself.
    """
    if not math.isfinite(w) or not 0 < w <= 1:
        raise ValueError("requires 0<w<=1")
    k = w**.6
    return np.array([
        2*w**3*(k**-.5-1),
        (2/5)*w**1.2*k**2.5,
        (6/17)*w*k**(17/6),
        (6/7)*w*w*k**(7/6),
    ])


def quartic_sublens(k, h, cubic_ratio=0.):
    """All wells of h-k*u^2-4*r*sqrt(k)*u^3-u^4, |r|<=1/2.

    A one-screen integral diagnostic, not a spacetime volume substitute.
    """
    if (not all(math.isfinite(v) for v in (k, h, cubic_ratio)) or
            k <= 0 or h <= 0 or abs(cubic_ratio) > .5):
        raise ValueError("positive finite k,h and |r|<=1/2 required")
    return k**2.5*quartic_profile(h/k**2, cubic_ratio)


def clipped_sine_integral(count, band_ratio):
    """Integral_{|b|<s} (b')^2 for b=sin(n*a)/n^2 on [0,2*pi]."""
    if (isinstance(count, bool) or not isinstance(count, int) or count < 1 or
            not math.isfinite(band_ratio) or not 0 < band_ratio < 1):
        raise ValueError("positive integer n and 0<band_ratio<1 required")
    r = band_ratio
    return (2*math.asin(r)+2*r*math.sqrt(1-r*r))/count**2


def panel_matched_head(s):
    """Matched bounded-domain Mellin numerator for the NON-GEOMETRIC panel.

    The large-t head is subtracted/restored, not extended as a convergent
    integral. Real arguments only; the written continuation is separate.
    """
    if (not math.isfinite(s) or not 0 < s < 2 or
            abs(1-1.5*s) < 1e-12 or abs(2-1.5*s) < 1e-12):
        raise ValueError("requires 0<s<2 away from 2/3 and 4/3")
    phi = (1+math.sqrt(5))/2
    a, b, d = 4/3, 8/5, 6/5
    left = quad(lambda t: t*(t+2)*(a*t+b)**(-s) *
                (1+t)**(-(8-5*s)/4), 0, phi, epsabs=2e-11)[0]
    # Taylor coefficients of (1+2u)*(1+d*u)^(-s).
    coeff = [1.]
    binomial = 1.
    previous = 1.
    for j in range(1, 7):
        binomial *= -(s+j-1)*d/j
        coeff.append(binomial+2*previous)
        previous = binomial

    def remainder(u):
        if u < 1e-3:
            return a**(-s)*u**(2-1.5*s)*sum(
                coeff[j]*u**(j-2) for j in range(2, 7))
        return u**(-1.5*s)*a**(-s)*(
            (1+2*u)*(1+d*u)**(-s)-1-coeff[1]*u)

    upper = 1/phi
    right = quad(remainder, 0, upper, epsabs=2e-11, epsrel=2e-11)[0]
    right += a**(-s)*(upper**(1-1.5*s)/(1-1.5*s) +
                      coeff[1]*upper**(2-1.5*s)/(2-1.5*s))
    return left+right


def panel_residue_value():
    """I(8/5), not a coefficient of any admitted spacetime action."""
    return -125/126*(3/4)**(8/5)*(6/5)**(7/5)


def fan_jump_sums(count):
    """Gradient-jump and reciprocal-jump sums of a regular polygon fan."""
    if isinstance(count, bool) or not isinstance(count, int) or count < 3:
        raise ValueError("integer count >= 3 required")
    jump = 2*math.sin(math.pi/count)
    return count*jump, count/jump
