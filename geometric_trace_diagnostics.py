"""Finite checks for GT's geometric trace attempts, not a general limit solver.

Clock jets integrate physical-flow widths before any nonlinear filter. The
slowly varying control is explicitly abstract, not a spacetime construction.
Nothing here changes an action/probability API or certifies analytic bounds.
"""
from fractions import Fraction
import math

import numpy as np
from scipy.integrate import quad

from dimension_kernels import factor_count
from intrinsic_union_response import filter_coefficients, filtered_power


def ramp_log_derivative(d, ratio):
    """r*Phi_d'(r) a.e., with zero assigned at both endpoints and above one.

    Phi is continuous at one but has different one-sided derivatives there.
    This assigned value is not a claim of differentiability at the endpoint.
    """
    coefficients = filter_coefficients(d)
    r = np.asarray(ratio, dtype=float)
    if np.any(~np.isfinite(r)) or np.any(r < 0):
        raise ValueError("ratios must be finite and nonnegative")
    result = np.zeros_like(r)
    active = (r > 0) & (r < 1)
    x = -np.log(r[active])
    result[active] = -r[active]*sum(float(c)*x**i/math.factorial(i)
                                   for i, c in enumerate(coefficients))
    return float(result) if result.ndim == 0 else result


def density_jet_exponent(d):
    """Exact relative-phase exponent eta>1 for k=floor(d/2) density jets."""
    factor_count(d)
    return Fraction(2*(d//2+1), d)


def clock_volume_jet(arrivals, departures, derivatives, weights):
    """Integrate finite physical-flow quadrature widths with density time jets.

    derivatives[i,x] is the i-th density derivative at the actual arrival.
    Callers first unite all routes to obtain the physical departure; this
    function does not add per-route volumes. Empty fibres contribute zero.
    Positive quadrature and a positive truncated density integral are required;
    a jet that has left its positive collar is rejected, not clamped.
    """
    a, b = np.asarray(arrivals, dtype=float), np.asarray(departures, dtype=float)
    c, w = np.asarray(derivatives, dtype=float), np.asarray(weights, dtype=float)
    if (a.ndim != 1 or not len(a) or b.shape != a.shape or w.shape != a.shape
            or c.ndim != 2 or not c.shape[0] or c.shape[1] != len(a)
            or any(np.any(~np.isfinite(x)) for x in (a, b, c, w))
            or np.any(w < 0) or np.any(c[0] <= 0)):
        raise ValueError("finite matching clock arrays, positive density and nonnegative weights required")
    width = np.maximum(b-a, 0.)
    integral = sum(row*width**(i+1)/math.factorial(i+1) for i, row in enumerate(c))
    if np.any(~np.isfinite(integral)) or np.any(integral[width > 0] <= 0):
        raise ValueError("density jet left its positive collar")
    return float(w@integral)


def first_filter_slope(d):
    """Exact nonzero f_d'(2/d), not a fitted slowly varying coefficient."""
    m = factor_count(d)
    alpha = Fraction(2, d)
    return math.prod(alpha-Fraction(2*j, d) for j in range(2, m+1))/(1+alpha)**(m+1)


def slow_control(d, v):
    """Abstract U, U' and U'' on 0<v<exp(-8); no spacetime realization."""
    factor_count(d)
    if not math.isfinite(v) or not 0 < v < math.exp(-8):
        raise ValueError("the abstract control requires 0<v<exp(-8)")
    alpha, L = 2/d, -math.log(v)
    sign = -1 if d == 2 else 1
    return (v**alpha*(1+sign/L),
            v**(alpha-1)*(alpha+sign*(alpha/L+1/L**2)),
            v**(alpha-2)*(alpha*(alpha-1)+sign*(alpha*(alpha-1)/L
                          +(2*alpha-1)/L**2+2/L**3)))


def slow_control_filter(d, v):
    """GT13's convergent Laplace integral, not a fitted asymptotic response."""
    slow_control(d, v)
    L = -math.log(v)
    sign = -1 if d == 2 else 1
    value = quad(lambda u: math.exp(-u)*filtered_power(d, 2/d+u/L),
                 0, np.inf, epsabs=1e-13, epsrel=1e-11)[0]
    return sign*v**(2/d)*value/L
