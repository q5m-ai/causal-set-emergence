"""Finite diagnostics for notes/curved4-physical-response.md.

Not a manifold solver, geometric regularity oracle, or action-limit proof.
The clock helper requires an actually increasing volume supplied by its caller;
it neither constructs a geodesic branch nor assumes a differentiable inverse.
Signed-response helpers operate on scalar test primitives, not G-SS instances.
Canonical coefficients are consumed unchanged from dimension_kernels.py.
"""

from functools import lru_cache
import math

import mpmath as mp
import sympy as s
from scipy.optimize import brentq

from dimension_kernels import Z, action_constants, interval_coefficient, kernel_polynomial


def clock_sublevel_integral(volume, lower, upper, cap, weighted_antiderivative):
    """Integral of the actual weighted clock density on {lower <= t <= upper,
    volume(t) <= cap}. The caller establishes continuous strict increase on
    this causal fibre. All endpoints are finite; an empty/closing fibre is zero.
    The antiderivative includes the target measure and can have either sign.
    """
    if not all(math.isfinite(x) for x in (lower, upper, cap)) or cap < 0:
        raise ValueError("finite clock endpoints and nonnegative volume cap required")
    if lower >= upper or cap <= volume(lower):
        return 0.0
    end = (upper if cap >= volume(upper) else
           brentq(lambda t: volume(t)-cap, lower, upper,
                  xtol=5e-15, rtol=8e-15))
    return weighted_antiderivative(end)-weighted_antiderivative(lower)


@lru_cache(maxsize=1)
def _mp_kernel_data():
    polynomial = kernel_polynomial(4)
    # Convert exact symbolic expressions at evaluation time: callers may use
    # different mp.workdps contexts after this cache has been populated.
    evaluate = lambda expr: s.lambdify((), expr, "mpmath")
    return (s.lambdify(Z, polynomial, "mpmath"),
            s.lambdify(Z, s.diff(polynomial, Z)-polynomial, "mpmath"),
            evaluate(interval_coefficient(4)), evaluate(action_constants(4)[1]))


def kernel4(value):
    return _mp_kernel_data()[0](value)*mp.exp(-value)


def kernel4_prime(value):
    return _mp_kernel_data()[1](value)*mp.exp(-value)


def constants4():
    """c4, beta4 evaluated at the current mpmath precision."""
    data = _mp_kernel_data()
    return data[2](), data[3]()


def _panels(breaks):
    points = [mp.mpf(b) for b in breaks]
    if any(not mp.isfinite(b) or b <= 0 for b in points):
        raise ValueError("breaks must be finite and positive")
    return [mp.mpf(0), *sorted(set([mp.mpf(1), *points])), mp.inf]


def dilation_response(increment, breaks=()):
    """CP7 for a supplied F(h*z)-F(h), not an assertion of its domination."""
    c, beta = constants4()
    return 2*beta*c**(-mp.mpf("1.5"))*mp.quad(
        lambda z: z**4*kernel4_prime(z*z)*increment(z), _panels(breaks))


def stieltjes_response(primitive, rho, breaks=()):
    """Exact G5 scaling for a finite scalar primitive, constant past support.

    Breaks are in rescaled z, not phase w. No derivative of primitive is used.
    """
    rho = mp.mpf(rho)
    if not mp.isfinite(rho) or rho <= 0:
        raise ValueError("finite positive density required")
    c, beta = constants4()
    h = 1/mp.sqrt(c*rho)
    return 2*beta*rho**mp.mpf("1.5")*mp.quad(
        lambda z: z*kernel4_prime(z*z)*primitive(h*z), _panels(breaks))
