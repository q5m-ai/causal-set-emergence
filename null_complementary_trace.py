"""Finite diagnostics for notes/null-complementary-trace.md.

No general-Y trace solver, production action change, or asymptotic certificate.
The triangle polynomial approximates only the elementary Abel prefactor;
conditional distances and the second square root must remain intact.
"""

import math

from scipy.integrate import quad

from dimension_kernels import action_constants, factor_count, interval_coefficient
from null_suspension import cap_weight
from null_suspension_matching import moment_pairing


def _finite(*values):
    if any(not math.isfinite(value) for value in values):
        raise ValueError("arguments must be finite")


def _order(order):
    if order is not None and (isinstance(order, bool)
                              or not isinstance(order, int) or order < 0):
        raise ValueError("order must be None or a nonnegative integer")


def triangle_prefactor(length, time, excess, order=None):
    """CT3 exact A or its total-degree polynomial, not a triangle-density jet.

    Positivity/comparison of the polynomial is proved only on a small fixed
    excess collar. Evaluating it farther away does not extend that theorem.
    """
    _finite(length, time, excess)
    _order(order)
    if length <= 0 or not 0 <= excess <= time:
        raise ValueError("use length > 0 and 0 <= excess <= time")
    if order is None:
        return math.sqrt(2*length+time+excess)/(length+time)
    x, y = (time+excess)/(2*length), -time/length
    coefficient = 1.0
    terms = []
    for i in range(order+1):
        if i:
            coefficient *= (1.5-i)/i
        terms.extend(coefficient*x**i*y**j for j in range(order-i+1))
    return math.sqrt(2/length)*math.fsum(terms)


def triangle_section(length, height, excess, difference, order=None):
    """Inner CT3 integral for one distance-pair atom, including both tips.

    This evaluates a finite geometric probe, not an endpoint-averaged phase.
    The exact version equals IN5's physical_section for the corresponding
    two intermediate-point distances.
    """
    _finite(length, height, excess, difference)
    _order(order)
    if (length <= 0 or height < 0 or excess < 0
            or abs(difference) > length):
        raise ValueError("use positive length, nonnegative gaps, |difference| <= length")
    if excess >= height:
        return 0.0
    gap = height-excess

    def integrand(z):
        t = excess+gap*z*z
        # This product retains the vanishing longitudinal factor at either tip.
        longitudinal = math.sqrt((length+t-difference)*(length+t+difference))
        return (2*gap**1.5*z*z*longitudinal
                * triangle_prefactor(length, t, excess, order))

    return quad(integrand, 0, 1, epsabs=2e-14, epsrel=2e-11)[0]


def replacement_exponent(d):
    """CT4 eta; normalized replacement error has order rho**(1-eta)."""
    factor_count(d)
    return 2*(d//2+1)/d


def cap_third(u, duration):
    """Third u derivative of the actual zero-extended G, a.e.; not d/dT."""
    _finite(u, duration)
    if u <= 0 or duration <= 0:
        raise ValueError("u and duration must be positive")
    if u >= duration:
        return 0.0
    return 6*math.log(duration/u)+(duration/u)**2-5


def transport_pairing(duration, anchor, moments, third_primitive):
    """Exact CT7 from four LOWER moments and the anchored third primitive.

    moments = (m1, l1, m3, l3), with log reference length one. The caller
    supplies finite signed data; this function does not infer a trace or
    discard homogeneous/anchor terms.
    """
    _finite(duration, anchor)
    if not 0 < anchor <= duration:
        raise ValueError("use 0 < anchor <= duration")
    if len(moments) != 4:
        raise ValueError("four lower moments required")
    homogeneous = moment_pairing(duration, *moments)
    return homogeneous-quad(
        lambda u: cap_third(u, duration)*third_primitive(u),
        anchor, duration, epsabs=2e-11, epsrel=2e-11)[0]


def fold_trace_prefactor(d):
    """CT5 c_d^fold divided by m_q, NOT the full charge or auxiliary moment."""
    factor_count(d)
    if d < 5:
        raise ValueError("the flat fold family requires d >= 5")
    p = d-4
    area = 2*math.pi**(p/2)/math.gamma(p/2)
    product = math.prod(1-7/(2*k) for k in range(4, d//2+2))
    return (float(action_constants(d)[1])*10**p*area
            * float(interval_coefficient(d))**(-7/d)*product
            / (336*math.sqrt(2)))


def six_dimensional_cap_integral(duration):
    """Integral_1^T G_T, in the actual SM lift window; not a fitted charge.

    Positive quadrature avoids cancellation of the closed CT6 expression
    near T=1. Multiplication by c_6^fold, including m_3, is still required.
    """
    _finite(duration)
    if not 1 < duration < math.sqrt(5)/2:
        raise ValueError("use 1 < T < sqrt(5)/2 for this family")
    gap = duration-1
    return gap*quad(lambda t: cap_weight(1+gap*t, duration),
                    0, 1, epsabs=1e-17, epsrel=2e-11)[0]
