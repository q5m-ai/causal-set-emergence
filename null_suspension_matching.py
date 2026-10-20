"""Finite diagnostics for notes/null-suspension-matching.md.

The canonical action, kernels and Poisson law are unchanged. Mellin formulas
are for the signed, radially integrated local reference; numerical profiles
and geometric cap coefficients are not a general-Y asymptotic solver.
"""

from functools import lru_cache
import math

from scipy.integrate import quad
import sympy as s

from dimension_kernels import (
    Z, action_constants, factor_count, interval_coefficient, kernel_polynomial,
)
from null_suspension import cap_weight


def _finite(*values):
    if any(not math.isfinite(value) for value in values):
        raise ValueError("arguments must be finite")


def moment_pairing(duration, m1, l1, m3, l3, log_scale=1.0):
    """Exact SM1 recombination; moments retain their actual upper endpoint."""
    _finite(duration, m1, l1, m3, l3, log_scale)
    if duration <= 0 or log_scale <= 0:
        raise ValueError("duration and reference length must be positive")
    log_t = math.log(duration/log_scale)
    return duration**2*((log_t-1)*m1-l1)+(log_t+1)*m3-l3


def origin_mellin(d, exponent):
    """SM3: integral u**s H_0(u), after signed radial integration.

    Symbolic exponents carry the stated strip obligation. Numeric exponents
    must be real, greater than 1-d, and less than 4 in odd dimension. The
    factored form preserves the zeros AND the logarithmic derivatives.
    """
    m = factor_count(d)
    exponent = s.sympify(exponent)
    if exponent.is_number and (
            exponent.is_real is not True or exponent <= 1-d
            or (d % 2 and exponent >= 4)):
        raise ValueError("exponent is outside the convergent profile strip")
    z = (exponent+d-1)/d
    prefactor = (s.pi**s.Rational(d-2, 2) * interval_coefficient(d)**(-z)
                 * s.gamma(z)/(d*s.factorial(m)))
    answer = prefactor*(1-exponent)*(3-exponent)/4
    if d % 2:
        answer *= s.gamma((4-exponent)/2)/s.gamma((5-exponent)/2)
    return answer


def curvature_mellin(d, exponent):
    """SM3 formal H_2 coefficient; actual scalar curvature is zero for n<2.

    In odd dimensions the power-3 integral is divergent, not an uncut moment
    to assign by analytic continuation. d=2 has no curvature coefficient.
    """
    factor_count(d)
    exponent = s.sympify(exponent)
    if d == 2:
        return s.S.Zero
    if exponent.is_number and (
            exponent.is_real is not True or exponent <= -d-1
            or (d % 2 and exponent >= 2)):
        raise ValueError("exponent is outside the curvature-profile strip")
    # The apparent pole at s=-1 is removable; do not evaluate 0/0.
    x = s.Dummy('x', real=True)
    factor = (s.Rational(1, 6)
              + (x+d+1)*(x+2*d+1)/(24*(d+1)*(d+2)))/(x+1)
    expression = origin_mellin(d, x+2)*factor
    if exponent == -1:
        return s.limit(expression, x, -1)
    return expression.subs(x, exponent)


@lru_cache(maxsize=None)
def _kernels(d):
    p = kernel_polynomial(d)
    return (s.lambdify(Z, p*s.exp(-Z), 'math'),
            s.lambdify(Z, (s.diff(p, Z)-p)*s.exp(-Z), 'math'))


def normal_profile(d, u, curvature=False):
    """Finite radial quadrature of SM2 at density one, not a tail estimator."""
    factor_count(d)
    _finite(u)
    if u < 0 or not isinstance(curvature, bool):
        raise ValueError("use nonnegative u and a boolean curvature flag")
    kernel, derivative = _kernels(d)
    c = float(interval_coefficient(d))
    if d == 2:
        return 0.0 if curvature else kernel(c*u*u)
    if u == 0:
        return 0.0
    n = d-2
    area = 2*math.pi**(n/2)/math.gamma(n/2)
    a = d/(24*(d+1))
    b = a/(d+2)

    def integrand(theta):
        sine, cosine = math.sin(theta), math.cos(theta)
        r2, sigma = (u*sine)**2, (u*cosine)**2
        z = c*sigma**(d/2)
        response = kernel(z)
        if curvature:
            response = (-r2*response/(6*n)
                        + (a*r2/n-b*sigma)*z*derivative(z))
        return sine**(n-1)*cosine*response

    return area*u**n*quad(integrand, 0, math.pi/2,
                         epsabs=2e-12, epsrel=2e-11, limit=180)[0]


def fold_cap_weight(flat_dimensions, squared_radius, duration):
    """Actual spectator integral F_{p,T}(A), including cubic physical closing.

    This weight exists outside the theorem's lift-enumeration window too;
    using it there does not establish that the same four lifts are complete.
    """
    if (isinstance(flat_dimensions, bool)
            or not isinstance(flat_dimensions, int) or flat_dimensions < 1):
        raise ValueError("flat spectator dimension must be a positive integer")
    _finite(squared_radius, duration)
    if squared_radius <= 0 or duration <= 0:
        raise ValueError("squared radius and duration must be positive")
    if squared_radius >= duration**2:
        return 0.0
    p = flat_dimensions
    radius = math.sqrt(duration**2-squared_radius)
    area = 2*math.pi**(p/2)/math.gamma(p/2)

    def integrand(t):
        u = math.sqrt(squared_radius+(radius*t)**2)
        return t**(p-1)*cap_weight(u, duration)/u

    return area*radius**p/2*quad(integrand, 0, 1,
                               epsabs=1e-15, epsrel=2e-11)[0]


def klein_charge_prefactor(d, duration=21/20):
    """SM8 D_d(T) divided by the positive auxiliary Weibull moment.

    That finite moment is specified independently in the note; it is NOT
    set to one and no sampled action is used to fit this coefficient.
    """
    factor_count(d)
    _finite(duration)
    if d < 5 or not 1 < duration < math.sqrt(5)/2:
        raise ValueError("use d >= 5 and 1 < T < sqrt(5)/2 for this family")
    p = d-4
    density = 10**p/(8*math.sqrt(2))*fold_cap_weight(p, 1.0, duration)
    positive_product = math.prod(1-7/(2*k) for k in range(4, d//2+2))
    beta = float(action_constants(d)[1])
    c = float(interval_coefficient(d))
    return beta*density*c**(-7/d)*positive_product/21
