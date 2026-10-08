"""Diagnostics for the written all-dimensional Minkowski producer theorem.

See notes/all-dimensional-flat-limit.md. These algorithms work for integer
physical d >= 2; finite tests do not prove the geometric theorem. Constants,
kernels, observables and formal interfaces are imported/unchanged. Actual
capsule overlaps are distinguished from Taylor models and quadrature is not
certified error control.
"""

from functools import lru_cache
import math

from scipy.integrate import quad
import sympy as s

from dimension_kernels import (
    action_constants, interval_coefficient, sphere_area, transverse_moment,
)


def _dimension(d):
    if isinstance(d, bool) or not isinstance(d, int) or d < 2:
        raise ValueError("physical dimension must be an integer >= 2")
    return d


def _natural(k):
    if isinstance(k, bool) or not isinstance(k, int) or k < 0:
        raise ValueError("monomial powers must be nonnegative integers")
    return k


def sufficient_regularity(d):
    """Sufficient r(d), not a minimality claim or admissibility oracle."""
    return max(3, (_dimension(d) + 1) // 2 + 1)


def short_monomial(d, time_power, radial_power, sigma, delta):
    """Actual sharp monomial fibre on 0<sigma<delta^2, WITHOUT sphere area.

    Finite Laurent integration, including both endpoints and resonant logs.
    The physical fibre is zero above delta^2; this symbolic expression is not.
    Symbols must represent positive sigma,delta in that domain.
    """
    d = _dimension(d)
    p, k = _natural(time_power), _natural(radial_power)
    x, L = s.sympify(sigma), s.sympify(delta)
    X = s.Dummy("X")
    polynomial = s.Poly((1-X)**(d-2+k) * (1+X)**p, X)
    D = d-2+p+k
    terms = []
    for (ell,), coefficient in polynomial.terms():
        exponent = D-2*ell
        primitive = ((L**exponent - x**s.Rational(exponent, 2))/exponent
                     if exponent else s.log(L)-s.log(x)/2)
        terms.append(coefficient*x**ell*primitive)
    return s.expand(sum(terms) / s.Integer(2)**(d-1+p+k))


def short_bases(d, sigma, delta):
    """Constant, time, time squared, radius squared; actual in-support fibres."""
    return tuple(short_monomial(d, p, k, sigma, delta)
                 for p, k in ((0, 0), (1, 0), (2, 0), (0, 2)))


def constant_singular_coefficient(d):
    """Coefficient of sigma^(q-1), odd; sigma^(q-1) log(sigma), even."""
    N = _dimension(d)//2
    if d % 2:
        return s.simplify((-1)**N * s.sqrt(s.pi)*s.gamma(N)
                          / (4*s.gamma(N+s.Rational(1, 2))))
    return (-1)**N * s.binomial(2*N-2, N-1)/s.Integer(2)**(2*N)


@lru_cache(maxsize=None, typed=True)
def log_moment(d, order):
    """Actual convergent logarithmic transverse moment (j > -1)."""
    _dimension(d)
    order = s.sympify(order)
    if order.is_number and (order.is_real is not True or order <= -1):
        raise ValueError("logarithmic moment requires real order > -1")
    j = s.Dummy("j", real=True)
    # Keep the finite product, avoiding meromorphic gamma quotients at roots.
    moment = (s.Rational(2, d)*s.gamma(2*(j+1)/d)
              * s.prod(1-(j+1)/i for i in range(1, d//2+2)))
    return s.simplify(s.diff(moment, j).subs(j, order))


def basis_responses(d):
    """Derived (constant pair/volume, normalized time^2, normalized radius^2).

    First entry must equal a/beta to cancel the point. Last two include the
    action's MINUS pair sign, not sphere area or geometric jet coefficients.
    """
    d = _dimension(d)
    q = s.Rational(d, 2)
    alpha = constant_singular_coefficient(d)
    moment = transverse_moment if d % 2 else log_moment
    c = interval_coefficient(d)
    _, beta = action_constants(d)
    point = s.simplify(sphere_area(d)*alpha*moment(d, q-1)/c)
    time2 = s.simplify(-beta*c**(-1-s.Rational(2, d))*alpha*moment(d, q)/d)
    return point, time2, s.simplify(-(d-1)*time2)


def sphere_monomial(d, powers):
    """Ordinary sphere monomial integral, including S^0's two atoms."""
    n = _dimension(d)-1
    powers = tuple(_natural(k) for k in powers)
    if len(powers) != n:
        raise ValueError("one power is required per spatial coordinate")
    if any(k % 2 for k in powers):
        return s.Integer(0)
    return s.simplify(2*s.prod(s.gamma(s.Rational(k+1, 2)) for k in powers)
                      / s.gamma(s.Rational(n+sum(powers), 2)))


def _steepness(steepness):
    value = float(steepness)
    if not math.isfinite(value) or not 0 < value < 1:
        raise ValueError("each face slope must be strictly between zero and one")
    return value


def capsule_overlap(d, tau, spatial, *, steepness=0.75, weight="one"):
    """Genuine full-partner symmetric-capsule overlap, not its quadratic jet.

    Allowed source weights: one, x_1^2, and 1-|x|^2 ('height'). No combined
    slope budget is required. The time and source coordinates were integrated
    exactly in (A24); this evaluates that formula in floating point.
    """
    n = _dimension(d)-1
    slope = _steepness(steepness)
    spatial = tuple(spatial)
    if (len(spatial) != n or not math.isfinite(tau)
            or not all(math.isfinite(b) for b in spatial)
            or tau < math.hypot(*spatial)):
        raise ValueError("require a finite future-causal displacement")
    if weight not in ("one", "axis-square", "height"):
        raise ValueError("unknown capsule source weight")
    radius2 = sum(b*b for b in spatial)
    gap = max(0.0, 1-tau/slope-radius2/4)
    ball = math.pi**(n/2)/math.gamma(1+n/2)
    V = 2*slope*ball/(n+2)*gap**((n+2)/2)
    first_axis = 2*slope*ball/((n+2)*(n+4))*gap**((n+4)/2)
    if weight == "axis-square":
        return first_axis+spatial[0]**2*V/4
    if weight == "height":
        return V-n*first_axis-radius2*V/4
    return V


def capsule_angular_jet(d, *, steepness=s.Rational(3, 4), weight="one"):
    """Actual angular two-jet differentiated from (A24), not a fitted target."""
    n = _dimension(d)-1
    _steepness(steepness)
    slope = s.sympify(steepness)
    tau, radius2 = s.symbols("tau radius_squared", real=True)
    ball = s.pi**s.Rational(n, 2)/s.gamma(1+s.Rational(n, 2))
    gap = 1-tau/slope-radius2/4
    V = 2*slope*ball/(n+2)*gap**s.Rational(n+2, 2)
    axis = 2*slope*ball/((n+2)*(n+4))*gap**s.Rational(n+4, 2)
    if weight == "axis-square":
        V = axis+radius2*V/(4*n)  # actual angular average of b_1^2
    elif weight == "height":
        V = V-n*axis-radius2*V/4
    elif weight != "one":
        raise ValueError("unknown capsule source weight")
    zero = {tau: 0, radius2: 0}
    return tuple(s.simplify(sphere_area(d)*term.subs(zero)) for term in
                 (V, s.diff(V, tau), s.diff(V, tau, 2)/2, s.diff(V, radius2)))


def capsule_geometric_terms(d, *, steepness=s.Rational(3, 4), weight="one"):
    """Independent normal/Gram joint integral and whole-ball source flux."""
    n = _dimension(d)-1
    _steepness(steepness)
    slope = s.sympify(steepness)
    ball = s.pi**s.Rational(n, 2)/s.gamma(1+s.Rational(n, 2))
    angle = (1+slope**2)/(2*slope)
    if weight == "one":
        return s.simplify(sphere_area(d)*angle), s.Integer(0)
    if weight == "axis-square":
        return s.simplify(ball*angle), s.simplify(-2*slope*ball/(n+2))
    if weight == "height":
        return s.Integer(0), s.simplify(2*slope*n*ball/(n+2))
    raise ValueError("unknown capsule source weight")


def capsule_density(d, sigma, delta, *, steepness=0.75, long=False,
                    coordinates="time"):
    """Actual capsule short/long density by either independent coordinate law.

    Numerical diagnostic only. Short is zero at/above delta^2. The short 2D
    density is not finite at sigma=0, so positive sigma is required throughout.
    """
    n = _dimension(d)-1
    slope = _steepness(steepness)
    if (not math.isfinite(sigma) or sigma <= 0 or not math.isfinite(delta)
            or delta <= 0 or coordinates not in ("time", "null")):
        raise ValueError("require positive finite sigma,delta and time/null coordinates")
    if not long and sigma >= delta**2:
        return 0.0
    root = math.sqrt(sigma)
    end = (4+sigma)/(math.sqrt(4/slope**2+4+sigma)+2/slope)
    if end <= root:
        return 0.0
    S = float(sphere_area(d))
    overlap = lambda t, r: capsule_overlap(
        d, t, (r,)+(0.0,)*(n-1), steepness=slope)
    if coordinates == "time":
        cutoff = (delta+sigma/delta)/2 if sigma < delta**2 else root
        lower, upper = (cutoff, end) if long else (root, min(cutoff, end))
        if upper <= lower:
            return 0.0
        length = upper-lower

        def integrand(u):
            # Square substitution controls the integrable d=2 radial endpoint.
            t = lower+length*u*u
            r2 = (t-root)*(t+root)
            return (S*length*u*r2**((d-3)/2)
                    * overlap(t, math.sqrt(r2)))

        return quad(integrand, 0, 1, epsabs=1e-11, epsrel=1e-11)[0]
    vend = end+math.sqrt(end*end-sigma)
    lower, upper = (max(delta, root), vend) if long else (root, min(delta, vend))
    if upper <= lower:
        return 0.0

    def integrand(v):
        t, r = (v+sigma/v)/2, (v-sigma/v)/2
        return S*r**(d-2)/(2*v)*overlap(t, r)

    return quad(integrand, lower, upper, epsabs=1e-11, epsrel=1e-11)[0]
