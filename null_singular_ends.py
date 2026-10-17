"""Finite diagnostics for SE/IF; not certificates of asymptotic remainders.

The observable, dimensional kernels, probability law and dependencies are
unchanged. Quadratures here retain actual endpoint domains/physical unions.
"""

import math

import numpy as np
from scipy.integrate import quad
from scipy.special import gammainc, hyp2f1

from null_complete_gluing import _order, _positive
from seven_dimensional_focusing import _hypergeometric_coefficients


def _rule(order):
    _order(order)
    x, w = np.polynomial.legendre.leggauss(order)
    return (x+1)/2, w/2


def cusp_contains(point):
    """SE1 with the closed excluded J+(b), including its null generators."""
    if len(point) != 3 or not all(math.isfinite(x) for x in point):
        raise ValueError("three finite null coordinates required")
    u, v, y = point
    future_a = u > 0 and v > -1 and u*(v+1) > y*y
    past_c = u < 1 and v < 1 and (1-u)*(1-v) > y*y
    closed_future_b = u >= 0 and v >= 0 and u*v >= y*y
    return future_a and past_c and not closed_future_b


def cusp_bounds(v, y):
    if not math.isfinite(v) or not -1 < v < 1 or not math.isfinite(y):
        raise ValueError("requires -1 < v < 1 and finite y")
    lower, cap = y*y/(v+1), 1-y*y/(1-v)
    upper = min(y*y/v, cap) if v > 0 else cap
    if v == 0 and y == 0:
        upper = 0.  # The excluded closed null generator is not a physical fibre.
    return lower, upper


def cusp_partner_roots(pv, qv):
    if not all(math.isfinite(x) for x in (pv, qv)) or not 0 < pv < qv < 1:
        raise ValueError("requires 0 < pv < qv < 1")
    root = math.sqrt((qv-pv)/(qv*(pv+1)))
    upper = qv/pv*(1+root)
    lower = (qv+1)/((pv+1)*(1+root))  # Stable rationalized smaller root.
    return lower, upper


def _cusp_panels(order):
    """All v/y panels, including the actual cap switch; no deleted end."""
    nodes, weights = _rule(order)
    panels = ((math.pi/2*nodes, math.pi/2*weights),
              (math.pi/2*(1+nodes**2), math.pi*nodes*weights))
    for angles, angular_weights in panels:
        for theta, wt in zip(angles, angular_weights):
            v = -math.cos(theta)
            split = math.sqrt(2*v/(1+v)) if v > 0 else 0.
            edges = (0., split, 1.) if split else (0., 1.)
            for bottom, top in zip(edges, edges[1:]):
                z = bottom+(top-bottom)*nodes
                cap = (1+v)*(1-z*z)
                H = np.minimum(cap, (1-v*v)*z*z/(2*v)) if v > 0 else cap
                measure = math.sqrt(2)*(1-v)*wt*(top-bottom)*weights
                yield H, measure


def cusp_action(rho, *, order=40, integrate_normal=True):
    """Complete flat 3D action after the proved signed past-fibre integration.

    Independently integrate the remaining normal, or its incomplete-gamma
    primitive. This checks finite quadratures, not a high-density error bound.
    """
    _positive(rho)
    _order(order)
    if not isinstance(integrate_normal, bool):
        raise ValueError("integrate_normal must be boolean")
    c = math.pi/12
    if not integrate_normal:
        nodes, weights = _rule(order)
        a = 2*c**(2/3)/math.gamma(5/3)
    parts = []
    for H, measure in _cusp_panels(order):
        if integrate_normal:
            response = gammainc(2/3, rho*c*H**1.5)
        else:
            response = a*rho**(2/3)*H/2 * (
                np.exp(-rho*c*(H[:, None]*nodes)**1.5)@weights)
        parts.append(float(measure@response))
    return math.fsum(parts)


def cusp_volume(*, order=40):
    """Actual endpoint volume, independently of diamond subtraction."""
    return math.fsum(float(measure@(H/2)) for H, measure in _cusp_panels(order))


def closing_weight(U, T, *, order=32, scaled=False):
    """IF2's actual NP endpoint weight, or G_T(U)/(T-U)^(9/2).

    Uses Taylor's integral identity for the overlap bracket, never subtraction
    of nearly equal logarithmic terms. The scaled value extends to U=T.
    """
    _positive(U, T)
    _order(order)
    if U > T or not isinstance(scaled, bool):
        raise ValueError("requires U <= T and boolean scaled")
    nodes, weights = _rule(order)
    delta = T-U
    x, t = nodes[:, None], nodes[None, :]
    v = U+delta*x*x
    h = delta*(1-x*x)
    denominator = v+h*t
    bracket = (1-t)**2*(1/denominator+v*v/denominator**3)
    integrand = 2*x*x*v*np.sqrt(2*U+delta*x*x)*(1-x*x)**3*bracket
    value = float(4*math.pi*U*(weights@integrand@weights))
    return value if scaled else delta**4.5*value


def secondary_coefficient(theta, *, order=64):
    """Actual IF1 coefficient of (2*pi-theta-U)_+^(7/2) in W."""
    if not math.isfinite(theta) or not 0 < theta < math.pi:
        raise ValueError("requires 0 < theta < pi")
    nodes, weights = _rule(order)
    phi = math.pi*nodes
    y = theta*np.cos(phi)
    cosine_difference = 2*np.sin((theta+y)/2)*np.sin((theta-y)/2)
    endpoint = 2*math.pi-theta
    integral = float(math.pi*theta*weights@(
        np.sin(phi)*np.sqrt(cosine_difference)*(endpoint**2-y*y)**2))
    return 2*math.pi**2/(105*endpoint**2*math.sqrt(math.sin(theta)))*integral


def secondary_derivative_deficit(theta, distance, *, order=56):
    """Exact omitted x-edge in O5's analytic continuation of W_U.

    At U=x_star-distance this equals W_{+,U}-W_U. Both sphere orientations
    remain in J. Its leading coefficient is (7/2)*kappa*distance^(5/2).
    """
    _positive(distance)
    if not math.isfinite(theta) or not 0 < theta < math.pi or distance >= 2*(math.pi-theta):
        raise ValueError("requires 0 < distance < 2*(pi-theta)")
    nodes, weights = _rule(order)
    endpoint = 2*math.pi-theta
    U = endpoint-distance
    z = distance*nodes[:, None]**2
    x = endpoint-z
    phi = math.pi*nodes[None, :]
    y = theta*np.cos(phi)
    cy = 2*np.sin((theta+y)/2)*np.sin((theta-y)/2)
    cx = 2*np.sin(theta+z/2)*np.sin(z/2)
    jacobian = (cy+cx)/(2*np.sqrt(cy*cx))
    integrand = jacobian*((U-x)*(U+x))**2*(U*U-y*y)**2/U**4
    measure = 2*distance*nodes[:, None]*math.pi*theta*np.sin(phi)
    return float(math.pi**2/32*(weights@(integrand*measure)@weights))


def matched_profile_parts():
    """Both sides and the matching subtraction of O12, separately visible.

    Floating arithmetic only; O13's unchanged rational certificate owns sign.
    """
    from fractions import Fraction
    coefficients = _hypergeometric_coefficients(18)
    reciprocal = [Fraction(1)]
    for n in range(1, len(coefficients)):
        reciprocal.append(-sum(coefficients[k]*reciprocal[n-k] for k in range(1, n+1)))
    b = [float(x) for x in reciprocal]

    def remainder(x):
        if x < .1:
            return sum(b[j]*x**(j-3.5) for j in range(3, len(b)))
        return (1/hyp2f1(.5, .5, 4.5, x)-1-b[1]*x-b[2]*x*x)/x**3.5

    multiplier = 35*math.pi/128
    opening = multiplier*quad(remainder, 0, 1, points=[.1], epsabs=2e-11)[0]
    matching = multiplier*(-2/5-2*b[1]/3-2*b[2])
    meridian = math.log(2.5)/3
    return opening, matching, meridian
