"""Finite diagnostics for notes/sphere-circle-focusing.md (#139).

These evaluate actual geometric integrals, not production action APIs or
asymptotic proof certificates. No sphere geodesic-image volumes are summed.
Circle lifts are valid only for the fixed duration 4, circumference 20 slab.
"""

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.optimize import brentq

from general_metric_gate import antipodal_coefficient, gauss_rule

DURATION = 4.0
CIRCUMFERENCE = 20.0
PAIR_FACTOR = 8 * np.pi**2 * CIRCUMFERENCE


def time_weight(u, cutoff=None, short=False):
    """Exact b/time average, F2/F3; the time allocation is always 4-tau."""
    if not 0 <= u <= DURATION:
        raise ValueError("requires 0 <= u <= 4")
    if cutoff is not None and not 0 < cutoff < DURATION:
        raise ValueError("requires 0 < cutoff < 4")
    if short and cutoff is None:
        raise ValueError("short weight requires a cutoff")
    if u == 0 or u == DURATION:
        return 0.0
    full = 2 * u * (4 * np.arccosh(4 / u) - np.sqrt(16 - u*u))
    if cutoff is None:
        return full
    removed = (2 * u * (4 * np.arccosh(cutoff / u)
                        - np.sqrt(cutoff**2 - u*u)) if u < cutoff else 0.0)
    return removed if short else full - removed


def circle_section(tau, b, r, s_distance, order=24):
    """Actual integral (tau-hypot(r,z)-hypot(s,z-b))_+ dz.

    Uses the exact ellipse roots to resolve small support, then integrates the
    original positive part. r and s_distance may be arrays. This is also an
    independent nonzero-b check of the boost reduction.
    """
    if not abs(b) < tau <= DURATION:
        raise ValueError("requires |b| < tau <= 4")
    r, s_distance = np.broadcast_arrays(r, s_distance)
    q = tau*tau - b*b
    active = r + s_distance < np.sqrt(q)
    discriminant = np.maximum(0, (q - (r+s_distance)**2)
                               * (q - (r-s_distance)**2))
    half = np.where(active, tau / (2*q) * np.sqrt(discriminant), 0)
    center = b * (q + r*r - s_distance*s_distance) / (2*q)
    nodes, weights = gauss_rule(order)
    z = center[..., None] + half[..., None] * (2*nodes-1)
    if b == 0:
        # Rationalize the two differences, rather than cancel O(1) distances.
        rr, ss = r[..., None], s_distance[..., None]
        gap = ((tau-r-s_distance)[..., None]
               - z*z / np.maximum(np.hypot(rr, z)+rr, 1e-300)
               - z*z / np.maximum(np.hypot(ss, z)+ss, 1e-300))
    else:
        gap = tau - np.hypot(r[..., None], z) - np.hypot(s_distance[..., None], z-b)
    return 2 * half * np.sum(weights * np.maximum(0, gap), axis=-1)


def _sphere_rule(theta, u, order):
    """Resolve both integrable two-distance Jacobian edges by sine maps."""
    if not 0 < theta < np.pi or not theta <= u <= DURATION:
        raise ValueError("requires 0 < theta < pi and theta <= u <= 4")
    nodes, weights = gauss_rule(order)
    a = np.pi - theta
    top = min(u, 2*np.pi-theta)
    xi_max = np.arccos(np.clip((np.pi-top)/a, -1, 1))
    xi = xi_max * nodes[:, None]
    eta = np.pi * (nodes[None, :] - 0.5)
    x = np.pi - a * np.cos(xi)
    y = theta * np.sin(eta)
    first = 2 * np.sin((theta+y)/2) * np.sin((theta-y)/2)
    second = 2 * np.sin((x+theta)/2) * np.sin((x-theta)/2)
    numerator = 2 * np.sin((x+y)/2) * np.sin((x-y)/2)
    jac = numerator / (2 * np.sqrt(first * second))
    measure = (weights[:, None] * weights[None, :] * xi_max * np.pi
               * a * np.sin(xi) * theta * np.cos(eta) * jac)
    return x, y, measure


def sphere_measure(theta, order=64):
    """Integral of the whole two-sheet Jacobian; must be 4*pi."""
    # The rule's upper bound is irrelevant to causal time for this check.
    if 2*np.pi-theta > DURATION:
        # Use a separate identical full-range map for general theta.
        nodes, weights = gauss_rule(order)
        a = np.pi-theta
        xi, eta = np.pi*nodes[:, None], np.pi*(nodes[None, :]-0.5)
        x, y = np.pi-a*np.cos(xi), theta*np.sin(eta)
        first = 2*np.sin((theta+y)/2)*np.sin((theta-y)/2)
        second = 2*np.sin((x+theta)/2)*np.sin((x-theta)/2)
        numerator = 2*np.sin((x+y)/2)*np.sin((x-y)/2)
        return np.sum(weights[:, None]*weights[None, :]*np.pi**2
                      * a*np.sin(xi)*theta*np.cos(eta)*numerator
                      / (2*np.sqrt(first*second)))
    return np.sum(_sphere_rule(theta, 2*np.pi-theta, order)[2])


def interval_volume(u, theta, order=48, circle_order=24):
    """Actual W(u,theta), F1/F4, resolving both sphere sheets and z support."""
    if not 0 <= theta <= np.pi or not theta <= u <= DURATION:
        raise ValueError("requires 0 <= theta <= pi and theta <= u <= 4")
    if u == theta:
        return 0.0
    if theta in (0, np.pi):
        nodes, weights = gauss_rule(order)
        r = (np.pi if theta == np.pi else min(np.pi, u/2)) * nodes
        ss = np.pi-r if theta == np.pi else r
        upper = np.pi if theta == np.pi else min(np.pi, u/2)
        return 2*np.pi*upper*np.sum(weights*np.sin(r)
                                   * circle_section(u, 0, r, ss, circle_order))
    x, y, measure = _sphere_rule(theta, u, order)
    return np.sum(measure * circle_section(u, 0, (x+y)/2, (x-y)/2, circle_order))


def volume_derivative(u, theta, order=64):
    """First u derivative only: the positive spatial sublevel measure, F4."""
    if u == theta:
        return 0.0
    x, y, measure = _sphere_rule(theta, u, order)
    width = np.sqrt(np.maximum(0, (u-x)*(u+x)*(u-y)*(u+y))) / u
    return np.sum(measure * width)


def polar_volume(tau, theta, b=0.0, order=64, circle_order=32):
    """Independent F1 cubature in north-pole coordinates, not the F4 Jacobian.

    Solve the exact spherical cap in phi at each r before circle integration.
    Both halves of phi are included. Split r at its cap contacts.
    """
    if not abs(b) < tau <= DURATION or not 0 < theta < np.pi:
        raise ValueError("requires |b| < tau <= 4 and 0 < theta < pi")
    u = np.sqrt(tau*tau-b*b)
    if u <= theta:
        return 0.0
    nodes, weights = gauss_rule(order)
    edges = sorted(set([0.0, np.pi, min(np.pi, (u-theta)/2),
                        min(np.pi, (u+theta)/2)]))
    result = 0.0
    for lo, hi in zip(edges, edges[1:]):
        r = (lo+(hi-lo)*nodes)[:, None]
        allowed = u-r
        threshold = ((np.cos(np.clip(allowed, 0, np.pi))-np.cos(r)*np.cos(theta))
                     / (np.sin(r)*np.sin(theta)))
        phi_max = np.where(allowed >= np.pi, np.pi,
                           np.where(allowed <= 0, 0, np.arccos(np.clip(threshold, -1, 1))))
        phi = phi_max * nodes[None, :]
        ss = np.arccos(np.clip(np.cos(r)*np.cos(theta)
                              + np.sin(r)*np.sin(theta)*np.cos(phi), -1, 1))
        sections = circle_section(tau, b, r, ss, circle_order)
        result += 2*(hi-lo)*np.sum(weights[:, None]*weights[None, :]
                                   * np.sin(r)*phi_max*sections)
    return result


def area_ratio(theta, r, ss):
    """Exact spherical/Euclidean two-distance area ratio, F8."""
    sinc = lambda v: np.sinc(v/np.pi)
    denominator = (sinc((r+ss+theta)/2)*sinc((r+ss-theta)/2)
                   * sinc((theta+r-ss)/2)*sinc((theta-r+ss)/2))
    return sinc(r)*sinc(ss)/np.sqrt(denominator)


def regular_phase(theta, e, order=32):
    """Exact H=W/e^2 from the fixed flat rest diamond, including e=0.

    The validity guard excludes the secondary transition; this representation
    is deliberately not transplanted through it.
    """
    if not 0 < theta < np.pi or not 0 <= e < 2*(np.pi-theta):
        raise ValueError("requires 0 < theta < pi and 0 <= e < 2*(pi-theta)")
    nodes, weights = gauss_rule(order)
    total = 0.0
    for sign in (-1, 1):
        A = sign*nodes[:, None, None]/2
        radius = 0.5-np.abs(A)
        B1 = radius*(2*nodes[None, :, None]-1)
        height = np.sqrt(np.maximum(0, radius*radius-B1*B1))
        eta = np.pi*(nodes[None, None, :]-0.5)
        B2 = height*np.sin(eta)
        ell = 0.5+A+B1
        q = 2*theta*e+e*e
        r = np.sqrt((theta*ell+e*B1)**2+q*B2*B2)
        ss = np.sqrt((theta*(1-ell)-e*B1)**2+q*B2*B2)
        # dA=1/2, dB1=2*radius, dB2*dB3=2*height^2*cos(eta)^2*deta.
        measure = (2*np.pi*radius*height**2*np.cos(eta)**2
                   * weights[:, None, None]*weights[None, :, None]*weights[None, None, :])
        total += np.sum(measure*area_ratio(theta, r, ss))
    return (2*theta+e)**2*total


def _log_sinc_derivatives(x):
    """First two derivatives of log(sinc(x)), with removable zero resolved."""
    x = np.asarray(x)
    small = np.abs(x) < 1e-3
    safe = np.where(small, 1.0, x)
    first = np.where(small, -x/3-x**3/45-2*x**5/945,
                     1/np.tan(safe)-1/safe)
    second = np.where(small, -1/3-x*x/15-2*x**4/189,
                      -1/np.sin(safe)**2+1/safe**2)
    return first, second


def regular_phase_jet(theta, order=32):
    """H, H_e, H_ee at zero by differentiating F9, not fitting volumes."""
    if not 0 < theta < np.pi:
        raise ValueError("requires 0 < theta < pi")
    nodes, weights = gauss_rule(order)
    integrals = np.zeros(3)
    for sign in (-1, 1):
        A = sign*nodes[:, None, None]/2
        radius = 0.5-np.abs(A)
        B1 = radius*(2*nodes[None, :, None]-1)
        height = np.sqrt(np.maximum(0, radius*radius-B1*B1))
        eta = np.pi*(nodes[None, None, :]-0.5)
        B2 = height*np.sin(eta)
        ell = 0.5+A+B1
        r, ss = theta*ell, theta*(1-ell)
        rp, sp = B1+B2*B2/ell, -B1+B2*B2/(1-ell)
        rpp = (B1*B1+B2*B2-rp*rp)/r
        spp = (B1*B1+B2*B2-sp*sp)/ss
        lr, lrr = _log_sinc_derivatives(r)
        ls, lss = _log_sinc_derivatives(ss)
        first = lr*rp+ls*sp
        second = lrr*rp*rp+lr*rpp+lss*sp*sp+ls*spp
        for arg, ap, app in (
            (theta, (rp+sp)/2, (rpp+spp)/2),
            (0.0, (rp+sp)/2, (rpp+spp)/2),
            (r, (rp-sp)/2, (rpp-spp)/2),
            (ss, (sp-rp)/2, (spp-rpp)/2),
        ):
            l1, l2 = _log_sinc_derivatives(arg)
            first -= l1*ap/2
            second -= (l2*ap*ap+l1*app)/2
        measure = (2*np.pi*radius*height**2*np.cos(eta)**2
                   * weights[:, None, None]*weights[None, :, None]*weights[None, None, :])
        q0 = area_ratio(theta, r, ss)
        for j, value in enumerate((q0, q0*first, q0*(second+first*first))):
            integrals[j] += np.sum(measure*value)
    i0, i1, i2 = integrals
    return np.array([4*theta*theta*i0, 4*theta*i0+4*theta*theta*i1,
                     2*i0+8*theta*i1+4*theta*theta*i2])


def primitive_coefficients(a, order=32):
    """Actual c1,c2,c3 of F15, retaining both derivatives of the time weight."""
    theta = np.pi-a
    h0, h1, h2 = regular_phase_jet(theta, order)
    alpha1 = h0**-0.5
    alpha2 = -h1/(2*h0*h0)
    alpha3 = 5*h1*h1/(8*h0**3.5)-h2/(4*h0**2.5)
    root = np.sqrt(16-theta*theta)
    g0 = time_weight(theta)
    g1 = 8*np.arccosh(4/theta)-4*root
    g2 = (4*theta*theta-32)/(theta*root)
    return np.array([g0*alpha1, g0*alpha2+g1*alpha1**2/2,
                     g0*alpha3+g1*alpha1*alpha2+g2*alpha1**3/6])


def averaged_coefficients(a0=0.15, order=32, diamond_order=24):
    """Finite cubature of n1,n2,n3 in F16, using its integrable endpoint power."""
    nodes, weights = gauss_rule(order)
    total = np.zeros(3)
    for t, weight in zip(nodes, weights):
        a = a0*t**(4/3)
        total += (weight*(4/3)*a0*t**(1/3)*np.sin(a)
                  * primitive_coefficients(a, diamond_order))
    return PAIR_FACTOR*total


def regular_leading(theta):
    """Independent one-dimensional H(a,0) from the lightfront marginal, F12."""
    return np.pi*theta*theta*quad(
        lambda ell: ell*(1-ell)*area_ratio(theta, theta*ell, theta*(1-ell)),
        0, 1, epsabs=2e-11)[0]


def transition_profile(S):
    """F(S) from F6, splitting at the moving angular opening."""
    if S <= -1:
        return 0.0
    phi_max = np.pi if S >= 1 else np.arccos(-S)
    return antipodal_coefficient()/np.pi*quad(
        lambda phi: max(0, S+np.cos(phi))**1.5, 0, phi_max,
        epsabs=2e-11, epsrel=2e-11)[0]


def transition_sector_coefficient(s0, s1):
    """Q of F19, not a complete-action coefficient."""
    if not -1 < s0 < s1:
        raise ValueError("requires -1 < s0 < s1")
    return PAIR_FACTOR*time_weight(np.pi)/3*quad(
        lambda v: transition_profile(v)**-2, s0, s1,
        points=[1] if s0 < 1 < s1 else None, epsabs=1e-9)[0]


def inverse_excess(a, w, e0=0.2, order=32):
    """Actual inverse from F4, NOT the antipodal/homogeneous approximation."""
    if not 0 < a < np.pi or w < 0 or not 0 < e0 < 4-np.pi:
        raise ValueError("requires 0<a<pi, w>=0, 0<e0<4-pi")
    if w == 0:
        return 0.0
    theta = np.pi-a
    volume = lambda e: interval_volume(theta+e, theta, order=order)
    if volume(e0) < w*w:
        raise ValueError("phase exceeds the fixed excess cap")
    return brentq(lambda e: volume(e)-w*w, 0, e0, xtol=2e-13)


def cut_primitive(w, a0=0.15, order=16, volume_order=32):
    """Actual N(w) of F14 for small w; resolves the a~w^(4/3) region.

    A change of integration variable is a quadrature device, not a
    density-dependent geometric cutoff. The full fixed [0,a0] is retained.
    """
    if w == 0:
        return 0.0
    if not w > 0 or not 0 < a0 < 0.5:
        raise ValueError("requires w>=0 and 0<a0<0.5")
    nodes, weights = gauss_rule(order)
    # Integrable a^(-1/4) bound is flattened by a=a0*t^(4/3).
    aa = a0*nodes**(4/3)
    total = 0.0
    for a, weight, t in zip(aa, weights, nodes):
        excess = inverse_excess(a, w, order=volume_order)
        theta = np.pi-a
        inner = quad(lambda e: time_weight(theta+e), 0, excess, epsabs=1e-13)[0]
        total += weight*(4/3)*a0*t**(1/3)*np.sin(a)*inner
    return PAIR_FACTOR*total


def check_focusing_identities():
    """Symbolic coefficients/moments; finite algebra, not F11/F16 proofs."""
    beta = s.symbols("beta", positive=True)
    polynomial = (1-9*(beta+1)+8*(beta+1)*(beta+2)
                  -s.Rational(4, 3)*(beta+1)*(beta+2)*(beta+3))
    factored = -s.Rational(4, 3)*beta*(beta-s.Rational(1, 2))*(beta+s.Rational(1, 2))
    assert s.expand(polynomial-factored) == 0
    assert factored.subs(beta, 1) == -1
    h0 = s.symbols("h0", positive=True)
    h1, h2, w = s.symbols("h1 h2 w")
    e = (w/s.sqrt(h0)-h1*w*w/(2*h0*h0)
         +(5*h1*h1/(8*h0**s.Rational(7, 2))-h2/(4*h0**s.Rational(5, 2)))*w**3)
    assert s.series(e*e*(h0+h1*e+h2*e*e/2)-w*w, w, 0, 5).removeO().expand() == 0
    print("PASS: #139 real signed moments and inverse cubic coefficients")


if __name__ == "__main__":
    check_focusing_identities()
