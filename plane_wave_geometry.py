"""Finite diagnostics for PW1--PW10, not a uniform estimate or certificate.

Coordinates are (u, v, X1, X2). The profile returns the physical positive
2x2 transverse metric G(u), not a conformal density or a phase coefficient.
Global G-SS/containment hypotheses are mathematical obligations, not inferred
from these finite quadratures.
"""

import numpy as np
from numpy.polynomial.legendre import leggauss


def _rule(order):
    if not isinstance(order, int) or order < 2:
        raise ValueError("quadrature order must be an integer >= 2")
    x, w = leggauss(order)
    return (x+1)/2, w/2


def _metric(profile, u):
    g = np.asarray(profile(float(u)), dtype=float)
    if (g.shape != (2, 2) or not np.all(np.isfinite(g))
            or not np.allclose(g, g.T, rtol=0, atol=1e-13)
            or np.min(np.linalg.eigvalsh(g)) <= 0):
        raise ValueError("profile must return a finite symmetric positive matrix")
    return g


def _endpoints(source, target):
    p, q = np.asarray(source, float), np.asarray(target, float)
    if p.shape != (4,) or q.shape != (4,) or not np.all(np.isfinite([p, q])):
        raise ValueError("endpoints must be finite four-vectors")
    return p, q


def average_inverse(profile, u, length, order=24):
    """PW6 average, with no division by length; zero/negative length allowed."""
    if not np.isfinite(u) or not np.isfinite(length):
        raise ValueError("finite u and length required")
    nodes, weights = _rule(order)
    return sum(w*np.linalg.inv(_metric(profile, u+length*t))
               for t, w in zip(nodes, weights))


def geometric_phase(source, target, profile, order=24):
    """Q is derived from the path energy, not obtained by inverting a volume."""
    p, q = _endpoints(source, target)
    length = q[0]-p[0]
    a = average_inverse(profile, p[0], length, order)
    d = q[2:]-p[2:]
    return float(2*length*(q[1]-p[1])-d@np.linalg.solve(a, d))


def phase_factor(profile, u, length, order=24):
    """Exact divided-volume formula PW7, evaluated by finite quadrature.

    The smooth coefficient extends to length <= 0; that extension alone is
    NOT a future-interval volume. No cutoff excludes the length=0 direction.
    """
    nodes, weights = _rule(order)
    a = average_inverse(profile, u, length, order)
    result = 0.
    for t, w in zip(nodes, weights):
        s = u+t*length
        a0 = average_inverse(profile, u, t*length, order)
        a1 = average_inverse(profile, s, (1-t)*length, order)
        factor = np.sqrt(np.linalg.det(_metric(profile, s))
                         * np.linalg.det(a0)*np.linalg.det(a1)/np.linalg.det(a))
        result += w*t*(1-t)*factor
    return float(np.pi*result/4)


def interval_volume(source, target, profile, order=24):
    """PW7 on actual future intervals; zero for unrelated/parallel-null pairs."""
    p, q = _endpoints(source, target)
    length = q[0]-p[0]
    if length <= 0:
        return 0.
    phase = geometric_phase(p, q, profile, order)
    if phase <= 0:
        return 0.
    return phase**2*phase_factor(profile, p[0], length, order)


def lens_point(source, target, profile, t, z, r, order=24):
    """PW4 physical point and pullback volume per dt d^2z dr.

    This slice map is NOT claimed uniformly differentiable as the u gap
    vanishes. PW7, rather than that claim, handles the parallel-null collar.
    """
    p, q = _endpoints(source, target)
    z = np.asarray(z, float)
    if (not np.isfinite(t) or not 0 < t < 1 or not np.isfinite(r) or not 0 <= r <= 1
            or z.shape != (2,) or not np.all(np.isfinite(z)) or z@z > 1):
        raise ValueError("requires 0<t<1, disk z and 0<=r<=1")
    length = q[0]-p[0]
    if length <= 0:
        raise ValueError("slice map requires positive u gap")
    a = average_inverse(profile, p[0], length, order)
    b = length*a
    d = q[2:]-p[2:]
    e = q[1]-p[1]-d@np.linalg.solve(b, d)/2
    if e <= 0:
        raise ValueError("slice map requires a chronological pair")
    s = p[0]+t*length
    a0 = average_inverse(profile, p[0], t*length, order)
    a1 = average_inverse(profile, s, (1-t)*length, order)
    # Keep factor order: the profile's eigendirections need not commute.
    c = length*t*(1-t)*(a0@np.linalg.solve(a, a1))
    c = (c+c.T)/2  # Roundoff symmetry only, not a geometric assumption.
    values, vectors = np.linalg.eigh(c)
    root = (vectors*np.sqrt(values))@vectors.T
    xc = p[2:]+t*a0@np.linalg.solve(a, d)
    x = xc+np.sqrt(2*e)*(root@z)
    dx = x-p[2:]
    v = p[1]+dx@np.linalg.solve(t*length*a0, dx)/2+r*e*(1-z@z)
    point = np.array([s, v, *x])
    jacobian = (2*e**2*length*np.sqrt(np.linalg.det(_metric(profile, s)))
                * np.sqrt(np.linalg.det(c))*(1-z@z))
    return point, float(jacobian)


def cosine_profile(epsilon):
    """The non-conformal deformation in section 6, with a global margin."""
    if not np.isfinite(epsilon) or abs(epsilon) >= 1:
        raise ValueError("requires finite |epsilon|<1")
    return lambda u: np.diag([(1+epsilon*np.cos(u))**2, 1.])


def joint_target(s, eta, epsilon, order=48):
    """PW10 independent joint integral; scalar bulk is zero in this class."""
    if (not all(np.isfinite([s, eta, epsilon])) or s <= 0 or eta <= 0
            or abs(epsilon) >= 1 or eta+s >= 1-abs(epsilon)):
        raise ValueError("requires positive s, eta and eta+s<1-|epsilon|")
    nodes, weights = _rule(order)
    z = 2*nodes-1
    a = 1+epsilon*np.cos((eta-1)*z/np.sqrt(2))
    value = a*(1-eta**2+s*s*z*z+s*s*(1-z*z)*(1+a**-2)/2)
    return float(2*np.pi/s*np.sum(weights*value))
