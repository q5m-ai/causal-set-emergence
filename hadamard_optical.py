"""Finite diagnostics for HO-4, not a certificate or full-action solver.

The variable-curvature metric is dt^2-dx^2-(1+kappa*x^2)^2*dy^2-dz^2.
Distances are computed from the actual nonlinear geodesic boundary problem;
the quadratic plane-wave formula is used only for the separate limiting check.
"""

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_bvp, quad
from scipy.optimize import brentq


def _finite(*values):
    if not all(np.all(np.isfinite(value)) for value in values):
        raise ValueError("finite data required")


def _kappa(kappa):
    _finite(kappa)
    if kappa < 0:
        raise ValueError("kappa must be nonnegative")


def _rule(order):
    if not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    nodes, weights = leggauss(order)
    return (nodes+1)/2, weights/2


def tube_radius_squared(length, excess, longitudinal):
    """HO3 Euclidean comparison envelope, not equality for a curved lens."""
    _finite(length, excess, longitudinal)
    if length <= 0 or excess < 0:
        raise ValueError("positive length and nonnegative excess required")
    s = np.asarray(longitudinal)
    value = (excess*(2*length+excess)*(s+excess/2)
             * (length+excess/2-s)/(length+excess)**2)
    return np.maximum(value, 0.)


def surface_geodesic(p, q, kappa, tolerance=2e-8):
    """Actual 2D affine geodesic for dx^2+a(x)^2 dy^2.

    Hadamard uniqueness is a written geometric fact, not inferred from BVP
    convergence. Solver failure raises, rather than returning a guessed path.
    """
    _kappa(kappa)
    p, q = np.asarray(p, float), np.asarray(q, float)
    if p.shape != (2,) or q.shape != (2,):
        raise ValueError("surface endpoints must be two-vectors")
    _finite(p, q, tolerance)
    if tolerance <= 0:
        raise ValueError("positive tolerance required")
    grid = np.linspace(0, 1, 17)
    guess = np.vstack([p[0]+(q[0]-p[0])*grid,
                       p[1]+(q[1]-p[1])*grid,
                       np.full_like(grid, q[0]-p[0]),
                       np.full_like(grid, q[1]-p[1])])

    def ode(_, state):
        x, _, vx, vy = state
        a, ap = 1+kappa*x*x, 2*kappa*x
        return np.array([vx, vy, a*ap*vy*vy, -2*ap/a*vx*vy])

    def boundary(left, right):
        return np.r_[left[:2]-p, right[:2]-q]

    solution = solve_bvp(ode, boundary, grid, guess, tol=tolerance,
                         max_nodes=2000)
    if not solution.success:
        raise RuntimeError(f"geodesic BVP failed: {solution.message}")
    return solution


def surface_distance(p, q, kappa, tolerance=2e-8):
    """Numerical physical distance; no monotone-x path assumption at a tip."""
    solution = surface_geodesic(p, q, kappa, tolerance)
    nodes, weights = _rule(24)
    x, _, vx, vy = solution.sol(nodes)
    return float(np.dot(weights, np.sqrt(vx*vx+(1+kappa*x*x)**2*vy*vy)))


def spatial_distance(p, q, kappa):
    p, q = np.asarray(p, float), np.asarray(q, float)
    if p.shape != (3,) or q.shape != (3,):
        raise ValueError("spatial endpoints must be three-vectors")
    _finite(p, q)
    return float(np.hypot(surface_distance(p[:2], q[:2], kappa), q[2]-p[2]))


def _flat_axis_clock(a, b, tau, nodes, weights):
    """Integrate z exactly in domain, quadrature in width; distances a,b >=0.

    Rationalization avoids subtracting the almost equal physical clock bounds.
    This is not an asymptotic approximation to either distance.
    """
    gap = tau-a-b
    if gap <= 0:
        return 0.
    z2 = gap*(tau+a+b)*(tau-a+b)*(tau+a-b)/(4*tau*tau)
    zmax = np.sqrt(max(z2, 0.))
    z = zmax*nodes
    da, db = np.hypot(a, z), np.hypot(b, z)
    # tau-(da+db) = 4*tau^2*(zmax^2-z^2) / two conjugate factors.
    denominator = (tau*tau-a*a-b*b-2*z*z+2*da*db)*(tau+da+db)
    width = 4*tau*tau*zmax*zmax*(1-nodes*nodes)/denominator
    return float(2*zmax*np.dot(weights, width))


def optical_volume(x0, length, excess, kappa, order=14, return_parts=False):
    """HO2 physical clock integral for axis endpoints, retaining BOTH caps.

    The three returned pieces are x<x0, x0<x<x1, x>x1; they are diagnostic
    integration sectors, not separately vanishing normalized actions.
    Reflection in y,z is an actual symmetry of this diagnostic metric.
    """
    _kappa(kappa)
    _finite(x0, length, excess)
    if length <= 0 or excess <= 0:
        raise ValueError("positive length and excess required")
    nodes, weights = _rule(order)
    zn, zw = _rule(max(order, 16))
    x1, tau = x0+length, length+excess
    sectors = [(x0-excess/2, x0), (x0, x1), (x1, x1+excess/2)]
    parts = []
    for left, right in sectors:
        total = 0.
        for u, wu in zip(nodes, weights):
            x = left+(right-left)*u
            ymax_bound = np.sqrt(tube_radius_squared(length, excess, x-x0))

            def distances(y):
                return (surface_distance([x0, 0], [x, y], kappa),
                        surface_distance([x1, 0], [x, y], kappa))

            def defect(y):
                a, b = distances(y)
                return a+b-tau

            # h >= Euclidean, so the physical root is within this envelope.
            # A tiny guard covers floating error at the flat equality case.
            ymax = brentq(defect, 0., ymax_bound*(1+2e-10),
                          xtol=2e-12, rtol=2e-12)
            inner = 0.
            for v, wv in zip(nodes, weights):
                a, b = distances(ymax*v)
                inner += wv*_flat_axis_clock(a, b, tau, zn, zw)
            total += wu*2*ymax*(1+kappa*x*x)*inner
        parts.append(float((right-left)*total))
    return tuple(parts) if return_parts else float(sum(parts))


def reference_factor(x0, length, kappa):
    """Leading V/e^2 from the Rosen reference, NOT the physical volume.

    In these coordinates t=x+e*v, y=sqrt(e)*Y, z=sqrt(e)*Z gives the exact
    rescaled metric 2 dx dv + e dv^2 - a(x)^2 dY^2 - dZ^2.
    """
    _kappa(kappa)
    _finite(x0, length)
    if length <= 0:
        raise ValueError("positive length required")

    def integral(left, right):
        return quad(lambda x: (1+kappa*x*x)**-2, left, right,
                    epsabs=1e-12, epsrel=1e-12)[0]

    full = integral(x0, x0+length)

    def integrand(s):
        b0, b1 = integral(x0, x0+s), integral(x0+s, x0+length)
        return (1+kappa*(x0+s)**2)*np.sqrt(b0*b1/full*s*(length-s)/length)

    return float(np.pi*quad(integrand, 0., length,
                            epsabs=1e-11, epsrel=1e-11)[0])


def independent_target(kappa, slope, tilt):
    """HO14: (volume, scalar bulk/2, actual SS joint), independently of phase."""
    _kappa(kappa)
    _finite(slope, tilt)
    if slope <= 0 or tilt < 0 or slope+tilt >= 1:
        raise ValueError("requires slope>0, tilt>=0 and slope+tilt<1")
    volume = 8*np.pi*slope/15*(1+kappa/7)
    bulk = -16*np.pi*kappa*slope/15

    def integrand(x):
        a = 1+kappa*x*x
        return ((1-tilt*tilt)*a
                + slope*slope/2*(a*(1+x*x)+(1-x*x)/a))

    joint = np.pi/slope*quad(integrand, -1, 1, epsabs=1e-12)[0]
    return float(volume), float(bulk), float(joint)
