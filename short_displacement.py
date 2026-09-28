"""Short-displacement diagnostics for #66, not a proof or a replacement action.

All cutoffs are fixed geometric cutoffs v=s+|b|<delta. The kernel stays signed.
Analytic formulae are derived in notes/curved-face-stability.md. float64 order
refinement is not a certified error bound, especially after bulk cancellation.
"""

import math

import numpy as np

from two_face_diagnostics import (
    AxialCap, C_INTERVAL, NORMALIZATION, axial_overlap, bdg_kernel, gauss_rule,
    quadrature, _positive,
)


def short_monomials(sigma, delta):
    """Integrals of j*(1,s,s^2,r^2) from sqrt(sigma) to delta; no sphere mass."""
    _positive(delta, "delta")
    if not math.isfinite(sigma) or sigma < 0:
        raise ValueError("sigma must be finite and nonnegative")
    if sigma >= delta**2:
        return np.zeros(4)
    # Dimensionless expressions avoid powers of two independent small scales.
    x = sigma / delta**2
    if x > 0.8:
        # The closed forms subtract through fifth order at x=1. Evaluate the
        # same positive rational integrals on a tiny fixed interval instead;
        # factor v^2-x to avoid cancellation even at the nearest float to 1.
        nodes, weights = gauss_rule(12)
        root = math.sqrt(x)
        width = (1-x)/(1+root)
        u = width*(nodes+1)/2
        v = root+u
        r = u*(v+root)/(2*v)
        s = (v*v+x)/(2*v)
        jac = r*r/(2*v)
        return np.array([scale*width/2*math.fsum(weights*jac*monomial)
                         for scale, monomial in zip(
                             (delta**2, delta**3, delta**4, delta**4), (1, s, s*s, r*r))])
    logx = math.log(x) if x else 0.0
    return np.array([
        delta**2 * (1 - x*x + 2*x*logx) / 16,
        delta**3 * (1 - x)**3 / 48,
        delta**4 * (1 - x**4 + 4*x*x*logx) / 128,
        delta**4 * (1 - 8*x + 8*x**3 - x**4 - 12*x*x*logx) / 128,
    ])


def axial_jet(cap, order=32, *, weight=None, weight_prime=None):
    """Angular quadratic jet derived from the actual axial positive-part overlap.

    The returned coefficients multiply (1,s,s^2,r^2) AFTER sphere integration.
    They do not use joint_geometry or a fitted high-density action value.
    Optional weights are smooth functions of x_1 on the fixed closed cap.
    """
    if not isinstance(cap, AxialCap):
        raise TypeError("axial_jet requires AxialCap")
    a, b, c = cap.axes
    w = (lambda x: np.ones_like(x)) if weight is None else weight
    wp = (lambda x: np.zeros_like(x)) if weight is None else weight_prime
    if wp is None:
        raise ValueError("supply weight_prime with weight")
    integral = lambda f: quadrature(f, [-a, 0, a], order)
    h = lambda x: cap.depth * (1 - (x/a)**2)
    p = cap.shift_prime
    hessian = cap.shift_second
    factor = math.pi*b*c / (2*cap.depth)
    volume = factor * integral(lambda x: w(x)*h(x)**2)
    linear_t = -2*factor * integral(lambda x: w(x)*h(x))
    quadratic_t = factor * integral(w)
    quadratic_axial = factor * integral(lambda x: w(x)*(p(x)**2 + h(x)*hessian(x)))
    # Spatial fibre volume = pi*b*c*(1-(x/a)^2), not the height integral.
    derivative = math.pi*b*c * integral(lambda x: wp(x)*p(x)*(1-(x/a)**2))
    laplacian = math.pi*b*c * integral(lambda x: w(x)*hessian(x)*(1-(x/a)**2))
    angular = np.array([4*math.pi*volume, 4*math.pi*linear_t,
                        4*math.pi*quadratic_t, 4*math.pi*quadratic_axial/3])
    coefficient = (angular[2] - 3*angular[3]) / (2*math.pi)
    return {"weighted_volume": volume, "angular": angular, "single_face_laplacian": laplacian,
            "short_limit_coefficient": coefficient, "cutoff_derivative": derivative,
            "joint_coefficient": coefficient - derivative}


def axial_short_density(cap, sigma, delta, order=20, *, weight=None, beta=0.0):
    """Independent (v, direction, source x_1) short overlap integral.

    For a planar cap, beta optionally evaluates the actual Lorentz-boosted
    overlap using the inverse boost, with the cutoff in the LAB frame. This is
    distinct from boosting a cutoff along with the region. Nonplanar boosts
    are deliberately not implemented here.
    """
    short_monomials(sigma, delta)  # Validate even when the support is empty.
    gauss_rule(order)
    if not math.isfinite(beta) or abs(beta) >= 1:
        raise ValueError("require |beta| < 1")
    if beta and (cap.bend or weight is not None):
        raise ValueError("boost diagnostic requires an unweighted planar cap")
    if sigma >= delta**2:
        return 0.0
    nodes, weights = gauss_rule(order)
    gamma = 1/math.sqrt(1-beta*beta)

    def integrand(vs):
        result = []
        for v in vs:
            s, r = (v+sigma/v)/2, (v-sigma/v)/2
            if beta:
                # Exact planar covariogram, evaluated at inverse-boosted time.
                rest_time = gamma*(s-beta*r*nodes)
                overlap = cap.volume*np.maximum(0, 1-rest_time/cap.depth)**2.5
            else:
                overlap = [axial_overlap(cap, s, r*mu, order, weight=weight) for mu in nodes]
            result.append(2*math.pi*math.fsum(weights*overlap)*(v-sigma/v)**2/(8*v))
        return np.array(result)

    return quadrature(integrand, [math.sqrt(sigma), delta], order)


def jet_short_action(angular, rho, delta, order=48):
    """Finite-density action of a quadratic overlap MODEL, not of a region.

    Retains all four monomial cutoff terms and the original signed kernel.
    The numerical Gaussian range stops at z=10, or the earlier geometric
    endpoint. Useful for normalization/power diagnostics, never as a curved
    region evaluator or a certified quadrature/tail error bound.
    """
    _positive(rho, "rho")
    _positive(delta, "delta")
    angular = np.asarray(angular, dtype=float)
    if angular.shape != (4,) or not np.all(np.isfinite(angular)):
        raise ValueError("require four finite angular coefficients")
    scale = math.sqrt(C_INTERVAL*rho)
    end = min(10.0, scale*delta**2)
    # z=w^2 softens the sigma*log(sigma) endpoint. Kernel root panels retain signs.
    roots = np.sqrt(np.sort(np.roots([-4/3, 8, -9, 1])))
    panels = [0, math.sqrt(end)] + [math.sqrt(z) for z in (*roots, 1, 2, 4, 6, 8) if z < end]
    pair = quadrature(lambda ws: np.array([
        2*w*bdg_kernel(w**4)*float(angular @ short_monomials(w*w/scale, delta))
        for w in ws]), panels, order)
    point = NORMALIZATION*math.sqrt(rho)*angular[0]/(4*math.pi)
    return point-NORMALIZATION*rho/math.sqrt(C_INTERVAL)*pair
