"""Finite TC/NA diagnostics, not a certified asymptotic solver.

The canonical dimensional constants/kernels and actual NP weight are imported.
No production observable, geometry contract or probability API is changed.
"""

import math

import numpy as np
from scipy.integrate import quad
from scipy.special import beta, betainc, dawsn, roots_jacobi

from dimension_kernels import factor_count, interval_coefficient, kernel_polynomial


def matching_tail(d, lower):
    """TC5's integrable envelope, evaluated as an incomplete beta integral."""
    m = factor_count(d)
    if not math.isfinite(lower) or lower < 0:
        raise ValueError("finite nonnegative lower endpoint required")
    a, b = (d+2)/d, (2*m-d)/d
    if lower == 0:
        fraction = 1.0
    else:
        exponent = d*math.log(lower)
        fraction = (math.exp(-exponent)/(1+math.exp(-exponent)) if exponent >= 0
                    else 1/(1+math.exp(exponent)))
    return float(beta(b, a)*betainc(b, a, fraction)/d)


def closing_model_parts(d, rho, height, cutoff=0.7, slope=0.3, cosine=0.4, order=40):
    """TC4 on the actual flat normal-wedge model, with a physical time split.

    Return (original positive part, smooth extension, closing correction).
    The phase is the true flat interval c_d*ell^d*xi^(d/2). This local model
    tests the domain/Jacobian identity only; it is NOT a complete-action test.
    """
    factor_count(d)
    if (not all(math.isfinite(x) for x in (rho, height, cutoff, slope, cosine))
            or rho <= 0 or cutoff <= 0 or abs(slope) >= 1 or abs(cosine) > 1
            or isinstance(order, bool) or not isinstance(order, int) or order < 4):
        raise ValueError("positive density/cutoff, strict slope and valid quadrature required")
    if height <= 0:
        return 0.0, 0.0, 0.0
    nodes, weights = roots_jacobi(order, (d-3)/2, 0)
    xis = (nodes+1)/2
    weights /= 2**((d-1)/2)
    coefficients = np.array([float(x) for x in reversed(kernel_polynomial(d).as_poly().all_coeffs())])
    c = float(interval_coefficient(d))
    totals = np.zeros(3)
    for xi, weight in zip(xis, weights):
        speed = 1+slope*math.sqrt(1-xi)*cosine
        root = height/speed

        def integrand(ell):
            z = c*rho*ell**d*xi**(d/2)
            return (ell**(d-1)*(height-ell*speed)**2
                    * np.polynomial.polynomial.polyval(z, coefficients)*math.exp(-z))

        original = quad(integrand, 0, min(cutoff, root), epsabs=2e-12)[0]
        smooth = quad(integrand, 0, cutoff, epsabs=2e-12)[0]
        # Independently resolve closing first, including d ell = root d r.
        error = (quad(lambda r: root*integrand(root*r), 1, cutoff/root,
                      epsabs=2e-12)[0] if root < cutoff else 0.0)
        totals += weight*np.array([original, smooth, error])
    return tuple(totals)


def null_closing_phase(xi, cosine):
    """NA1; no single inverse is supplied across its two physical branches."""
    if not 0 < xi <= 1 or not -1 <= cosine <= 1:
        raise ValueError("requires 0 < xi <= 1 and a unit-direction cosine")
    # Stable for cosine=1 and small xi.
    b = math.sqrt(1-xi)
    speed = (1-cosine)+cosine*xi/(1+b)
    return xi/(speed*speed)


def null_displacement(v, eta, transverse):
    """NA2 in original time/space coordinates, retaining the physical gap."""
    y = np.asarray(transverse, dtype=float)
    if (y.ndim != 1 or not np.all(np.isfinite(y)) or not math.isfinite(v)
            or not math.isfinite(eta) or v <= 0 or eta < 0):
        raise ValueError("positive v, nonnegative eta and a finite transverse vector required")
    w = eta+float(y@y)/v
    return np.concatenate(([0.5*(v+w), 0.5*(v-w)], y))


def flat_2d_round_cap_action(rho, duration=1.0):
    """Exact full-partner ND response integrated by divergence; not a fit.

    With x=T*sqrt(rho/2), the complete action is 4*x*Dawson(x).
    This also checks TC's counting atom for two just-touching caps.
    """
    if (not math.isfinite(rho) or not math.isfinite(duration)
            or rho <= 0 or duration <= 0):
        raise ValueError("finite positive density and duration required")
    x = duration*math.sqrt(rho/2)
    return float(4*x*dawsn(x))
