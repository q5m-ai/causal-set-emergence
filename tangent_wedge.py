"""Independent finite-density diagnostics for the regulated tangent wedge.

These are numerical checks, not proofs. The observable weights the first
endpoint only. See notes/regulated-tangent-wedge.md for the finite regulator,
complete-future argument, and subtraction of the artificial complement.
All values are per unit integral of the tangential test weight.
"""

from mpmath import mp
import numpy as np
from scipy.special import roots_legendre

from calculations import plane_kernel


def _parameters(rho, slope, radius, power):
    rho, slope, radius = map(mp.mpf, (rho, slope, radius))
    if not all(mp.isfinite(x) for x in (rho, slope, radius)):
        raise ValueError("parameters must be finite")
    if rho <= 0 or radius <= 0 or not 0 < slope < 1:
        raise ValueError("require rho > 0, radius > 0, and 0 < slope < 1")
    if isinstance(power, bool) or not isinstance(power, int) or power < 1:
        raise ValueError("power must be a positive integer (continuous cutoff)")
    return rho, slope, radius


def profile_action(rho, slope, radius=1, power=1):
    """Signed G integral with cutoff (1-r/radius)**power on [0,radius].

    Scaling is applied before quadrature. No negative tail inside the cutoff
    is omitted and no asymptotic answer is inserted into the evaluator.
    """
    rho, slope, radius = _parameters(rho, slope, radius, power)
    upper = slope * radius * mp.root(rho, 4)
    points = [mp.mpf(0)]
    value = mp.mpf(1)
    while value < upper:
        points.append(value)
        value *= 2
    points.append(upper)
    return mp.quad(
        lambda u: (1 - u / upper) ** power * plane_kernel(u), points
    ) / slope


def pair_action(rho, slope, radius=1, power=1, order=64):
    """Direct original signed kernel, without F, G, or their derivatives.

    Integrating the first endpoint's depth and normal coordinate gives
    D(t) = k*R**2/((p+1)*(p+2)) * (1-t/(k*R))**(p+2).
    The full future displacement has 0 <= radial <= time <= k*R.
    Tensor Gauss-Legendre quadrature retains the entire near-null range.
    Refinement is a diagnostic, not a certified quadrature error bound.
    """
    rho, slope, radius = _parameters(rho, slope, radius, power)
    if isinstance(order, bool) or not isinstance(order, int) or order < 2:
        raise ValueError("order must be an integer >= 2")
    rho, slope, radius = map(float, (rho, slope, radius))
    if not np.isfinite([rho, slope, radius]).all():
        raise ValueError("pair quadrature requires float-representable parameters")
    nodes, weights = roots_legendre(order)
    nodes, weights = (nodes + 1) / 2, weights / 2
    duration = slope * radius
    t = duration * nodes[:, None]
    radial = t * nodes[None, :]
    argument = np.pi * rho * (t**2 - radial**2) ** 2 / 24
    kernel = (1 - 9 * argument + 8 * argument**2 - 4 * argument**3 / 3) * np.exp(-argument)
    point = slope * radius**2 / ((power + 1) * (power + 2))
    depth_weight = point * (1 - t / duration) ** (power + 2)
    pair = 4 * np.pi * duration * np.sum(
        weights[:, None] * weights[None, :] * t * radial**2 * kernel * depth_weight
    )
    return 4 / np.sqrt(6) * np.sqrt(rho) * (point - rho * pair)


def regulator_height(spatial, slope, height):
    """The independent bounded tent h=min(k*r, H-k*|x|_infinity)."""
    spatial = np.asarray(spatial, dtype=float)
    if spatial.shape != (3,) or not np.isfinite(spatial).all():
        raise ValueError("spatial must have three finite coordinates")
    if not np.isfinite([slope, height]).all() or not 0 < slope < 1 or height <= 0:
        raise ValueError("require finite 0 < slope < 1 and height > 0")
    return min(slope * spatial[0], height - slope * np.max(np.abs(spatial)))
