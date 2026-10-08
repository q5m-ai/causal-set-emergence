"""Bounded #150 geometry/model diagnostics, NOT general short-limit producers.

See notes/general-metric-short.md for the proved locality/finite-density results
and the still-unproved null-edge, face and joint signed remainders. Canonical
normalization is imported, not redefined. No production action API is changed.
"""

import numpy as np
import sympy as s
from numpy.polynomial.legendre import leggauss

from dimension_kernels import interval_coefficient


def rest_diamond_moments(d):
    """Normalized t^2 and one spatial-coordinate square, unit proper duration.

    Compute the section beta integrals rather than fitting interval coefficients.
    Ordinary S^(d-2) cancels between numerator and denominator, also for d=2.
    """
    interval_coefficient(d)  # Validate physical dimension using the canonical API.
    time = s.Rational(d, 4) * s.factorial(2) * s.factorial(d - 1) / s.factorial(d + 2)
    space = s.Rational(d, 4 * (d + 1) * (d + 2))
    return time, space


def interval_corrections(d, ric_tt, scalar):
    """Separate density and cone contributions to V/(c_d*T^d), at order T^2.

    #90 sign convention. The theorem is uniform on compact timelike-direction
    families only; this function does not certify a null-edge remainder.
    """
    time, space = rest_diamond_moments(d)
    density = (time * ric_tt + space * (ric_tt - scalar)) / 6
    cone = -s.sympify(ric_tt) / 24
    return s.simplify(density), cone


def model_curvature_responses(d):
    """R coefficients of endpoint density, directional phase, scalar phase.

    Responses of the entire second-order *model*, not the actual integral.
    Tensor K response is 2*g^-1; Z*K' multiplies it by -(1+2/d).
    """
    ric, scalar = s.symbols("ric scalar")
    density, cone = interval_corrections(d, ric, scalar)
    interval = s.expand(density + cone)
    multiplier = -(1 + s.Rational(2, d))
    endpoint = s.Rational(1, 3)
    directional = s.simplify(2 * multiplier * interval.coeff(ric))
    scalar_phase = s.simplify(2 * d * multiplier * interval.coeff(scalar))
    return endpoint, directional, scalar_phase


def joint_geometry(metric, future_slope, height_gradient):
    """Independent normal/Gram geometry at a joint in a temporal graph chart.

    Unit spatial reference area; no field factors. Also return the raw tangent
    *model* coefficient and compensating flux. Their sum is geometry, NOT an
    actual face/corner limit. The empty Gram determinant implements 2D counting.
    """
    g = np.asarray(metric, dtype=float)
    p = np.asarray(future_slope, dtype=float)
    a = np.asarray(height_gradient, dtype=float)
    if (g.ndim != 2 or g.shape[0] != g.shape[1] or g.shape[0] < 2
            or p.shape != (g.shape[0] - 1,) or a.shape != p.shape
            or not np.all(np.isfinite(g)) or not np.all(np.isfinite(p))
            or not np.all(np.isfinite(a)) or not np.allclose(g, g.T)):
        raise ValueError("finite symmetric metric and matching spatial covectors required")
    eigenvalues = np.linalg.eigvalsh(g)
    if not (eigenvalues[-1] > 0 and np.all(eigenvalues[:-1] < 0)):
        raise ValueError("signature (+,-,...,-) required")
    k = np.linalg.norm(a)
    if k == 0:
        raise ValueError("transverse joint requires nonzero height gradient")
    inverse = np.linalg.inv(g)
    plus = np.r_[1.0, -p]
    minus = np.r_[1.0, -(p - a)]
    sp, sm = plus @ inverse @ plus, minus @ inverse @ minus
    c = minus @ inverse @ plus
    if not (inverse[0, 0] > 0 and sp > 0 and sm > 0
            and (inverse @ plus)[0] > 0 and (inverse @ minus)[0] > 0):
        raise ValueError("temporal chart and future timelike conormals required")
    discriminant = c * c - sp * sm
    if discriminant <= 0:
        raise ValueError("positive transverse angle required")
    w = np.sqrt(abs(np.linalg.det(g)))
    # Euclidean orthonormal basis of ker(dh) in the spatial reference chart.
    _, _, vh = np.linalg.svd(a[None, :], full_matrices=True)
    spatial = vh[1:].T
    tangents = np.vstack((p @ spatial, spatial))
    gram = -tangents.T @ g @ tangents
    area = np.sqrt(np.linalg.det(gram))  # det of the 0x0 matrix is one.
    b = plus @ inverse @ np.r_[0.0, a]
    return {
        "area": area,
        "coarea": w * np.sqrt(discriminant) / k,
        "coth": c / np.sqrt(discriminant),
        "target": area * c / np.sqrt(discriminant),
        "raw_model": w * sp / k,
        "flux": -w * b / k,
        "face_vector": w * (inverse @ plus)[1:],
    }


def ultrastatic_rest_volume(duration, radius=1.0, circle_length=20.0, order=48):
    """Actual rest interval on R x S^2_a x S^1_L, below the spatial cut radii.

    Time Fubini of spatial metric balls, NOT the RNC truncated expansion.
    Endpoints have identical spatial coordinate. The normalized sine expression
    avoids cancellation when extracting the small-duration quadratic correction.
    """
    if not (radius > 0 and circle_length > 0
            and 0 < duration < min(2 * np.pi * radius, circle_length)):
        raise ValueError("positive duration below both spatial cut radii required")
    if isinstance(order, bool) or not isinstance(order, int) or order < 2:
        raise ValueError("quadrature order must be an integer >= 2")
    nodes, weights = leggauss(order)
    u, weights = (nodes + 1) / 2, weights / 2
    theta = u[None, :] * np.pi / 2
    argument = duration * u[:, None] * np.sin(theta) / (2 * radius)
    ratio = 12 * np.sum(
        weights[:, None] * weights[None, :] * u[:, None]**3
        * np.sin(theta) * np.cos(theta)**2 * np.pi / 2
        * np.sinc(argument / np.pi)
    )
    return np.pi / 24 * duration**4 * ratio
