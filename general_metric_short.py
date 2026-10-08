"""#150 geometric/analytic regressions, NOT proofs of general short limits.

See notes/general-metric-short.md and its signed-remainder continuation for the
written proofs. Finite diagnostics do not certify those estimates or replace
independent review. Canonical normalization is imported, not redefined.
No production action API is changed.
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
    *model* coefficient and signed compensating flux. The geometric target is
    raw_model - flux, NOT raw_model + flux or an actual face/corner limit.
    The empty Gram determinant implements 2D counting.
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


def product_null_rescaled_metric(v, e, point, radius=1.0):
    """Exact null-rescaled source-normal metric of R x S^2_a x S^1.

    point=(s,r,Z1,Z2); the continuous value at e=0 is included. This evaluates
    the actual product metric, not a truncated curvature or interval model.
    """
    point = np.asarray(point, dtype=float)
    if (point.shape != (4,) or not np.all(np.isfinite(point))
            or not np.isfinite(v) or not np.isfinite(e)
            or not np.isfinite(radius) or radius <= 0):
        raise ValueError("finite rescaling data and positive sphere radius required")
    longitudinal, other, transverse, _ = point
    r2 = v*v * ((longitudinal-e*e*other)**2/4 + e*e*transverse**2)
    z2 = r2 / radius**2
    if z2 < 1e-6:
        curvature = (1/3 - 2*z2/45 + z2*z2/315 - 2*z2**3/14175) / radius**2
    else:
        curvature = (1 - np.sinc(np.sqrt(z2)/np.pi)**2) / r2
    vector = np.array([-transverse, e*e*transverse, longitudinal-e*e*other, 0.0])
    flat = np.array([[0, 0.5, 0, 0], [0.5, 0, 0, 0],
                     [0, 0, -1, 0], [0, 0, 0, -1]], dtype=float)
    return flat + curvature * v*v/4 * np.outer(vector, vector)


def product_interval_ratio(v, ratio, radius=1.0, circle_length=20.0, order=28):
    """Actual V/[c4*(uv)^2] for a nearly-null sphere-direction interval.

    Ultrastatic time Fubini integrates (T-distance0-distance1)_+ over the
    *whole* spatial lens. Sphere Fermi coordinates give its exact volume
    density cos(b/a). Both longitudinal end caps are retained. No H jet is
    substituted. The small, no-wrap diagnostic domain is checked explicitly.
    """
    if not (np.isfinite(v) and np.isfinite(ratio) and v > 0 and 0 < ratio <= 1
            and np.isfinite(radius) and np.isfinite(circle_length)
            and radius > 0 and circle_length > 0):
        raise ValueError("positive v, radius, period and ratio in (0,1] required")
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    u = v * ratio
    time, separation = (v+u)/2, (v-u)/2
    if time >= min(np.pi*radius/4, circle_length/2):
        raise ValueError("diagnostic requires a small interval with no spatial wrap")
    nodes, weights = leggauss(order)
    nodes, weights = (nodes+1)/2, weights/2
    angle = nodes[None, :] * np.pi/2
    cos_angle, sin_angle = np.cos(angle), np.sin(angle)
    coefficient = float(interval_coefficient(4))
    total = 0.0
    edges = sorted({-u/2, 0.0, separation, separation+u/2})
    for left, right in zip(edges, edges[1:]):
        ell = (left+(right-left)*nodes)[:, None]
        shape = np.maximum(0, 1-((2*ell-separation)/time)**2)
        flat_radius = np.sqrt(u*v*shape)/2

        def gap(perp):
            # Accurate local spherical distance from cos(d/a)=cos(ell/a)cos(b/a).
            b = perp * cos_angle
            z = perp * sin_angle
            def distance(longitudinal):
                haversine = (np.sin(longitudinal/(2*radius))**2
                             + np.cos(longitudinal/radius)*np.sin(b/(2*radius))**2)
                sphere = 2*radius*np.arcsin(np.sqrt(np.clip(haversine, 0, 1)))
                return np.sqrt(sphere*sphere+z*z)
            return time-distance(ell)-distance(ell-separation)

        lo = np.zeros((order, order))
        hi = np.full((order, order), 2.0)
        if np.any(gap(flat_radius*hi) >= 0):
            raise ValueError("transverse root left the verified quadrature bracket")
        for _ in range(48):
            mid = (lo+hi)/2
            positive = gap(flat_radius*mid) > 0
            lo, hi = np.where(positive, mid, lo), np.where(positive, hi, mid)
        root = (lo+hi)/2
        # Integrate transverse radius using the actual root, with dimensionless
        # gap/u to avoid dividing a small volume by another small volume.
        inner = np.zeros_like(root)
        for eta, weight in zip(nodes, weights):
            perp = flat_radius*root*eta
            inner += weight*eta*(gap(perp)/u)*np.cos(perp*cos_angle/radius)
        total += np.sum(weights[:, None]*weights[None, :] * (right-left)
                        * (2*np.pi) * shape*root*root*inner) / (4*coefficient*v)
    return float(total)


def lapse_face_gap(s, depth, v, ratio, lapse_slope=0.4):
    """Actual source-dependent geodesic exit gap in a flat lapse chart.

    g=(1+b*t)^2 dt^2-dz^2, proper time t+b*t^2/2, future graph
    f(z)=0.1*z+0.05*z^2, and height coordinate s=0.3*z. Return d,d_s,d_depth.
    This coordinate regression tests the moving-source terms, not a new pilot.
    """
    z, k = s/0.3, 0.3
    f = lambda z: 0.1*z + 0.05*z*z
    df = lambda z: 0.1 + 0.1*z
    t = f(z)-depth
    lapse = 1+lapse_slope*t
    if not (lapse > 0 and v > 0 and 0 <= ratio <= 1):
        raise ValueError("positive lapse/v and causal ratio required")
    proper_time, displacement = v*(1+ratio)/2, v*(1-ratio)/2
    future_lapse_squared = lapse*lapse+2*lapse_slope*proper_time
    if not np.isfinite(future_lapse_squared) or future_lapse_squared <= 0:
        raise ValueError("geodesic must stay in the positive-lapse chart")
    time = 2*proper_time/(np.sqrt(future_lapse_squared)+lapse)
    time_t = -lapse_slope*time/(lapse+lapse_slope*time)
    gap = time + f(z)-f(z+displacement)
    ds = (time_t*df(z) + df(z)-df(z+displacement))/k
    return gap, ds, -time_t
