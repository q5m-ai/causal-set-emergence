"""Finite diagnostics for NF/NT/NP, not production action APIs or limit proofs.

NF uses a whole past set and genuine dimensional kernels. NP changes the
endpoint region, not the physical seven-dimensional sphere/product interval.
All numerical integrals below are diagnostics; the remainder proofs are written.
"""

from itertools import combinations

import numpy as np
from scipy.integrate import quad


def nonempty_subsets(count):
    """Every inclusion-exclusion term, with no multiplicity truncation."""
    if isinstance(count, bool) or not isinstance(count, int) or count < 1:
        raise ValueError("a positive integer number of sets is required")
    for size in range(1, count + 1):
        for indices in combinations(range(count), size):
            yield indices, (-1) ** (size + 1)


def cone_memberships(points, centers):
    """Strict pasts of the simultaneous tips (0, center), not route weights."""
    points, centers = np.asarray(points, dtype=float), np.asarray(centers, dtype=float)
    if (points.ndim != 2 or centers.ndim != 2 or not len(centers)
            or points.shape[1] != centers.shape[1] + 1
            or not np.all(np.isfinite(points)) or not np.all(np.isfinite(centers))):
        raise ValueError("finite endpoint/center arrays of compatible dimension required")
    return points[:, :1] < -np.linalg.norm(points[:, None, 1:] - centers[None], axis=2)


def closed_causal_order(points):
    """Actual Minkowski closed order; includes null pairs and the diagonal."""
    points = np.asarray(points, dtype=float)
    dt = points[None, :, 0] - points[:, None, 0]
    dx2 = np.sum((points[None, :, 1:] - points[:, None, 1:]) ** 2, axis=-1)
    return (dt >= 0) & (dt * dt >= dx2)


def layers_on_subset(order, selected, max_layer=3):
    """Count actual ordered exclusive layers on one restricted configuration."""
    order, selected = np.asarray(order, dtype=bool), np.asarray(selected, dtype=bool)
    indices = np.flatnonzero(selected)
    layers = np.zeros(max_layer + 1, dtype=int)
    for i in indices:
        for j in indices:
            if i != j and order[i, j]:
                interior = selected & order[i] & order[:, j]
                interior[i] = interior[j] = False
                k = int(np.count_nonzero(interior))
                if k <= max_layer:
                    layers[k] += 1
    return layers


def null_overlap(tau, z, duration=4.0):
    """NP3: actual (t,z) source measure, with both endpoint masks."""
    if not np.isfinite(duration) or duration <= 0 or not np.isfinite(tau) or tau < 0:
        raise ValueError("finite nonnegative gap and positive duration required")
    if not np.isfinite(z) or abs(z) > tau:
        raise ValueError("a causal projected displacement is required")
    return 0.5 * max(0.0, duration - tau - z) * max(0.0, duration - tau + z)


def _validate_u(u, duration):
    if not np.isfinite(duration) or duration <= 0 or not np.isfinite(u) or not 0 <= u <= duration:
        raise ValueError("requires positive T and 0 <= u <= T")


def null_time_weight(u, duration=4.0):
    """NP3 via a positive integral; stable near closing (no fitted asymptotics)."""
    _validate_u(u, duration)
    if u == 0 or u == duration:
        return 0.0

    def bracket(v):
        # B/v^2 = (exp(2a)+1)*a - exp(2a)+1, a=log(T/v).
        # Its convergent series avoids cancellation of the third-order zero.
        a = np.log(duration / v)
        if a < 0.05:
            term = 4.0 * a**3 / 6.0
            result = term
            for k in range(4, 18):
                term *= 2.0 * a * (k - 2) / (k * (k - 3))
                result += term
            return v*v*result
        return (duration**2 + v*v)*a - duration**2 + v*v

    # v^2=u^2+r^2 removes the square-root at the lower endpoint.
    top = np.sqrt(duration**2 - u*u)
    return 4*np.pi*u*quad(lambda r: r*r*bracket(np.hypot(u, r)),
                         0, top, epsabs=2e-12, epsrel=2e-12)[0]


def null_time_weight_closed(u, duration=4.0):
    """NP4 exact expression; cancellation near T makes the positive form safer."""
    _validate_u(u, duration)
    r = np.sqrt(max(0.0, duration**2-u*u))
    return 4*np.pi*u*(4*r**5/225 - 8*u*u*r**3/45 - 7*u**4*r/15
                     + u**3*(5*duration**2+2*u*u)/15*np.arccos(u/duration))


def null_time_weight_unreduced(u, duration=4.0, cutoff=None, short=False):
    """Independent original flat-partner integral of u/tau times H_T.

    Integrate the actual z displacement and transverse radius. The actual
    temporal mask, rather than u<delta alone, decides the short piece.
    """
    _validate_u(u, duration)
    if cutoff is not None and (not np.isfinite(cutoff) or not 0 < cutoff < duration):
        raise ValueError("requires 0 < cutoff < T")
    if short and cutoff is None:
        raise ValueError("a short weight needs a cutoff")
    if u == 0 or u == duration:
        return 0.0
    top = np.sqrt(duration**2 - u*u)
    if short:
        top = np.sqrt(max(0.0, cutoff**2-u*u))

    def radial(r):
        v = np.hypot(u, r)
        ztop = (duration**2-v*v)/(2*duration)
        split = np.sqrt(max(0.0, cutoff**2-v*v)) if cutoff is not None else 0.0
        lo, hi = (0.0, ztop) if cutoff is None else (
            (0.0, min(ztop, split)) if short else (min(ztop, split), ztop))
        if hi <= lo:
            return 0.0
        return 8*np.pi*r*r*quad(
            lambda z: u/np.hypot(v, z)*null_overlap(np.hypot(v, z), z, duration),
            lo, hi, epsabs=2e-11, epsrel=2e-11)[0]

    points = []
    if cutoff is not None and u < cutoff < duration:
        points.append(np.sqrt(cutoff**2-u*u))
    return quad(radial, 0, top, points=[p for p in points if 0 < p < top],
                epsabs=3e-10, epsrel=3e-11)[0]


def null_short_weight(u, cutoff, duration=4.0):
    """NP5 at a fixed physical cutoff delta<T/2; retains the whole polynomial."""
    _validate_u(u, duration)
    if not np.isfinite(cutoff) or not 0 < cutoff < duration/2:
        raise ValueError("requires 0 < cutoff < T/2")
    if u >= cutoff:
        return 0.0
    return np.pi**2*u*quad(
        lambda tau: ((duration-tau)**2-(tau*tau-u*u)/4)*(tau*tau-u*u),
        u, cutoff, epsabs=2e-12)[0]


def ramp_remainder(height, epsilon, speed=1.0):
    """NT2 actual right quadratic subtraction, including zero/negative heights."""
    h, a = np.broadcast_arrays(np.asarray(height, float), np.asarray(speed, float))
    if not np.isfinite(epsilon) or epsilon < 0 or np.any(a <= 0) or not np.all(np.isfinite(h+a)):
        raise ValueError("finite heights, positive speeds and nonnegative epsilon required")
    return (np.maximum(h-epsilon*a, 0)**2 - np.maximum(h, 0)**2
            + 2*epsilon*a*np.maximum(h, 0) - epsilon**2*a*a*(h > 0))
