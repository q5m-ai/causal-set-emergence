"""Focused #133 diagnostics, NOT production observables or limit proofs.

See notes/general-metric-atlas-gate.md. Tests reuse the existing diagnostic
kernel. There are no action/probability API changes.
"""

from functools import lru_cache

import numpy as np
import sympy as s
from numpy.polynomial.legendre import leggauss


@lru_cache(maxsize=None)
def gauss_rule(order):
    """Nodes/weights on [0,1], shared only by these finite diagnostics."""
    nodes, weights = leggauss(order)
    return (nodes + 1) / 2, weights / 2


def time_density_phase(q, t, u, v, order=32):
    """H_q = average of q over a boosted unit diamond, including u=0.

    Integrate rest time a, longitudinal coordinate b, and the transverse disk
    exactly in the latter two transverse directions. Split a at zero to keep
    the cross-section radius smooth. This does not freeze q at either endpoint.
    """
    nodes, weights = gauss_rule(order)
    total = 0.0
    T, r = (u + v) / 2, (v - u) / 2
    for sign in (-1, 1):
        a = sign * nodes[:, None] / 2
        radius = 0.5 - np.abs(a)
        b = radius * (2 * nodes[None, :] - 1)
        disk = np.pi * (radius**2 - b**2)
        values = q(t + T / 2 + T * a + r * b)
        total += np.sum(weights[:, None] * weights[None, :] * radius * disk * values)
    return total / (np.pi / 24)


def null_ray_phase(q, t, v, order=64):
    """Exact one-dimensional null-limit representation, evaluated numerically."""
    z, weights = gauss_rule(order)
    return np.sum(weights * 6 * z * (1 - z) * q(t + v * z / 2))


def torus_distance(p, q, length):
    """Flat cubic quotient distance, not distance between chart representatives."""
    if length <= 0:
        raise ValueError("positive period required")
    delta = (np.asarray(q) - np.asarray(p) + length / 2) % length - length / 2
    return np.linalg.norm(delta, axis=-1)


def thin_torus_interval(tau, distance, length, duration):
    """Actual interval formula ONLY in the proved thin-slab regime."""
    if not 0 < duration < length / 2:
        raise ValueError("requires fixed 0 < duration < length/2")
    if not 0 <= distance <= tau <= duration:
        raise ValueError("requires a causal pair in the slab")
    return np.pi / 24 * (tau**2 - distance**2)**2


def slab_phase_amplitude(w, duration):
    """Full time/radius pair density per spatial volume; zero beyond T^2."""
    if duration <= 0 or w < 0:
        raise ValueError("positive duration and nonnegative phase required")
    if w == 0:
        return np.pi * duration**3 / 3
    if w >= duration**2:
        return 0.0
    root = np.sqrt(duration**2 - w)
    return 2 * np.pi * (
        duration * (duration * root - w * np.log((duration + root) / np.sqrt(w))) / 2
        - root**3 / 3
    )


def antipodal_scaled_volume(epsilon, radius=1.0, order=96):
    """Actual S^2_a x S^1 interval volume divided by epsilon^(3/2).

    Endpoints are antipodal on S^2, same circle coordinate, separated in time
    by pi*a+epsilon. Assumes circle circumference exceeds twice that separation.
    Spatial/time Fubini gives integral (tau-d_N-d_S)_+; stable rationalized
    square-root differences avoid subtracting nearly equal travel times.
    No asymptotic model is substituted in this function.
    """
    if epsilon <= 0 or radius <= 0:
        raise ValueError("positive epsilon and radius required")
    nodes, weights = gauss_rule(order)
    D = np.pi * radius
    tau = D + epsilon
    r = D * nodes[:, None]
    zeta_max = 0.5 * np.sqrt((2 * D + epsilon) * (1 - (2 * r - D)**2 / tau**2))
    zeta = zeta_max * nodes[None, :]
    deficit = (
        zeta**2 / (np.sqrt(r**2 + epsilon * zeta**2) + r)
        + zeta**2 / (np.sqrt((D - r)**2 + epsilon * zeta**2) + D - r)
    )
    return 4 * np.pi * radius * D * np.sum(
        weights[:, None] * weights[None, :] * np.sin(r / radius)
        * zeta_max * (1 - deficit)
    )


def antipodal_coefficient(radius=1.0, order=128):
    """Independent coefficient from the proved rescaled limiting integral."""
    nodes, weights = gauss_rule(order)
    D = np.pi * radius
    r = D * nodes
    return 8 * np.pi * radius / 3 * D * np.sum(
        weights * np.sin(r / radius) * np.sqrt(2 * r * (D - r) / D)
    )


@lru_cache(maxsize=None)
def product_curvature():
    """Direct connection/Riemann contractions for dt^2-a^2 dS2^2-dz^2.

    Uses #90's convention (opposite conformal_geometry.py). Return scalar and
    Weyl square, rather than presupposing that the product is conformally flat.
    Coordinate polar singularities are excluded from this local calculation.
    """
    t, theta, phi, z = s.symbols("t theta phi z", real=True)
    a = s.symbols("a", positive=True)
    x = (t, theta, phi, z)
    g = s.diag(1, -a**2, -a**2 * s.sin(theta)**2, -1)
    inv = g.inv()
    gamma = {
        (i, j, k): s.simplify(sum(inv[i, e] * (
            s.diff(g[e, k], x[j]) + s.diff(g[e, j], x[k])
            - s.diff(g[j, k], x[e])) / 2 for e in range(4)))
        for i in range(4) for j in range(4) for k in range(4)
    }
    riemann = {
        (i, j, k, l): s.trigsimp(
            s.diff(gamma[i, k, j], x[l]) - s.diff(gamma[i, l, j], x[k])
            + sum(gamma[i, l, e] * gamma[e, k, j]
                  - gamma[i, k, e] * gamma[e, l, j] for e in range(4)))
        for i in range(4) for j in range(4) for k in range(4) for l in range(4)
    }
    ricci = s.Matrix(4, 4, lambda j, l: s.trigsimp(sum(
        riemann[i, j, i, l] for i in range(4))))
    scalar = s.simplify(sum(inv[i, i] * ricci[i, i] for i in range(4)))
    ricci_sq = s.simplify(sum(inv[i, i] * inv[j, j] * ricci[i, j]**2
                             for i in range(4) for j in range(4)))
    riemann_sq = s.trigsimp(sum(
        inv[i, i] * inv[j, j] * inv[k, k] * inv[l, l]
        * (g[i, i] * value)**2
        for (i, j, k, l), value in riemann.items()))
    return a, scalar, s.simplify(riemann_sq - 2 * ricci_sq + scalar**2 / 3)


def check_general_metric_identities():
    """Exact algebra certificates; none is a universal analytic proof."""
    a, scalar, weyl_sq = product_curvature()
    assert s.simplify(scalar - 2 / a**2) == 0
    assert s.simplify(weyl_sq - 4 / (3 * a**4)) == 0
    w, T = s.symbols("w T", positive=True)
    B = 2 * s.pi * (
        T * (T * s.sqrt(T**2 - w)
             - w * s.log((T + s.sqrt(T**2 - w)) / s.sqrt(w))) / 2
        - (T**2 - w)**s.Rational(3, 2) / 3)
    jet = (s.pi * T**3 / 3 + s.pi * T * w * s.log(w) / 2
           + s.pi * T * (s.Rational(1, 2) - s.log(2 * T)) * w
           - s.pi * w**2 / (8 * T))
    expansion = s.series(B, w, 0, 4).removeO()
    assert s.simplify(expansion - jet + s.pi * w**3 / (96 * T**3)) == 0
    j = s.symbols("j")
    moment = -j * (j - 1) * (j - 2) * s.gamma((j + 1) / 2) / 12
    assert all(moment.subs(j, k) == 0 for k in range(3))
    assert s.diff(moment, j).subs(j, 1) == s.Rational(1, 12)
    assert s.simplify((s.pi * T / 2) / (12 * (s.pi / 24)) - T) == 0
    print("PASS: #133 product curvature/Weyl, full slab jet and physical point cancellation")


if __name__ == "__main__":
    check_general_metric_identities()
