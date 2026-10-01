"""Independent finite-order and Poisson-layer diagnostics for issue #84.

The written theorem is in notes/null-mixed-assembly.md, not in this evaluator.
Positive layer means are integrated separately in ordinary source coordinates
and complete rest-frame partner intervals. No reduced Gaussian action or
coarea weight is used to define the expectation. Fixed Gaussian quadrature is
for moderate densities only: refinement errors are not certified, and signed
subtraction of large layer means is unsuitable for an asymptotic solver.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from numpy.polynomial.legendre import leggauss

from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT, SineMixedCap


def _positive_density(rho):
    if not math.isfinite(rho) or rho <= 0:
        raise ValueError("density must be finite and positive")


def _points(points):
    points = np.asarray(points, dtype=float)
    if points.shape == (0,):
        points = points.reshape(0, 4)
    if points.ndim != 2 or points.shape[1] != 4 or not np.isfinite(points).all():
        raise ValueError("points must be a finite N-by-4 array (time, x, y, z)")
    if len(np.unique(points, axis=0)) != len(points):
        raise ValueError("this finite-order diagnostic requires distinct points")
    return points


def layer_counts(points):
    """Count ordered, distinct causal pairs with k=0,1,2,3 other elements.

    Closed causal order includes null pairs. Only the two marked endpoints
    are excluded from each interval. No coordinate tolerance changes order.
    Complexity is cubic; this is a small-configuration regression helper.
    """
    points = _points(points)
    delta = points[None, :, :] - points[:, None, :]
    causal = ((delta[:, :, 0] >= 0)
              & (np.sum(delta[:, :, 1:]**2, axis=2) <= delta[:, :, 0]**2))
    layers = [0, 0, 0, 0]
    for i, j in zip(*np.nonzero(causal)):
        if i != j:
            interior = np.count_nonzero(causal[i, :] & causal[:, j]) - 2
            if interior < 4:
                layers[interior] += 1
    return tuple(layers)


def discrete_action(rho, points):
    """Actual normalized finite-order observable, not a continuum definition."""
    _positive_density(rho)
    points = _points(points)
    l0, l1, l2, l3 = layer_counts(points)
    return ACTION_CONSTANT / math.sqrt(rho) * (len(points) - l0 + 9*l1 - 16*l2 + 8*l3)


@lru_cache(maxsize=8)
def _unit_rule(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    nodes, weights = leggauss(order)
    return (nodes + 1) / 2, weights / 2


@lru_cache(maxsize=8)
def _partner_rule(order):
    """Polar volume rule on I(0,(1,0)); split the equatorial kink exactly."""
    u, weights = _unit_rule(order)
    time = np.concatenate((u / 2, (1 + u) / 2))
    time_weights = np.tile(weights / 2, 2)
    radius_bound = np.minimum(time, 1 - time)[:, None]
    radius = radius_bound * u[None, :]
    volume_weights = 4 * math.pi * radius**2 * radius_bound * time_weights[:, None] * weights
    phase = (time[:, None]**2 - radius**2)**2
    return phase.ravel(), volume_weights.ravel()


def _interval_layers(rho, sigma, order):
    # Proper duration is sqrt(sigma), hence the 4-volume scales by sigma^2.
    phase, weights = _partner_rule(order)
    scale = np.asarray(sigma).reshape(-1, 1)**2
    z = INTERVAL_CONSTANT * rho * scale * phase
    pmf = np.exp(-z)
    integrals = []
    for k in range(4):
        if k:
            pmf = pmf * z / k
        integrals.append(scale[:, 0] * np.sum(pmf * weights, axis=1))
    return np.stack(integrals, axis=-1)


def interval_layer_integrals(rho, sigma, order=20):
    """Four positive partner integrals for a source at squared duration sigma."""
    _positive_density(rho)
    if not math.isfinite(sigma) or sigma < 0:
        raise ValueError("squared duration must be finite and nonnegative")
    return _interval_layers(rho, sigma, order)[0]


@dataclass(frozen=True)
class PoissonLayerMeans:
    density: float
    points: float
    layers: tuple[float, float, float, float]

    def action(self):
        l0, l1, l2, l3 = self.layers
        return ACTION_CONSTANT / math.sqrt(self.density) * (
            self.points - l0 + 9*l1 - 16*l2 + 8*l3)


def mixed_layer_means(cap: SineMixedCap, rho, source_order=16, partner_order=16):
    """Campbell--Mecke layer quadrature, not Monte Carlo or a limit proof.

    Integrate sources with r<R(mu), r<w<H(r*mu), t=-w. For each source
    integrate the four Poisson PMFs over the ENTIRE future interval to the tip,
    using Lorentz volume preservation. The evaluator supports only SineMixedCap;
    its extra concave-slice restriction is not a hypothesis of the theorem.
    """
    _positive_density(rho)
    if not isinstance(cap, SineMixedCap):
        raise TypeError("the numerical evaluator supports only SineMixedCap")
    u, weights = _unit_rule(source_order)
    _unit_rule(partner_order)
    point_volume = 0.0
    pair_integrals = np.zeros(4)
    for mu, angular_weight in zip(2*u - 1, 2*weights):
        R = cap.joint_radius(mu)
        radius = R * u[:, None]
        height = cap.T + cap.epsilon * np.sin(radius * mu)
        time_depth = radius + (height - radius) * u[None, :]
        sigma = time_depth**2 - radius**2
        source_weights = (2 * math.pi * angular_weight * R * (height - radius)
                          * radius**2 * weights[:, None] * weights[None, :])
        point_volume += np.sum(source_weights)
        layers = _interval_layers(rho, sigma, partner_order)
        pair_integrals += np.sum(source_weights.reshape(-1, 1) * layers, axis=0)
    return PoissonLayerMeans(rho, float(rho * point_volume),
                            tuple(float(x) for x in rho**2 * pair_integrals))
