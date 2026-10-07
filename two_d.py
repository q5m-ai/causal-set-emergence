"""Diagnostics for the conventional smooth flat 2D theorem in notes/two-d-limit.md.

Not a theorem prover or an admissibility decision procedure. The supplied
fixtures have the complete positive-component list, smooth regular endpoints,
and strictly concave causal overlap fibres on each listed interval. The
optimizer below relies on that fixture-specific property. Production geometric
contracts live in formal/BoundaryDraft/TwoD*.lean.

No target is used to compute the action. Both spatial directions and the full
causal partner domain are retained, including for the disconnected fixture.
"""

from dataclasses import dataclass
from math import cos, exp, log, sin, sqrt
from typing import Callable

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import roots_laguerre


@dataclass(frozen=True)
class TwoDFixture:
    height: Callable[[float], float]
    height_derivative: Callable[[float], float]
    future: Callable[[float], float]
    future_derivative: Callable[[float], float]
    components: tuple[tuple[float, float], ...]
    max_height: float
    height_lipschitz: float
    future_lipschitz: float

    @property
    def endpoints(self):
        return tuple(x for interval in self.components for x in interval)

    @property
    def volume(self):
        return sum(quad(self.height, lo, hi, epsabs=1e-12)[0]
                   for lo, hi in self.components)

    @property
    def null_support_bound(self):
        # Positive overlap implies t < max_height/(1-eta), v <= 2t.
        return 2 * self.max_height / (1 - self.future_lipschitz)

    def target(self):
        """Evaluate the independently specified positive-normal angle weights."""
        result = 0.0
        for x in self.endpoints:
            q = self.future_derivative(x)
            p = q - self.height_derivative(x)
            c = (1 - p * q) / sqrt((1 - p * p) * (1 - q * q))
            result += c / sqrt(c * c - 1)
        return result

    def target_slopes(self):
        return sum((1 - self.future_derivative(x)**2
                    + self.future_derivative(x) * self.height_derivative(x))
                   / abs(self.height_derivative(x)) for x in self.endpoints)


def interval_fixture(epsilon=1 / 8, tilt=0.0):
    """h=(1-x^2)/4, f=tilt*x+epsilon*sin(x); all endpoints and x=0 retained."""
    if not 0 <= epsilon <= 1 / 8 or 0.5 + abs(tilt) + epsilon >= 1:
        raise ValueError("fixture requires epsilon <= 1/8 and a strict combined causal budget")
    return TwoDFixture(
        lambda x: (1 - x*x) / 4, lambda x: -x / 2,
        lambda x: tilt*x + epsilon*sin(x), lambda x: tilt + epsilon*cos(x),
        ((-1.0, 1.0),), 1 / 4, 1 / 2, abs(tilt) + epsilon,
    )


def disconnected_fixture(epsilon=1 / 64):
    """Two positive intervals, FOUR endpoints and TWO positive critical points.

    Raw exterior data are clipped to zero beyond radius two as in #92.
    For this diagnostic epsilon is bounded to preserve strictly concave fibres
    on each interval; the written theorem has no concavity hypothesis.
    """
    if not 0 <= epsilon <= 1 / 64:
        raise ValueError("diagnostic concave-fibre range is 0 <= epsilon <= 1/64")
    a = 1 / 8
    return TwoDFixture(
        lambda x: a*(x*x - 1/4)*(1 - x*x) if abs(x) < 2 else 0.0,
        lambda x: a*(2.5*x - 4*x**3),
        lambda x: epsilon*sin(x), lambda x: epsilon*cos(x),
        ((-1.0, -0.5), (0.5, 1.0)), a * 9 / 64, 3*a/2, epsilon,
    )


def kernel(z):
    """The entire signed physical-dimension-two kernel."""
    return (1 - 2*z + z*z/2) * exp(-z)


def fibre_length(model, x, t, r):
    """Original intersection of BOTH time fibres, for an arbitrary displacement."""
    low_x = model.future(x) - max(0.0, model.height(x))
    low_y = model.future(x+r) - max(0.0, model.height(x+r))
    return max(0.0, min(model.future(x), model.future(x+r)-t)
               - max(low_x, low_y-t))


def causal_fibre_length(model, x, t, r):
    if t < abs(r):
        raise ValueError("causal displacements only")
    return max(0.0, max(0.0, model.height(x))
               + model.future(x+r) - model.future(x) - t)


def overlap(model, t, r):
    """Actual full overlap via complete time fibres; NOT componentwise action sums.

    Concavity isolates the support for THESE fixtures. At an endpoint of a
    spatial interval, the strict causal budget makes the expression nonpositive.
    Each partner x+r is evaluated using the entire original region/future.
    """
    if t < abs(r):
        raise ValueError("causal displacements only")
    result = 0.0
    for lo, hi in model.components:
        def g(x):
            return model.height(x) + model.future(x+r) - model.future(x) - t
        def dg(x):
            return (model.height_derivative(x) + model.future_derivative(x+r)
                    - model.future_derivative(x))
        if dg(lo) <= 0:
            maximum = lo
        elif dg(hi) >= 0:
            maximum = hi
        else:
            maximum = brentq(dg, lo, hi, xtol=1e-14)
        if g(maximum) <= 0:
            continue
        left = lo if g(lo) >= 0 else brentq(g, lo, maximum, xtol=1e-14)
        right = hi if g(hi) >= 0 else brentq(g, maximum, hi, xtol=1e-14)
        result += quad(g, left, right, epsabs=2e-12, epsrel=2e-12)[0]
    return result


def overlap_jet(model, t, r):
    """Derived origin two-jet; endpoint target is NOT defined by this jet."""
    length = sum(hi-lo for lo, hi in model.components)
    first = sum(model.future(hi)-model.future(lo) for lo, hi in model.components)
    second = sum(model.future_derivative(hi)-model.future_derivative(lo)
                 for lo, hi in model.components)
    endpoint = sum((t-r*model.future_derivative(x))**2
                   / abs(model.height_derivative(x)) for x in model.endpoints)
    return model.volume - length*t + first*r + second*r*r/2 + endpoint/2


def density(model, sigma, cutoff=None, long=False):
    """Signed-action density transport with dt dr = d(sigma) dv/(2v).

    The two directions are summed explicitly. With a cutoff, equality belongs
    to long (irrelevant only for the Lebesgue integral). Short has no point term;
    that term is allocated once in action_from_density.
    """
    if sigma < 0 or (sigma == 0 and not (long and cutoff is not None and cutoff > 0)):
        raise ValueError("sigma=0 is permitted only for a positive-cutoff long density")
    lower, upper = sqrt(sigma), model.null_support_bound
    if cutoff is not None:
        if cutoff <= 0:
            raise ValueError("positive fixed cutoff required")
        if long:
            lower = max(lower, cutoff)
        else:
            upper = min(upper, cutoff)
    if lower >= upper:
        return 0.0

    def integrand(v):
        t, r = (v + sigma/v)/2, max(0.0, (v - sigma/v)/2)
        return (overlap(model, t, r) + overlap(model, t, -r)) / (2*v)
    return quad(integrand, lower, upper, epsabs=2e-10, epsrel=2e-9, limit=160)[0]


def action_from_density(model, rho, order=96):
    """Full signed action, with only the known volume log sector subtracted.

    The log moment -1/2 cancels the point term exactly. Gauss--Laguerre and
    Gauss--Legendre quadratures approximate the remaining integrals. The target
    is NEVER used. Quadrature-order refinement is necessary; this evaluator is
    a diagnostic, not an error-certified integral or a proof of convergence.
    """
    if rho <= 0 or order < 8:
        raise ValueError("positive density and quadrature order >= 8 required")
    volume = model.volume
    z_nodes, z_weights = roots_laguerre(order)
    v_nodes, v_weights = leggauss(2*order)
    upper = model.null_support_bound
    values = []
    for z in z_nodes:
        sigma = 2*z/rho
        lower = sqrt(sigma)
        d = 0.0
        if lower < upper:
            half, mid = (upper-lower)/2, (upper+lower)/2
            for node, weight in zip(v_nodes, v_weights):
                v = mid + half*node
                t, r = (v+sigma/v)/2, (v-sigma/v)/2
                d += weight * (overlap(model, t, r) + overlap(model, t, -r))/(2*v)
            d *= half
        values.append((1-2*z+z*z/2)*(d+volume*log(sigma)/2))
    return -8*rho*float(np.dot(z_weights, values))
