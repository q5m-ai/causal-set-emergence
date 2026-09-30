"""Fixed-null mixed-cap diagnostics for #83, not a Lean or Poisson theorem.

The conventional all-partner reduction and explicit bounds are proved in
notes/null-mixed-estimates.md. Geometry stays fixed as density varies. The
numerical sine evaluator deliberately uses a smaller, concave-slice subfamily;
that computational restriction is NOT an admissibility condition in the note.
Quadrature and root tolerances are not certified error bounds.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import erfc

INTERVAL_CONSTANT = math.pi / 24
ACTION_CONSTANT = 4 / math.sqrt(6)


def _finite(*values):
    if not all(math.isfinite(value) for value in values):
        raise ValueError("parameters must be finite")


def coarea_primitive(radius, sigma):
    """Integral from 0 to radius of r^2/(2*sqrt(r^2+sigma))."""
    _finite(radius, sigma)
    if radius < 0 or sigma < 0:
        raise ValueError("radius and sigma must be nonnegative")
    if sigma == 0:
        return radius**2 / 4
    x = radius / math.sqrt(sigma)
    # Avoid subtracting two O(x) terms when the answer is O(x^3).
    if x < 0.01:
        return sigma * x**3 * (1 / 6 - x**2 / 20 + 3 * x**4 / 112
                               - 5 * x**6 / 288)
    return (radius * math.hypot(radius, math.sqrt(sigma))
            - sigma * math.asinh(x)) / 4


def round_weight(sigma, T=1.0):
    """Exact radial weight for H=T (numerically evaluated)."""
    _finite(sigma, T)
    if sigma < 0 or T <= 0:
        raise ValueError("require sigma >= 0 and T > 0")
    if sigma >= T**2:
        return 0.0
    return 4 * math.pi * coarea_primitive(math.sqrt(T**2 - sigma), sigma)


def continuity_bound(sigma, T, slope, weight_bound=1.0, time_lipschitz=0.0):
    """E(sigma) in (NM5), valid for 0 <= sigma <= T^2/4.

    T=H(0), slope is a GLOBAL Lipschitz bound <1, and the last two inputs
    bound a first-endpoint weight and its time derivative. This function
    evaluates the written bound; it does not verify those geometric inputs.
    """
    _finite(sigma, T, slope, weight_bound, time_lipschitz)
    if (T <= 0 or not 0 <= slope < 1 or not 0 <= sigma <= T**2 / 4
            or weight_bound < 0 or time_lipschitz < 0):
        raise ValueError("require T>0, 0<=slope<1, 0<=sigma<=T^2/4, M,L>=0")
    if sigma == 0:
        return 0.0
    lower, upper = T / (1 + slope), T / (1 - slope)
    return math.pi * sigma * (
        weight_bound * (1 + math.log(upper / math.sqrt(sigma))
                        + 2 * upper / (lower * (1 - slope)))
        + time_lipschitz * upper)


def action_error_bound(rho, split, T, slope, weight_bound=1.0, time_lipschitz=0.0):
    """Fixed-split bound (NM7), not a claim of uniformity over geometries."""
    _finite(rho, split)
    if rho <= 0 or split <= 0:
        raise ValueError("density and proper-time-squared split must be positive")
    local = continuity_bound(split, T, slope, weight_bound, time_lipschitz)
    upper = T / (1 - slope)
    tail = erfc(math.sqrt(INTERVAL_CONSTANT * rho) * split)
    return 4 * local + 8 * weight_bound * math.pi * upper**2 * tail


@lru_cache(maxsize=16)
def _angular_rule(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 8:
        raise ValueError("angular quadrature order must be an integer >= 8")
    return leggauss(order)


@dataclass(frozen=True)
class SineMixedCap:
    """Numerical H(x)=T+epsilon*sin(x_1), including the round epsilon=0 case.

    T*epsilon+2*epsilon^2<1 ensures Q(r)=H(r*omega)^2-r^2 is strictly
    concave for every direction. It lets us bracket ALL slice components,
    including the annular slices at sigma>T^2. It is only an evaluator domain.
    The written estimates cover every H in #90, without this restriction.
    """

    T: float = 1.0
    epsilon: float = 0.2

    def __post_init__(self):
        _finite(self.T, self.epsilon)
        if not (0 <= self.epsilon < min(1, self.T)
                and self.T * self.epsilon + 2 * self.epsilon**2 < 1):
            raise ValueError("require 0<=epsilon<min(1,T) and T*epsilon+2*epsilon^2<1")

    def height(self, radius, mu):
        return self.T + self.epsilon * math.sin(radius * mu)

    def joint_radius(self, mu):
        _finite(mu)
        if not -1 <= mu <= 1:
            raise ValueError("mu must lie in [-1,1]")
        return brentq(lambda r: r - self.height(r, mu),
                      self.T / (1 + self.epsilon), self.T / (1 - self.epsilon))

    def squared_duration(self, radius, mu):
        return self.height(radius, mu)**2 - radius**2

    def radial_slice(self, sigma, mu):
        """Return the open radial interval at sigma, or None if empty.

        Do not assume a sigma slice starts at zero: positive-mu slices can
        survive above H(0)^2 and then have TWO positive endpoints.
        """
        _finite(sigma)
        if sigma < 0:
            raise ValueError("sigma must be nonnegative")
        radius = self.joint_radius(mu)
        if sigma == 0:
            return 0.0, radius

        def derivative(r):
            return 2 * (self.height(r, mu) * self.epsilon * mu
                        * math.cos(r * mu) - r)

        peak = brentq(derivative, 0, radius) if derivative(0) > 0 else 0.0
        maximum = self.squared_duration(peak, mu)
        if sigma >= maximum:
            return None
        equation = lambda r: self.squared_duration(r, mu) - sigma
        low = brentq(equation, 0, peak) if sigma > self.T**2 else 0.0
        high = brentq(equation, peak, radius)
        return low, high

    def joint_area(self, angular_order=64):
        """Independent screen-area quadrature, integral of R(omega)^2."""
        nodes, weights = _angular_rule(angular_order)
        return 2 * math.pi * sum(w * self.joint_radius(mu)**2
                                for mu, w in zip(nodes, weights))

    def weight(self, sigma, angular_order=64):
        """Coarea weight W_H; full radial slices, not a small-sigma model."""
        _finite(sigma)
        if sigma < 0:
            raise ValueError("sigma must be nonnegative")
        nodes, weights = _angular_rule(angular_order)
        total = 0.0
        for mu, w in zip(nodes, weights):
            bounds = self.radial_slice(sigma, mu)
            if bounds is not None:
                low, high = bounds
                total += w * (coarea_primitive(high, sigma)
                              - coarea_primitive(low, sigma))
        return 2 * math.pi * total

    def action(self, rho, angular_order=64):
        """Reduced all-partner action; deterministic quadrature, not expectation.

        Scaling sigma by sqrt(c*rho) resolves the Gaussian layer. A cutoff
        u=10 omits at most J_H*erfc(10) analytically; floating-point, radial
        root and angular/outer quadrature errors are separate, uncertified.
        """
        _finite(rho)
        if rho <= 0:
            raise ValueError("rho must be positive")
        _angular_rule(angular_order)
        scale = math.sqrt(INTERVAL_CONSTANT * rho)
        upper = min(10.0, scale * (self.T / (1 - self.epsilon))**2)
        points = [p for p in (1.0, 3.0, self.T**2 * scale) if 0 < p < upper]
        integral, _ = quad(lambda u: self.weight(u / scale, angular_order)
                           * math.exp(-u**2), 0, upper,
                           points=sorted(set(points)), epsabs=2e-8, epsrel=2e-8,
                           limit=150)
        return 8 / math.sqrt(math.pi) * integral

    def volume(self, angular_order=64):
        """Independent ordinary time/radius volume, not a coarea identity input."""
        nodes, weights = _angular_rule(angular_order)
        return 2 * math.pi * sum(w * quad(
            lambda r: r**2 * (self.height(r, mu) - r),
            0, self.joint_radius(mu), epsabs=1e-11)[0]
            for mu, w in zip(nodes, weights))
