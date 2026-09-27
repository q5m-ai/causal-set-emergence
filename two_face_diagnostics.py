"""Deterministic diagnostics for #54, not a two-face limit theorem.

The density functions integrate the actual causal overlap, not the proposed
joint target. See notes/two-face-diagnostics.md for reductions and error limits.
Arithmetic is IEEE float64; order refinement is NOT a certified error bound.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from scipy.optimize import brentq


C_INTERVAL = math.pi / 24
NORMALIZATION = 4 / math.sqrt(6)


def bdg_kernel(x):
    return (1 + x * (-9 + x * (8 - 4 * x / 3))) * np.exp(-x)


@lru_cache(maxsize=16)
def gauss_rule(order):
    if not isinstance(order, int) or order < 4:
        raise ValueError("quadrature order must be an integer >= 4")
    return np.polynomial.legendre.leggauss(order)


def quadrature(function, points, order):
    """Composite Gauss-Legendre, with explicit panels and compensated summation."""
    nodes, weights = gauss_rule(order)
    points = sorted(set(float(p) for p in points))
    panels = []
    for left, right in zip(points, points[1:]):
        half = (right - left) / 2
        values = function((left + right) / 2 + half * nodes)
        panels.append(half * math.fsum(weights * values))
    return math.fsum(panels)


def _positive(value, name):
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and positive")


@dataclass(frozen=True)
class AxialCap:
    """h=d*(1-sum(x_i/a_i)^2), f=b*sin(x_1/a_1), everywhere raw h.

    Causal envelopes are (f-max(h,0), f); the raw lower face is f-h.
    """

    depth: float = 0.25
    axes: tuple = (1.0, 2.0, 3.0)
    bend: float = 0.0625

    def __post_init__(self):
        _positive(self.depth, "depth")
        if len(self.axes) != 3:
            raise ValueError("require three axes")
        for axis in self.axes:
            _positive(axis, "axis")
        if not math.isfinite(self.bend) or self.slope_budget >= 1:
            raise ValueError("require finite bend and strict kappa+lambda < 1")
        if abs(self.bend) >= self.depth:
            raise ValueError("require |bend| < depth for the axial overlap contact solver")
        # Ensures a unique maximum in the one-dimensional support solver.
        if self.curvature_bound * math.sqrt(self.sigma_max) >= (1 - self.lam**2)**1.5:
            raise ValueError("bend exceeds the diagnostic support-solver curvature bound")

    @property
    def kappa(self):
        return 2 * self.depth / min(self.axes)

    @property
    def lam(self):
        return abs(self.bend) / self.axes[0]

    @property
    def slope_budget(self):
        return self.kappa + self.lam

    @property
    def curvature_bound(self):
        return abs(self.bend) / self.axes[0]**2

    @property
    def sigma_max(self):
        return self.depth**2 / (1 - self.lam**2)

    @property
    def time_bound(self):
        return self.depth + 2 * abs(self.bend)

    @property
    def volume(self):
        return 8 * math.pi * self.depth * math.prod(self.axes) / 15

    def shift(self, x):
        return self.bend * np.sin(x / self.axes[0])

    def shift_prime(self, x):
        return self.bend / self.axes[0] * np.cos(x / self.axes[0])

    def dilated(self, scale):
        _positive(scale, "scale")
        return AxialCap(scale * self.depth, tuple(scale * a for a in self.axes), scale * self.bend)


@dataclass(frozen=True)
class RadialCap:
    """h=d*(1-|x|^2/R^2), f=b*(1-|x|^2/core^2)_+^4.

    f is globally C3 and identically zero throughout a neighborhood of the
    joint. Both face germs curve in the interior; this is not a Lorentz boost.
    """

    depth: float = 0.25
    radius: float = 1.0
    bend: float = 0.025
    core: float = 0.65

    def __post_init__(self):
        for value, name in ((self.depth, "depth"), (self.radius, "radius"), (self.core, "core")):
            _positive(value, name)
        if not 0 < self.core < self.radius:
            raise ValueError("require 0 < core < radius")
        if not math.isfinite(self.bend) or self.slope_budget >= 1:
            raise ValueError("require finite bend and strict kappa+lambda < 1")
        if self.curvature_bound * math.sqrt(self.sigma_max) >= (1 - self.lam**2)**1.5:
            raise ValueError("bend exceeds the diagnostic support-solver curvature bound")

    @property
    def kappa(self):
        return 2 * self.depth / self.radius

    @property
    def lam(self):
        return 8 * abs(self.bend) / (math.sqrt(7) * self.core) * (6 / 7)**3

    @property
    def slope_budget(self):
        return self.kappa + self.lam

    @property
    def curvature_bound(self):
        return 8 * abs(self.bend) / self.core**2

    @property
    def sigma_max(self):
        return self.depth**2 / (1 - self.lam**2)

    @property
    def time_bound(self):
        return self.depth + 2 * abs(self.bend)

    @property
    def volume(self):
        return 8 * math.pi * self.depth * self.radius**3 / 15

    def shift(self, x):
        return self.bend * np.maximum(0, 1 - (x / self.core)**2)**4

    def shift_prime(self, x):
        return -8 * self.bend * x / self.core**2 * np.maximum(0, 1 - (x / self.core)**2)**3

    def dilated(self, scale):
        _positive(scale, "scale")
        return RadialCap(scale * self.depth, scale * self.radius, scale * self.bend, scale * self.core)


def region_data(cap, x):
    """Raw face germs and globally causal envelopes, deliberately distinct."""
    x = np.asarray(x, dtype=float)
    if x.shape != (3,) or not np.all(np.isfinite(x)):
        raise ValueError("require three finite spatial coordinates")
    if isinstance(cap, RadialCap):
        r = np.linalg.norm(x)
        height = cap.depth * (1 - (r / cap.radius)**2)
        shift = cap.shift(r)
    else:
        height = cap.depth * (1 - np.sum((x / cap.axes)**2))
        shift = cap.shift(x[0])
    return {"raw_height": height, "lower_raw": shift - height,
            "upper": shift, "lower_envelope": shift - max(0, height)}


def contains(cap, t, x):
    data = region_data(cap, x)
    return data["lower_envelope"] < t < data["upper"]


def _root(function, left, right):
    return brentq(function, left, right, xtol=5e-324, rtol=4 * np.finfo(float).eps)


def _support(cap, center, height, sigma, left, right):
    """Positive interval of height+f(q)-f(center)-sqrt((q-center)^2+sigma).

    |f'|<=lambda<1 restricts stationary points to a small interval; the checked
    curvature bound makes the derivative strictly decreasing there. Outside
    it the derivative has a fixed sign. Thus there are at most two roots.
    """
    base = height - cap.shift(center)

    def gap(q):
        return base + cap.shift(q) - math.hypot(q - center, math.sqrt(sigma))

    if sigma == 0:
        peak = min(right, max(left, center))
    else:
        width = cap.lam * math.sqrt(sigma / (1 - cap.lam**2))
        lo, hi = max(left, center - width), min(right, center + width)

        def derivative(q):
            return cap.shift_prime(q) - (q - center) / math.hypot(q - center, math.sqrt(sigma))

        if lo >= hi:
            peak = min(right, max(left, center))
        elif derivative(lo) <= 0:
            peak = lo
        elif derivative(hi) >= 0:
            peak = hi
        else:
            peak = _root(derivative, lo, hi)
    if gap(peak) <= 0:
        return None
    lo = left if gap(left) >= 0 else _root(gap, left, peak)
    hi = right if gap(right) >= 0 else _root(gap, peak, right)
    return lo, hi


def _inner_density(cap, p, sigma, delta, order):
    radial = isinstance(cap, RadialCap)
    radius = cap.radius if radial else cap.axes[0]
    height = cap.depth * (1 - (p / radius)**2)
    domain = (0, radius) if radial else (-radius, radius)
    support = _support(cap, p, height, sigma, *domain)
    if support is None:
        return 0.0
    lo, hi = support
    points = [lo, hi, p]
    if radial:
        points.append(cap.core)
    # Resolve the sqrt boundary layer independently of the density-run scale.
    width = math.sqrt(sigma)
    while width > 0 and width < 2 * radius:
        points.extend((p - width, p + width))
        width *= 4
    cut = (delta + sigma / delta) / 2 if delta > 0 and sigma < delta**2 else 0
    rcut = math.sqrt(max(0, cut**2 - sigma))
    points.extend((p - rcut, p + rcut))

    def L(q):
        return height + cap.shift(q) - cap.shift(p)

    # f is monotone on either chosen one-dimensional domain (with a flat part
    # for the bump). Split the cutoff's positive part at its possible root.
    if cut > 0 and (L(lo) - cut) * (L(hi) - cut) < 0:
        points.append(_root(lambda q: L(q) - cut, lo, hi))
    if radial:
        points.append(rcut - p)
        # The upper angular endpoint p+q can also become tangent to a face.
        other = _support(cap, -p, height, sigma, *domain)
        if other is not None:
            points.extend(other)

    def integrand(q):
        lower = np.maximum(np.hypot(q - p, math.sqrt(sigma)), cut)
        first = np.maximum(0, L(q) - lower)
        if not radial:
            return first**3
        upper = np.hypot(q + p, math.sqrt(sigma))
        second = np.maximum(0, L(q) - upper)
        return p * q * np.maximum(0, first**2 - second**2)

    return quadrature(integrand, [x for x in points if lo <= x <= hi], order)


def _crossings(function, left, right):
    """Bracket geometric panel events; refinement remains necessary at contacts."""
    grid = np.linspace(left, right, 65)
    values = [function(p) for p in grid]
    return [_root(function, a, b) for a, b, fa, fb in zip(grid, grid[1:], values, values[1:])
            if fa * fb < 0]


def overlap_density(cap, sigma, delta=0.0, order=24):
    """Actual B_delta(sigma); delta=0 includes the whole future cone.

    Angular and time integrations are analytic. The remaining spatial pair
    integral is deterministic, positive, and two dimensional. At delta>0 it
    is exactly the long-displacement diagnostic in #52, including tangencies.
    """
    if not math.isfinite(sigma) or sigma < 0 or not math.isfinite(delta) or delta < 0:
        raise ValueError("sigma and delta must be finite and nonnegative")
    gauss_rule(order)
    if sigma >= cap.sigma_max:
        return 0.0
    radial = isinstance(cap, RadialCap)
    radius = cap.radius if radial else cap.axes[0]
    bound = radius * math.sqrt(max(0, 1 - math.sqrt((1 - cap.lam**2) * sigma) / cap.depth))
    points = [0, bound] if radial else [-bound, 0, bound]
    if radial:
        points.extend(x for x in (cap.core, cap.depth / 2, delta / 2) if 0 < x < bound)
    if 0 < delta and sigma < delta**2:
        cut = (delta + sigma / delta) / 2
        rcut = (delta - sigma / delta) / 2
        # Contact of the moving integration boundary with a translated face.
        # Split in p as well as q, rather than smoothing over this event.
        for sign in (-1, 1):
            points.extend(_crossings(
                lambda p: cap.depth * (1 - (p / radius)**2)
                + cap.shift(p + sign * rcut) - cap.shift(p) - cut,
                0 if radial else -bound, bound,
            ))
    factor = 2 * math.pi**2 if radial else math.pi**2 * cap.axes[1] * cap.axes[2] / (6 * cap.depth)
    return factor * quadrature(
        lambda ps: np.array([_inner_density(cap, p, sigma, delta, order) for p in ps]), points, order
    )


def ellipsoid_overlap(s, depth, axes):
    """Closed form ONLY for a planar-future ellipsoid and future causal z."""
    return 8 * math.pi * depth * math.prod(axes) / 15 * np.maximum(0, 1 - s / depth)**2.5


def axial_overlap(cap, s, a1, order=32):
    """V((s,a)) with f depending on x_1, for a future-causal displacement.

    Only the axial component a1 is needed; the caller must have s>=|a|.
    This function enforces the necessary axial inequality.
    """
    if not math.isfinite(s) or not math.isfinite(a1) or s < abs(a1):
        raise ValueError("require s >= |a1|")
    a = cap.axes[0]

    def gap(x):
        return cap.depth * (1 - (x / a)**2) + cap.shift(x + a1) - cap.shift(x) - s

    peak = _root(lambda x: -2 * cap.depth * x / a**2
                 + cap.shift_prime(x + a1) - cap.shift_prime(x), -a, a)
    if gap(peak) <= 0:
        return 0.0
    lo = -a if gap(-a) >= 0 else _root(gap, -a, peak)
    hi = a if gap(a) >= 0 else _root(gap, peak, a)
    return math.pi * cap.axes[1] * cap.axes[2] / (2 * cap.depth) * quadrature(
        lambda x: gap(x)**2, [lo, peak, hi], order,
    )


def axial_null_contact(cap):
    """Translated-face tangency on the ray (s,a)=(s,s*e_1).

    At contact the overlap's maximizing axial coordinate is stationary and
    its vertical gap is zero. |bend|<depth makes that gap strictly concave.
    """
    a = cap.axes[0]

    def maximum(s):
        x = _root(lambda x: -2 * cap.depth * x / a**2
                  + cap.shift_prime(x + s) - cap.shift_prime(x), -a, a)
        return cap.depth * (1 - (x / a)**2) + cap.shift(x + s) - cap.shift(x) - s

    return _root(maximum, 0, cap.depth / (1 - cap.lam))


def _tail_bound(cap, rho, end):
    """Analytic absolute kernel-tail bound, not a quadrature error bound."""
    from mpmath import mp

    with mp.workdps(35):
        tail = mp.fsum(coefficient * mp.gammainc(mp.mpf(j + 1) / 2, end**2, mp.inf) / 2
                      for j, coefficient in ((0, 1), (2, 9), (4, 8), (6, mp.mpf(4) / 3)))
        # B_sigma <= pi*volume*time_bound^2, using v<=2*time_bound.
        return float(NORMALIZATION * rho / math.sqrt(C_INTERVAL)
                     * math.pi * cap.volume * cap.time_bound**2 * tail)


def action(cap, rho, order=24, delta=0.15, sigma_split=0.01, z_limit=9.0):
    """Full signed action and a disjoint three-regime pair decomposition.

    Returned pair pieces already include the normalized rho**(3/2) prefactor
    and are subtracted from point. A large cancellation ratio warns against
    interpreting small raw cubature errors as an accurate action residual.
    """
    for value, name in ((rho, "rho"), (delta, "delta"), (sigma_split, "sigma_split"), (z_limit, "z_limit")):
        _positive(value, name)
    scale = math.sqrt(C_INTERVAL * rho)
    end = min(z_limit, scale * cap.sigma_max)
    roots = np.sqrt(np.sort(np.roots([-4 / 3, 8, -9, 1])))
    points = [0, end] + [float(x) for x in (*roots, 1, 2, 4, 6, 8,
                                         scale * delta**2, scale * sigma_split) if 0 < x < end]
    nodes, weights = gauss_rule(order)
    terms = [[], [], []]
    absolute = []
    # z=w^2 softens the diagonal density's sigma*log(sigma) endpoint.
    points = sorted(set(math.sqrt(p) for p in points))
    for lo, hi in zip(points, points[1:]):
        half = (hi - lo) / 2
        for w, weight in zip((lo + hi) / 2 + half * nodes, half * weights):
            z = w * w
            weight *= 2 * w
            sigma = z / scale
            full = overlap_density(cap, sigma, order=order)
            long = overlap_density(cap, sigma, delta, order)
            coefficient = NORMALIZATION * rho / math.sqrt(C_INTERVAL) * weight * bdg_kernel(z * z)
            terms[0].append(coefficient * (full - long))
            terms[1 if sigma < sigma_split else 2].append(coefficient * long)
            absolute.append(abs(coefficient) * full)
    pieces = [math.fsum(part) for part in terms]
    point = NORMALIZATION * math.sqrt(rho) * cap.volume
    residual = math.fsum([point, *(-p for p in pieces)])
    return {
        "rho": rho, "order": order, "volume": cap.volume, "point": point,
        "pair_diagonal": pieces[0], "pair_long_near_null": pieces[1],
        "pair_long_timelike": pieces[2], "pair": math.fsum(pieces), "action": residual,
        "absolute_pair": math.fsum(absolute),
        "roundoff_scale_not_bound": np.finfo(float).eps * (point + math.fsum(absolute)),
        "cancellation_ratio": (point + math.fsum(absolute)) / max(abs(residual), np.finfo(float).tiny),
        "tail_bound": _tail_bound(cap, rho, end) if end < scale * cap.sigma_max else 0.0,
    }


def joint_geometry(cap, order=32):
    """Independent tangent Gram area and both future unit normals (+---).

    Reports Lorentzian area/weighted target, ambient Euclidean negative
    control, and sampled angle extrema (not certified global extrema).
    """
    radial = isinstance(cap, RadialCap)
    axes = (cap.radius,) * 3 if radial else cap.axes
    nodes, weights = gauss_rule(order)
    totals = np.zeros(3)
    angles = []
    for mu, wm in zip(nodes, weights):
        st = math.sqrt(1 - mu**2)
        for phi, wp in zip(math.pi * (nodes + 1), math.pi * weights):
            cp, sp = math.cos(phi), math.sin(phi)
            x = np.array([axes[0] * st * cp, axes[1] * st * sp, axes[2] * mu])
            # Derivatives wrt mu and phi, not an assumed projected density.
            v = np.array([-axes[0] * mu / st * cp, -axes[1] * mu / st * sp, axes[2]])
            w = np.array([-axes[0] * st * sp, axes[1] * st * cp, 0])
            gh = -2 * cap.depth * x / np.square(axes)
            gf = np.zeros(3) if radial else np.array([cap.shift_prime(x[0]), 0, 0])
            vm, vp = gf - gh, gf
            nm = np.r_[1, vm] / math.sqrt(1 - vm @ vm)
            np_ = np.r_[1, vp] / math.sqrt(1 - vp @ vp)
            C = nm[0] * np_[0] - nm[1:] @ np_[1:]
            angle = math.acosh(C)
            angles.append(angle)
            weight = C / math.sqrt((C - 1) * (C + 1))
            lift = np.array([[gf @ v, *v], [gf @ w, *w]])
            lorentz = lift[:, 1:] @ lift[:, 1:].T - np.outer(lift[:, 0], lift[:, 0])
            euclid = lift @ lift.T
            dL, dE = math.sqrt(np.linalg.det(lorentz)), math.sqrt(np.linalg.det(euclid))
            totals += wm * wp * np.array([dL, weight * dL, weight * dE])
    return dict(zip(("area_lorentz", "target", "euclidean_wrong_target"), totals)) | {
        "sampled_angle_min": min(angles), "sampled_angle_max": max(angles),
    }


def boosted_ellipsoid_action(rho, depth=0.25, axes=(1.0, 2.0, 3.0), beta=0.6, order=32):
    """Independent direct (s,r,mu) cubature in a boosted frame.

    Integrate over the image of the rest cone, with determinant one. Evaluate
    Q in lab coordinates and overlap after the explicit inverse boost, rather
    than calling the covariance identity or the proper-time density routine.
    This unscaled calibration is intended for moderate densities only.
    """
    _positive(rho, "rho")
    AxialCap(depth, axes, 0)
    if not math.isfinite(beta) or abs(beta) >= 1:
        raise ValueError("require |beta| < 1")
    nodes, weights = gauss_rule(order)
    gamma = 1 / math.sqrt(1 - beta**2)
    pieces = []
    for s, ws in zip(depth * (nodes + 1) / 2, depth * weights / 2):
        r = s * (nodes[:, None] + 1) / 2
        mu = nodes[None, :]
        t_lab = gamma * (s + beta * r * mu)
        x_lab = gamma * (r * mu + beta * s)
        q_lab = t_lab**2 - x_lab**2 - r**2 * (1 - mu**2)
        t_rest = gamma * (t_lab - beta * x_lab)
        values = r**2 * bdg_kernel(C_INTERVAL * rho * q_lab**2) * ellipsoid_overlap(t_rest, depth, axes)
        pieces.append(ws * s / 2 * math.fsum((weights[:, None] * weights[None, :] * values).ravel()))
    pair = 2 * math.pi * math.fsum(pieces)
    return NORMALIZATION * math.sqrt(rho) * (AxialCap(depth, axes, 0).volume - rho * pair)


def quadratic_remainder_probe(values, step):
    """Third forward difference / step^2: annihilates ANY quadratic jet.

    Necessary diagnostic only, not a fitted jet or proof of little-o. In
    particular s^2*log(s) gives a nonzero constant as step tends to zero.
    """
    _positive(step, "step")
    if len(values) != 4:
        raise ValueError("require B(0), B(h), B(2h), B(3h)")
    return math.fsum(c * v for c, v in zip((-1, 3, -3, 1), values)) / step**2
