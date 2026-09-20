"""Numerical checks for the proof draft; quadrature is not a proof.

All actions returned here are normalized as l_p**2 * E[S] / hbar.
Use mpmath.workdps to choose precision. Geometric parameters stay fixed
when the density tends to infinity.
"""

from mpmath import mp


def kernel(z):
    z = mp.mpf(z)
    return (1 - 9 * z + 8 * z**2 - mp.mpf(4) * z**3 / 3) * mp.exp(-z)


def _null_parameters(T, a):
    T, a = mp.mpf(T), mp.mpf(a)
    if not 0 < a <= T:
        raise ValueError("require 0 < a <= T (a=T is the uncut check)")
    return T, a


def null_cap_area(T, a):
    T, a = _null_parameters(T, a)
    return mp.pi * a * (2 * T - a)


def null_cap_volume(T, a):
    T, a = _null_parameters(T, a)
    return mp.pi * a**2 * T * (3 * T - 2 * a) / 24


def null_cap_weight(sigma, T, a):
    """Exact coarea weight (9); sigma is squared proper time, not time."""
    T, a = _null_parameters(T, a)
    sigma = mp.mpf(sigma)
    if sigma < 0:
        raise ValueError("sigma must be nonnegative")
    if sigma >= a * T:
        return mp.mpf(0)
    if sigma == 0:
        return null_cap_area(T, a) / 4
    return mp.pi / 4 * (
        a * (2 * T - a)
        - 2 * (1 - a / T) * sigma
        - sigma**2 / T**2
        - 2 * sigma * mp.log(a * T / sigma)
    )


def null_cap_weight_geometric(sigma, T, a):
    """Independent radial/solid-angle quadrature, not formula (9)."""
    T, a = _null_parameters(T, a)
    sigma = mp.mpf(sigma)
    if not 0 < sigma < a * T:
        raise ValueError("geometric check requires 0 < sigma < a*T")
    rmax = (T**2 - sigma) / (2 * T)
    transition = abs(a**2 - sigma) / (2 * a)

    def integrand(r):
        if r == 0:
            return mp.mpf(0)
        w = mp.sqrt(r**2 + sigma)
        solid_angle = 2 * mp.pi * min(2, max(0, 1 + (a - w) / r))
        return solid_angle * r**2 / (2 * w)

    points = [mp.mpf(0)]
    if 0 < transition < rmax:
        points.append(transition)
    points.append(rmax)
    return mp.quad(integrand, points)


def null_cap_action(rho, T, a):
    """Positive, scaled one-dimensional integral (6), (9)."""
    T, a = _null_parameters(T, a)
    rho = mp.mpf(rho)
    if rho <= 0:
        raise ValueError("rho must be positive")
    scale = mp.sqrt(mp.pi * rho / 24)
    upper = a * T * scale
    # W(sigma) lies in [0, W(0)]. This cutoff has relative error <= erfc(end)
    # when it truncates the integral, well below the working precision.
    end = min(upper, mp.sqrt((mp.dps + 10) * mp.log(10)))
    points = [mp.mpf(0)] + [mp.mpf(x) for x in (1, 3, 8) if x < end] + [end]
    return 8 / mp.sqrt(mp.pi) * mp.quad(
        lambda u: null_cap_weight(u / scale, T, a) * mp.exp(-u**2), points
    )


def interval_kernel_integral(rho, duration):
    """Direct two-dimensional integration for the independent check of (3)."""
    rho, duration = mp.mpf(rho), mp.mpf(duration)
    if rho <= 0 or duration <= 0:
        raise ValueError("rho and duration must be positive")
    upper = duration / mp.sqrt(2)
    return 2 * mp.pi * mp.quad(
        lambda v: mp.quad(
            lambda u: (v - u) ** 2 * kernel(mp.pi * rho * u**2 * v**2 / 6),
            [0, v],
        ),
        [0, upper],
    )


def plane_auxiliary(u, derivative=0):
    """F_1 and its first three derivatives, by differentiating under the integral.

    Reference quadrature for moderate u, independent of the hypergeometric
    representation used in plane_kernel. Narrow layers require extra care
    for very large u; this evaluator is only used at moderate arguments.
    """
    u = mp.mpf(u)
    if u < 0 or derivative not in (0, 1, 2, 3):
        raise ValueError("require u >= 0 and derivative in {0,1,2,3}")
    z = mp.pi * u**4 / 24

    def polynomial(x):
        return (
            1,
            3 - 4 * x,
            6 - 36 * x + 16 * x**2,
            6 - 204 * x + 288 * x**2 - 64 * x**3,
        )[derivative]

    def integrand(v):
        x = z * (1 - v**2) ** 2
        return v**2 * polynomial(x) * mp.exp(-x)

    return 4 * mp.pi * u ** (3 - derivative) * mp.quad(integrand, [0, 1])


def plane_kernel(u):
    """Signed G_1(u)=F_1''(u)/(2*pi*sqrt(6)), not a positive density.

    The 2F2 representation follows by differentiating the beta-integral
    power series. In particular G(u) ~ -2*sqrt(6)/(pi*u**3).
    """
    u = mp.mpf(u)
    if u < 0:
        raise ValueError("u must be nonnegative")
    z = mp.pi * u**4 / 24
    return 4 * u / mp.sqrt(6) * mp.hyper(
        [1, mp.mpf(3) / 2], [mp.mpf(3) / 4, mp.mpf(5) / 4], -z
    )


def plane_future_kernel_integral(rho, H):
    """Direct future-cone integral Q_rho(H) used to check (12)."""
    rho, H = mp.mpf(rho), mp.mpf(H)
    if rho <= 0 or H <= 0:
        raise ValueError("rho and H must be positive")
    return 4 * mp.pi * mp.quad(
        lambda t: mp.quad(
            lambda r: r**2 * kernel(mp.pi * rho * (t**2 - r**2) ** 2 / 24),
            [0, t],
        ),
        [0, H],
    )


def _ellipsoid_parameters(depth, axes):
    depth = mp.mpf(depth)
    axes = tuple(mp.mpf(b) for b in axes)
    if len(axes) != 3 or not 0 < 2 * depth < min(axes):
        raise ValueError("require three positive axes and 0 < 2*depth < min(axes)")
    return depth, axes


def ellipsoid_limit(depth, axes):
    depth, axes = _ellipsoid_parameters(depth, axes)
    return 2 * mp.pi * mp.fprod(axes) / depth


def ellipsoid_action(rho, depth, axes):
    """Finite-density graph-cap action from (13) and exact ellipsoid coarea.

    This integrates the signed kernel, including its negative tail.
    """
    depth, axes = _ellipsoid_parameters(depth, axes)
    rho = mp.mpf(rho)
    if rho <= 0:
        raise ValueError("rho must be positive")
    upper = depth * mp.root(rho, 4)
    points = [mp.mpf(0)]
    for value in (1, 2, 3):
        if value < upper:
            points.append(mp.mpf(value))
    value = mp.mpf(4)
    while value < upper:
        points.append(value)
        value *= 2
    points.append(upper)
    integral = mp.quad(
        lambda u: mp.sqrt(max(0, 1 - u / upper)) * plane_kernel(u), points
    )
    return ellipsoid_limit(depth, axes) * integral
