"""Finite diagnostics for notes/independent-null-investigation.md.

These are physical-domain quadratures, not a general asymptotic solver.
Canonical action/kernel definitions are imported unchanged. No test of a
sampled error certifies the missing critical signed remainder.
"""

import math

from scipy.integrate import quad


def _nonnegative(*values):
    if any(not math.isfinite(x) or x < 0 for x in values):
        raise ValueError("arguments must be finite and nonnegative")


def _widths(u, duration):
    _nonnegative(u, duration)
    if duration == 0:
        raise ValueError("duration must be positive")


def cap_weight(u, duration):
    """Both (t,z) endpoint measures, after the physical Lorentz boost (IN6)."""
    _widths(u, duration)
    if u == 0 or u >= duration:
        return 0.0
    gap = duration - u
    if gap < 0.05 * u:
        # Positive integral remainder of the third derivative, avoiding
        # cancellation at the cubic physical closing surface.
        return u * gap**3 * quad(
            lambda t: (1-t)**2 * (1/(u+gap*t) + u*u/(u+gap*t)**3),
            0, 1, epsabs=1e-13, epsrel=1e-12)[0]
    return u * ((duration**2 + u**2) * math.log(duration/u)
                - duration**2 + u**2)


def rapidity_weight(u, duration, cutoff=None, short=False):
    """Independent integration of the source overlap, including tau cutoff."""
    _widths(u, duration)
    if cutoff is not None:
        _nonnegative(cutoff)
        if cutoff == 0 or 2*cutoff >= duration:
            raise ValueError("use one physical cutoff 0 < delta < T/2")
    elif short:
        raise ValueError("short requires a physical cutoff")
    if u == 0 or u >= duration:
        return 0.0
    closing = math.log(duration/u)
    bound = 0.0 if cutoff is None or u >= cutoff else math.acosh(cutoff/u)
    lo, hi = (0.0, bound) if short else (bound, closing)
    # Symmetry in eta cancels the 1/2 of the source null-coordinate Jacobian.
    return quad(lambda eta: u * (duration-u*math.exp(eta))
                * (duration-u*math.exp(-eta)), lo, hi,
                epsabs=1e-12, epsrel=1e-11)[0]


def short_weight(u, cutoff, duration):
    """IN7: cutoff is in original time, not merely u < delta."""
    _widths(u, duration)
    _nonnegative(cutoff)
    if cutoff == 0 or 2*cutoff >= duration:
        raise ValueError("use one physical cutoff 0 < delta < T/2")
    if u == 0 or u >= cutoff:
        return 0.0
    h = math.acosh(cutoff/u)
    return u * ((duration**2+u**2)*h
                - 2*duration*math.sqrt(cutoff**2-u**2))


def section_radius(u, r, s):
    """Allowed intermediate z radius from the two actual metric distances."""
    _nonnegative(u, r, s)
    if u <= r+s:
        return 0.0
    return math.sqrt((u*u-(r+s)**2)*(u*u-(r-s)**2)) / (2*u)


def physical_section(u, r, s):
    """Time/real-flat intermediate measure in IN5, integrated before K."""
    radius = section_radius(u, r, s)
    if radius == 0:
        return 0.0
    return 2*quad(lambda z: max(0.0, u-math.hypot(r, z)-math.hypot(s, z)),
                  0, radius, epsabs=1e-12, epsrel=1e-11)[0]


def circle_interval(u, separation, circumference):
    """Actual interval on R_t x R_z x S^1, including all circle routes."""
    _nonnegative(u, separation, circumference)
    if circumference == 0 or separation > circumference/2:
        raise ValueError("use 0 <= separation <= circumference/2, L > 0")

    def distance(x, y):
        a = abs(x-y) % circumference
        return min(a, circumference-a)

    cuts = sorted({0.0, circumference, separation, circumference/2,
                   (separation+circumference/2) % circumference})
    return sum(quad(lambda x: physical_section(u, distance(0, x),
                                              distance(separation, x)),
                    a, b, epsabs=3e-10, epsrel=2e-9)[0]
               for a, b in zip(cuts, cuts[1:]))


def suspended_sphere_weight(u, duration):
    """Integrate the three flat endpoint displacements; recover NP3 (IN10)."""
    _widths(u, duration)
    if u == 0 or u >= duration:
        return 0.0
    return 4*math.pi*u * quad(
        lambda v: cap_weight(v, duration)*math.sqrt(v*v-u*u),
        u, duration, epsabs=1e-11, epsrel=1e-10)[0]


def diamond_action(rho, duration):
    """Exact complete 2D calibration, not a replacement dimensional kernel."""
    _widths(rho, duration)
    return -2*math.expm1(-rho*duration**2/2)


def diamond_target_variation(rho, duration):
    """Total variation AFTER point/all-past-partner cancellation (IN3)."""
    _widths(rho, duration)
    a = rho*duration**2/2
    if a == 0:
        return 0.0
    if a <= 1:
        return diamond_action(rho, duration)
    positive = quad(lambda z: (1-z)*math.exp(-z)*math.log(a/z),
                    0, 1, epsabs=1e-11, epsrel=1e-11)[0]
    # Subtract the exact SIGNED integral: this retains the entire negative
    # tail through a. Direct quadrature over [20,a] can miss its lower end.
    return 4*positive-diamond_action(rho, duration)
