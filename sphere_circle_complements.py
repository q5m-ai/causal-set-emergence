"""Finite evidence for the actual 4D producers in sphere-circle-complements.md.

The phase is the exact fixed-diamond integral, not its curvature polynomial.
Quadratures and finite differences are diagnostics, not analytic certificates.
No action, order, probability or formal-production API is changed.
"""

from functools import lru_cache

import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq

from general_metric_gate import gauss_rule, product_curvature
from sphere_circle_focusing import PAIR_FACTOR, time_weight

FLAT_VOLUME = np.pi / 24


@lru_cache(maxsize=12)
def _diamond_rule(order):
    """Four-dimensional rest diamond, with the unused B3 integrated exactly."""
    nodes, weights = gauss_rule(order)
    arrays = [[], [], [], []]
    for sign in (-1, 1):
        a = sign * nodes[:, None, None] / 2
        radius = 0.5 - np.abs(a)
        b1 = radius * (2 * nodes[None, :, None] - 1)
        height = np.sqrt(radius**2 - b1**2)
        eta = np.pi * (nodes[None, None, :] - 0.5)
        b2 = height * np.sin(eta)
        measure = (2 * np.pi * radius * height**2 * np.cos(eta)**2
                   * weights[:, None, None] * weights[None, :, None]
                   * weights[None, None, :])
        for dest, value in zip(arrays, np.broadcast_arrays(a, b1, b2, measure)):
            dest.append(value.ravel())
    return tuple(np.concatenate(parts) for parts in arrays)


def _sinc(z):
    """Stable entire sinc, including its tiny imaginary part at the origin.

    This evaluates the elementary factor, not a truncated volume/phase model.
    At |z|<.01 the omitted series term is below 1e-40.
    """
    z2 = z*z
    series = 1 + z2*(-1/6 + z2*(1/120 + z2*(-1/5040 + z2*(
        1/362880 + z2*(-1/39916800 + z2/6227020800)))))
    return np.where(np.abs(z) < .01, series, np.sinc(z/np.pi))


def phase_factor(y, q, order=12):
    """Actual H(y,q) of SC4, including y=0 and q=0.

    A tiny imaginary q is allowed for complex-step differentiation. The guard
    prevents use through the secondary spherical transition or beyond the slab.
    """
    qr = float(np.real(q))
    if not 0 <= y < np.pi**2 or qr < 0:
        raise ValueError("requires 0<=y<pi^2 and real(q)>=0")
    theta = np.sqrt(y)
    if np.sqrt(y + qr) > 4 or np.sqrt(y + qr) >= 2*np.pi-theta:
        raise ValueError("phase is outside the regular-side slab domain")
    a, b1, b2, weights = _diamond_rule(order)
    u = np.sqrt(y + q)
    rs = np.sqrt((theta*(0.5+a)+u*b1)**2 + q*b2*b2)
    ss = np.sqrt((theta*(0.5-a)-u*b1)**2 + q*b2*b2)
    denominator = (_sinc((rs+ss+theta)/2)*_sinc((rs+ss-theta)/2)
                   * _sinc((theta+rs-ss)/2)*_sinc((theta-rs+ss)/2))
    ratio = _sinc(rs)*_sinc(ss)/np.sqrt(denominator)
    return np.sum(weights * ratio) / FLAT_VOLUME


def phase_factor_derivative(y, q, order=12):
    """H_q by differentiating the actual analytic integrand (complex step)."""
    return np.imag(phase_factor(y, q + 1e-24j, order)) / 1e-24


def inverse_phase(y, v, order=12):
    """Return Q and Q_v from the actual SC4 phase, not a fitted jet."""
    if v < 0 or not 0 <= y < np.pi**2:
        raise ValueError("requires v>=0 and 0<=y<pi^2")
    if v == 0:
        return 0.0, 1 / np.sqrt(phase_factor(y, 0, order))
    cap = min(16-y, 4*np.pi*(np.pi-np.sqrt(y))) * (1-1e-10)
    hi = min(2*v, cap)
    phase = lambda q: q*np.sqrt(phase_factor(y, q, order))
    while phase(hi) < v and hi < cap:
        hi = min(2*hi, cap)
    if phase(hi) < v:
        raise ValueError("phase exceeds the regular-side slab cap")
    q = brentq(lambda q: phase(q)-v, 0, hi, xtol=1e-300, rtol=2e-14)
    h = phase_factor(y, q, order)
    hq = phase_factor_derivative(y, q, order)
    return q, 1 / (np.sqrt(h) + q*hq/(2*np.sqrt(h)))


def time_radius(duration, m, v, order=12):
    """Actual moving R_T in SC6, on directions where the regular chart exists."""
    if not 0 < duration <= 4 or not -1 <= m <= 1 or v < 0:
        raise ValueError("requires 0<T<=4, |m|<=1, v>=0")
    k = 1-m*m
    if k*duration**2 >= np.pi**2:
        raise ValueError("direction is outside the regular sphere chart")
    if v == 0:
        return duration
    phase = lambda q: q*np.sqrt(phase_factor(k*(duration**2-q), q, order))
    if phase(duration**2) <= v:
        raise ValueError("phase reaches or exceeds the time-contact origin")
    # A small bracket avoids evaluating a large timelike diamond unnecessarily.
    hi = min(2*v, duration**2)
    while phase(hi) < v:
        hi = min(2*hi, duration**2)
    q = brentq(lambda q: phase(q)-v, 0, hi, xtol=1e-300, rtol=2e-14)
    return np.sqrt(duration**2-q)


def radial_amplitude(r, m, v, order=12):
    """The full f of SC6/SC9, including both time contacts and both measures."""
    y = (1-m*m)*r*r
    q, qv = inverse_phase(y, v, order)
    tau = np.sqrt(r*r+q)
    if tau == 0:  # removable r=0,v=0 after multiplying the spatial measure
        return 0.0
    return r*r*np.sinc(np.sqrt(y)/np.pi)*qv*(4/tau-1)


def short_density(v, delta=0.2, order=12, radial_order=36, direction_order=10):
    """Actual near-zero density B_s, not its two-log expansion.

    The sinh quadrature resolves the origin without deleting any radial range.
    delta is fixed for the whole evaluation; it does not track phase/density.
    """
    if not 0 < delta < 0.25 or v < 0:
        raise ValueError("requires 0<delta<1/4 and v>=0")
    rr, wr = gauss_rule(radial_order)
    mm, wm = gauss_rule(direction_order)
    total = 0.0
    for m, weight in zip(mm, wm):
        top = time_radius(delta, m, v, order)
        if v:
            height = np.arcsinh(top/np.sqrt(v))
            radii = np.sqrt(v)*np.sinh(height*rr)
            jac = np.sqrt(v)*height*np.cosh(height*rr)
        else:
            radii, jac = top*rr, top
        total += weight*np.sum(wr*jac*np.array([
            radial_amplitude(r, m, v, order) for r in radii]))
    return PAIR_FACTOR*total  # C/2 times both signs of m


def offcut_density(v, delta=0.2, sphere_cap=2.8, order=16,
                   radial_order=18, direction_order=18):
    """Actual B_o of SC6; both radial/time roots and the moving m_* retained."""
    if not 0 < delta < sphere_cap < np.pi or v < 0:
        raise ValueError("requires 0<delta<sphere_cap<pi and v>=0")
    qcut, _ = inverse_phase(sphere_cap**2, v, order)
    split = np.sqrt(1-sphere_cap**2/(16-qcut))
    nn, wn = gauss_rule(direction_order)
    rr, wr = gauss_rule(radial_order)
    total = 0.0
    for lo, hi, capped in ((0, split, True), (split, 1, False)):
        for m, weight in zip(lo+(hi-lo)*nn, (hi-lo)*wn):
            bottom = time_radius(delta, m, v, order)
            top = (sphere_cap/np.sqrt(1-m*m) if capped
                   else time_radius(4, m, v, order))
            radii = bottom+(top-bottom)*rr
            total += weight*(top-bottom)*np.sum(wr*np.array([
                radial_amplitude(r, m, v, order) for r in radii]))
    return PAIR_FACTOR*total


def reduced_density(v, delta=0.2, sphere_cap=2.8, short=False, order=16):
    """Independent F3 density integral in theta, with the cusp explicitly split.

    This is for positive phase only; polar-axis values have measure zero.
    It retains G_short/G_delta with their factor 4, not a delta-duration slab.
    """
    if v <= 0 or not 0 < delta < sphere_cap < np.pi:
        raise ValueError("requires v>0 and 0<delta<sphere_cap<pi")
    contact = time_radius(delta, 0, v, order)

    def integrand(theta):
        q, qv = inverse_phase(theta*theta, v, order)
        u = np.sqrt(theta*theta+q)
        return np.sin(theta)*time_weight(u, delta, short=short)*qv/(2*u)

    if short:
        value = quad(integrand, 0, contact, epsabs=3e-10, epsrel=3e-10)[0]
    else:
        value = sum(quad(integrand, lo, hi, epsabs=3e-9, epsrel=3e-10)[0]
                    for lo, hi in ((0, contact), (contact, sphere_cap)))
    return PAIR_FACTOR*value


def check_complement_identities():
    """Exact algebra of derived 4D jets/moments and independent target check."""
    y, q, v, k = sp.symbols("y q v k")
    # Integrate the Qs quadratic term with actual D0 moments, not a desired jet.
    mean_a2, mean_b2 = sp.Rational(1, 60), sp.Rational(1, 30)
    average_ratio_correction = (
        y/2 - 2*y*mean_a2 - 2*(y+q)*mean_b2 - 2*q*mean_b2)/12
    assert sp.expand(average_ratio_correction-y/30+q/90) == 0
    # Inverse coefficient comparison at common total degree, y~v.
    scale = sp.symbols("scale")
    inverse = v-y*v/60+v*v/180
    residual = inverse*(1+y/60-inverse/180)-v
    assert sp.series(residual.subs({y: scale*y, v: scale*v}), scale, 0, 3).removeO() == 0
    log2 = sp.Rational(1, 720) + (sp.Rational(1, 90)+k/40)/4 + 33*k/960
    assert sp.simplify(log2-sp.Rational(1, 240)-13*k/320) == 0
    m = sp.symbols("m")
    assert sp.integrate(2*log2.subs(k, 1-m*m), (m, -1, 1)) == sp.Rational(1, 8)
    j = sp.symbols("j")
    moment = -j*(j-1)*(j-2)*sp.gamma((j+1)/2)/12
    assert all(moment.subs(j, n) == 0 for n in range(3))
    assert sp.diff(moment, j).subs(j, 1) == sp.Rational(1, 12)
    assert sp.simplify(sp.diff(moment, j).subs(j, 2)) == -sp.sqrt(sp.pi)/12
    c, C = sp.pi/24, 160*sp.pi**2
    assert C/(12*c) == 320*sp.pi
    pair_finite = -C*sp.sqrt(sp.pi)/(96*c**sp.Rational(3, 2))
    assert sp.simplify(pair_finite+80*sp.sqrt(6)*sp.pi) == 0
    radius, scalar, _ = product_curvature()
    target = scalar.subs(radius, 1)/2 * 4*(4*sp.pi*20)
    assert sp.simplify(-4/sp.sqrt(6)*pair_finite-target) == 0
    print("PASS: #152 actual 4D phase jet, two logarithms, signed point/bulk normalization")


if __name__ == "__main__":
    check_complement_identities()
