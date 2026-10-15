"""Finite diagnostics for the audited 3D cluster estimates.

Geometric clock/Jacobi checks and generating-family panels are separate.
Circular controls obey terminal null-covector identities, but no panel is
asserted to be a Lorentzian point-source realization, G-SS counterexample
or numerical certificate of a continuum limit.
"""

from functools import lru_cache
import math

import mpmath as mp
import numpy as np
from scipy.optimize import brentq


def phase_scales(volume, quartic):
    """R,H,K with q*R**5+R**7=v, H=v/R, K=v/R**3.

    Dimensionless bracketing avoids an absolute root tolerance at tiny v.
    These are estimate scales, not a replacement interval volume or cutoff.
    """
    if (not math.isfinite(volume) or volume <= 0 or
            not math.isfinite(quartic) or quartic < 0):
        raise ValueError("finite v>0 and q>=0 required")
    lv = math.log(volume)
    lr = lv/7
    if quartic:
        lr = min(lr, (lv-math.log(quartic))/5)
    a = math.exp(math.log(quartic)+5*lr-lv) if quartic else 0.
    b = math.exp(7*lr-lv)
    y = brentq(lambda z: a*z**5+b*z**7-1, .5, 1.01,
               xtol=1e-14, rtol=1e-14)
    lr += math.log(y)
    return tuple(math.exp(z) for z in (lr, lv-lr, lv-3*lr))


def screen_integral(coefficients, excess, radius=1.):
    """Integral [-r,r] of [h-D(z)]_+ for a polynomial D, in ascending order.

    All real roots and all components are retained. Floating polynomial root
    isolation is a diagnostic, not a rigorous enclosure or physical volume.
    """
    coefficients = np.asarray(coefficients, dtype=float)
    if (coefficients.ndim != 1 or not len(coefficients) or
            np.any(~np.isfinite(coefficients)) or
            not math.isfinite(excess) or not math.isfinite(radius) or radius <= 0):
        raise ValueError("finite coefficients/excess and positive radius required")
    p = np.polynomial.Polynomial(-coefficients)
    p.coef[0] += excess
    edges = [-radius, radius]
    for root in p.roots():
        if abs(root.imag) <= 1e-9*max(1., abs(root.real)):
            if -radius < root.real < radius:
                edges.append(float(root.real))
    edges = sorted(set(edges))
    primitive = p.integ()
    return float(sum(primitive(hi)-primitive(lo)
                     for lo, hi in zip(edges, edges[1:])
                     if p((lo+hi)/2) > 0))


def cubic_negative_part_bound(k, quartic, sixth_bound, negative_mass, radius):
    """Explicit loose projection bound for |b| in D=k*z²+b*z³+c*z⁴+d*z⁵+R6.

    Requires |R6|<=sixth_bound*|z|^6 and negative_mass=int D_- on [-r,r].
    This routine checks inputs, not those analytic hypotheses.
    """
    values = (k, quartic, sixth_bound, negative_mass, radius)
    if (not all(math.isfinite(x) for x in values) or k < 0 or
            sixth_bound < 0 or negative_mass < 0 or radius <= 0):
        raise ValueError("finite values, k,M,negative_mass>=0 and r>0 required")
    return (105*k/radius + 63*max(quartic, 0)*radius +
            90*sixth_bound*radius**3 + 315*negative_mass/radius**4)


def accumulating_profile(u):
    """One fixed smooth flat profile, not an asserted Lorentzian realization."""
    u = mp.mpf(u)
    if not mp.isfinite(u):
        raise ValueError("finite state required")
    return mp.exp(-1/u**2)*mp.sin(mp.pi/u)**2 if u else mp.mpf(0)


def accumulating_zero_curvature(n):
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError("positive integer required")
    return 2*mp.pi**2*n**4*mp.exp(-n*n)


def _mp_scales(v, q):
    r = v**(mp.mpf(1)/7)
    if q:
        r = min(r, (v/q)**(mp.mpf(1)/5))
    a, b = q*r**5/v, r**7/v
    y = mp.findroot(lambda z: a*z**5+b*z**7-1, (mp.mpf('.8'), mp.mpf(1)))
    r *= y
    return r, v/r, v/r**3


@lru_cache(maxsize=8)
def accumulating_well_diagnostic(n):
    """Actual screen-panel quadrature for a finite active block of one germ.

    The endpoint controls and excess vary; the smooth profile is fixed.
    Returned log ratios avoid underflow. No spacetime action is computed.
    n is deliberately bounded because this is a finite regression diagnostic.
    """
    if isinstance(n, bool) or not isinstance(n, int) or not 4 <= n <= 16:
        raise ValueError("diagnostic integer 4<=n<=16 required")
    jmax = math.ceil(5*n/4)+1
    digits = math.ceil(4*jmax*jmax/math.log(10))+80
    with mp.workdps(digits):
        center = mp.mpf(1)/n
        radius = 19*center/100
        A = mp.exp(-4*jmax*jmax)
        # Circular controls have terminal covectors null for a timelike
        # Minkowski clock; use sin² to avoid cancellation in 1-cos.
        excess = 4*A*mp.sin(radius/2)**2
        potential = lambda u: accumulating_profile(u)+4*A*mp.sin((u-center)/2)**2
        nodes, weights = np.polynomial.legendre.leggauss(16)
        wells = []
        volume = mp.mpf(0)
        for j in range(max(1, math.floor(5*n/6)-1), jmax+1):
            zero = mp.mpf(1)/j
            if abs(zero-center) > radius:
                continue
            curvature = accumulating_zero_curvature(j)
            derivative = lambda u: mp.diff(accumulating_profile, u)+2*A*mp.sin(u-center)
            root = mp.findroot(lambda u: derivative(u)/curvature, zero,
                               df=lambda u: (mp.diff(accumulating_profile, u, 2)+2*A*mp.cos(u-center))/curvature,
                               solver='newton')
            depth = potential(root)
            h = excess-depth
            if h <= 0:
                continue
            k = mp.diff(potential, root, 2)/2
            q = max(mp.diff(potential, root, 4)/24, mp.mpf(0))
            width = mp.sqrt(h/k)
            normalized = lambda z: (potential(root+width*z)-depth)/h-1
            # This finite quadrature needs a relative root tolerance, not every
            # working digit lost in subtracting nearly equal tiny depths.
            lo = mp.findroot(normalized, (mp.mpf('-1.1'), mp.mpf('-.9')),
                             tol=mp.mpf('1e-100'))
            hi = mp.findroot(normalized, (mp.mpf('.9'), mp.mpf('1.1')),
                             tol=mp.mpf('1e-100'))
            if max(abs(normalized(lo)), abs(normalized(hi))) > mp.mpf('1e-40'):
                raise ArithmeticError("unresolved normalized panel root")
            half, mid = (hi-lo)/2, (hi+lo)/2
            integral = mp.fsum(mp.mpf(float(w)) *
                              (excess-potential(root+width*(mid+half*mp.mpf(float(z)))))
                              for z, w in zip(nodes, weights))
            volume += width*half*integral
            wells.append((k, q, h, depth))
        if not wells or volume <= 0:
            raise ArithmeticError("positive active block required")
        ratios = [mp.log10(k/_mp_scales(volume, q)[2]) for k, q, _, _ in wells]
        barriers = [mp.log10(h/(k*k/(q+mp.sqrt(k)))) for k, q, h, _ in wells]
        return {
            'active_wells': len(wells),
            'log10_screen_volume': float(mp.log10(volume)),
            'min_log10_good_ratio': float(min(ratios)),
            'max_log10_excess_barrier_ratio': float(max(barriers)),
        }
