"""Finite diagnostics for C3/F3, not a universal curved-action solver.

Canonical coefficients come from dimension_kernels. The only reused focal
routine solves the dimension-independent circle mechanical action on its
explicitly guarded domain; no 4D kernel/volume/response is imported.
"""

from functools import lru_cache
import math

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import roots_legendre

from dimension_kernels import action_constants, interval_coefficient
from curved4_focal_geometry import physical_segment_action

C3 = float(interval_coefficient(3))
A3, BETA3 = map(float, action_constants(3))
DURATION = 7 / 4


@lru_cache(maxsize=None)
def rule(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 4:
        raise ValueError("integer quadrature order >= 4 required")
    return roots_legendre(order)


def grid(lo, hi, order):
    nodes, weights = rule(order)
    return (lo + hi) / 2 + (hi - lo) / 2 * nodes, (hi - lo) / 2 * weights


def kernel3(z):
    z = np.asarray(z)
    return (1 - 27 * z / 8 + 9 * z * z / 8) * np.exp(-z)


def time_density_interval(source_time, gap, radius, lam):
    """Exact physical volume for Omega^3=1+lam*t^2, not frozen endpoints."""
    if not all(math.isfinite(x) for x in (source_time, gap, radius, lam)):
        raise ValueError("finite interval parameters required")
    if gap < 0 or not 0 <= radius <= gap or lam < 0:
        raise ValueError("requires gap >= radius >= 0 and lam >= 0")
    sigma = (gap - radius) * (gap + radius)
    midpoint = source_time + gap / 2
    return C3 * sigma**1.5 * (1 + lam * (midpoint**2 + gap**2 / 40 + 3 * radius**2 / 80))


def boosted_interval(source, target, density, order=20):
    """Actual weighted 3D diamond using the whole boosted rest-domain map."""
    source, target = np.asarray(source, float), np.asarray(target, float)
    if source.shape != (3,) or target.shape != (3,) or not np.isfinite([source, target]).all():
        raise ValueError("finite three-component endpoints required")
    gap = target[0] - source[0]
    spatial = target[1:] - source[1:]
    radius = np.linalg.norm(spatial)
    if gap <= radius:
        raise ValueError("strict chronological endpoints required")
    direction = spatial / radius if radius else np.array([1., 0.])
    transverse = np.array([-direction[1], direction[0]])
    sigma = (gap - radius) * (gap + radius)
    radial, rw = grid(0, 1, order)
    angles = 2 * math.pi * np.arange(2 * order) / (2 * order)
    result = 0.
    for lo, hi in ((-.5, 0), (0, .5)):
        times, tw = grid(lo, hi, order)
        for aa, wa in zip(times, tw):
            extent = .5 - abs(aa)
            bp = extent * radial[:, None] * np.cos(angles)
            bt = extent * radial[:, None] * np.sin(angles)
            tt = source[0] + gap * (.5 + aa) + radius * bp
            xx = source[1:, None, None] + (
                radius * (.5 + aa) + gap * bp)[None, :, :] * direction[:, None, None]
            xx = xx + math.sqrt(sigma) * bt[None, :, :] * transverse[:, None, None]
            result += wa * extent**2 * (math.pi / order) * np.sum(
                rw[:, None] * radial[:, None] * density(tt, xx[0], xx[1]))
    return sigma**1.5 * result


def slice_interval(source_time, gap, radius, density, order=32):
    """Independent physical time/disk-intersection integral; endpoints on x axis.

    Splits at both disk-lens changes; integrates the actual conformal density.
    No boost or proper-time volume formula is used.
    """
    if not 0 < radius < gap or not math.isfinite(source_time + gap + radius):
        raise ValueError("requires finite gap > radius > 0")
    total = 0.
    edges = [0, (gap - radius) / 2, (gap + radius) / 2, gap]
    for lo_t, hi_t in zip(edges, edges[1:]):
        times, tw = grid(lo_t, hi_t, order)
        for tt, wt in zip(times, tw):
            lo, hi = max(-tt, radius - (gap - tt)), min(tt, radius + gap - tt)
            switch = (tt**2 - (gap - tt)**2 + radius**2) / (2 * radius)
            cuts = sorted(set([lo, hi, min(hi, max(lo, switch))]))
            for left, right in zip(cuts, cuts[1:]):
                xs, xw = grid(left, right, order)
                for xx, wx in zip(xs, xw):
                    height = math.sqrt(max(0, min(tt**2 - xx**2,
                        (gap - tt)**2 - (xx - radius)**2)))
                    ys, yw = grid(-height, height, order)
                    total += wt * wx * np.dot(yw, density(source_time + tt, xx, ys))
    return total


def cap_targets(b, slope, tilt):
    """Independent C3.8 curvature integral and induced angle/length integral."""
    if not b > 0 or not 0 < slope or not 0 <= tilt or slope + tilt >= 1:
        raise ValueError("requires b>0, slope>0, tilt>=0, slope+tilt<1")
    bulk = 2 * math.pi * slope * quad(lambda r: r * (1-r*r) * (
        -8*b + 4*b*b*r*r/(1+b*r*r)), 0, 1, epsabs=1e-12)[0]
    joint = math.pi / slope * (1 - tilt*tilt + slope*slope) * (1+b)
    return bulk, joint


def thin_torus_action(rho, duration=.6, period=4., lam=.5, order=28,
                      cutoff=None, pair_order="gap", fields=None):
    """Complete finite-density quadrature, not a convergence oracle.

    Omega^3=1+lam*t^2 on a square torus, 0<T<L/2. Every causal displacement
    and both time endpoints are included. Optional endpoint fields are functions
    of time. Returns (full, short, long); point belongs only to short.
    The two integration orders are gap/radius and radius/gap, not a duplicate
    evaluation of the same nodes. Temporal cutoff is integrated by splitting.
    """
    if not all(math.isfinite(x) for x in (rho, duration, period, lam)) or (
            rho <= 0 or duration <= 0 or period <= 2*duration or lam < 0):
        raise ValueError("requires rho>0, 0<T<L/2, lam>=0")
    cutoff = duration / 3 if cutoff is None else cutoff
    if not 0 < cutoff < duration or pair_order not in ("gap", "radius"):
        raise ValueError("invalid cutoff or integration order")
    chi, phi = fields if fields is not None else (lambda t: np.ones_like(t),)*2
    ts, ws = grid(-duration/2, duration/2, order)
    point = A3 * rho**(2/3) * period**2 * np.dot(ws,
        (1+lam*ts**2)*chi(ts)*phi(ts))
    pairs = np.zeros(2)

    def time_integral(gap, radius):
        mids, mw = grid(-(duration-gap)/2, (duration-gap)/2, order)
        t0, t1 = mids-gap/2, mids+gap/2
        volume = C3 * ((gap-radius)*(gap+radius))**1.5 * (
            1+lam*(mids*mids+gap*gap/40+3*radius*radius/80))
        return np.dot(mw, (1+lam*t0*t0)*(1+lam*t1*t1)*chi(t0)*phi(t1)*kernel3(rho*volume))

    for index, (lo, hi) in enumerate(((0, cutoff), (cutoff, duration))):
        if pair_order == "gap":
            gaps, gw = grid(lo, hi, order)
            for gap, wg in zip(gaps, gw):
                radii, rw = grid(0, gap, order)
                pairs[index] += wg * sum(wr*2*math.pi*r*time_integral(gap, r)
                                          for r, wr in zip(radii, rw))
        else:
            for rl, rh in ((0, lo), (lo, hi)):
                if rh == rl:
                    continue
                radii, rw = grid(rl, rh, order)
                for radius, wr in zip(radii, rw):
                    gaps, gw = grid(max(lo, radius), hi, order)
                    pairs[index] += wr * 2*math.pi*radius * sum(
                        wg*time_integral(gap, radius) for gap, wg in zip(gaps, gw))
    response = -BETA3*rho**(5/3)*period**2*pairs
    return point + sum(response), point + response[0], response[1]


def thin_torus_action_phase(rho, duration=.6, period=4., lam=.5, order=24,
                            cutoff=.2):
    """Independent volume-phase quadrature of the SAME complete thin action.

    Numerical panels resolve density-dependent scales; the physical cutoff
    remains fixed. No large-density convergence claim follows from this helper.
    Includes the entire finite phase domain, not a discarded exponential tail.
    """
    if not all(math.isfinite(x) for x in (rho, duration, period, lam, cutoff)) or (
            rho <= 0 or duration <= 0 or period <= 2*duration or lam < 0 or
            not 0 < cutoff < duration):
        raise ValueError("requires rho>0, 0<T<L/2, lam>=0, 0<cutoff<T")
    scale = (C3*rho)**(-2/3)
    # s below denotes the dimensionless volume phase, NOT physical time.
    temporal = sorted(set([0., cutoff, duration, *[x*math.sqrt(scale)
        for x in (.5, 1, 2, 4, 8, 16) if x*math.sqrt(scale) < duration]]))
    pairs = np.zeros(2)
    for left, right in zip(temporal, temporal[1:]):
        gaps, gw = grid(left, right, order)
        for gap, wg in zip(gaps, gw):
            mids, mw = grid(-(duration-gap)/2, (duration-gap)/2, order)
            h0 = 1+lam*(mids*mids+gap*gap/16)
            cc = 3*lam/80
            top = gap*gap*(h0-cc*gap*gap)**(2/3)/scale
            inner = np.zeros_like(mids)
            # One vectorized fixed-domain map per panel and midpoint.
            edges = [0., .25, 1., 3., 6., 14., float(max(14., np.max(top)))]
            for lo, hi in zip(edges, edges[1:]):
                lows, highs = np.minimum(lo, top), np.minimum(hi, top)
                nodes, weights = rule(order)
                low_roots, high_roots = np.sqrt(lows), np.sqrt(highs)
                root = (low_roots[:, None]+high_roots[:, None])/2 + (
                    high_roots-low_roots)[:, None]/2*nodes
                phase = root*root
                pw = (high_roots-low_roots)[:, None]*weights*root
                w = scale*phase
                sigma = w/h0[:, None]**(2/3)
                for _ in range(6):
                    hh = h0[:, None]-cc*sigma
                    derivative = hh**(2/3)-2*cc*sigma/(3*hh**(1/3))
                    sigma -= (sigma*hh**(2/3)-w)/derivative
                hh = h0[:, None]-cc*sigma
                derivative = hh**(2/3)-2*cc*sigma/(3*hh**(1/3))
                inner += math.pi*scale*np.sum(pw*kernel3(phase**1.5)/derivative, axis=1)
            t0, t1 = mids-gap/2, mids+gap/2
            index = 0 if gap < cutoff else 1
            pairs[index] += wg*np.dot(mw, (1+lam*t0*t0)*(1+lam*t1*t1)*inner)
    point = A3*rho**(2/3)*period**2*(duration+lam*duration**3/12)
    response = -BETA3*rho**(5/3)*period**2*pairs
    return point+sum(response), point+response[0], response[1]


def focal_time_weight(length, energy, cutoff=None, short=False):
    """Actual 3D both-time weight, not the 4D z-integrated fractional weight."""
    if not all(math.isfinite(x) for x in (length, energy)) or length <= 0:
        raise ValueError("finite positive length and finite energy required")
    if cutoff is not None and not 0 < cutoff < DURATION:
        raise ValueError("cutoff must lie in (0,T)")
    if short and cutoff is None:
        raise ValueError("short requires a cutoff")
    gap = length/2 + energy
    if gap < 0:
        raise ValueError("negative temporal separation is not a physical pair")
    weight = max(0, DURATION-gap)
    if cutoff is None:
        return weight
    return weight if ((gap < cutoff) == short) else 0.


def physical_axis_volume(length, excess, order=24):
    """Actual W3(L,0,0,e) for 0<L<=pi, small e>0, both tips and x signs.

    Poincare/coercivity exclude other circle components on this guarded range.
    This is not the polynomial optical model or a general S_L(p,q) solver.
    """
    if not 0 < length <= math.pi or not 0 < excess <= .001:
        raise ValueError("requires 0<L<=pi, 0<excess<=.001")
    nodes, weights = rule(order)
    total = 0.
    # The pi-length coercive bound also bounds shorter intervals (rescale paths).
    amplitude = math.sqrt(4/math.sqrt(math.pi)*math.sqrt(excess)+8/math.pi*excess)
    for ss, sw in zip(length/4*(1+nodes), length/4*weights):
        def cost(x):
            return physical_segment_action(ss, x)+physical_segment_action(length-ss, x)
        # A conservative global bound, not a fitted focal profile.
        top = min(math.pi/4-1e-9, amplitude+math.sqrt(8*excess*length/3))
        end = brentq(lambda x: cost(x)-excess, 0, top, xtol=2e-13, rtol=2e-13)
        xs = end/2*(1+nodes)
        inner = end/2*np.dot(weights, [max(0, excess-cost(x)) for x in xs])
        total += sw*inner
    return 4*total  # both tips and both screen signs


def regular_axis_leading(length):
    """Derived regular null-index coefficient, no signed kernel."""
    if not 0 < length < math.pi:
        raise ValueError("requires 0<L<pi")
    return 4/3*quad(lambda s: math.sqrt(
        2*math.sin(s)*math.sin(length-s)/math.sin(length)), 0, length,
        epsabs=1e-12)[0]


def focal_axis_leading():
    return 16/5*(math.pi/4)**(-.25)


def quartic_profile(excess, r):
    """Exact polynomial integration of ALL 3D model wells, not physical W3."""
    if not math.isfinite(excess) or excess <= 0 or not math.isfinite(r) or abs(r) > .5:
        raise ValueError("requires finite E>0, |r|<=1/2")
    roots = np.roots([1, 4*r, 1, 0, -excess])
    real = sorted(z.real for z in roots if abs(z.imag) < 1e-7)
    # Repeated contact roots need not split the outer positive interval:
    # integration by an exact antiderivative handles the zero inside it.
    def primitive(u):
        return excess*u-u**3/3-r*u**4-u**5/5
    total = 0.
    for lo, hi in zip(real, real[1:]):
        probe = lo + (hi-lo)*.37
        if probe**4+4*r*probe**3+probe*probe <= excess:
            total += primitive(hi)-primitive(lo)
    return total


def quadratic_tube_union(excess, separation, split):
    """Physical pointwise max of two quadratic tip clocks (model only).

    Returns union, sum. Integrates over the screen instead of adding route
    volumes before the nonlinear kernel. separation is velocity difference.
    """
    if min(excess, separation, split) <= 0 or not all(
            math.isfinite(x) for x in (excess, separation, split)):
        raise ValueError("positive finite model parameters required")
    width = math.sqrt(2*split*excess)
    center = split*separation/2
    single = 4/3*math.sqrt(2*split)*excess**1.5
    overlap = 0.
    if center < width:
        overlap = 2*quad(lambda x: max(0, excess-(x+center)**2/(2*split)),
                         0, width-center, epsabs=1e-14)[0]
    return 2*single-overlap, 2*single
