"""Finite diagnostics for aggregate 3D union/variational estimates.

The parabolic caps and affine-arrival ensembles are analytic controls, not
Lorentzian point-source realizations or complete-action counterexamples.
The single nonlinear kernel must always see the aggregate volume.
"""

import math

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq


def _vectors(*values, positive=()):
    arrays = tuple(np.asarray(v, dtype=float) for v in values)
    if (not arrays or arrays[0].ndim != 1 or not arrays[0].size or
            any(a.shape != arrays[0].shape or not np.isfinite(a).all()
                for a in arrays)):
        raise ValueError("nonempty finite vectors of equal shape required")
    if any(np.any(arrays[i] <= 0) for i in positive):
        raise ValueError("positive entries required")
    return arrays


def morse_volume(clock, arrivals, amplitudes):
    """Sum of positive Morse volumes, not a sum of kernels or inverses."""
    u, a = _vectors(arrivals, amplitudes, positive=(1,))
    if not math.isfinite(clock):
        raise ValueError("finite clock required")
    return float(np.dot(a, np.maximum(clock-u, 0)**1.5))


def aggregate_inverse(phase, arrivals, amplitudes):
    """Inverse of sum A_i*(t-U_i)_+^(3/2), with phase = volume^(2/3).

    This diagnostic absorbs c3; the physical action's c3 is not redefined.
    Relative bracketing resolves small clock increments without an absolute
    root tolerance. Arbitrarily large/small floating inputs may be rejected.
    """
    u, a = _vectors(arrivals, amplitudes, positive=(1,))
    if not math.isfinite(phase) or phase < 0:
        raise ValueError("finite nonnegative phase required")
    primary = int(np.argmin(u))
    origin = float(u[primary])
    if not phase:
        return origin
    scale = phase/a[primary]**(2/3)
    if not math.isfinite(scale) or scale <= 0:
        raise ValueError("clock scale outside floating diagnostic range")
    gaps, weights = (u-origin)/scale, a/a[primary]
    if not np.isfinite(gaps).all() or not np.isfinite(weights).all():
        raise ValueError("relative data outside floating diagnostic range")
    root = brentq(lambda z: np.dot(weights, np.maximum(z-gaps, 0)**1.5)-1,
                  0, 1.01, xtol=1e-14, rtol=1e-14)
    return origin+scale*root


def variational_value(phase, arrivals, amplitudes, probability):
    """Holder dual cost for one probability vector, not an optimizer."""
    u, a, lam = _vectors(arrivals, amplitudes, probability, positive=(1,))
    if (not math.isfinite(phase) or phase < 0 or np.any(lam < 0) or
            not math.isclose(float(lam.sum()), 1., rel_tol=1e-12, abs_tol=1e-12)):
        raise ValueError("nonnegative phase and a probability vector required")
    # Equivalent to (sum lambda^3/A^2)^(1/3), without squaring A first.
    cost = np.linalg.norm(lam/a**(2/3), ord=3)
    return float(np.dot(lam, u)+phase*cost)


def affine_inverse_data(phase, arrivals, amplitudes, slopes):
    """Aggregate covariance derivatives for CONSTANT A and AFFINE arrivals.

    An exact opening has a singular second derivative and is rejected here;
    the written distributional identity does not divide by a zero deficit.
    No eikonal/geometric claim is inferred from these input slope vectors.
    """
    u, a = _vectors(arrivals, amplitudes, positive=(1,))
    n = np.asarray(slopes, dtype=float)
    if (phase <= 0 or n.shape != (len(u), 2) or not np.isfinite(n).all()):
        raise ValueError("positive phase and finite two-component slopes required")
    clock = aggregate_inverse(phase, u, a)
    d = clock-u
    if np.any(d == 0):
        raise ValueError("second derivatives at an exact opening use one-sided limits")
    active = d > 0
    da, aa, na = d[active], a[active], n[active]
    lam = aa*np.sqrt(da)
    lam /= lam.sum()
    spatial = lam@na
    speed = float(lam@da/phase)
    residual = np.column_stack((spatial-na, speed-da/phase))
    hessian = -.5*np.einsum('i,ij,ik->jk', lam/da, residual, residual)
    probabilities = np.zeros(len(u))
    probabilities[active] = lam
    return {"clock": clock, "probability": probabilities,
            "gradient": np.r_[spatial, speed], "hessian": hessian}


def cap_union_slice(split, centers, stiffness, excess):
    """Actual maximum of finitely many quadratic model tip clocks.

    Integrates s*max_i[h_i-k_i*s/(s+2*k_i)*(theta-a_i)^2]_+ over theta.
    All intersections and positive components are kept. Returns union and
    sum; floating root isolation is a diagnostic, not a certified enclosure.
    """
    a, k, h = _vectors(centers, stiffness, excess, positive=(1, 2))
    if not math.isfinite(split) or split <= 0:
        raise ValueError("positive finite split required")
    c = k*split/(split+2*k)
    width = np.sqrt(h/c)
    edges = list(a-width)+list(a+width)
    for i in range(len(a)):
        for j in range(i):
            left = max(a[i]-width[i], a[j]-width[j])
            right = min(a[i]+width[i], a[j]+width[j])
            if left >= right:
                continue
            delta = a[i]-a[j]
            # Intersections in the coordinate theta-a_i limit cancellation.
            poly = np.polynomial.Polynomial(
                [h[i]-h[j]+c[j]*delta**2, 2*c[j]*delta, c[j]-c[i]])
            for z in poly.roots():
                if abs(z.imag) <= 1e-11*max(1., abs(z.real)):
                    x = a[i]+float(z.real)
                    if left < x < right:
                        edges.append(x)
    edges = sorted(set(edges))
    union = 0.
    for lo, hi in zip(edges, edges[1:]):
        values = h-c*((lo+hi)/2-a)**2
        winner = int(np.argmax(values))
        if values[winner] <= 0:
            continue
        x0, x1 = lo-a[winner], hi-a[winner]
        # Integrate in the winning cap's centered coordinate.
        union += h[winner]*(hi-lo)-c[winner]*(x1**3-x0**3)/3
    total = float(np.sum(4/3*split*h**1.5/np.sqrt(c)))
    return max(0., split*union), total


def tip_packing_diagnostic(centers, stiffness, excess, radii):
    """Integrate the model union deficit; verify natural packing hypotheses.

    The analytic bound is 64*sum h_i^3/r_i^3. Broad intervals are charged
    once, even when one covers many smaller tubes. No physical realization.
    """
    a, k, h, r = _vectors(centers, stiffness, excess, radii, positive=(1, 2, 3))
    order = np.argsort(a)
    if (np.any(r > 1) or np.any(h > k*r*r/4) or
            np.any(np.diff(a[order]) < (r[order][:-1]+r[order][1:])*(1-1e-13))):
        raise ValueError("disjoint radii<=1 and h<=k*r^2/4 required")
    broad = 8*h/(r*r)
    top = float(max(broad))
    # No deficit remains above top. Square-root panels resolve the vertex
    # and the independently scaled broad-tube thresholds.
    edges = sorted(set([0., 1., *np.sqrt(broad/top)]))
    bound = float(64*np.sum(h**3/r**3))

    def integrand(z):
        if z == 0:
            return 0.
        union, total = cap_union_slice(top*z*z, a, k, h)
        return max(0., total-union)*2*top*z/bound

    ratio = sum(quad(integrand, lo, hi, epsabs=2e-9, epsrel=2e-7,
                     limit=150)[0] for lo, hi in zip(edges, edges[1:]))
    return {"deficit": ratio*bound, "bound": bound, "ratio": ratio}


def opening_coefficient(primary, secondary):
    """Coefficient of the two-well primitive interaction, c3 absorbed.

    It comes from the inverse of the sum. This finite quadrature does not
    prove a uniform half-order remainder for changing geometric competitors.
    """
    if (not all(math.isfinite(x) and x > 0 for x in (primary, secondary))):
        raise ValueError("positive finite amplitudes required")
    radius = primary**(-2/3)
    ratio = secondary/primary

    def inverse(z):
        return brentq(lambda y: y**1.5+ratio*max(y-z, 0)**1.5-1,
                      0, 1, xtol=1e-13, rtol=1e-13)

    return radius**2*quad(lambda z: inverse(z)-1, 0, 1,
                         epsabs=2e-11, epsrel=2e-11)[0]
