"""Finite checks for the critical 3D continuation.

The accompanying note constructs actual smooth support-lens metrics in writing.
These scalar routines check their identities, not a complete spacetime action,
Cantor-measure theorem, or arbitrary-smooth remainder bound.
"""

import math

import numpy as np
from scipy.integrate import quad

from curved_three_d_union import aggregate_inverse


def _finite(*values):
    if not all(math.isfinite(v) for v in values):
        raise ValueError("finite scalar data required")


def smooth_switch_jet(x):
    """Value and first two derivatives of a flat smooth step (float check)."""
    _finite(x)
    if x <= 0:
        return 0., 0., 0.
    if x >= 1:
        return 1., 0., 0.
    left, right = -1/x, -1/(1-x)
    value = float(np.exp(left-np.logaddexp(left, right)))
    if value == 0 or value == 1:  # underflow, not a proof of exact flatness
        return value, 0., 0.
    first = x**-2+(1-x)**-2
    second = -2*x**-3+2*(1-x)**-3
    return (value, value*(1-value)*first,
            value*(1-value)*((1-2*value)*first*first+second))


def cap_metric_jet(radial, cap_radius, boundary_radius):
    """j,j_r,j_rr on ONE polar ray of the written glued metric.

    boundary_radius is R+F+F'' at that angle. Global smoothness/positivity
    in angle is a written hypothesis, not inferred from this scalar check.
    """
    _finite(radial, cap_radius, boundary_radius)
    if cap_radius <= 0 or boundary_radius <= 0 or not 0 <= radial <= cap_radius:
        raise ValueError("positive radii and a radial point in the cap required")
    value, first, second = smooth_switch_jet(3*radial/cap_radius-1)
    first *= 3/cap_radius
    second *= (3/cap_radius)**2
    difference = cap_radius+boundary_radius-2*radial
    return (radial+value*difference,
            1+first*difference-2*value,
            second*difference-4*first)


def support_boundary(angle, value, first, second, radius):
    """Boundary, tangent, and positive curvature radius for a support jet."""
    _finite(angle, value, first, second, radius)
    curvature_radius = radius+value+second
    if radius <= 0 or curvature_radius <= 0:
        raise ValueError("positive R and R+F+F'' required")
    n = np.array([math.cos(angle), math.sin(angle)])
    tangent = np.array([-n[1], n[0]])
    return (-(radius+value)*n-first*tangent,
            -curvature_radius*tangent, curvature_radius)


def proper_stiffness(end_jacobi, middle, cap_radius, boundary_radius):
    """Actual fixed-middle Jacobi stiffness on the rotational primary arc.

    end_jacobi is the full spatial Jacobi value, not an endpoint inverse.
    Zero is allowed to check the conjugate limit with a fixed proper margin.
    """
    _finite(end_jacobi, middle, cap_radius, boundary_radius)
    if (not 0 < middle < cap_radius or boundary_radius <= 0 or
            not 0 <= end_jacobi < boundary_radius):
        raise ValueError("fixed interior middle and 0<=end_jacobi<boundary radius required")
    integral = quad(lambda r: cap_metric_jet(r, cap_radius, boundary_radius)[0]**-2,
                    middle, cap_radius, points=[cap_radius/3, 2*cap_radius/3],
                    epsabs=1e-10, epsrel=1e-10)[0]
    factor = 1+end_jacobi*(integral-1/boundary_radius)
    return end_jacobi/(2*factor)


def cut_support_jet(theta, radius, speed):
    """F,F',F'' and the two stiffnesses for a'=-speed, r'=r*cot(theta/2)*a'."""
    _finite(theta, radius, speed)
    if not 0 < theta < math.pi or radius <= 0 or speed < 0:
        raise ValueError("separated angle, positive radius and nonnegative speed required")
    return {"value": -radius*(1-math.cos(theta)),
            "first": -radius*math.sin(theta),
            "second": -radius*math.cos(theta)+radius*speed,
            "primary": radius/2, "secondary": radius*speed/2,
            "singular_weight": radius/(4*math.sin(theta/2)**2)}


def two_state_head_and_budget(stiff, soft, soft_P, chord):
    """Candidate head and reciprocal-cut CRITICAL BUDGET, not a remainder.

    The written coalescing-minimum argument proves integrability of this
    budget. It does not bound a multi-state/masked numerator by the budget.
    """
    _finite(stiff, soft, soft_P, chord)
    if not 0 < soft <= stiff or soft_P <= 0 or not 0 < chord <= 2:
        raise ValueError("ordered positive stiffnesses, positive P and chord<=2 required")
    head = chord*soft**1.5/(math.sqrt(soft_P)*stiff**(1/3))
    budget = stiff**(5/6)*soft**.25*soft_P**.25/chord**2.5
    return head, budget


def ramp_kernel_moment(power):
    """Integral z^power * (K3(z^(3/2)))'' for power>1, via Mellin."""
    _finite(power)
    if power <= 1:
        raise ValueError("power>1 required for this integration-by-parts formula")
    s = 2*(power-1)/3
    return 2/3*power*(power-1)*math.gamma(s)*(1-3*s/2)*(1-3*s/4)


def two_state_proxy(phase, arrivals, amplitudes):
    """Best primary-plus-one inverse; NOT the physical aggregate observable.

    Used only to expose the error of dropping a third active state. This
    never sums individual inverses or applies separate physical kernels.
    """
    u, a = np.asarray(arrivals, dtype=float), np.asarray(amplitudes, dtype=float)
    # Validate the complete data with the actual aggregate diagnostic first.
    aggregate_inverse(phase, u, a)
    primary = int(np.argmin(u))
    if len(u) == 1:
        return aggregate_inverse(phase, u, a)
    return min(aggregate_inverse(phase, u[[primary, j]], a[[primary, j]])
               for j in range(len(u)) if j != primary)
