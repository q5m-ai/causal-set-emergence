"""Exact required curved-null continuation diagnostics; NO curved limit theorem.

The canonical conformal factor is Omega(t)^4=1+t² on the round mixed cap
-1<t<-|x|. Polynomial interval volume is imported in meaning from C9, with
both endpoint densities retained. See notes/null-mixed-required-coverage.md.
"""

import math

import numpy as np
from scipy.special import roots_jacobi

from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT
from two_tip_lens import rule


def source_gaussian_mismatch(depth, b=1.0):
    """rho² coefficient of 1-rho*int K - exp(-rho*V(p,tip)).

    This is a finite-density identity obstruction, NOT a limit counterexample.
    b=0 is the flat calibration; the selected curved continuation has b=1.
    """
    if not all(math.isfinite(v) for v in (depth, b)) or not 0 < depth < 1 or b < 0:
        raise ValueError("require 0<depth<1 and b>=0, finite")
    return math.pi**2*depth**10*b*(2400-439*depth*depth*b)/58060800


def point_volume(b=1.0):
    return 4*math.pi/3*(1/4+b/6)


def independent_target():
    """R/2 integral plus induced curved SN area, fixed b=1, not fitted."""
    return math.pi*(53*math.sqrt(2)/6-20/3)


def pair_integral(rho, b=1.0, order=40, min_gap=0.0):
    """Complete ordered partner integral, or its explicitly retained gap complement.

    q=(-v,y), p=(-u,x), gap=u-v. For |x-y|<=gap, the radius-v
    target ball lies in the radius-u source ball. Integrating the physical
    target position ONCE gives 4*pi*v³/3, not separate overlapping balls.
    """
    if (not all(math.isfinite(x) for x in (rho, b, min_gap))
            or rho <= 0 or b < 0 or not 0 <= min_gap < 1):
        raise ValueError("require rho>0, b>=0 and 0<=min_gap<1, finite")
    nodes, weights = rule(order)
    radial_nodes, radial_weights = roots_jacobi(order, 0.5, 0)
    radial_nodes = (radial_nodes+1)/2
    radial_weights = radial_weights/2**1.5
    total = 0.0
    for gap, wg in zip(min_gap+(1-min_gap)*nodes, (1-min_gap)*weights):
        v = ((1-gap)*nodes)[:, None]
        sigma = (gap*gap*radial_nodes)[None, :]
        u = v+gap
        h = 1+b*(v*v+v*gap+0.3*gap*gap-sigma/30)
        phase = INTERVAL_CONSTANT*rho*sigma*sigma*h
        kernel = (1-9*phase+8*phase*phase-4*phase**3/3)*np.exp(-phase)
        measure = (wg*(1-gap)*gap**3*weights[:, None]*radial_weights[None, :]
                   * v**3*(1+b*u*u)*(1+b*v*v))
        total += np.sum(measure*kernel)
    return float(8*math.pi**2/3*total)


def full_action(rho, b=1.0, order=40):
    """Canonical complete action evaluated numerically, not a proved limit."""
    pair = pair_integral(rho, b, order)
    return ACTION_CONSTANT*math.sqrt(rho)*(point_volume(b)-rho*pair)
