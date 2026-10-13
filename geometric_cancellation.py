"""Finite diagnostics for geometric-long-cancellation.md, not theorem oracles."""

import numpy as np

from curved4_corrected_convergence import diamond_rule


def conformal_diamond_factor(source, radius, direction, q, density, order=12):
    """Actual V/q**2 for an entire faithful Minkowski diamond, q=0 included.

    density(t, xyz) is the physical Omega**4 density. Region containment is a
    geometric obligation of the caller; this function does not infer it.
    """
    source, direction = np.asarray(source, float), np.asarray(direction, float)
    if (source.shape != (4,) or direction.shape != (3,)
            or not np.all(np.isfinite(source)) or not np.all(np.isfinite(direction))
            or not np.isfinite(radius) or not np.isfinite(q) or radius <= 0 or q < 0
            or not np.isclose(direction@direction, 1, atol=1e-12, rtol=0)):
        raise ValueError("requires finite source, radius>0, q>=0 and unit direction")
    helper = np.eye(3)[np.argmin(np.abs(direction))]
    e2 = np.cross(direction, helper)
    e2 /= np.linalg.norm(e2)
    e3 = np.cross(direction, e2)
    a, b1, b2, b3, weights = diamond_rule(order)
    tau = np.sqrt(radius*radius+q)
    t = source[0]+tau*(0.5+a)+radius*b1
    xyz = (source[1:]+(radius*(0.5+a)+tau*b1)[:, None]*direction
           + np.sqrt(q)*(b2[:, None]*e2+b3[:, None]*e3))
    value = np.asarray(density(t, xyz), float)
    if np.any(~np.isfinite(value)) or np.any(value <= 0):
        raise ValueError("density must be finite and strictly positive")
    return float(np.sum(weights*value))


def capsule_joint_data(point, s, epsilon, b):
    """Independent future normals, angle and induced area for GC7's joint.

    The returned area density is relative to the ordinary unit sphere. It is
    NOT supplied by an action coefficient. Positive b is the stated example.
    """
    point = np.asarray(point, float)
    if (point.shape[-1:] != (3,) or np.any(~np.isfinite(point))
            or not np.allclose(np.sum(point*point, axis=-1), 1, atol=1e-12, rtol=0)
            or not 0 < s < 1 or not 0 <= epsilon < 1-s or not np.isfinite(b) or b <= 0):
        raise ValueError("requires unit points and GC7 parameters")
    fgrad = np.array([epsilon, 0., 0.])
    lower, upper = fgrad+s*point, fgrad-s*point
    denom = np.sqrt((1-np.sum(lower*lower, axis=-1))
                    *(1-np.sum(upper*upper, axis=-1)))
    normal_inner = (1-np.sum(lower*upper, axis=-1))/denom
    angle_weight = normal_inner/np.sqrt(normal_inner*normal_inner-1)
    induced_area = (1+b)**2*np.sqrt(1-epsilon**2+(epsilon*point[..., 0])**2)
    return normal_inner, angle_weight, induced_area


def optical_tip_dominator(order, lower):
    """Integral of the pessimistic interior derivative bound s**(1-order).

    This is a bound-route diagnostic, NOT a computed physical coefficient.
    The flat exact diamond already shows its logarithm need not survive.
    """
    if not isinstance(order, int) or order < 0 or not 0 < lower < 1:
        raise ValueError("requires nonnegative integer order and 0<lower<1")
    if order == 2:
        return float(-np.log(lower))
    return float((1-lower**(2-order))/(2-order))
