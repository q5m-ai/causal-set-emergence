"""Finite certificates for the written controlled curved assembly (#76).

These are algebra/geometry checks, not a new production action or a numerical
proof of a limit. The observable and Poisson law remain ConformalAction.lean;
notes/curved-assembly.md assembles the separately proved analytic producers.
"""

import sympy as s

from curved_bulk_pilot import KERNEL, Z, scalar_curvature


def ordered_layer_kernel(z):
    """Poisson layer probabilities with the original signed pair coefficients.

    Two-point Mecke supplies rho**2 outside this expression. Counts are ordered
    and exclude the two selected endpoints; k! is essential in each layer.
    """
    z = s.sympify(z)
    return sum(weight*z**k/s.factorial(k) for k, weight in
               enumerate((1, -9, 16, -8))) * s.exp(-z)


def bulk_time_primitive(t):
    """Primitive of R*q/2 for q=1+t**2, in the C4 curvature convention.

    Geometry only: this is not an action-derived definition of scalar curvature.
    """
    t = s.sympify(t)
    return 9*t/(4*s.sqrt(1+t*t)) - 3*s.asinh(t)/4


def check_curved_assembly_identities():
    """Exact signs, density powers and geometric calibration, not asymptotics."""
    rho = s.Symbol("rho", positive=True)
    volume, full, face, corner, long_pair = s.symbols("volume full face corner long_pair")
    bulk, normal, flux, joint = s.symbols("bulk normal flux joint")
    point_scale, pair_scale = 4*s.sqrt(rho)/s.sqrt(6), 4*rho**s.Rational(3, 2)/s.sqrt(6)
    # H3 is a finite-density identity, including auxiliary partners. H5, H14,
    # J19 and A14 separately prove that these four residuals tend to zero.
    actual = point_scale*volume-pair_scale*(full-face+corner+long_pair)
    residuals = (point_scale*volume-pair_scale*full-bulk,
                 pair_scale*face-normal+flux,
                 -pair_scale*corner-flux-joint,
                 -pair_scale*long_pair)
    assert s.expand(actual-bulk-normal-joint-sum(residuals)) == 0
    # Neither the face flux nor the finite-density long term can be dropped.
    assert s.expand(sum(residuals[:2])+(-pair_scale*corner-joint)
                    +residuals[3]-(actual-bulk-normal-joint)) == flux
    print("PASS: full/face/corner/long residual assembly retains the joint flux and one point term")

    assert s.expand(ordered_layer_kernel(Z)-KERNEL) == 0
    layers = s.symbols("L0:4")  # Pair integrals of the four Poisson probabilities.
    pair = sum(w*layer for w, layer in zip((1, -9, 16, -8), layers))
    expectation = 4/(s.sqrt(6)*s.sqrt(rho))*(rho*volume-rho**2*pair)
    assert s.expand(expectation-point_scale*(volume-rho*pair)) == 0
    print("PASS: exclusive ordered Poisson layers, factorials and both density factors")

    t = s.Symbol("t", real=True)
    assert s.simplify(s.diff(bulk_time_primitive(t), t)
                      -(1+t*t)*scalar_curvature(t)/2) == 0
    # The region has time extent [-1/8,1/8], not constant scalar curvature.
    assert scalar_curvature(0) == 3
    assert (scalar_curvature(0)-scalar_curvature(s.Rational(1, 16))).is_positive
    print("PASS: independent bulk primitive and nonconstant positive-curvature witness")


if __name__ == "__main__":
    check_curved_assembly_identities()
