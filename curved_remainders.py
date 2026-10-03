"""Exact diagnostics for #74's sharp-cutoff obstruction, not a bulk theorem.

The canonical observable remains BoundaryDraft.conformalAction.  This module
only represents its polynomial-density phase and the complete long fibre of
the planar-future pilot.  Conventional proofs and OPEN successor contracts are
in notes/curved-remainders.md.  No Poisson law or limit is defined here.
"""

import sympy as s

from curved_bulk_pilot import null_phase_factor, volume_density


def phase(t, u, v):
    """w = u*v*sqrt(H), with the pilot density fixed to 1+t^2."""
    t, u, v = map(s.sympify, (t, u, v))
    return u * v * s.sqrt(null_phase_factor(t, u, v))


def phase_jacobian(t, u, v):
    """dw/du > 0 for v > 0, u >= 0; see the sum-of-squares proof."""
    t, u, v = map(s.sympify, (t, u, v))
    h = null_phase_factor(t, u, v)
    hu = t / 2 + 3 * u / 20 + 7 * v / 60
    return v * (2 * h + u * hu) / (2 * s.sqrt(h))


def endpoint_amplitude(t, u, v):
    """Inner endpoint density times polar/null and inverse-phase Jacobians.

    This excludes the sphere integral, region indicator and first-endpoint
    measure q(t) dx, all of which must still be supplied in the exact identity.
    Evaluate at u=U(t,v,w); preconditions: v>0 and 0<=u<=v.
    """
    t, u, v = map(s.sympify, (t, u, v))
    return volume_density(t + (u + v) / 2) * (v - u)**2 / (8 * phase_jacobian(t, u, v))


def moving_integral_jet(interior0, interior1, interior2,
                        edge0, edge_w, edge_v, root1, root2):
    """Coefficients of integral_delta^R(w) A(w,v) dv at an ACTIVE root.

    interiorj denotes the integral of partial_w^j A at w=0; rootj is
    R^(j)(0), not its Taylor coefficient.  This is not the exact-contact
    formula: closed/negative fibres instead have three zero coefficients.
    """
    values = map(s.sympify, (interior0, interior1, interior2,
                           edge0, edge_w, edge_v, root1, root2))
    i0, i1, i2, a0, aw, av, r1, r2 = values
    return i0, i1 + a0 * r1, (i2 + 2 * aw * r1 + av * r1**2 + a0 * r2) / 2


def planar_long_coordinate_volume(a, delta):
    """Complete long-future Lebesgue mass when 0<a<delta, L=delta+a.

    Integrates all directions and 0<=u, delta<=v, u+v<L.  There is no
    spatial truncation: the lower causal epigraph retains every such partner.
    The phase, endpoint measures and kernel are NOT included in this volume.
    """
    a, delta = map(s.sympify, (a, delta))
    return s.pi * a**2 * (a**2 + 6 * delta**2) / 24


def obstruction_density(a, delta):
    """A density probe, not density-dependent geometry: eps=1/100, Q=2.

    In the fixed pilot, every long partner at t=f-(delta+a)/2 then has
    0<=rho*V<=1/100.  Preconditions: 0<a<=delta/2, delta=1/32, f=1/8.
    """
    a, delta = map(s.sympify, (a, delta))
    return s.Rational(1, 100) / (2 * (s.pi / 24) * a**2 * (delta + a)**2)


def planar_contact_scale(top, delta):
    """k_* and A_* in B_t(w)=A_*(a-w/k_*)_+ + O(a^2).

    Includes all 4*pi directions and the second-endpoint density, but not
    the outer q(t) measure.  The error assertion is a written local argument,
    not a claim that this leading hinge equals the actual amplitude.
    """
    top, delta = map(s.sympify, (top, delta))
    contact_time = top - delta / 2
    h = null_phase_factor(contact_time, 0, delta)
    return delta * s.sqrt(h), s.pi * delta * volume_density(top) / (2 * s.sqrt(h))


def check_curved_remainder_identities():
    """Algebraic certificates only; not a machine-checked analytic proof."""
    t, u, v = s.symbols("t u v", real=True)
    h = null_phase_factor(t, u, v)
    h_squares = 1 + (t + (u + v) / 4)**2 + (3*u**2 - 2*u*v + 3*v**2) / 240
    d_squares = 2 + 2*(t + 3*u/8 + v/4)**2 + (3*u**2 - 4*u*v + 4*v**2) / 160
    assert s.expand(h - h_squares) == 0
    assert s.expand(2*h + u*s.diff(h, u) - d_squares) == 0
    assert s.simplify(s.diff(phase(t, u, v), u) - phase_jacobian(t, u, v)) == 0
    assert s.simplify(endpoint_amplitude(t, u, v) * phase_jacobian(t, u, v)
                      - volume_density(t + (u + v)/2) * (v-u)**2/8) == 0
    print("PASS: exact curved phase, positive-Jacobian certificates and both measure factors")

    a, delta = s.symbols("a delta", positive=True)
    raw_mass = 4*s.pi*s.integrate(s.integrate((v-u)**2/8, (u, 0, delta+a-v)),
                                 (v, delta, delta+a))
    assert s.simplify(raw_mass - planar_long_coordinate_volume(a, delta)) == 0
    z = s.Rational(1, 100)
    assert (1 - 9*z - s.Rational(4, 3)*z**3)*(1-z) > s.Rational(1, 2)
    assert s.simplify(obstruction_density(a, delta) * (s.pi/24)
                      * 2*a**2*(delta+a)**2) == z
    print("PASS: complete long triangle, small signed-kernel band and density probe")


if __name__ == "__main__":
    check_curved_remainder_identities()
