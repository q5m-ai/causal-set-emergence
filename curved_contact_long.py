"""Exact diagnostics for #117's contact-averaged curved long theorem.

The production observable remains BoundaryDraft.conformalAction. These are
algebraic certificates, not a Lean proof, an admissibility predicate, or a
replacement action. See notes/curved-contact-long.md for the conventional
proof, fixed-cutoff quantifiers and remaining short/bulk/joint obligations.
"""

import sympy as s

from curved_bulk_pilot import null_phase_factor, volume_density


def phase(t, u, v):
    """Exact w with V=(pi/24)*w^2, for the fixed density q(t)=1+t^2."""
    t, u, v = map(s.sympify, (t, u, v))
    return u*v*s.sqrt(null_phase_factor(t, u, v))


def phase_derivative(t, u, v):
    """dw/du, strictly positive for v>0 and u>=0 by (A3)."""
    t, u, v = map(s.sympify, (t, u, v))
    h = null_phase_factor(t, u, v)
    hu = t/2 + 3*u/20 + 7*v/60
    return v*(2*h+u*hu)/(2*s.sqrt(h))


def pair_amplitude(t, u, v, weight=1):
    """BOTH endpoint densities, polar and inverse-phase Jacobians.

    Substitute u=U(t,v,w). The optional weight represents chi(x)*phi(y).
    This excludes all region indicators and the t,v,z,n integrations.
    """
    t, u, v, weight = map(s.sympify, (t, u, v, weight))
    return (weight * volume_density(t) * volume_density(t+(u+v)/2)
            * (v-u)**2 / (8*phase_derivative(t, u, v)))


def time_boundary_derivatives(t, v, slope, hessian):
    """tau'(0), tau''(0) at t=tau_0(v); (A10), not coefficients.

    slope=Df[n], hessian=D^2f[n,n] at z+v*n/2. Includes the mixed
    inverse-phase derivative caused by the moving first-endpoint time.
    """
    t, v, slope, hessian = map(s.sympify, (t, v, slope, hessian))
    h = null_phase_factor(t, 0, v)
    ht, hu = 2*t+v/2, t/2+7*v/60
    b = (1+slope)/2
    return (-b/(v*s.sqrt(h)),
            hessian/(4*v**2*h) + (b*hu-b**2*ht)/(v**2*h**2))


def time_integral_jet(interior0, interior1, interior2,
                      edge0, edge_w, edge_t, tau1, tau2):
    """Taylor coefficients of integral_ell^tau(w) a(t,w) dt.

    interiorj is the integral of partial_w^j a at zero; tauj is a derivative.
    The formula is for the oriented smooth extension, before clipping at ell.
    """
    i0, i1, i2, a0, aw, at, t1, t2 = map(s.sympify, (
        interior0, interior1, interior2, edge0, edge_w, edge_t, tau1, tau2))
    return i0, i1+a0*t1, (i2+2*aw*t1+at*t1**2+a0*t2)/2


def outer_contact_coefficient(amplitude, tau1, exit_speed):
    """The v-contact term a(ell,R,0)*tau1^2/(2*d), at an ACTIVE cutoff.

    exit_speed=d=(1-Df[n])/2>0. Exact/nonpositive cutoff contacts instead
    have zero right coefficients; do not apply this active formula there.
    """
    amplitude, tau1, exit_speed = map(s.sympify, (amplitude, tau1, exit_speed))
    return amplitude*tau1**2/(2*exit_speed)


def check_contact_long_identities():
    """Exact finite identities only; no general limit is inferred by code."""
    t, u, v = s.symbols("t u v", real=True)
    h = null_phase_factor(t, u, v)
    assert s.expand(h - (1+(t+(u+v)/4)**2
                         +(3*u**2-2*u*v+3*v**2)/240)) == 0
    assert s.expand(2*h+u*s.diff(h, u) - (2+2*(t+3*u/8+v/4)**2
                                        +(3*u**2-4*u*v+4*v**2)/160)) == 0
    fu = phase_derivative(t, u, v)
    assert s.simplify(s.diff(phase(t, u, v), u)-fu) == 0
    assert s.simplify(pair_amplitude(t, u, v)*fu
                      - (1+t*t)*(1+(t+(u+v)/2)**2)*(v-u)**2/8) == 0
    print("PASS: contact-averaged transport retains the exact phase and both measures")

    # Implicit differentiation is independent of the closed formula (A10).
    slope, hessian = s.symbols("slope hessian", real=True)
    b = (1+slope)/2
    inverse1 = 1/fu.subs(u, 0)
    inverse2 = -s.diff(fu, u).subs(u, 0)*inverse1**3
    inverse_tw = s.diff(inverse1, t)
    tau1 = -b*inverse1
    tau2 = hessian*inverse1**2/4-b*inverse2-2*b*inverse_tw*tau1
    expected = time_boundary_derivatives(t, v, slope, hessian)
    # Use v>0 for the square-root simplifier without introducing abs(v).
    vp = s.Symbol("vp", positive=True)
    for actual, target in zip((tau1, tau2), expected):
        assert s.simplify((actual-target).subs(v, vp)) == 0
    print("PASS: moving-time acceleration includes the mixed inverse-phase derivative")

    w = s.Symbol("w", real=True)
    ell = s.Rational(-1, 3)
    boundary = 2-3*w+5*w*w/2
    amplitude = 1+2*t+3*t*t+w*(4+5*t)+6*w*w
    integral = s.integrate(amplitude, (t, ell, boundary))
    parts = [s.diff(amplitude, w, j).subs(w, 0) for j in range(3)]
    interior = [s.integrate(p, (t, ell, 2)) for p in parts]
    coefficients = time_integral_jet(*interior, parts[0].subs(t, 2),
                                     parts[1].subs(t, 2),
                                     s.diff(parts[0], t).subs(t, 2), -3, 5)
    for j, coefficient in enumerate(coefficients):
        assert s.expand(coefficient-s.diff(integral, w, j).subs(w, 0)/s.factorial(j)) == 0

    a, d, b = s.symbols("a d b", positive=True)
    # Actual local lost-layer calculation: oriented negative triangle restored.
    layer = s.integrate(-a*(d*t-b*w), (t, 0, b*w/d))
    assert s.simplify(layer/w**2-outer_contact_coefficient(a, -b, d)) == 0
    print("PASS: both moving-boundary jets and the retained quadratic contact triangle")


if __name__ == "__main__":
    check_contact_long_identities()
