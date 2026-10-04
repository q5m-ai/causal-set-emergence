"""Exact certificates for #74's written boundary-collar handoff.

The canonical action is unchanged. Auxiliary full/face/corner integrals cancel
exactly before limits. The signed single-face and bulk proofs are in
notes/curved-boundary-collar.md; the actual corner limit remains owned by #75.
These finite identities are not Lean proofs or geometric admissibility data.
"""

import sympy as s

from curved_bulk_pilot import ACTION_CONSTANT, INTERVAL_CONSTANT, null_phase_factor, transverse_moment


def time_interval_split(primitive, variable, height, gap):
    """Actual/full/face/corner weighted integrals, for height,gap >= 0.

    primitive is an arbitrary antiderivative in the source depth variable.
    Equal-contact intervals are empty. No unweighted hinge replaces a density.
    """
    height, gap = map(s.sympify, (height, gap))
    at = lambda value: primitive.subs(variable, value)
    contact = s.Min(height, gap)
    return (at(height)-at(contact), at(height)-at(0),
            at(gap)-at(0), at(gap)-at(contact))


def strip_phase_derivative(face_time, gap, gap_u, u, v, depth_fraction):
    """Total dw/du after a=b*d(u,v), retaining the moving source time."""
    f, d, du, u, v, b = map(s.sympify, (face_time, gap, gap_u, u, v, depth_fraction))
    t = f-b*d
    h = null_phase_factor(t, u, v)
    hu, ht = t/2+3*u/20+7*v/60, 2*t+(u+v)/2
    return v*(2*h+u*(hu-b*du*ht))/(2*s.sqrt(h))


def moving_lower_second(interior, value, derivative_w, derivative_v, lower_w, lower_ww):
    """Second w derivative of a moving-lower-endpoint integral; (H11)."""
    interior, value, ew, ev, nw, nww = map(s.sympify, (
        interior, value, derivative_w, derivative_v, lower_w, lower_ww))
    return interior-2*ew*nw-ev*nw*nw-value*nww


def face_jet_coefficients(q, q1, gradient_squared, laplacian_f,
                          chi=1, chi_t=0, phi=1, phi_t=0, gradient_dot_phi=0):
    """Coefficients of T*K, T^2*K, r^2*K, r^2*Z*K' in (H13).

    Both density factors and the complete first phase correction are included.
    This is after time integration and sphere AVERAGE, before the cone Jacobian.
    """
    q, q1, p, lf, chi, ct, phi, pt, m = map(s.sympify, (
        q, q1, gradient_squared, laplacian_f, chi, chi_t, phi, phi_t, gradient_dot_phi))
    return (q*q*chi*phi,
            q*q*(chi*pt-ct*phi)/2,
            -q*q*(chi*phi*lf/6+p*(ct*phi+chi*pt)/6+chi*m/3)-q*q1*chi*phi*p/3,
            -q*q1*chi*phi*p/6)


def face_basis_responses(q):
    """Original +C*rho^(3/2) responses, derived from signed log moments.

    The finite-density T*K response is not zero; its limit is zero. These
    formulas are model coefficients, justified for the actual face by (H12).
    """
    q = s.sympify(q)
    j = s.Symbol("j", real=True)
    log_moment = s.diff(transverse_moment(j), j).subs(j, 2)
    t2 = s.simplify(ACTION_CONSTANT*2*s.pi*(INTERVAL_CONSTANT*q)**(-s.Rational(3, 2))
                    * log_moment/16)
    r2 = -3*t2
    return s.Integer(0), t2, r2, -s.Rational(3, 2)*r2


def face_response(q, q1, gradient_squared, laplacian_f,
                  chi=1, chi_t=0, phi=1, phi_t=0, gradient_dot_phi=0):
    """Derived single-face density with respect to source spatial dz."""
    coefficients = face_jet_coefficients(q, q1, gradient_squared, laplacian_f,
                                         chi, chi_t, phi, phi_t, gradient_dot_phi)
    return s.simplify(sum(a*b for a, b in zip(coefficients, face_basis_responses(q))))


def future_flux_density(q, chi, chi_t, gradient_dot_chi, phi, phi_t, gradient_dot_phi):
    """The N density in (H15), not including the retained joint flux T."""
    q, chi, ct, dc, phi, pt, dp = map(s.sympify, (
        q, chi, chi_t, gradient_dot_chi, phi, phi_t, gradient_dot_phi))
    return s.sqrt(q)*(phi*(ct+dc)-chi*(pt+dp))


def check_boundary_collar_identities():
    """Finite algebra checks only; #75's general corner limit is not asserted."""
    a, h, d = s.symbols("a h d", real=True)
    primitive = s.Function("W")(a)
    actual, full, face, corner = time_interval_split(primitive, a, h, d)
    assert s.expand(actual-full+face-corner) == 0
    print("PASS: exact weighted actual/full/face/corner interval restoration")

    u, v = s.symbols("u v", positive=True)
    f, b, p1, p2, p3 = s.symbols("f b p1 p2 p3", real=True)
    T, r = (u+v)/2, (v-u)/2
    gap = T-p1*r-p2*r*r/2-p3*r**3/6
    t = f-b*gap
    phase = u*v*s.sqrt(null_phase_factor(t, u, v))
    assert s.simplify(s.diff(phase, u)-strip_phase_derivative(f, gap, s.diff(gap, u), u, v, b)) == 0
    diagonal = null_phase_factor(f-b*v, v, v)
    assert s.expand(diagonal-(1+(f+(s.Rational(1, 2)-b)*v)**2+v*v/60)) == 0
    print("PASS: source-time derivative in the strip phase Jacobian and diagonal law")

    q = s.Symbol("q", positive=True)
    q1, chi, ct, phi, pt, dotphi, dotchi, p, lf = s.symbols(
        "q1 chi ct phi pt dotphi dotchi p lf", real=True)
    # Before angular averaging, n = Df[n], hh = D2f[n,n], and pn = Dphi[n].
    n, hh, pn, TT, rr, z, k, kp = s.symbols("n hh pn T r z K Kp", real=True)
    d1, d2 = TT-rr*n, -rr*rr*hh/2
    unaveraged = (q*q*chi*phi*(d1+d2)*k
        + q*q1*chi*phi*(TT*d1-d1*d1)*k
        + q*q*(-ct*phi*d1*d1/2+chi*pt*(TT*d1-d1*d1/2)+chi*rr*pn*d1)*k
        + q*q1*chi*phi*z*(TT*d1-d1*d1)*kp/2)
    polynomial = s.Poly(s.expand(unaveraged), n, hh, pn)
    averages = {(0, 0, 0): 1, (1, 0, 0): 0, (0, 0, 1): 0,
                (2, 0, 0): p/3, (0, 1, 0): lf/3, (1, 0, 1): dotphi/3}
    averaged = sum(coefficient*averages[powers] for powers, coefficient in polynomial.terms())
    a1, a2, a3, a4 = face_jet_coefficients(q, q1, p, lf, chi, ct, phi, pt, dotphi)
    assert s.expand(averaged-(a1*TT*k+a2*TT*TT*k+a3*rr*rr*k+a4*rr*rr*z*kp)) == 0
    assert face_basis_responses(q) == (0, -2/q**s.Rational(3, 2),
                                      6/q**s.Rational(3, 2), -9/q**s.Rational(3, 2))
    print("PASS: entire face jet and signed basis responses with original normalization")

    response = face_response(q, q1, p, lf, chi, ct, phi, pt, dotphi)
    flux = future_flux_density(q, chi, ct, dotchi, phi, pt, dotphi)
    # div_z(sqrt(q(f))*chi(f,z)*phi(f,z)*Df), including trace derivatives.
    divergence = (chi*phi*(s.sqrt(q)*lf+q1*p/(2*s.sqrt(q)))
                  + s.sqrt(q)*(phi*(dotchi+ct*p)+chi*(dotphi+pt*p)))
    assert s.simplify(response-flux+divergence) == 0
    print("PASS: source/field partition derivatives and retained single-face joint flux")


if __name__ == "__main__":
    check_boundary_collar_identities()
