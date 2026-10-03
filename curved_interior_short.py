"""Exact certificates for the written #74 interior short/bulk proof.

These are finite identities, not a production action, a geometric admissibility
predicate, a numerical proof of a limit, or a Lean theorem. The actual signed
remainder and its outer-integral justification are in
notes/curved-interior-short.md. The long theorem is consumed from #117/#121.
"""

import sympy as s

from curved_bulk_pilot import KERNEL, Z, null_phase_factor


def interpolated_phase_factor(t, u, v, lam):
    """H_lambda = H(t, lambda*u, lambda*v); not endpoint-frozen at lambda=1."""
    t, u, v, lam = map(s.sympify, (t, u, v, lam))
    return null_phase_factor(t, lam*u, lam*v)


def angular_density_jet(q, q1, q2, duration, sigma, kernel_argument,
                        phi, phi_t, phi_tt, laplacian, k0, k1, k2):
    """Coefficients 0,1,2 of <q_y phi_y K(c*rho*(uv)^2 H_lambda)>.

    Brackets are sphere AVERAGE. Include the polar Jacobian, 4*pi and the
    first-endpoint measure separately. sigma=T^2-r^2; k_j is K^(j)(z).
    Returns the entire (C11) polynomial, not only its surviving log terms.
    """
    q, q1, q2, T, sigma, z, phi, pt, ptt, lap, k0, k1, k2 = map(
        s.sympify, (q, q1, q2, duration, sigma, kernel_argument,
                   phi, phi_t, phi_tt, laplacian, k0, k1, k2))
    g0 = q*phi
    g1 = T*(q*pt + q1*phi)
    g2 = q*(T*T*ptt/2 + (T*T-sigma)*lap/6) + q1*T*T*pt + q2*T*T*phi/2
    h1 = z*q1*T/(2*q)
    h2 = z*q2*(3*T*T/s.Integer(20)-sigma/60)/q
    return g0*k0, g1*k0+g0*h1*k1, g2*k0+(g1*h1+g0*h2)*k1+g0*h1*h1*k2/2


def third_lower_boundary_derivative(interior, f, f_lam, f_v,
                                    f_lamlam, f_lamv, f_vv, r1, r2, r3):
    """Third lambda derivative of integral_{r(lambda)}^delta f(lambda,v) dv.

    interior is the integral of partial_lambda^3 f. All remaining f values
    are evaluated at the moving lower endpoint; r_j is a DERIVATIVE, not a
    Taylor coefficient. None of these six contact terms is generally zero.
    """
    interior, f, fl, fv, fll, flv, fvv, r1, r2, r3 = map(s.sympify, (
        interior, f, f_lam, f_v, f_lamlam, f_lamv, f_vv, r1, r2, r3))
    return interior - (3*fll*r1 + 3*flv*r1**2 + fvv*r1**3
                       + 3*fl*r2 + 3*fv*r1*r2 + f*r3)


def check_interior_short_identities():
    """Finite algebraic checks; uniformity and signed limits require the note."""
    t, u, v, lam, e, r = s.symbols("t u v lam e r", real=True)
    h = interpolated_phase_factor(t, u, v, lam)
    hd = h.subs(u, v)
    assert s.expand(4*hd+v*s.diff(hd, v)
                      - (4+4*(t+5*lam*v/8)**2+3*lam**2*v**2/80)) == 0
    scaled_h = null_phase_factor(t, e*r, e)
    assert s.expand(h.subs(u, v*r)-scaled_h.subs(e, lam*v)) == 0
    # F_u/v equals the r derivative of F/v^2; hence the amplitude is v*Psi.
    fu_over_v = (2*h+u*s.diff(h, u))/(2*s.sqrt(h))
    scaled_derivative = s.diff(r*s.sqrt(scaled_h), r)
    assert s.simplify(fu_over_v.subs(u, v*r)
                      - scaled_derivative.subs(e, lam*v)) == 0
    print("PASS: exact interpolation, monotone diagonal and scaled phase Jacobian")

    q = s.Symbol("q", positive=True)
    q1, q2, T, sigma, phi, pt, ptt, lap = s.symbols(
        "q1 q2 T sigma phi pt ptt lap", real=True)
    endpoint = (q+lam*q1*T+lam**2*q2*T*T/2) * (
        phi+lam*T*pt+lam**2*(T*T*ptt/2+(T*T-sigma)*lap/6))
    phase_factor = q+lam*q1*T/2+lam**2*q2*(3*T*T/s.Integer(20)-sigma/60)
    actual = endpoint*KERNEL.subs(Z, Z*phase_factor/q)
    coefficients = angular_density_jet(q, q1, q2, T, sigma, Z,
                                      phi, pt, ptt, lap,
                                      KERNEL, s.diff(KERNEL, Z), s.diff(KERNEL, Z, 2))
    for j, coefficient in enumerate(coefficients):
        assert s.simplify(s.diff(actual, lam, j).subs(lam, 0)/s.factorial(j)
                          - coefficient) == 0
    print("PASS: full angular second jet retains field, measure, K' and K'' terms")

    boundary = 1+lam+2*lam**2+3*lam**3
    f = 2+v+3*v*v+lam*(1+2*v+4*v*v)+lam**2*(5+v+v*v)+lam**3*(v+v**3)
    integral = s.integrate(f, (v, boundary, 4))
    at_edge = lambda expression: expression.subs({lam: 0, v: 1})
    calculated = third_lower_boundary_derivative(
        s.integrate(s.diff(f, lam, 3).subs(lam, 0), (v, 1, 4)),
        *[at_edge(expression) for expression in (
            f, s.diff(f, lam), s.diff(f, v), s.diff(f, lam, 2),
            s.diff(f, lam, v), s.diff(f, v, 2))], 1, 4, 18)
    assert s.expand(s.diff(integral, lam, 3).subs(lam, 0)-calculated) == 0
    print("PASS: all six third-order moving-diagonal contact terms")


if __name__ == "__main__":
    check_interior_short_identities()
