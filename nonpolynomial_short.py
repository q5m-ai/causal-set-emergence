"""Finite #136 certificates/diagnostics, NOT a production action or limit proof.

The actual signed estimates and conventional assembly are in
notes/nonpolynomial-short-limit.md. Shared action, geometry and probability
APIs are unchanged. The interval evaluator retains the nonpolynomial phase.
"""

import numpy as np
import sympy as s

from curved_bulk_pilot import second_jet_response
from curved_interior_short import angular_density_jet


def density(t):
    """q on the controlled slab; not its globally measurable extension."""
    return (1.0 - np.asarray(t))**-4


def phase_data(t, u, v):
    """Actual de Sitter H and its partial derivatives H_t,H_u,H_v (N6).

    A,B must be positive. The analytic continuation near the causal ratio
    interval is also used by the proof's local inverse; no global inverse is
    asserted. Evaluate S by a convergent series at small y to avoid loss of
    precision in log(1+y)-y/(1+y). This is NOT a displacement two-jet.
    """
    t, u, v = np.broadcast_arrays(t, u, v)
    A, B = 1-t, 1-t-(u+v)/2
    if np.any(A <= 0) or np.any(B <= 0):
        raise ValueError("endpoints must be in the t<1 patch")
    y = u*v/(4*A*B)
    if np.any(y <= -1):
        raise ValueError("outside the real analytic phase domain")
    small = np.abs(y) <= .125
    # Pick the finite evaluation order from a rigorous geometric tail bound,
    # not from the density or a fitted action. Both S and S' tails are below
    # long-double roundoff. Ignore direct-branch entries in the series itself.
    ys = np.where(small, y, 0)
    radius = np.max(np.abs(ys))
    terms = 2
    tolerance = np.finfo(np.longdouble).eps/8
    while radius and 2*terms*radius**(terms-1)/(1-radius)**2 > tolerance:
        terms += 1
    polynomial, derivative = np.zeros_like(y), np.zeros_like(y)
    for j in range(terms-1, -1, -1):
        derivative = derivative*ys + polynomial
        polynomial = polynomial*ys + (2*(-1)**j*(j+1)/np.longdouble(j+2))
    safe = np.where(small, .5, y)
    numerator = np.log1p(safe)-safe/(1+safe)
    direct = 2*numerator/safe**2
    direct_derivative = 2/(safe*(1+safe)**2)-4*numerator/safe**3
    S, Sy = np.where(small, polynomial, direct), np.where(small, derivative, direct_derivative)
    prefactor = (A*B)**-2
    h = prefactor*S
    ht = prefactor*(2*S+y*Sy)*(1/A+1/B)
    hu = prefactor*(S/B+Sy*(v/(4*A*B)+y/(2*B)))
    hv = prefactor*(S/B+Sy*(u/(4*A*B)+y/(2*B)))
    return h, ht, hu, hv


def total_phase_derivative(t, u, v, time_u=0):
    """dw/du after flattening: source time may move with the ratio."""
    h, ht, hu, _ = phase_data(t, u, v)
    return v*(2*h+u*(hu+ht*time_u))/(2*np.sqrt(h))


def check_nonpolynomial_identities():
    """Exact finite identities, separately from all analytic remainder proofs."""
    A = s.Symbol("A", positive=True)  # A=1-t
    T, r, lam = s.symbols("T r lam", real=True)
    alpha, b = s.symbols("alpha b", real=True)
    L = T/2+T*alpha+r*b
    # Independent normalized rest-diamond moments, not assumed Taylor data.
    moments = []
    for k in range(4):
        value = 0
        for lo, hi, radius in ((-s.Rational(1, 2), 0, s.Rational(1, 2)+alpha),
                               (0, s.Rational(1, 2), s.Rational(1, 2)-alpha)):
            disk_integral = s.integrate((radius**2-b*b)*L**k, (b, -radius, radius))
            value += 24*s.integrate(disk_integral, (alpha, lo, hi))
        moments.append(s.expand(value))
    sigma = T*T-r*r
    assert moments == [1, T/2, 4*T*T/s.Integer(15)+r*r/30,
                        3*T**3/s.Integer(20)+T*r*r/20]
    q, q1, q2, q3 = A**-4, 4*A**-5, 20*A**-6, 120*A**-7
    hjet = sum(qk*moments[k]*lam**k/s.factorial(k)
               for k, qk in enumerate((q, q1, q2, q3)))
    assert s.expand(hjet.coeff(lam, 2)-q2*(3*T*T/s.Integer(20)-sigma/60)) == 0
    assert s.expand(hjet.coeff(lam, 3)-q3*(T**3/30-T*sigma/120)) == 0
    assert hjet.coeff(lam, 3).subs(r, 0) == 3*T**3/A**7
    # This cubic term rules out the old exact quadratic interpolation.
    print("PASS: actual rest-diamond moments and nonzero nonpolynomial cubic jet")

    # An exact rational primitive certificate for the disk-section integral.
    # After x=s/A and x=-s/B the two logarithm products both equal 1+y.
    x, u, v = s.symbols("x u v", nonzero=True)
    gap = u-v
    cu, cv = (3*u-v)/(u*u*gap**3), (u-3*v)/(v*v*gap**3)
    rational = 1/(u*u*gap**2*(1-u*x))+1/(v*v*gap**2*(1-v*x))
    primitive = cu*s.log(1-u*x)+cv*s.log(1-v*x)+rational
    assert s.factor(s.diff(primitive, x)-x**3/((1-u*x)**2*(1-v*x)**2)) == 0
    B = A-(u+v)/2
    y0 = u*v/(4*A*B)
    for k in (u, v):
        assert s.factor((1-k/(2*A))*(1+k/(2*B))-1-y0) == 0
    assert s.factor(cu+cv-1/(u*v)**2) == 0
    endpoints = rational.subs(x, 1/(2*A))+rational.subs(x, -1/(2*B))-2*rational.subs(x, 0)
    assert s.factor(endpoints+y0/((u*v)**2*(1+y0))) == 0
    print("PASS: exact section primitive gives the full rational/log phase")

    y = s.Symbol("y", positive=True)
    S = 2*(s.log(1+y)-y/(1+y))/y**2
    assert s.series(S, y, 0, 5).removeO() == 1-4*y/3+3*y*y/2-8*y**3/5+5*y**4/3
    u, v = s.symbols("u v", real=True)
    B = A-lam*(u+v)/2
    yy = lam*lam*u*v/(4*A*B)
    # Only finite jet comparison, not using a truncated S in the analysis.
    phase_jet = s.series((1-4*yy/3+3*yy**2/2)/(A*B)**2, lam, 0, 4).removeO()
    assert s.simplify(phase_jet-hjet.subs({T: (u+v)/2, r: (v-u)/2})) == 0

    phi, pt, ptt, lap, z, k0, k1, k2 = s.symbols("phi pt ptt lap z k0 k1 k2")
    endpoint_jet = (phi+lam*T*pt+lam**2*(T*T*ptt/2+r*r*lap/6))*(A-lam*T)**-4
    phase_increment = z*(hjet/q-1)
    direct_jet = endpoint_jet*(k0+k1*phase_increment+k2*phase_increment**2/2)
    expected = angular_density_jet(q, q1, q2, T, sigma, z, phi, pt, ptt, lap, k0, k1, k2)
    for j in range(3):
        assert s.simplify(s.diff(direct_jet, lam, j).subs(lam, 0)/s.factorial(j)-expected[j]) == 0
    response = second_jet_response(q, q1, q2, phi, pt, ptt, lap)
    assert s.simplify(response-(A*A*(ptt-lap)+2*A*pt+6*phi)) == 0
    print("PASS: complete endpoint/interval second jet, including K'', and derived response")

    # New diagonal jet with a moving source; higher terms do not terminate.
    depth, f = s.symbols("depth f", real=True)
    diagonal = phase_jet.subs({u: v, A: A+depth*lam*v})
    diagonal = s.series(diagonal, lam, 0, 4).removeO().expand()
    expected_second = q2*(depth**2/2-depth/2+s.Rational(2, 15))*v*v
    assert s.simplify(diagonal.coeff(lam, 2)-expected_second) == 0
    assert s.simplify(diagonal.coeff(lam, 3)
                      - q3*(-depth**3/6+depth**2/4-2*depth/15+s.Rational(1, 40))*v**3) == 0
    yy = u*v/(4*(1-f)*(1-f-(u+v)/2))
    exact_h = S.subs(y, yy)/((1-f)*(1-f-(u+v)/2))**2
    time = f+depth*u+u*u
    moving_h = exact_h.subs(f, time)
    total_hu = (s.diff(exact_h, u).subs(f, time)
                + s.diff(exact_h, f).subs(f, time)*s.diff(time, u))
    assert s.factor(s.diff(moving_h, u)-total_hu) == 0
    phase_factor = s.Function("phase_factor")(u)
    derivative = v*(2*phase_factor+u*s.diff(phase_factor, u))/(2*s.sqrt(phase_factor))
    assert s.simplify(s.diff(u*v*s.sqrt(phase_factor), u)-derivative) == 0
    print("PASS: nonpolynomial moving diagonal and total source-time phase Jacobian")


if __name__ == "__main__":
    check_nonpolynomial_identities()
