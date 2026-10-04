"""Finite certificates for the written #75 curved-joint theorem.

The universal signed comparison is in notes/curved-joint-corner.md, not proved
by these identities. The actual H16 functional and canonical action are
unchanged. Geometry is calculated before comparing its density with the
signed corner response and the compensating single-face flux.
"""

import sympy as s

from curved_boundary_collar import face_basis_responses
from curved_bulk_pilot import null_phase_factor


def minkowski_inner(v, w):
    """Signature (+---), for four-coordinate vectors."""
    return v[0]*w[0]-sum(v[i]*w[i] for i in range(1, 4))


def future_normal(gradient, q):
    """Actual future g-unit graph normal for g=sqrt(q)*eta; |gradient|<1."""
    gradient = tuple(map(s.sympify, gradient))
    denominator = s.sympify(q)**s.Rational(1, 4)*s.sqrt(1-sum(x*x for x in gradient))
    return tuple(x/denominator for x in (s.Integer(1), *gradient))


def induced_gram(v, w, gradient_f, q):
    """Positive induced two-frame Gram matrix from the actual joint lift."""
    v, w, p = (s.Matrix(x) for x in (v, w, gradient_f))
    return s.sqrt(q)*s.Matrix([[v.dot(v)-p.dot(v)**2, v.dot(w)-p.dot(v)*p.dot(w)],
                               [v.dot(w)-p.dot(v)*p.dot(w), w.dot(w)-p.dot(w)**2]])


def corner_rectangle_jacobian(gap, gap_s, beta):
    """ds dA for s=beta*d(s), A=d(s)*(beta+(1-beta)*lambda)."""
    d, ds, beta = map(s.sympify, (gap, gap_s, beta))
    return (1-beta)*d*d/(1-beta*ds)


def corner_phase_derivative(t, t_u, u, v):
    """Total dw/du after flattening BOTH boundaries; source time moves."""
    t, tu, u, v = map(s.sympify, (t, t_u, u, v))
    h = null_phase_factor(t, u, v)
    hu, ht = t/2+3*u/20+7*v/60, 2*t+(u+v)/2
    return v*(2*h+u*(hu+ht*tu))/(2*s.sqrt(h))


def tangent_corner_response(q, k, gradient_squared, trace_product=1):
    """The -C*rho^(3/2) tangent response per spatial joint area.

    Derived from the two signed logarithmic radial responses, not defined by
    the target angle integral. The nonzero single-face flux is NOT included.
    """
    q, k, p2, weight = map(s.sympify, (q, k, gradient_squared, trace_product))
    _, t2, r2, _ = face_basis_responses(q)
    return s.simplify(-q*q*weight*(t2+p2*r2/3)/(2*k))


def check_joint_corner_identities():
    q, k = s.symbols("q k", positive=True)
    p1, p2, pn = s.symbols("p1 p2 pn", real=True)
    p = (p1, p2, pn)
    past = (p1, p2, pn-k)  # Height normal aligned with the third axis.
    nf, nl = future_normal(p, q), future_normal(past, q)
    assert s.simplify(s.sqrt(q)*minkowski_inner(nf, nf)) == 1
    assert s.simplify(s.sqrt(q)*minkowski_inner(nl, nl)) == 1
    numerator = 1-p1*p1-p2*p2-pn*pn+pn*k
    denominator_squared = (1-p1*p1-p2*p2-pn*pn)*(1-p1*p1-p2*p2-(pn-k)**2)
    assert s.expand(numerator**2-denominator_squared-k*k*(1-p1*p1-p2*p2)) == 0
    gram = induced_gram((1, 0, 0), (0, 1, 0), p, q)
    assert s.expand(gram.det()-q*(1-p1*p1-p2*p2)) == 0
    print("PASS: conformal unit normals, positive-angle discriminant and induced Gram determinant")

    beta, lam, d0, ds = s.symbols("beta lam d0 ds", real=True)
    # Exact nonconstant-in-height gap. This checks the implicit denominator,
    # not just a rectangular constant-gap special case.
    height = beta*d0/(1-beta*ds)
    gap = d0+ds*height
    depth = gap*(beta+(1-beta)*lam)
    determinant = s.Matrix([[s.diff(height, beta), s.diff(height, lam)],
                             [s.diff(depth, beta), s.diff(depth, lam)]]).det()
    assert s.simplify(determinant-corner_rectangle_jacobian(gap, ds, beta)) == 0
    print("PASS: exact two-boundary corner rectangle Jacobian")

    u, v = s.symbols("u v", positive=True)
    t0, t1, t2 = s.symbols("t0 t1 t2", real=True)
    t = t0+t1*u+t2*u*u
    phase = u*v*s.sqrt(null_phase_factor(t, u, v))
    assert s.simplify(s.diff(phase, u)-corner_phase_derivative(t, s.diff(t, u), u, v)) == 0
    print("PASS: total curved corner phase derivative with moving source time")

    weight = s.Symbol("weight", real=True)
    p_squared = sum(x*x for x in p)
    raw = tangent_corner_response(q, k, p_squared, weight)
    # Outward spatial normal is -Dh/|Dh|, hence T=-sqrt(q)*weight*pn.
    flux = -s.sqrt(q)*weight*pn
    geometry = s.sqrt(q)*weight*numerator/k
    assert s.simplify(raw-flux-geometry) == 0
    assert s.simplify(raw-s.sqrt(q)*weight*(1-p_squared)/k) == 0
    print("PASS: signed tangent coefficient plus retained face flux equals independent geometry")


if __name__ == "__main__":
    check_joint_corner_identities()
