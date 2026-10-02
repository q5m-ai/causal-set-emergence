"""Finite-geometry diagnostics for notes/dimension-two-face-geometry.md (#92).

Physical dimension is explicit: d = spatial dimension + 1, joint dimension d-2.
These routines evaluate derivatives/Gram matrices, not actions, asymptotic limits,
or arbitrary geometric admissibility. The written class/goal contracts live in
that note; no Python object is a certificate of those universal hypotheses.
"""

from dataclasses import dataclass

from mpmath import mp
import sympy as s


def _dimension(d):
    if isinstance(d, bool) or not isinstance(d, int) or d < 2:
        raise ValueError("physical dimension must be an integer >= 2")
    return d


def _vector(values, size):
    values = tuple(mp.mpf(value) for value in values)
    if len(values) != size or not all(mp.isfinite(value) for value in values):
        raise ValueError(f"expected {size} finite real coordinates")
    return values


def _dot(v, w):
    return mp.fsum(a * b for a, b in zip(v, w))


def lorentz_inner(d, v, w):
    """Actual (+,-,...,-) bilinear form; no Euclidean spacetime substitute."""
    _dimension(d)
    v, w = _vector(v, d), _vector(w, d)
    return v[0] * w[0] - _dot(v[1:], w[1:])


def future_normal(d, gradient):
    """Future unit normal of a strictly spacelike graph from its gradient."""
    _dimension(d)
    q = _vector(gradient, d - 1)
    square = 1 - _dot(q, q)
    if square <= 0:
        raise ValueError("graph gradient must have norm strictly less than one")
    norm = mp.sqrt(square)
    return tuple(value / norm for value in (mp.mpf(1), *q))


def graph_tangent(d, gradient, vector):
    """Derivative of x -> (f(x),x); callers supply actual spatial tangents."""
    _dimension(d)
    q, v = _vector(gradient, d - 1), _vector(vector, d - 1)
    return (_dot(q, v), *v)


def induced_gram_density(d, frame):
    """sqrt(det(-g(v_i,v_j))) for d-2 independent spacelike joint tangents.

    Positive definiteness is checked, not inferred from a positive determinant
    (two timelike/negative directions would invalidate that inference). The
    empty determinant is one, giving counting measure in physical dimension 2.
    """
    _dimension(d)
    frame = tuple(_vector(vector, d) for vector in frame)
    if len(frame) != d - 2:
        raise ValueError("joint frame must contain exactly d-2 vectors")
    if not frame:
        return mp.mpf(1)
    gram = mp.matrix([[-lorentz_inner(d, v, w) for w in frame] for v in frame])
    try:
        cholesky = mp.cholesky(gram)
    except ValueError as error:
        raise ValueError("joint Gram matrix must be positive definite") from error
    return mp.fprod(cholesky[i, i] for i in range(d - 2))


@dataclass(frozen=True)
class JointPointGeometry:
    """Numerical values at one supplied regular joint point, not a measure."""

    physical_dimension: int
    past_normal: tuple
    future_normal: tuple
    cosh: object
    angle: object
    weight: object
    area_density: object
    target_density: object


def joint_point_geometry(d, grad_h, grad_f):
    """Compute normal/metric data from gradients; target density uses N/|dh|.

    Weight is computed independently from the two normalized timelike normals.
    Area density is computed from spatial orthogonal projection. Regressions
    compare their product with target_density; it is not defined as that product.
    A zero joint differential or unresolved numerical angle is rejected.
    """
    _dimension(d)
    a, q = _vector(grad_h, d - 1), _vector(grad_f, d - 1)
    k = mp.sqrt(_dot(a, a))
    if k == 0:
        raise ValueError("joint height differential must be nonzero")
    p = tuple(qi - ai for qi, ai in zip(q, a))
    past, future = future_normal(d, p), future_normal(d, q)
    C = lorentz_inner(d, past, future)
    if C <= 1:
        raise ValueError("positive angle unresolved; increase numerical precision")
    nu = tuple(ai / k for ai in a)
    qn = _dot(q, nu)
    b = tuple(qi - qn * ni for qi, ni in zip(q, nu))
    area = mp.sqrt(1 - _dot(b, b))
    return JointPointGeometry(
        d, past, future, C, mp.acosh(C), C / mp.sqrt(C**2 - 1),
        area, (1 - _dot(q, p)) / k,
    )


def boost(d, vector, velocity, axis=0):
    """A genuine future-preserving Lorentz boost on one spatial coordinate."""
    _dimension(d)
    v = _vector(vector, d)
    velocity = mp.mpf(velocity)
    if not mp.isfinite(velocity) or abs(velocity) >= 1:
        raise ValueError("boost velocity must be finite with magnitude < 1")
    if isinstance(axis, bool) or not isinstance(axis, int) or not 0 <= axis < d - 1:
        raise ValueError("boost axis must index a spatial coordinate")
    gamma = 1 / mp.sqrt(1 - velocity**2)
    result = list(v)
    result[0] = gamma * (v[0] - velocity * v[axis + 1])
    result[axis + 1] = gamma * (v[axis + 1] - velocity * v[0])
    return tuple(result)


@dataclass(frozen=True)
class BallSineRegion:
    """The explicit smooth nonempty example (G20), not arbitrary admissibility.

    h=a(1-|x|^2), f=epsilon*sin(x_1); 2a+epsilon<1 is a geometric budget.
    The joint includes the entire unit sphere. The interior critical point at
    the origin is deliberately retained. In d=2 the sphere has two points.
    """

    physical_dimension: int
    height: object = "0.25"
    bend: object = "0.125"

    def __post_init__(self):
        _dimension(self.physical_dimension)
        a, epsilon = mp.mpf(self.height), mp.mpf(self.bend)
        if not (mp.isfinite(a) and mp.isfinite(epsilon)
                and a > 0 and epsilon >= 0 and 2 * a + epsilon < 1):
            raise ValueError("require a>0, epsilon>=0 and 2a+epsilon<1")
        object.__setattr__(self, "height", a)
        object.__setattr__(self, "bend", epsilon)

    def data(self, x):
        """Return raw h, f and their actual gradients, also at exterior points."""
        x = _vector(x, self.physical_dimension - 1)
        h = self.height * (1 - _dot(x, x))
        f = self.bend * mp.sin(x[0])
        grad_h = tuple(-2 * self.height * xi for xi in x)
        grad_f = (self.bend * mp.cos(x[0]),) + (mp.mpf(0),) * (len(x) - 1)
        return h, f, grad_h, grad_f

    def contains(self, event):
        event = _vector(event, self.physical_dimension)
        h, f, *_ = self.data(event[1:])
        return f - h < event[0] < f

    def stratum(self, event):
        """Exact predicates for this explicit family; no floating tolerance.

        Points off the closed positive ball cannot be faces, even if an
        extension of a raw graph passes through them.
        """
        event = _vector(event, self.physical_dimension)
        x = event[1:]
        if _dot(x, x) > 1:
            return "exterior"
        h, f, *_ = self.data(x)
        if h == 0 and event[0] == f:
            return "joint"
        if event[0] == f - h:
            return "past"
        if event[0] == f:
            return "future"
        return "interior" if self.contains(event) else "exterior"


def check_joint_identities():
    """Exact algebra checks, not proofs of global geometry/limits.

    G9 is an identity in the three abstract scalar products in any dimension.
    The Gram determinant checks in dimensions 0..4 are only finite regressions;
    the written all-dimension argument uses the matrix determinant lemma.
    """
    aa, qq, aq = s.symbols("aa qq aq", real=True)
    numerator = 1 - qq + aq
    A, B = 1 - qq, 1 - qq + 2 * aq - aa
    assert s.expand(numerator**2 - A * B - (aa * (1 - qq) + aq**2)) == 0
    for m in range(5):
        tangent_q = s.Matrix(m, 1, s.symbols(f"b0:{m}", real=True))
        gram = s.eye(m) - tangent_q * tangent_q.T
        assert s.expand(gram.det() - (1 - sum(b**2 for b in tangent_q))) == 0
    print("PASS: dimension-independent normal discriminant; joint Gram regressions (d=2..6)")


if __name__ == "__main__":
    check_joint_identities()
