"""Actual-region diagnostics for notes/dimension-long-null.md, not Lean proofs.

Physical dimension d means d-1 spatial coordinates. The cutoff is v=t+r,
angular measure is ordinary sphere area, and the kernel/normalization are
imported from the existing dimension family. Contact models are explicitly
separate negative controls, never substitutes for a region's overlap.
"""

from mpmath import mp
import sympy as s

from dimension_kernels import (
    Z, action_constants, interval_coefficient, kernel_polynomial,
    sphere_area, transverse_moment,
)


def _dimension(d):
    if isinstance(d, bool) or not isinstance(d, int) or d < 3:
        raise ValueError("these diagnostics require integer physical dimension >= 3")
    return d


def _positive(value, name):
    value = mp.mpf(value)
    if not mp.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and positive")
    return value


def _causal(sigma, v):
    v = _positive(v, "v")
    sigma = mp.mpf(sigma)
    if not mp.isfinite(sigma) or not 0 <= sigma <= v*v:
        raise ValueError("causal ray requires 0 <= sigma <= v^2")
    return sigma, v


def ray_coordinates(sigma, v):
    sigma, v = _causal(sigma, v)
    return (v + sigma/v)/2, (v - sigma/v)/2


def ray_jacobian(d, sigma, v):
    _dimension(d)
    sigma, v = _causal(sigma, v)
    return (v - sigma/v)**(d - 2) / (2**(d - 1) * v)


def _ball_data(d, height, bend, x, omega):
    _dimension(d)
    height = _positive(height, "height")
    bend = mp.mpf(bend)
    if not mp.isfinite(bend) or bend < 0 or 2*height + bend >= 1:
        raise ValueError("require bend >= 0 and the strict budget 2*height+bend < 1")
    x, omega = tuple(map(mp.mpf, x)), tuple(map(mp.mpf, omega))
    if len(x) != d - 1 or len(omega) != d - 1:
        raise ValueError("x and omega must have d-1 spatial coordinates")
    if not all(mp.isfinite(t) for t in (*x, *omega)):
        raise ValueError("coordinates must be finite")
    if abs(mp.fsum(t*t for t in omega) - 1) > 32*mp.eps:
        raise ValueError("omega must be a unit direction")
    return height, bend, x, omega


def ball_sine_gap(d, height, bend, x, omega, sigma, v, *, intersect=False):
    """Raw ray gap, or the independently intersected nonnegative fibre length."""
    height, bend, x, omega = _ball_data(d, height, bend, x, omega)
    t, r = ray_coordinates(sigma, v)
    y = tuple(xi + r*wi for xi, wi in zip(x, omega))
    H = lambda p: max(mp.mpf(0), height*(1 - mp.fsum(z*z for z in p)))
    f = lambda p: bend*mp.sin(p[0])
    if intersect:
        return max(mp.mpf(0), min(f(x), f(y)-t)
                   - max(f(x)-H(x), f(y)-H(y)-t))
    return H(x) + f(y) - f(x) - t


def _bisect_root(gap, lower, upper):
    # Callers prove strict decrease on this bracket from the slope budget.
    for _ in range(mp.prec + 10):
        middle = (lower + upper)/2
        if gap(middle) > 0:
            lower = middle
        else:
            upper = middle
    return (lower + upper)/2


def ball_sine_fibre(d, height, bend, x, omega, delta, sigma, *, intersect=False):
    """Actual near-null v fibre; no angular/spatial averaging is replaced.

    Restrict sigma so strict v decrease holds uniformly. The caller cannot
    silently apply this root algorithm in a timelike nonmonotone regime.
    """
    height, bend, x, omega = _ball_data(d, height, bend, x, omega)
    delta = _positive(delta, "delta")
    sigma = mp.mpf(sigma)
    if not mp.isfinite(sigma) or not 0 <= sigma <= delta**2*(1-bend)/(2*(1+bend)):
        raise ValueError("sigma must lie in the controlled near-null interval")
    gap = lambda v: ball_sine_gap(d, height, bend, x, omega, sigma, v)
    if gap(delta) <= 0:
        return mp.mpf(0)
    upper = delta + 2*height/(1-bend) + 1
    root = _bisect_root(gap, delta, upper)
    def integrand(v):
        length = (ball_sine_gap(d, height, bend, x, omega, sigma, v, intersect=True)
                  if intersect else max(mp.mpf(0), gap(v)))
        return ray_jacobian(d, sigma, v)*length
    return mp.quad(integrand, [delta, root])


def ball_sine_fibre_jet(d, height, bend, x, omega, delta):
    """Return (F0,F1,F2,moving_contact); F2 includes the contact coefficient."""
    height, bend, x, omega = _ball_data(d, height, bend, x, omega)
    delta = _positive(delta, "delta")
    gap = lambda v: ball_sine_gap(d, height, bend, x, omega, 0, v)
    if gap(delta) <= 0:
        return (mp.mpf(0),)*4
    root = _bisect_root(gap, delta, delta + 2*height/(1-bend) + 1)
    J0 = lambda v: v**(d-3)/2**(d-1)
    J1 = lambda v: -(d-2)*v**(d-5)/2**(d-1)
    J2 = lambda v: mp.mpf((d-2)*(d-3))/2*v**(d-7)/2**(d-1)
    first = lambda v: bend*omega[0]*mp.cos(x[0]+v*omega[0]/2)
    a = lambda v: -(1+first(v))/(2*v)
    b = lambda v: -bend*omega[0]**2*mp.sin(x[0]+v*omega[0]/2)/(8*v*v)
    contact = J0(root)*a(root)**2/(1-first(root))
    F0 = mp.quad(lambda v: J0(v)*gap(v), [delta, root])
    F1 = mp.quad(lambda v: J1(v)*gap(v)+J0(v)*a(v), [delta, root])
    F2 = mp.quad(lambda v: J2(v)*gap(v)+J1(v)*a(v)+J0(v)*b(v), [delta, root]) + contact
    return F0, F1, F2, contact


def _area(d):
    return 2*mp.pi**(mp.mpf(d-1)/2)/mp.gamma(mp.mpf(d-1)/2)


def planar_ball_overlap(d, height, t):
    """Actual V_M(t,r*omega) for causal displacements, independent of r."""
    _dimension(d)
    height = _positive(height, "height")
    if 2*height >= 1:
        raise ValueError("planar ball requires 2*height < 1")
    t = mp.mpf(t)
    if not mp.isfinite(t) or t < 0:
        raise ValueError("elapsed time must be finite and nonnegative")
    n = d-1
    ball_volume = mp.pi**(mp.mpf(n)/2)/mp.gamma(1+mp.mpf(n)/2)
    return 2*height*ball_volume/(n+2)*max(mp.mpf(0), 1-t/height)**(mp.mpf(n+2)/2)


def planar_ball_density(d, height, delta, sigma, *, coordinates="time"):
    """Actual averaged B, by independent time- or null-coordinate integrals."""
    _dimension(d)
    height, delta = _positive(height, "height"), _positive(delta, "delta")
    planar_ball_overlap(d, height, 0)  # validate the strict face budget
    sigma = mp.mpf(sigma)
    if not mp.isfinite(sigma):
        raise ValueError("sigma must be finite")
    if coordinates not in ("time", "null"):
        raise ValueError("coordinates must be time or null")
    if sigma < 0 or sigma >= height*height:
        return mp.mpf(0)
    lower = (delta+sigma/delta)/2 if sigma < delta**2 else mp.sqrt(sigma)
    if lower >= height:
        return mp.mpf(0)
    if coordinates == "time":
        if d == 3:
            return mp.pi**2/(6*height)*(height-lower)**3
        return _area(d)/2*mp.quad(
            lambda t: max(mp.mpf(0), t*t-sigma)**(mp.mpf(d-3)/2)
            * planar_ball_overlap(d, height, t), [lower, height])
    vmin = max(delta, mp.sqrt(sigma))
    vmax = height + mp.sqrt(height*height-sigma)
    return _area(d)*mp.quad(
        lambda v: ray_jacobian(d, sigma, v)
        * planar_ball_overlap(d, height, ray_coordinates(sigma, v)[0]), [vmin, vmax])


def planar_three_long_action(height, delta, rho):
    """Full signed long pair term, not absolute kernel or reduced plane action.

    Uses the exact piecewise 3D density and scaled quadrature; no jet is
    substituted and no signed moment is subtracted from the integrand.
    """
    height, delta, rho = (_positive(v, name) for v, name in
                          ((height, "height"), (delta, "delta"), (rho, "rho")))
    planar_ball_overlap(3, height, 0)
    c = mp.pi/12
    beta = 2*c**(mp.mpf(2)/3)/mp.gamma(mp.mpf(5)/3)
    scale = (c*rho)**(-mp.mpf(2)/3)
    upper = height**2/scale
    transition = delta**2/scale
    points = sorted(set([mp.mpf(0), upper]
                        + [mp.mpf(t) for t in (1, 2, 4, 8, 16, transition) if 0 < t < upper]))
    def integrand(u):
        z = u**mp.mpf("1.5")
        kernel = (1-mp.mpf(27)/8*z+mp.mpf(9)/8*z*z)*mp.exp(-z)
        return planar_ball_density(3, height, delta, scale*u)*kernel
    return -beta*rho**(mp.mpf(5)/3)*scale*mp.quad(integrand, points)


def check_long_null_identities():
    """Exact finite algebra checks, including retained fractional/log terms."""
    sigma, v, a, delta, x = s.symbols("sigma v a delta x", positive=True)
    for d in (3, 4, 5, 6):
        J = (v-sigma/v)**(d-2)/(2**(d-1)*v)
        expected = (v**(d-3)/2**(d-1), -(d-2)*v**(d-5)/2**(d-1),
                    s.binomial(d-2, 2)*v**(d-7)/2**(d-1))
        for j, coefficient in enumerate(expected):
            assert s.simplify(s.diff(J, sigma, j).subs(sigma, 0)/s.factorial(j)-coefficient) == 0
    actual = 2*s.integrate((x*x-sigma)**2, (x, s.sqrt(sigma), 1))
    assert s.simplify(actual-(s.Rational(2, 5)-4*sigma/3+2*sigma**2
                             -s.Rational(16, 15)*sigma**s.Rational(5, 2))) == 0
    logarithmic = s.integrate((a-sigma)**2*(-s.log(a)), (a, sigma, 1))
    assert s.simplify(logarithmic-(s.Rational(1, 9)-sigma/2+sigma**2
                                  +sigma**3*s.log(sigma)/3-11*sigma**3/18)) == 0
    assert s.simplify(transverse_moment(5, s.Rational(5, 2))+s.gamma(s.Rational(7, 5))/8) == 0
    order = s.Symbol("j", real=True)
    assert s.simplify(s.diff(transverse_moment(6, order), order).subs(order, 3)
                      -s.gamma(s.Rational(4, 3))/12) == 0
    # Derive the planar d=3 density from the actual spatial/time integrals.
    spatial = 2*s.pi*s.integrate((a-v-a*x*x)*x, (x, 0, s.sqrt(1-v/a)))
    density = sphere_area(3)/2*s.integrate(spatial, (v, (delta+sigma/delta)/2, a))
    assert s.simplify(density-s.pi**2/(6*a)*(a-delta/2-sigma/(2*delta))**3) == 0
    # Full normalization agrees with the existing actual dimension family.
    assert kernel_polynomial(3) == 1-s.Rational(27, 8)*Z+s.Rational(9, 8)*Z**2
    assert interval_coefficient(3) == s.pi/12
    assert s.simplify(action_constants(3)[1]-2*(s.pi/12)**s.Rational(2, 3)
                      /s.gamma(s.Rational(5, 3))) == 0
    print("PASS: actual long-overlap Jacobians, planar 3D density, retained contact coefficients (3..6)")
