"""3D direct-origin short diagnostics, not a formal or global limit solver.

Written proof/consumer contract: notes/dimension-three-short.md. The observable
uses the unchanged SmoothPilot3 action and v=tau+|b|<delta. Model evaluators are
explicitly distinguished from an actual ball/cosine overlap. No production
region, admissibility, intrinsic-target or Lean API is introduced here.
"""

import math

from mpmath import mp
import numpy as np
from scipy.integrate import quad
import sympy as s


def short_basis3_symbolic(sigma, delta):
    """In-support densities of (1,tau,tau^2,r^2), WITHOUT circle area.

    The formula is valid for 0<=sigma<=delta^2, delta>0; the actual sharp-cutoff
    densities are zero above it. Symbols/domain assumptions belong to callers.
    """
    sigma, delta = s.sympify(sigma), s.sympify(delta)
    return (
        delta/4 + sigma/(4*delta) - s.sqrt(sigma)/2,
        delta**2/16 - sigma/8 + sigma**2/(16*delta**2),
        delta**3/48 + sigma*delta/16 + sigma**2/(16*delta)
        + sigma**3/(48*delta**3) - sigma**s.Rational(3, 2)/6,
        delta**3/48 - 3*sigma*delta/16 - 3*sigma**2/(16*delta)
        + sigma**3/(48*delta**3) + sigma**s.Rational(3, 2)/3,
    )


def _positive(value, name):
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and positive")


def short_basis3(sigma, delta):
    """Stable float64 evaluation of the four actual sharp-cutoff fibres."""
    _positive(delta, "delta")
    if not math.isfinite(sigma) or sigma < 0:
        raise ValueError("sigma must be finite and nonnegative")
    if sigma >= delta**2:
        return np.zeros(4)
    x = sigma/delta**2
    t = math.sqrt(x)
    gap = (1-x)/(1+t)
    return np.array([
        delta*gap**2/4,
        delta**2*(1-x)**2/16,
        delta**3*gap**2*(t**4 + 2*t**3 + 6*t**2 + 2*t + 1)/48,
        delta**3*gap**4*(t**2 + 4*t + 1)/48,
    ])


def jet_short_action3(angular, rho, delta, *, dps=50):
    """Finite-density QUADRATIC MODEL action via incomplete gamma integrals.

    Coefficients already contain full circle area. All four modes, the point
    term, signs and sharp endpoint are kept; no large-density tail is deleted.
    This is not an arbitrary region evaluator or a certified numerical bound.
    """
    _positive(rho, "rho")
    _positive(delta, "delta")
    angular = tuple(angular)
    if len(angular) != 4 or not all(mp.isfinite(value) for value in angular):
        raise ValueError("require four finite angular coefficients")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 20:
        raise ValueError("dps must be an integer >= 20")
    with mp.workdps(dps):
        rho, delta = mp.mpf(rho), mp.mpf(delta)
        constant, linear, alpha, beta = map(mp.mpf, angular)
        c = mp.pi/12
        normalization = 2*c**(mp.mpf(2)/3)/mp.gamma(mp.mpf(5)/3)

        def moment(power):
            exponent = 2*(power+1)/3
            return (mp.mpf(2)/3 * (c*rho)**(-exponent)
                    * mp.fsum(coefficient * mp.gammainc(exponent+k, 0, c*rho*delta**3)
                              for k, coefficient in enumerate(
                                  (1, -mp.mpf(27)/8, mp.mpf(9)/8))))

        # Expand the independent closed fibres, including critical half powers.
        coefficients = (
            (0, constant*delta/4 + linear*delta**2/16 + (alpha+beta)*delta**3/48),
            (mp.mpf(1)/2, -constant/2),
            (1, constant/(4*delta) - linear/8 + (alpha-3*beta)*delta/16),
            (mp.mpf(3)/2, -alpha/6 + beta/3),
            (2, linear/(16*delta**2) + (alpha-3*beta)/(16*delta)),
            (3, (alpha+beta)/(48*delta**3)),
        )
        pair = mp.fsum(coefficient*moment(mp.mpf(power)) for power, coefficient in coefficients)
        return normalization*rho**(mp.mpf(2)/3)*(constant/(2*mp.pi) - rho*pair)


def _ball_cos_parameters(height, bend):
    if not (math.isfinite(height) and math.isfinite(bend)
            and height > 0 and bend >= 0 and 2*height + bend < 1):
        raise ValueError("require height>0, bend>=0 and 2*height+bend<1")


def ball_cos_overlap3(tau, spatial, *, height=0.25, bend=0.125, weight=None):
    """Actual causal overlap for h=a(1-|x|^2), f=epsilon*cos(x_1).

    Vertical and x_2 integrals are performed exactly, then x_1 is quadrature.
    Optional real spatial source weight depends on x_1; ALL partners remain.
    The geometric budget is specific to this diagnostic family, not an
    admissibility decision procedure. Quadrature errors are not certified.
    """
    _ball_cos_parameters(height, bend)
    spatial = tuple(spatial)
    if (len(spatial) != 2 or not math.isfinite(tau)
            or not all(math.isfinite(value) for value in spatial)
            or tau < math.hypot(*spatial)):
        raise ValueError("require a finite future-causal 3D displacement")
    w = (lambda _: 1.0) if weight is None else weight
    bx = spatial[0]

    def fibre(x):
        gap = height*(1-x*x) - tau + bend*(math.cos(x+bx)-math.cos(x))
        return w(x)*max(0.0, gap)**1.5

    return 4/(3*math.sqrt(height))*quad(fibre, -1, 1, points=[0],
                                      epsabs=2e-13, epsrel=2e-13, limit=200)[0]


def ball_cos_jet3(*, height=0.25, bend=0.125, weight=None, weight_prime=None):
    """Jet from bulk/surface integrals, NOT a fitted action or target value.

    This example deliberately has a nonzero future-Hessian integral. The
    returned artificial derivative term is evaluated separately. Normal/Gram
    target checks belong to the independent dimension_joint_geometry module.
    """
    _ball_cos_parameters(height, bend)
    w = (lambda _: 1.0) if weight is None else weight
    wp = (lambda _: 0.0) if weight is None else weight_prime
    if wp is None:
        raise ValueError("supply weight_prime with weight")
    integral = lambda f: quad(f, -1, 1, epsabs=2e-12, epsrel=2e-12)[0]
    circle = lambda f: quad(lambda theta: f(math.cos(theta)), 0, 2*math.pi,
                            epsabs=2e-12, epsrel=2e-12)[0]
    volume = 4*height/3*integral(lambda x: w(x)*(1-x*x)**1.5)
    area = 2*integral(lambda x: w(x)*math.sqrt(1-x*x))
    hessian = 2*integral(lambda x: -w(x)*bend*math.cos(x)*math.sqrt(1-x*x))
    surface = circle(w)/(2*height)
    surface_square = circle(lambda x: w(x)*(bend*math.sin(x))**2)/(2*height)
    derivative = 2*integral(lambda x: -wp(x)*bend*math.sin(x)*math.sqrt(1-x*x))
    angular = np.array([2*math.pi*volume, -2*math.pi*area,
                        math.pi*surface, math.pi/2*(hessian+surface_square)])
    return {"angular": angular, "future_hessian": hessian,
            "partition_derivative": derivative,
            "short_coefficient": (angular[2]-2*angular[3])/math.pi}


def check_short3_identities():
    """Exact finite regressions; written derivations are not Lean theorems."""
    from dimension_kernels import action_constants, interval_coefficient, transverse_moment

    sigma, delta, v = s.symbols("sigma delta v", positive=True)
    tau, radius = (v+sigma/v)/2, (v-sigma/v)/2
    jacobian = (1-sigma/v**2)/4
    for expected, monomial in zip(short_basis3_symbolic(sigma, delta),
                                  (1, tau, tau**2, radius**2)):
        primitive = s.integrate(s.expand(jacobian*monomial), v)
        actual = primitive.subs(v, delta)-primitive.subs(v, s.sqrt(sigma))
        assert s.simplify(actual-expected) == 0
    point, pair = action_constants(3)
    c = interval_coefficient(3)
    assert transverse_moment(3, 0) == transverse_moment(3, 1) == 0
    assert s.simplify(point + pair*s.pi*transverse_moment(3, s.Rational(1, 2))/c) == 0
    response = -pair*c**(-s.Rational(5, 3))*transverse_moment(3, s.Rational(3, 2))
    assert s.simplify(response + 6/s.pi) == 0
    print("PASS: 3D moving short fibres, signed half-powers and physical normalization")


if __name__ == "__main__":
    check_short3_identities()
