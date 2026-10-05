"""Bounded 5D/6D short diagnostics for notes/dimension-five-six-short.md.

Written proofs, not Lean results or an arbitrary-region limit solver. Actual
ball overlaps are separate from the explicitly quadratic MODEL action. No
production geometry, target, layer normalization or formal API is replaced.
"""

from functools import lru_cache
import math

from mpmath import mp
import numpy as np
from scipy.integrate import quad
import sympy as s

from dimension_kernels import (
    action_constants, interval_coefficient, kernel_polynomial, sphere_area,
    transverse_moment, Z,
)


def _dimension(d):
    if isinstance(d, bool) or not isinstance(d, int) or d not in (5, 6):
        raise ValueError("this diagnostic supports physical dimensions 5 and 6 only")


def _positive(value, name):
    if not mp.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and positive")


def _precision(dps):
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise ValueError("dps must be an integer >= 30")


def short_basis56_symbolic(d, sigma, delta):
    """Closed in-support fibres (1,tau,tau^2,r^2), WITHOUT sphere area.

    Valid on 0<sigma<=delta^2, delta>0. Actual fibres are zero above the
    cutoff and have continuous limits at zero (avoid evaluating 0*log(0)).
    This explicit table is checked against independent Laurent integration.
    """
    _dimension(d)
    x, L = s.sympify(sigma), s.sympify(delta)
    if d == 5:
        return (
            L**3/48 - 3*L*x/16 + x**s.Rational(3, 2)/3
            - 3*x**2/(16*L) + x**3/(48*L**3),
            L**4/128 - L**2*x/32 + 3*x**2/64
            - x**3/(32*L**2) + x**4/(128*L**4),
            L**5/320 - L**3*x/192 - L*x**2/32 + x**s.Rational(5, 2)/15
            - x**3/(32*L) - x**4/(192*L**3) + x**5/(320*L**5),
            L**5/320 - 5*L**3*x/192 + 5*L*x**2/32 - 4*x**s.Rational(5, 2)/15
            + 5*x**3/(32*L) - 5*x**4/(192*L**3) + x**5/(320*L**5),
        )
    ell = s.log(L) - s.log(x)/2
    return (
        L**4/128 - L**2*x/16 + 3*x**2*ell/16
        + x**3/(16*L**2) - x**4/(128*L**4),
        L**5/320 - L**3*x/64 + L*x**2/32 - x**3/(32*L)
        + x**4/(64*L**3) - x**5/(320*L**5),
        L**6/768 - L**4*x/256 - L**2*x**2/256 + x**3*ell/32
        + x**4/(256*L**2) + x**5/(256*L**4) - x**6/(768*L**6),
        L**6/768 - 3*L**4*x/256 + 15*L**2*x**2/256 - 5*x**3*ell/32
        - 15*x**4/(256*L**2) + 3*x**5/(256*L**4) - x**6/(768*L**6),
    )


@lru_cache(maxsize=None)
def _basis_terms(d):
    x, L = s.symbols("sigma delta", positive=True)
    result = []
    for basis in short_basis56_symbolic(d, x, L):
        terms = []
        for term in s.Add.make_args(s.expand(basis)):
            powers = term.as_powers_dict()
            power, log_power = powers.get(x, 0), powers.get(s.log(x), 0)
            coefficient = term / (x**power * s.log(x)**log_power)
            terms.append((power, log_power, s.lambdify(L, coefficient, "mpmath")))
        result.append(terms)
    return result


def _mp_exact(expr):
    return mp.mpf(str(s.N(expr, mp.dps)))


def jet_short_action56(d, angular, rho, delta, *, dps=60):
    """Finite-density QUADRATIC MODEL, with exact sharp cutoff and point term.

    Incomplete-gamma moments retain tails; differentiation supplies log moments.
    Coefficients include ordinary sphere area. This is not an actual ball action
    (even the planar 5D ball has a cubic overlap). Numerical errors uncertified.
    """
    _dimension(d)
    _positive(rho, "rho")
    _positive(delta, "delta")
    _precision(dps)
    angular = tuple(angular)
    if len(angular) != 4 or not all(mp.isfinite(x) for x in angular):
        raise ValueError("require four finite angular coefficients")
    with mp.workdps(dps):
        rho, delta = mp.mpf(rho), mp.mpf(delta)
        c = _mp_exact(interval_coefficient(d))
        point, pair = map(_mp_exact, action_constants(d))
        coefficients = [_mp_exact(kernel_polynomial(d).coeff(Z, k))
                        for k in range(d//2 + 2)]

        def moment(power):
            exponent = 2*(power+1)/d
            return (mp.mpf(2)/d * (c*rho)**(-exponent)
                    * mp.fsum(coef * mp.gammainc(exponent+k, 0, c*rho*delta**d)
                              for k, coef in enumerate(coefficients)))

        moments = {}
        contributions = []
        for amplitude, terms in zip(angular, _basis_terms(d)):
            for power, log_power, coefficient in terms:
                key = (power, log_power)
                if key not in moments:
                    order = _mp_exact(s.sympify(power))
                    moments[key] = mp.diff(moment, order) if log_power else moment(order)
                contributions.append(mp.mpf(amplitude)*coefficient(delta)*moments[key])
        return rho**(mp.mpf(2)/d)*(point*mp.mpf(angular[0])/_mp_exact(sphere_area(d))
                                   - pair*rho*mp.fsum(contributions))


def _ball_parameters(d, height, bend):
    _dimension(d)
    if not (math.isfinite(height) and math.isfinite(bend)
            and height > 0 and bend >= 0 and 2*height + bend < 1):
        raise ValueError("require height>0, bend>=0 and 2*height+bend<1")


def _unit_ball(m):
    return math.pi**(m/2)/math.gamma(1+m/2)


def ball_cos_overlap56(d, tau, spatial, *, height=0.25, bend=0.125, weight=None):
    """Actual causal overlap (S21); source weight may depend on x_1 only.

    Transverse source and time coordinates are integrated exactly. One remaining
    ordinary quadrature keeps all partners, including null displacements.
    """
    _ball_parameters(d, height, bend)
    spatial = tuple(spatial)
    if (len(spatial) != d-1 or not math.isfinite(tau)
            or not all(math.isfinite(x) for x in spatial)
            or tau < math.hypot(*spatial)):
        raise ValueError("require a finite future-causal displacement in the stated dimension")
    w = (lambda _: 1.0) if weight is None else weight

    def integrand(x):
        gap = height*(1-x*x) - tau + bend*(math.cos(x+spatial[0])-math.cos(x))
        return w(x)*max(0.0, gap)**(d/2)

    return (2*_unit_ball(d-2)/(d*height**((d-2)/2))
            * quad(integrand, -1, 1, points=[0], epsabs=2e-13,
                   epsrel=2e-13, limit=200)[0])


def ball_cos_jet56(d, *, height=0.25, bend=0.125, weight=None, weight_prime=None):
    """Actual bulk/coarea two-jet and source derivative, not a fitted target.

    The independent normal/Gram target is computed separately in the tests.
    Unaveraged fields also retain the linear spatial and mixed responses.
    """
    _ball_parameters(d, height, bend)
    w = (lambda _: 1.0) if weight is None else weight
    wp = (lambda _: 0.0) if weight is None else weight_prime
    if wp is None:
        raise ValueError("supply weight_prime with weight")
    integral = lambda f: quad(f, -1, 1, epsabs=2e-12, epsrel=2e-12)[0]
    bulk = lambda f: _unit_ball(d-2)*integral(lambda x: f(x)*(1-x*x)**((d-2)/2))
    surface = lambda f: float(sphere_area(d-1))*integral(
        lambda x: f(x)*(1-x*x)**((d-4)/2))
    p = lambda x: -bend*math.sin(x)
    volume = 2*height*_unit_ball(d-2)/d*integral(lambda x: w(x)*(1-x*x)**(d/2))
    area = bulk(w)
    gradient = bulk(lambda x: w(x)*p(x))
    hessian = bulk(lambda x: -w(x)*bend*math.cos(x))
    surf = surface(w)/(2*height)
    surf_p = surface(lambda x: w(x)*p(x))/(2*height)
    surf_pp = surface(lambda x: w(x)*p(x)**2)/(2*height)
    derivative = bulk(lambda x: wp(x)*p(x))
    sphere = float(sphere_area(d))
    angular = np.array([sphere*volume, -sphere*area, sphere*surf/2,
                        sphere*(hessian+surf_pp)/(2*(d-1))])
    return {"angular": angular, "volume": volume, "spatial_volume": area,
            "bulk_gradient": gradient, "future_hessian": hessian,
            "surface": surf, "surface_p": surf_p, "surface_pp": surf_pp,
            "partition_derivative": derivative,
            "short_coefficient": 2*(angular[2]-(d-1)*angular[3])/sphere}


def planar_short_density56(d, sigma, delta, *, height=0.25):
    """Independent fixed-time integral (S22), high-precision scalar quadrature.

    Uses the ACTUAL planar overlap, cubic in 5D and power 7/2 in 6D.
    Precision is the caller's mpmath context; no certified error is claimed.
    """
    _dimension(d)
    _positive(delta, "delta")
    _positive(height, "height")
    if height >= 0.5 or delta >= height or not mp.isfinite(sigma) or sigma < 0:
        raise ValueError("require 0<delta<height<1/2 and finite sigma>=0")
    x, L, a = mp.mpf(sigma), mp.mpf(delta), mp.mpf(height)
    if x >= L*L:
        return mp.mpf(0)
    root = mp.sqrt(x)
    length = (L-root)**2/(2*L)
    n = d-1
    ball = mp.pi**(mp.mpf(n)/2)/mp.gamma(1+mp.mpf(n)/2)
    sphere = n*ball
    scale = sphere*ball/(d+1)*a**(-mp.mpf(n)/2)

    def integrand(u):
        t = root+length*u
        return (length*u*(2*root+length*u))**(mp.mpf(d-3)/2)*(a-t)**(mp.mpf(d+1)/2)

    return scale*length*mp.quad(integrand, [0, 1])


def planar_short_action56(d, rho, delta, *, height=0.25, dps=40):
    """ACTUAL planar short action by nested quadrature, not the two-jet model.

    Integrates the finite sharp interval in a density-rescaled coordinate.
    This is a slow numerical regression, not a certified asymptotic estimate.
    """
    _dimension(d)
    _positive(rho, "rho")
    _precision(dps)
    with mp.workdps(dps):
        rho, delta, a = mp.mpf(rho), mp.mpf(delta), mp.mpf(height)
        # Validate before even the zero probe or endpoint partition.
        planar_short_density56(d, 0, delta, height=a)
        c = _mp_exact(interval_coefficient(d))
        point, pair = map(_mp_exact, action_constants(d))
        scale = (c*rho)**(mp.mpf(1)/d)
        end = scale*delta
        coefficients = [_mp_exact(kernel_polynomial(d).coeff(Z, k))
                        for k in range(d//2 + 2)]

        def integrand(u):
            z = u**d
            kernel = mp.polyval(list(reversed(coefficients)), z)*mp.exp(-z)
            return 2*u/scale**2*kernel*planar_short_density56(
                d, (u/scale)**2, delta, height=a)

        endpoints = [mp.mpf(0), *[mp.mpf(x) for x in (1, 2, 4) if x < end], end]
        pairs = mp.quad(integrand, endpoints)
        n = d-1
        ball = mp.pi**(mp.mpf(n)/2)/mp.gamma(1+mp.mpf(n)/2)
        volume = 2*ball*a/(d+1)
        return rho**(mp.mpf(2)/d)*(point*volume-pair*rho*pairs)


def check_short56_identities():
    """Finite exact regressions, not verification of the written geometric proof."""
    x, L, v, j = s.symbols("sigma delta v j", positive=True)
    tau, radius = (v+x/v)/2, (v-x/v)/2
    for d in (5, 6):
        basis = short_basis56_symbolic(d, x, L)
        jacobian = radius**(d-2)/(2*v)
        for expected, monomial in zip(basis, (1, tau, tau**2, radius**2)):
            primitive = s.integrate(s.expand(jacobian*monomial), v)
            actual = primitive.subs(v, L)-primitive.subs(v, s.sqrt(x))
            assert s.simplify(actual-expected) == 0
            assert s.simplify(expected.subs(x, L**2)) == 0
        assert s.simplify(basis[2]-basis[3]-x*basis[0]) == 0
        a, beta = action_constants(d)
        c, sphere = interval_coefficient(d), sphere_area(d)
        M = transverse_moment(d, j)
        if d == 5:
            point_response = sphere*transverse_moment(d, s.Rational(3, 2))/(3*c)
            critical = transverse_moment(d, s.Rational(5, 2))
            time_coefficient, radial_coefficient = s.Rational(1, 15), -s.Rational(4, 15)
        else:
            point_response = -3*sphere*s.diff(M, j).subs(j, 2)/(32*c)
            critical = s.diff(M, j).subs(j, 3)
            time_coefficient, radial_coefficient = -s.Rational(1, 64), s.Rational(5, 64)
        assert s.simplify(beta*point_response-a) == 0
        response = -beta*c**(-1-s.Rational(2, d))*critical
        assert s.simplify(response*time_coefficient-2/sphere) == 0
        assert s.simplify(response*radial_coefficient+2*(d-1)/sphere) == 0
    print("PASS: 5D/6D actual sharp bases, fractional/log responses and point normalization")


if __name__ == "__main__":
    check_short56_identities()
