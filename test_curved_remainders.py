"""Regression evidence for #74's route obstruction, not full-action convergence."""

import math
import unittest

from mpmath import mp
from scipy.integrate import quad
import sympy as s

import curved_remainders as cr


def _h(t, u, v):
    # Independently written midpoint/boost formula (C9), not the null helper.
    duration = (u+v)/2
    return 1 + (t+duration/2)**2 + duration**2/20 - u*v/30


def _phase(t, u, v):
    return u*v*mp.sqrt(_h(t, u, v))


def _jacobian(t, u, v):
    h = _h(t, u, v)
    hu = t/2 + 3*u/20 + 7*v/60
    return v*(2*h+u*hu)/(2*mp.sqrt(h))


def _kernel(z):
    return (1-9*z+8*z*z-4*z**3/3)*math.exp(-z)


def _inverse(t, v, w):
    if not w:
        return mp.mpf(0)
    return mp.findroot(lambda u: _phase(t, u, v)-w,
                       w/(v*mp.sqrt(_h(t, 0, v))))


def _amplitude(t, w, delta, top):
    """Actual complete inner long fibre, including all directions."""
    length = 2*(top-t)
    a = length-delta
    if a <= 0 or w >= _phase(t, a, delta):
        return mp.mpf(0)
    root = length if not w else mp.findroot(
        lambda v: _phase(t, length-v, v)-w,
        length-w/(length*mp.sqrt(_h(t, 0, length))))

    def integrand(v):
        u = _inverse(t, v, w)
        return (1+(t+(u+v)/2)**2)*(v-u)**2/(8*_jacobian(t, u, v))

    return 4*mp.pi*mp.quad(integrand, [delta, root])


def _pair_triangle(rho, t, delta, top):
    """Actual signed long pair integral in a fixed unit-triangle quadrature.

    0<a<delta.  Direct coordinates, no inverse phase or model amplitude.
    """
    a = 2*(top-t)-delta

    def integrand(r, z):
        v, u = delta+a*r, a*z
        argument = (math.pi/24)*rho*(u*v)**2*_h(t, u, v)
        return (1+(t+(u+v)/2)**2)*(v-u)**2*_kernel(argument)

    integral = quad(lambda r: quad(lambda z: integrand(r, z), 0, 1-r,
                                  epsabs=1e-16)[0], 0, 1, epsabs=1e-16)[0]
    return math.pi*a*a*integral/2


class CurvedRemainderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        t, u, v = s.symbols("t u v", real=True)
        amplitude = cr.endpoint_amplitude(t, u, v)
        jacobian = cr.phase_jacobian(t, u, v)
        aw = s.diff(amplitude, u)/jacobian
        aww = s.diff(aw, u)/jacobian
        expressions = (amplitude, aw, aww, s.diff(amplitude, v))
        cls.amplitude_derivatives = [s.lambdify((t, v), e.subs(u, 0), "mpmath")
                                     for e in expressions]

    def _active_jet(self, t, delta, top):
        length = 2*(top-t)
        a0, aw, aww, av = self.amplitude_derivatives
        j = _jacobian(t, 0, length)
        r1 = -1/j
        # Invert w=F(t,L-v,v) at v=L.  This retains root acceleration.
        phi2 = mp.diff(lambda v: _phase(t, length-v, v), length, 2)
        r2 = phi2/j**3
        integrals = [mp.quad(lambda v: f(t, v), [delta, length])
                     for f in (a0, aw, aww)]
        b0, b1, b2 = cr.moving_integral_jet(*integrals, a0(t, length),
                                          aw(t, length), av(t, length), r1, r2)
        return tuple(4*mp.pi*mp.mpf(str(b)) for b in (b0, b1, b2))

    def test_exact_certificates(self):
        cr.check_curved_remainder_identities()

    def test_global_phase_monotonicity_and_inverse(self):
        with mp.workdps(35):
            # Includes t outside the example's slab: the SOS proof is global.
            for t in map(mp.mpf, (-10, -1, 0, 2)):
                for v in map(mp.mpf, (".01", ".5", "3")):
                    for u in (0, v/3, v):
                        self.assertGreaterEqual(_h(t, u, v), 1)
                        self.assertGreaterEqual(_jacobian(t, u, v), v/mp.sqrt(_h(t, u, v)))
                        w = _phase(t, u, v)
                        self.assertLess(abs(_inverse(t, v, w)-u), mp.mpf("1e-30"))
                        self.assertLess(abs(mp.diff(lambda z: _phase(t, z, v), u)
                                            - _jacobian(t, u, v)), mp.mpf("1e-30"))

    def test_both_measures_and_jacobian_are_not_optional(self):
        t, u, v = map(s.Rational, ("1/16", "1/128", "1/16"))
        inner = cr.endpoint_amplitude(t, u, v)*cr.phase_jacobian(t, u, v)
        raw = (1+t*t)*(1+(t+(u+v)/2)**2)*(v-u)**2/8
        self.assertEqual(s.simplify((1+t*t)*inner-raw), 0)
        self.assertNotEqual(s.simplify(inner-raw), 0)
        self.assertNotEqual(s.simplify((1+t*t)*(v-u)**2/8-raw), 0)
        # Freezing H at the first endpoint does not give the same phase.
        self.assertNotEqual(s.simplify(cr.phase(t, u, v)**2-(u*v)**2*(1+t*t)), 0)

    def test_moving_contact_terms_and_half_factor(self):
        w, v = s.symbols("w v", real=True)
        delta = s.Rational(1, 3)
        root = 2-w+3*w*w/2
        amplitude = 1+2*v+v*v+w*(3+v)+5*w*w
        integral = s.integrate(amplitude, (v, delta, root))
        a0 = amplitude.subs(w, 0)
        aw = s.diff(amplitude, w).subs(w, 0)
        aww = s.diff(amplitude, w, 2).subs(w, 0)
        interior = [s.integrate(f, (v, delta, 2)) for f in (a0, aw, aww)]
        jet = cr.moving_integral_jet(*interior, a0.subs(v, 2), aw.subs(v, 2),
                                     s.diff(a0, v).subs(v, 2), -1, 3)
        for k, actual in enumerate(jet):
            self.assertEqual(actual, s.diff(integral, w, k).subs(w, 0)/s.factorial(k))
        self.assertNotEqual(jet[1], interior[1])
        self.assertNotEqual(jet[2], interior[2]/2)

    def test_actual_active_jet_and_exact_contact(self):
        with mp.workdps(40):
            top, delta = mp.mpf(1)/8, mp.mpf(1)/32
            a = delta/4
            t = top-(delta+a)/2
            b0, b1, b2 = self._active_jet(t, delta, top)
            self.assertLess(abs(b0-_amplitude(t, 0, delta, top)), mp.mpf("1e-35"))
            errors = []
            for w in (mp.mpf("1e-8"), mp.mpf("5e-9")):
                remainder = _amplitude(t, w, delta, top)-b0-b1*w-b2*w*w
                errors.append(abs(remainder)/w**2)
            self.assertLess(errors[1], errors[0]*mp.mpf(".51"))
            contact = top-delta/2
            self.assertEqual(_amplitude(contact, 0, delta, top), 0)
            self.assertEqual(_amplitude(contact, mp.mpf("1e-8"), delta, top), 0)
            # The active formula is not the right jet at exact contact.
            a0 = self.amplitude_derivatives[0]
            self.assertNotEqual(-4*mp.pi*a0(contact, delta)/_jacobian(contact, 0, delta), 0)

    def test_actual_phase_pushforward_against_signed_pair_integral(self):
        with mp.workdps(25):
            top, delta = mp.mpf(1)/8, mp.mpf(1)/32
            a = delta/4
            t = top-(delta+a)/2
            end = _phase(t, a, delta)
            rho = mp.mpf("1e8")

            def integrand(z):
                w = end*z
                argument = mp.pi/24*rho*w*w
                kernel = (1-9*argument+8*argument**2-4*argument**3/3)*mp.exp(-argument)
                return end*kernel*_amplitude(t, w, delta, top)

            pushed = mp.quad(integrand, [0, mp.mpf(".5"), 1])
            direct = _pair_triangle(float(rho), float(t), float(delta), float(top))
            self.assertAlmostEqual(float(pushed)/direct, 1, delta=2e-11)
            # This probe includes negative as well as positive kernel values.
            self.assertLess(_kernel(float(mp.pi/24*rho*end*end)), 0)

    def test_averaging_retains_the_quadratic_contact_coefficient(self):
        a, bound, beta, w = s.symbols("a A beta w", positive=True)
        # For beta*w<A, split at the moving contact rather than differentiating
        # the old active integrand alone.  This is a toy identity, not geometry.
        actual = s.integrate(a-beta*w, (a, beta*w, bound))
        expected = bound**2/2-bound*beta*w+beta**2*w*w/2
        self.assertEqual(s.expand(actual-expected), 0)
        frozen_active_set = s.integrate(a-beta*w, (a, 0, bound))
        self.assertEqual(s.expand(actual-frozen_active_set), beta**2*w*w/2)

    def test_no_integrable_first_endpoint_quadratic_remainder_bound(self):
        with mp.workdps(40):
            top, delta = mp.mpf(1)/8, mp.mpf(1)/32
            kstar, astar = cr.planar_contact_scale(s.Rational(1, 8), s.Rational(1, 32))
            kstar, astar = (mp.mpf(str(s.N(x, 42))) for x in (kstar, astar))
            target = astar/(4*kstar*kstar)
            errors = []
            for divisor in (64, 256, 1024):
                a = delta/divisor
                t = top-(delta+a)/2
                w = 2*kstar*a
                self.assertGreater(w, _phase(t, a, delta))
                b0, b1, b2 = self._active_jet(t, delta, top)
                residual = _amplitude(t, w, delta, top)-b0-b1*w-b2*w*w
                self.assertGreater(residual, 0)
                scaled = a*residual/(w*w)
                errors.append(abs(scaled/target-1))
            self.assertLess(errors[-1], mp.mpf(".004"))
            self.assertLess(errors[-1], errors[0]/10)

    def test_actual_signed_obstruction_not_absolute_kernel_only(self):
        top, delta, eps, c, C, Q = 1/8, 1/32, 1/100, math.pi/24, 4/math.sqrt(6), 2
        lower_constant = C*math.pi*eps**1.5/(27*c**1.5*Q**1.5*delta)
        values = []
        for divisor in (4, 16, 64, 256):
            a = delta/divisor
            t = top-(delta+a)/2
            rho = float(cr.obstruction_density(a, delta))
            self.assertLessEqual(c*rho*(a*(delta+a))**2*Q, eps*(1+1e-14))
            integral = _pair_triangle(rho, t, delta, top)
            volume = float(cr.planar_long_coordinate_volume(a, delta))
            self.assertGreaterEqual(integral, volume/2)
            normalized = C*rho**1.5*integral
            self.assertGreater(normalized, lower_constant/a)
            values.append(normalized)
            # All first endpoints in a positive spatial ball are in the
            # original region, not just a null line or a single endpoint.
            self.assertGreater(t, (1/4)**2/4-1/8)
            self.assertLess(t, top)
            for u, v in ((0, delta), (a, delta), (0, delta+a)):
                ytime = t+(u+v)/2
                radius = 1/4+(v-u)/2
                self.assertGreater(ytime, radius*radius/4-1/8)
        for earlier, later in zip(values, values[1:]):
            self.assertGreater(later/earlier, 3.8)

    def test_exact_short_long_accounting_in_original_coordinates(self):
        top, delta = 1/8, 1/32
        t = top-5*delta/8  # L=5*delta/4, so the sharp contact is present.
        rho, c, C = 1e8, math.pi/24, 4/math.sqrt(6)
        length = 2*(top-t)

        def uv(u, v):
            argument = c*rho*(u*v)**2*_h(t, u, v)
            return math.pi/2*(v-u)**2*(1+(t+(u+v)/2)**2)*_kernel(argument)

        short = quad(lambda v: quad(lambda u: uv(u, v), 0, min(v, length-v),
                                    epsabs=1e-18)[0], 0, delta,
                     points=[length/2], epsabs=1e-18)[0]
        long = _pair_triangle(rho, t, delta, top)

        def tr(T, r):
            sigma = T*T-r*r
            h = 1+(t+T/2)**2+T*T/20-sigma/30
            return 4*math.pi*r*r*(1+(t+T)**2)*_kernel(c*rho*sigma*sigma*h)

        unsplit = quad(lambda T: quad(lambda r: tr(T, r), 0, T,
                                      epsabs=1e-18)[0], 0, top-t, epsabs=1e-18)[0]
        self.assertAlmostEqual((short+long)/unsplit, 1, delta=2e-11)
        outer_q = 1+t*t
        full = outer_q*C*math.sqrt(rho)*(1-rho*unsplit)
        short_action = outer_q*C*math.sqrt(rho)*(1-rho*short)
        long_action = -outer_q*C*rho**1.5*long
        self.assertAlmostEqual(full, short_action+long_action, delta=2e-9)
        # Finite signed first-endpoint weights do not restrict any partners.
        weights = (-0.25, 0.5, 0.75)
        self.assertAlmostEqual(sum(w*(short_action+long_action) for w in weights),
                               full, delta=2e-9)


if __name__ == "__main__":
    unittest.main()
