"""Independent diagnostics for #73; none is a full curved-action limit test."""

import math
import unittest

from mpmath import mp
from scipy.integrate import quad
import sympy as s

import calculations
import curved_bulk_pilot as cb


def _kernel(z):
    return (1 - 9 * z + 8 * z**2 - mp.mpf(4) * z**3 / 3) * mp.exp(-z)


def _boosted_interval_quadrature(t, duration, radius, b):
    """Integrate the actual density over rest-frame spatial balls, then boost.

    The time coordinate after the boost is midpoint + gamma*w + gamma*beta*z1.
    The z1^2 integral is 4*pi*R^5/15.  No interval-factor formula is used.
    """
    tau = math.sqrt(duration**2 - radius**2)
    gamma = duration / tau
    gamma_beta = radius / tau
    midpoint = t + duration / 2

    def integrand(w):
        ball_radius = tau / 2 - abs(w)
        return (4 * math.pi * ball_radius**3 / 3 * (1 + b * (midpoint + gamma * w)**2)
                + b * gamma_beta**2 * 4 * math.pi * ball_radius**5 / 15)

    return quad(integrand, -tau / 2, tau / 2, points=[0], epsabs=1e-20, epsrel=2e-12)[0]


class CurvedBulkPilotTests(unittest.TestCase):
    def test_exact_symbolic_checks(self):
        cb.check_curved_pilot_identities()

    def test_scalar_domains(self):
        for order in (-2, -1, s.I):
            with self.assertRaises(ValueError):
                cb.transverse_moment(order)
        for order in (-1, 0.5, True):
            with self.assertRaises(ValueError):
                cb.kernel_derivative_polynomial(order)

    def test_original_signed_kernel(self):
        with mp.workdps(40):
            for z in map(mp.mpf, ("0", ".1", ".5", "2", "7")):
                self.assertAlmostEqual(float(_kernel(z)), float(calculations.kernel(z)), places=14)
            self.assertLess(_kernel(mp.mpf(".2")), 0)
        self.assertEqual(s.simplify(cb.KERNEL.subs(cb.Z, 0)), 1)

    def test_rest_diamond_second_moments(self):
        # Independent ball integrals determine all coefficients of (C6).
        t, tau = s.symbols("t tau", positive=True)
        radius = tau / 2 - t
        volume = 2 * s.integrate(4 * s.pi * radius**3 / 3, (t, 0, tau / 2))
        time_moment = 2 * s.integrate(t**2 * 4 * s.pi * radius**3 / 3, (t, 0, tau / 2))
        spatial_moment = 2 * s.integrate(4 * s.pi * radius**5 / 15, (t, 0, tau / 2))
        self.assertEqual(s.simplify(volume), s.pi * tau**4 / 24)
        self.assertEqual(s.simplify(time_moment / volume), tau**2 / 60)
        self.assertEqual(s.simplify(spatial_moment / volume), tau**2 / 30)

    def test_actual_interval_against_boosted_volume_quadrature(self):
        for t in (-0.12, 0, 0.07):
            for duration, radius in ((0.1, 0), (0.2, 0.13), (0.1, 0.0999)):
                for b in (0, 1, 3):
                    actual = _boosted_interval_quadrature(t, duration, radius, b)
                    expected = float(cb.interval_volume(t, duration, radius, b))
                    self.assertAlmostEqual(actual / expected, 1, delta=2e-11)

    def test_null_diagonal_and_flat_calibrations(self):
        t, T, r = s.symbols("t T r", real=True)
        self.assertEqual(cb.interval_volume(t, T, T), 0)
        self.assertEqual(cb.interval_volume(t, 0, 0), 0)
        self.assertEqual(cb.interval_volume(t, T, r, 0), s.pi * (T**2 - r**2)**2 / 24)
        self.assertEqual(cb.scalar_curvature(t, 0), 0)
        # Both endpoint measures are needed for the a^2 action scaling.
        scale, rho = s.symbols("scale rho", positive=True)
        volume, pair = s.symbols("volume pair", real=True)
        curved = cb.ACTION_CONSTANT * s.sqrt(rho) * (scale**4 * volume - rho * scale**8 * pair)
        flat_at_scaled_density = cb.ACTION_CONSTANT * s.sqrt(rho * scale**4) * (volume - rho * scale**4 * pair)
        self.assertEqual(s.simplify(curved - scale**2 * flat_at_scaled_density), 0)
        wrong_one_endpoint = cb.ACTION_CONSTANT * s.sqrt(rho) * (scale**4 * volume - rho * scale**4 * pair)
        self.assertNotEqual(s.simplify(curved - wrong_one_endpoint), 0)

    def test_curvature_from_connection_not_action(self):
        t = s.Symbol("t", real=True)
        sigma = s.Function("sigma")(t)
        eta = (1, -1, -1, -1)
        # Christoffel symbols of exp(2*sigma(t))*diag(1,-1,-1,-1).
        def gamma(a, b, c):
            coefficient = (int(a == b) * int(c == 0) + int(a == c) * int(b == 0)
                           - int(b == c) * eta[b] * eta[a] * int(a == 0))
            return coefficient * s.diff(sigma, t)

        def partial(expr, index):
            return s.diff(expr, t) if index == 0 else s.Integer(0)

        ricci = s.Matrix(4, 4, lambda b, n: s.simplify(sum(
            partial(gamma(a, a, b), n) - partial(gamma(a, n, b), a)
            + sum(gamma(a, n, k) * gamma(k, a, b)
                  - gamma(a, a, k) * gamma(k, n, b) for k in range(4))
            for a in range(4))))
        self.assertEqual(ricci[0, 0], 3 * s.diff(sigma, t, 2))
        for i in range(1, 4):
            self.assertEqual(s.simplify(ricci[i, i] + s.diff(sigma, t, 2)
                                       + 2 * s.diff(sigma, t)**2), 0)
        for i in range(4):
            for j in range(4):
                if i != j:
                    self.assertEqual(ricci[i, j], 0)
        scalar = s.exp(-2 * sigma) * sum(eta[i] * ricci[i, i] for i in range(4))
        b = s.Symbol("b", positive=True)
        concrete = scalar.subs(sigma, s.log(1 + b * t**2) / 4).doit()
        self.assertEqual(s.simplify(concrete - cb.scalar_curvature(t, b)), 0)
        self.assertEqual(cb.scalar_curvature(0, b), 3 * b)
        for time in (-s.Rational(1, 8), 0, s.Rational(1, 8)):
            self.assertGreater(cb.scalar_curvature(time), 0)

    def test_invariant_rest_remainder_bounds(self):
        with mp.workdps(40):
            for b, duration in ((1, mp.mpf(".1")), (1, mp.mpf(".8")), (4, mp.mpf(".4"))):
                e = b * duration**2
                tau = mp.quad(lambda t: (1 + b * t*t)**mp.mpf(".25"),
                              [-duration/2, 0, duration/2])
                self.assertLessEqual(abs(tau/duration - 1 - e/48), 3*e**2/2560)
                actual_ratio = (1 + e/60) * (duration/tau)**4
                self.assertLessEqual(abs(actual_ratio - 1 + e/15), e**2)

    def test_radial_primitives_actual_fixed_v_cutoff(self):
        for delta in (0.2, 1.0):
            for fraction in (0.001, 0.1, 0.8):
                sigma = fraction * delta**2
                upper = (delta + sigma/delta)/2
                for order, expected in enumerate(cb.radial_primitives(sigma, delta)):
                    actual = quad(lambda t: t**order * math.sqrt(max(0, t*t - sigma)),
                                  math.sqrt(sigma), upper, epsabs=1e-14)[0]
                    self.assertAlmostEqual(actual, float(expected), delta=2e-12)
        sigma, delta = s.symbols("sigma delta", positive=True)
        for primitive in cb.radial_primitives(sigma, delta):
            self.assertEqual(s.simplify(primitive.subs(sigma, delta**2)), 0)

    def test_log_moments_and_kernel_derivative_responses_by_quadrature(self):
        with mp.workdps(45):
            for order in range(4):
                value = mp.quad(lambda w: w**order * _kernel(w*w), [0, 1, 3, 12])
                self.assertLess(abs(value - mp.mpf(str(cb.transverse_moment(order)))), mp.mpf("1e-35"))
            for k, multiplier in enumerate((1, -mp.mpf(3)/2, mp.mpf(15)/4)):
                polynomial = cb.kernel_derivative_polynomial(k)
                coefficients = [mp.mpf(str(polynomial.coeff(cb.Z, j))) for j in range(4)]
                derivative = lambda z: mp.polyval(list(reversed(coefficients)), z) * mp.exp(-z)
                value = mp.quad(lambda w: w**2 * mp.log(w) * w**(2*k) * derivative(w*w),
                                [0, 1, 3, 12])
                self.assertLess(abs(value + multiplier * mp.sqrt(mp.pi)/12), mp.mpf("1e-34"))

    def test_endpoint_derivatives_and_gradient_squared_are_not_optional(self):
        q = s.Symbol("q", positive=True)
        q1, q2 = s.symbols("q1 q2", real=True)
        response = cb.second_jet_response(q, q1, q2)
        self.assertEqual(s.simplify(response - 3*q2/(4*q**s.Rational(3, 2))
                                   + 9*q1**2/(16*q**s.Rational(5, 2))), 0)
        self.assertNotEqual(cb.second_jet_response(1, 1, 0), 0)
        self.assertEqual(cb.second_jet_response(1, 0, 2), s.Rational(3, 2))
        # Flat phi=t^2 and phi=x1^2 at x=0 must give +2 and -2, not zero.
        self.assertEqual(cb.second_jet_response(1, 0, 0, phi=0, phi_tt=2), 2)
        self.assertEqual(cb.second_jet_response(1, 0, 0, phi=0, spatial_laplacian=2), -2)
        self.assertEqual(cb.second_jet_response(4, 8, 0, phi=0, phi_t=1), s.Rational(1, 2))
        # Independently evaluate Box_g via its divergence expression.
        t = s.Symbol("t", real=True)
        density = 1 + t*t
        field = t**3 + t
        box = s.diff(s.sqrt(density) * s.diff(field, t), t) / density
        actual = cb.second_jet_response(density, s.diff(density, t), s.diff(density, t, 2),
                                        field, s.diff(field, t), s.diff(field, t, 2))
        self.assertEqual(s.simplify(actual - box - cb.scalar_curvature(t)*field/2), 0)

    def test_jet_model_finite_density_quadrature(self):
        # Integrate (C11) on the actual finite v-cutoff using (C12), without
        # calling the Mellin/log-response helper. This is NOT the full action.
        with mp.workdps(45):
            c, C, delta = mp.pi/24, 4/mp.sqrt(6), mp.mpf(1)/32
            kp = lambda z: (-10+25*z-12*z*z+4*z**3/3)*mp.exp(-z)
            kpp = lambda z: (35-49*z+16*z*z-4*z**3/3)*mp.exp(-z)
            for t in (mp.mpf(0), mp.mpf(1)/16):
                q = 1+t*t
                a, d = 2*t/q, 2/q
                target = mp.mpf(3)/2*(1-t*t/2)/q**mp.mpf("2.5")
                errors = []
                for rho in (mp.mpf("1e12"), mp.mpf("1e14")):
                    scale = mp.sqrt(c*rho*q)

                    def integrand(w):
                        sigma, z = w/scale, w*w
                        logarithm = mp.log(sigma/delta**2)
                        j0 = (delta**2-sigma**2/delta**2)/8+sigma*logarithm/4
                        j1 = (delta-sigma/delta)**3/24
                        j2 = (delta**4-sigma**4/delta**4)/64+sigma**2*logarithm/16
                        return (a*j1*(_kernel(z)+z*kp(z)/2)
                                + d*(j2*_kernel(z)/2+z*(3*j2/20-sigma*j0/60)*kp(z))
                                + a*a*j2*(z*kp(z)/2+z*z*kpp(z)/8))

                    # All polynomial-Gaussian tails beyond 15 are negligible
                    # at this precision; the coordinate cutoff is much larger.
                    self.assertGreater(delta**2*scale, 15)
                    pair_correction = 2*mp.pi*q/scale*mp.quad(integrand, [0, 1, 3, 15])
                    flat_response = C*mp.sqrt(rho)*mp.exp(-c*rho*q*delta**4)
                    value = flat_response-C*rho**mp.mpf("1.5")*pair_correction
                    errors.append(abs(value-target))
                self.assertLess(errors[1], mp.mpf(".0004"))
                self.assertLess(errors[1], errors[0]/5)

    def test_derivative_envelopes_and_kernel_taylor_remainder(self):
        for k in range(4):
            derivative = s.lambdify(cb.Z, cb.kernel_derivative_polynomial(k)*s.exp(-cb.Z), "math")
            for z in (0, 0.1, 1, 4, 10):
                envelope = float(cb.derivative_envelope(k, z))
                for fraction in (0.5, 0.8, 1, 1.3, 1.5):
                    self.assertLessEqual(abs(derivative(fraction*z)), envelope + 1e-12)
        # Explicit (C15), with the cross term E1*E2 and E2^2 retained.
        t, delta = 0.1, 0.05
        q = 1+t*t
        a, d = 2*t/q, 2/q
        c1, c2 = abs(a)/2, abs(d)/6
        self.assertLess(c1*delta+c2*delta**2, 0.5)
        derivatives = [s.lambdify(cb.Z, cb.kernel_derivative_polynomial(k)*s.exp(-cb.Z), "math")
                       for k in range(3)]
        for T in (0.01, delta):
            for radius in (0, T*0.99):
                sigma = T*T-radius*radius
                e1, e2 = a*T/2, d*(3*T*T/20-sigma/60)
                for z in (0.1, 1, 5):
                    model = (derivatives[0](z) + z*(e1+e2)*derivatives[1](z)
                             + z*z*e1*e1*derivatives[2](z)/2)
                    remainder = abs(derivatives[0](z*(1+e1+e2)) - model)
                    bound = T**3 * ((c1+c2*delta)**3*z**3*float(cb.derivative_envelope(3, z))/6
                                     + (c1*c2+c2*c2*delta/2)*z*z*float(cb.derivative_envelope(2, z)))
                    self.assertLessEqual(remainder, bound + 1e-14)

    def test_macroscopic_null_phase_does_not_freeze(self):
        u = s.Symbol("u", nonnegative=True)
        v, b, alpha = s.symbols("v b alpha", positive=True)
        factor = cb.null_phase_factor(0, u, v, b)
        self.assertEqual(s.simplify(factor.subs(u, 0)-1), 3*b*v*v/40)
        # Along u=alpha/sqrt(rho), rho*V has this non-flat limit.
        rho = s.Symbol("rho", positive=True)
        scaled_phase = cb.INTERVAL_CONSTANT*alpha**2*v**2*factor.subs(u, alpha/s.sqrt(rho))
        limit = s.limit(scaled_phase, rho, s.oo)
        self.assertEqual(s.simplify(limit-cb.INTERVAL_CONSTANT*alpha**2*v**2*(1+3*b*v*v/40)), 0)
        self.assertEqual(s.limit((factor-1)/(u*v), u, 0, dir="+"), s.oo)

    def test_positive_measure_absolute_obstruction_constants(self):
        beta, v0, v1 = 1/64, 1/16, 1/8
        self.assertLess(2*float(cb.INTERVAL_CONSTANT)*beta**2*v1**2, 1/100)
        # Analytic lower envelope P(z)>=1-9z-(4/3)z^3, exp(-z)>=1-z.
        endpoint = s.Rational(1, 100)
        lower = (1-9*endpoint-s.Rational(4, 3)*endpoint**3)*(1-endpoint)
        self.assertGreater(lower, s.Rational(1, 2))
        for x_time in (-beta, beta):
            for v in (v0, v1):
                for u in (0, beta):
                    y_time = x_time+(u+v)/2
                    spatial_bound = beta+(v-u)/2
                    self.assertLess(y_time, 1/8)
                    self.assertGreater(y_time, spatial_bound**2/4-1/8)
                    self.assertGreater(x_time, beta**2/4-1/8)
                    self.assertGreaterEqual((v-u)**2/8, (v0-beta)**2/8)
        ball_volume = math.pi**2*beta**4/2
        constant = float(cb.ACTION_CONSTANT)*ball_volume*4*math.pi*(v1-v0)*(v0-beta)**2/8*beta/4
        self.assertGreater(constant, 0)

    def test_signed_remainder_estimate_after_full_normalization(self):
        # Scalar regression for the proof of (C25), B(w)=exp(-w).
        # Its third derivative is bounded by 1. No boundary indicators here.
        with mp.workdps(45):
            c, C = mp.pi/24, 4/mp.sqrt(6)
            errors = []
            for rho in map(mp.mpf, (100, 1000, 10000)):
                scale = mp.sqrt(c*rho)
                remainder = lambda z: mp.expm1(-z/scale)+z/scale-z*z/(2*scale*scale)
                actual = C*rho/mp.sqrt(c)*mp.quad(lambda z: _kernel(z*z)*remainder(z),
                                                [0, 1, 3, 12])
                bound = 99*C/(12*c*c*mp.sqrt(rho))
                self.assertLess(abs(actual), bound)
                errors.append(abs(actual))
            self.assertGreater(errors[0], errors[1])
            self.assertGreater(errors[1], errors[2])


if __name__ == "__main__":
    unittest.main()
