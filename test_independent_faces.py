"""Regressions for #85's geometry/obstruction package, NOT a limit proof.

See notes/independent-face-extension.md. Helpers below describe only the fixed
symmetric capsule; they are not an arbitrary-region admissibility checker or a
new implementation of the BDG action/Poisson law.
"""

import math
import unittest

import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq


def envelope(x, slope):
    """Upper causal envelope; the lower envelope is its negative."""
    return slope * max(0.0, 1.0 - np.dot(x, x)) / 2


def vertical_overlap(x, b, tau, slope):
    """Direct interval intersection, without assuming any causal gap formula."""
    upper_x = envelope(x, slope)
    upper_y = envelope(x + b, slope)
    return max(0.0, min(upper_x, upper_y - tau)
               - max(-upper_x, -upper_y - tau))


def capsule_overlap_quadrature(tau, distance, slope):
    """Integrate actual vertical intersections in source-ball coordinates.

    Spatial measure is pi * d(perpendicular radius squared) * d(axial x).
    Breakpoints only help quadrature at the clipping/overlap hinges.
    """
    b = np.array([distance, 0.0, 0.0])

    def axial_integral(u):
        max_q = max(0.0, 1 - u * u)
        if max_q == 0:
            return 0.0
        candidate_points = [1 - (u + distance)**2,
                            1 - u*u - u*distance - distance**2/2 - tau/slope]
        points = sorted({q for q in candidate_points if 0 < q < max_q})
        value, _ = quad(lambda q: vertical_overlap(
            np.array([u, math.sqrt(q), 0.0]), b, tau, slope),
            0, max_q, points=points, epsabs=1e-11, epsrel=1e-11)
        return math.pi * value

    radius = math.sqrt(max(0.0, 1 - tau/slope - distance**2/4))
    points = sorted({u for u in [-distance/2 - radius, -distance/2 + radius,
                                1 - distance]
                     if -1 < u < 1})
    value, _ = quad(axial_integral, -1, 1, points=points,
                    epsabs=1e-10, epsrel=1e-10)
    return value


class IndependentFaceTests(unittest.TestCase):
    def test_separate_envelopes_allow_steep_height_and_critical_point(self):
        slope = sp.Rational(3, 4)
        r = sp.symbols("r", real=True)
        raw_upper = slope * (1 - r*r) / 2
        height = 2 * raw_upper
        self.assertEqual(sp.diff(height, r).subs(r, 0), 0)
        self.assertGreater(height.subs(r, 0), 0)
        self.assertEqual(abs(sp.diff(raw_upper, r).subs(r, 1)), slope)
        self.assertEqual(abs(sp.diff(height, r).subs(r, 1)), sp.Rational(3, 2))
        # The raw germ must NOT be replaced by the clipped envelope outside K.
        self.assertLess(raw_upper.subs(r, 2), 0)
        self.assertEqual(envelope(np.array([2., 0., 0.]), float(slope)), 0)
        # Clipping creates a derivative jump at the joint, not a smooth envelope.
        self.assertNotEqual(sp.diff(raw_upper, r).subs(r, 1), 0)
        rng = np.random.default_rng(85)
        for x, y in rng.uniform(-1.5, 1.5, (100, 2, 3)):
            difference = abs(envelope(x, float(slope)) - envelope(y, float(slope)))
            self.assertLessEqual(difference, float(slope) * np.linalg.norm(y-x) + 1e-14)

    def test_induced_gram_and_normal_coefficient_with_tangential_slope(self):
        a, b, c, k = sp.symbols("a b c k", real=True)
        p = sp.Matrix([a, b, c])
        g = sp.Matrix([0, 0, k])
        metric = sp.diag(1, -1, -1, -1)
        tangents = sp.Matrix([[a, b], [1, 0], [0, 1], [0, 0]])
        gram = -tangents.T * metric * tangents
        j_squared = sp.factor(gram.det())
        self.assertEqual(j_squared, 1 - a*a - b*b)
        future_norm_squared = 1 - p.dot(p)
        past_norm_squared = 1 - (p-g).dot(p-g)
        numerator = 1 - p.dot(p) + p.dot(g)
        self.assertEqual(sp.expand(numerator**2
                                  - future_norm_squared * past_norm_squared
                                  - k*k*j_squared), 0)
        data = {a: sp.Rational(1, 5), b: 0,
                c: sp.Rational(3, 5), k: sp.Rational(6, 5)}
        self.assertGreater(future_norm_squared.subs(data), 0)
        self.assertGreater(past_norm_squared.subs(data), 0)
        self.assertGreater(numerator.subs(data), 0)
        cosh_squared = (numerator**2 / (future_norm_squared * past_norm_squared)).subs(data)
        self.assertGreater(cosh_squared, 1)
        weight_times_area_squared = sp.cancel(cosh_squared / (cosh_squared - 1)
                                             * j_squared.subs(data))
        self.assertEqual(weight_times_area_squared, (numerator/k).subs(data)**2)
        euclidean_gram = tangents.T * tangents
        self.assertNotEqual(euclidean_gram.det().subs(data), j_squared.subs(data))

    def test_capsule_independent_area_volume_and_variable_angle_member(self):
        slope = sp.Rational(3, 4)
        r = sp.symbols("r", real=True)
        volume = 4 * sp.pi * sp.integrate(slope * (1-r*r)*r*r, (r, 0, 1))
        self.assertEqual(volume, 2 * sp.pi / 5)
        # Joint is at t=0: Lorentzian induced area is ordinary sphere area.
        cosh_angle = (1 + slope*slope) / (1 - slope*slope)
        weight = sp.simplify(cosh_angle / sp.sqrt(cosh_angle**2 - 1))
        self.assertEqual(weight, sp.Rational(25, 24))
        self.assertEqual(4 * sp.pi * weight, 25 * sp.pi / 6)
        # Symmetric unequal-axis capsule: both envelope constants <=3/4,
        # yet joint weights vary. No constant-angle restriction is introduced.
        weights = []
        for axis in [1, 2, 3]:
            local_slope = slope / axis
            self.assertLess(local_slope, 1)
            weights.append((1 + local_slope**2) / (2 * local_slope))
        self.assertEqual(weights[0], sp.Rational(25, 24))
        self.assertEqual(weights[-1], sp.Rational(17, 8))
        self.assertEqual(len(set(weights)), 3)

    def test_planar_reference_has_explicit_interval_containment_failure(self):
        R = sp.Rational
        slope = R(3, 4)
        a = (R(-41, 128), R(3, 4))
        z = (R(-25, 128), R(7, 8))
        b = (R(-1, 8), R(7, 8))

        def in_reference(point):
            t, x = point
            return -slope * (1-x*x) < t < 0

        self.assertTrue(in_reference(a))
        self.assertTrue(in_reference(b))
        self.assertFalse(in_reference(z))
        self.assertEqual(z[0] - a[0], abs(z[1] - a[1]))
        self.assertGreater(b[0] - z[0], abs(b[1] - z[1]))
        self.assertEqual(-slope * (1-z[1]**2) - z[0], R(5, 256))

    def test_planar_gap_formula_fails_at_arbitrarily_short_null_displacement(self):
        R = sp.Rational
        tau = sp.symbols("tau", positive=True)
        slope, x = R(3, 4), R(3, 4)
        height_x = slope * (1-x*x)
        height_y = slope * (1-(x+tau)**2)
        difference = sp.expand(height_x - tau - height_y)
        self.assertEqual(difference, tau/8 + 3*tau*tau/4)
        for step in [R(1, 8), R(1, 100), R(1, 10000)]:
            proposed = height_x - step
            actual = height_y.subs(tau, step)
            self.assertGreater(actual, 0)
            self.assertGreater(proposed, actual)
        self.assertEqual((height_x-tau).subs(tau, R(1, 8)), R(13, 64))
        self.assertEqual(height_y.subs(tau, R(1, 8)), R(45, 256))
        # The formula is not merely unavailable as a theorem: direct source /
        # shifted-partner interval intersection produces the smaller number.
        tau0 = R(1, 8)
        intersection = min(0, -tau0) - max(-height_x,
                                           -height_y.subs(tau, tau0) - tau0)
        self.assertEqual(intersection, R(45, 256))
        # A strict timelike displacement also fails; this is not confined to
        # the null displacement set discarded by volume integration.
        timelike_tau = R(9, 64)
        self.assertGreater(timelike_tau, tau0)
        actual_timelike = min(0, -timelike_tau) - max(
            -height_x, -height_y.subs(tau, tau0) - timelike_tau)
        self.assertEqual(actual_timelike, R(45, 256))
        self.assertEqual(height_x - timelike_tau - actual_timelike, R(3, 256))

    def test_actual_envelope_gap_equals_direct_intersections(self):
        slope = 0.75
        rng = np.random.default_rng(8501)
        for _ in range(250):
            x = rng.uniform(-1.2, 1.2, 3)
            b = rng.uniform(-0.4, 0.4, 3)
            tau = np.linalg.norm(b) + rng.choice([0., 0.1, 0.3])
            gap = envelope(x+b, slope) + envelope(x, slope) - tau
            self.assertAlmostEqual(vertical_overlap(x, b, tau, slope), max(0., gap), places=13)
            if gap >= 0:
                self.assertGreaterEqual(2 * envelope(x, slope) + 1e-14, (1-slope)*tau)
                self.assertGreaterEqual(2 * envelope(x+b, slope) + 1e-14, (1-slope)*tau)
        # Small causal raw-germ gaps and envelope gaps have identical positive
        # parts, even with one spatial endpoint just outside the sphere.
        for radius in [0.9, 0.99, 0.9999]:
            x = np.array([radius, 0., 0.])
            for step in [0.001, 0.02, 0.06]:
                b = np.array([step, 0., 0.])
                raw_gap = slope * (2 - np.dot(x, x) - np.dot(x+b, x+b))/2 - step
                self.assertAlmostEqual(max(0., raw_gap), vertical_overlap(x, b, step, slope))

    def test_exact_capsule_overlap_against_actual_fibre_quadrature(self):
        # Includes the vertex, null and timelike displacements and empty overlap.
        # Quadrature agreement is diagnostic, not a certified error bound.
        for slope, tau, distance in [(0.75, 0., 0.), (0.75, 0.125, 0.125),
                                     (0.75, 0.45, 0.35), (0.75, 0.9, 0.2),
                                     (0.55, 0.2, 0.1)]:
            with self.subTest(slope=slope, tau=tau, distance=distance):
                radius_squared = max(0., 1-tau/slope-distance**2/4)
                closed_form = 8 * math.pi * slope / 15 * radius_squared**2.5
                actual = capsule_overlap_quadrature(tau, distance, slope)
                self.assertAlmostEqual(actual, closed_form, delta=2e-9)

    def test_absolute_two_jet_retains_bulk_hessian(self):
        slope = sp.symbols("s", positive=True)
        tau, r, mu = sp.symbols("tau r mu", real=True)
        exact = 8 * sp.pi * slope / 15 * (1-tau/slope-r*r/4)**sp.Rational(5, 2)
        at_zero = {tau: 0, r: 0}
        linear = sp.diff(exact, tau).subs(at_zero) * tau
        quadratic = (sp.diff(exact, tau, 2).subs(at_zero) * tau*tau
                     + sp.diff(exact, r, 2).subs(at_zero) * r*r) / 2
        self.assertEqual(sp.simplify(linear), -4*sp.pi*tau/3)
        surface = sp.pi * sp.integrate((tau+slope*r*mu)**2/(2*slope), (mu, -1, 1))
        bulk = -sp.Rational(1, 2) * slope * r*r * 4*sp.pi/3
        self.assertEqual(sp.simplify(quadratic - surface - bulk), 0)
        self.assertNotEqual(sp.simplify(quadratic - surface), 0)
        self.assertEqual(sp.simplify(quadratic), sp.pi*tau*tau/slope - sp.pi*slope*r*r/3)
        # Algebraic coefficient after full-sphere averaging and the published
        # signed-log multiplier. This does NOT compute an action limit.
        alpha = 4*sp.pi * sp.pi/slope
        beta = 4*sp.pi * (-sp.pi*slope/3)
        coefficient = sp.simplify((alpha - 3*beta)/(2*sp.pi))
        self.assertEqual(sp.simplify(coefficient - 4*sp.pi*(1+slope*slope)/(2*slope)), 0)

    def test_independent_endpoint_margins_and_perturbed_active_tube(self):
        slope, delta = 0.75, 0.25
        margin, thickness_lip = 1-slope, 2*slope
        self.assertLess(1-thickness_lip-slope, 0)  # old combined margin fails
        epsilon = min(delta**2/2, margin*delta**2/(2*(1+thickness_lip)))
        self.assertGreater(epsilon, 0)
        self.assertLessEqual(thickness_lip*epsilon/(2*delta), margin*delta/4)
        # Retaining the old shortcut epsilon=m*delta^2/2 would not discharge
        # this sufficient inequality once the thickness constant exceeds one.
        old_epsilon = margin*delta**2/2
        self.assertGreater(thickness_lip*old_epsilon/(2*delta), margin*delta/4)

        def gap(x, omega, sigma, v):
            r, tau = (v-sigma/v)/2, (v+sigma/v)/2
            return envelope(x+r*omega, slope) + envelope(x, slope) - tau

        rng = np.random.default_rng(8502)
        count = 0
        for _ in range(100):
            x = rng.uniform(-0.5, 0.5, 3)
            omega = rng.normal(size=3)
            omega /= np.linalg.norm(omega)
            for v in np.linspace(delta, 1.3, 8):
                if gap(x, omega, 0, v) < 0:
                    continue
                count += 1
                old_y = x + v*omega/2
                for point in [x, old_y]:
                    self.assertGreaterEqual(2*envelope(point, slope) + 1e-14, margin*v/2)
                for sigma in [epsilon/2, epsilon]:
                    new_y = x + (v-sigma/v)*omega/2
                    self.assertGreaterEqual(2*envelope(new_y, slope) + 1e-14, margin*delta/4)
        self.assertGreater(count, 100)
        # The tube argument must cover an old root after its perturbed gap is
        # negative, not just the new active set.
        x, omega = np.zeros(3), np.array([1., 0., 0.])
        root = brentq(lambda v: gap(x, omega, 0, v), delta, 2)
        self.assertLess(gap(x, omega, epsilon, root), 0)
        new_y = (root-epsilon/root)*omega/2
        self.assertGreaterEqual(2*envelope(new_y, slope), margin*delta/4)

    def test_long_fibre_keeps_moving_contact_coefficient(self):
        # Actual steep capsule, source -1/3 and null contact v=4/3. Integrate
        # the original Jacobian and direct interval intersection, not a new
        # density. This is a finite numerical/symbolic regression, not a limit
        # proof or uniform fibre little-o assertion.
        sigma, v = sp.symbols("sigma v", real=True)
        R = sp.Rational
        target = -R(1, 3) + (v - sigma/v)/2
        gap = R(1, 3) + R(3, 8)*(1-target**2) - (v+sigma/v)/2
        weight = (v-sigma/v)**2/(8*v)
        root = R(4, 3)
        self.assertEqual(gap.subs({sigma: 0, v: root}), 0)
        speed = -sp.diff(gap, v).subs({sigma: 0, v: root})
        transverse = sp.diff(gap, sigma).subs({sigma: 0, v: root})
        moving = sp.simplify(weight.subs({sigma: 0, v: root})
                             * transverse**2 / (2*speed))
        self.assertEqual(speed, R(5, 8))
        self.assertEqual(moving, R(27, 2560))
        product = sp.expand(weight*gap)
        coefficients = [sp.integrate(product.coeff(sigma, j), (v, 1, root))
                        for j in range(3)]
        fixed_quadratic = float(coefficients[2])
        c0, c1, c2 = map(float, coefficients)
        c2 += float(moving)
        gap_value = sp.lambdify((sigma, v), gap, "math")
        x = np.array([-1/3, 0., 0.])

        def fibre(s):
            contact = brentq(lambda w: gap_value(s, w), 1., float(root))
            return quad(lambda w: (w-s/w)**2/(8*w) * vertical_overlap(
                x, np.array([(w-s/w)/2, 0., 0.]), (w+s/w)/2, 0.75),
                1., contact, epsabs=1e-13, epsrel=1e-13)[0]

        errors = []
        for s in [1e-3, 5e-4, 2.5e-4]:
            value = fibre(s)
            errors.append(abs(value-c0-c1*s-c2*s*s)/(s*s))
            omitted = (value-c0-c1*s-fixed_quadratic*s*s)/(s*s)
            self.assertAlmostEqual(omitted, float(moving), delta=2e-5)
        self.assertLess(errors[-1], errors[0]/3)
        # At exact cutoff contact the right fibre is instead identically zero;
        # the strictly active moving coefficient must not be inserted there.
        for s in [0., 1e-3, 0.02]:
            value = quad(lambda w: (w-s/w)**2/(8*w) * vertical_overlap(
                x, np.array([(w-s/w)/2, 0., 0.]), (w+s/w)/2, 0.75),
                float(root), 2., epsabs=1e-13)[0]
            self.assertAlmostEqual(value, 0., delta=1e-14)

    def test_null_transversality_and_cutoff_contact_do_not_need_smooth_envelope(self):
        slope, delta = 0.75, 0.4
        source = brentq(lambda x: envelope(np.array([x, 0., 0.]), slope)
                        + envelope(np.array([x+delta/2, 0., 0.]), slope)
                        - delta/2, 0, 1)

        def gap(sigma, v):
            r, tau = (v-sigma/v)/2, (v+sigma/v)/2
            return (envelope(np.array([source+r, 0., 0.]), slope)
                    + envelope(np.array([source, 0., 0.]), slope) - tau)

        self.assertAlmostEqual(gap(0, delta), 0, places=12)
        for v in [delta, 0.7, 1., 2., 4.]:
            self.assertLessEqual(gap(0, v)-gap(0, delta),
                                 -(1-slope)*(v-delta)/2 + 1e-12)
            for sigma in [delta**2/20, delta**2/2]:
                difference = gap(sigma, v)-gap(0, v)
                self.assertGreaterEqual(difference, -(1+slope)*sigma/(2*v) - 1e-12)
                self.assertLessEqual(difference, -(1-slope)*sigma/(2*v) + 1e-12)
                self.assertLessEqual(gap(sigma, v), 1e-12)


if __name__ == "__main__":
    unittest.main()
