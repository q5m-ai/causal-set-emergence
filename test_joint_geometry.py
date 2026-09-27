"""Independent geometric diagnostics, not action-limit or proof substitutes.

Integrate actual tangent Gram densities and the product of two boosted unit
normals. The ambient four-coordinate Euclidean Gram density is a negative
control; it must NOT reproduce the Lorentzian target on the boosted joint.
"""

import unittest

from mpmath import mp


def inner(v, w, lorentz=True):
    return v[0] * w[0] + (-1 if lorentz else 1) * mp.fsum(
        v[i] * w[i] for i in range(1, 4)
    )


def gram_density(v, w, lorentz=True):
    determinant = inner(v, v, lorentz) * inner(w, w, lorentz) - inner(v, w, lorentz) ** 2
    return mp.sqrt(determinant)


def boost(v):
    # Same velocity magnitude as the Lean regression, written without any
    # library transport/area identity. Translations do not act on tangents.
    return (mp.mpf(5) / 4 * v[0] - mp.mpf(3) / 4 * v[1],
            mp.mpf(3) / 4 * v[0] - mp.mpf(5) / 4 * v[1], v[2], v[3])


def joint_data(theta, phi, bend=0):
    """Ellipsoid (1,2,3), height 1/4, future graph bend*sin(x[0])."""
    st, ct, sp, cp = mp.sin(theta), mp.cos(theta), mp.sin(phi), mp.cos(phi)
    axes = (1, 2, 3)
    x = (st * cp, 2 * st * sp, 3 * ct)
    v, w = (ct * cp, 2 * ct * sp, -3 * st), (-st * sp, 2 * st * cp, 0)
    grad_h = tuple(-x[i] / (2 * axes[i] ** 2) for i in range(3))
    grad_f = (bend * mp.cos(x[0]), 0, 0)
    grad_past = tuple(grad_f[i] - grad_h[i] for i in range(3))

    def normal(q):
        factor = mp.sqrt(1 - mp.fsum(a * a for a in q))
        return tuple(a / factor for a in (1, *q))

    def tangent(y):
        return (mp.fsum(grad_f[i] * y[i] for i in range(3)), *y)

    return tangent(v), tangent(w), normal(grad_past), normal(grad_f), grad_h, grad_f


def weighted_integral(order, lorentz):
    nodes, weights = mp.gauss_quadrature(order, "legendre")
    total = mp.mpf(0)
    for i, node in enumerate(nodes):
        theta = (node + 1) * mp.pi / 2
        for j, other in enumerate(nodes):
            phi = (other + 1) * mp.pi
            v, w, past, future, _, _ = joint_data(theta, phi)
            C = inner(boost(past), boost(future))
            weight = C / mp.sqrt(C * C - 1)
            total += weights[i] * weights[j] * weight * gram_density(boost(v), boost(w), lorentz)
    return total * mp.pi**2 / 2


class JointGeometryTest(unittest.TestCase):
    def setUp(self):
        context = mp.workdps(40)
        context.__enter__()
        self.addCleanup(context.__exit__, None, None, None)

    def assertNear(self, actual, expected, tol="1e-32"):
        self.assertLess(abs(actual - expected), mp.mpf(tol) * max(1, abs(expected)))

    def test_curved_joint_density_and_two_normals(self):
        # A genuinely curved future face with a strict budget: 1/2 + 1/8 < 1.
        for theta, phi in [("0.3", "0.7"), ("1.1", "2.4"), ("2.2", "4.8")]:
            v, w, past, future, g, q = joint_data(mp.mpf(theta), mp.mpf(phi), mp.mpf(1) / 8)
            self.assertNear(inner(past, past), 1)
            self.assertNear(inner(future, future), 1)
            self.assertGreater(past[0], 0)
            self.assertGreater(future[0], 0)
            for tangent in (v, w):
                self.assertNear(inner(past, tangent), 0)
                self.assertNear(inner(future, tangent), 0)
            C = inner(past, future)
            self.assertGreater(C, 1)
            angle = mp.acosh(C)
            self.assertGreater(angle, 0)
            self.assertNear(C / mp.sqrt(C * C - 1), mp.coth(angle))
            norm_g = mp.sqrt(mp.fsum(a * a for a in g))
            n = tuple(a / norm_g for a in g)
            qn = mp.fsum(a * b for a, b in zip(q, n))
            tangential = tuple(q[i] - qn * n[i] for i in range(3))
            density = mp.sqrt(1 - mp.fsum(a * a for a in tangential))
            spatial = gram_density((0, *v[1:]), (0, *w[1:]))
            self.assertNear(gram_density(v, w), density * spatial)
            self.assertNear(gram_density(boost(v), boost(w)), gram_density(v, w))
            self.assertNear(inner(boost(past), boost(future)), C)
            self.assertLess(gram_density(v, w), spatial)
            self.assertGreater(gram_density(v, w, lorentz=False), spatial)

    def test_boosted_unequal_axes_integral_and_euclidean_negative_control(self):
        # Two quadrature resolutions and a precision check. These are numerical
        # diagnostics; exact covariance and 48*pi are separately checked in Lean.
        exact = 48 * mp.pi
        self.assertNear(weighted_integral(24, True), exact, "1e-30")
        wrong_low = weighted_integral(24, False)
        wrong_high = weighted_integral(48, False)
        self.assertNear(wrong_low, wrong_high, "1e-5")
        self.assertGreater(wrong_high, mp.mpf("1.1") * exact)
        with mp.workdps(55):
            self.assertNear(weighted_integral(24, True), exact, "1e-30")

    def test_frame_orientation_and_dilation(self):
        v, w, *_ = joint_data(mp.mpf("1.2"), mp.mpf("0.8"), mp.mpf(1) / 8)
        original = gram_density(v, w)
        self.assertNear(gram_density(w, v), original)
        changed_v = tuple(2 * a + b for a, b in zip(v, w))
        self.assertNear(gram_density(changed_v, tuple(-a for a in w)), 2 * original)
        for scale in (mp.mpf(2), mp.mpf(1) / 2):
            self.assertNear(gram_density(tuple(scale * a for a in v), tuple(scale * a for a in w)),
                            scale**2 * original)


if __name__ == "__main__":
    unittest.main()
