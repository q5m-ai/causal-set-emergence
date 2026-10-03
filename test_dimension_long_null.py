"""Actual-overlap regressions; written proofs and Lean status stay separate."""

import unittest

from mpmath import mp

import dimension_long_null as ln
from dimension_kernels import transverse_moment


class DimensionLongNullTests(unittest.TestCase):
    def setUp(self):
        context = mp.workdps(45)
        context.__enter__()
        self.addCleanup(context.__exit__, None, None, None)

    def assertNear(self, actual, expected, tolerance="1e-36"):
        self.assertLessEqual(abs(actual-expected), mp.mpf(tolerance)*max(1, abs(expected)))

    def test_symbolic_geometry_and_retained_contact_terms(self):
        ln.check_long_null_identities()

    def test_actual_vertical_intersection_curved_future_and_coordinate_directions(self):
        for d in (3, 4, 5, 6):
            for first in (mp.mpf("-0.6"), mp.mpf(0), mp.mpf("0.2"), mp.mpf("1.2")):
                x = (first,) + (mp.mpf(0),)*(d-2)
                for axis in range(d-1):
                    for sign in (-1, 1):
                        omega = tuple(mp.mpf(sign if i == axis else 0) for i in range(d-1))
                        for sigma, v in ((0, mp.mpf("0.125")), (mp.mpf("0.01"), mp.mpf("0.25")),
                                         (mp.mpf("0.16"), mp.mpf("0.4")), (0, mp.mpf(2))):
                            args = (d, "0.25", "0.125", x, omega, sigma, v)
                            with self.subTest(d=d, first=first, axis=axis, sign=sign, sigma=sigma):
                                self.assertNear(max(0, ln.ball_sine_gap(*args)),
                                                ln.ball_sine_gap(*args, intersect=True))

    def test_curved_cutoff_contact_gradient_has_a_uniform_geometric_margin(self):
        height, bend, delta = mp.mpf("0.25"), mp.mpf("0.125"), mp.mpf("0.125")
        bound = 2*height*mp.sqrt(1-(1+bend)*delta/(2*height))-bend*delta/2
        self.assertGreater(bound, 0)
        for d in (3, 5, 6):
            for sign in (-1, 1):
                omega = (mp.mpf(3)/5, sign*mp.mpf(4)/5) + (mp.mpf(0),)*(d-3)
                for axis in range(d-1):
                    def source(radius):
                        return tuple(radius if i == axis else mp.mpf(0) for i in range(d-1))
                    def contact(radius):
                        first = source(radius)[0]
                        return (height*(1-radius*radius)
                                + bend*(mp.sin(first+delta*omega[0]/2)-mp.sin(first))
                                - delta/2)
                    radius = mp.findroot(contact, (mp.mpf("0.7"), mp.mpf(1)))
                    x = source(radius)
                    self.assertNear(contact(radius), 0)
                    gradient = [-2*height*xi for xi in x]
                    gradient[0] += bend*(mp.cos(x[0]+delta*omega[0]/2)-mp.cos(x[0]))
                    self.assertGreaterEqual(mp.sqrt(mp.fsum(z*z for z in gradient)), bound)
                    args = (d, height, bend, x, omega, 0, delta)
                    self.assertNear(max(0, ln.ball_sine_gap(*args)),
                                    ln.ball_sine_gap(*args, intersect=True))

    def test_actual_curved_fibres_and_moving_contact_coefficient(self):
        for d in (3, 4, 5, 6):
            # Genuine sine curvature at the translated target; no toy amplitude.
            x = (mp.mpf("0.2"),) + (mp.mpf(0),)*(d-2)
            omega = (mp.mpf(1),) + (mp.mpf(0),)*(d-2)
            args = (d, "0.25", "0.125", x, omega, "0.125")
            F0, F1, F2, contact = ln.ball_sine_fibre_jet(*args)
            self.assertGreater(contact, 0)
            self.assertNear(ln.ball_sine_fibre(*args, 0), F0)
            quotients = []
            for sigma in map(mp.mpf, ("0.00001", "0.000001", "0.0000001")):
                actual = ln.ball_sine_fibre(*args, sigma)
                self.assertNear(actual, ln.ball_sine_fibre(*args, sigma, intersect=True))
                quotient = (actual-F0-F1*sigma)/sigma**2
                quotients.append(quotient)
            self.assertLess(abs(quotients[-1]-F2), abs(quotients[0]-F2)/50)
            self.assertNear(quotients[-1], F2, "0.0001")
            # Omitting the root term leaves a real quadratic discrepancy.
            self.assertNear(quotients[-1]-(F2-contact), contact, "0.0001")

    def test_exact_cutoff_contact_empty_fibres_and_critical_source(self):
        for d in (3, 5, 6):
            omega = (mp.mpf(1),) + (mp.mpf(0),)*(d-2)
            x = (mp.mpf("0.5"),) + (mp.mpf(0),)*(d-2)
            # H(x)=3/16, null root=3/8: rational exact contact, not a tolerance.
            args = (d, "0.25", 0, x, omega, mp.mpf(3)/8)
            self.assertEqual(ln.ball_sine_fibre_jet(*args), (0, 0, 0, 0))
            for sigma in (0, mp.mpf("0.0001")):
                self.assertEqual(ln.ball_sine_fibre(*args, sigma), 0)
            center = (mp.mpf(0),)*(d-1)  # retained positive-height critical point
            self.assertGreater(ln.ball_sine_fibre(d, "0.25", 0, center, omega, "0.125", 0), 0)
            exterior = (mp.mpf(2),) + center[1:]
            self.assertEqual(ln.ball_sine_fibre(d, "0.25", 0, exterior, omega, "0.125", 0), 0)

    def test_approaching_contacts_do_not_have_uniform_quadratic_little_o(self):
        delta = mp.mpf("0.25")
        omega = (mp.mpf(1), mp.mpf(0))
        errors = []
        # One fixed planar region; only source points approach the contact set.
        for sigma in map(mp.mpf, ("0.0001", "0.00001", "0.000001")):
            H = delta/2 + sigma/(4*delta)
            x = (mp.sqrt(1-4*H), mp.mpf(0))
            args = (3, "0.25", 0, x, omega, delta)
            self.assertEqual(ln.ball_sine_fibre(*args, sigma), 0)  # already closed
            F0, F1, F2, _ = ln.ball_sine_fibre_jet(*args)
            errors.append(abs(F0+F1*sigma+F2*sigma*sigma)/sigma**2)
            # The uniform first-order O(sigma^2) estimate remains viable.
            self.assertLess(abs(F0+F1*sigma)/sigma**2, 10)
        self.assertGreater(errors[-1], mp.mpf("0.01"))
        self.assertNear(errors[-1], errors[-2], "0.001")

    def test_actual_averaged_density_two_disintegrations_and_support(self):
        for d in (3, 4, 5, 6):
            for delta in map(mp.mpf, ("0.125", "0.3", "0.5", "0.75")):
                for sigma in map(mp.mpf, ("0", "0.001", "0.015625", "0.03", "0.0625", "0.08")):
                    args = (d, "0.25", delta, sigma)
                    with self.subTest(d=d, delta=delta, sigma=sigma):
                        actual = ln.planar_ball_density(*args)
                        self.assertGreaterEqual(actual, 0)
                        self.assertNear(actual, ln.planar_ball_density(*args, coordinates="null"))
            self.assertEqual(ln.planar_ball_density(d, "0.25", "0.125", -1), 0)

    def test_actual_five_six_density_jets_at_regular_cutoff(self):
        # Independent high-precision Taylor probes of the full averaged density.
        # Differentiating the quadrature is only a regression, not the proof in §5.
        for d in (5, 6):
            density = lambda sigma: ln.planar_ball_density(d, "0.25", "0.125", sigma)
            # Use a smooth time-integral extension near zero for two-sided probes.
            def extension(sigma):
                height, delta = mp.mpf("0.25"), mp.mpf("0.125")
                lower = (delta+sigma/delta)/2
                return ln._area(d)/2*mp.quad(
                    lambda t: (t*t-sigma)**(mp.mpf(d-3)/2)
                    * ln.planar_ball_overlap(d, height, t), [lower, height])
            degree = d//2
            coefficients = [mp.diff(extension, 0, j)/mp.factorial(j) for j in range(degree+1)]
            residuals = []
            for sigma in map(mp.mpf, ("0.00001", "0.000001")):
                self.assertNear(density(sigma), extension(sigma))
                residuals.append(abs(density(sigma)-mp.fsum(
                    b*sigma**j for j, b in enumerate(coefficients)))/sigma**(mp.mpf(d)/2))
            self.assertLess(residuals[-1], residuals[0]/2)

    def test_complete_signed_three_long_action_not_absolute_kernel(self):
        height, delta = mp.mpf("0.25"), mp.mpf("0.125")
        # Actual B has b2 sigma^2 as its first uncancelled term. Check the full
        # signed quadrature against its independent coefficient, not a fitted jet.
        b2 = mp.pi**2*(height-delta/2)/(8*height*delta**2)
        c = mp.pi/12
        beta = 2*c**(mp.mpf(2)/3)/mp.gamma(mp.mpf(5)/3)
        predicted = -beta*b2*c**(-2)*mp.mpf(2)/3
        values = []
        for rho in map(mp.mpf, ("1e8", "1e10")):
            actual = ln.planar_three_long_action(height, delta, rho)
            values.append(actual)
            self.assertLess(actual, 0)
            self.assertNear(actual*rho**(mp.mpf(1)/3), predicted, "0.001")
        self.assertLess(abs(values[1]), abs(values[0])/4)

    def test_fractional_model_is_not_annihilated_in_five_or_six(self):
        for d in (5, 6):
            self.assertNotEqual(transverse_moment(d, mp.mpf("2.5")), 0)
        sigma = mp.mpf("0.03125")
        fractional = mp.quad(lambda x: (x*x-sigma)**2, [-1, -mp.sqrt(sigma)])
        fractional += mp.quad(lambda x: (x*x-sigma)**2, [mp.sqrt(sigma), 1])
        polynomial = mp.mpf(2)/5-4*sigma/3+2*sigma**2
        self.assertNear((fractional-polynomial)/sigma**mp.mpf("2.5"), -mp.mpf(16)/15)
        logarithmic = mp.quad(lambda a: (a-sigma)**2*(-mp.log(a)), [sigma, 1])
        self.assertNear(logarithmic, mp.mpf(1)/9-sigma/2+sigma**2
                        +sigma**3*mp.log(sigma)/3-mp.mpf(11)/18*sigma**3)

    def test_invalid_inputs_are_not_silent_geometry_changes(self):
        for d in (True, 2, 3.5):
            with self.assertRaises(ValueError):
                ln.ray_jacobian(d, 0, 1)
        for sigma, v in ((-1, 1), (2, 1), (0, 0)):
            with self.assertRaises(ValueError):
                ln.ray_coordinates(sigma, v)
        with self.assertRaises(ValueError):
            ln.ball_sine_fibre(3, "0.25", "0.5", (0, 0), (1, 0), 1, 0)
        with self.assertRaises(ValueError):
            ln.ball_sine_fibre(3, "0.25", 0, (0, 0), (1, 0), "0.1", "0.02")
        with self.assertRaises(ValueError):
            ln.ball_sine_fibre(3, "0.25", 0, (0, 0, 0), (1, 0), 1, 0)
        with self.assertRaises(ValueError):
            ln.ball_sine_fibre(3, "0.25", 0, (0, 0), (1, 1), 1, 0)
        with self.assertRaises(ValueError):
            ln.planar_ball_density(3, "0.25", 0, 0)
        with self.assertRaises(ValueError):
            ln.planar_ball_density(3, "0.25", "0.1", 0, coordinates="probability")


if __name__ == "__main__":
    unittest.main()
