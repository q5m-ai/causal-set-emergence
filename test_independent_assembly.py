"""Full-action calibration for the steep class-E capsule (#109).

Integrate the original signed kernel against the actual overlap, not its jet
or an inadmissible planar reference. These are finite-density diagnostics,
not a numerical proof of convergence or a certified quadrature error bound.
The independent vertical-intersection checks live in test_independent_faces.
"""

import math
import unittest

from scipy.integrate import quad


def capsule_pair_integral(rho, slope=0.75, cutoff=None, part="full", tolerance=2e-11):
    """Time/radius coordinates, with full 4*pi sphere and r^2 Jacobian.

    The exact overlap is 8*pi*s/15 * (1-t/s-r^2/4)_+^(5/2).
    The finite support, cone boundary and sharp t+r cutoff are integrated
    explicitly. Both short and long integrals retain the entire signed kernel.
    """
    if rho <= 0 or not 0 < slope < 1:
        raise ValueError("positive density and independent strict face slope required")
    if part not in ("full", "short", "long"):
        raise ValueError("unknown integration part")
    if part != "full" and (cutoff is None or cutoff <= 0):
        raise ValueError("a fixed positive cutoff is required")

    switch = 2 * slope / (math.sqrt(1 + slope*slope) + 1)

    def time_slice(t):
        upper = min(t, 2 * math.sqrt(max(0.0, 1-t/slope)))
        lower = 0.0
        if part == "short":
            upper = min(upper, max(0.0, cutoff-t))
        elif part == "long":
            lower = min(upper, max(0.0, cutoff-t))
        if lower == upper:
            return 0.0

        def radial(r):
            z = math.pi/24 * rho * (t*t-r*r)**2
            kernel = (1-9*z+8*z*z-4*z**3/3) * math.exp(-z)
            overlap = 8*math.pi*slope/15 * max(0.0, 1-t/slope-r*r/4)**2.5
            return 4*math.pi*r*r * kernel * overlap

        return quad(radial, lower, upper, epsabs=tolerance, epsrel=tolerance)[0]

    points = [switch]
    if part != "full":
        points.extend(t for t in (cutoff/2, cutoff) if 0 < t < slope)
    return quad(time_slice, 0, slope, points=sorted(set(points)),
                epsabs=tolerance, epsrel=tolerance)[0]


def capsule_action(rho, **kwargs):
    slope = kwargs.get("slope", 0.75)
    point_volume = 8*math.pi*slope/15
    return 4/math.sqrt(6) * math.sqrt(rho) * (
        point_volume - rho*capsule_pair_integral(rho, **kwargs))


class IndependentAssemblyTests(unittest.TestCase):
    def test_actual_full_action_is_fixed_cutoff_independent(self):
        rho = 1000.0
        prefactor = 4/math.sqrt(6) * math.sqrt(rho)
        full = capsule_action(rho)
        short_values = []
        for delta in (0.2, 0.45):
            short = capsule_action(rho, cutoff=delta, part="short")
            long = -prefactor*rho*capsule_pair_integral(rho, cutoff=delta, part="long")
            self.assertAlmostEqual(short + long, full, delta=2e-7)
            self.assertGreater(abs(long), 0.1)  # cannot drop it at finite density
            short_values.append(short)
        self.assertGreater(abs(short_values[0]-short_values[1]), 1.0)

    def test_full_capsule_action_calibrates_intrinsic_target(self):
        slope = 0.75
        # Independently defined future unit normals and Lorentzian sphere area.
        cosh_angle = (1+slope*slope)/(1-slope*slope)
        target = 4*math.pi * cosh_angle/math.sqrt(cosh_angle*cosh_angle-1)
        self.assertAlmostEqual(target, 25*math.pi/6, places=13)
        values = [capsule_action(rho) for rho in (100.0, 1000.0, 10000.0)]
        errors = [abs(value-target) for value in values]
        self.assertGreater(errors[0], errors[1])
        self.assertGreater(errors[1], errors[2])
        self.assertLess(errors[2], 0.6)
        # Refinement is a diagnostic only, not a rigorous asymptotic estimate.
        refined = capsule_action(10000.0, tolerance=2e-12)
        self.assertAlmostEqual(values[-1], refined, delta=2e-7)

    def test_sharp_cutoff_past_support_and_invalid_inputs(self):
        rho = 100.0
        full = capsule_pair_integral(rho)
        self.assertAlmostEqual(capsule_pair_integral(rho, cutoff=2, part="short"), full,
                               delta=2e-10)
        self.assertEqual(capsule_pair_integral(rho, cutoff=2, part="long"), 0.0)
        for kwargs in ({"rho": 0}, {"rho": rho, "slope": 1},
                       {"rho": rho, "part": "short"},
                       {"rho": rho, "cutoff": 0, "part": "long"}):
            with self.assertRaises(ValueError):
                capsule_pair_integral(**kwargs)


if __name__ == "__main__":
    unittest.main()
