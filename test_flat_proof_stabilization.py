"""Proof-mechanism diagnostics, not certification or new example theorems.

The boost quotient tests faithful diamond/physical-union bookkeeping outside
an ultrastatic presentation. The mask models test exactly the weak contact
regularity used by FL12; they are not claimed to be physical action examples.
"""

import math
import unittest

from scipy.integrate import quad

from test_finite_lift_flat_reduction import _circle_distance, _circle_pieces


def _milne_fibre(lower, upper, source_time):
    """Integral of tau*d(tau) in log(tau/source_time) coordinates."""
    if upper <= lower:
        return 0.0
    return source_time**2 * math.exp(2*lower) * math.expm1(2*(upper-lower))/2


def _milne_union(intervals, source_time):
    cuts = sorted({v for interval in intervals for v in interval})
    return sum(_milne_fibre(a, b, source_time)
               for a, b in zip(cuts, cuts[1:])
               if any(lo <= (a+b)/2 <= hi for lo, hi in intervals))


class FlatProofStabilizationTest(unittest.TestCase):
    def test_faithful_boost_diamond_against_independent_milne_integral(self):
        # The future Minkowski cone in Milne coordinates has volume tau*d(tau)*d(chi).
        # A deck boost shifts chi. There is no global ultrastatic metric assumption.
        for source_time in (.7, 1.8):
            for gap in (.23, .81, 1.7):
                target_time = source_time * math.exp(gap)
                for chi in (-.8*gap, .1*gap, .7*gap):
                    lower, upper = (chi-gap)/2, (chi+gap)/2
                    direct = quad(
                        lambda z: _milne_fibre(abs(z), gap-abs(z-chi), source_time),
                        lower, upper, points=sorted([0, chi]),
                        epsabs=2e-12, epsrel=2e-12)[0]
                    phase = (source_time**2+target_time**2
                             - 2*source_time*target_time*math.cosh(chi))
                    self.assertAlmostEqual(direct, phase/2, delta=2e-11*phase)
                    # Forgetting the nonconstant endpoint/intermediate measure fails.
                    conformal_area = (gap*gap-chi*chi)/2
                    self.assertGreater(abs(direct-conformal_area), 1e-4*direct)

    def test_boost_quotient_union_not_sum_of_developed_volumes(self):
        length, gap, target, source_time = 1.1, 2.4, .31, .7
        for z in (0, .12, .31, .56, .82, 1.07):
            pieces = _circle_pieces(length, gap, target, z)
            actual = _milne_union([interval for _, _, interval in pieces], source_time)
            independent = _milne_fibre(
                _circle_distance(z, length),
                gap-_circle_distance(z-target, length), source_time)
            self.assertAlmostEqual(actual, independent, delta=2e-12*max(1, independent))
        physical = quad(
            lambda z: _milne_fibre(_circle_distance(z, length),
                                  gap-_circle_distance(z-target, length), source_time),
            0, length, points=[target, length/2, target+length/2],
            epsabs=2e-11, epsrel=2e-11)[0]
        target_time = source_time*math.exp(gap)
        lift_sum = sum((source_time**2+target_time**2
                        - 2*source_time*target_time*math.cosh(target+m*length))/2
                       for m in range(math.ceil((-gap-target)/length),
                                      math.floor((gap-target)/length)+1))
        self.assertGreater(lift_sum, 1.1*physical)

    def test_coincident_masks_have_directional_not_linear_derivative(self):
        # All three masks z>=0, z>=u*x and z>=v are individually regular;
        # their zero sets coincide on a positive-measure boundary at u=v=0.
        def fibre(u, v):
            points = [0]
            if u and -1 < v/u < 1:
                points.append(v/u)
            return quad(lambda x: 1-max(0, u*x, v), -1, 1,
                        points=sorted(set(points)), epsabs=1e-13)[0]
        derivatives = []
        for a, b, expected in ((1, 0, -.5), (0, 1, -2), (1, 1, -2)):
            for h in (.1, .001, .00001):
                actual = (fibre(h*a, h*b)-fibre(0, 0))/h
                self.assertAlmostEqual(actual, expected, delta=1e-9)
            derivatives.append(expected)
        self.assertNotEqual(derivatives[0]+derivatives[1], derivatives[2])

    def test_infinite_order_contact_has_no_unjustified_power_rate(self):
        # Three scaled positive coordinates with sum <= w, and the smooth
        # regular mask u1 >= exp(-1/z^2), extended by zero at z=0.
        # Exact integration of the three coordinates gives N(w)/w^3 below.
        # This diagnoses FL12's o(w^3), not a claimed physical G-SS density.
        normalized = []
        for log_inverse_w in (16, 64, 256, 1024):
            ell = log_inverse_w
            integral = quad(
                lambda t: (-math.expm1(-ell*(1/(t*t)-1)))**3 if t else 1,
                0, 1, epsabs=2e-12, epsrel=2e-12)[0]
            ratio = integral/(3*math.sqrt(ell))
            normalized.append(ratio)
            self.assertLessEqual(math.sqrt(ell)*ratio, 1/3+1e-13)
            self.assertGreaterEqual(math.sqrt(ell)*ratio,
                                    (1-3/(2*ell))/3-1e-13)
        self.assertTrue(all(a > b for a, b in zip(normalized, normalized[1:])))
        # For any fixed positive power gain, the ratio to that gain diverges.
        # This lower bound already rules out the tempting quarter-power rate.
        self.assertGreater(normalized[-1]*math.exp(1024/4), 1e100)


if __name__ == '__main__':
    unittest.main()
