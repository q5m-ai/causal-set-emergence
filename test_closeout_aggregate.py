"""Finite checks of CA1--CA4, not physical intervals or a #177 proof.

The inverse is the ONE aggregate leading Morse volume. These controls test
its count-free comparison, including the sharp all-opening case. They neither
realize a spacetime nor estimate the missing geometric integral H(w).
"""

import math
import random
import unittest


def _volume(clock, amplitudes, gaps):
    return math.fsum(a * max(clock - d, 0.0) ** 1.5
                     for a, d in zip(amplitudes, gaps))


def _inverse(volume, amplitudes, gaps):
    """Bisection with the zero-gap primary's exact upper bracket."""
    assert volume > 0 and len(amplitudes) == len(gaps)
    assert amplitudes[0] > 0 and gaps[0] == 0
    assert all(a > 0 for a in amplitudes) and all(d >= 0 for d in gaps)
    lo, hi = 0.0, (volume / amplitudes[0]) ** (2.0 / 3.0)
    for _ in range(100):
        mid = (lo + hi) / 2
        if _volume(mid, amplitudes, gaps) < volume:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def _comparison(volume, amplitudes, gaps, retained):
    kept_a = [amplitudes[i] for i in retained]
    kept_d = [gaps[i] for i in retained]
    upper = _inverse(volume, kept_a, kept_d)
    omitted = math.fsum(a * max(upper - d, 0.0) ** 1.5
                        for i, (a, d) in enumerate(zip(amplitudes, gaps))
                        if i not in retained)
    ratio = omitted / volume
    # log1p/expm1 avoid loss when the omitted mass is tiny.
    loss_bound = upper * -math.expm1(-2 * math.log1p(ratio) / 3)
    actual = _inverse(volume, amplitudes, gaps)
    return upper, actual, ratio, loss_bound


class AggregateCloseoutTests(unittest.TestCase):
    def test_count_free_bound_and_actual_root(self):
        rng = random.Random(177180)
        for count in (1, 2, 3, 8, 64, 257):
            for _ in range(12):
                volume = 10 ** rng.uniform(-5, 3)
                amplitudes = [10 ** rng.uniform(-3, 3) for _ in range(count)]
                primary = (volume / amplitudes[0]) ** (2 / 3)
                gaps = [0.0] + [primary * rng.uniform(0, 2)
                                for _ in range(count - 1)]
                retained = list(range(min(count, 2)))
                upper, actual, ratio, bound = _comparison(
                    volume, amplitudes, gaps, retained)
                tol = 2e-12 * primary
                self.assertLessEqual(actual, upper + tol)
                self.assertLessEqual(upper - actual, bound + tol)
                self.assertLessEqual(bound, upper * min(1, 2 * ratio / 3) + tol)
                self.assertAlmostEqual(
                    _volume(actual, amplitudes, gaps) / volume, 1, places=11)

    def test_sharp_equal_arrivals(self):
        # Equality in the new comparison. Scalar control, NOT a spacetime.
        for count in (3, 10, 100):
            for phase in (1e-7, 0.1, 1.0):
                upper, actual, _, bound = _comparison(
                    phase ** 1.5, [1.0] * count, [0.0] * count, [0, 1])
                self.assertAlmostEqual(upper / phase, 2 ** (-2 / 3), places=13)
                self.assertAlmostEqual(actual / phase, count ** (-2 / 3), places=13)
                self.assertAlmostEqual((upper - actual) / phase,
                                       bound / phase, places=13)
                self.assertGreater((upper - actual) / phase, 0.14)

    def test_inactive_states_have_no_effect(self):
        upper, actual, ratio, bound = _comparison(
            1.0, [1.0, 2.0, 1e20], [0.0, 0.1, 2.0], [0, 1])
        self.assertEqual(ratio, 0)
        self.assertEqual(bound, 0)
        self.assertEqual(upper, actual)

    def test_aggregate_not_route_count_controls_bound(self):
        original = _comparison(0.6, [1, 3, 7], [0, 0.1, 0.2], [0, 1])
        # Split the same amplitude among labels: no physical multiplicity claim.
        refined = _comparison(0.6, [1, 3] + [7 / 128] * 128,
                              [0, 0.1] + [0.2] * 128, [0, 1])
        for x, y in zip(original, refined):
            self.assertAlmostEqual(x, y, places=13)

    def test_common_cap_and_signed_mask_keep_strip_bound(self):
        upper, actual, _, bound = _comparison(
            1.0, [1, 2, 5, 3], [0, 0.1, 0.03, 0.2], [0, 1])
        # Signed piecewise-constant physical-clock weight, supremum <= 2.
        pieces = [(0, 0.2, 2.0), (0.2, 0.5, -1.5), (0.5, 3.0, 1.0)]
        for cap in (0.01, actual, (actual + upper) / 2, upper, 3):
            signed = math.fsum(weight * max(0, min(upper, cap, right)
                                             - max(actual, left))
                               for left, right, weight in pieces)
            self.assertLessEqual(abs(signed), 2 * bound + 1e-14)

    def test_best_pair_does_not_erase_third_arrivals(self):
        amplitudes, gaps = [1, 2, 3, 4], [0, 0.03, 0.07, 0.1]
        pair = min(range(1, 4), key=lambda j: _inverse(
            1.0, [amplitudes[0], amplitudes[j]], [0, gaps[j]]))
        upper, actual, _, bound = _comparison(1, amplitudes, gaps, [0, pair])
        self.assertGreater(upper - actual, 0.01)
        self.assertLessEqual(upper - actual, bound)


if __name__ == "__main__":
    unittest.main()
