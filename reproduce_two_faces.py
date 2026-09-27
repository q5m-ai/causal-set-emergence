"""Emit the bounded #54 experiment as JSON; never infer a proved limit.

Default run: a few minutes, deterministic CPU quadrature, no sampling.
Use --orders 12 20 --densities 1e4 for a shorter exploratory run.
"""

import argparse
from dataclasses import asdict
import json
import math
import platform
import sys

import numpy as np
import scipy
import mpmath
from mpmath import mp

from calculations import ellipsoid_action
from two_face_diagnostics import (
    AxialCap, RadialCap, action, axial_null_contact, axial_overlap,
    boosted_ellipsoid_action, joint_geometry, overlap_density,
    quadratic_remainder_probe,
)


def planar_density_reference(sigma, delta, depth=0.25, axes=(1, 2, 3)):
    """Independent 1D (s,r) disintegration of the known planar overlap."""
    sigma, delta, depth = map(mp.mpf, (sigma, delta, depth))
    lower = max(mp.sqrt(sigma), (delta + sigma / delta) / 2) if 0 < delta and sigma < delta**2 else mp.sqrt(sigma)
    if lower >= depth:
        return mp.mpf(0)
    volume = 8 * mp.pi * depth * mp.fprod(axes) / 15
    return 2 * mp.pi * volume * mp.quad(
        lambda s: mp.sqrt(s * s - sigma) * (1 - s / depth)**mp.mpf("2.5"), [lower, depth]
    )


def experiments(orders, densities):
    caps = {
        "planar_ellipsoid": AxialCap(bend=0),
        "matched_joint_bump": RadialCap(),
        "nonplanar_sine": AxialCap(),
        # Separate FIXED geometries; no density-dependent angle tuning.
        "small_angle_008": AxialCap(depth=0.08, axes=(1, 1, 1), bend=0.01),
        "small_angle_004": AxialCap(depth=0.04, axes=(1, 1, 1), bend=0.005),
    }
    report = {
        "status": "exploratory deterministic evidence; refinement differences are not certified errors",
        "arithmetic": "IEEE float64, compensated accumulation; mpmath references at 40 and 60 dps",
        "versions": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__, "mpmath": mpmath.__version__},
        "settings": {"orders": orders, "densities": densities, "delta": 0.15, "sigma_split": 0.01,
                     "z_limit": 9, "kernel": [1, -9, 8, -4 / 3]},
        "regions": {}, "calibrations": {},
    }
    for name, cap in caps.items():
        print(f"Integrating {name}", file=sys.stderr, flush=True)
        region = {"type": type(cap).__name__, "parameters": asdict(cap), "kappa": cap.kappa,
                  "lambda": cap.lam, "spacelike_margin": 1 - cap.slope_budget,
                  "sigma_support_bound": cap.sigma_max, "volume": cap.volume,
                  "geometry": [dict(order=n, **joint_geometry(cap, n)) for n in orders],
                  "runs": [], "remainder_probes": []}
        for rho in densities:
            runs = [action(cap, rho, n) for n in orders]
            references = []
            # The bump's independent matched-joint reference is the sphere,
            # not the unequal-axis ellipsoid used by the covariance test.
            for dps in (40, 60):
                with mp.workdps(dps):
                    axes = (cap.radius,) * 3 if isinstance(cap, RadialCap) else cap.axes
                    references.append(mp.nstr(ellipsoid_action(rho, cap.depth, axes), 30))
            region["runs"].append({"rho": rho, "quadratures": runs,
                                   "action_refinement_spread_not_bound": max(r["action"] for r in runs) - min(r["action"] for r in runs),
                                   "planar_reference_40_60_dps": references})
        # Fixed long cutoff: no fitting jet supplied to the integration engine.
        for h in (0.001, 0.0005, 0.00025):
            probes = []
            for n in orders:
                values = [overlap_density(cap, k * h, 0.15, n) for k in range(4)]
                probes.append({"order": n, "B_0_h_2h_3h": values,
                               "third_difference_over_h_squared": quadratic_remainder_probe(values, h)})
            region["remainder_probes"].append({"h": h, "quadratures": probes})
        report["regions"][name] = region

    calibrations = report["calibrations"]
    with mp.workdps(40):
        calibrations["boost"] = [
            {"rho": rho, "beta": beta, "order": n,
             "action": boosted_ellipsoid_action(rho, beta=beta, order=n),
             "reference": mp.nstr(ellipsoid_action(rho, 0.25, (1, 2, 3)), 30)}
            for rho in (1000, 100000) for beta in (0, 0.6, -0.6) for n in orders
        ]
    cap, rho, dilation = AxialCap(), 1000, 1.7
    calibrations["dilation"] = [
        {"order": n, "scale": dilation, "rho": rho,
         "scaled_action": action(cap.dilated(dilation), rho, n, delta=0.15 * dilation,
                                 sigma_split=0.01 * dilation**2)["action"],
         "squared_scale_times_action_at_scaled_density": dilation**2 * action(cap, rho * dilation**4, n)["action"]}
        for n in orders
    ]
    calibrations["long_density"] = []
    for sigma in (0, 0.001, 0.01):
        refs = []
        for dps in (40, 60):
            with mp.workdps(dps):
                refs.append(mp.nstr(planar_density_reference(str(sigma), "0.15"), 30))
        calibrations["long_density"].append({"sigma": sigma, "reference_40_60_dps": refs,
            "quadratures": [{"order": n, "B": overlap_density(AxialCap(bend=0), sigma, 0.15, n)} for n in orders]})
    contact = axial_null_contact(cap)
    calibrations["translated_contact"] = {
        "region": asdict(cap), "ray": "(s,s*e1)", "contact_s": contact,
        "samples": [{"relative_gap": gap, "order": n,
                     "overlap": axial_overlap(cap, contact * (1 - gap), contact * (1 - gap), n)}
                    for gap in (0.1, 0.01, 0.001, -0.001) for n in orders],
    }
    # Synthetic obstruction control: a quadratic-log remainder must not be
    # mistaken for a vanishing diagnostic just because B itself is small.
    calibrations["quadratic_log_control"] = [
        {"h": h, "probe": quadratic_remainder_probe([0] + [(k * h)**2 * math.log(k * h) for k in (1, 2, 3)], h)}
        for h in (0.001, 0.0005, 0.00025)
    ]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="+", type=int, default=[16, 32])
    parser.add_argument("--densities", nargs="+", type=float, default=[1e4, 1e6, 1e8])
    args = parser.parse_args()
    if len(set(args.orders)) < 2 or any(n < 4 for n in args.orders):
        parser.error("supply at least two distinct quadrature orders >= 4")
    if any(not math.isfinite(r) or r <= 0 for r in args.densities):
        parser.error("densities must be finite and positive")
    print(json.dumps(experiments(sorted(set(args.orders)), sorted(set(args.densities))), indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
