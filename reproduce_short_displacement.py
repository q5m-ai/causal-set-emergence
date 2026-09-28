"""Reproduce #66 finite-displacement diagnostics; never infer a theorem from them."""

import json
import math
from pathlib import Path

import numpy as np

from short_displacement import axial_jet, axial_short_density, jet_short_action, short_monomials
from two_face_diagnostics import AxialCap, RadialCap, action, joint_geometry


def report():
    families = []
    for name, cap, beta in (("planar_unequal_axes", AxialCap(bend=0), 0),
                            ("curved_sine", AxialCap(), 0),
                            ("boosted_planar_lab_cutoff", AxialCap(bend=0), 0.6)):
        jet = axial_jet(cap)["angular"].copy()
        if beta:
            gamma = 1/math.sqrt(1-beta*beta)
            original = jet[2]
            jet[1] *= gamma
            jet[2] *= gamma**2
            jet[3] = original*gamma**2*beta**2/3
        rows = []
        for delta in (0.08, 0.04, 0.02):
            sigma = 0.04*delta**2
            low, high = [axial_short_density(cap, sigma, delta, n, beta=beta) for n in (16, 24)]
            model = float(jet @ short_monomials(sigma, delta))
            rows.append({"delta": delta, "sigma": sigma, "orders": [16, 24],
                         "density_low": low, "density_high": high,
                         "refinement_difference_not_bound": abs(high-low),
                         "quadratic_model": model, "difference_from_model": high-model,
                         "absolute_difference_over_delta5": abs(high-model)/delta**5})
        families.append({"family": name, "beta": beta, "fixed_geometry": {
            "depth": cap.depth, "axes": cap.axes, "bend": cap.bend},
            "independent_target": joint_geometry(cap, 40)["target"],
            "quadratic_short_coefficient": (jet[2]-3*jet[3])/(2*math.pi),
            "density_rows": rows})
    cap = AxialCap()
    weighted = axial_jet(cap, weight=lambda x: x/cap.axes[0],
                         weight_prime=lambda x: np.ones_like(x)/cap.axes[0])
    model_rows = []
    for rho in (1e6, 1e8, 1e9):
        angular = axial_jet(cap)["angular"]
        low, high = [jet_short_action(angular, rho, 0.15, n) for n in (32, 48)]
        model_rows.append({"rho": rho, "delta": 0.15, "orders": [32, 48],
                           "model_action_low": low, "model_action_high": high,
                           "refinement_difference_not_bound": abs(high-low)})
    axial_action_rows = []
    for rho in (1e6, 1e8):
        for order in (16, 24):
            value = action(cap, rho, order, delta=0.08)
            axial_action_rows.append({"rho": rho, "delta": 0.08, "order": order,
                                      "full_action": value["action"],
                                      "short_action": value["point"]-value["pair_diagonal"],
                                      "normalized_long_pair": value["pair_long_near_null"]+value["pair_long_timelike"],
                                      "cancellation_ratio": value["cancellation_ratio"]})
    radial_rows = []
    for order in (16, 24):
        value = action(RadialCap(), 10000, order, delta=0.08)
        radial_rows.append({"rho": 10000, "delta": 0.08, "order": order,
                            "full_action": value["action"],
                            "short_action": value["point"]-value["pair_diagonal"],
                            "normalized_long_pair": value["pair_long_near_null"]+value["pair_long_timelike"],
                            "cancellation_ratio": value["cancellation_ratio"]})
    return {"status": "finite-density/finite-displacement diagnostics, not a proof",
            "arithmetic": "IEEE float64; refinement differences are not certified errors",
            "families": families,
            "signed_weight_x1_over_axis": {k: v for k, v in weighted.items() if k != "angular"},
            "quadratic_model_only_not_region_action": model_rows,
            "quadratic_model_gaussian_z_limit": 10,
            "curved_sine_actual_region": axial_action_rows,
            "curved_radial_actual_region": radial_rows,
            "limitations": ["No conclusion about #61 or the full curved-face limit.",
                            "Bulk/pair and full/long subtractions can amplify numerical errors.",
                            "The model-action table omits the actual overlap remainder.",
                            "Changing displacement cutoffs does not change the fixed geometry."]}


if __name__ == "__main__":
    path = Path(__file__).resolve().parent / "results" / "short-displacement.json"
    path.write_text(json.dumps(report(), indent=2, allow_nan=False)+"\n")
    print(path)
