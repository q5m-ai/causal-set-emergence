"""Order-of-magnitude feasibility checks, NOT a causal-set signal prediction.

Standard library only. No network access. Optional FIRAS input is the small
NASA table identified in evidence.json; it is not downloaded by this script.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

C_M_S = 299_792_458.0
H_J_S = 6.62607015e-34
PARSEC_M = 3.085677581491367e16
PLANCK_ENERGY_GEV = 1.22089e19  # rounded hbar-based Planck energy, for toy dispersion only


def dhs_fractional_rms_bound(
    distance: float, duration: float, area: float, depth: float, velocity: float
) -> float:
    """DHS 1009.3058v2 Eq. (70); inputs in that paper's fundamental units.

    This is an approximate upper-bound expression in the source's regime,
    not a measured noise level, a lower bound or a Maxwell calculation.
    """
    if min(distance, duration, area, depth, velocity) <= 0 or velocity >= 1:
        raise ValueError("positive inputs and 0 < velocity < 1 required")
    return math.sqrt(16 * (
        math.pi * distance / (velocity**2 * duration * area * depth)
        + 1 / (2 * velocity**2 * duration)
    ))


def transport_strength(rate_j_s: float, elapsed_s: float, frequency_hz: float) -> float:
    """Dimensionless k*t/E only; not a fitted spectral residual."""
    if elapsed_s < 0 or frequency_hz <= 0:
        raise ValueError("elapsed time must be nonnegative and frequency positive")
    return rate_j_s * elapsed_s / (H_J_S * frequency_hz)


def toy_delay(travel_s: float, energy_gev: float, order: int) -> float:
    """Toy |delta v|/c=(E/E_Pl)^order; no cosmology or causal-set derivation."""
    if travel_s < 0 or energy_gev < 0 or order not in (1, 2):
        raise ValueError("nonnegative travel/energy and order 1 or 2 required")
    return travel_s * (energy_gev / PLANCK_ENERGY_GEV)**order


def firas_summary(path: Path) -> dict:
    """Read the five documented columns; preserve MJy versus kJy units."""
    rows = [list(map(float, line.split())) for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    if not rows or any(len(row) != 5 for row in rows):
        raise ValueError("expected nonempty five-column FIRAS table")
    if any(row[0] <= 0 or row[3] < 0 for row in rows):
        raise ValueError("invalid frequency or uncertainty")
    peak = max(rows, key=lambda row: row[1])
    if peak[1] <= 0:
        raise ValueError("positive peak intensity required")
    return {
        "rows": len(rows),
        "frequency_GHz_range": [min(r[0] for r in rows) * 100 * C_M_S / 1e9,
                                max(r[0] for r in rows) * 100 * C_M_S / 1e9],
        "peak_MJy_sr": peak[1],
        "peak_bin_one_sigma_ppm": peak[3] / (1000 * peak[1]) * 1e6,
        "warning": "Single-bin uncertainty, not a covariance-aware bound or likelihood.",
    }


def estimates() -> dict:
    age = 4.35e17  # illustrative elapsed time, not a fitted cosmological history
    gpc_light_time = 1e9 * PARSEC_M / C_M_S
    lens_delay = 30 * 86400  # illustrative differential lens path time
    return {
        "status": "scales and conditional bounds; not predictions of the BDG action results",
        "DHS_eq70_fractional_rms_upper_scale": dhs_fractional_rms_bound(
            1e60, 1e27, 1e52, 1e26, 0.1),
        "CMB_k1_t_over_E_at_160GHz": transport_strength(3e-44, age, 160e9),
        "CMB_abs_k2_t_over_E_at_160GHz": transport_strength(1e-43, age, 160e9),
        "forecast_kappa_t_over_E_at_1mHz": transport_strength(1e-56, age, 1e-3),
        "toy_30GeV_1Gpc_linear_seconds": toy_delay(gpc_light_time, 30, 1),
        "toy_30GeV_1Gpc_quadratic_seconds": toy_delay(gpc_light_time, 30, 2),
        "toy_1eV_30day_differential_linear_seconds": toy_delay(lens_delay, 1e-9, 1),
        "toy_30GeV_30day_differential_linear_seconds": toy_delay(lens_delay, 30, 1),
        "GW170817_1p74s_over_40Mpc_light_time": 1.74 / (40e6 * PARSEC_M / C_M_S),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--firas", type=Path, help="optional local NASA monopole table")
    args = parser.parse_args()
    result = estimates()
    if args.firas:
        result["FIRAS_table"] = firas_summary(args.firas)
    print(json.dumps(result, indent=2, allow_nan=False))
