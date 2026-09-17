"""Exact fixed-point data shared by the Erdős 690 certificate generators."""

from __future__ import annotations

from math import isqrt

FIXED_WEIGHT_SCALE = 10**9
FIXED_WEIGHT_REQUIRED_ENDPOINTS = {113, 211, 15683, 15727, 31397, 31469}


def _is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def fixed_weight_values() -> tuple[list[int], dict[int, tuple[int, int]]]:
    """Compute both directed fixed-point sums at all certificate endpoints."""
    endpoints = sorted(set(range(250, 31251, 250)) | FIXED_WEIGHT_REQUIRED_ENDPOINTS)
    values: dict[int, tuple[int, int]] = {0: (0, 0)}
    lower = 0
    upper = 0
    endpoint_set = set(endpoints)
    for n in range(31469):
        if _is_prime(n):
            term = FIXED_WEIGHT_SCALE // (n - 1)
            lower += term
            upper += term + 1
        if n + 1 in endpoint_set:
            values[n + 1] = (lower, upper)
    return endpoints, values


def medium_weight_bounds_module() -> str:
    """Generate the rational bounds consumed by the medium-range proof."""
    _, values = fixed_weight_values()
    specs = (
        (113, "upper"),
        (211, "upper"),
        (15683, "lower"),
        (15727, "lower"),
        (15727, "upper"),
        (31397, "lower"),
        (31469, "lower"),
        (31469, "upper"),
    )
    body = """import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums

set_option autoImplicit false

/-! Generated rational reciprocal-weight bounds for the medium finite range. -/

namespace PrimeFactorUnimodality

"""
    for endpoint, direction in specs:
        lower, upper = values[endpoint]
        if direction == "lower":
            body += f"""theorem weightSumPrimesBelow{endpoint}Lower :
    ({lower} : Rat) / {FIXED_WEIGHT_SCALE} ≤ weightSum (primesBelow {endpoint}) := by
  exact fixedWeightSums_lower_bound {FIXED_WEIGHT_SCALE} {endpoint} {lower} {upper}
    (by norm_num) fixedWeightSumsAt{endpoint}

"""
        else:
            body += f"""theorem weightSumPrimesBelow{endpoint}Upper :
    weightSum (primesBelow {endpoint}) ≤ ({upper} : Rat) / {FIXED_WEIGHT_SCALE} := by
  exact fixedWeightSums_upper_bound {FIXED_WEIGHT_SCALE} {endpoint} {lower} {upper}
    (by norm_num) fixedWeightSumsAt{endpoint}

"""
    return body + "end PrimeFactorUnimodality\n"
