#!/usr/bin/env python3
"""Extract the published Table 6.6 theta endpoint values.

The paper prints decimal theta values at the interval endpoints.  This
generator converts each printed value to conservative integer-scaled bounds
so a later Lean row generator can attach one shared endpoint fact to each
Table 6.6 coefficient row.  It deliberately emits data only; Lean must still
prove the corresponding Chebyshev-theta inequalities from its certificate.
"""

from __future__ import annotations

import argparse
import json
import re
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from pathlib import Path


ROW = re.compile(
    r"\$\s*([0-9]+)E\+([0-9]+)\s*\$\s*&\s*\$\s*"
    r"([0-9]+(?:\.[0-9]+)?)\s*\$\s*&"
)


def parse_rows(source: str) -> dict[int, Decimal]:
    values: dict[int, Decimal] = {}
    for match in ROW.finditer(source):
        mantissa, exponent, value = match.groups()
        endpoint = int(mantissa) * 10 ** int(exponent)
        values[endpoint] = Decimal(value)
    return values


def scaled_bounds(value: Decimal, scale: int) -> tuple[int, int]:
    with localcontext() as context:
        context.prec = 80
        scaled = value * scale
        lower = int(scaled.to_integral_value(rounding=ROUND_FLOOR)) - 1
        upper = int(scaled.to_integral_value(rounding=ROUND_CEILING)) + 1
    return lower, upper


def extract(source: str) -> list[dict[str, int]]:
    values = parse_rows(source)
    lefts = list(range(100_000_000, 1_000_000_000, 100_000_000))
    lefts += list(range(1_000_000_000, 10_000_000_000, 1_000_000_000))
    lefts += list(range(10_000_000_000, 100_000_000_000, 10_000_000_000))
    lefts += list(range(100_000_000_000, 800_000_000_000, 100_000_000_000))
    rows: list[dict[str, int]] = []
    for left in lefts:
        right = left + (100_000_000 if left < 1_000_000_000 else
                        1_000_000_000 if left < 10_000_000_000 else
                        10_000_000_000 if left < 100_000_000_000 else
                        100_000_000_000)
        if left not in values or right not in values:
            raise ValueError(f"missing theta endpoint {left} or {right}")
        lower_left, _ = scaled_bounds(values[left], 1_000_000)
        _, upper_right = scaled_bounds(values[right], 1_000_000)
        rows.append({
            "left": left,
            "right": right,
            "theta_lower_left_scaled": lower_left,
            "theta_upper_right_scaled": upper_right,
            "scale": 1_000_000,
        })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = extract(args.input.read_text())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"rows": rows}, indent=2) + "\n")
    print(f"extracted {len(rows)} Table 6.6 endpoint rows")


if __name__ == "__main__":
    main()
