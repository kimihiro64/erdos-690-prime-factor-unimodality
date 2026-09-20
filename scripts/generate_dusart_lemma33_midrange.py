#!/usr/bin/env python3
"""Generate compact endpoint-row metadata for Dusart Lemma 3.3.

The row assembler works on half-open unit intervals.  This generator chooses
larger rows whenever the endpoint monotonicity proof remains valid, while
keeping the exact endpoint and square-root-floor witnesses in the data file.
It deliberately emits metadata only; Lean proof terms are supplied by the
reusable row constructors in ``DusartFiniteRows.lean``.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


CONSTANT = 1_777_745 / 1_000_000
PAPER_FINITE_CUTOFF = 10**33


def sieve(limit: int) -> bytearray:
    prime = bytearray(b"\1") * (limit + 1)
    prime[:2] = b"\0\0"
    for p in range(2, math.isqrt(limit) + 1):
        if prime[p]:
            prime[p * p : limit + 1 : p] = b"\0" * (
                (limit - p * p) // p + 1
            )
    return prime


def endpoint_values(limit: int) -> tuple[list[float], list[float]]:
    """Return psi-theta and theta at all integer endpoints through limit.

    The first array is accumulated from prime powers of exponent at least two;
    the second is the usual prime logarithm sum.  This is only the numerical
    row-selection pass; the resulting Lean data must still be checked by the
    kernel-side endpoint certificates.
    """
    prime = sieve(limit)
    prime_list = [n for n in range(2, limit + 1) if prime[n]]
    theta = [0.0] * (limit + 1)
    psi_minus_theta = [0.0] * (limit + 1)
    for p in prime_list:
        weight = math.log(p)
        theta[p] += weight
        power = p * p
        while power <= limit:
            psi_minus_theta[power] += weight
            power *= p
    for n in range(1, limit + 1):
        theta[n] += theta[n - 1]
        psi_minus_theta[n] += psi_minus_theta[n - 1]
    return psi_minus_theta, theta


def choose_rows(limit: int) -> list[dict[str, int]]:
    prime_power_sum, theta = endpoint_values(limit)
    rows: list[dict[str, int]] = []
    left = 2402
    while left <= limit:
        root = math.isqrt(left)
        right = left
        while right < limit:
            candidate = right + 1
            margin = prime_power_sum[candidate] - theta[root]
            if margin >= CONSTANT * left ** (1 / 3):
                break
            right = candidate
        rows.append({"left": left, "right": right, "root": root})
        left = right + 1
    return rows


def lean_data(rows: list[dict[str, int]]) -> str:
    lines = [
        "import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows",
        "",
        "set_option autoImplicit false",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "/-! Endpoint metadata for the compact Lemma 3.3 midrange rows. -/",
        "def dusartLemma33MidrangeData : List (Nat × Nat × Nat) := [",
    ]
    lines.extend(
        f"  ({row['left']}, {row['right']}, {row['root']})," for row in rows
    )
    lines.extend(
        [
            "]",
            "",
            "theorem dusartLemma33MidrangeData_length :",
            f"    dusartLemma33MidrangeData.length = {len(rows)} := by decide",
            "",
            "theorem dusartLemma33MidrangeData_cover :",
            "    ∀ n : Nat, 2402 ≤ n → n ≤ 10000000 →",
            "      ∃ row ∈ dusartLemma33MidrangeData,",
            "        row.1 ≤ n ∧ n ≤ row.2.1 := by",
            "  intro n hn hN",
            "  simp [dusartLemma33MidrangeData]",
            "  omega",
            "",
            "end PrimeFactorUnimodality",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=10_000_000)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-output", type=Path)
    args = parser.parse_args()
    rows = choose_rows(args.limit)
    payload = {
        "source": "Dusart, Estimates of Some Functions over Primes Without R.H., Lemma 3.3",
        "left": 2402,
        "right": args.limit,
        "paper_finite_cutoff": PAPER_FINITE_CUTOFF,
        "covers_paper_finite_range": args.limit >= PAPER_FINITE_CUTOFF,
        "constant": "1777745/1000000",
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    if args.lean_output is not None:
        args.lean_output.parent.mkdir(parents=True, exist_ok=True)
        args.lean_output.write_text(lean_data(rows))
    print(f"generated {len(rows)} rows through {args.limit}")


if __name__ == "__main__":
    main()
