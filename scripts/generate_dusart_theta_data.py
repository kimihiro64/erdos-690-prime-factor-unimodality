#!/usr/bin/env python3
"""Generate reusable exact theta facts for the Lemma 3.3 endpoint rows.

The endpoint proofs only need theta at integer root floors.  Keeping those
facts in one generated module avoids repeating a prime-list certificate in
every row proof.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def integer_root(n: int, k: int) -> int:
    lo, hi = 0, n + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return lo


def primes_le(n: int) -> list[int]:
    sieve = bytearray(b"\1") * (n + 1)
    if n >= 0:
        sieve[0] = 0
    if n >= 1:
        sieve[1] = 0
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\0" * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def roots(payload: dict) -> list[int]:
    result: set[int] = set()
    for row in payload["rows"]:
        for n in (row["left"], row["right"]):
            k = 2
            while 2**k <= n:
                result.add(integer_root(n, k))
                k += 1
    return sorted(result)


def render(values: list[int]) -> str:
    out = [
        "import Mathlib.NumberTheory.Chebyshev",
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 10000000",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "noncomputable section",
        "",
        "/- Integer theta values shared by generated Lemma 3.3 endpoint rows. -/",
    ]
    for n in values:
        ps = primes_le(n)
        elems = ", ".join(map(str, ps))
        out.extend(
            [
                f"theorem dusart_theta_nat_{n} :",
                f"    Chebyshev.theta ({n} : Real) =",
                f"      ∑ p ∈ ({{{elems}}} : Finset Nat), Real.log p := by",
                f"  have h := Chebyshev.theta_eq_sum_primesLE_log {n}",
                f"  have hp : Nat.primesLE {n} = {{{elems}}} := by decide",
                "  rw [hp] at h",
                "  simpa using h",
                "",
            ]
        )
    out.extend(["end", "", "end PrimeFactorUnimodality", ""])
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    payload = json.loads(args.input.read_text())
    values = roots(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(values))
    print(f"generated {len(values)} shared theta facts")


if __name__ == "__main__":
    main()
