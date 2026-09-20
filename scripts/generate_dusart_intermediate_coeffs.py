#!/usr/bin/env python3
"""Generate exact rational coefficients for the intermediate exponent sum."""

from __future__ import annotations

from fractions import Fraction
import math
from pathlib import Path


DEN = 10_000


def coefficient(n: int, k: int) -> int:
    # q >= 2^(-n*(k-3)/(3*k)); choose the least denominator-DEN rational.
    # The final comparison is exact, so the Decimal-like floating estimate is
    # only a starting point for the integer search.
    exponent = Fraction(n * (k - 3), 3 * k)
    # Start near the real value, then adjust with exact integer arithmetic.
    num = math.ceil(DEN * 2 ** (-float(exponent))) + 1
    while num > 0:
        candidate = Fraction(num - 1, DEN)
        if candidate == 0:
            break
        # candidate^(3k) * 2^(n(k-3)) >= 1 is the exact certificate.
        if candidate ** (3 * k) * 2 ** (n * (k - 3)) >= 1:
            num -= 1
        else:
            break
    return num


def render() -> str:
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
        "def dusartIntermediateCoeff : Nat → Nat → Nat",
    ]
    for n in range(23, 110):
        for k in range(4, 32):
            out.append(f"  | {n}, {k} => {coefficient(n, k)}")
    out += ["  | _, _ => 0", ""]
    out += [
        "theorem dusartIntermediateCoeff_power",
        "    {N k : Nat} (hN : 23 ≤ N) (hN' : N ≤ 109)",
        "    (hk : 4 ≤ k) (hk' : k ≤ 31) :",
        "    (1 : Real) ≤",
        "      ((dusartIntermediateCoeff N k : Real) / 10000) ^ (3 * k) *",
        "        (2 ^ N : Real) ^ (k - 3) := by",
        "  interval_cases N <;> interval_cases k <;>",
        "    norm_num [dusartIntermediateCoeff]",
        "",
        "theorem dusartIntermediateCoeff_margin",
        "    {N : Nat} (hN : 23 ≤ N) (hN' : N ≤ 109) :",
        "    (∑ k ∈ (Finset.Icc 4 (min N 30) : Finset Nat),",
        "      (dusartIntermediateCoeff N k : Real) / 10000) +",
        "      ((N - min N 30 : Nat) : Real) *",
        "        (dusartIntermediateCoeff N (min N 30 + 1) : Real) / 10000 ≤",
        "      (777 : Real) / 1000 := by",
        "  interval_cases N <;>",
        "    norm_num [dusartIntermediateCoeff, Finset.sum_Icc_succ_top]",
        "",
        "end",
        "",
        "end PrimeFactorUnimodality",
        "",
    ]
    return "\n".join(out)


if __name__ == "__main__":
    Path("PrimeFactorUnimodality/Helpers/Analytic/DusartIntermediateCoeffData.lean").write_text(render())
