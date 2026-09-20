#!/usr/bin/env python3
"""Generate endpoint proof declarations for compact Lemma 3.3 rows."""

from __future__ import annotations

import argparse
import json
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


def endpoint_theorem(left: int, n: int) -> str:
    max_power = n.bit_length() - 1
    roots = [(k, integer_root(n, k)) for k in range(2, max_power + 1)]
    name = f"dusart_lemma33_row_endpoint_{left}_{n}"
    out = [
        f"theorem {name} :",
        f"    Chebyshev.psi ({n} : Real) - Chebyshev.theta {n} -",
        f"        Chebyshev.theta (Real.sqrt ({n} : Real)) <",
        f"      (1777745 : Real) / 1000000 * ({left} : Real) ^ (1 / (3 : Real)) := by",
        "  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)",
        f"  have hN : ⌊Real.log ({n} : Real) / Real.log 2⌋₊ ≤ {max_power} := by",
        "    apply Nat.le_of_lt_succ",
        "    apply (Nat.floor_lt (by positivity)).2",
        f"    have hlog : Real.log ({n} : Real) < Real.log ((2 : Real) ^ {max_power + 1}) :=",
        "      Real.log_lt_log (by norm_num) (by norm_num)",
        "    rw [Real.log_pow] at hlog",
        "    norm_num at hlog ⊢",
        "    apply (div_lt_iff₀ hlog2).2",
        "    exact hlog",
    ]
    for k, r in roots:
        out.extend(
            [
                f"  have hroot_{k} := nat_floor_rpow_eq_of_pow_le_pow_lt",
                f"    (n := {n}) (k := {k}) (r := {r}) (by norm_num) (by norm_num) (by norm_num)",
                f"  have hroot_{k}' : ⌊({n} : Real) ^ (1 / ({k} : Real))⌋₊ = {r} := by",
                f"    simpa using hroot_{k}",
                f"  have htheta_{k} : Chebyshev.theta (({n} : Real) ^ (1 / ({k} : Real))) =",
                f"      Chebyshev.theta ({r} : Real) := by",
                f"    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_{k}']",
                "    norm_num",
            ]
        )
    out.extend(
        [
            f"  have hsqrt : Chebyshev.theta (Real.sqrt ({n} : Real)) =",
            f"      Chebyshev.theta ({roots[0][1]} : Real) := by",
            "    rw [Real.sqrt_eq_rpow]",
            "    exact htheta_2",
            f"  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := ({n} : Real))",
            "    (by norm_num) hN",
            "  rw [hpsi]",
            "  norm_num [Finset.sum_Icc_succ_top]",
        ]
    )
    out.append("  rw [" + ", ".join(f"htheta_{k}" for k, _ in roots) + ", hsqrt]")
    unique_roots = list(dict.fromkeys(r for _, r in roots))
    out.extend(
        [
            "  rw [" + ", ".join(f"dusart_theta_nat_{r}" for r in unique_roots) + "]",
            "  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]",
            "  interval_decide",
            "",
        ]
    )
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    payload = json.loads(args.input.read_text())
    values = [(row["left"], row["right"]) for row in payload["rows"]]
    if args.limit is not None:
        values = values[: args.limit]
    header = [
        "import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows",
        "import PrimeFactorUnimodality.Helpers.Analytic.DusartProof",
        "import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33ThetaData",
        "import LeanCert.Tactic.IntervalAuto",
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 10000000",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "noncomputable section",
        "",
    ]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "\n".join(header)
        + "\n".join(endpoint_theorem(left, right) for left, right in values)
        + "\nend\n\nend PrimeFactorUnimodality\n"
    )
    print(f"generated {len(values)} endpoint theorems")


if __name__ == "__main__":
    main()
