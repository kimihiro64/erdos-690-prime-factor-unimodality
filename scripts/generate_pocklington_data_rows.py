#!/usr/bin/env python3
"""Render compact numeric Pocklington rows from an existing replay shard.

This is intentionally a migration tool: it reads the checked legacy shard,
extracts only the numeric certificate data, and leaves the legacy family in
place until a compact consumer has been validated.
"""

from __future__ import annotations

import argparse
import ast
import re
from pathlib import Path


THEOREM = re.compile(
    r"theorem lowPrime_(\d+) : Nat\.Prime \1 := by\n"
    r".*?apply Nat\.prime_of_pocklington_factor_of_prime_factors "
    r"(\d+) (\d+) (\d+) (\d+) (\[[^\n]+\])",
    re.S,
)


def extract(path: Path) -> list[tuple[int, int, int, int, list[int], list[int]]]:
    text = path.read_text()
    matches = list(THEOREM.finditer(text))
    result = []
    for index, match in enumerate(matches):
        start = match.start()
        finish = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        block = text[start:finish]
        n, _, F, R, base = map(int, match.groups()[:5])
        factors = ast.literal_eval(match.group(6))
        inverses = [
            int(value)
            for value in re.findall(
                rf"apply IsUnit\.of_mul_eq_one \((\d+) : ZMod {n}\)", block
            )
        ]
        if len(inverses) != len(factors):
            raise ValueError(f"{path}: {n}: factor/residue count mismatch")
        result.append((n, F, R, base, factors, inverses))
    if not result:
        raise ValueError(f"no Pocklington witnesses found in {path}")
    return result


def render(name: str, certificates: list[tuple[int, int, int, int, list[int], list[int]]]) -> str:
    data_name = f"pocklingtonData{name}"
    rows = []
    for n, F, R, base, factors, inverses in certificates:
        residues = ", ".join(f"({q}, {inv})" for q, inv in zip(factors, inverses))
        rows.append(
            "    { n := "
            f"{n}, F := {F}, R := {R}, a := {base}, "
            f"factors := {factors!r}, residues := [{residues}] }}"
        )
    names = [f"d{index}" for index in range(len(certificates))]
    cases = " | ".join("rfl" for _ in names)
    return "\n".join(
        [
            "import PrimeFactorUnimodality.Mathlib.NumberTheory.PocklingtonRows",
            "",
            "set_option autoImplicit false",
            "set_option maxRecDepth 100000",
            "",
            "namespace PrimeFactorUnimodality",
            "",
            f"def {data_name} : List PocklingtonData :=",
            "  [",
            ",\n".join(rows),
            "  ]",
            "",
            f"set_option maxRecDepth 100000 in\ntheorem {data_name}_valid :",
            f"    PocklingtonRow.Valid {data_name} := by",
            "  intro d hd",
            f"  simp [{data_name}] at hd",
            f"  rcases hd with {cases}",
            "  all_goals",
            "    unfold PocklingtonData.Valid PocklingtonData.coverValid",
            "      PocklingtonData.residueValid",
            "    decide",
            "",
            "end PrimeFactorUnimodality",
            "",
        ]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--name", required=True)
    args = parser.parse_args()
    args.output.write_text(render(args.name, extract(args.source)))


if __name__ == "__main__":
    main()
