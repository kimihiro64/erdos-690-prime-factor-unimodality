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
        n, _, factor_bound, remainder_bound, base = map(int, match.groups()[:5])
        factors = ast.literal_eval(match.group(6))
        inverses = [
            int(value)
            for value in re.findall(rf"apply IsUnit\.of_mul_eq_one \((\d+) : ZMod {n}\)", block)
        ]
        if len(inverses) != len(factors):
            raise ValueError(f"{path}: {n}: factor/residue count mismatch")
        result.append((n, factor_bound, remainder_bound, base, factors, inverses))
    if not result:
        raise ValueError(f"no Pocklington witnesses found in {path}")
    return result


def render(name: str, certificates: list[tuple[int, int, int, int, list[int], list[int]]]) -> str:
    data_name = f"pocklingtonData{name}"
    defs = []
    data_names = []
    for n, factor_bound, remainder_bound, base, factors, inverses in certificates:
        residues = ", ".join(f"({q}, {inv})" for q, inv in zip(factors, inverses, strict=False))
        datum_name = f"{data_name}_{n}"
        data_names.append(datum_name)
        defs.extend(
            [
                f"def {datum_name} : PocklingtonData :=",
                "  { n := "
                f"{n}, F := {factor_bound}, R := {remainder_bound}, a := {base}, "
                f"factors := {factors!r}, residues := [{residues}] }}",
                "",
            ]
        )
    cases = " | ".join("rfl" for _ in data_names)
    wrappers = []
    for datum_name, (n, *_rest) in zip(data_names, certificates, strict=False):
        wrappers.extend(
            [
                f"set_option maxRecDepth 100000 in\ntheorem lowPrime_{n} : Nat.Prime {n} := by",
                f"  apply PocklingtonData.prime {datum_name}",
                f"  apply {data_name}_valid",
                f"  simp [{data_name}, {datum_name}]",
                "",
            ]
        )
    return "\n".join(
        [
            "import PrimeFactorUnimodality.Helpers.FiniteCertificates.PocklingtonRows",
            "",
            "set_option autoImplicit false",
            "set_option maxRecDepth 100000",
            "",
            "namespace PrimeFactorUnimodality",
            "",
            *defs,
            f"def {data_name} : List PocklingtonData := [{', '.join(data_names)}]",
            "",
            f"set_option maxRecDepth 1000000 in\ntheorem {data_name}_valid :",
            f"    PocklingtonRow.Valid {data_name} := by",
            "  intro d hd",
            f"  simp [{data_name}] at hd",
            f"  rcases hd with {cases}",
            "  all_goals",
            "    unfold PocklingtonData.Valid PocklingtonData.coverValid",
            "      PocklingtonData.residueValid",
            "    decide",
            "",
            *wrappers,
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
