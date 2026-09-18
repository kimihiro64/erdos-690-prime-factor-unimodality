#!/usr/bin/env python3
"""Render binary-dispatch Lean modules for the full record-gap partition."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


CHUNK = 512


def label(index: int) -> str:
    return f"{index:05d}"


def leaf_proof(
    assignment: dict[str, Any], d: int, operation: str, fermat_indices: dict[int, int]
) -> list[str]:
    offset = -d if operation == "sub" else d
    kind = assignment["kind"]
    if kind == "fermat":
        index = fermat_indices[offset]
        return [f"      exact fullRecordGapTerm{label(index)}_not_prime"]
    q = int(assignment["q"])
    if kind == "tail":
        if operation == "sub":
            return [
                f"      apply fullRecordGap_sub_not_prime (q := {q}) (by norm_num)",
                "      exact by decide",
            ]
        return [
            f"      apply fullRecordGap_add_not_prime (q := {q})",
            "      exact by decide",
        ]
    r = int(assignment["r"])
    if operation == "sub":
        return [
            f"      apply fullRecordGap_sub_not_prime (q := {q}) (by norm_num)",
            "      right",
                f"      exact ⟨{r}, by norm_num, by norm_num, by norm_num, by norm_num⟩",
        ]
    return [
        f"      apply fullRecordGap_add_not_prime (q := {q})",
        "      right",
        f"      exact ⟨{r}, by norm_num, by norm_num, by norm_num, by norm_num⟩",
    ]


def dispatch(
    assignments: dict[int, dict[str, Any]],
    lo: int,
    hi: int,
    operation: str,
    fermat_indices: dict[int, int],
    indent: str = "  ",
) -> list[str]:
    if lo == hi:
        lines = [f"{indent}have : d = {lo} := by omega", f"{indent}subst d"]
        lines.extend(leaf_proof(assignments[lo], lo, operation, fermat_indices))
        return lines
    mid = (lo + hi) // 2
    lines = [f"{indent}by_cases h : {mid + 1} ≤ d", f"{indent}·"]
    lines.extend(dispatch(assignments, mid + 1, hi, operation, fermat_indices, indent + "  "))
    lines.append(f"{indent}·")
    lines.extend(dispatch(assignments, lo, mid, operation, fermat_indices, indent + "  "))
    return lines


def render_part(
    assignments: dict[int, dict[str, Any]],
    lo: int,
    hi: int,
    operation: str,
    fermat_indices: dict[int, int],
    index: int,
) -> str:
    bound = "455703" if operation == "sub" else "657401"
    term = "recordGapCenter - d" if operation == "sub" else "recordGapCenter + d"
    theorem = f"fullRecordGap{operation.capitalize()}Block_part{index:04d}"
    body = dispatch(assignments, lo, hi, operation, fermat_indices)
    return "\n".join(
        [
            "import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure",
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat",
            "",
            "set_option autoImplicit false",
            "set_option maxRecDepth 1000000",
            "set_option linter.style.longLine false",
            "",
            "namespace PrimeFactorUnimodality",
            "",
            f"theorem {theorem} (d : Nat) ({lo} ≤ d) (d ≤ {hi}) : ¬({term}).Prime := by",
            *body,
            "",
            "end PrimeFactorUnimodality",
            "",
        ]
    )


def render_chunk_dispatch(operation: str, bound: int) -> list[str]:
    ranges = [(lo, min(bound, lo + CHUNK - 1)) for lo in range(1, bound + 1, CHUNK)]
    offset = 0 if operation == "sub" else len(range(1, 455704, CHUNK))

    def go(first: int, last: int, indent: str) -> list[str]:
        if first == last:
            lo, hi = ranges[first]
            part = first + 1 + offset
            return [
                f"{indent}exact fullRecordGap{operation.capitalize()}Block_part{part:04d}"
                f" d (by omega) (by omega)"
            ]
        mid = (first + last) // 2
        threshold = ranges[mid + 1][0]
        lines = [f"{indent}by_cases h : {threshold} ≤ d", f"{indent}·"]
        lines.extend(go(mid + 1, last, indent + "  "))
        lines.append(f"{indent}·")
        lines.extend(go(first, mid, indent + "  "))
        return lines

    return go(0, len(ranges) - 1, "  ")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("assignments", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()
    payload = json.loads(args.assignments.read_text())
    assignments = {
        int(item["offset"]): item for item in payload["assignments"]
    }
    manifest = json.loads(args.manifest.read_text())
    fermat_indices = {
        offset: index for index, offset in enumerate(manifest["fermat_offsets"], start=1)
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    imports: list[str] = []
    part_index = 1
    for operation, bound in (("sub", 455703), ("add", 657401)):
        for lo in range(1, bound + 1, CHUNK):
            hi = min(bound, lo + CHUNK - 1)
            name = f"FullRecordGap{operation.capitalize()}BlockPart{part_index:04d}.lean"
            (args.output_dir / name).write_text(
                render_part(
                    {d: assignments[-d if operation == "sub" else d]
                     for d in range(lo, hi + 1)},
                    lo, hi, operation, fermat_indices, part_index
                )
            )
            imports.append(
                "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapOwners."
                + name.removesuffix(".lean")
            )
            part_index += 1
    sub_dispatch = render_chunk_dispatch("sub", 455703)
    add_dispatch = render_chunk_dispatch("add", 657401)
    assembly = "\n".join(imports) + """

set_option autoImplicit false

namespace PrimeFactorUnimodality

theorem fullRecordGapSubBlock (d : Nat) (lower : 1 ≤ d)
    (upper : d ≤ 455703) : ¬(recordGapCenter - d).Prime := by
""" + "\n".join(sub_dispatch) + """

theorem fullRecordGapAddBlock (d : Nat) (lower : 1 ≤ d)
    (upper : d ≤ 657401) : ¬(recordGapCenter + d).Prime := by
""" + "\n".join(add_dispatch) + """

end PrimeFactorUnimodality
"""
    (args.output_dir.parent / "FullRecordGapOwners.lean").write_text(assembly)


if __name__ == "__main__":
    main()
