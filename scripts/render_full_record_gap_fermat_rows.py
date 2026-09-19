#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scripts.render_full_record_gap_fermat import validate_manifest


def label(index: int) -> str:
    return f"{index:05d}"


def term(offset: int) -> str:
    return f"recordGapCenter {'-' if offset < 0 else '+'} {abs(offset)}"


def value(offset: int) -> str:
    return f"fullRecordGapCenterValue {'-' if offset < 0 else '+'} {abs(offset)}"


def witness(index: int, offset: int, row_name: str) -> str:
    name = label(index)
    return (
        f"\ntheorem fullRecordGapTerm{name}_not_prime : ¬({term(offset)}).Prime := by\n"
        "  rw [recordGapCenter_eq_fullRecordGapCenterValue]\n"
        "  apply not_prime_of_fastPowMod_ne_one (a := 3)\n"
        "  · norm_num\n"
        f"  · norm_num [{value(offset)}]\n"
        f"  · apply {row_name}_fermat\n"
        f"    simp [{row_name}_values]\n"
    )


def row(indices: list[tuple[int, int]], row_name: str | None = None) -> str:
    if row_name is None:
        row_name = f"fullRecordGapRow{label((indices[0][0] - 1) // 256 + 1)}"
    values = ",\n    ".join(value(offset) for _, offset in indices)
    header = (
        "import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod\n"
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter\n\n"
        "set_option autoImplicit false\nset_option maxRecDepth 10000000\n"
        "set_option linter.style.longLine false\n\nnamespace PrimeFactorUnimodality\n"
    )
    row_header = (
        f"\ndef {row_name}_values : List Nat :=\n"
        f"  [{values}]\n\n"
        "set_option maxHeartbeats 0 in\n"
        f"theorem {row_name}_fermat : ∀ n ∈ {row_name}_values,\n"
        "    fastPowMod 3 n (n - 1) ≠ 1 := by\n"
        "  decide\n"
    )
    return (
        header
        + row_header
        + "".join(witness(i, d, row_name) for i, d in indices)
        + "\nend PrimeFactorUnimodality\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--row-size", type=int, default=64)
    args = parser.parse_args()
    offsets = validate_manifest(json.loads(args.manifest.read_text()))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows: list[str] = []
    for start in range(0, len(offsets), args.row_size):
        indices = list(enumerate(offsets[start : start + args.row_size], start=start + 1))
        name = f"Row{start // args.row_size + 1:04d}"
        (args.output_dir / f"{name}.lean").write_text(
            row(indices, f"fullRecordGapRow{label(start // args.row_size + 1)}")
        )
        rows.append(name)
    assembly = "\n".join(
        f"import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat.Rows.{name}"
        for name in rows
    )
    (args.output_dir.parent.parent / "FullRecordGapFermat.lean").write_text(assembly + "\n")
    print(f"wrote {len(rows)} rows for {len(offsets)} witnesses")


if __name__ == "__main__":
    main()
