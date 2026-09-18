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

def witness(index: int, offset: int) -> str:
    name = label(index)
    return (f"\ndef fullRecordGapValue{name} : Nat := {value(offset)}\n"
            f"\ntheorem fullRecordGapTerm{name}_eq_value :\n"
            f"    {term(offset)} = fullRecordGapValue{name} := by\n"
            "  rw [recordGapCenter_eq_fullRecordGapCenterValue]\n"
            "  rfl\n\n"
            "set_option maxHeartbeats 0 in\n"
            f"theorem fullRecordGapLiteral{name}_fast_pow_mod_ne_one :\n"
            f"    fastPowMod 3 fullRecordGapValue{name} (fullRecordGapValue{name} - 1) ≠ 1 := by\n"
            "  decide\n\n"
            f"theorem fullRecordGapTerm{name}_not_prime : ¬({term(offset)}).Prime := by\n"
            f"  rw [fullRecordGapTerm{name}_eq_value]\n"
            "  apply not_prime_of_fastPowMod_ne_one (a := 3)\n"
            "  · norm_num\n"
            f"  · norm_num [fullRecordGapValue{name}, fullRecordGapCenterValue]\n"
            f"  · exact fullRecordGapLiteral{name}_fast_pow_mod_ne_one\n")

def row(indices: list[tuple[int, int]]) -> str:
    header = ("import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod\n"
              "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter\n\n"
              "set_option autoImplicit false\nset_option maxRecDepth 10000000\n"
              "set_option linter.style.longLine false\n\nnamespace PrimeFactorUnimodality\n")
    return header + "".join(witness(i, d) for i, d in indices) + "\nend PrimeFactorUnimodality\n"

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--row-size", type=int, default=256)
    args = parser.parse_args()
    offsets = validate_manifest(json.loads(args.manifest.read_text()))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows: list[str] = []
    for start in range(0, len(offsets), args.row_size):
        indices = list(enumerate(offsets[start:start + args.row_size], start=start + 1))
        name = f"Row{start // args.row_size + 1:04d}"
        (args.output_dir / f"{name}.lean").write_text(row(indices))
        rows.append(name)
    assembly = "\n".join(f"import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat.Rows.{name}" for name in rows)
    (args.output_dir.parent.parent / "FullRecordGapFermat.lean").write_text(assembly + "\n")
    print(f"wrote {len(rows)} rows for {len(offsets)} witnesses")

if __name__ == "__main__":
    main()
