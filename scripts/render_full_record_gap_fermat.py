#!/usr/bin/env python3
"""Render kernel-replayable Fermat witnesses for full record-gap exceptions.

Generation is deliberately range-addressable so the 10,918 expensive Lean
checks can be scheduled and resumed without duplicating completed work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.generate_record_gap_block import PRIME_LIMIT, primes_up_to


def validate_manifest(data: dict[str, Any]) -> list[int]:
    digest = data.pop("semantic_sha256")
    encoded = json.dumps(data, sort_keys=True, separators=(",", ":")).encode()
    if hashlib.sha256(encoded).hexdigest() != digest:
        raise ValueError("full record-gap manifest semantic hash mismatch")
    offsets = data["fermat_offsets"]
    if not isinstance(offsets, list) or not all(isinstance(value, int) for value in offsets):
        raise ValueError("invalid Fermat offset list")
    if len(offsets) != data["fermat_count"] or len(offsets) != len(set(offsets)):
        raise ValueError("inconsistent Fermat offset count")
    return offsets


def record_center() -> int:
    value = 587
    for prime in primes_up_to(PRIME_LIMIT):
        if prime >= 13:
            value *= prime
    return value


def render_center(center: int) -> str:
    return f"""import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

/-! Literal bridge for the published full record-gap center. -/

namespace PrimeFactorUnimodality

def fullRecordGapCenterValue : Nat := {center}

set_option maxHeartbeats 0 in
-- Exact reduction of the 4,499-factor center is intentionally unbounded.
theorem recordGapCenter_eq_fullRecordGapCenterValue :
    recordGapCenter = fullRecordGapCenterValue := by
  rfl

end PrimeFactorUnimodality
"""


def label(index: int) -> str:
    return f"{index:05d}"


def term_expression(offset: int) -> str:
    if offset < 0:
        return f"recordGapCenter - {abs(offset)}"
    return f"recordGapCenter + {offset}"


def render_witness(index: int, offset: int, modulus: int, residue: int) -> str:
    name = label(index)
    term = term_expression(offset)
    return f"""import Mathlib.Tactic.ReduceModChar
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option exponentiation.threshold 100000
set_option linter.style.longLine false

/-! Generated base-3 Fermat replay for full-gap offset {offset}. -/

namespace PrimeFactorUnimodality

def fullRecordGapValue{name} : Nat := {modulus}

def fullRecordGapResidue{name} : Nat := {residue}

theorem fullRecordGapTerm{name}_eq_value :
    {term} = fullRecordGapValue{name} := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  norm_num [fullRecordGapCenterValue, fullRecordGapValue{name}]

set_option maxHeartbeats 0 in
-- Proof-producing modular exponentiation of a roughly 62,000-bit exponent.
theorem fullRecordGapLiteral{name}_three_pow :
    (3 : ZMod {modulus}) ^ {modulus - 1} =
      (({residue} : Nat) : ZMod {modulus}) := by
  reduce_mod_char

theorem fullRecordGapResidue{name}_ne_one :
    ((fullRecordGapResidue{name} : Nat) : ZMod fullRecordGapValue{name}) ≠ 1 := by
  intro residue_eq_one
  have modulus_gt_one : 1 < fullRecordGapValue{name} := by
    norm_num [fullRecordGapValue{name}]
  have value_eq_one :=
    (ZMod.val_eq_one modulus_gt_one
      ((fullRecordGapResidue{name} : Nat) : ZMod fullRecordGapValue{name})).mpr
      residue_eq_one
  rw [ZMod.val_natCast_of_lt (by
    norm_num [fullRecordGapResidue{name}, fullRecordGapValue{name}])] at value_eq_one
  norm_num [fullRecordGapResidue{name}] at value_eq_one

theorem fullRecordGapTerm{name}_not_prime : ¬({term}).Prime := by
  rw [fullRecordGapTerm{name}_eq_value]
  apply not_prime_of_pow_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue{name}]
  · change (3 : ZMod {modulus}) ^ {modulus - 1} ≠ 1
    rw [fullRecordGapLiteral{name}_three_pow]
    simpa only [fullRecordGapResidue{name}, fullRecordGapValue{name}] using
      fullRecordGapResidue{name}_ne_one

end PrimeFactorUnimodality
"""


def render_assembly(count: int) -> str:
    imports = "\n".join(
        f"import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapFermat.Part{label(index)}"
        for index in range(1, count + 1)
    )
    return f"""{imports}

set_option autoImplicit false

/-! Assembly of the kernel-replayed Fermat witnesses for the full record gap. -/
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--start", type=int, default=1, help="one-based witness index")
    parser.add_argument("--count", type=int, default=1)
    args = parser.parse_args()
    if args.start < 1 or args.count < 1:
        parser.error("--start and --count must be positive")

    offsets = validate_manifest(json.loads(args.manifest.read_text()))
    selected = offsets[args.start - 1 : args.start - 1 + args.count]
    if len(selected) != args.count:
        parser.error("requested witness range exceeds the manifest")
    center = record_center()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    center_target = args.output_dir.parent / "FullRecordGapCenter.lean"
    center_target.write_text(render_center(center))

    for index, offset in enumerate(selected, start=args.start):
        modulus = center + offset
        residue = pow(3, modulus - 1, modulus)
        if residue == 1:
            raise ValueError(f"offset {offset} is a base-3 probable prime")
        target = args.output_dir / f"Part{label(index)}.lean"
        target.write_text(render_witness(index, offset, modulus, residue))
        print(f"wrote witness {index}/{len(offsets)} for offset {offset}")

    end = args.start + args.count - 1
    if end == len(offsets):
        assembly_target = args.output_dir.parent / "FullRecordGapFermat.lean"
        assembly_target.write_text(render_assembly(len(offsets)))
        print(f"wrote assembly for {len(offsets)} witnesses")


if __name__ == "__main__":
    sys.set_int_max_str_digits(1_000_000)
    main()
