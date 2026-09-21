#!/usr/bin/env python3
"""Render bounded Lean owner certificates for the record-gap block."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.generate_record_gap_block import Assignment, semantic_hash

CHUNK_SIZE = 80

RESIDUE_CONSTRUCTORS = {
    2: (1, "two"),
    3: (2, "three"),
    5: (1, "five"),
    7: (1, "seven"),
    11: (4, "eleven"),
    44_983: (39_717, "q44983"),
    45_541: (37_619, "q45541"),
    52_103: (32_377, "q52103"),
    228_523: (85_050, "q228523"),
    550_631: (86_302, "q550631"),
    1_129_577: (82_320, "q1129577"),
    1_291_193: (82_500, "q1291193"),
    3_020_411_447: (85_750, "q3020411447"),
}


def validate(data: dict[str, Any]) -> list[Assignment]:
    digest = data.pop("semantic_sha256")
    if semantic_hash(data) != digest:
        raise ValueError("record-gap semantic hash mismatch")
    assignments = cast(list[Assignment], data["assignments"])
    expected = list(range(data["low_offset"], data["high_offset"] + 1))
    if [entry["offset"] for entry in assignments] != expected:
        raise ValueError("record-gap offsets are not consecutive")
    for entry in assignments:
        owner = entry["owner"]
        if entry["source"] == "fermat":
            if owner is not None:
                raise ValueError("Fermat exception unexpectedly has an owner")
            continue
        if not isinstance(owner, int) or owner < 2 or owner > 3_100_000_000:
            raise ValueError("invalid owner")
        d = -int(entry["offset"])
        if entry["source"] == "primorial-tail-prime":
            if d % owner:
                raise ValueError("tail owner does not divide the offset")
        else:
            residue, _ = RESIDUE_CONSTRUCTORS[owner]
            if d % owner != residue:
                raise ValueError("residue owner does not match the offset")
    return assignments


def theorem(entry: Assignment) -> str:
    d = -int(entry["offset"])
    owner = entry["owner"]
    if owner is None:
        return ""
    if entry["source"] == "primorial-tail-prime":
        owner_proof = """Or.inl ⟨by
      decide, by norm_num⟩"""
    else:
        residue, constructor = RESIDUE_CONSTRUCTORS[int(owner)]
        owner_proof = f"""Or.inr ⟨{residue}, RecordGapResidue.{constructor}, by norm_num⟩"""
    return f"""theorem recordGap_not_prime_{d} :
    ¬(recordGapCenter - {d}).Prime := by
  apply recordGap_sub_not_prime (d := {d}) (q := {owner})
  · norm_num
  · norm_num
  · norm_num
  · exact {owner_proof}
"""


def render_chunk(number: int, entries: list[Assignment]) -> str:
    body = "\n".join(filter(None, (theorem(entry) for entry in entries)))
    ds = [-int(entry["offset"]) for entry in entries]
    proved_ds = [d for d, entry in zip(ds, entries, strict=True) if entry["owner"] is not None]
    alternatives = "\n".join(f"      | exact recordGap_not_prime_{d}" for d in proved_ds)
    exceptional = 84_672 in ds
    exception_argument = " (exception_ne : d ≠ 84672)" if exceptional else ""
    exception_case = "\n      | exact (exception_ne rfl).elim" if exceptional else ""
    coverage = f"""
theorem recordGapCoverage_part{number:02d} (d : Nat)
    (lower : {min(ds)} ≤ d) (upper : d ≤ {max(ds)}){exception_argument} :
    ¬(recordGapCenter - d).Prime := by
  interval_cases d <;>
    first{exception_case}
{alternatives}
"""
    previous_import = (
        ""
        if number == 1
        else f"import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part{number - 1:02d}\n"
    )
    return f"""{previous_import}import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Generated record-gap owner certificates, part {number:02d}. -/

namespace PrimeFactorUnimodality

{body}
{coverage}
end PrimeFactorUnimodality
"""


def render_group(
    group_number: int,
    chunk_numbers: list[int],
    chunks: list[list[Assignment]],
) -> str:
    previous_group = (
        ""
        if group_number == 1
        else f"\nimport PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup{group_number - 1:02d}"
    )
    imports = (
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordGapCoverage.Part{chunk_numbers[-1]:02d}" + previous_group
    )
    ds = [-int(entry["offset"]) for number in chunk_numbers for entry in chunks[number - 1]]
    cases: list[str] = []
    for position, number in enumerate(chunk_numbers):
        chunk_ds = [-int(entry["offset"]) for entry in chunks[number - 1]]
        call = f"recordGapCoverage_part{number:02d} d (by omega) (by omega)"
        if 84_672 in chunk_ds:
            call += " exception_ne"
        if position + 1 == len(chunk_numbers):
            cases.append(f"  exact {call}")
        else:
            cases.extend(
                [
                    f"  by_cases h{position} : {min(chunk_ds)} ≤ d",
                    f"  · exact {call}",
                ]
            )
    proof = "\n".join(cases)
    exception_binder = "exception_ne" if 84_672 in ds else "_exception_ne"
    return f"""{imports}

set_option autoImplicit false

/-! Generated assembly group {group_number:02d} for the record-gap coverage certificate. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage_group{group_number:02d} (d : Nat)
    (lower : {min(ds)} ≤ d) (upper : d ≤ {max(ds)})
    ({exception_binder} : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
{proof}

end PrimeFactorUnimodality
"""


def render_facade(group_ranges: list[tuple[int, int]]) -> str:
    imports = (
        "import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup"
        f"{len(group_ranges):02d}"
    )
    cases: list[str] = []
    for index, (lower, _) in enumerate(group_ranges, start=1):
        call = f"recordGapCoverage_group{index:02d} d (by omega) (by omega) exception_ne"
        if index == len(group_ranges):
            cases.append(f"  exact {call}")
        else:
            cases.extend([f"  by_cases h{index} : {lower} ≤ d", f"  · exact {call}"])
    proof = "\n".join(cases)
    return f"""{imports}

set_option autoImplicit false

/-! Assembly of the generated composite coverage for the record-gap block. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage (d : Nat) (lower : 81649 ≤ d) (upper : d ≤ 86399)
    (exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
{proof}

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    entries = validate(data)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    chunks = [entries[index : index + CHUNK_SIZE] for index in range(0, len(entries), CHUNK_SIZE)]
    for index, chunk in enumerate(chunks):
        number = index + 1
        target = args.output_dir / f"Part{number:02d}.lean"
        target.write_text(render_chunk(number, chunk))
    group_ranges: list[tuple[int, int]] = []
    for start in range(0, len(chunks), 12):
        numbers = list(range(start + 1, min(start + 12, len(chunks)) + 1))
        group_number = start // 12 + 1
        group_entries = [entry for number in numbers for entry in chunks[number - 1]]
        ds = [-int(entry["offset"]) for entry in group_entries]
        group_ranges.append((min(ds), max(ds)))
        group_target = (
            args.output_dir.parent.parent / f"RecordGapCoverageGroup{group_number:02d}.lean"
        )
        group_target.write_text(render_group(group_number, numbers, chunks))
    facade_target = args.output_dir.parent.parent / "RecordGapCoverage.lean"
    facade_target.write_text(render_facade(group_ranges))


if __name__ == "__main__":
    main()
