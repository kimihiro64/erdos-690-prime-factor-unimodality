#!/usr/bin/env python3
"""Render the compact full-record owner rows and reusable block assemblers."""

from __future__ import annotations

import argparse
import io
import sys
import zipfile
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.audit_full_record_gap import (
    HIGH_ENDPOINT,
    LOW_ENDPOINT,
    parse_factors,
    parse_residues,
    smallest_prime_factors,
)
from scripts.fetch_record_gap_archive import fetch_payload
from scripts.generate_record_gap_block import PRIME_LIMIT, primes_up_to


def archive_text(payload: bytes) -> str:
    with zipfile.ZipFile(io.BytesIO(payload)) as archive:
        members = [name for name in archive.namelist() if not name.endswith("/")]
        if len(members) != 1:
            raise ValueError(f"expected one archive member, found {members}")
        return archive.read(members[0]).decode("ascii")


def classify() -> tuple[
    list[tuple[int, int, int]], list[tuple[int, int, int]], list[int], list[int]
]:
    factors = parse_factors(archive_text(fetch_payload("factors")))
    residues = parse_residues(archive_text(fetch_payload("residues")))
    primes = primes_up_to(PRIME_LIMIT)
    tail = [q for q in primes if q >= 13]
    center = 587
    for q in tail:
        center *= q
    center_residues = {q: center % q for q in (2, 3, 5, 7, 11)}
    spf = smallest_prime_factors(max(abs(LOW_ENDPOINT), abs(HIGH_ENDPOINT)))
    sub_archive: list[tuple[int, int, int]] = []
    add_archive: list[tuple[int, int, int]] = []
    sub_fermat: list[int] = []
    add_fermat: list[int] = []
    for offset in range(LOW_ENDPOINT + 1, HIGH_ENDPOINT):
        if offset == 0:
            continue
        small = next(
            (q for q in center_residues if (center_residues[q] + offset) % q == 0),
            None,
        )
        rough = abs(offset)
        for q in center_residues:
            while rough % q == 0:
                rough //= q
        tail_owner = spf[rough] if rough >= 2 else 1
        if small is not None or 13 <= tail_owner <= PRIME_LIMIT:
            continue
        factor = factors.get(offset)
        if factor is not None:
            r = center % factor
            if offset < 0:
                sub_archive.append((-offset, factor, r))
            else:
                add_archive.append((offset, factor, r))
            continue
        if offset not in residues:
            raise ValueError(f"unclassified offset {offset}")
        if offset < 0:
            sub_fermat.append(-offset)
        else:
            add_fermat.append(offset)
    return sub_archive, add_archive, sub_fermat, add_fermat


def lean_list(rows: list[tuple[int, int, int]]) -> str:
    return "[" + ",\n    ".join(f"({d}, {q}, {r})" for d, q, r in rows) + "]"


def witness_list(
    name: str, type_name: str, offsets: list[tuple[int, int]], theorem_prefix: str
) -> str:
    entries = ",\n    ".join(
        f"{{ d := {d}, not_prime := {theorem_prefix}{index:05d}_not_prime }}"
        for d, index in offsets
    )
    return f"def {name} : List {type_name} := [\n    {entries}\n  ]"


def fermat_rows_text(fermat_offsets: list[tuple[int, str]]) -> str:
    """Render all replay rows and derived facts in the compact source file."""
    lines: list[str] = []
    row_size = 64
    for start in range(0, len(fermat_offsets), row_size):
        row_number = start // row_size + 1
        row_name = f"fullRecordGapRow{row_number:05d}"
        entries = fermat_offsets[start : start + row_size]
        values = ",\n    ".join(
            f"fullRecordGapCenterValue {'-' if offset < 0 else '+'} {abs(offset)}"
            for offset, _ in entries
        )
        lines.extend(
            [
                f"def {row_name}_values : List Nat :=\n  [{values}]\n",
                "set_option maxHeartbeats 0 in",
                f"theorem {row_name}_fermat : ∀ n ∈ {row_name}_values,",
                "    fastPowMod 3 n (n - 1) ≠ 1 := by",
                "  decide\n",
            ]
        )
        for index, (offset, _) in enumerate(entries, start=start + 1):
            label = f"{index:05d}"
            sign = "-" if offset < 0 else "+"
            lines.extend(
                [
                    f"theorem fullRecordGapTerm{label}_not_prime : "
                    f"¬(recordGapCenter {sign} {abs(offset)}).Prime := by",
                    "  rw [recordGapCenter_eq_fullRecordGapCenterValue]",
                    "  apply not_prime_of_fastPowMod_ne_one (a := 3)",
                    "  · norm_num",
                    f"  · norm_num [fullRecordGapCenterValue {sign} {abs(offset)}]",
                    f"  · apply {row_name}_fermat",
                    f"    simp [{row_name}_values]\n",
                ]
            )
    return "\n".join(lines)


def render(output: Path) -> None:
    sub_archive, add_archive, sub_fermat, add_fermat = classify()
    fermat_offsets = sorted([(-d, "sub") for d in sub_fermat] + [(d, "add") for d in add_fermat])
    indices = {offset: index for index, (offset, _) in enumerate(fermat_offsets, start=1)}
    sub_entries = witness_list(
        "fullRecordGapSubWitnesses",
        "FullRecordGapSubWitness",
        [(d, indices[-d]) for d in sub_fermat],
        "fullRecordGapTerm",
    )
    add_entries = witness_list(
        "fullRecordGapAddWitnesses",
        "FullRecordGapAddWitness",
        [(d, indices[d]) for d in add_fermat],
        "fullRecordGapTerm",
    )
    fermat_rows = fermat_rows_text(fermat_offsets)
    source = f"""import PrimeFactorUnimodality.Proof.LargeRange.RecordGapOwnerRows
import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

structure FullRecordGapArchiveRow where
  d : Nat
  q : Nat
  r : Nat

structure FullRecordGapSubWitness where
  d : Nat
  not_prime : ¬(recordGapCenter - d).Prime

structure FullRecordGapAddWitness where
  d : Nat
  not_prime : ¬(recordGapCenter + d).Prime

def fullRecordGapSubArchive : List FullRecordGapArchiveRow :=
  {lean_list(sub_archive)}

def fullRecordGapAddArchive : List FullRecordGapArchiveRow :=
  {lean_list(add_archive)}

def fullRecordGapSubArchiveOwner? (d : Nat) : Option FullRecordGapOwner :=
  match fullRecordGapSubArchive.find? (fun row => row.d == d) with
  | some row => some (.residue row.q row.r)
  | none => none

def fullRecordGapAddArchiveOwner? (d : Nat) : Option FullRecordGapOwner :=
  match fullRecordGapAddArchive.find? (fun row => row.d == d) with
  | some row => some (.residue row.q row.r)
  | none => none

def fullRecordGapSmallSubOwner? (d : Nat) : Option FullRecordGapOwner :=
  if (1 + d) % 2 = 0 then some (.residue 2 1)
  else if (2 + d) % 3 = 0 then some (.residue 3 2)
  else if (1 + d) % 5 = 0 then some (.residue 5 1)
  else if (1 + d) % 7 = 0 then some (.residue 7 1)
  else if (4 + d) % 11 = 0 then some (.residue 11 4)
  else none

def fullRecordGapSmallAddOwner? (d : Nat) : Option FullRecordGapOwner :=
  if (1 + d) % 2 = 0 then some (.residue 2 1)
  else if (2 + d) % 3 = 0 then some (.residue 3 2)
  else if (1 + d) % 5 = 0 then some (.residue 5 1)
  else if (1 + d) % 7 = 0 then some (.residue 7 1)
  else if (4 + d) % 11 = 0 then some (.residue 11 4)
  else none

def fullRecordGapTailOwner? (d : Nat) : Option FullRecordGapOwner :=
  (recordGapPrimeList.find? (fun q => d % q == 0)).map FullRecordGapOwner.tail

def fullRecordGapSubOwner? (d : Nat) : Option FullRecordGapOwner :=
  fullRecordGapSmallSubOwner? d |>.orElse (fun _ =>
    fullRecordGapTailOwner? d |>.orElse (fun _ => fullRecordGapSubArchiveOwner? d))

def fullRecordGapAddOwner? (d : Nat) : Option FullRecordGapOwner :=
  fullRecordGapSmallAddOwner? d |>.orElse (fun _ =>
    fullRecordGapTailOwner? d |>.orElse (fun _ => fullRecordGapAddArchiveOwner? d))

{fermat_rows}

{sub_entries}

{add_entries}

def FullRecordGapSubWitnesses.offsets : List Nat :=
  fullRecordGapSubWitnesses.map FullRecordGapSubWitness.d

def FullRecordGapAddWitnesses.offsets : List Nat :=
  fullRecordGapAddWitnesses.map FullRecordGapAddWitness.d

def fullRecordGapSubOwnerValidAt (d : Fin 455704) : Prop :=
  d = 0 \u2228 match fullRecordGapSubOwner? d with
  | some owner => owner.ValidSub d
  | none => d ∈ FullRecordGapSubWitnesses.offsets

def fullRecordGapAddOwnerValidAt (d : Fin 657402) : Prop :=
  d = 0 \u2228 match fullRecordGapAddOwner? d with
  | some owner => owner.ValidAdd d
  | none => d ∈ FullRecordGapAddWitnesses.offsets

theorem fullRecordGapSubOwner_valid_or_fermat_all :
    ∀ d : Fin 455704, fullRecordGapSubOwnerValidAt d := by
  native_decide

theorem fullRecordGapAddOwner_valid_or_fermat_all :
    ∀ d : Fin 657402, fullRecordGapAddOwnerValidAt d := by
  native_decide

theorem fullRecordGapSubOwner_valid_or_fermat (d : Nat)
    (lower : 1 ≤ d) (upper : d ≤ 455703) :
    match fullRecordGapSubOwner? d with
    | some owner => owner.ValidSub d
    | none => d ∈ FullRecordGapSubWitnesses.offsets := by
  have h := fullRecordGapSubOwner_valid_or_fermat_all
    (⟨d, by omega⟩ : Fin 455704)
  simpa [fullRecordGapSubOwnerValidAt, lower.ne'] using h

theorem fullRecordGapAddOwner_valid_or_fermat (d : Nat)
    (lower : 1 ≤ d) (upper : d ≤ 657401) :
    match fullRecordGapAddOwner? d with
    | some owner => owner.ValidAdd d
    | none => d ∈ FullRecordGapAddWitnesses.offsets := by
  have h := fullRecordGapAddOwner_valid_or_fermat_all
    (⟨d, by omega⟩ : Fin 657402)
  simpa [fullRecordGapAddOwnerValidAt, lower.ne'] using h

theorem fullRecordGapSubFermat (d : Nat)
    (hd : d ∈ FullRecordGapSubWitnesses.offsets) :
    ¬(recordGapCenter - d).Prime := by
  simp only [FullRecordGapSubWitnesses.offsets, List.mem_map] at hd
  obtain ⟨w, _, rfl⟩ := hd
  exact w.not_prime

theorem fullRecordGapAddFermat (d : Nat)
    (hd : d ∈ FullRecordGapAddWitnesses.offsets) :
    ¬(recordGapCenter + d).Prime := by
  simp only [FullRecordGapAddWitnesses.offsets, List.mem_map] at hd
  obtain ⟨w, _, rfl⟩ := hd
  exact w.not_prime

theorem fullRecordGapSubBlock (d : Nat) (lower : 1 ≤ d)
    (upper : d ≤ 455703) : ¬(recordGapCenter - d).Prime := by
  have h := fullRecordGapSubOwner_valid_or_fermat d lower upper
  split at h
  · exact FullRecordGapOwner.sub_not_prime (by omega) h
  · exact fullRecordGapSubFermat d h

theorem fullRecordGapAddBlock (d : Nat) (lower : 1 ≤ d)
    (upper : d ≤ 657401) : ¬(recordGapCenter + d).Prime := by
  have h := fullRecordGapAddOwner_valid_or_fermat d lower upper
  split at h
  · exact FullRecordGapOwner.add_not_prime h
  · exact fullRecordGapAddFermat d h

end PrimeFactorUnimodality
"""
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(source)
    print(
        f"wrote {output} ({output.stat().st_size} bytes; "
        f"sub={len(sub_archive)}, add={len(add_archive)}, "
        f"sub-fermat={len(sub_fermat)}, add-fermat={len(add_fermat)})"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    render(args.output)


if __name__ == "__main__":
    main()
