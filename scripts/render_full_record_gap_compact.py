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


def lean_nat_list(values: list[int]) -> str:
    """Render offset data without emitting one declaration per witness."""
    return "[\n    " + ",\n    ".join(str(value) for value in values) + "\n  ]"


def render(output: Path) -> None:
    sub_archive, add_archive, sub_fermat, add_fermat = classify()
    source = f"""import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapOwnerRows

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

structure FullRecordGapArchiveRow where
  d : Nat
  q : Nat
  r : Nat

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

/-! Exceptional offsets are data.  The list-level certificates below are
    reused for every member by the block theorems. -/

def fullRecordGapSubFermatOffsets : List Nat :=
  {lean_nat_list(sorted(sub_fermat))}

def fullRecordGapAddFermatOffsets : List Nat :=
  {lean_nat_list(sorted(add_fermat))}

def FullRecordGapSubWitnesses.offsets : List Nat :=
  fullRecordGapSubFermatOffsets

def FullRecordGapAddWitnesses.offsets : List Nat :=
  fullRecordGapAddFermatOffsets

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
  decide

theorem fullRecordGapAddOwner_valid_or_fermat_all :
    ∀ d : Fin 657402, fullRecordGapAddOwnerValidAt d := by
  decide

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

set_option maxHeartbeats 0 in
theorem fullRecordGapSubFermatCertificate :
    fullRecordGapSubFermatOffsets.all (fun d =>
      decide (fastPowMod 3 (fullRecordGapCenterValue - d)
        (fullRecordGapCenterValue - d - 1) ≠ 1)) = true := by
  decide

set_option maxHeartbeats 0 in
theorem fullRecordGapAddFermatCertificate :
    fullRecordGapAddFermatOffsets.all (fun d =>
      decide (fastPowMod 3 (fullRecordGapCenterValue + d)
        (fullRecordGapCenterValue + d - 1) ≠ 1)) = true := by
  decide

theorem fullRecordGapSubFermat (d : Nat)
    (hd : d ∈ FullRecordGapSubWitnesses.offsets) :
    ¬(recordGapCenter - d).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · have hd_upper : d ≤ 455703 := by
      have h : ∀ d ∈ fullRecordGapSubFermatOffsets, d ≤ 455703 := by
        decide
      exact h d hd
    omega
  · have h := List.all_eq_true.mp fullRecordGapSubFermatCertificate d hd
    exact of_decide_eq_true h

theorem fullRecordGapAddFermat (d : Nat)
    (hd : d ∈ FullRecordGapAddWitnesses.offsets) :
    ¬(recordGapCenter + d).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · omega
  · have h := List.all_eq_true.mp fullRecordGapAddFermatCertificate d hd
    exact of_decide_eq_true h

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
