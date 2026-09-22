#!/usr/bin/env python3
"""Render the compact full-record owner rows and reusable block assemblers."""

from __future__ import annotations

import argparse
import io
import re
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
    return "[" + ",\n    ".join(f"{{d := {d}, q := {q}, r := {r}}}" for d, q, r in rows) + "]"


def lean_nat_list(values: list[int]) -> str:
    """Render offset data without emitting one declaration per witness."""
    return "[\n    " + ",\n    ".join(str(value) for value in values) + "\n  ]"


def lean_archive_lookup(prefix: str, rows: list[tuple[int, int, int]]) -> str:
    """Render compact rows with a logarithmic executable lookup."""
    return f"""def {prefix}Rows : List FullRecordGapArchiveRow :=
  {lean_list(rows)}

def {prefix} (d : Nat) : Option FullRecordGapOwner :=
  match {prefix}Rows.find? (fun row => row.d == d) with
  | some row => some (.residue row.q row.r)
  | none => none"""


def owner_certificates() -> str:
    """Assemble bounded owner proofs from small, independently reducible rows."""
    chunk_size = 128
    specs = [("Sub", 455704), ("Add", 657402)]
    chunks: list[tuple[str, int, int, int]] = []
    lines: list[str] = []
    for side, bound in specs:
        count = (bound + chunk_size - 1) // chunk_size
        for index in range(count):
            offset = index * chunk_size
            size = min(chunk_size, bound - offset)
            chunks.append((side, index, offset, size))
            lines.append(
                "set_option maxHeartbeats 0 in\n"
                f"theorem fullRecordGap{side}Owner_valid_chunk_{index:04d} :\n"
                f"    ∀ i : Fin {size}, fullRecordGap{side}OwnerValidAt\n"
                f"      ⟨{offset} + i.1, by omega⟩ := by\n"
                "  intro i\n"
                f"  fin_cases i <;> apply fullRecordGap{side}OwnerValidAt_of_bool <;> decide\n"
            )
    for side, bound in specs:
        side_chunks = [item for item in chunks if item[0] == side]
        lines.append(
            f"theorem fullRecordGap{side}Owner_valid_or_fermat_all :\n"
            f"    ∀ d : Fin {bound}, fullRecordGap{side}OwnerValidAt d := by\n"
            "  intro d\n"
        )
        for position, (_, index, offset, size) in enumerate(side_chunks):
            if position < len(side_chunks) - 1:
                lines.append(f"  by_cases h{index} : d.1 < {offset + size}\n")
                lines.append(
                    f"  · convert fullRecordGap{side}Owner_valid_chunk_"
                    f"{index:04d} ⟨d.1 - {offset}, by omega⟩ using 1 <;> "
                    "apply Fin.ext <;> omega\n"
                )
                lines.append("  ·")
            else:
                lines.append(
                    f"  convert fullRecordGap{side}Owner_valid_chunk_"
                    f"{index:04d} ⟨d.1 - {offset}, by omega⟩ using 1 <;> "
                    "apply Fin.ext <;> omega\n"
                )
        lines.append("")
    return "\n".join(lines)


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

{lean_archive_lookup("fullRecordGapSubArchiveOwner?", sub_archive)}

{lean_archive_lookup("fullRecordGapAddArchiveOwner?", add_archive)}

def fullRecordGapSmallSubOwner? (d : Nat) : Option FullRecordGapOwner :=
  if (1 + d) % 2 = 0 then some (.residue 2 1)
  else if d % 3 = 2 then some (.residue 3 2)
  else if d % 5 = 1 then some (.residue 5 1)
  else if d % 7 = 1 then some (.residue 7 1)
  else if d % 11 = 4 then some (.residue 11 4)
  else none

def fullRecordGapSmallAddOwner? (d : Nat) : Option FullRecordGapOwner :=
  if (1 + d) % 2 = 0 then some (.residue 2 1)
  else if (2 + d) % 3 = 0 then some (.residue 3 2)
  else if (1 + d) % 5 = 0 then some (.residue 5 1)
  else if (1 + d) % 7 = 0 then some (.residue 7 1)
  else if (4 + d) % 11 = 0 then some (.residue 11 4)
  else none

def fullRecordGapTailOwner? (d : Nat) : Option FullRecordGapOwner :=
  let rough := d / (2 ^ padicValNat 2 d * 3 ^ padicValNat 3 d *
    5 ^ padicValNat 5 d * 7 ^ padicValNat 7 d * 11 ^ padicValNat 11 d)
  if rough < 2 then none
  else
    let q := Nat.minFac rough
    if 13 ≤ q ∧ q ≤ 43_103 then some (.tail q) else none

def fullRecordGapSubOwner? (d : Nat) : Option FullRecordGapOwner :=
  fullRecordGapSmallSubOwner? d |>.orElse (fun _ =>
    fullRecordGapSubArchiveOwner? d |>.orElse (fun _ => fullRecordGapTailOwner? d))

def fullRecordGapAddOwner? (d : Nat) : Option FullRecordGapOwner :=
  fullRecordGapSmallAddOwner? d |>.orElse (fun _ =>
    fullRecordGapAddArchiveOwner? d |>.orElse (fun _ => fullRecordGapTailOwner? d))

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
  | none => d.1 ∈ FullRecordGapSubWitnesses.offsets

def fullRecordGapAddOwnerValidAt (d : Fin 657402) : Prop :=
  d = 0 \u2228 match fullRecordGapAddOwner? d with
  | some owner => owner.ValidAdd d
  | none => d.1 ∈ FullRecordGapAddWitnesses.offsets

def fullRecordGapSubOwnerValidAtBool (d : Nat) : Bool :=
  if d = 0 then true else
    match fullRecordGapSubOwner? d with
    | some owner => decide (owner.ValidSub d)
    | none => decide (d ∈ FullRecordGapSubWitnesses.offsets)

def fullRecordGapAddOwnerValidAtBool (d : Nat) : Bool :=
  if d = 0 then true else
    match fullRecordGapAddOwner? d with
    | some owner => decide (owner.ValidAdd d)
    | none => decide (d ∈ FullRecordGapAddWitnesses.offsets)

theorem fullRecordGapSubOwnerValidAt_of_bool {{d : Fin 455704}}
    (h : fullRecordGapSubOwnerValidAtBool d = true) :
    fullRecordGapSubOwnerValidAt d := by
  by_cases hz : d = 0
  · exact Or.inl hz
  · right
    cases ho : fullRecordGapSubOwner? d with
    | none =>
        have hb : decide (d.1 ∈ FullRecordGapSubWitnesses.offsets) = true := by
          simpa [fullRecordGapSubOwnerValidAtBool, hz, ho] using h
        simpa [ho] using of_decide_eq_true hb
    | some owner =>
        have hb : decide (owner.ValidSub d) = true := by
          simpa [fullRecordGapSubOwnerValidAtBool, hz, ho] using h
        simpa [ho] using of_decide_eq_true hb
theorem fullRecordGapAddOwnerValidAt_of_bool {{d : Fin 657402}}
    (h : fullRecordGapAddOwnerValidAtBool d = true) :
    fullRecordGapAddOwnerValidAt d := by
  by_cases hz : d = 0
  · exact Or.inl hz
  · right
    cases ho : fullRecordGapAddOwner? d with
    | none =>
        have hb : decide (d.1 ∈ FullRecordGapAddWitnesses.offsets) = true := by
          simpa [fullRecordGapAddOwnerValidAtBool, hz, ho] using h
        simpa [ho] using of_decide_eq_true hb
    | some owner =>
        have hb : decide (owner.ValidAdd d) = true := by
          simpa [fullRecordGapAddOwnerValidAtBool, hz, ho] using h
        simpa [ho] using of_decide_eq_true hb
{owner_certificates()}
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
    if output.name == "FullRecordGapCompact.lean":
        sub_rows_marker = "def fullRecordGapSubArchiveOwner?Rows"
        add_rows_marker = "def fullRecordGapAddArchiveOwner?Rows"
        sub_lookup_marker = "def fullRecordGapSubArchiveOwner? (d"
        add_lookup_marker = "def fullRecordGapAddArchiveOwner? (d"
        small_owner_marker = "def fullRecordGapSmallSubOwner? (d"
        chunk_marker = (
            "set_option maxHeartbeats 0 in\ntheorem fullRecordGapSubOwner_valid_chunk_0000"
        )
        assembly_marker = "theorem fullRecordGapSubOwner_valid_or_fermat_all"
        data_header, remainder = source.split(sub_rows_marker, 1)
        sub_rows, remainder = remainder.split(sub_lookup_marker, 1)
        sub_lookup, remainder = remainder.split(add_rows_marker, 1)
        add_rows, remainder = remainder.split(add_lookup_marker, 1)
        add_lookup, remainder = remainder.split(small_owner_marker, 1)
        small_owner_body, remainder = remainder.split(chunk_marker, 1)
        sub_rows = sub_rows_marker + sub_rows
        add_rows = add_rows_marker + add_rows
        owner_body = (
            sub_lookup_marker
            + sub_lookup
            + add_lookup_marker
            + add_lookup
            + small_owner_marker
            + small_owner_body
        )
        prefix = (
            "import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod\n"
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter\n"
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
            "FullRecordGapCompactAddData\n\n"
            "set_option autoImplicit false\n"
            "set_option maxRecDepth 10000000\n"
            "set_option linter.style.longLine false\n\n"
            "/-! Generated compact owner rows and their serial certificate chain. -/\n\n"
            "namespace PrimeFactorUnimodality\n\n"
        )
        remainder = chunk_marker + remainder
        chunk_text, assembly = remainder.split(assembly_marker, 1)
        chunk_matches = re.findall(
            r"(?:set_option maxHeartbeats 0 in\n)?"
            r"theorem fullRecordGap(?:Sub|Add)Owner_valid_chunk_.*?"
            r"(?=(?:set_option maxHeartbeats 0 in\n)?"
            r"theorem fullRecordGap(?:Sub|Add)Owner_valid_chunk_|$)",
            chunk_text,
            flags=re.S,
        )
        data = output.with_name("FullRecordGapCompactData.lean")
        data.write_text(
            data_header.replace(
                "namespace PrimeFactorUnimodality\n",
                "/-! Shared generated archive-row structure. -/\n\n"
                "namespace PrimeFactorUnimodality\n",
                1,
            )
            + "end PrimeFactorUnimodality\n"
        )
        sub_data = output.with_name("FullRecordGapCompactSubData.lean")
        sub_data.write_text(
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCompactData\n"
            "set_option maxRecDepth 10000000\n\n"
            "/-! Generated subtraction archive rows. -/\n\n"
            "namespace PrimeFactorUnimodality\n\n" + sub_rows + "\nend PrimeFactorUnimodality\n"
        )
        add_data = output.with_name("FullRecordGapCompactAddData.lean")
        add_data.write_text(
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCompactSubData\n"
            "set_option maxRecDepth 10000000\n\n"
            "/-! Generated addition archive rows. -/\n\n"
            "namespace PrimeFactorUnimodality\n\n" + add_rows + "\nend PrimeFactorUnimodality\n"
        )
        base = output.with_name("FullRecordGapCompactBase.lean")
        base.write_text(prefix + owner_body + "end PrimeFactorUnimodality\n")
        previous = base.stem
        group_size = 32
        for group_start in range(0, len(chunk_matches), group_size):
            group = chunk_matches[group_start : group_start + group_size]
            part_number = group_start // group_size + 1
            part = output.with_name(f"FullRecordGapCompactOwnerPart{part_number:02d}.lean")
            part.write_text(
                f"import PrimeFactorUnimodality.Proof.LargeRange.Generated.{previous}\n\n"
                "set_option maxRecDepth 10000000\n\n"
                "/-! Generated bounded owner certificate rows. -/\n\n"
                "namespace PrimeFactorUnimodality\n\n"
                + "\n".join(group)
                + "\nend PrimeFactorUnimodality\n"
            )
            previous = part.stem
        output.write_text(
            f"import PrimeFactorUnimodality.Proof.LargeRange.Generated.{previous}\n\n"
            "/-! Compact full-record certificate assembly. -/\n\n"
            "namespace PrimeFactorUnimodality\n\n" + assembly + "\nend PrimeFactorUnimodality\n"
        )
    else:
        output.write_text(source)
    print(
        f"wrote {output} ({output.stat().st_size} bytes; "
        f"sub={len(sub_archive)}, add={len(add_archive)}, "
        f"sub-fermat={len(sub_fermat)}, add-fermat={len(add_fermat)})"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    render(parser.parse_args().output)


if __name__ == "__main__":
    main()
