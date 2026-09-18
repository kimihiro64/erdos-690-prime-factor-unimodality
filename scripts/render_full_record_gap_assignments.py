#!/usr/bin/env python3
"""Render the explicit owner partition for the published full prime gap.

The output records, for every interior offset, either a divisor owner, a
center-residue owner, or the Fermat replay queue.  It is derived from the
verified historical factor/residue archives; no RES64 value is treated as a
proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import zipfile
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.audit_full_record_gap import (
    FACTOR_ARCHIVE_SHA256,
    HIGH_ENDPOINT,
    LOW_ENDPOINT,
    RESIDUE_ARCHIVE_SHA256,
    center_mod,
    file_sha256,
    one_text_member,
    parse_factors,
    parse_residues,
    smallest_prime_factors,
)
from scripts.generate_record_gap_block import PRIME_LIMIT, primes_up_to


def record_center(primes: list[int]) -> int:
    center = 587
    for prime in primes:
        if prime >= 13:
            center *= prime
    return center


def render(factors_zip: Path, residues_zip: Path) -> dict[str, Any]:
    if file_sha256(factors_zip) != FACTOR_ARCHIVE_SHA256:
        raise ValueError("factor archive SHA-256 mismatch")
    if file_sha256(residues_zip) != RESIDUE_ARCHIVE_SHA256:
        raise ValueError("residue archive SHA-256 mismatch")
    factors = parse_factors(one_text_member(factors_zip))
    residues = parse_residues(one_text_member(residues_zip))
    primes = primes_up_to(PRIME_LIMIT)
    center = record_center(primes)
    small_primes = [2, 3, 5, 7, 11]
    small_residues = {
        prime: center_mod(prime, [p for p in primes if p >= 13])
        for prime in small_primes
    }
    spf = smallest_prime_factors(max(abs(LOW_ENDPOINT), abs(HIGH_ENDPOINT)))
    fermat_offsets = {
        offset
        for offset in residues
        if offset not in factors
    }
    assignments: list[dict[str, int | str]] = []
    for offset in range(LOW_ENDPOINT + 1, HIGH_ENDPOINT):
        if offset == 0:
            continue
        small_owner = next(
            (q for q in small_primes if (small_residues[q] + offset) % q == 0),
            None,
        )
        if small_owner is not None:
            assignments.append({
                "offset": offset,
                "kind": "residue",
                "q": small_owner,
                "r": small_residues[small_owner],
            })
            continue
        rough = abs(offset)
        for q in small_primes:
            while rough % q == 0:
                rough //= q
        owner = spf[rough] if rough >= 2 else 1
        if 13 <= owner <= PRIME_LIMIT:
            assignments.append({"offset": offset, "kind": "tail", "q": owner})
            continue
        factor = factors.get(offset)
        if factor is not None:
            assignments.append({
                "offset": offset,
                "kind": "residue",
                "q": factor,
                "r": center % factor,
            })
            continue
        if offset not in fermat_offsets:
            raise ValueError(f"unclassified offset {offset}")
        assignments.append({"offset": offset, "kind": "fermat"})

    body: dict[str, Any] = {
        "schema_version": 1,
        "factor_archive_sha256": FACTOR_ARCHIVE_SHA256,
        "residue_archive_sha256": RESIDUE_ARCHIVE_SHA256,
        "low_endpoint": LOW_ENDPOINT,
        "high_endpoint": HIGH_ENDPOINT,
        "assignments": assignments,
    }
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    body["semantic_sha256"] = hashlib.sha256(encoded).hexdigest()
    return body


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("factors_zip", type=Path)
    parser.add_argument("residues_zip", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = render(args.factors_zip, args.residues_zip)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    counts: dict[str, int] = {}
    for assignment in result["assignments"]:
        kind = str(assignment["kind"])
        counts[kind] = counts.get(kind, 0) + 1
    print(json.dumps(counts, sort_keys=True))


if __name__ == "__main__":
    main()
