#!/usr/bin/env python3
"""Generate the compact owner certificate for the 4,751-term gap sub-block.

The eight large factors below come from ``gap1113106factors.txt`` in the
published archive whose SHA-256 is pinned in ``SOURCE_ARCHIVE_SHA256``.  Every
other term except offset -84672 has an elementary prime owner at most 43103.
The exceptional offset is deliberately emitted without an owner: it requires
its own independently generated Fermat compositeness certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import TypedDict

SOURCE_ARCHIVE_SHA256 = "764ff7ee9c7c8e823d8959c1d8b4b05cdb7af2739c2ca8a3ba18bcb357f422ad"
LOW_OFFSET = -86_399
HIGH_OFFSET = -81_649
EXCEPTIONAL_OFFSET = -84_672
PRIME_LIMIT = 43_103

ARCHIVED_FACTORS: dict[int, int] = {
    -86_302: 550_631,
    -85_750: 3_020_411_447,
    -85_050: 228_523,
    -84_700: 44_983,
    -84_480: 52_103,
    -83_160: 45_541,
    -82_500: 1_291_193,
    -82_320: 1_129_577,
}


class Assignment(TypedDict):
    offset: int
    owner: int | None
    source: str


class Certificate(TypedDict):
    schema_version: int
    source_archive_sha256: str
    low_offset: int
    high_offset: int
    exceptional_offset: int
    prime_limit: int
    center_residues: dict[str, int]
    assignments: list[Assignment]
    semantic_sha256: str


def primes_up_to(limit: int) -> list[int]:
    """Return the primes at most ``limit`` by an elementary sieve."""
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for candidate in range(2, int(limit**0.5) + 1):
        if sieve[candidate]:
            start = candidate * candidate
            sieve[start : limit + 1 : candidate] = b"\x00" * ((limit - start) // candidate + 1)
    return [candidate for candidate in range(2, limit + 1) if sieve[candidate]]


def center_residue(modulus: int, primes: list[int]) -> int:
    """Compute ``587 * product(primes in [13, 43103])`` modulo ``modulus``."""
    residue = 587 % modulus
    for prime in primes:
        if prime >= 13:
            residue = residue * prime % modulus
    return residue


def semantic_hash(payload: dict[str, object]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def generate() -> Certificate:
    primes = primes_up_to(PRIME_LIMIT)
    small_primes = [2, 3, 5, 7, 11]
    residues = {str(prime): center_residue(prime, primes) for prime in small_primes}
    assignments: list[Assignment] = []

    for offset in range(LOW_OFFSET, HIGH_OFFSET + 1):
        if offset == EXCEPTIONAL_OFFSET:
            assignments.append({"offset": offset, "owner": None, "source": "fermat"})
            continue

        owner: int | None = None
        source = ""
        for prime in small_primes:
            if (residues[str(prime)] + offset) % prime == 0:
                owner = prime
                source = "removed-small-prime"
                break
        if owner is None:
            for prime in primes:
                if prime >= 13 and offset % prime == 0:
                    owner = prime
                    source = "primorial-tail-prime"
                    break
        if owner is None and offset in ARCHIVED_FACTORS:
            candidate = ARCHIVED_FACTORS[offset]
            if (center_residue(candidate, primes) + offset) % candidate != 0:
                raise ValueError(f"archived factor does not divide offset {offset}")
            owner = candidate
            source = "archived-factor"
        if owner is None:
            raise ValueError(f"uncovered offset {offset}")
        assignments.append({"offset": offset, "owner": owner, "source": source})

    body: dict[str, object] = {
        "schema_version": 1,
        "source_archive_sha256": SOURCE_ARCHIVE_SHA256,
        "low_offset": LOW_OFFSET,
        "high_offset": HIGH_OFFSET,
        "exceptional_offset": EXCEPTIONAL_OFFSET,
        "prime_limit": PRIME_LIMIT,
        "center_residues": residues,
        "assignments": assignments,
    }
    digest = semantic_hash(body)
    return {
        "schema_version": 1,
        "source_archive_sha256": SOURCE_ARCHIVE_SHA256,
        "low_offset": LOW_OFFSET,
        "high_offset": HIGH_OFFSET,
        "exceptional_offset": EXCEPTIONAL_OFFSET,
        "prime_limit": PRIME_LIMIT,
        "center_residues": residues,
        "assignments": assignments,
        "semantic_sha256": digest,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    certificate = generate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
