#!/usr/bin/env python3
"""Audit and compact the published full 1,113,106 prime-gap certificate.

The two historical ZIP files split the interior into explicit factors and
PFGW compositeness tests.  This script independently reconstructs the cheap
primorial owners, verifies every listed factor modulo its claimed divisor,
and checks that the residue log covers every remaining interior offset.

It deliberately does not treat a ``RES64`` checksum as a proof.  The emitted
Fermat-offset list is the work queue for later kernel replay in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import zipfile
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.generate_record_gap_block import PRIME_LIMIT, primes_up_to

LOW_ENDPOINT = -455_704
HIGH_ENDPOINT = 657_402
FACTOR_ARCHIVE_SHA256 = "764ff7ee9c7c8e823d8959c1d8b4b05cdb7af2739c2ca8a3ba18bcb357f422ad"
RESIDUE_ARCHIVE_SHA256 = "4bf239672c0d9a293f837bbc424c1bcd488940ed654297d44a2014ce37bb2346"

FACTOR_LINE = re.compile(r"^\s*(-?\d+)\s+(\d+)\s*$")
RESIDUE_LINE = re.compile(
    r"^587\*43103#/2310(?P<offset>[+-]\d+) is composite: RES64: "
    r"\[(?P<checksum>[0-9A-F]{16})\]"
)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def one_text_member(path: Path) -> str:
    with zipfile.ZipFile(path) as archive:
        members = [name for name in archive.namelist() if not name.endswith("/")]
        if len(members) != 1:
            raise ValueError(f"expected one member in {path}, found {members}")
        return archive.read(members[0]).decode("ascii")


def parse_factors(text: str) -> dict[int, int]:
    result: dict[int, int] = {}
    for line in text.splitlines():
        match = FACTOR_LINE.match(line)
        if match is None:
            continue
        offset, factor = map(int, match.groups())
        if offset in result:
            raise ValueError(f"duplicate factor offset {offset}")
        result[offset] = factor
    return result


def parse_residues(text: str) -> dict[int, str]:
    result: dict[int, str] = {}
    for line in text.splitlines():
        match = RESIDUE_LINE.match(line)
        if match is None:
            continue
        offset = int(match.group("offset"))
        if offset in result:
            raise ValueError(f"duplicate residue offset {offset}")
        result[offset] = match.group("checksum")
    return result


def center_mod(modulus: int, tail_primes: list[int]) -> int:
    value = 587 % modulus
    for prime in tail_primes:
        value = value * prime % modulus
    return value


def smallest_prime_factors(limit: int) -> list[int]:
    factors = list(range(limit + 1))
    if limit >= 1:
        factors[1] = 1
    for prime in range(2, int(limit**0.5) + 1):
        if factors[prime] != prime:
            continue
        for multiple in range(prime * prime, limit + 1, prime):
            if factors[multiple] == multiple:
                factors[multiple] = prime
    return factors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("factors_zip", type=Path)
    parser.add_argument("residues_zip", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if file_sha256(args.factors_zip) != FACTOR_ARCHIVE_SHA256:
        raise ValueError("factor archive SHA-256 mismatch")
    if file_sha256(args.residues_zip) != RESIDUE_ARCHIVE_SHA256:
        raise ValueError("residue archive SHA-256 mismatch")

    factors = parse_factors(one_text_member(args.factors_zip))
    residues = parse_residues(one_text_member(args.residues_zip))
    primes = primes_up_to(PRIME_LIMIT)
    tail_primes = [prime for prime in primes if prime >= 13]
    center = 587
    for prime in tail_primes:
        center *= prime
    center_residues = {
        prime: center_mod(prime, tail_primes) for prime in (2, 3, 5, 7, 11)
    }
    spf = smallest_prime_factors(max(abs(LOW_ENDPOINT), abs(HIGH_ENDPOINT)))

    small_owner_count = 0
    archive_owner_count = 0
    fermat_offsets: list[int] = []
    used_factor_offsets: set[int] = set()
    used_residue_offsets: set[int] = set()

    for offset in range(LOW_ENDPOINT + 1, HIGH_ENDPOINT):
        owned = any(
            (center_residues[prime] + offset) % prime == 0
            for prime in center_residues
        )
        absolute = abs(offset)
        if not owned and absolute == 0:
            owned = True
        if not owned and absolute >= 2:
            rough_part = absolute
            for removed_prime in center_residues:
                while rough_part % removed_prime == 0:
                    rough_part //= removed_prime
            owner = spf[rough_part] if rough_part >= 2 else 1
            owned = 13 <= owner <= PRIME_LIMIT
        if owned:
            small_owner_count += 1
            continue

        factor = factors.get(offset)
        if factor is not None:
            if factor <= PRIME_LIMIT:
                raise ValueError(f"archive factor {factor} was not classified cheaply")
            if (center + offset) % factor:
                raise ValueError(f"listed factor {factor} fails at offset {offset}")
            archive_owner_count += 1
            used_factor_offsets.add(offset)
            continue

        if offset not in residues:
            raise ValueError(f"uncovered interior offset {offset}")
        fermat_offsets.append(offset)
        used_residue_offsets.add(offset)

    unused_factors = sorted(set(factors) - used_factor_offsets)
    unused_residues = sorted(set(residues) - used_residue_offsets)
    if unused_factors:
        raise ValueError(f"unused factor offsets, first values: {unused_factors[:10]}")
    if unused_residues:
        raise ValueError(f"unused residue offsets, first values: {unused_residues[:10]}")

    payload = {
        "schema_version": 1,
        "factor_archive_sha256": FACTOR_ARCHIVE_SHA256,
        "residue_archive_sha256": RESIDUE_ARCHIVE_SHA256,
        "low_endpoint": LOW_ENDPOINT,
        "high_endpoint": HIGH_ENDPOINT,
        "interior_count": HIGH_ENDPOINT - LOW_ENDPOINT - 1,
        "small_owner_count": small_owner_count,
        "archive_owner_count": archive_owner_count,
        "fermat_count": len(fermat_offsets),
        "fermat_offsets": fermat_offsets,
        "res64_checksums": {str(offset): residues[offset] for offset in fermat_offsets},
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["semantic_sha256"] = hashlib.sha256(encoded).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        f"audited {payload['interior_count']} interior offsets: "
        f"{small_owner_count} cheap, {archive_owner_count} factored, "
        f"{len(fermat_offsets)} require kernel Fermat replay"
    )


if __name__ == "__main__":
    main()
