#!/usr/bin/env python3
"""Generate positional factor rows, bounded replays, and their CI manifest."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
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
from scripts.fetch_record_gap_archive import ARTIFACTS, fetch_payload
from scripts.full_record_gap_compact_helpers import (
    GENERATED,
    ROWS_PER_SHARD,
    make_rows,
    render_aggregate,
    render_assembly,
    render_owners,
    render_replay,
)
from scripts.generate_record_gap_block import PRIME_LIMIT, primes_up_to
from scripts.render_full_record_gap_fermat import record_center, render_center, render_center_value

ROOT = Path(__file__).resolve().parent.parent


def archive_text(kind: str, cache: Path) -> str:
    path = cache / f"record-gap-{kind}.zip"
    payload = path.read_bytes() if path.exists() else fetch_payload(kind)
    if hashlib.sha256(payload).hexdigest() != ARTIFACTS[kind]["sha256"]:
        raise ValueError(f"{kind} archive digest mismatch")
    cache.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)
    with zipfile.ZipFile(io.BytesIO(payload)) as archive:
        members = [name for name in archive.namelist() if not name.endswith("/")]
        if len(members) != 1:
            raise ValueError(f"expected one archive member, found {members}")
        return archive.read(members[0]).decode("ascii")


def classify(cache: Path) -> tuple[list[int], list[int]]:
    factors = parse_factors(archive_text("factors", cache))
    residues = parse_residues(archive_text("residues", cache))
    center = 587
    for q in primes_up_to(PRIME_LIMIT):
        if q >= 13:
            center *= q
    small_residues = {q: center % q for q in (2, 3, 5, 7, 11)}
    spf = smallest_prime_factors(max(-LOW_ENDPOINT, HIGH_ENDPOINT))
    sides: list[list[int]] = []
    for sign, stop in ((-1, -LOW_ENDPOINT), (1, HIGH_ENDPOINT)):
        owners: list[int] = []
        for d in range(1, stop):
            offset = sign * d
            q = next((p for p, r in small_residues.items() if (r + offset) % p == 0), 0)
            if not q:
                rough = d
                for p in small_residues:
                    while rough % p == 0:
                        rough //= p
                tail = spf[rough] if rough >= 2 else 1
                if 13 <= tail <= PRIME_LIMIT:
                    q = tail
            if not q:
                q = factors.get(offset, 0)
            if q:
                if not (2 <= q < center + offset and (center + offset) % q == 0):
                    raise ValueError(f"invalid factor {q} at {offset}")
            elif offset not in residues:
                raise ValueError(f"unclassified offset {offset}")
            owners.append(q)
        sides.append(owners)
    if [side.count(0) for side in sides] != [3815, 7103]:
        raise ValueError("unexpected Fermat exception cardinalities")
    return sides[0], sides[1]


def render(output: Path, cache: Path, *, sample: bool = False) -> None:
    sys.set_int_max_str_digits(20000)
    center = record_center()
    output.with_name("FullRecordGapCenterValue.lean").write_text(render_center_value(center))
    output.with_name("FullRecordGapCenter.lean").write_text(render_center(center))
    sub, add = classify(cache)
    rows = make_rows("Sub", sub, 1)
    rows += make_rows("Add", add, len(rows) + 1)
    directory = output.with_name("FullRecordGapCompactRows")
    directory.mkdir(parents=True, exist_ok=True)
    selected = rows[:1] if sample else rows
    shards: list[dict[str, object]] = []
    previous = None
    shard_count = 0
    shard_exceptions = 0
    for index, row in enumerate(selected):
        count = row.factors.count(0)
        if count > 100:
            raise ValueError("single row exceeds the replay budget; reduce ROW_SIZE")
        if index == 0 or shard_count == ROWS_PER_SHARD or shard_exceptions + count > 100:
            shards.append({"id": f"{len(shards) + 1:03d}", "rows": []})
            previous = None
            shard_count = 0
            shard_exceptions = 0
        (directory / f"Owners{row.tag}.lean").write_text(render_owners(row))
        (directory / f"Replay{row.tag}.lean").write_text(render_replay(row, previous))
        shard_rows = shards[-1]["rows"]
        assert isinstance(shard_rows, list)
        shard_rows.append(row.tag)
        shards[-1]["target"] = f"{GENERATED}.Replay{row.tag}"
        previous = row
        shard_count += 1
        shard_exceptions += count
    if sample:
        return
    assembly_count = 0
    for start in range(0, len(rows), 32):
        assembly_count += 1
        path = directory / f"Assembly{assembly_count:03d}.lean"
        path.write_text(render_assembly(rows[start : start + 32], assembly_count))
    output.write_text(render_aggregate(rows, [f"{GENERATED}.Assembly{assembly_count:03d}"]))
    digest = hashlib.sha256(json.dumps([sub, add], separators=(",", ":")).encode()).hexdigest()
    manifest = {
        "schema": 1,
        "archives": {kind: value["sha256"] for kind, value in ARTIFACTS.items()},
        "row_sha256": digest,
        "offsets": len(sub) + len(add),
        "exceptions": sub.count(0) + add.count(0),
        "owners_target": f"{GENERATED}.Owners{rows[-1].tag}",
        "shards": shards,
    }
    (directory / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"wrote {len(rows)} positional rows in {len(shards)} bounded replay shards")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--archive-cache", type=Path, default=ROOT / ".research")
    parser.add_argument("--sample", action="store_true")
    args = parser.parse_args()
    render(args.output, args.archive_cache, sample=args.sample)


if __name__ == "__main__":
    main()
