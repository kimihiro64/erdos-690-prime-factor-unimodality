"""Plan, replay, and verify cacheable record-gap certificate shards."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import TypedDict, cast

ROOT = Path(__file__).resolve().parent.parent
RELATIVE = Path("PrimeFactorUnimodality/Proof/LargeRange/Generated/FullRecordGapCompactRows")
DIRECTORY = ROOT / RELATIVE
MODULE = str(RELATIVE).replace("/", ".")


class Shard(TypedDict):
    id: str
    rows: list[str]
    target: str


class Manifest(TypedDict):
    schema: int
    offsets: int
    exceptions: int
    row_sha256: str
    owners_target: str
    shards: list[Shard]


def manifest() -> Manifest:
    data = cast(Manifest, json.loads((DIRECTORY / "manifest.json").read_text()))
    if data["schema"] != 1 or data["offsets"] != 1113104 or data["exceptions"] != 10918:
        raise ValueError("invalid record-gap manifest")
    ids = [shard["id"] for shard in data["shards"]]
    rows = [row for shard in data["shards"] for row in shard["rows"]]
    if len(ids) != len(set(ids)) or len(rows) != len(set(rows)) or not rows:
        raise ValueError("duplicate or empty replay shards")
    if rows != [f"{i:03d}" for i in range(1, len(rows) + 1)]:
        raise ValueError("incomplete replay row sequence")
    if not 1 <= len(ids) <= 256:
        raise ValueError("matrix exceeds GitHub's job limit")
    if data["owners_target"] != f"{MODULE}.Owners{rows[-1]}":
        raise ValueError("incorrect owner-chain terminal")
    for shard in data["shards"]:
        if not 1 <= len(shard["rows"]) <= 2:
            raise ValueError("unbounded replay shard")
        if shard["target"] != f"{MODULE}.Replay{shard['rows'][-1]}":
            raise ValueError("incorrect replay-chain terminal")
    return data


def source_key() -> str:
    paths = [ROOT / "lean-toolchain", ROOT / "lake-manifest.json"]
    paths += sorted(DIRECTORY.glob("*"))
    paths += sorted((ROOT / "PrimeFactorUnimodality/Helpers/Arithmetic").glob("*.lean"))
    paths += sorted((ROOT / "PrimeFactorUnimodality/Proof/LargeRange").glob("CompactGap*.lean"))
    paths += [DIRECTORY.parent / "FullRecordGapCenterValue.lean"]
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0")
        digest.update(path.read_bytes())
    return digest.hexdigest()[:24]


def build(target: str) -> None:
    started = time.monotonic()
    print(f"::group::Record-gap target {target}", flush=True)
    try:
        with subprocess.Popen(["lake", "-v", "build", f"+{target}"], cwd=ROOT) as process:
            while True:
                try:
                    status = process.wait(timeout=30)
                    if status:
                        raise subprocess.CalledProcessError(status, process.args)
                    break
                except subprocess.TimeoutExpired:
                    elapsed = time.monotonic() - started
                    print(f"Still building {target}: {elapsed:.0f}s", flush=True)
                    snapshot = subprocess.run(
                        ["ps", "-eo", "pid,ppid,rss,etime,args", "--sort=-rss"],
                        check=False,
                        stdout=subprocess.PIPE,
                        text=True,
                    )
                    print("\n".join(snapshot.stdout.splitlines()[:8]), flush=True)
    finally:
        print(f"Target {target}: elapsed {time.monotonic() - started:.1f}s", flush=True)
        print("::endgroup::", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--matrix", action="store_true")
    mode.add_argument("--source-key", action="store_true")
    mode.add_argument("--owners", action="store_true")
    mode.add_argument("--shard")
    mode.add_argument("--require-artifacts", action="store_true")
    args = parser.parse_args()
    data = manifest()
    if args.matrix:
        print(json.dumps([shard["id"] for shard in data["shards"]], separators=(",", ":")))
    elif args.source_key:
        print(source_key())
    elif args.owners:
        build(data["owners_target"])
    elif args.shard:
        shard = next(item for item in data["shards"] if item["id"] == args.shard)
        for row in shard["rows"]:
            build(f"{MODULE}.Replay{row}")
    else:
        missing = []
        for shard in data["shards"]:
            for row in shard["rows"]:
                for suffix in (".olean", ".trace"):
                    path = ROOT / ".lake/build/lib/lean" / RELATIVE / f"Replay{row}{suffix}"
                    if not path.is_file():
                        missing.append(str(path.relative_to(ROOT)))
        if missing:
            raise SystemExit(
                "Missing replay artifacts; refusing parallel rebuild:\n" + "\n".join(missing)
            )


if __name__ == "__main__":
    main()
