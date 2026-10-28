"""Persist complete exports and their exact checker binary across CI job boundaries."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import tarfile
import tempfile
from pathlib import Path
from typing import TypedDict, cast

EXPORTS = (
    "challenge.export",
    "solution.export",
    "configuration.sha256",
    "challenge.sha256",
    "solution.sha256",
)
PAYLOADS = {*EXPORTS, "comparator.bin"}
MAX_BYTES = 16 * 1024**3


class Record(TypedDict):
    bytes: int
    sha256: str


def identity(repository: str, commit: str, run_id: str) -> dict[str, str]:
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repository):
        raise ValueError("invalid checkpoint repository")
    if not re.fullmatch(r"[0-9a-f]{40}", commit) or not re.fullmatch(r"[1-9][0-9]*", run_id):
        raise ValueError("invalid checkpoint commit or run ID")
    return {"repository": repository, "commit": commit, "run_id": run_id}


def file_hash(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def pack(exports: Path, comparator: Path, archive: Path, context: dict[str, str]) -> None:
    paths = {name: exports / name for name in EXPORTS}
    paths["comparator.bin"] = comparator
    for path in paths.values():
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"checkpoint source is not a regular file: {path}")
    files: dict[str, Record] = {
        name: {"bytes": path.stat().st_size, "sha256": file_hash(path)}
        for name, path in paths.items()
    }
    if (
        any(row["bytes"] <= 0 for row in files.values())
        or sum(row["bytes"] for row in files.values()) > MAX_BYTES
    ):
        raise ValueError("checkpoint payload size outside bound")
    metadata = json.dumps(
        {"schema": 1, "identity": context, "files": files}, sort_keys=True
    ).encode()
    archive.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryFile() as manifest:
        manifest.write(metadata)
        manifest.seek(0)
        with tarfile.open(archive, "w:gz", compresslevel=1) as bundle:
            info = tarfile.TarInfo("manifest.json")
            info.size = len(metadata)
            bundle.addfile(info, manifest)
            for name, path in sorted(paths.items()):
                info = tarfile.TarInfo(name)
                info.size = files[name]["bytes"]
                info.mode = 0o755 if name == "comparator.bin" else 0o644
                with path.open("rb") as stream:
                    bundle.addfile(info, stream)
    print(
        f"Checkpoint saved: solution={files['solution.export']['bytes']} bytes; "
        f"archive={archive.stat().st_size} bytes"
    )


def restore(exports: Path, comparator: Path, archive: Path, context: dict[str, str]) -> None:
    if exports.is_symlink() or comparator.is_symlink():
        raise ValueError("checkpoint destination cannot be a symlink")
    exports.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=exports.parent) as temporary:
        staging = Path(temporary)
        with tarfile.open(archive, "r|gz") as bundle:
            members = iter(bundle)
            first = next(members, None)
            if (
                first is None
                or first.name != "manifest.json"
                or not first.isfile()
                or first.size > 65536
            ):
                raise ValueError("invalid checkpoint manifest member")
            stream = bundle.extractfile(first)
            if stream is None:
                raise ValueError("checkpoint manifest absent")
            raw: object = json.loads(stream.read())
            if (
                not isinstance(raw, dict)
                or raw.get("schema") != 1
                or raw.get("identity") != context
            ):
                raise ValueError("checkpoint identity differs from this repository, commit or run")
            files = raw.get("files")
            if not isinstance(files, dict) or set(files) != PAYLOADS:
                raise ValueError("checkpoint payload inventory differs")
            total = 0
            for record in files.values():
                if not isinstance(record, dict) or type(record.get("bytes")) is not int:
                    raise ValueError("invalid checkpoint size")
                if record["bytes"] <= 0 or not re.fullmatch(
                    r"[0-9a-f]{64}", str(record.get("sha256"))
                ):
                    raise ValueError("invalid checkpoint hash or size")
                total += record["bytes"]
            if total > MAX_BYTES:
                raise ValueError("checkpoint exceeds size bound")
            records = cast(dict[str, Record], files)
            seen: set[str] = set()
            for member in members:
                if member.name not in PAYLOADS or member.name in seen or not member.isfile():
                    raise ValueError("unexpected, duplicate or non-file checkpoint member")
                record = records[member.name]
                if member.size != record["bytes"]:
                    raise ValueError("checkpoint member size differs")
                source = bundle.extractfile(member)
                if source is None:
                    raise ValueError("checkpoint payload absent")
                digest = hashlib.sha256()
                with (staging / member.name).open("wb") as destination:
                    while block := source.read(1024 * 1024):
                        digest.update(block)
                        destination.write(block)
                if digest.hexdigest() != record["sha256"]:
                    raise ValueError("checkpoint payload checksum differs")
                seen.add(member.name)
            if seen != PAYLOADS:
                raise ValueError("checkpoint payload missing")
        exports.mkdir(parents=True, exist_ok=True)
        comparator.parent.mkdir(parents=True, exist_ok=True)
        for name in EXPORTS:
            os.replace(staging / name, exports / name)
        os.replace(staging / "comparator.bin", comparator)
        comparator.chmod(0o755)
    print(f"Checkpoint verified: solution={records['solution.export']['bytes']} bytes")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("pack", "restore"))
    parser.add_argument("--exports", type=Path, required=True)
    parser.add_argument("--comparator", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--run-id", required=True)
    args = parser.parse_args()
    context = identity(args.repository, args.commit, args.run_id)
    operation = pack if args.command == "pack" else restore
    operation(args.exports, args.comparator, args.archive, context)


if __name__ == "__main__":
    main()
