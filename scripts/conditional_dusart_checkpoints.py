"""Validated, content-addressed build bundles stored as draft release assets.

These are build checkpoints, not mathematical releases or proof certificates.
Only the trusted manual workflow may upload them. Lake still validates its
normal dependency traces after restoration.
"""

from __future__ import annotations

import hashlib
import io
import json
import shutil
import subprocess
import tarfile
from pathlib import Path
from typing import IO

from scripts.conditional_dusart_plan import Unit, artifact_paths, required_artifacts


def file_hash(stream: IO[bytes]) -> str:
    digest = hashlib.sha256()
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(block)
    return digest.hexdigest()


def pack(root: Path, unit: Unit, archive: Path) -> None:
    paths = [path for path in artifact_paths(unit) if (root / path).is_file()]
    if not required_artifacts(unit) <= set(paths):
        raise ValueError("cannot checkpoint incomplete Lean output")
    hashes: dict[str, str] = {}
    with tarfile.open(archive, "w:gz", compresslevel=1) as bundle:
        for path in paths:
            source = root / path
            if source.is_symlink():
                raise ValueError(f"symlink artifact: {path}")
            with source.open("rb") as stream:
                hashes[path.as_posix()] = file_hash(stream)
            bundle.add(source, arcname=path.as_posix(), recursive=False)
        metadata = json.dumps({"key": unit.key, "files": hashes}, sort_keys=True).encode()
        info = tarfile.TarInfo("checkpoint.json")
        info.size = len(metadata)
        bundle.addfile(info, io.BytesIO(metadata))
    if archive.stat().st_size >= 2_000_000_000:
        raise ValueError("checkpoint exceeds release asset limit; reduce unit size")


def restore(root: Path, unit: Unit, archive: Path) -> None:
    allowed = {path.as_posix() for path in artifact_paths(unit)}
    with tarfile.open(archive, "r:gz") as bundle:
        members = bundle.getmembers()
        names = [member.name for member in members]
        if len(names) != len(set(names)) or not all(member.isfile() for member in members):
            raise ValueError("duplicate or nonregular archive member")
        if not set(names) <= allowed | {"checkpoint.json"}:
            raise ValueError("unexpected archive path")
        metadata_file = bundle.extractfile("checkpoint.json")
        if metadata_file is None:
            raise ValueError("missing checkpoint metadata")
        metadata = json.load(metadata_file)
        hashes = metadata["files"]
        if metadata["key"] != unit.key or set(hashes) != set(names) - {"checkpoint.json"}:
            raise ValueError("checkpoint identity mismatch")
        if not {path.as_posix() for path in required_artifacts(unit)} <= set(hashes):
            raise ValueError("incomplete checkpoint")
        # Validate the entire archive before overwriting any existing build output.
        for name, expected in hashes.items():
            target = root / name
            if any(path.is_symlink() for path in (target, *target.parents)):
                raise ValueError("symlink destination")
            stream = bundle.extractfile(name)
            if stream is None or file_hash(stream) != expected:
                raise ValueError(f"artifact digest mismatch: {name}")
        for name in hashes:
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            stream = bundle.extractfile(name)
            assert stream is not None
            with target.open("wb") as output:
                shutil.copyfileobj(stream, output)


class Store:
    """Never overwrite a saved asset or convert a checkpoint into a release."""

    def __init__(self, repo: str, phase: str, commit: str) -> None:
        self.repo = repo
        self.tag = f"conditional-proof-checkpoints-v1-{phase}"
        endpoint = f"repos/{repo}/releases/tags/{self.tag}"
        result = subprocess.run(["gh", "api", endpoint], capture_output=True, text=True)
        if result.returncode:
            if "404" not in result.stderr:
                raise RuntimeError(result.stderr)
            result = subprocess.run(
                [
                    "gh",
                    "api",
                    f"repos/{repo}/releases",
                    "--method",
                    "POST",
                    "-f",
                    f"tag_name={self.tag}",
                    "-f",
                    f"target_commitish={commit}",
                    "-F",
                    "draft=true",
                    "-f",
                    f"name={self.tag}",
                    "-f",
                    "body=Internal build checkpoints; not a verified mathematical release.",
                ],
                check=True,
                capture_output=True,
                text=True,
            )
        release = json.loads(result.stdout)
        if not release["draft"]:
            raise ValueError("checkpoint store must remain a draft")
        listing = subprocess.run(
            [
                "gh",
                "api",
                f"repos/{repo}/releases/{release['id']}/assets",
                "--paginate",
                "--jq",
                ".[].name",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        self.assets = set(listing.stdout.splitlines())

    def download(self, unit: Unit, directory: Path) -> Path | None:
        if unit.asset not in self.assets:
            return None
        subprocess.run(
            [
                "gh",
                "release",
                "download",
                self.tag,
                "--repo",
                self.repo,
                "--pattern",
                unit.asset,
                "--dir",
                str(directory),
            ],
            check=True,
        )
        return directory / unit.asset

    def upload(self, unit: Unit, archive: Path) -> None:
        if unit.asset in self.assets:
            return
        if len(self.assets) >= 950:
            raise ValueError(
                "checkpoint store near asset limit; rotate its version, preserving old data"
            )
        subprocess.run(
            ["gh", "release", "upload", self.tag, str(archive), "--repo", self.repo],
            check=True,
        )
        self.assets.add(unit.asset)
