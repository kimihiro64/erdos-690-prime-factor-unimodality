"""Reject damaged or wrong-input exports before replacing a consumer's checkpoint."""

import io
import os
import tarfile
from pathlib import Path

import pytest

from scripts.comparator_checkpoint import EXPORTS, identity, pack, restore

CONTEXT = identity("owner/repo", "a" * 40, "123")


def checkpoint(tmp_path: Path) -> tuple[Path, Path, Path]:
    exports = tmp_path / "producer"
    exports.mkdir()
    for name in EXPORTS:
        (exports / name).write_bytes(name.encode())
    binary = tmp_path / "comparator"
    binary.write_bytes(b"checker")
    archive = tmp_path / "checkpoint.tar.gz"
    pack(exports, binary, archive, CONTEXT)
    return exports, binary, archive


def test_round_trip_preserves_all_payloads_and_executable(tmp_path: Path) -> None:
    original, binary, archive = checkpoint(tmp_path)
    restored = tmp_path / "restored"
    checker = tmp_path / "consumer/checker"
    restore(restored, checker, archive, CONTEXT)
    for name in EXPORTS:
        assert (restored / name).read_bytes() == (original / name).read_bytes()
    assert checker.read_bytes() == binary.read_bytes()
    if os.name == "posix":
        assert checker.stat().st_mode & 0o111


@pytest.mark.parametrize("field", ["repository", "commit", "run_id"])
def test_other_inputs_are_rejected_before_writing(tmp_path: Path, field: str) -> None:
    _, _, archive = checkpoint(tmp_path)
    other = {**CONTEXT, field: "different"}
    restored = tmp_path / "restored"
    checker = tmp_path / "consumer/checker"
    with pytest.raises(ValueError, match="identity"):
        restore(restored, checker, archive, other)
    assert not restored.exists()
    assert not checker.exists()


@pytest.mark.parametrize("damage", ["checksum", "missing", "duplicate", "traversal", "symlink"])
def test_damaged_archive_cannot_replace_existing_checkpoint(tmp_path: Path, damage: str) -> None:
    _, _, archive = checkpoint(tmp_path)
    broken = tmp_path / "broken.tar.gz"
    with tarfile.open(archive, "r:gz") as source, tarfile.open(broken, "w:gz") as destination:
        for member in source:
            data = source.extractfile(member)
            assert data is not None
            payload = data.read()
            if member.name == "solution.export":
                if damage == "missing":
                    continue
                if damage == "checksum":
                    payload = b"x" * len(payload)
                if damage == "traversal":
                    member.name = "../outside"
                if damage == "symlink":
                    member.type = tarfile.SYMTYPE
                    member.linkname = "../outside"
            destination.addfile(member, io.BytesIO(payload))
            if damage == "duplicate" and member.name == "solution.export":
                destination.addfile(member, io.BytesIO(payload))
    restored = tmp_path / "restored"
    restored.mkdir()
    (restored / "solution.export").write_bytes(b"preserved")
    checker = tmp_path / "consumer/checker"
    with pytest.raises(ValueError):
        restore(restored, checker, broken, CONTEXT)
    assert (restored / "solution.export").read_bytes() == b"preserved"
    assert not checker.exists()
    assert not (tmp_path / "outside").exists()
