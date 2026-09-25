"""A complete warm proof restores dependencies once and rejects stale or unsafe bundles."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from scripts.conditional_complete_restore import candidate_runs, restore_bundle, restore_complete
from scripts.conditional_dusart_plan import CONFIG, TARGET, THEOREM
from scripts.conditional_release_bundle import archive_parts
from scripts.conditional_release_receipt import STATEMENT, make_receipt

MODULE = "scripts.conditional_complete_restore"
COMMIT = "a" * 40


def fixture_bundle(root: Path) -> tuple[Path, dict[str, object], list[Path]]:
    for name in CONFIG:
        (root / name).parent.mkdir(parents=True, exist_ok=True)
        (root / name).write_text("locked config")
    source = root / (TARGET.replace(".", "/") + ".lean")
    source.parent.mkdir(parents=True)
    source.write_text("import Mathlib.Test\n")
    report = f"{STATEMENT}\n'{THEOREM}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    receipt = make_receipt(root, COMMIT, {THEOREM: report})
    files = [
        Path(".lake/build/lib/lean") / (TARGET.replace(".", "/") + ".olean"),
        Path(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Test.olean"),
        Path(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Test.trace"),
    ]
    for relative in files:
        (root / relative).parent.mkdir(parents=True, exist_ok=True)
        (root / relative).write_bytes(b"compiled")
    bundle = root / "bundle"
    bundle.mkdir()
    parts = archive_parts(root, files, bundle)
    (bundle / "conditional-audit.json").write_text(json.dumps(receipt))
    (bundle / "conditional-build-manifest.json").write_text(
        json.dumps(
            {
                "conditional": True,
                "commit": COMMIT,
                "toolchain": receipt["toolchain"],
                "modules": [TARGET, "Mathlib.Test"],
                "parts": parts,
            }
        )
    )
    return bundle, receipt, files


def test_complete_bundle_restores_project_and_package_artifacts(tmp_path: Path) -> None:
    bundle, receipt, files = fixture_bundle(tmp_path)
    for name in files:
        (tmp_path / name).unlink()
    unrelated = tmp_path / ".lake/build/unrelated-cache"
    unrelated.write_text("preserve")
    restore_bundle(tmp_path, bundle, receipt)
    assert all((tmp_path / name).read_bytes() == b"compiled" for name in files)
    assert unrelated.read_text() == "preserve"


def test_changed_proof_rejects_bundle_before_overwriting(tmp_path: Path) -> None:
    bundle, receipt, files = fixture_bundle(tmp_path)
    (tmp_path / files[0]).write_bytes(b"preserve")
    (tmp_path / (TARGET.replace(".", "/") + ".lean")).write_text("-- different proof")
    with pytest.raises(ValueError, match="proof closure"):
        restore_bundle(tmp_path, bundle, receipt)
    assert (tmp_path / files[0]).read_bytes() == b"preserve"


def test_corrupt_archive_rejected_before_overwriting(tmp_path: Path) -> None:
    bundle, receipt, files = fixture_bundle(tmp_path)
    (tmp_path / files[0]).write_bytes(b"preserve")
    next(bundle.glob("*.tar.gz")).write_bytes(b"corrupt")
    with pytest.raises(ValueError, match="digest"):
        restore_bundle(tmp_path, bundle, receipt)
    assert (tmp_path / files[0]).read_bytes() == b"preserve"


def test_symlink_destination_rejected_before_overwriting(tmp_path: Path) -> None:
    bundle, receipt, files = fixture_bundle(tmp_path)
    outside = tmp_path / "outside"
    outside.write_bytes(b"preserve")
    destination = tmp_path / files[-1]
    destination.unlink()
    destination.symlink_to(outside)
    with pytest.raises(ValueError, match="symlink"):
        restore_bundle(tmp_path, bundle, receipt)
    assert outside.read_bytes() == b"preserve"


def test_only_trusted_completed_runs_are_candidates_even_if_docs_failed() -> None:
    good = {
        "id": 1,
        "status": "completed",
        "conclusion": "failure",
        "head_branch": "main",
        "event": "push",
        "head_repository": {"full_name": "o/r"},
    }
    runs = [
        good,
        good | {"id": 2, "status": "in_progress"},
        good | {"id": 3, "head_branch": "feature"},
        good | {"id": 4, "event": "pull_request"},
        good | {"id": 5, "head_repository": {"full_name": "other/repo"}},
        good | {"id": 6},
    ]
    with patch(
        f"{MODULE}.subprocess.check_output", return_value=json.dumps({"workflow_runs": runs})
    ):
        assert candidate_runs("o/r", "6") == [good]


def test_matching_receipt_skips_large_downloads_for_other_sources(tmp_path: Path) -> None:
    _, receipt, _ = fixture_bundle(tmp_path)
    runs = [{"id": 1, "head_sha": "b" * 40}, {"id": 2, "head_sha": COMMIT}]
    downloads: list[tuple[int, str]] = []

    def download(repo: str, run_id: int, name: str, directory: Path) -> None:
        downloads.append((run_id, name))
        directory.mkdir(parents=True)
        if name == "conditional-proof-audit":
            (directory / "conditional-audit.json").write_text(json.dumps(receipt))

    with (
        patch(f"{MODULE}.candidate_runs", return_value=runs),
        patch(
            f"{MODULE}.artifact_names",
            return_value={"conditional-proof-audit", "conditional-build-release"},
        ),
        patch(f"{MODULE}.download", side_effect=download),
        patch(f"{MODULE}.restore_bundle") as restore,
    ):
        assert restore_complete(tmp_path, "o/r", "3")
    assert downloads == [
        (1, "conditional-proof-audit"),
        (2, "conditional-proof-audit"),
        (2, "conditional-build-release"),
    ]
    restore.assert_called_once()


def test_expired_complete_artifact_falls_back_without_download(tmp_path: Path) -> None:
    with (
        patch(f"{MODULE}.candidate_runs", return_value=[{"id": 1}]),
        patch(f"{MODULE}.artifact_names", return_value={"conditional-proof-audit"}),
        patch(f"{MODULE}.download") as download,
    ):
        assert not restore_complete(tmp_path, "o/r", "2")
    download.assert_not_called()
