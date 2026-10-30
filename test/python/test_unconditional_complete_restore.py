"""Unchanged proof restores a completed build even when checkpoint drafts vanish."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from scripts.conditional_dusart_plan import Unit, required_artifacts
from scripts.unconditional_ci import AUDITED, STATEMENT, check_report, replay_proof
from scripts.unconditional_complete_restore import restore_build, restore_complete, validate_receipt

MODULE = "scripts.unconditional_complete_restore"
RUNNER = "scripts.unconditional_ci"
COMMIT = "a" * 40
UNITS = [Unit(("PrimeFactorUnimodality",), "source-key", "certificates")]


def receipt(root: Path) -> dict[str, object]:
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
    report = (
        STATEMENT
        + "\n"
        + "\n".join(
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for name in AUDITED
        )
    )
    return {
        "commit": COMMIT,
        "conditional": False,
        "targets": ["PrimeFactorUnimodality", "Challenge", "Solution"],
        "toolchain": "leanprover/lean4:v4.34.0",
        "unit_keys": [unit.key for unit in UNITS],
        "statement": STATEMENT,
        "axiom_reports": report,
    }


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("commit", "b" * 40),
        ("conditional", True),
        ("unit_keys", ["changed-proof-or-config"]),
        ("toolchain", "different"),
        ("targets", ["Solution"]),
        ("statement", "different"),
        ("axiom_reports", "unverified"),
    ],
)
def test_changed_provenance_rejected(tmp_path: Path, field: str, value: object) -> None:
    previous = receipt(tmp_path)
    validate_receipt(tmp_path, UNITS, previous, COMMIT, check_report)
    previous[field] = value
    with pytest.raises(ValueError):
        validate_receipt(tmp_path, UNITS, previous, COMMIT, check_report)


def test_large_build_download_requires_matching_small_receipt(tmp_path: Path) -> None:
    good = receipt(tmp_path)
    downloads: list[tuple[int, str]] = []

    def fake_download(repo: str, run_id: int, name: str, directory: Path) -> None:
        downloads.append((run_id, name))
        directory.mkdir(parents=True)
        if name == "unconditional-proof-audit":
            data = good | ({"unit_keys": ["old-proof"]} if run_id == 1 else {})
            (directory / "unconditional-audit.json").write_text(json.dumps(data))

    with (
        patch(
            f"{MODULE}.candidate_runs",
            return_value=[{"id": 1, "head_sha": COMMIT}, {"id": 2, "head_sha": COMMIT}],
        ) as candidates,
        patch(
            f"{MODULE}.artifact_names",
            return_value={"unconditional-proof-audit", "linux-lean-build"},
        ),
        patch(f"{MODULE}.download", side_effect=fake_download),
        patch(f"{MODULE}.restore_build") as restore,
    ):
        assert restore_complete(tmp_path, UNITS, "o/r", "3", check_report=check_report)
        candidates.assert_called_once_with("o/r", "3", workflow="ci.yml")
        restore.assert_called_once()
    assert downloads == [
        (1, "unconditional-proof-audit"),
        (2, "unconditional-proof-audit"),
        (2, "linux-lean-build"),
    ]


def test_build_restore_preserves_unrelated_files_and_rejects_incomplete_artifact(
    tmp_path: Path,
) -> None:
    bundle = tmp_path / "bundle"
    for path in required_artifacts(UNITS[0]):
        source = bundle / path.relative_to(".lake/build")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes(b"compiled")
    unrelated = tmp_path / ".lake/build/unrelated"
    unrelated.parent.mkdir(parents=True)
    unrelated.write_bytes(b"preserve")
    restore_build(tmp_path, bundle, UNITS)
    assert unrelated.read_bytes() == b"preserve"
    required = next(iter(required_artifacts(UNITS[0])))
    (bundle / required.relative_to(".lake/build")).unlink()
    with pytest.raises(ValueError, match="incomplete"):
        restore_build(tmp_path, bundle, UNITS)


def test_matching_complete_build_never_enters_checkpoint_or_compiler_path(tmp_path: Path) -> None:
    with (
        patch(f"{RUNNER}.restore_complete", return_value=True),
        patch(f"{RUNNER}.run_lake", return_value=0) as run,
        patch(f"{RUNNER}.replay_units") as replay,
        patch(f"{RUNNER}.build") as compile_one,
    ):
        replay_proof(tmp_path, UNITS, "o/r", COMMIT, 100, read_only=False)
    run.assert_called_once_with(tmp_path, ("PrimeFactorUnimodality",), 100, check=True)
    replay.assert_not_called()
    compile_one.assert_not_called()


@pytest.mark.parametrize("restored", [False, True])
def test_missing_or_stale_complete_build_repairs_checkpoints(
    tmp_path: Path, restored: bool
) -> None:
    with (
        patch(f"{RUNNER}.restore_complete", return_value=restored),
        patch(f"{RUNNER}.run_lake", return_value=3) as run,
        patch(f"{RUNNER}.replay_units") as replay,
    ):
        replay_proof(tmp_path, UNITS, "o/r", COMMIT, 100, read_only=True)
    assert run.call_count == int(restored)
    replay.assert_called_once_with(tmp_path, UNITS, "o/r", COMMIT, 100, read_only=True)


def test_checker_failure_is_fatal_without_rebuild(tmp_path: Path) -> None:
    with (
        patch(f"{RUNNER}.restore_complete", return_value=True),
        patch(f"{RUNNER}.run_lake", side_effect=subprocess.CalledProcessError(1, ["lake"])),
        patch(f"{RUNNER}.replay_units") as replay,
        pytest.raises(subprocess.CalledProcessError),
    ):
        replay_proof(tmp_path, UNITS, "o/r", COMMIT, 100, read_only=False)
    replay.assert_not_called()
