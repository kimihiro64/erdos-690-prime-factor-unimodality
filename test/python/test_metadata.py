from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

import pytest

from scripts.check import CheckFailure, check_metadata


@pytest.mark.parametrize("release", [False, True])
def test_missing_ruby_fails_metadata_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, release: bool
) -> None:
    (tmp_path / "formalization.yaml").write_text("version: v0.4\n")
    monkeypatch.setattr("scripts.check.shutil.which", lambda _: None)

    with pytest.raises(CheckFailure, match="Ruby is required for metadata validation"):
        check_metadata(tmp_path, release=release)


def test_fast_metadata_gate_runs_tests_and_validator(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "formalization.yaml").write_text("version: v0.4\n")
    (tmp_path / "test").mkdir()
    (tmp_path / "test/validate_formalization_test.rb").touch()
    monkeypatch.setattr("scripts.check.shutil.which", lambda _: "/usr/bin/ruby")
    calls: list[tuple[tuple[str, ...], Path]] = []

    def record(command: Sequence[str], cwd: Path) -> None:
        calls.append((tuple(command), cwd))

    monkeypatch.setattr("scripts.check.run", record)
    check_metadata(tmp_path, release=False)

    assert calls == [
        (("/usr/bin/ruby", "test/validate_formalization_test.rb"), tmp_path),
        (("/usr/bin/ruby", "scripts/validate-formalization.rb"), tmp_path),
    ]
