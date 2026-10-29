"""Pin the orchestration port without changing any upstream checker implementation."""

from pathlib import Path

import pytest

from scripts.patch_comparator_stages import (
    MAIN_SHA256,
    NAMESPACE_END,
    NEW_DISPATCH,
    OLD_DISPATCH,
    STAGES,
    digest,
    stage_source,
)

FIXTURE = Path(__file__).parents[1] / "fixtures/comparator/Main.lean.txt"


def test_port_preserves_every_upstream_checker_and_default_entry_point() -> None:
    original = FIXTURE.read_text(encoding="utf-8")
    assert digest(original) == MAIN_SHA256
    patched, changed = stage_source(original)
    assert changed
    assert patched.split(STAGES, 1)[0] == original.split(NAMESPACE_END, 1)[0]
    assert patched.replace(STAGES, "", 1).replace(NEW_DISPATCH, OLD_DISPATCH, 1) == original
    assert "none => Comparator.M.run Comparator.compareIt config" in patched
    assert stage_source(patched) == (patched, False)


@pytest.mark.parametrize("body", ["Comparator.compareAt", "Comparator.checkAxioms", "runKernel"])
def test_port_rejects_changed_checker_source(body: str) -> None:
    original = FIXTURE.read_text(encoding="utf-8")
    changed = original.replace(body, body + "Changed", 1)
    with pytest.raises(ValueError, match="reviewed pinned source"):
        stage_source(changed)
    patched, _ = stage_source(original)
    with pytest.raises(ValueError, match="checker source changed"):
        stage_source(patched.replace(body, body + "Changed", 1))


def test_previous_serial_orchestration_is_upgraded_without_changing_checkers() -> None:
    from scripts.patch_comparator_stages import LEGACY_STAGED_SHA256

    legacy = FIXTURE.with_name("Main.staged-serial.lean.txt").read_text(encoding="utf-8")
    assert digest(legacy) == LEGACY_STAGED_SHA256
    patched, changed = stage_source(legacy)
    assert changed
    original = FIXTURE.read_text(encoding="utf-8")
    assert patched.replace(STAGES, "", 1).replace(NEW_DISPATCH, OLD_DISPATCH, 1) == original
    assert stage_source(patched) == (patched, False)
