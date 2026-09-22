"""Compatibility ports are exact, idempotent, and fail closed on source drift."""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from scripts import patch_pnt_compat as compat


def test_edit_sites_are_unique() -> None:
    for edits in compat.CHANGES.values():
        for before, after in edits:
            assert before != after
            assert compat.patched_source(before, ((before, after),)) == after
            for text in ("", before + before):
                with pytest.raises(ValueError, match="expected one edit site"):
                    compat.patched_source(text, ((before, after),))


def test_sources_are_preserved_on_drift() -> None:
    assert compat.validate_current("original", "original", "patched")
    assert not compat.validate_current("patched", "original", "patched")
    with pytest.raises(ValueError, match="unrelated local edits"):
        compat.validate_current("user edit", "original", "patched")


def test_revision_matches_both_locked_manifests_and_configuration() -> None:
    for name in ("lake-manifest.json", "docbuild/lake-manifest.json"):
        manifest = json.loads((compat.ROOT / name).read_text())
        package = next(p for p in manifest["packages"] if p["name"] == "PrimeNumberTheoremAnd")
        assert package["rev"] == compat.REVISION
    config = (compat.ROOT / "lakefile.toml").read_text()
    assert f'rev = "{compat.REVISION}"' in config


def test_validation_precedes_every_write(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    package = tmp_path / ".lake/packages/PrimeNumberTheoremAnd"
    source = package / compat.PREFIX
    source.mkdir(parents=True)
    (tmp_path / "lake-manifest.json").write_text(
        json.dumps({"packages": [{"name": "PrimeNumberTheoremAnd", "rev": compat.REVISION}]})
    )
    (source / "First.lean").write_text("original")
    (source / "Second.lean").write_text("user edit")
    monkeypatch.setattr(
        compat,
        "CHANGES",
        {"First.lean": (("original", "ported"),), "Second.lean": (("original", "ported"),)},
    )
    monkeypatch.setattr(
        compat,
        "git_output",
        lambda _package, *args: compat.REVISION if args[0] == "rev-parse" else "original",
    )
    with pytest.raises(ValueError, match="unrelated local edits"):
        compat.apply_patches(tmp_path)
    assert (source / "First.lean").read_text() == "original"
    assert (source / "Second.lean").read_text() == "user edit"
    (source / "Second.lean").write_text("original")
    with pytest.raises(ValueError, match="not been applied"):
        compat.apply_patches(tmp_path, check=True)
    assert (source / "First.lean").read_text() == "original"
    assert compat.apply_patches(tmp_path) == 2
    assert compat.apply_patches(tmp_path) == 0
    assert compat.apply_patches(tmp_path, check=True) == 0


def test_ci_applies_ports_before_new_xi_target() -> None:
    workflow = (compat.ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    patch = "python3 scripts/patch_pnt_compat.py"
    target = "+PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeroContribution"
    regression = "lake env lean test/lean/ZetaZeroFreeIngredients.lean"
    assert foundations.index(patch) < foundations.index(target) < foundations.index(regression)


def test_all_lean_jobs_apply_the_same_ports() -> None:
    workflow = (compat.ROOT / ".github/workflows/ci.yml").read_text()
    for job in (
        "release-licensing",
        "lean-foundations",
        "certificate-prebuild",
        "analytic-tail",
        "build",
        "docs",
        "comparator",
    ):
        body = workflow.split(f"  {job}:\n", 1)[1]
        body = re.split(r"(?m)^  [a-z][a-z0-9-]*:\n", body, maxsplit=1)[0]
        assert "scripts/patch_pnt_compat.py" in body
