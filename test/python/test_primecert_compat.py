"""Pinned PrimeCert ports preserve source edits and handle the changed zero case."""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from scripts import patch_primecert_compat as compat
from scripts.patch_pnt_compat import patched_source


def test_edit_sites_are_unique() -> None:
    for edits in compat.CHANGES.values():
        for before, after in edits:
            assert before != after
            assert patched_source(before, ((before, after),)) == after
            for text in ("", before + before):
                with pytest.raises(ValueError, match="expected one edit site"):
                    patched_source(text, ((before, after),))


def test_modulus_zero_is_excluded_and_existing_caller_supplies_the_premise() -> None:
    assert "(hn₀ : n ≠ 0)" in compat.NEW_CONGRUENCE
    assert "multiplicity_zero" not in compat.NEW_CONGRUENCE
    assert (
        "rw [Nat.modEq_iff_forall_prime_dvd hf₀]"
        in dict(compat.CHANGES["Pocklington.lean"]).values()
    )


def test_revision_matches_both_locked_manifests() -> None:
    for name in ("lake-manifest.json", "docbuild/lake-manifest.json"):
        manifest = json.loads((compat.ROOT / name).read_text())
        package = next(p for p in manifest["packages"] if p["name"] == "PrimeCert")
        assert package["rev"] == compat.REVISION


def test_validation_precedes_every_write(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    package = tmp_path / ".lake/packages/PrimeCert"
    source = package / compat.PREFIX
    source.mkdir(parents=True)
    (tmp_path / "lake-manifest.json").write_text(
        json.dumps({"packages": [{"name": "PrimeCert", "rev": compat.REVISION}]})
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
    assert compat.apply_patches(tmp_path) == 2
    assert compat.apply_patches(tmp_path) == 0
    assert compat.apply_patches(tmp_path, check=True) == 0


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
        assert "scripts/patch_primecert_compat.py" in body
