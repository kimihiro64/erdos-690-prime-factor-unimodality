"""Fail-closed release provenance, conditional-only stages, and bounded packaging."""

from __future__ import annotations

import copy
import json
import tarfile
from pathlib import Path

import pytest

from scripts.conditional_docs import verify_pages
from scripts.conditional_dusart_plan import (
    CONFIG,
    PREBUILD_TARGET,
    TARGET,
    THEOREM,
    plan,
    stage_units,
)
from scripts.conditional_paper import render
from scripts.conditional_release_bundle import (
    archive_parts,
    closure_files,
    module_artifacts,
    sha256,
    verify_parts,
)
from scripts.conditional_release_receipt import (
    STATEMENT,
    check_report,
    make_receipt,
    validate_receipt,
)
from scripts.publish_conditional_release import prepare, regular_file, verify_hashes

ROOT = Path(__file__).resolve().parents[2]
COMMIT = "a" * 40
REPORT = f"{STATEMENT}\n'{THEOREM}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"


def fixture_project(root: Path) -> None:
    for name in CONFIG:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("fixed config")
    for module, source in (
        (TARGET, f"import {PREBUILD_TARGET}\n"),
        (PREBUILD_TARGET, "import PrimeFactorUnimodality.Generated.Row\n"),
        ("PrimeFactorUnimodality.Generated.Row", "import Mathlib.Data.Nat.Basic\n"),
    ):
        path = root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)


def test_receipt_matches_exact_statement_commit_and_sources(tmp_path: Path) -> None:
    fixture_project(tmp_path)
    receipt = make_receipt(tmp_path, COMMIT, {THEOREM: REPORT})
    assert validate_receipt(tmp_path, receipt, COMMIT) == receipt
    for field, value in (
        ("conditional", False),
        ("commit", "b" * 40),
        ("unit_keys", []),
        ("targets", ["Solution"]),
        ("schema", 0),
        ("unit_size", True),
    ):
        changed = copy.deepcopy(receipt)
        changed[field] = value
        with pytest.raises(ValueError):
            validate_receipt(tmp_path, changed, COMMIT)
    source = tmp_path / (TARGET.replace(".", "/") + ".lean")
    source.write_text(source.read_text() + "-- changed actual source\n")
    with pytest.raises(ValueError, match="proof closure"):
        validate_receipt(tmp_path, receipt, COMMIT)


def test_report_rejects_extra_hypotheses_and_wrong_axioms() -> None:
    check_report(REPORT)
    with pytest.raises(ValueError, match="type differs"):
        check_report(REPORT.replace(" → ", " → False → ", 1))
    with pytest.raises(ValueError, match="unexpected"):
        check_report(REPORT.replace("Quot.sound", "sorryAx"))


def test_separated_stages_preserve_checkpoint_keys(tmp_path: Path) -> None:
    fixture_project(tmp_path)
    units = plan(tmp_path, size=1)
    prebuild = stage_units(units, "prebuild")
    assert PREBUILD_TARGET in prebuild[-1].modules
    assert prebuild == units[: len(prebuild)]
    assert all(unit.phase == "foundations" for unit in stage_units(units, "foundations"))
    assert stage_units(units, "build") == units
    with pytest.raises(ValueError):
        stage_units(units, "unknown")


def test_paper_is_separate_and_provenance_is_escaped(tmp_path: Path) -> None:
    original = (ROOT / "paper/research-paper.tex").read_bytes()
    source = render(ROOT, tmp_path, COMMIT, "leanprover/lean4:v4.34.0")
    assert source.name == "conditional-paper.tex"
    text = source.read_text()
    assert COMMIT in text
    assert "@@COMMIT@@" not in text
    assert "one explicit proposition" in text
    assert "Precise relationship to Wang--Crapis" in text
    assert "8{,}600{,}001" in text and "38{,}001" in text
    assert "Measured costs and rejected approaches" in text
    assert "Analytic height reduction and ongoing zero work" in text
    assert (ROOT / "paper/research-paper.tex").read_bytes() == original
    with pytest.raises(ValueError, match="unsafe"):
        render(ROOT, tmp_path, COMMIT, "bad\\input{escape}")


def fixture_artifacts(root: Path) -> Path:
    target = root / ".lake/build/lib/lean" / (TARGET.replace(".", "/") + ".olean")
    dependency = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Test.olean"
    for path in (target, dependency):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"compiled artifact")
    setup = root / ".lake/build/ir" / (TARGET.replace(".", "/") + ".setup.json")
    setup.parent.mkdir(parents=True, exist_ok=True)
    setup.write_text(
        json.dumps(
            {
                "name": TARGET,
                "plugins": [],
                "dynlibs": [],
                "importArts": {"Mathlib.Test": [[str(dependency)]]},
            }
        )
    )
    return setup


def test_full_artifact_closure_includes_dependencies_and_target(tmp_path: Path) -> None:
    fixture_artifacts(tmp_path)
    modules = module_artifacts(tmp_path)
    assert set(modules) == {TARGET, "Mathlib.Test"}
    files = closure_files(tmp_path, modules)
    assert any("packages/mathlib" in str(path) for path in files)
    output = tmp_path / "output"
    output.mkdir()
    parts = archive_parts(tmp_path, files, output)
    assert len(parts) == 1
    with tarfile.open(output / str(parts[0]["asset"]), "r:gz") as archive:
        assert set(archive.getnames()) == {path.as_posix() for path in files}
        assert all(member.isfile() for member in archive.getmembers())
    verify_parts(output, {"parts": parts, "modules": sorted(modules)})
    with pytest.raises(ValueError, match="module set"):
        verify_parts(output, {"parts": parts, "modules": [TARGET]})


def test_artifact_closure_rejects_omitted_and_external_files(tmp_path: Path) -> None:
    setup = fixture_artifacts(tmp_path)
    data = json.loads(setup.read_text())
    data["importArts"]["Mathlib.Test"] = [["/etc/passwd"]]
    setup.write_text(json.dumps(data))
    with pytest.raises(ValueError):
        module_artifacts(tmp_path)


def test_release_assets_reject_traversal_and_wrong_hash(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="unsafe"):
        regular_file(tmp_path, "../escape")
    (tmp_path / "test.pdf").write_bytes(b"wrong")
    with pytest.raises(ValueError, match="hash mismatch"):
        verify_hashes(tmp_path, {"test.pdf": "0" * 64})


def test_resource_projections_are_not_presented_as_measurements() -> None:
    data = json.loads((ROOT / "paper/conditional-resources.json").read_text())
    assert data["meissel"]["kind"] == "projection"
    assert data["platt_scenario"]["kind"] == "nonrigorous workload screen"
    assert "NOT a whole-Dusart runtime" in data["scope"]
    assert "no olean" in data["packed_convolution"]["scope"].lower()


def test_documentation_requires_every_nonempty_module_page(tmp_path: Path) -> None:
    modules = [TARGET, "Mathlib.Test"]
    target = tmp_path / (TARGET.replace(".", "/") + ".html")
    target.parent.mkdir(parents=True)
    target.write_text("conditional theorem")
    dependency = tmp_path / "Mathlib/Test.html"
    with pytest.raises(ValueError, match="Mathlib.Test"):
        verify_pages(tmp_path, modules)
    dependency.parent.mkdir()
    dependency.touch()
    with pytest.raises(ValueError, match="Mathlib.Test"):
        verify_pages(tmp_path, modules)
    dependency.write_text("dependency declarations")
    verify_pages(tmp_path, modules)
    with pytest.raises(ValueError, match="unique"):
        verify_pages(tmp_path, [*modules, TARGET])
    with pytest.raises(ValueError, match="complete"):
        verify_pages(tmp_path, ["Mathlib.Test"])


@pytest.mark.parametrize("module", ["../outside", "Mathlib..Test", "Mathlib/Test", "Mathlib\\Test"])
def test_documentation_rejects_unsafe_module_names(tmp_path: Path, module: str) -> None:
    with pytest.raises(ValueError, match="unsafe"):
        verify_pages(tmp_path, [module, TARGET])


def test_documentation_rejects_symlink_pages(tmp_path: Path) -> None:
    directory = tmp_path / "docs"
    outside = tmp_path / "outside.html"
    outside.write_text("not part of documentation")
    target = directory / (TARGET.replace(".", "/") + ".html")
    target.parent.mkdir(parents=True)
    target.symlink_to(outside)
    with pytest.raises(ValueError, match="missing or invalid"):
        verify_pages(directory, [TARGET])


def test_release_assembly_requires_matching_paper_and_proof_without_docs(tmp_path: Path) -> None:
    fixture_project(tmp_path)
    fixture_artifacts(tmp_path)
    inputs = tmp_path / "inputs"
    for name in ("paper", "build"):
        (inputs / name).mkdir(parents=True)
    receipt = make_receipt(tmp_path, COMMIT, {THEOREM: REPORT})
    for name in ("paper", "build"):
        (inputs / name / "conditional-audit.json").write_text(json.dumps(receipt))
    modules = module_artifacts(tmp_path)
    build = inputs / "build"
    parts = archive_parts(tmp_path, closure_files(tmp_path, modules), build)
    for name in ("conditional-source.tar.gz", "conditional-licenses.tar.gz"):
        (build / name).write_bytes(b"fixture archive")
    extras = {
        name: sha256(build / name)
        for name in (
            "conditional-source.tar.gz",
            "conditional-licenses.tar.gz",
            "conditional-audit.json",
        )
    }
    (build / "conditional-build-manifest.json").write_text(
        json.dumps(
            {
                "commit": COMMIT,
                "conditional": True,
                "modules": sorted(modules),
                "other_sha256": extras,
                "parts": parts,
            }
        )
    )
    paper = inputs / "paper"
    for name in ("conditional-paper.pdf", "conditional-paper.tex", "conditional-resources.json"):
        (paper / name).write_bytes(b"fixture paper")
    (paper / "paper-provenance.json").write_text(
        json.dumps(
            {
                "commit": COMMIT,
                "conditional": True,
                "statement": STATEMENT,
                "sha256": {p.name: sha256(p) for p in paper.iterdir()},
            }
        )
    )
    assert not (inputs / "docs").exists()
    assembled = prepare(tmp_path, inputs, tmp_path / "release", COMMIT)
    assert assembled["conditional"] is True
    assert assembled["api_documentation"] == "not built or included in the conditional release"
    assert "conditional-api-documentation.zip" not in assembled["assets"]
    assert "conditional-licenses.tar.gz" in assembled["assets"]
    assert "conditional-paper.pdf" in assembled["assets"]
    assert "conditional-build-manifest.json" in assembled["assets"]
    (paper / "conditional-paper.pdf").write_bytes(b"changed")
    with pytest.raises(ValueError, match="hash mismatch"):
        prepare(tmp_path, inputs, tmp_path / "invalid", COMMIT)
