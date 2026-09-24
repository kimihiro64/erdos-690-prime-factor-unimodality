"""Test isolation, checkpoint identity, safe restoration, and the proof audit."""

from __future__ import annotations

import io
import tarfile
from pathlib import Path

import pytest

from scripts.conditional_dusart_checkpoints import pack, restore
from scripts.conditional_dusart_ci import check_axioms
from scripts.conditional_dusart_plan import (
    CONFIG,
    TARGET,
    THEOREM,
    Unit,
    artifact_paths,
    owned_plan,
    plan,
    required_artifacts,
)
from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]


def test_euler_maclaurin_facade_reuses_the_analytic_dependency() -> None:
    source = (ROOT / "VendorPrimeNumberTheoremAnd/EulerMaclaurin.lean").read_text()
    code = strip_lean_comments(source)
    assert lean_imports(code) == ["PrimeNumberTheoremAnd.EulerMaclaurin"]
    assert code.strip() == "module\n\npublic import PrimeNumberTheoremAnd.EulerMaclaurin"
    regression = (ROOT / "test/lean/FinalThetaIntegration.lean").read_text()
    assert "import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartReflectedBootstrap" in (
        regression
    )
    assert (
        "import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredReduction" in regression
    )


def write_module(root: Path, name: str, code: str) -> Path:
    path = root.joinpath(*name.split(".")).with_suffix(".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(code)
    return path


def fixture_project(root: Path) -> None:
    for name in CONFIG:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("locked configuration")
    write_module(root, TARGET, "import PrimeFactorUnimodality.Generated.Row\n")
    write_module(
        root, "PrimeFactorUnimodality.Generated.Row", "import PrimeFactorUnimodality.Basic\n"
    )
    write_module(root, "PrimeFactorUnimodality.Basic", "import Mathlib.Data.Nat.Basic\n")


def test_conditional_import_graph_is_isolated() -> None:
    ordered, imports = owned_plan(ROOT)
    assert ordered[-1] == TARGET
    assert "PrimeFactorUnimodality.Proof.LargeRange.RecordTwinClosed" in ordered
    assert "PrimeFactorUnimodality.Proof.LargeRange.UniformTailClosedMertens" in ordered
    assert "PrimeFactorUnimodality.Proof.LargeRange.RecordPrimeCountingReduction" in ordered
    assert not any("RecordReciprocal" in module for module in ordered)
    seen: set[str] = set()
    for module in ordered:
        assert all(dependency in seen for dependency in imports[module] if dependency in imports)
        seen.add(module)
    source = ROOT.joinpath(*TARGET.split(".")).with_suffix(".lean").read_text()
    assert source.count(" : HasThetaLogSquaredError") == 1
    assert ": CompleteClassification :=" in source
    regression = (ROOT / "test/lean/ConditionalTheta.lean").read_text()
    assert "∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3)" in regression


def test_keys_follow_dependencies_not_unrelated_files(tmp_path: Path) -> None:
    fixture_project(tmp_path)
    initial = plan(tmp_path, size=1)
    assert [unit.phase for unit in initial] == ["foundations", "certificates", "certificates"]
    write_module(tmp_path, "Unrelated", "anything at all")
    assert plan(tmp_path, size=1) == initial
    write_module(tmp_path, TARGET, "import PrimeFactorUnimodality.Generated.Row\n-- edit\n")
    changed = plan(tmp_path, size=1)
    assert changed[:-1] == initial[:-1]
    assert changed[-1].key != initial[-1].key
    write_module(tmp_path, "PrimeFactorUnimodality.Basic", "-- changed prerequisite\n")
    assert all(a.key != b.key for a, b in zip(changed, plan(tmp_path, size=1), strict=True))


@pytest.mark.parametrize(
    "dependency",
    ["PrimeFactorUnimodality.Helpers.Analytic.DusartProvider", "PrimeFactorUnimodality.Missing"],
)
def test_rejects_unfinished_or_missing_imports(tmp_path: Path, dependency: str) -> None:
    write_module(tmp_path, TARGET, f"import {dependency}\n")
    with pytest.raises(ValueError):
        owned_plan(tmp_path)


def test_rejects_cycles(tmp_path: Path) -> None:
    write_module(tmp_path, TARGET, f"import {TARGET}\n")
    with pytest.raises(ValueError, match="cycle"):
        owned_plan(tmp_path)


def test_checkpoint_round_trip_and_identity(tmp_path: Path) -> None:
    unit = Unit((TARGET,), "a" * 64, "certificates")
    source = tmp_path / "source"
    for path in required_artifacts(unit):
        (source / path).parent.mkdir(parents=True, exist_ok=True)
        (source / path).write_bytes(path.as_posix().encode())
    archive = tmp_path / unit.asset
    pack(source, unit, archive)
    restored = tmp_path / "restored"
    restore(restored, unit, archive)
    for path in required_artifacts(unit):
        assert (restored / path).read_bytes() == (source / path).read_bytes()
    with pytest.raises(ValueError, match="identity"):
        restore(restored, Unit(unit.modules, "b" * 64, unit.phase), archive)
    assert any(path.suffix == ".c" for path in artifact_paths(unit))
    assert any(str(path).endswith(".ir.sig") for path in artifact_paths(unit))


def test_checkpoint_rejects_traversal_and_incomplete_output(tmp_path: Path) -> None:
    unit = Unit((TARGET,), "a" * 64, "certificates")
    archive = tmp_path / unit.asset
    with pytest.raises(ValueError, match="incomplete"):
        pack(tmp_path, unit, archive)
    with tarfile.open(archive, "w:gz") as bundle:
        entry = tarfile.TarInfo("../../escape")
        entry.size = 3
        bundle.addfile(entry, io.BytesIO(b"bad"))
    with pytest.raises(ValueError, match="path"):
        restore(tmp_path, unit, archive)


def test_axiom_audit_fails_closed() -> None:
    check_axioms(f"'{THEOREM}' depends on axioms: [propext, Classical.choice, Quot.sound]")
    with pytest.raises(ValueError, match="missing"):
        check_axioms("no theorem found")
    with pytest.raises(ValueError, match="unexpected"):
        check_axioms(f"'{THEOREM}' depends on axioms: [propext, sorryAx]")


def test_only_reduced_target_is_built() -> None:
    units = plan(ROOT)
    modules = [module for unit in units for module in unit.modules]
    assert len(modules) == len(set(modules))
    assert TARGET in modules
    assert "PrimeFactorUnimodality.Proof.CompleteClassificationConditional" not in modules
    runner = (ROOT / "scripts/conditional_dusart_ci.py").read_text()
    assert '"ConditionalDusart"' not in runner
    assert "PrimeFactorUnimodality.Helpers.Analytic.DusartPublishedPrimeCounting" in modules
    assert not any("Xi" in module or "DusartClosed" in module for module in modules)
    with pytest.raises(ValueError, match="missing"):
        check_axioms(
            "'PrimeFactorUnimodality.completeClassification_assuming_dusart' "
            "depends on axioms: [propext]"
        )


def test_theta_target_does_not_allow_arbitrary_dusart_providers(tmp_path: Path) -> None:
    write_module(
        tmp_path, TARGET, "import PrimeFactorUnimodality.Helpers.Analytic.DusartProvider\n"
    )
    with pytest.raises(ValueError, match="unfinished"):
        owned_plan(tmp_path)


def test_conditional_workflow_is_state_gated_bounded_and_not_cancelled_by_push() -> None:
    workflow = (ROOT / ".github/workflows/conditional-dusart.yml").read_text()
    assert "  workflow_dispatch:" in workflow
    assert "  push:" in workflow
    assert "vars.CONDITIONAL_CI_BUILDS == 'enabled'" in workflow
    assert "--both" not in workflow
    assert "cancel-in-progress: false" in workflow
    assert "timeout-minutes: 360" in workflow
    assert "use-mathlib-cache: true" in workflow
    assert ".githooks/pre-commit" in workflow
    assert "--minutes 280" in workflow
    assert "DUSART_CI_BUILDS" not in workflow
