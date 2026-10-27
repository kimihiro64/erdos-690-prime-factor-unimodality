"""Keep the unconditional release automatic and historical proof jobs explicitly manual."""

from pathlib import Path

import pytest

from scripts.conditional_dusart_plan import CONFIG, owned_plan, plan
from scripts.render_conditional_workflow import original_jobs
from scripts.unconditional_ci import AUDITED, ROOT, STATEMENT, TARGET, check_report


def test_unconditional_release_has_no_retired_provider_gate() -> None:
    jobs = original_jobs(ROOT)
    for name in ("release-licensing", "build", "docs", "comparator", "paper", "release"):
        assert "DUSART_CI_BUILDS" not in jobs[name], name
        assert "CONDITIONAL_CI_BUILDS" not in jobs[name], name
    build = jobs["build"]
    assert "needs: [release_version, metadata-and-boundary, python]" in build
    assert "scripts.unconditional_ci --minutes 280" in build
    assert "scripts.conditional_dusart_ci" not in build
    assert "unconditional-proof-audit" in build
    assert "linux-lean-build" in build
    release = jobs["release"]
    assert "needs.release_version.outputs.release_ready == 'true'" in release
    assert "github.ref == 'refs/heads/main'" in release
    assert "github.event_name == 'push'" in release
    assert all(
        legacy not in release
        for legacy in ("lean-foundations", "certificate-prebuild", "analytic-tail")
    )


def test_historical_dusart_jobs_require_explicit_manual_selection() -> None:
    jobs = original_jobs(ROOT)
    for name in ("lean-foundations", "certificate-prebuild", "analytic-tail"):
        condition = jobs[name].split("    if: >-\n", 1)[1].split("    needs:", 1)[0]
        assert "github.event_name == 'workflow_dispatch'" in condition
        assert "inputs.legacy_dusart" in condition
    workflow = (ROOT / ".github/workflows/conditional-dusart.yml").read_text()
    assert "  workflow_dispatch:" in workflow
    assert "  push:" not in workflow
    assert "  pull_request:" not in workflow


def test_proof_consumers_preserve_the_committed_dependency_lock() -> None:
    jobs = original_jobs(ROOT)
    for name in ("docs", "comparator"):
        assert "lake update" not in jobs[name], name
        assert "git diff --exit-code HEAD -- lake-manifest.json" in jobs[name], name
        assert "python3 scripts/check_docbuild_manifest.py" in jobs[name], name
    verifier = (ROOT / "scripts/verify-comparator.sh").read_text(encoding="utf-8")
    assert "lake update" not in verifier
    consumer = verifier.rsplit('cd "$repository_root"', 1)[1]
    assert "lake build +Challenge +Solution" in consumer
    assert "\nlake build\n" not in consumer
    assert "git diff --exit-code HEAD -- lake-manifest.json" in consumer


def test_lightweight_checks_remain_independent() -> None:
    jobs = original_jobs(ROOT)
    for name in (
        "release_version",
        "metadata-and-boundary",
        "python",
        "sandbox",
        "submission-link",
    ):
        assert "    if:" not in jobs[name]
        assert "    needs:" not in jobs[name]


def report(statement: str = STATEMENT, axiom: str = "Quot.sound") -> str:
    return (
        statement
        + "\n"
        + "\n".join(
            f"'{theorem}' depends on axioms: [propext, Classical.choice, {axiom}]"
            for theorem in AUDITED
        )
    )


def test_audit_accepts_the_actual_unconditional_type_only() -> None:
    check_report(report())
    with pytest.raises(ValueError, match="type differs"):
        check_report(report(STATEMENT.replace(" : ", " : UnprovedHypothesis -> ")))


@pytest.mark.parametrize("axiom", ["sorryAx", "UnprovedThetaEstimate"])
def test_audit_rejects_unproved_inputs(axiom: str) -> None:
    with pytest.raises(ValueError, match="unexpected"):
        check_report(report(axiom=axiom))


@pytest.mark.parametrize("missing", AUDITED)
def test_audit_requires_every_public_density_and_challenge_result(missing: str) -> None:
    incomplete = "\n".join(line for line in report().splitlines() if f"'{missing}'" not in line)
    with pytest.raises(ValueError):
        check_report(incomplete)


def test_unconditional_plan_uses_the_elementary_closure() -> None:
    ordered, _ = owned_plan(ROOT, TARGET)
    assert ordered[-1] == TARGET
    assert "PrimeFactorUnimodality.Proof.CompleteClassificationElementary" in ordered
    assert "PrimeFactorUnimodality.Proof.LargeRange.RecordRangeElementary" in ordered
    assert "PrimeFactorUnimodality.Proof.LargeRange.ElementaryDensityTail" in ordered
    assert not any(
        part in module for module in ordered for part in ("Dusart", "Conditional", ".Xi")
    )


def test_plan_target_parameter_changes_the_requested_root(tmp_path: Path) -> None:
    for name in CONFIG:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("locked configuration")
    basic = tmp_path / "PrimeFactorUnimodality/Basic.lean"
    basic.parent.mkdir(parents=True, exist_ok=True)
    basic.write_text("import Mathlib.Data.Nat.Basic\n")
    (tmp_path / "Public.lean").write_text("import PrimeFactorUnimodality.Basic\n")
    units = plan(tmp_path, size=1, target="Public")
    assert units[-1].modules == ("Public",)
    assert all(
        "CompleteClassificationSquaredConditional" not in m for u in units for m in u.modules
    )
