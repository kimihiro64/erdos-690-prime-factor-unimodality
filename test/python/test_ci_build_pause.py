"""Keep expensive CI jobs opt-in while preserving the lightweight checks."""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATE = "vars.DUSART_CI_BUILDS == 'enabled'"


def workflow_jobs() -> dict[str, str]:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    jobs = workflow.split("\njobs:\n", 1)[1]
    return dict(re.findall(r"^  ([\w-]+):\n(.*?)(?=^  [\w-]+:\n|\Z)", jobs, re.M | re.S))


def test_expensive_jobs_require_explicit_build_opt_in() -> None:
    jobs = workflow_jobs()
    expensive = {
        "release-licensing",
        "lean-foundations",
        "certificate-prebuild",
        "analytic-tail",
        "build",
        "docs",
        "comparator",
        "paper",
    }
    # Catch new jobs that invoke Lean even if omitted from the explicit set.
    lake_command = r"(?m)^\s*(?:/usr/bin/time -v )?lake(?:\s+-v)?\s+(?:build|env|lint|update)\b"
    for name, body in jobs.items():
        if "leanprover/lean-action@" in body or re.search(lake_command, body):
            expensive.add(name)
    for name in expensive:
        assert f"    if: ${{{{ {GATE} }}}}\n" in jobs[name], name


def test_release_cannot_publish_during_build_pause() -> None:
    release = workflow_jobs()["release"]
    condition = release.split("    if: >-\n", 1)[1].split("    needs:\n", 1)[0]
    assert condition.lstrip().startswith(f"{GATE} &&\n")
    assert "needs.release_version.outputs.release_ready == 'true'" in condition


def test_lightweight_checks_remain_independent_of_builds() -> None:
    jobs = workflow_jobs()
    for name in (
        "release_version",
        "metadata-and-boundary",
        "python",
        "sandbox",
        "submission-link",
    ):
        body = jobs[name]
        assert "    if:" not in body, name
        assert "    needs:" not in body, name
        assert "DUSART_CI_BUILDS" not in body, name
