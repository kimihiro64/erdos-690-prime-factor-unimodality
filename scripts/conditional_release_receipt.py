"""Bind conditional publication to the exact audited theorem and source closure."""

from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path
from typing import Any

from scripts.conditional_dusart_plan import CONFIG, TARGET, THEOREM, plan

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
HYPOTHESIS = "PrimeFactorUnimodality.HasThetaLogSquaredError (1 / 5) 3594641"
CONCLUSION = "PrimeFactorUnimodality.CompleteClassification"
STATEMENT = f"{THEOREM} : {HYPOTHESIS} → {CONCLUSION}"


def check_axioms(output: str, theorem: str = THEOREM) -> None:
    match = re.search(rf"'{re.escape(theorem)}' depends on axioms:\s*\[([^]]*)\]", output)
    if match is None:
        raise ValueError("missing conditional theorem axiom report")
    axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
    if not axioms <= STANDARD_AXIOMS:
        raise ValueError(f"unexpected theorem axioms: {sorted(axioms - STANDARD_AXIOMS)}")


def check_report(output: str) -> None:
    """Check both the displayed complete type and the independently printed axioms."""
    check_axioms(output)
    displayed = output.split(f"'{THEOREM}' depends on axioms:", 1)[0]
    if " ".join(displayed.split()) != STATEMENT:
        raise ValueError("conditional theorem type differs from the advertised statement")


def clean_commit(root: Path, expected: str) -> None:
    """A release receipt must never certify a dirty tree or a different checkout."""
    if not re.fullmatch(r"[0-9a-f]{40}", expected):
        raise ValueError("expected a full release commit SHA")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=root, text=True)
    if head != expected or dirty:
        raise ValueError("conditional publication requires the clean exact audited commit")


def make_receipt(
    root: Path, commit: str, reports: dict[str, str], unit_size: int = 16
) -> dict[str, Any]:
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("expected a full audit commit SHA")
    if set(reports) != {THEOREM}:
        raise ValueError("receipt must audit only the primary conditional theorem")
    check_report(reports[THEOREM])
    return {
        "schema": 1,
        "commit": commit,
        "targets": [TARGET],
        "statement": STATEMENT,
        "conditional": True,
        "toolchain": (root / "lean-toolchain").read_text().strip(),
        "configuration_sha256": {
            name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in CONFIG
        },
        "unit_size": unit_size,
        "unit_keys": [unit.key for unit in plan(root, unit_size)],
        "axiom_reports": reports,
    }


def validate_receipt(root: Path, receipt: Any, commit: str) -> dict[str, Any]:
    """Fail closed for old receipts, stale sources, alternate targets, or extra assumptions."""
    if not isinstance(receipt, dict):
        raise ValueError("receipt must be an object")
    reports = receipt.get("axiom_reports")
    size = receipt.get("unit_size")
    if (
        not isinstance(reports, dict)
        or any(not isinstance(k, str) or not isinstance(v, str) for k, v in reports.items())
        or type(size) is not int
        or not 1 <= size <= 1024
    ):
        raise ValueError("invalid conditional audit receipt fields")
    expected = make_receipt(root, commit, reports, size)
    if receipt != expected:
        raise ValueError("receipt does not match this commit, configuration, or proof closure")
    return expected
