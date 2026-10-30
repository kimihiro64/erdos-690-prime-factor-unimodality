"""Restore unchanged unconditional proof artifacts before per-unit replay.

Trigger: a replay with an unchanged proof closure. Require matching locked
configuration/source keys and a successful theorem/axiom receipt before download.
Never depend solely on draft checkpoint stores: they may disappear independently
of source changes. Lake must validate restored targets without compiling, and the
current Challenge, Solution, axiom and independent checker gates still run.
"""

from __future__ import annotations

import json
import shutil
import tempfile
from collections.abc import Callable
from pathlib import Path
from typing import Any

from scripts.conditional_complete_restore import artifact_names, candidate_runs, download
from scripts.conditional_dusart_plan import Unit, required_artifacts


def validate_receipt(
    root: Path,
    units: list[Unit],
    receipt: dict[str, Any],
    commit: str,
    check_report: Callable[[str], None],
) -> None:
    if (
        receipt.get("commit") != commit
        or receipt.get("conditional") is not False
        or receipt.get("targets") != ["PrimeFactorUnimodality", "Challenge", "Solution"]
        or receipt.get("toolchain") != (root / "lean-toolchain").read_text().strip()
        or receipt.get("unit_keys") != [unit.key for unit in units]
        or receipt.get("statement")
        != "PrimeFactorUnimodality.completeClassification : "
        "PrimeFactorUnimodality.CompleteClassification"
        or not isinstance(receipt.get("axiom_reports"), str)
    ):
        raise ValueError("complete unconditional proof has different source/configuration")
    check_report(receipt["axiom_reports"])


def restore_build(root: Path, bundle: Path, units: list[Unit]) -> None:
    """Preflight the entire artifact before copying only into .lake/build."""
    destination = root / ".lake/build"
    required = {
        path.relative_to(".lake/build") for unit in units for path in required_artifacts(unit)
    }
    if not required or any(not (bundle / name).is_file() for name in required):
        raise ValueError("incomplete unconditional build artifact")
    files = sorted(bundle.rglob("*"))
    for source in files:
        target = destination / source.relative_to(bundle)
        if (
            source.is_symlink()
            or not (source.is_file() or source.is_dir())
            or any(path.is_symlink() for path in (target, *target.parents))
        ):
            raise ValueError("unsafe unconditional build artifact path")
    for source in files:
        target = destination / source.relative_to(bundle)
        if source.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)


def restore_complete(
    root: Path,
    units: list[Unit],
    repo: str,
    current_run: str,
    *,
    check_report: Callable[[str], None],
) -> bool:
    research = root / ".research"
    research.mkdir(exist_ok=True)
    for run in candidate_runs(repo, current_run, workflow="ci.yml"):
        run_id = int(run["id"])
        if not {"unconditional-proof-audit", "linux-lean-build"} <= artifact_names(repo, run_id):
            continue
        with tempfile.TemporaryDirectory(prefix="unconditional-restore-", dir=research) as name:
            scratch = Path(name)
            download(repo, run_id, "unconditional-proof-audit", scratch / "audit")
            receipt = json.loads((scratch / "audit/unconditional-audit.json").read_text())
            try:
                validate_receipt(root, units, receipt, run["head_sha"], check_report)
            except ValueError:
                print(f"Unconditional proof from run {run_id} has different source/configuration")
                continue
            print(f"Restoring complete unconditional build from run {run_id}", flush=True)
            download(repo, run_id, "linux-lean-build", scratch / "build")
            restore_build(root, scratch / "build", units)
            return True
    print("No matching complete unconditional build; resuming per-unit checkpoints", flush=True)
    return False
