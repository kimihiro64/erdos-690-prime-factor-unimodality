"""Build the elementary public proof with reusable, dependency-checked checkpoints."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

from scripts.conditional_dusart_ci import build, replay_units
from scripts.conditional_dusart_plan import plan
from scripts.conditional_release_receipt import check_axioms, clean_commit

ROOT = Path(__file__).resolve().parents[1]
TARGET = "PrimeFactorUnimodality"
THEOREM = "PrimeFactorUnimodality.completeClassification"
STATEMENT = f"{THEOREM} : PrimeFactorUnimodality.CompleteClassification"
AUDITED = (
    THEOREM,
    "PrimeFactorUnimodality.hasNaturalDensity_primeFactorDensity",
    "ChallengeStatementAudit.exact_challenge_statement",
)


def check_report(output: str) -> None:
    """Require the unconditional type and standard axioms for every audited result."""
    displayed = output.split(f"'{THEOREM}' depends on axioms:", 1)[0]
    if " ".join(displayed.split()) != STATEMENT:
        raise ValueError("unconditional theorem type differs from CompleteClassification")
    for theorem in AUDITED:
        check_axioms(output, theorem)


def audit(root: Path, scratch: Path) -> str:
    """Compile the actual copied Challenge transport and audit that same declaration."""
    source = (root / "test/lean/UnconditionalClassification.lean").read_text(encoding="utf-8")
    source += f"\n#check @{THEOREM}\n"
    source += "".join(f"#print axioms {theorem}\n" for theorem in AUDITED)
    probe = scratch / "UnconditionalAxioms.lean"
    probe.write_text(source, encoding="utf-8")
    result = subprocess.run(
        ["lake", "env", "lean", str(probe)],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    )
    print(result.stdout, flush=True)
    check_report(result.stdout)
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--minutes", type=int, default=280)
    args = parser.parse_args()
    if args.minutes <= 0:
        parser.error("minutes must be positive")
    units = plan(ROOT, target=TARGET)
    print(f"{sum(len(unit.modules) for unit in units)} modules in {len(units)} units")
    if args.plan:
        for unit in units:
            print(f"{unit.phase} {unit.key} {unit.modules[-1]}")
        return
    commit = os.environ["GITHUB_SHA"]
    clean_commit(ROOT, commit)
    deadline = time.monotonic() + args.minutes * 60
    replay_units(
        ROOT,
        units,
        os.environ["GITHUB_REPOSITORY"],
        commit,
        deadline,
        read_only=os.environ.get("GITHUB_EVENT_NAME") == "pull_request",
    )
    # Explicit module targets avoid building every historical library module.
    for target in ("Challenge", "Solution"):
        build(ROOT, target, deadline)
    with tempfile.TemporaryDirectory(prefix="unconditional-audit-", dir=ROOT / ".research") as name:
        report = audit(ROOT, Path(name))
    clean_commit(ROOT, commit)
    receipt = {
        "commit": commit,
        "conditional": False,
        "targets": [TARGET, "Challenge", "Solution"],
        "statement": STATEMENT,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "unit_keys": [unit.key for unit in units],
        "axiom_reports": report,
    }
    (ROOT / ".lake/build/unconditional-audit.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )
    print("PASS: unconditional all-k classification, exact Challenge transport, and axiom audit")


if __name__ == "__main__":
    main()
