"""Replay only the all-k proof conditional on the single log-square theta estimate.

No thread limits: owned targets are explicitly topologically ordered. Completed
units are saved immediately, before later targets can fail. A complete restored
proof is validated in one Lake invocation without enabling recompilation.
Re-dispatch this workflow to resume; an incomplete run never claims that the theorem passed.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

from scripts.conditional_complete_restore import restore_complete
from scripts.conditional_dusart_checkpoints import Store, pack, restore
from scripts.conditional_dusart_plan import (
    TARGET,
    THEOREM,
    Unit,
    plan,
    required_artifacts,
    stage_units,
)
from scripts.conditional_release_receipt import check_report, clean_commit, make_receipt

ROOT = Path(__file__).resolve().parents[1]


def run_lake(root: Path, targets: tuple[str, ...], deadline: float, *, check: bool) -> int:
    """Only validation accepts several targets; actual builds remain serial."""
    if not targets or (not check and len(targets) != 1):
        raise ValueError("builds require one target; validation requires nonempty targets")
    if time.monotonic() >= deadline:
        raise TimeoutError("budget reached before starting Lake; re-dispatch to resume")
    started = time.monotonic()
    label = f"Checking {len(targets)} cached targets" if check else f"Building {targets[0]}"
    command = ["lake", "build", "--log-level=error"]
    if check:
        command += ["--no-build", "-q"]
    command += [f"+{target}" for target in targets]
    print(f"::group::{label}", flush=True)
    try:
        with subprocess.Popen(command, cwd=root, start_new_session=True) as p:
            while True:
                try:
                    status = p.wait(timeout=max(0, min(30, deadline - time.monotonic())))
                    if status != 0 and not (check and status == 3):
                        raise subprocess.CalledProcessError(status, p.args)
                    return status
                except subprocess.TimeoutExpired:
                    print(f"{label}: {time.monotonic() - started:.0f}s elapsed", flush=True)
                    if time.monotonic() >= deadline:
                        # Terminate this process group only, leaving uploaded checkpoints intact.
                        import signal

                        os.killpg(p.pid, signal.SIGTERM)
                        try:
                            p.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            os.killpg(p.pid, signal.SIGKILL)
                            p.wait()
                        raise TimeoutError(f"time budget reached: {label}") from None
    finally:
        print(f"Target elapsed: {time.monotonic() - started:.1f}s\n::endgroup::", flush=True)


def build(root: Path, target: str, deadline: float) -> None:
    """Compile one owned target after its owned predecessors have been checked."""
    run_lake(root, (target,), deadline, check=False)


def validate_cached(root: Path, targets: tuple[str, ...], deadline: float) -> None:
    """Skip fresh batches; bisect stale batches and repair in dependency order.

    Lake's --no-build returns 3 for stale targets and never runs a compiler.
    Other failures remain fatal. Checking the right half after repairing the
    left avoids unnecessary builds when their only stale input was on the left.
    """
    if not targets or run_lake(root, targets, deadline, check=True) == 0:
        return
    if len(targets) == 1:
        build(root, targets[0], deadline)
        return
    middle = len(targets) // 2
    validate_cached(root, targets[:middle], deadline)
    validate_cached(root, targets[middle:], deadline)


def replay_units(
    root: Path,
    units: list[Unit],
    repo: str,
    commit: str,
    deadline: float,
    *,
    read_only: bool,
) -> None:
    """Check each restored prefix once, including the entire proof on a warm run.

    Collect local and downloaded artifacts before starting Lake. A fresh complete
    closure needs one --no-build invocation, not one per checkpoint or batch.
    Stale prefixes are repaired unit by unit so each completed unit can be saved
    before any later compilation fails. Checkpoint identities stay unchanged.
    """
    research = root / ".research"
    research.mkdir(exist_ok=True)
    stores: dict[str, Store] = {}
    pending: list[Unit] = []

    def save(unit: Unit) -> None:
        store = stores[unit.phase]
        if unit.asset in store.assets or store.read_only:
            return
        with tempfile.TemporaryDirectory(prefix="conditional-save-", dir=research) as name:
            archive = Path(name) / unit.asset
            pack(root, unit, archive)
            store.upload(unit, archive)
            print(f"Saved {unit.asset}", flush=True)

    def flush() -> None:
        if not pending:
            return
        targets = tuple(module for unit in pending for module in unit.modules)
        fresh = run_lake(root, targets, deadline, check=True) == 0
        for unit in pending:
            if not fresh:
                validate_cached(root, unit.modules, deadline)
            save(unit)
        pending.clear()

    for index, unit in enumerate(units):
        if time.monotonic() >= deadline:
            raise TimeoutError("budget reached at checkpoint boundary; re-dispatch to resume")
        print(f"Checkpoint {index + 1}/{len(units)} ({unit.phase})", flush=True)
        if unit.phase not in stores:
            stores[unit.phase] = Store(repo, unit.phase, commit, read_only=read_only)
        store = stores[unit.phase]
        with tempfile.TemporaryDirectory(prefix="conditional-", dir=research) as name:
            scratch = Path(name)
            local = all((root / path).is_file() for path in required_artifacts(unit))
            downloaded = None if local else store.download(unit, scratch)
            if downloaded:
                restore(root, unit, downloaded)
                print(f"Restored {unit.asset}", flush=True)
            if local or downloaded is not None:
                pending.append(unit)
                continue
            # Finish every predecessor before permitting any new compilation.
            flush()
            for module in unit.modules:
                build(root, module, deadline)
            save(unit)
    flush()


def audit(root: Path, scratch: Path) -> dict[str, str]:
    for source in ("TailThetaBounds", "ConditionalTheta", "DusartPublishedAnchors"):
        subprocess.run(["lake", "env", "lean", f"test/lean/{source}.lean"], cwd=root, check=True)
    probe = scratch / "ConditionalAxioms.lean"
    probe.write_text(f"import {TARGET}\n#check @{THEOREM}\n#print axioms {THEOREM}\n")
    result = subprocess.run(
        ["lake", "env", "lean", str(probe)],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    )
    print(result.stdout, flush=True)
    check_report(result.stdout)
    return {THEOREM: result.stdout}


def replay_proof(
    root: Path, units: list[Unit], repo: str, commit: str, deadline: float, *, read_only: bool
) -> None:
    """A complete saved closure bypasses every per-module checkpoint replay."""
    if restore_complete(root, repo, os.environ.get("GITHUB_RUN_ID", "")):
        if run_lake(root, (TARGET,), deadline, check=True) == 0:
            print("Complete conditional proof validated once; no certificate replay needed")
            return
        print("Complete artifact has stale Lake traces; repairing from durable checkpoints")
    replay_units(root, units, repo, commit, deadline, read_only=read_only)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--minutes", type=int, default=280)
    parser.add_argument("--unit-size", type=int, default=16)
    parser.add_argument("--stage", choices=("foundations", "prebuild", "build"), default="build")
    args = parser.parse_args()
    units = stage_units(plan(ROOT, args.unit_size), args.stage)
    print(
        f"{sum(len(u.modules) for u in units)} modules in {len(units)} checkpoint units", flush=True
    )
    if args.plan:
        for index, unit in enumerate(units):
            print(f"{index + 1}: {unit.phase} {unit.key[:12]} {unit.modules[-1]}")
        return
    if args.minutes <= 0:
        parser.error("minutes must be positive")
    repo = os.environ["GITHUB_REPOSITORY"]
    commit = os.environ["GITHUB_SHA"]
    clean_commit(ROOT, commit)
    deadline = time.monotonic() + args.minutes * 60
    research = ROOT / ".research"
    research.mkdir(exist_ok=True)
    replay = replay_proof if args.stage == "build" else replay_units
    replay(
        ROOT,
        units,
        repo,
        commit,
        deadline,
        read_only=os.environ.get("GITHUB_EVENT_NAME") == "pull_request",
    )
    if args.stage != "build":
        print(
            f"PASS: conditional {args.stage} stage; final theorem audit still required", flush=True
        )
        return
    with tempfile.TemporaryDirectory(prefix="conditional-audit-", dir=research) as name:
        reports = audit(ROOT, Path(name))
    clean_commit(ROOT, commit)
    receipt = make_receipt(ROOT, commit, reports, args.unit_size)
    (research / "conditional-audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(
        "PASS: all-k theorem conditional on one theta estimate, including axiom audit", flush=True
    )


if __name__ == "__main__":
    main()
