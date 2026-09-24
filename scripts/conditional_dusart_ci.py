"""Replay only the all-k proof conditional on the single log-square theta estimate.

No thread limits: owned targets are explicitly topologically ordered. Completed
units are saved immediately, before later targets can fail. Re-dispatch this
workflow to resume; an incomplete run never claims that the theorem passed.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

from scripts.conditional_dusart_checkpoints import Store, pack, restore
from scripts.conditional_dusart_plan import TARGET, THEOREM, plan, required_artifacts, stage_units
from scripts.conditional_release_receipt import check_report, clean_commit, make_receipt

ROOT = Path(__file__).resolve().parents[1]


def build(root: Path, target: str, deadline: float) -> None:
    started = time.monotonic()
    print(f"::group::Building {target}", flush=True)
    try:
        with subprocess.Popen(
            ["lake", "build", f"+{target}"], cwd=root, start_new_session=True
        ) as p:
            while True:
                try:
                    status = p.wait(timeout=30)
                    if status:
                        raise subprocess.CalledProcessError(status, p.args)
                    return
                except subprocess.TimeoutExpired:
                    print(f"Still building {target}: {time.monotonic() - started:.0f}s", flush=True)
                    if time.monotonic() >= deadline:
                        # Terminate this process group only, leaving uploaded checkpoints intact.
                        import signal

                        os.killpg(p.pid, signal.SIGTERM)
                        try:
                            p.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            os.killpg(p.pid, signal.SIGKILL)
                            p.wait()
                        raise TimeoutError(f"time budget reached in {target}") from None
    finally:
        print(f"Target elapsed: {time.monotonic() - started:.1f}s\n::endgroup::", flush=True)


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
    stores: dict[str, Store] = {}
    for index, unit in enumerate(units):
        if time.monotonic() >= deadline:
            raise TimeoutError("budget reached at checkpoint boundary; re-dispatch to resume")
        print(f"Checkpoint {index + 1}/{len(units)} ({unit.phase})", flush=True)
        if unit.phase not in stores:
            stores[unit.phase] = Store(
                repo,
                unit.phase,
                commit,
                read_only=os.environ.get("GITHUB_EVENT_NAME") == "pull_request",
            )
        store = stores[unit.phase]
        with tempfile.TemporaryDirectory(prefix="conditional-", dir=research) as name:
            scratch = Path(name)
            local = all((ROOT / path).is_file() for path in required_artifacts(unit))
            downloaded = None if local else store.download(unit, scratch)
            if downloaded:
                restore(ROOT, unit, downloaded)
                print(f"Restored {unit.asset}", flush=True)
            # Lake checks restored traces too. Never jump to an aggregate that
            # could unexpectedly fan out across absent owned dependencies.
            for module in unit.modules:
                build(ROOT, module, deadline)
            if unit.asset not in store.assets and not store.read_only:
                archive = scratch / unit.asset
                pack(ROOT, unit, archive)
                store.upload(unit, archive)
                print(f"Saved {unit.asset}", flush=True)
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
