"""Replay only the all-k proof conditional on the three named Dusart bounds.

No thread limits: owned targets are explicitly topologically ordered. Completed
units are saved immediately, before later targets can fail. Re-dispatch this
workflow to resume; an incomplete run never claims that the theorem passed.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

from scripts.conditional_dusart_checkpoints import Store, pack, restore
from scripts.conditional_dusart_plan import TARGET, THEOREM, plan

ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


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


def check_axioms(output: str) -> None:
    match = re.search(rf"'{re.escape(THEOREM)}' depends on axioms:\s*\[([^]]*)\]", output)
    if match is None:
        raise ValueError("missing conditional theorem axiom report")
    axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
    if not axioms <= STANDARD_AXIOMS:
        raise ValueError(f"unexpected theorem axioms: {sorted(axioms - STANDARD_AXIOMS)}")


def audit(root: Path, scratch: Path) -> None:
    for source in ("TailThetaBounds", "ConditionalDusart"):
        subprocess.run(["lake", "env", "lean", f"test/lean/{source}.lean"], cwd=root, check=True)
    probe = scratch / "ConditionalAxioms.lean"
    probe.write_text(f"import {TARGET}\n#print axioms {THEOREM}\n")
    result = subprocess.run(
        ["lake", "env", "lean", str(probe)],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    )
    print(result.stdout, flush=True)
    check_axioms(result.stdout)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--minutes", type=int, default=280)
    parser.add_argument("--unit-size", type=int, default=16)
    args = parser.parse_args()
    units = plan(ROOT, args.unit_size)
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
    deadline = time.monotonic() + args.minutes * 60
    research = ROOT / ".research"
    research.mkdir(exist_ok=True)
    stores: dict[str, Store] = {}
    for index, unit in enumerate(units):
        if time.monotonic() >= deadline:
            raise TimeoutError("budget reached at checkpoint boundary; re-dispatch to resume")
        print(f"Checkpoint {index + 1}/{len(units)} ({unit.phase})", flush=True)
        if unit.phase not in stores:
            stores[unit.phase] = Store(repo, unit.phase, commit)
        store = stores[unit.phase]
        with tempfile.TemporaryDirectory(prefix="conditional-", dir=research) as name:
            scratch = Path(name)
            downloaded = store.download(unit, scratch)
            if downloaded:
                restore(ROOT, unit, downloaded)
                print(f"Restored {unit.asset}", flush=True)
            # Lake checks restored traces too. Never jump to an aggregate that
            # could unexpectedly fan out across absent owned dependencies.
            for module in unit.modules:
                build(ROOT, module, deadline)
            if downloaded is None:
                archive = scratch / unit.asset
                pack(ROOT, unit, archive)
                store.upload(unit, archive)
                print(f"Saved {unit.asset}", flush=True)
    with tempfile.TemporaryDirectory(prefix="conditional-audit-", dir=research) as name:
        audit(ROOT, Path(name))
    print("PASS: exact all-k theorem checked with three explicit Dusart hypotheses", flush=True)


if __name__ == "__main__":
    main()
