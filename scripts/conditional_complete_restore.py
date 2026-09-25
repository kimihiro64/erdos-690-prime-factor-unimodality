"""Restore a previously audited complete closure, including dependency artifacts.

Only completed main-branch push/manual runs of this repository are candidates.
The overall workflow may have failed after the proof passed. Source/configuration
Merkle keys, theorem/axiom receipt and every archived byte must still match.
Lake subsequently validates the restored target once; this is not a new audit.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path
from typing import Any

from scripts.conditional_release_bundle import verify_parts
from scripts.conditional_release_receipt import validate_receipt


def candidate_runs(repo: str, current_run: str) -> list[dict[str, Any]]:
    result = subprocess.check_output(
        [
            "gh",
            "api",
            f"repos/{repo}/actions/workflows/conditional-dusart.yml/runs?branch=main&per_page=30",
        ],
        text=True,
    )
    return [
        run
        for run in json.loads(result)["workflow_runs"]
        if str(run["id"]) != current_run
        and run["status"] == "completed"
        and run["head_branch"] == "main"
        and run["event"] in {"push", "workflow_dispatch"}
        and run["head_repository"]["full_name"] == repo
    ]


def artifact_names(repo: str, run_id: int) -> set[str]:
    result = subprocess.check_output(
        [
            "gh",
            "api",
            f"repos/{repo}/actions/runs/{run_id}/artifacts?per_page=100",
            "--paginate",
            "--jq",
            ".artifacts[] | select(.expired == false) | .name",
        ],
        text=True,
    )
    return set(result.splitlines())


def download(repo: str, run_id: int, name: str, directory: Path) -> None:
    subprocess.run(
        [
            "gh",
            "run",
            "download",
            str(run_id),
            "--repo",
            repo,
            "--name",
            name,
            "--dir",
            str(directory),
        ],
        check=True,
    )


def restore_bundle(root: Path, bundle: Path, receipt: dict[str, Any]) -> None:
    """Validate everything before overwriting regular build artifacts in place."""
    validate_receipt(root, receipt, receipt["commit"])
    if json.loads((bundle / "conditional-audit.json").read_text()) != receipt:
        raise ValueError("complete artifact and audit receipts differ")
    manifest = json.loads((bundle / "conditional-build-manifest.json").read_text())
    if (
        manifest["commit"] != receipt["commit"]
        or manifest["toolchain"] != receipt["toolchain"]
        or manifest["conditional"] is not True
    ):
        raise ValueError("complete artifact provenance differs from its audit")
    verify_parts(bundle, manifest)
    for part in manifest["parts"]:
        for name in part["files"]:
            target = root / name
            if any(path.is_symlink() for path in (target, *target.parents)):
                raise ValueError("symlink destination in complete proof restore")
    for part in manifest["parts"]:
        with tarfile.open(bundle / part["asset"], "r|gz") as archive:
            for member in archive:
                target = root / member.name
                target.parent.mkdir(parents=True, exist_ok=True)
                stream = archive.extractfile(member)
                assert stream is not None  # verify_parts accepted only regular members.
                with target.open("wb") as output:
                    shutil.copyfileobj(stream, output)


def restore_complete(root: Path, repo: str, current_run: str) -> bool:
    """Find matching content across commits without downloading mismatched large bundles."""
    research = root / ".research"
    research.mkdir(exist_ok=True)
    for run in candidate_runs(repo, current_run):
        run_id = int(run["id"])
        if not {"conditional-proof-audit", "conditional-build-release"} <= artifact_names(
            repo, run_id
        ):
            continue
        with tempfile.TemporaryDirectory(prefix="conditional-complete-", dir=research) as name:
            scratch = Path(name)
            download(repo, run_id, "conditional-proof-audit", scratch / "audit")
            receipt = json.loads((scratch / "audit/conditional-audit.json").read_text())
            try:
                validate_receipt(root, receipt, run["head_sha"])
            except ValueError:
                print(f"Complete proof from run {run_id} has different source/configuration")
                continue
            print(f"Restoring complete compiled proof from run {run_id}", flush=True)
            download(repo, run_id, "conditional-build-release", scratch / "bundle")
            restore_bundle(root, scratch / "bundle", receipt)
            print("Restored all project AND imported dependency artifacts", flush=True)
            return True
    print("No matching complete artifact; resuming durable per-unit checkpoints", flush=True)
    return False
