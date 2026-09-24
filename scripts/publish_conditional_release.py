"""Publish a conditional prerelease only after all original non-Comparator gates."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
import zipfile
from pathlib import Path
from typing import Any

from scripts.conditional_docs import verify_pages
from scripts.conditional_dusart_plan import TARGET
from scripts.conditional_release_bundle import sha256, verify_parts
from scripts.conditional_release_receipt import clean_commit, validate_receipt

ROOT = Path(__file__).resolve().parents[1]


def regular_file(directory: Path, name: str) -> Path:
    if Path(name).name != name or name in {"", ".", ".."}:
        raise ValueError(f"unsafe release asset name: {name}")
    path = directory / name
    if path.is_symlink() or not path.is_file() or path.stat().st_size <= 0:
        raise ValueError(f"missing or invalid release asset: {name}")
    return path


def verify_hashes(directory: Path, hashes: dict[str, str]) -> None:
    for name, digest in hashes.items():
        if sha256(regular_file(directory, name)) != digest:
            raise ValueError(f"release artifact hash mismatch: {name}")


def prepare(root: Path, inputs: Path, output: Path, commit: str) -> dict[str, Any]:
    build = inputs / "build"
    paper = inputs / "paper"
    docs = inputs / "docs"
    receipt = validate_receipt(
        root, json.loads((build / "conditional-audit.json").read_text()), commit
    )
    paper_receipt = validate_receipt(
        root, json.loads((paper / "conditional-audit.json").read_text()), commit
    )
    if paper_receipt != receipt:
        raise ValueError("paper and compiled proof have different audit receipts")
    docs_receipt = validate_receipt(
        root, json.loads((docs / "conditional-audit.json").read_text()), commit
    )
    if docs_receipt != receipt:
        raise ValueError("documentation and compiled proof have different audit receipts")
    manifest = json.loads((build / "conditional-build-manifest.json").read_text())
    if manifest["commit"] != commit or manifest["conditional"] is not True:
        raise ValueError("wrong compiled conditional provenance")
    if TARGET not in manifest["modules"]:
        raise ValueError("compiled closure omits the conditional target")
    hashes = manifest["other_sha256"] | {
        part["asset"]: part["sha256"] for part in manifest["parts"]
    }
    verify_hashes(build, hashes)
    if "conditional-audit.json" not in hashes or not manifest["parts"]:
        raise ValueError("compiled bundle is missing its audit or archive parts")
    if set(manifest["other_sha256"]) != {
        "conditional-audit.json",
        "conditional-licenses.tar.gz",
        "conditional-source.tar.gz",
    }:
        raise ValueError("compiled bundle is missing its source or licensing provenance")
    verify_parts(build, manifest)
    paper_metadata = json.loads((paper / "paper-provenance.json").read_text())
    if (
        paper_metadata["commit"] != commit
        or paper_metadata["conditional"] is not True
        or paper_metadata["statement"] != receipt["statement"]
    ):
        raise ValueError("wrong conditional paper provenance")
    verify_hashes(paper, paper_metadata["sha256"])
    if set(paper_metadata["sha256"]) != {
        "conditional-audit.json",
        "conditional-paper.tex",
        "conditional-paper.pdf",
        "conditional-resources.json",
    }:
        raise ValueError("paper provenance does not cover every required artifact")
    verify_pages(docs, manifest["modules"])
    for relative in ("index.html", "licensing/index.html", TARGET.replace(".", "/") + ".html"):
        if not (docs / relative).is_file():
            raise ValueError(f"conditional documentation missing: {relative}")
    if "HasThetaLogSquaredError" not in (docs / "index.html").read_text():
        raise ValueError("documentation does not disclose the analytic hypothesis")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("refusing to mix release assets in a nonempty output directory")
    for name in [*hashes, "conditional-build-manifest.json"]:
        shutil.copyfile(regular_file(build, name), output / name)
    for name in (
        "conditional-paper.pdf",
        "conditional-paper.tex",
        "conditional-resources.json",
        "paper-provenance.json",
    ):
        shutil.copyfile(regular_file(paper, name), output / name)
    with zipfile.ZipFile(
        output / "conditional-api-documentation.zip", "w", zipfile.ZIP_DEFLATED
    ) as zip_:
        for path in sorted(docs.rglob("*")):
            if path.is_symlink():
                raise ValueError(f"symlink in documentation: {path}")
            if path.is_file():
                zip_.write(path, path.relative_to(docs))
    assets = {
        path.name: {"sha256": sha256(path), "bytes": path.stat().st_size}
        for path in output.iterdir()
        if path.is_file()
    }
    if any(path.stat().st_size >= 2_000_000_000 for path in output.iterdir()):
        raise ValueError("conditional release asset exceeds the per-file size limit")
    result = {
        "conditional": True,
        "commit": commit,
        "statement": receipt["statement"],
        "comparator": "not run: conditional theorem, not unconditional Challenge",
        "assets": assets,
    }
    (output / "conditional-release-manifest.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def publish(repo: str, tag: str, commit: str, output: Path, metadata: dict[str, Any]) -> None:
    """Complete a draft, verify all uploaded bytes, then mark it as a prerelease."""
    if not re.fullmatch(r"v\d+\.\d+\.\d+-conditional\." + re.escape(commit[:12]), tag):
        raise ValueError("conditional release tag must be separate and commit-specific")
    lookup = subprocess.run(
        ["gh", "api", f"repos/{repo}/releases/tags/{tag}"], text=True, capture_output=True
    )
    existing = None
    if lookup.returncode == 0:
        existing = json.loads(lookup.stdout)
        if existing["target_commitish"] != commit or not existing["prerelease"]:
            raise ValueError("existing tag is not this exact conditional prerelease")
    elif "404" not in lookup.stderr:
        raise RuntimeError(lookup.stderr)
    notes = (
        f"Conditional Lean formalization at `{commit}`.\n\n"
        f"Proved statement: `{metadata['statement']}`. The unbounded theta estimate remains "
        "an explicit hypothesis; this is NOT an unconditional solution.\n\n"
        "The original non-Comparator CI stages gate publication: metadata/source boundary, "
        "Python tests, sandbox policy, licensing, separated foundations and high-memory "
        "prebuilds, analytic reduction, complete conditional build, Lean linting, paper, "
        "documentation, and submission-link checks. Comparator and its associated NanoDa "
        "replay were not run; no such certification is claimed.\n\n"
        "See conditional-release-manifest.json for SHA-256 hashes, the build manifest for "
        "the compiled transitive closure and reuse instructions, the audit for the exact "
        "theorem type and axioms, and the separate conditional paper for mathematical scope "
        "and resource limitations. Original paper source remains in the source snapshot.\n"
    )
    with tempfile.TemporaryDirectory(prefix="publish-", dir=output.parent) as temporary:
        scratch = Path(temporary)
        note_file = scratch / "notes.md"
        note_file.write_text(notes)
        if existing is None:
            subprocess.run(
                [
                    "gh",
                    "release",
                    "create",
                    tag,
                    "--repo",
                    repo,
                    "--target",
                    commit,
                    "--title",
                    f"Conditional all-k formalization {tag}",
                    "--notes-file",
                    str(note_file),
                    "--draft",
                    "--prerelease",
                ],
                check=True,
            )
        if existing is None or existing["draft"]:
            subprocess.run(
                [
                    "gh",
                    "release",
                    "upload",
                    tag,
                    "--repo",
                    repo,
                    "--clobber",
                    *map(str, sorted(output.iterdir())),
                ],
                check=True,
            )
            subprocess.run(
                ["gh", "release", "edit", tag, "--repo", repo, "--notes-file", str(note_file)],
                check=True,
            )
        # This also verifies immutable already-published assets on a rerun. A
        # conflicting public release is never overwritten or silently accepted.
        verified = scratch / "verified"
        subprocess.run(
            ["gh", "release", "download", tag, "--repo", repo, "--dir", str(verified)], check=True
        )
        expected = {path.name: sha256(path) for path in output.iterdir()}
        if {path.name for path in verified.iterdir()} != set(expected):
            raise ValueError("uploaded release asset set differs from the verified local set")
        verify_hashes(verified, expected)
        subprocess.run(
            [
                "gh",
                "release",
                "edit",
                tag,
                "--repo",
                repo,
                "--draft=false",
                "--prerelease",
                "--latest=false",
            ],
            check=True,
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    args = parser.parse_args()
    clean_commit(ROOT, args.commit)
    metadata = prepare(ROOT, args.inputs, args.output, args.commit)
    publish(
        os.environ["GITHUB_REPOSITORY"],
        os.environ["RELEASE_TAG"],
        args.commit,
        args.output,
        metadata,
    )


if __name__ == "__main__":
    main()
