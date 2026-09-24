"""Package the complete imported Lean artifact closure of the conditional theorem."""

from __future__ import annotations

import argparse
import gzip
import json
import re
import subprocess
import tarfile
from pathlib import Path
from typing import Any

from scripts.conditional_dusart_checkpoints import file_hash
from scripts.conditional_dusart_plan import ARTIFACT_SUFFIXES, TARGET
from scripts.conditional_release_receipt import clean_commit, validate_receipt

ROOT = Path(__file__).resolve().parents[1]
MAX_PART_BYTES = 1_000_000_000  # Raw size, leaving ample room below the release asset limit.


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return file_hash(stream)


def module_artifacts(root: Path) -> dict[str, Path]:
    """Read Lake's actual compiled transitive import closure, not a source guess."""
    setup = root / ".lake/build/ir" / (TARGET.replace(".", "/") + ".setup.json")
    data = json.loads(setup.read_text())
    if data["name"] != TARGET or data["plugins"] or data["dynlibs"]:
        raise ValueError("unexpected target or dynamically loaded proof dependencies")
    modules: dict[str, Path] = {}
    for module, groups in data["importArts"].items():
        paths = [Path(name) for group in groups for name in group]
        oleans = [path for path in paths if path.suffix == ".olean"]
        if len(oleans) != 1:
            raise ValueError(f"missing or ambiguous compiled dependency: {module}")
        for path in paths:
            if not path.is_absolute():
                path = root / path
            relative = path.resolve().relative_to(root.resolve())
            if not safe_build_path(relative) or not path.is_file() or path.is_symlink():
                raise ValueError(f"invalid compiled dependency: {path}")
        modules[module] = oleans[0] if oleans[0].is_absolute() else root / oleans[0]
    modules[TARGET] = root / ".lake/build/lib/lean" / (TARGET.replace(".", "/") + ".olean")
    for module, path in modules.items():
        expected = "/lib/lean/" + module.replace(".", "/") + ".olean"
        if not path.as_posix().endswith(expected) or not path.is_file():
            raise ValueError(f"artifact path does not match module {module}")
    return modules


def safe_build_path(path: Path) -> bool:
    """Only build artifacts can appear in the compiled archive."""
    if path.is_absolute() or ".." in path.parts:
        return False
    return bool(
        re.fullmatch(r"\.lake/(?:packages/[^/]+/\.lake/)?build/(?:lib/lean|ir)/.+", path.as_posix())
    )


def closure_files(root: Path, modules: dict[str, Path]) -> list[Path]:
    result: set[Path] = set()
    for module, olean in modules.items():
        stem = olean.with_suffix("")
        prefix = olean.as_posix().split("/lib/lean/", 1)[0]
        ir = Path(prefix) / "ir" / module.replace(".", "/")
        candidates = [Path(str(stem) + suffix) for suffix in ARTIFACT_SUFFIXES]
        candidates += [Path(str(ir) + suffix) for suffix in (".c", ".bc", ".setup.json")]
        candidates += [Path(str(path) + ".hash") for path in list(candidates)]
        for path in candidates:
            if path.is_file():
                relative = path.resolve().relative_to(root.resolve())
                if not safe_build_path(relative) or path.is_symlink():
                    raise ValueError(f"unsafe archive member: {path}")
                result.add(relative)
    return sorted(result)


def archive_parts(root: Path, files: list[Path], output: Path) -> list[dict[str, object]]:
    """Stream bounded archives in place; never duplicate the compiled tree."""
    groups: list[list[Path]] = [[]]
    size = 0
    for path in files:
        length = (root / path).stat().st_size
        if length >= MAX_PART_BYTES:
            raise ValueError(f"single artifact too large for release: {path}")
        if size + length > MAX_PART_BYTES and groups[-1]:
            groups.append([])
            size = 0
        groups[-1].append(path)
        size += length
    records: list[dict[str, object]] = []
    for index, group in enumerate(groups, 1):
        target = output / f"conditional-linux-lean-part{index:03d}.tar.gz"
        hashes: dict[str, str] = {}
        with (
            target.open("wb") as raw,
            gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, compresslevel=1) as zipped,
            tarfile.open(fileobj=zipped, mode="w|") as archive,
        ):
            for path in group:
                hashes[path.as_posix()] = sha256(root / path)
                info = archive.gettarinfo(str(root / path), arcname=path.as_posix())
                info.uid = info.gid = info.mtime = 0
                info.uname = info.gname = ""
                with (root / path).open("rb") as stream:
                    archive.addfile(info, stream)
        records.append({"asset": target.name, "sha256": sha256(target), "files": hashes})
        print(f"Packaged {target.name}: {target.stat().st_size} bytes", flush=True)
    return records


def dependency_notices(root: Path, output: Path) -> None:
    """Include original notices for all pinned proof dependencies and the toolchain."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    with tarfile.open(output / "conditional-licenses.tar.gz", "w:gz") as archive:
        for name in ("LICENSE", "LICENSING.md", "lean-toolchain", "lake-manifest.json"):
            archive.add(root / name, arcname=name, recursive=False)
        for package in manifest["packages"]:
            name = package["name"].strip("«»")
            directory = root / ".lake/packages" / name
            revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=directory, text=True
            ).strip()
            if revision != package["rev"]:
                raise ValueError(f"dependency revision differs from lock: {name}")
            notices = [
                path
                for path in directory.iterdir()
                if path.is_file()
                and re.match(r"^(LICENSE|LICENCE|COPYING|NOTICE)", path.name, re.I)
            ]
            if not notices:
                raise ValueError(f"no licensing notice for {name}")
            for path in notices:
                archive.add(path, arcname=f"dependencies/{name}/{path.name}", recursive=False)
        prefix = Path(
            subprocess.check_output(["lean", "--print-prefix"], cwd=root, text=True).strip()
        )
        notices = [
            path
            for path in prefix.iterdir()
            if path.is_file() and re.match(r"^(LICENSE|LICENCE|COPYING|NOTICE)", path.name, re.I)
        ]
        if not notices:
            raise ValueError("no licensing notice for Lean")
        for path in notices:
            archive.add(path, arcname=f"dependencies/Lean4/{path.name}", recursive=False)


def verify_parts(directory: Path, manifest: dict[str, Any]) -> None:
    """Recheck every archived member without extracting or duplicating the tree."""
    all_names: set[str] = set()
    all_modules: set[str] = set()
    assets: set[str] = set()
    for part in manifest["parts"]:
        name = part["asset"]
        if not re.fullmatch(r"conditional-linux-lean-part[0-9]+\.tar\.gz", name) or name in assets:
            raise ValueError("unsafe or duplicate compiled archive name")
        assets.add(name)
        path = directory / name
        if path.is_symlink() or sha256(path) != part["sha256"]:
            raise ValueError("compiled archive digest mismatch")
        hashes = part["files"]
        seen: set[str] = set()
        with tarfile.open(path, "r|gz") as archive:
            for entry in archive:
                if (
                    not entry.isfile()
                    or not safe_build_path(Path(entry.name))
                    or entry.name in all_names
                    or entry.name not in hashes
                ):
                    raise ValueError("unsafe, duplicate, or unexpected compiled archive member")
                stream = archive.extractfile(entry)
                if stream is None or file_hash(stream) != hashes[entry.name]:
                    raise ValueError("compiled archive member digest mismatch")
                seen.add(entry.name)
                all_names.add(entry.name)
                if entry.name.endswith(".olean"):
                    all_modules.add(entry.name.split("/lib/lean/", 1)[1][:-6].replace("/", "."))
        if seen != set(hashes):
            raise ValueError("compiled archive omits declared files")
    if all_modules != set(manifest["modules"]) or TARGET not in all_modules:
        raise ValueError("compiled archive does not contain the advertised complete module set")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    clean_commit(ROOT, args.commit)
    receipt = validate_receipt(ROOT, json.loads(args.receipt.read_text()), args.commit)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("release output must be empty; refusing to mix artifacts")
    modules = module_artifacts(ROOT)
    parts = archive_parts(ROOT, closure_files(ROOT, modules), output)
    dependency_notices(ROOT, output)
    subprocess.run(
        [
            "git",
            "archive",
            "--format=tar.gz",
            f"--output={output / 'conditional-source.tar.gz'}",
            args.commit,
        ],
        cwd=ROOT,
        check=True,
    )
    (output / "conditional-audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
    manifest = {
        "conditional": True,
        "commit": args.commit,
        "toolchain": receipt["toolchain"],
        "modules": sorted(modules),
        "parts": parts,
        "other_sha256": {
            path.name: sha256(path)
            for path in output.iterdir()
            if path.is_file() and not path.name.startswith("conditional-linux-lean-part")
        },
        "usage": "Install the exact lean-toolchain with elan. Extract every build part at the "
        "repository root, alongside the source snapshot. Fetch the locked dependency sources "
        "with Lake, apply the included compatibility scripts, then import the conditional target. "
        "Core Lean artifacts are supplied by that toolchain, not bundled. This is NOT an "
        "unconditional proof. The explicit theta-error hypothesis remains required.",
    }
    (output / "conditional-build-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
