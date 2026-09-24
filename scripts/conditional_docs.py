"""Generate only the conditional import closure, admitting doc-info tasks serially."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path

from scripts.conditional_dusart_plan import TARGET
from scripts.conditional_release_bundle import module_artifacts
from scripts.conditional_release_receipt import clean_commit, validate_receipt
from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[1]


def ordered_modules(root: Path) -> list[str]:
    artifacts = module_artifacts(root)
    imports: dict[str, list[str]] = {}
    for module, path in artifacts.items():
        package = Path(path.as_posix().split("/.lake/build/", 1)[0])
        source = package / (module.replace(".", "/") + ".lean")
        imports[module] = lean_imports(strip_lean_comments(source.read_text()))
    ordered: list[str] = []
    seen: set[str] = set()
    visiting: set[str] = set()

    def visit(module: str) -> None:
        if module in seen or module not in imports:
            return
        if module in visiting:
            raise ValueError(f"documentation import cycle: {module}")
        visiting.add(module)
        for dependency in imports[module]:
            visit(dependency)
        visiting.remove(module)
        seen.add(module)
        ordered.append(module)

    visit(TARGET)
    if seen != set(artifacts):
        raise ValueError("documentation source traversal differs from compiled import closure")
    return ordered


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    args = parser.parse_args()
    clean_commit(ROOT, args.commit)
    receipt = validate_receipt(ROOT, json.loads(args.receipt.read_text()), args.commit)
    env = os.environ | {"DISABLE_EQUATIONS": "1", "DOCGEN_SRC": "github"}
    workspace = ROOT / "docbuild"
    build = workspace / ".lake/build"
    build.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lake", "build", "doc-gen4"], cwd=workspace, env=env, check=True)
    # Capture only Lean's search-path settings; never print process credentials.
    selected = subprocess.check_output(
        [
            "lake",
            "env",
            "python3",
            "-c",
            "import json,os; print(json.dumps({k:os.environ[k] "
            "for k in ('LEAN_PATH','LEAN_SRC_PATH','LD_LIBRARY_PATH','LEAN_SYSROOT') "
            "if k in os.environ}))",
        ],
        cwd=workspace,
        env=env,
        text=True,
    )
    env.update(json.loads(selected))
    executable = ROOT / ".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"

    def run(*arguments: str) -> None:
        subprocess.run([str(executable), *arguments], cwd=workspace, env=env, check=True)

    # These are the pinned doc-gen4 facet's commands. Calling them in dependency
    # order also serializes the four core scans, which its coreDocs facet fans out.
    run("bibPrepass", "--build", str(build), "--none")
    state_file = build / "conditional-doc-state.json"
    state: dict[str, str] = {}
    if state_file.is_file() and (build / "api-docs.db").is_file():
        state = json.loads(state_file.read_text())
    seed = hashlib.sha256(
        (ROOT / "docbuild/lake-manifest.json").read_bytes()
        + (ROOT / "lean-toolchain").read_bytes()
        + Path(__file__).read_bytes()
        + b"conditional-docs-v1-disable-equations"
    ).hexdigest()
    core = ("Init", "Std", "Lake", "Lean")
    for module in core:
        key = f"core:{module}"
        if state.get(key) != seed:
            print(f"Core documentation: {module}", flush=True)
            run("genCore", "--build", str(build), module, "api-docs.db")
            state[key] = seed
            state_file.write_text(json.dumps(state))
    modules = ordered_modules(ROOT)
    artifacts = module_artifacts(ROOT)
    package_urls: dict[Path, str] = {}
    for index, module in enumerate(modules, 1):
        package = Path(artifacts[module].as_posix().split("/.lake/build/", 1)[0])
        if package not in package_urls:
            remote = subprocess.check_output(
                ["git", "remote", "get-url", "origin"], cwd=package, text=True
            ).strip()
            if remote.startswith("git@github.com:"):
                remote = remote.replace("git@github.com:", "https://github.com/", 1)
            if not remote.startswith("https://github.com/"):
                raise ValueError(f"unsupported documentation source remote: {remote}")
            revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=package, text=True
            ).strip()
            package_urls[package] = f"{remote.removesuffix('.git')}/blob/{revision}/"
        uri = package_urls[package] + module.replace(".", "/") + ".lean"
        with artifacts[module].open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        key = hashlib.sha256((seed + uri + digest).encode()).hexdigest()
        if state.get(module) == key:
            continue
        print(f"Documentation {index}/{len(modules)}: {module}", flush=True)
        run("single", "--build", str(build), module, "api-docs.db", uri)
        state[module] = key
        state_file.write_text(json.dumps(state))
    run(
        "fromDb",
        "--build",
        str(build),
        "--manifest",
        str(build / "doc-manifest.json"),
        str(build / "api-docs.db"),
        TARGET,
        *core,
    )
    (build / "doc/conditional-audit.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
