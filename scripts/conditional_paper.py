"""Generate the separate conditional paper only from an exact successful audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

from scripts.conditional_release_receipt import clean_commit, validate_receipt

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = Path("paper/conditional-paper.tex")


def render(root: Path, destination: Path, commit: str, toolchain: str) -> Path:
    """Render provenance; callers must validate the audit before publication."""
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("paper needs a full commit SHA")
    if not re.fullmatch(r"[a-zA-Z0-9./:+-]+", toolchain):
        raise ValueError("unsafe paper toolchain identifier")
    source = (root / TEMPLATE).read_text()
    for name, value in (("COMMIT", commit), ("TOOLCHAIN", toolchain)):
        if source.count(f"@@{name}@@") != 1:
            raise ValueError(f"paper must have exactly one {name} field")
        source = source.replace(f"@@{name}@@", value)
    # The template's explanatory comment is not a substitution field.
    if re.search(r"@@[A-Z]+@@", source):
        raise ValueError("unresolved conditional paper provenance")
    destination.mkdir(parents=True, exist_ok=True)
    output = destination / "conditional-paper.tex"
    output.write_text(source)
    return output


def compile_paper(source: Path, epoch: str) -> Path:
    if not epoch.isdigit():
        raise ValueError("source date must be a nonnegative epoch")
    environment = os.environ | {"SOURCE_DATE_EPOCH": epoch, "FORCE_SOURCE_DATE": "1", "TZ": "UTC"}
    for _ in range(2):
        subprocess.run(
            [
                "pdflatex",
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-file-line-error",
                source.name,
            ],
            cwd=source.parent,
            env=environment,
            check=True,
        )
    log = source.with_suffix(".log").read_text()
    for marker in (
        "undefined references",
        "undefined citations",
        "Rerun to get cross-references",
        "Overfull ",
    ):
        if marker in log:
            raise ValueError(f"conditional paper has {marker}")
    pdf = source.with_suffix(".pdf")
    text = subprocess.check_output(["pdftotext", "-layout", str(pdf), "-"], text=True)
    for required in ("conditional", "Jonas Whidden", "Apache License 2.0", "CC BY 4.0"):
        if required not in text:
            raise ValueError(f"conditional PDF is missing {required}")
    subprocess.run(["pdfinfo", str(pdf)], check=True)
    return pdf


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    clean_commit(ROOT, args.commit)
    receipt = validate_receipt(ROOT, json.loads(args.receipt.read_text()), args.commit)
    source = render(ROOT, args.output.resolve(), args.commit, receipt["toolchain"])
    epoch = subprocess.check_output(
        ["git", "show", "-s", "--format=%ct", args.commit], cwd=ROOT, text=True
    ).strip()
    pdf = compile_paper(source, epoch)
    shutil.copyfile(args.receipt, source.parent / "conditional-audit.json")
    shutil.copyfile(
        ROOT / "paper/conditional-resources.json", source.parent / "conditional-resources.json"
    )
    provenance = {
        "conditional": True,
        "commit": args.commit,
        "statement": receipt["statement"],
        "sha256": {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (
                source,
                pdf,
                source.parent / "conditional-audit.json",
                source.parent / "conditional-resources.json",
            )
        },
    }
    (source.parent / "paper-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")


if __name__ == "__main__":
    main()
