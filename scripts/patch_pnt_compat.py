"""Apply audited Lean 4.34 API ports to the exact locked PNT sources.

No theorem statements change. Original sources are read from the pinned Git
object; all target files are validated before any write. An unrelated local
edit, wrong revision, or missing replacement is an error, never overwritten.
Re-running the command preserves already-patched files and all build caches.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Final

ROOT = Path(__file__).resolve().parents[1]
REVISION: Final = "f6147e7572ab3abe5428101bc0b13627bcb005df"
PREFIX: Final = "PrimeNumberTheoremAnd/Mathlib/"
CHANGES: Final[dict[str, tuple[tuple[str, str], ...]]] = {
    "Analysis/Complex/CanonicalProduct.lean": (
        ("rw [hE, logDeriv_mul z hf", "rw [hE, logDeriv_fun_mul z hf"),
    ),
    "Analysis/Complex/CartanProductBound.lean": (
        ("Finset.prod_le_prod ha hab", "Finset.prod_le_prod₀ ha hab"),
    ),
    "Analysis/Complex/CartanBound.lean": (
        (
            "Real.posLog_le_posLog (by positivity) hdiv",
            "Real.posLog_le_posLog (by linarith [one_div_nonneg.mpr (norm_nonneg "
            "((1 : ℂ) - w))]) hdiv",  # noqa: RUF001 (Lean's complex-number type)
        ),
        (
            "Real.posLog_le_posLog (by positivity) hfrac",
            "Real.posLog_le_posLog (by linarith [one_div_nonneg.mpr (abs_nonneg (1 - t))]) hfrac",
        ),
    ),
    "Analysis/SpecialFunctions/Gamma/GammaStirlingAux.lean": (
        (
            "apply Finset.prod_le_prod (fun k _ => norm_nonneg _)",
            "apply Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)",
        ),
    ),
}


def patched_source(original: str, replacements: tuple[tuple[str, str], ...]) -> str:
    """Produce the exact API port, rejecting ambiguous or missing edit sites."""
    result = original
    for before, after in replacements:
        if result.count(before) != 1:
            raise ValueError(f"expected one edit site: {before!r}")
        result = result.replace(before, after, 1)
    return result


def validate_current(current: str, original: str, patched: str) -> bool:
    """Return whether a write is needed; reject every other source state."""
    if current == patched:
        return False
    if current != original:
        raise ValueError("source has unrelated local edits; refusing to overwrite")
    return True


def git_output(package: Path, *args: str) -> str:
    """Read an exact Git object without fetching or changing the checkout."""
    return subprocess.check_output(["git", "-C", str(package), *args], text=True)


def apply_patches(root: Path, *, check: bool = False) -> int:
    """Validate the locked revision and all files, then apply only these ports."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    locked = next(p for p in manifest["packages"] if p["name"] == "PrimeNumberTheoremAnd")
    if locked["rev"] != REVISION:
        raise ValueError("PNT lock revision changed; review compatibility patches first")
    package = root / ".lake/packages/PrimeNumberTheoremAnd"
    if git_output(package, "rev-parse", "HEAD").strip() != REVISION:
        raise ValueError("PNT checkout does not match the reviewed revision")
    pending: list[tuple[Path, str]] = []
    for relative, replacements in CHANGES.items():
        relative = PREFIX + relative
        path = package / relative
        if path.is_symlink() or not path.resolve().is_relative_to(package.resolve()):
            raise ValueError(f"unsafe source path: {relative}")
        original = git_output(package, "show", f"{REVISION}:{relative}")
        patched = patched_source(original, replacements)
        if validate_current(path.read_text(), original, patched):
            pending.append((path, patched))
    if check and pending:
        raise ValueError(f"{len(pending)} PNT compatibility ports have not been applied")
    for path, patched in pending:
        path.write_text(patched)
    return len(pending)


def main() -> None:
    """Command-line entry point used locally and by every Lean CI job."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify without modifying files")
    args = parser.parse_args()
    changed = apply_patches(ROOT, check=args.check)
    print(f"PNT Lean 4.34 compatibility: {changed} files updated ({len(CHANGES)} verified)")


if __name__ == "__main__":
    main()
