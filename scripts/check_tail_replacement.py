"""Reject retired full-gap and prime-witness replays in the solution import chain."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.lean_source import lean_imports, strip_lean_comments  # noqa: E402

PREFIX = "PrimeFactorUnimodality.Proof.LargeRange."
FORBIDDEN = (
    PREFIX + "FullRecordRange",
    PREFIX + "Generated.FullRecordGapCompact",
    PREFIX + "Generated.RecordPrimeWitnesses",
)
REQUIRED = PREFIX + "UniformTailClosedMertens"


def solution_closure(root: Path) -> set[str]:
    """Traverse local imports, leaving external dependency modules to Lean."""
    pending = ["Solution"]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            code = strip_lean_comments(path.read_text(encoding="utf-8"))
            pending.extend(lean_imports(code))
    return visited


def check_tail_replacement(root: Path) -> None:
    """Require the analytic replacement and exclude the retired full-gap family."""
    closure = solution_closure(root)
    forbidden = sorted(module for module in closure if module.startswith(FORBIDDEN))
    if forbidden:
        raise ValueError(
            "retired certificate replay reached from Solution: " + ", ".join(forbidden)
        )
    if REQUIRED not in closure:
        raise ValueError("Solution does not reach the uniform CRT replacement")
    print("analytic boundary: uniform tail present; full-gap and prime-witness replays excluded")


if __name__ == "__main__":
    check_tail_replacement(ROOT)
