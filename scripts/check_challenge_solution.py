"""Check that the public Challenge and Solution theorem types are identical."""

from __future__ import annotations

import re
import sys
from pathlib import Path


THEOREM = "PrimeFactorUnimodality.completeClassification"
DECLARATION = re.compile(
    rf"(?ms)^\s*theorem\s+{re.escape(THEOREM)}\s*:\s*(.*?)\s*:=\s*by\b"
)


def theorem_type(path: Path) -> str:
    source = path.read_text(encoding="utf-8")
    match = DECLARATION.search(source)
    if match is None:
        raise ValueError(f"{path.name}: missing theorem {THEOREM}")
    return " ".join(match.group(1).split())


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    challenge = theorem_type(root / "Challenge.lean")
    solution = theorem_type(root / "Solution.lean")
    if challenge != solution:
        print("Challenge/Solution theorem type mismatch:")
        print(f"  Challenge: {challenge}")
        print(f"  Solution:  {solution}")
        return 1
    print(f"Challenge/Solution theorem type: identical ({THEOREM})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
