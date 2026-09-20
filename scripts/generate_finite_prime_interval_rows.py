#!/usr/bin/env python3
"""Reproducibly split the finite Dusart row family into Lean modules.

The row data is kept in the pre-split source revision so this generator does
not depend on terminal output, shell quoting, or hand-edited multi-thousand
line patches.  The generated modules contain only the requested contiguous
families; shared definitions and assemblers live in Core.lean.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path


SOURCE_REVISION = "c6200344"
SOURCE_PATH = "PrimeFactorUnimodality/Helpers/Analytic/FinitePrimeIntervalRows.lean"
LOW_START = "def dusartUpper"
LOW_END = "theorem dusartPrimeRows_3275_23158_chain"
HIGH_START = "def dusartPrimeRows_23159_89693"
HIGH_END = "structure LogCubedPrimeRow"


def source_text(repo: Path) -> str:
    return subprocess.check_output(
        ["git", "show", f"{SOURCE_REVISION}:{SOURCE_PATH}"],
        cwd=repo,
        text=True,
    )


def extract(text: str, start: str, end: str) -> str:
    start_at = text.index(start)
    end_at = text.index(end, start_at)
    return text[start_at:end_at]


def normalize(body: str) -> str:
    """Apply the small source repairs required by the split module API."""
    lines = []
    for line in body.splitlines(keepends=True):
        if "dusartPrimeRow_of_explicit_" in line and "(q := " in line:
            count = len(re.findall(r"\(by (?:norm_num|decide|omega)\)", line))
            if count == 4:
                stripped = line.rstrip()
                if stripped.endswith(","):
                    close = line.rfind(",")
                elif stripped.endswith(")]"):
                    close = line.rfind("]")
                elif stripped.endswith("))"):
                    close = line.rfind(")")
                else:
                    close = len(line.rstrip("\n"))
                line = line[:close] + " (by norm_num)" + line[close:]
            line = re.sub(
                r"(\(q := \d+\)) \(by norm_num\)",
                r"\1 (by decide)",
                line,
                count=1,
            )
        lines.append(line)
    body = "".join(lines)
    body = body.replace(
        """  | empty h =>
      intro x hleft hright
      exfalso
      norm_num at h
      linarith""",
        """  | @empty a b h =>
      intro x hleft hright
      exfalso
      have hab : (b : Real) + 1 ≤ a := by
        exact_mod_cast Nat.succ_le_of_lt h
      linarith""",
    )
    body = body.replace(
        "exact DusartPrimeRowsChain.cons row (by omega) hordered ih",
        "exact DusartPrimeRowsChain.cons row (by omega) hordered htail",
    )
    body = re.sub(
        r"(?m)^(def dusartPrimeRows_|theorem dusartPrimeRows_)",
        "set_option maxHeartbeats 20000000 in\\n\\1",
        body,
    )
    return body


LOW_HEADER = """import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Core
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prime-row prefix -/

namespace PrimeFactorUnimodality

noncomputable section
"""

HIGH_HEADER = """import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Low

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Upper finite Dusart prime-row prefix -/

namespace PrimeFactorUnimodality

noncomputable section
"""

LOW_FACADE = """import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart04

/-! # Lower finite Dusart prefix facade

The implementation is chained through cacheable generated row modules.
-/
"""


def low_modules(body: str) -> dict[str, str]:
    """Split the lower prefix at complete row-list/chain family boundaries."""
    marker = re.compile(
        r"(?m)^set_option maxHeartbeats 20000000 in\ndef dusartPrimeRows_"
    )
    starts = [match.start() for match in marker.finditer(body)]
    assert starts
    family_starts = starts[::2]
    family_count = len(family_starts)
    chunk_size = (family_count + 3) // 4
    result = {
        "LowBase.lean": (LOW_HEADER + body[:family_starts[0]]).rstrip() + "\n"
    }
    previous = "LowBase"
    for part, offset in enumerate(range(0, family_count, chunk_size), 1):
        end_family = min(offset + chunk_size, family_count)
        start = family_starts[offset]
        end = family_starts[end_family] if end_family < family_count else len(body)
        module = f"LowPart{part:02d}"
        header = f"""import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.{previous}

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk {part:02d} -/

namespace PrimeFactorUnimodality

noncomputable section
"""
        result[f"{module}.lean"] = (header + body[start:end]).rstrip() + "\n"
        previous = module
    assert previous == "LowPart04"
    result["Low.lean"] = LOW_FACADE
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    out = (args.output_dir or repo / "PrimeFactorUnimodality/Helpers/Analytic/FinitePrimeIntervalRows").resolve()
    out.mkdir(parents=True, exist_ok=True)
    text = source_text(repo)
    low = normalize(extract(text, LOW_START, HIGH_START))
    high = normalize(extract(text, HIGH_START, HIGH_END))
    assert low.count("def dusartUpper") == 1
    assert low.count(LOW_END) == 1
    assert high.count(HIGH_START) == 1
    assert high.count("theorem hasDusartShortIntervalPrimeBelow_3275_23158") == 1
    assert "sorry" not in low and "sorry" not in high
    for module in (low, high):
        for line in module.splitlines():
            if "dusartPrimeRow_of_explicit_" in line and "(q := " in line:
                proofs = len(re.findall(r"\(by (?:norm_num|decide|omega)\)", line))
                assert proofs == 5, (proofs, line)
    for name, generated in low_modules(low).items():
        (out / name).write_text(generated)
    (out / "High.lean").write_text((HIGH_HEADER + high).rstrip() + "\n")
    for name in ("LowBase.lean", "LowPart01.lean", "LowPart02.lean", "LowPart03.lean", "LowPart04.lean", "Low.lean"):
        generated = (out / name).read_text()
        print(f"generated {name}: {len(generated.splitlines())} lines, {len(generated)} bytes")
    print(f"generated High.lean: {len(high.splitlines())} lines, {len(high)} bytes")


if __name__ == "__main__":
    main()
