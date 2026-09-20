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
ROW_PART_SIZE = 24
LOW_MODULE_TARGET_BYTES = 120_000


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


def _append_chain_terms(names: list[str]) -> str:
    """Build a right-associated expression using the generic append lemma."""
    if len(names) == 1:
        return f"{names[0]}_chain"
    return f"dusartPrimeRowsChain_append {names[0]}_chain ({_append_chain_terms(names[1:])})"


def split_large_row_families(body: str) -> str:
    """Split literal row families before module sharding.

    A literal family carries both its row data and a chain proof that repeats
    the rows.  Keeping those two large terms together makes elaboration peak
    memory grow needlessly.  Each generated part has its own bounded list and
    chain proof; the original family name remains the append of those parts.
    """
    family = re.compile(
        r"(?ms)^set_option maxHeartbeats 20000000 in\n"
        r"def (dusartPrimeRows_\d+_\d+) : List DusartPrimeRow :=\n"
        r"  \[(.*?)\]\n\n"
        r"set_option maxHeartbeats 20000000 in\n"
        r"theorem \1_chain :\n"
        r"    DusartPrimeRowsChain (\d+) (\d+) \1 := by\n"
        r"(.*?)(?=^set_option maxHeartbeats 20000000 in\n|\Z)",
    )

    def replace(match: re.Match[str]) -> str:
        name, rows_text, start, finish, proof = match.groups()
        rows = re.findall(r"^    dusartPrimeRow[^\n]+(?:\n)?", rows_text, re.M)
        blocks = re.findall(
            r"(?ms)^  apply DusartPrimeRowsChain\.cons\n"
            r"    \(dusartPrimeRow[^\n]+\)\n"
            r"  · norm_num\n"
            r"  · norm_num\n",
            proof,
        )
        if len(rows) != len(blocks) or len(rows) <= ROW_PART_SIZE:
            return match.group(0)

        parts = [
            rows[offset : offset + ROW_PART_SIZE]
            for offset in range(0, len(rows), ROW_PART_SIZE)
        ]
        part_names = [f"{name}_part{index:02d}" for index in range(1, len(parts) + 1)]
        output: list[str] = []
        for index, (part_name, part_rows) in enumerate(zip(part_names, parts)):
            first = re.search(r"\(p := (\d+)\).*\(q := (\d+)\)", part_rows[0])
            last = re.search(r"\(p := (\d+)\).*\(q := (\d+)\)", part_rows[-1])
            assert first and last
            part_blocks = blocks[index * ROW_PART_SIZE : (index + 1) * ROW_PART_SIZE]
            output.extend(
                [
                    "set_option maxHeartbeats 20000000 in",
                    f"def {part_name} : List DusartPrimeRow :=",
                    "  [",
                    "\n".join(row.rstrip(",\n") + "," for row in part_rows),
                    "  ]",
                    "",
                    "set_option maxHeartbeats 20000000 in",
                    f"theorem {part_name}_chain :",
                    f"    DusartPrimeRowsChain {first.group(1)} {last.group(2)} {part_name} := by",
                    "".join(part_blocks),
                    "  exact DusartPrimeRowsChain.empty (by norm_num)",
                    "",
                ]
            )
        output.extend(
            [
                "set_option maxHeartbeats 20000000 in",
                f"def {name} : List DusartPrimeRow :=",
                "  " + " ++ ".join(part_names),
                "",
                "set_option maxHeartbeats 20000000 in",
                f"theorem {name}_chain :",
                f"    DusartPrimeRowsChain {start} {finish} {name} := by",
                f"  exact {_append_chain_terms(part_names)}",
                "",
            ]
        )
        return "\n".join(output)

    return family.sub(replace, body)


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

def low_facade(last_part: int) -> str:
    return f"""import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart{last_part:02d}

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
    result = {
        "LowBase.lean": (LOW_HEADER + body[:family_starts[0]]).rstrip() + "\n"
    }
    previous = "LowBase"
    ranges: list[tuple[int, int]] = []
    offset = 0
    while offset < family_count:
        end_family = offset + 1
        while end_family < family_count:
            start = family_starts[offset]
            candidate_end = (
                family_starts[end_family + 1]
                if end_family + 1 < family_count
                else len(body)
            )
            if candidate_end - start > LOW_MODULE_TARGET_BYTES:
                break
            end_family += 1
        ranges.append((offset, end_family))
        offset = end_family
    for part, (offset, end_family) in enumerate(ranges, 1):
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
    assert previous == f"LowPart{len(ranges):02d}"
    result["Low.lean"] = low_facade(len(ranges))
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
    low = split_large_row_families(normalize(extract(text, LOW_START, HIGH_START)))
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
    generated_low = low_modules(low)
    for name, generated in generated_low.items():
        (out / name).write_text(generated)
    (out / "High.lean").write_text((HIGH_HEADER + high).rstrip() + "\n")
    for name in generated_low:
        generated = (out / name).read_text()
        print(f"generated {name}: {len(generated.splitlines())} lines, {len(generated)} bytes")
    print(f"generated High.lean: {len(high.splitlines())} lines, {len(high)} bytes")


if __name__ == "__main__":
    main()
