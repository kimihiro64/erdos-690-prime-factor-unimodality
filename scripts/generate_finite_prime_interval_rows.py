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
from pathlib import Path

try:
    from scripts.finite_prime_interval_generator import (
        extract,
        normalize,
        prime_certificates,
        source_text,
    )
except ModuleNotFoundError:
    from finite_prime_interval_generator import (  # type: ignore[import-not-found, no-redef]
        extract,
        normalize,
        prime_certificates,
        source_text,
    )

SOURCE_REVISION = "c6200344736f94e6cacc924d1aa3a6cd9531f2d5"
SOURCE_PATH = "PrimeFactorUnimodality/Helpers/Analytic/FinitePrimeIntervalRows.lean"
LOW_START = "def dusartUpper"
LOW_END = "theorem dusartPrimeRows_3275_23158_chain"
HIGH_START = "def dusartPrimeRows_23159_89693"
HIGH_END = "structure LogCubedPrimeRow"
ROW_PART_SIZE = 8
# Keep each generated module small enough that its local arithmetic proof does
# not retain the entire lower-prefix row family during elaboration.  The
# module count remains proportional to row chunks, rather than to witnesses.
# Keep the row family in a small number of independently cacheable modules.
# The old 1 KiB threshold produced hundreds of nearly empty modules because
# each module repeated the local Pocklington support.  A bounded data shard is
# still preferable to one monolithic file, but the shard should amortize that
# shared support and leave the reusable row assembler—not the filesystem—as
# the unit of composition.
LOW_MODULE_TARGET_BYTES = 32_000
EXPECTED_LOW_ROW_COUNT = 2_122


def _append_chain_terms(names: list[str]) -> str:
    """Build a right-associated expression using the generic append lemma."""
    if len(names) == 1:
        return f"{names[0]}_chain"
    return f"dusartPrimeRowsChain_append {names[0]}_chain ({_append_chain_terms(names[1:])})"


def _local_chain_proof(part_rows: list[str]) -> str:
    """Generate a constructor proof for one small row chunk.

    A single ``decide +kernel`` over the whole chunk forces Lean to unfold
    every row constructor while reducing the recursive data predicate.  The
    constructor proof keeps each arithmetic obligation local, so the shard
    remains cheap to elaborate and does not depend on reduction of the entire
    generated list at once.
    """
    proof: list[str] = ["  apply DusartPrimeRowsChain.cons"]
    for index, row in enumerate(part_rows):
        constructor = re.search(r"dusartPrimeRow_of_explicit_[A-Za-z0-9_]+", row)
        assert constructor, row
        bounds = re.search(r"\(p := (\d+)\) \(q := (\d+)\)", row)
        assert bounds, row
        left, right_prime = map(int, bounds.groups())
        indent = "  " * (index + 1)
        proof.extend(
            [
                indent + f"· norm_num [{constructor.group(0)}]",
                indent + f"· norm_num [{constructor.group(0)}]",
            ]
        )
        if index + 1 < len(part_rows):
            proof.append(indent + "· apply DusartPrimeRowsChain.cons")
        else:
            proof.append(indent + "· apply DusartPrimeRowsChain.empty")
            proof.append(
                indent + f"  norm_num [{constructor.group(0)}, dusartPrimeRow_of_explicit_right]"
            )
    return "\n".join(proof)


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
        r"\s*\[(.*?)\]\n\n"
        r"set_option maxHeartbeats 20000000 in\n"
        r"theorem \1_chain :\n"
        r"    DusartPrimeRowsChain (\d+) (\d+) \1 := by\n"
        r"(.*?)(?=^set_option maxHeartbeats 20000000 in\n|\Z)",
    )

    def replace(match: re.Match[str]) -> str:
        name, rows_text, start, finish, proof = match.groups()
        rows = re.findall(r"^    dusartPrimeRow_of_explicit[^\n]+(?:\n)?", rows_text, re.M)
        if len(rows) <= ROW_PART_SIZE:
            return match.group(0)

        parts = [
            rows[offset : offset + ROW_PART_SIZE] for offset in range(0, len(rows), ROW_PART_SIZE)
        ]
        part_names = [f"{name}_part{index:02d}" for index in range(1, len(parts) + 1)]
        output: list[str] = []
        expected_start = int(start)
        for _index, (part_name, part_rows) in enumerate(zip(part_names, parts, strict=False)):
            first = re.search(r"\(p := (\d+)\).*\(q := (\d+)\)", part_rows[0])
            last = re.search(r"\(p := (\d+)\).*\(q := (\d+)\)", part_rows[-1])
            assert first and last
            assert int(first.group(1)) == expected_start
            expected_start = int(last.group(2))
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
                    "    DusartPrimeRowsChain "
                    f"{first.group(1)} {int(last.group(2)) - 1} {part_name} := by",
                    _local_chain_proof(part_rows),
                    "",
                ]
            )
        assert expected_start - 1 == int(finish), (name, expected_start, finish)
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
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBoundsPart02
import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Helpers.FiniteCertificates.PocklingtonRows
import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prime-row prefix -/

namespace PrimeFactorUnimodality

noncomputable section
"""

CHAIN_ASSEMBLER = """
/-! Reusable assembler for generated row parts. -/
def DusartPrimeRowsChainData (a b : Nat) : List DusartPrimeRow → Prop
  | [] => b < a
  | row :: tail =>
      row.left ≤ a ∧ row.left ≤ row.right ∧
        DusartPrimeRowsChainData (row.right + 1) b tail

theorem dusartPrimeRowsChain_of_data
    {a b : Nat} {rows : List DusartPrimeRow}
    (h : DusartPrimeRowsChainData a b rows) :
    DusartPrimeRowsChain a b rows := by
  induction rows generalizing a b with
  | nil => exact DusartPrimeRowsChain.empty h
  | cons row tail ih =>
      exact DusartPrimeRowsChain.cons row h.1 h.2.1 (ih h.2.2)
"""

ROW_PROJECTIONS = """
@[simp] theorem dusartPrimeRow_of_explicit_left
    {p q : Nat} {L : Real} (hq : q.Prime) (hpq : p < q)
    (hleft_large : 3275 ≤ p) (hlog : Real.log p ≤ L)
    (hL : 0 < L) (hproduct : (q - p : Real) * (2 * L ^ 2) ≤ p) :
    (dusartPrimeRow_of_explicit hq hpq hleft_large hlog hL hproduct).left = p := by
  rfl

@[simp] theorem dusartPrimeRow_of_explicit_right
    {p q : Nat} {L : Real} (hq : q.Prime) (hpq : p < q)
    (hleft_large : 3275 ≤ p) (hlog : Real.log p ≤ L)
    (hL : 0 < L) (hproduct : (q - p : Real) * (2 * L ^ 2) ≤ p) :
    (dusartPrimeRow_of_explicit hq hpq hleft_large hlog hL hproduct).right = q - 1 := by
  rfl
"""

HIGH_HEADER = """import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Low

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Upper finite Dusart prime-row prefix -/

namespace PrimeFactorUnimodality

noncomputable section
"""


def low_facade(last_part: int) -> str:
    return f"""import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart{
        last_part:02d
    }

/-! # Lower finite Dusart prefix facade

The implementation is chained through cacheable generated row modules.
-/
"""


def low_manifest(part_count: int, row_count: int) -> str:
    """Record the generated part sequence for deterministic CI sharding."""
    return f'''/-! Generated lower-prefix module manifest. -/

def finitePrimeIntervalRowsLowPartCount : Nat := {part_count}
def finitePrimeIntervalRowsLowRowCount : Nat := {row_count}
def finitePrimeIntervalRowsLowSourceRevision : String := "{SOURCE_REVISION}"
'''


def low_modules(body: str) -> dict[str, str]:
    """Split row data into chunks and assemble it through a serial import chain."""
    marker = re.compile(r"(?m)^set_option maxHeartbeats 20000000 in\ndef dusartPrimeRows_")
    starts = [match.start() for match in marker.finditer(body)]
    assert starts
    family_starts = starts
    family_count = len(family_starts)
    segments = [
        body[start : family_starts[index + 1] if index + 1 < family_count else len(body)]
        for index, start in enumerate(family_starts)
    ]
    part_segments: list[str] = []
    aggregate_segments: list[str] = []
    for segment in segments:
        match = re.search(r"\ndef (dusartPrimeRows_[A-Za-z0-9_]+)", segment)
        assert match, segment[:200]
        if "_part" in match.group(1):
            part_segments.append(segment)
        else:
            aggregate_segments.append(segment)

    result = {
        "LowBase.lean": (
            LOW_HEADER + body[: family_starts[0]] + ROW_PROJECTIONS + CHAIN_ASSEMBLER
        ).rstrip()
        + "\n"
    }
    ranges: list[tuple[int, int]] = []
    offset = 0
    while offset < len(part_segments):
        end_family = offset + 1
        while end_family < len(part_segments):
            candidate = "".join(part_segments[offset : end_family + 1])
            if len(candidate) > LOW_MODULE_TARGET_BYTES:
                break
            end_family += 1
        ranges.append((offset, end_family))
        offset = end_family
    for part, (offset, end_family) in enumerate(ranges, 1):
        module = f"LowPart{part:02d}"
        previous_import = (
            ""
            if part == 1
            else "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart"
            f"{part - 1:02d}\n"
        )
        header = f"""import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
{previous_import}

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk {part:02d} -/

namespace PrimeFactorUnimodality

noncomputable section
"""
        part_body = "".join(part_segments[offset:end_family])
        part_rows = re.findall(r"^    dusartPrimeRow_of_explicit[^\n]+(?:\n)?", part_body, re.M)
        data_name = f"lowPocklingtonData{part:02d}"
        accessor_name = f"lowPocklingtonPrime{part:02d}"
        certificates = prime_certificates(part_rows, data_name, accessor_name)
        witness_indices = {
            n: index
            for index, n in enumerate(
                sorted({int(q) for row in part_rows for q in re.findall(r"\(q := (\d+)\)", row)})
            )
        }

        def replace_witness(
            match: re.Match[str],
            accessor_name: str = accessor_name,
            witness_indices: dict[int, int] = witness_indices,
            data_name: str = data_name,
        ) -> str:
            return (
                f"{match.group(1)} (by\n"
                f"      have hp := {accessor_name} ⟨{witness_indices[int(match.group(2))]}, "
                f"by simp [{data_name}]⟩\n"
                f"      simpa [{data_name}] using hp)"
            )

        part_body = re.sub(
            r"(\(q := (\d+)\)) \(by decide\)",
            replace_witness,
            part_body,
            count=0,
        )
        result[f"{module}.lean"] = (header + certificates + part_body).rstrip() + "\n"
    group_size = 12
    group_count = (len(ranges) + group_size - 1) // group_size
    for group in range(group_count):
        last = min((group + 1) * group_size, len(ranges))
        previous_group = (
            ""
            if group == 0
            else "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows."
            f"LowGroup{group:02d}\n"
        )
        group_imports = (
            previous_group
            + "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows."
            f"LowPart{last:02d}"
        )
        result[f"LowGroup{group + 1:02d}.lean"] = (
            group_imports
            + "\n\n/-! Generated import group for lower finite Dusart row chunks. -/\n"
        )
    imports = (
        "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows."
        f"LowGroup{group_count:02d}"
    )
    result["Low.lean"] = (
        imports
        + "\n\nset_option autoImplicit false\nset_option maxRecDepth 1000000\n\n"
        + "/-! # Generated low finite prime interval rows\n\n"
        + "This facade imports the independent low-range row chunks and assembles "
        + "their shared coverage data. -/\n\n"
        + "namespace PrimeFactorUnimodality\n\nnoncomputable section\n"
        + "".join(aggregate_segments)
    ).rstrip() + "\n"
    row_count = sum(
        len(re.findall(r"^    dusartPrimeRow_of_explicit[^\\n]+(?:\\n)?", segment, re.M))
        for segment in part_segments
    )
    result["LowManifest.lean"] = low_manifest(len(ranges), row_count)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    out = (
        args.output_dir or repo / "PrimeFactorUnimodality/Helpers/Analytic/FinitePrimeIntervalRows"
    ).resolve()
    out.mkdir(parents=True, exist_ok=True)
    text = source_text(repo, SOURCE_REVISION, SOURCE_PATH)
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
    assert len([name for name in generated_low if name.startswith("LowPart")]) <= 32
    row_count = sum(
        len(re.findall(r"^    dusartPrimeRow_of_explicit[^\n]+(?:\n)?", segment, re.M))
        for segment in re.findall(
            r"(?ms)^set_option maxHeartbeats 20000000 in\ndef dusartPrimeRows_.*?"
            r"(?=^set_option maxHeartbeats 20000000 in\ndef dusartPrimeRows_|\Z)",
            low,
        )
    )
    assert row_count == EXPECTED_LOW_ROW_COUNT, row_count
    generated_names = set(generated_low)
    stale_patterns = (re.compile(r"LowPart\d+\.lean"), re.compile(r"LowGroup\d+\.lean"))
    stale_paths = list(out.glob("LowPart*.lean")) + list(out.glob("LowGroup*.lean"))
    for stale in stale_paths:
        if (
            any(pattern.fullmatch(stale.name) for pattern in stale_patterns)
            and stale.name not in generated_names
        ):
            stale.unlink()
    for name, generated in generated_low.items():
        (out / name).write_text(generated)
    (out / "High.lean").write_text((HIGH_HEADER + high).rstrip() + "\n")
    for name in generated_low:
        generated = (out / name).read_text()
        print(f"generated {name}: {len(generated.splitlines())} lines, {len(generated)} bytes")
    print(f"generated High.lean: {len(high.splitlines())} lines, {len(high)} bytes")


if __name__ == "__main__":
    main()
