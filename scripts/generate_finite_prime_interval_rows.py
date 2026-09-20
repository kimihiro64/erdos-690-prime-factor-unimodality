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
ROW_PART_SIZE = 8
# Keep each generated module small enough that its local arithmetic proof does
# not retain the entire lower-prefix row family during elaboration.  The
# module count remains proportional to row chunks, rather than to witnesses.
LOW_MODULE_TARGET_BYTES = 1_000


def factor_nat(n: int) -> list[int]:
    factors: list[int] = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def pocklington_certificate(n: int) -> str:
    """Emit one compact Pocklington proof for a small prime witness.

    The factor-list assembler supplies the divisor reasoning.  The generated
    proof contains only the factorization and modular residues; it does not
    ask Lean to search for primality by reducing the full trial-division
    predicate.
    """
    factors = factor_nat(n - 1)
    base = next(
        a for a in range(2, n)
        if pow(a, n - 1, n) == 1
        and all(pow(a, (n - 1) // q, n) != 1 for q in set(factors))
    )
    inverses = {
        q: pow((pow(base, (n - 1) // q, n) - 1) % n, -1, n)
        for q in set(factors)
    }
    theorem = [
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 20000000 in",
        f"theorem lowPrime_{n} : Nat.Prime {n} := by",
        f"  apply Nat.prime_of_pocklington_factor_of_prime_factors {n} {n - 1} 1 {base} [{', '.join(map(str, factors))}]",
        "  · norm_num",
        "  · norm_num",
        "  · norm_num",
    ]
    theorem.extend(
        [
            "  · intro p hp",
            "    simp at hp",
            "    rcases hp with "
            + " | ".join("rfl" for _ in factors),
        ]
    )
    theorem.extend(["    all_goals decide", "  · norm_num", "  · norm_num"])
    theorem.extend(["  · decide"])
    theorem.extend(["  · intro q hq", "    simp at hq"])
    residue_factors = list(dict.fromkeys(factors))
    theorem.append(
        "    rcases hq with " + " | ".join("rfl" for _ in residue_factors)
    )
    for q in residue_factors:
        theorem.extend(
            [
                f"    · apply IsUnit.of_mul_eq_one ({inverses[q]} : ZMod {n})",
                "      decide",
            ]
        )
    theorem.extend(["  · norm_num", ""])
    return "\n".join(theorem)


def prime_certificates(rows: list[str]) -> str:
    witnesses = sorted({int(q) for row in rows for q in re.findall(r"\(q := (\d+)\)", row)})
    return "\n".join(pocklington_certificate(q) for q in witnesses)


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
        chain_start = left if index == 0 else int(
            re.search(r"\(q := (\d+)\)", part_rows[index - 1]).group(1)
        )
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
            proof.append(indent +
                         f"  norm_num [{constructor.group(0)}, "
                         "dusartPrimeRow_of_explicit_right]")
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
        rows = re.findall(r"^    dusartPrimeRow[^\n]+(?:\n)?", rows_text, re.M)
        if len(rows) <= ROW_PART_SIZE:
            return match.group(0)

        parts = [
            rows[offset : offset + ROW_PART_SIZE]
            for offset in range(0, len(rows), ROW_PART_SIZE)
        ]
        part_names = [f"{name}_part{index:02d}" for index in range(1, len(parts) + 1)]
        output: list[str] = []
        expected_start = int(start)
        for index, (part_name, part_rows) in enumerate(zip(part_names, parts)):
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
                    f"    DusartPrimeRowsChain {first.group(1)} {int(last.group(2)) - 1} {part_name} := by",
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
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds
import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington
import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod

set_option autoImplicit false
set_option maxRecDepth 100000

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


def low_manifest(part_count: int) -> str:
    """Record the generated part sequence for deterministic CI sharding."""
    return f"""/-! Generated lower-prefix module manifest. -/

def finitePrimeIntervalRowsLowPartCount : Nat := {part_count}
"""


def low_modules(body: str) -> dict[str, str]:
    """Split row data into independent chunks and assemble it in the facade.

    The generated row chunks deliberately do not import one another.  A
    sequential import chain makes the last chunk retain every earlier chunk
    during elaboration, defeating the purpose of sharding.  Aggregate list
    definitions and their chain proofs are small and belong in ``Low.lean``,
    after all row chunks have been imported.
    """
    marker = re.compile(
        r"(?m)^set_option maxHeartbeats 20000000 in\ndef dusartPrimeRows_"
    )
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
        "LowBase.lean": (LOW_HEADER + body[:family_starts[0]] + CHAIN_ASSEMBLER).rstrip() + "\n"
    }
    ranges: list[tuple[int, int]] = []
    offset = 0
    while offset < len(part_segments):
        end_family = offset + 1
        while end_family < len(part_segments):
            candidate = "".join(part_segments[offset:end_family + 1])
            if len(candidate) > LOW_MODULE_TARGET_BYTES:
                break
            end_family += 1
        ranges.append((offset, end_family))
        offset = end_family
    for part, (offset, end_family) in enumerate(ranges, 1):
        module = f"LowPart{part:02d}"
        header = f"""import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk {part:02d} -/

namespace PrimeFactorUnimodality

noncomputable section
"""
        part_body = "".join(part_segments[offset:end_family])
        part_rows = re.findall(r"^    dusartPrimeRow[^\n]+(?:\n)?", part_body, re.M)
        certificates = prime_certificates(part_rows)
        part_body = re.sub(
            r"(\(q := (\d+)\)) \(by decide\)",
            lambda match: f"{match.group(1)} (by exact lowPrime_{match.group(2)})",
            part_body,
            count=0,
        )
        result[f"{module}.lean"] = (
            header + certificates + part_body
        ).rstrip() + "\n"
    imports = "\n".join(
        f"import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart{part:02d}"
        for part in range(1, len(ranges) + 1)
    )
    result["Low.lean"] = (
        imports
        + "\n\nset_option autoImplicit false\nset_option maxRecDepth 100000\n\n"
        + "namespace PrimeFactorUnimodality\n\nnoncomputable section\n"
        + "".join(aggregate_segments)
    ).rstrip() + "\n"
    result["LowManifest.lean"] = low_manifest(len(ranges))
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
    generated_names = set(generated_low)
    stale_pattern = re.compile(r"LowPart\d+\.lean")
    for stale in out.glob("LowPart*.lean"):
        if stale_pattern.fullmatch(stale.name) and stale.name not in generated_names:
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
