#!/usr/bin/env python3
# ruff: noqa: RUF001 -- Lean source strings intentionally use blackboard-bold types.
"""Render serially cacheable tail chunks for a record-twin seed."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

import gmpy2  # type: ignore[import-untyped]
from render_record_twin_seed_chunks import quadratic_mul  # type: ignore[import-not-found]
from render_record_twin_seed_lean import (  # type: ignore[import-not-found]
    source_note,
    validate_common,
)


def names(task: str) -> tuple[str, str, str, str]:
    if task == "upper-seed":
        return "Upper", "ZMod recordUpper", "recordUpperWitnessBase", "recordUpper"
    if task == "lower-seed":
        return (
            "Lower",
            "BLSPrimality.X7 recordLower",
            "BLSPrimality.alpha recordLower",
            "recordLower",
        )
    raise ValueError("unsupported seed task")


GROUP_SIZE = 40


def render_prefix_group(
    task: str, checkpoint: int, chunks: list[str], note: str, group: int
) -> str:
    side, _, _, _ = names(task)
    checkpoint_label = f"{checkpoint:03d}"
    first = checkpoint + 1 + (group - 1) * GROUP_SIZE
    last = min(checkpoint + group * GROUP_SIZE, len(chunks))
    imported = (
        "PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure"
        if group == 1 and checkpoint == 0
        else "PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordTwin{side}SeedChunks.Part{checkpoint_label}"
        if group == 1
        else "PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordTwin{side}SeedTail.Prefixes.Part{group - 1:02d}"
    )
    lines = [
        "import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerStep",
        f"import {imported}",
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 1000000",
        "set_option linter.style.longLine false",
        "",
        f"/-! {note} Independent tail exponent prefixes. -/",
        "",
        "namespace PrimeFactorUnimodality",
        "",
    ]
    if group == 1:
        lines.extend(
            [
                f"def record{side}SeedTailPrefix{checkpoint_label} : ℕ :=",
                ("  0" if checkpoint == 0 else f"  record{side}SeedChunk{checkpoint_label}Prefix"),
                "",
            ]
        )
    for index in range(first, last + 1):
        label = f"{index:03d}"
        previous = f"{index - 1:03d}"
        bits = chunks[index - 1]
        lines.extend(
            [
                f"def record{side}SeedTailChunk{label}Width : ℕ := {len(bits)}",
                "",
                f"def record{side}SeedTailChunk{label}Value : ℕ := {int(bits, 2)}",
                "",
                f"def record{side}SeedTailPrefix{label} : ℕ :=",
                f"  record{side}SeedTailPrefix{previous} *",
                f"    2 ^ record{side}SeedTailChunk{label}Width +",
                f"    record{side}SeedTailChunk{label}Value",
                "",
            ]
        )
    lines.extend(["end PrimeFactorUnimodality", ""])
    return "\n".join(lines)


def state_literal(task: str, state: Any) -> str:
    if task == "upper-seed":
        return str(state)
    re, im = state
    return f"⟨{re}, {im}⟩"


def load_existing_states(task: str, directory: Path, count: int) -> list[Any]:
    side, _, _, _ = names(task)
    states: list[Any] = []
    for index in range(1, count + 1):
        source = (directory / f"Part{index:03d}.lean").read_text()
        label = f"record{side}SeedChunk{index:03d}State"
        if task == "upper-seed":
            match = re.search(rf"def {label} : ZMod recordUpper := (\d+)", source)
            if match is None:
                raise ValueError(f"could not parse {label}")
            states.append(gmpy2.mpz(match.group(1)))
        else:
            match = re.search(
                rf"def {label} : BLSPrimality\.X7 recordLower :=\s*⟨(\d+), (\d+)⟩",
                source,
            )
            if match is None:
                raise ValueError(f"could not parse {label}")
            states.append((gmpy2.mpz(match.group(1)), gmpy2.mpz(match.group(2))))
    return states


def render_chunk(
    task: str,
    checkpoint: int,
    index: int,
    before_state: Any,
    after_state: Any,
    bits: str,
    note: str,
) -> str:
    side, state_type, base, _ = names(task)
    label = f"{index:03d}"
    previous = f"{index - 1:03d}"
    prefix_group = (index - checkpoint - 1) // GROUP_SIZE + 1
    prefix_import = (
        "PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordTwin{side}SeedTail.Prefixes.Part{prefix_group:02d}"
    )
    previous_import = (
        ""
        if index == checkpoint + 1
        else "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordTwin{side}SeedTail.Part{previous}\n"
    )
    return f"""import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerStep
{previous_import}import {prefix_import}

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false
set_option linter.defProp false

/-! {note} Independently checked tail chunk {index}. -/

namespace PrimeFactorUnimodality

def record{side}SeedTailChunk{label}Before : {state_type} :=
  {state_literal(task, before_state)}

def record{side}SeedTailChunk{label}State : {state_type} :=
  {state_literal(task, after_state)}

set_option maxHeartbeats 0 in
-- The closed modular replay intentionally has no heuristic heartbeat budget.
def record{side}SeedTailChunk{label}_kernel :
    powChunkMSB record{side}SeedTailChunk{label}Width
      record{side}SeedTailChunk{label}Value
      record{side}SeedTailChunk{label}Before ({base}) =
        record{side}SeedTailChunk{label}State := by
  rfl

def record{side}SeedTailChunk{label}Step : PowerStep ({base} : {state_type})
    record{side}SeedTailChunk{label}Before
    record{side}SeedTailChunk{label}State
    record{side}SeedTailPrefix{previous}
    record{side}SeedTailChunk{label}Width
    record{side}SeedTailChunk{label}Value where
  bits_lt := by
    set_option exponentiation.threshold 10000 in
      norm_num [record{side}SeedTailChunk{label}Width,
        record{side}SeedTailChunk{label}Value]
  checked := record{side}SeedTailChunk{label}_kernel

end PrimeFactorUnimodality
"""


def render_assembly_group(task: str, checkpoint: int, count: int, note: str, group: int) -> str:
    side, _state_type, base, _ = names(task)
    checkpoint_label = f"{checkpoint:03d}"
    first = checkpoint + 1 + (group - 1) * GROUP_SIZE
    last = min(checkpoint + group * GROUP_SIZE, count)
    imports = []
    if group > 1:
        imports.append(
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
            f"RecordTwin{side}SeedTail.Assembly.Part{group - 1:02d}"
        )
    imports.append(
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordTwin{side}SeedTail.Part{last:03d}"
    )
    lines = [
        *imports,
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 1000000",
        "",
        f"/-! {note} Semantic tail assembly group {group}. -/",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        f"theorem record{side}SeedTailGroup{group:02d}_semantic :",
        f"    record{side}SeedTailChunk{last:03d}State =",
        f"      ({base}) ^ record{side}SeedTailPrefix{last:03d} := by",
    ]
    if group == 1:
        if checkpoint == 0:
            lines.extend(
                [
                    f"  have h{checkpoint_label} : (1 : _) =",
                    f"      ({base}) ^ record{side}SeedTailPrefix{checkpoint_label} := by",
                    f"    simp only [record{side}SeedTailPrefix{checkpoint_label}, pow_zero]",
                ]
            )
        else:
            lines.extend(
                [
                    f"  have h{checkpoint_label} : record{side}SeedChunk{checkpoint_label}State =",
                    f"      ({base}) ^ record{side}SeedTailPrefix{checkpoint_label} := by",
                    f"    simpa only [record{side}SeedTailPrefix{checkpoint_label}] using",
                    f"      PowerTrace.certifies record{side}SeedChunk{checkpoint_label}Trace",
                ]
            )
        previous_h = f"h{checkpoint_label}"
    else:
        previous_h = f"record{side}SeedTailGroup{group - 1:02d}_semantic"
    for index in range(first, last + 1):
        label = f"{index:03d}"
        previous = f"{index - 1:03d}"
        lines.extend(
            [
                f"  have h{label} : record{side}SeedTailChunk{label}State =",
                f"      ({base}) ^ record{side}SeedTailPrefix{label} := by",
                f"    have prior : record{side}SeedTailChunk{label}Before =",
                f"        ({base}) ^ record{side}SeedTailPrefix{previous} := by",
                "      simpa only [",
                f"        record{side}SeedTailChunk{label}Before,",
                (
                    f"        ] using {previous_h}"
                    if index == 1 and checkpoint == 0
                    else f"        record{side}SeedChunk{checkpoint_label}State] using {previous_h}"
                    if index == checkpoint + 1
                    else f"        record{side}SeedTailChunk{previous}State] using {previous_h}"
                ),
                f"    simpa only [record{side}SeedTailPrefix{label}] using",
                f"      record{side}SeedTailChunk{label}Step.certifies prior",
            ]
        )
        previous_h = f"h{label}"
    lines.extend([f"  exact h{last:03d}", "", "end PrimeFactorUnimodality", ""])
    return "\n".join(lines)


def render_facade(task: str, count: int, note: str, groups: int) -> str:
    side, state_type, base, _ = names(task)
    final = f"{count:03d}"
    assembly_import = (
        "PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordTwin{side}SeedTail.Assembly.Part{groups:02d}"
    )
    return f"""import {assembly_import}

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! {note} Parallel tail-chain facade. -/

namespace PrimeFactorUnimodality

def record{side}Seed : {state_type} := record{side}SeedTailChunk{final}State

set_option maxHeartbeats 0 in
-- Normalization checks that the complete chunk prefix is the shared exponent.
theorem record{side}_seedExponent_eq_prefix :
    recordSeedExponent = record{side}SeedTailPrefix{final} := by
  set_option exponentiation.threshold 5000 in
    norm_num [recordSeedExponent, recordFactor, recordBase,
      record{side}SeedTailPrefix{final}]

theorem record{side}_seed_pow :
    ({base}) ^ recordSeedExponent = record{side}Seed := by
  rw [record{side}_seedExponent_eq_prefix, record{side}Seed]
  exact record{side}SeedTailGroup{groups:02d}_semantic.symm

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output_directory", type=Path)
    parser.add_argument("--checkpoint", type=int, required=True)
    parser.add_argument("--chunk-bits", type=int, default=512)
    parser.add_argument("--reuse-state-directory", type=Path)
    args = parser.parse_args()
    data: dict[str, Any] = json.loads(args.input.read_text())
    modulus_int, _, _ = validate_common(data)
    modulus = gmpy2.mpz(modulus_int)
    factor = gmpy2.mpz(data["base"]) ** int(data["factor_exponent"])
    exponent = gmpy2.mpz(data["base"]) ** (int(data["factor_exponent"]) - 1) * (factor - 1)
    exponent_bits = exponent.digits(2)
    chunks = [
        exponent_bits[start : start + args.chunk_bits]
        for start in range(0, len(exponent_bits), args.chunk_bits)
    ]
    if not 0 <= args.checkpoint < len(chunks):
        parser.error("checkpoint must lie inside the chunk range")
    note = source_note(data, args.input)
    task = str(data["task"])
    side, _, _, _ = names(task)
    prefix = 0
    state: Any = gmpy2.mpz(1) if task == "upper-seed" else (gmpy2.mpz(1), gmpy2.mpz(0))
    base: Any = (
        gmpy2.mpz(data["witness_base"]) if task == "upper-seed" else (gmpy2.mpz(1), gmpy2.mpz(1))
    )
    args.output_directory.mkdir(parents=True, exist_ok=True)
    groups = (len(chunks) - args.checkpoint + GROUP_SIZE - 1) // GROUP_SIZE
    prefix_directory = args.output_directory / "Prefixes"
    assembly_directory = args.output_directory / "Assembly"
    prefix_directory.mkdir(parents=True, exist_ok=True)
    assembly_directory.mkdir(parents=True, exist_ok=True)
    for group in range(1, groups + 1):
        (prefix_directory / f"Part{group:02d}.lean").write_text(
            render_prefix_group(task, args.checkpoint, chunks, note, group)
        )
    existing_states = (
        load_existing_states(task, args.reuse_state_directory, len(chunks))
        if args.reuse_state_directory is not None
        else None
    )
    for index, bits in enumerate(chunks, start=1):
        before_state = state
        if existing_states is not None:
            state = existing_states[index - 1]
        elif task == "upper-seed":
            state = gmpy2.powmod(state, 2 ** len(bits), modulus)
            state = state * gmpy2.powmod(base, int(bits, 2), modulus) % modulus
        else:
            for bit in bits:
                state = quadratic_mul(state, state, modulus)
                if bit == "1":
                    state = quadratic_mul(state, base, modulus)
        prefix = prefix * 2 ** len(bits) + int(bits, 2)
        if index > args.checkpoint:
            (args.output_directory / f"Part{index:03d}.lean").write_text(
                render_chunk(task, args.checkpoint, index, before_state, state, bits, note)
            )
    if prefix != exponent:
        raise ValueError("tail prefixes do not reconstruct the seed exponent")
    expected = data["derived"]
    if task == "upper-seed" and state != gmpy2.mpz(expected["seed"]):
        raise ValueError("upper tail does not reach the recorded seed")
    if task == "lower-seed" and state != (
        gmpy2.mpz(expected["seed_re"]),
        gmpy2.mpz(expected["seed_im"]),
    ):
        raise ValueError("lower tail does not reach the recorded seed")
    for group in range(1, groups + 1):
        (assembly_directory / f"Part{group:02d}.lean").write_text(
            render_assembly_group(task, args.checkpoint, len(chunks), note, group)
        )
    facade = render_facade(task, len(chunks), note, groups)
    (args.output_directory.parent / f"RecordTwin{side}Seed.lean").write_text(facade)
    print(f"wrote {len(chunks) - args.checkpoint} serial {side.lower()} chunks")


if __name__ == "__main__":
    sys.set_int_max_str_digits(1_000_000)
    main()
