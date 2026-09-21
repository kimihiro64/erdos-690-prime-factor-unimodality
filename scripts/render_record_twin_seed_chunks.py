#!/usr/bin/env python3
# ruff: noqa: RUF001 -- Lean source strings intentionally use blackboard-bold types.
"""Render bounded kernel-replay chunks for a record-twin shared seed."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import gmpy2  # type: ignore[import-not-found]
from render_record_twin_seed_lean import (  # type: ignore[import-not-found]
    source_note,
    validate_common,
)


def quadratic_mul(
    left: tuple[gmpy2.mpz, gmpy2.mpz],
    right: tuple[gmpy2.mpz, gmpy2.mpz],
    modulus: gmpy2.mpz,
) -> tuple[gmpy2.mpz, gmpy2.mpz]:
    a, b = left
    c, d = right
    return ((a * c + 7 * b * d) % modulus, (a * d + b * c) % modulus)


def render_upper_chunk(
    index: int,
    bits: str,
    state: gmpy2.mpz,
    previous_prefix: int,
    prefix: int,
    witness_base: int,
    note: str,
    engine: str,
    kernel_only: bool,
) -> str:
    del previous_prefix, prefix
    label = f"{index:03d}"
    previous_label = f"{index - 1:03d}"
    evaluator = "powChunkMSB" if engine == "direct" else "powChunkHorner"
    if index == 1:
        imports = (
            "import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerChunk\n"
            "import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure"
        )
        previous_state = "(1 : ZMod recordUpper)"
        previous_trace = ".nil"
        witness_definition = f"def recordUpperWitnessBase : ℕ := {witness_base}\n\n"
    else:
        imports = (
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
            f"RecordTwinUpperSeedChunks.Part{previous_label}"
        )
        previous_state = f"recordUpperSeedChunk{previous_label}State"
        previous_trace = f"recordUpperSeedChunk{previous_label}Trace"
        witness_definition = ""
    prefix_definition = (
        f"recordUpperSeedChunk{label}Value"
        if index == 1
        else (
            f"recordUpperSeedChunk{previous_label}Prefix * "
            f"2 ^ recordUpperSeedChunk{label}Width + "
            f"recordUpperSeedChunk{label}Value"
        )
    )
    trace_type = "PowerTrace" if engine == "direct" else "PowerHornerTrace"
    trace_bits_proof = (
        ""
        if engine == "horner"
        else f"""
    (by
      set_option exponentiation.threshold 10000 in
        norm_num [recordUpperSeedChunk{label}Width, recordUpperSeedChunk{label}Value])"""
    )
    trace = (
        ""
        if kernel_only
        else f"""
def recordUpperSeedChunk{label}Trace : {trace_type}
    (recordUpperWitnessBase : ZMod recordUpper)
    recordUpperSeedChunk{label}State recordUpperSeedChunk{label}Prefix :=
  .step {previous_trace} recordUpperSeedChunk{label}Width
    recordUpperSeedChunk{label}Value recordUpperSeedChunk{label}State{trace_bits_proof}
    recordUpperSeedChunk{label}_kernel
"""
    )
    return f"""{imports}

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false
set_option linter.defProp false

/-! {note} Chunk {index}. -/

namespace PrimeFactorUnimodality

{witness_definition}\
def recordUpperSeedChunk{label}Width : ℕ := {len(bits)}

def recordUpperSeedChunk{label}Value : ℕ := {int(bits, 2)}

def recordUpperSeedChunk{label}Prefix : ℕ :=
  {prefix_definition}

def recordUpperSeedChunk{label}State : ZMod recordUpper := {state}

set_option maxHeartbeats 0 in
-- The closed modular replay intentionally has no heuristic heartbeat budget.
def recordUpperSeedChunk{label}_kernel :
    {evaluator} recordUpperSeedChunk{label}Width recordUpperSeedChunk{label}Value
      {previous_state}
      (recordUpperWitnessBase : ZMod recordUpper) =
        recordUpperSeedChunk{label}State := by
  rfl

{trace}

end PrimeFactorUnimodality
"""


def render_lower_chunk(
    index: int,
    bits: str,
    state: tuple[gmpy2.mpz, gmpy2.mpz],
    previous_prefix: int,
    prefix: int,
    note: str,
    engine: str,
    kernel_only: bool,
) -> str:
    del previous_prefix, prefix
    label = f"{index:03d}"
    previous_label = f"{index - 1:03d}"
    evaluator = "powChunkMSB" if engine == "direct" else "powChunkHorner"
    if index == 1:
        imports = (
            "import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerChunk\n"
            "import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure"
        )
        previous_state = "(1 : BLSPrimality.X7 recordLower)"
        previous_trace = ".nil"
    else:
        imports = (
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
            f"RecordTwinLowerSeedChunks.Part{previous_label}"
        )
        previous_state = f"recordLowerSeedChunk{previous_label}State"
        previous_trace = f"recordLowerSeedChunk{previous_label}Trace"
    prefix_definition = (
        f"recordLowerSeedChunk{label}Value"
        if index == 1
        else (
            f"recordLowerSeedChunk{previous_label}Prefix * "
            f"2 ^ recordLowerSeedChunk{label}Width + "
            f"recordLowerSeedChunk{label}Value"
        )
    )
    trace_type = "PowerTrace" if engine == "direct" else "PowerHornerTrace"
    trace_bits_proof = (
        ""
        if engine == "horner"
        else f"""
    (by
      set_option exponentiation.threshold 10000 in
        norm_num [recordLowerSeedChunk{label}Width, recordLowerSeedChunk{label}Value])"""
    )
    trace = (
        ""
        if kernel_only
        else f"""
def recordLowerSeedChunk{label}Trace : {trace_type}
    (BLSPrimality.alpha recordLower)
    recordLowerSeedChunk{label}State recordLowerSeedChunk{label}Prefix :=
  .step {previous_trace} recordLowerSeedChunk{label}Width
    recordLowerSeedChunk{label}Value recordLowerSeedChunk{label}State{trace_bits_proof}
    recordLowerSeedChunk{label}_kernel
"""
    )
    return f"""{imports}

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false
set_option linter.defProp false

/-! {note} Chunk {index}. -/

namespace PrimeFactorUnimodality

def recordLowerSeedChunk{label}Width : ℕ := {len(bits)}

def recordLowerSeedChunk{label}Value : ℕ := {int(bits, 2)}

def recordLowerSeedChunk{label}Prefix : ℕ :=
  {prefix_definition}

def recordLowerSeedChunk{label}State : BLSPrimality.X7 recordLower :=
  ⟨{state[0]}, {state[1]}⟩

set_option maxHeartbeats 0 in
-- The closed modular replay intentionally has no heuristic heartbeat budget.
def recordLowerSeedChunk{label}_kernel :
    {evaluator} recordLowerSeedChunk{label}Width recordLowerSeedChunk{label}Value
      {previous_state}
      (BLSPrimality.alpha recordLower) = recordLowerSeedChunk{label}State := by
  rfl

{trace}

end PrimeFactorUnimodality
"""


def render_facade(task: str, chunk_count: int, note: str, engine: str) -> str:
    label = f"{chunk_count:03d}"
    if task == "upper-seed":
        side = "Upper"
        base = "(recordUpperWitnessBase : ZMod recordUpper)"
        state_type = "ZMod recordUpper"
    elif task == "lower-seed":
        side = "Lower"
        base = "BLSPrimality.alpha recordLower"
        state_type = "BLSPrimality.X7 recordLower"
    else:
        raise ValueError("unsupported facade task")
    imported_module = (
        f"PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwin{side}SeedChunks.Part{label}"
    )
    trace_type = "PowerTrace" if engine == "direct" else "PowerHornerTrace"
    return f"""import {imported_module}

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! {note} Closed chunk-chain facade. -/

namespace PrimeFactorUnimodality

def record{side}Seed : {state_type} := record{side}SeedChunk{label}State

set_option maxHeartbeats 0 in
-- The equality closes the externally validated complete binary decomposition.
theorem record{side}_seedExponent_eq_prefix :
    recordSeedExponent = record{side}SeedChunk{label}Prefix := by
  set_option exponentiation.threshold 5000 in
    norm_num [recordSeedExponent, recordFactor, recordBase,
      record{side}SeedChunk{label}Prefix]

theorem record{side}_seed_pow :
    {base} ^ recordSeedExponent = record{side}Seed := by
  rw [record{side}_seedExponent_eq_prefix, record{side}Seed]
  exact ({trace_type}.certifies
    record{side}SeedChunk{label}Trace).symm

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output_directory", type=Path)
    parser.add_argument("--chunk-bits", type=int, default=4096)
    parser.add_argument("--engine", choices=("direct", "horner"), default="direct")
    parser.add_argument("--limit-chunks", type=int)
    parser.add_argument(
        "--kernel-only",
        action="store_true",
        help="render only cached computation kernels, omitting semantic certificates",
    )
    parser.add_argument(
        "--facade-only",
        action="store_true",
        help="rewrite the facade after a complete chunk set without recomputing states",
    )
    args = parser.parse_args()
    if args.chunk_bits <= 0:
        parser.error("--chunk-bits must be positive")
    if args.limit_chunks is not None and args.limit_chunks <= 0:
        parser.error("--limit-chunks must be positive")
    if args.facade_only and args.limit_chunks is not None:
        parser.error("--facade-only cannot be combined with --limit-chunks")
    if args.facade_only and args.kernel_only:
        parser.error("--facade-only cannot be combined with --kernel-only")

    data: dict[str, Any] = json.loads(args.input.read_text())
    note = source_note(data, args.input)
    modulus_int, _, _ = validate_common(data)
    modulus = gmpy2.mpz(modulus_int)
    factor = gmpy2.mpz(data["base"]) ** int(data["factor_exponent"])
    exponent = gmpy2.mpz(data["base"]) ** (int(data["factor_exponent"]) - 1) * (factor - 1)
    exponent_bits = exponent.digits(2)
    all_chunks = [
        exponent_bits[start : start + args.chunk_bits]
        for start in range(0, len(exponent_bits), args.chunk_bits)
    ]
    chunks = all_chunks[: args.limit_chunks] if args.limit_chunks is not None else all_chunks
    complete = len(chunks) == len(all_chunks)

    args.output_directory.mkdir(parents=True, exist_ok=True)
    if args.facade_only:
        missing = [
            index
            for index in range(1, len(all_chunks) + 1)
            if not (args.output_directory / f"Part{index:03d}.lean").is_file()
        ]
        if missing:
            raise ValueError(f"missing chunk files, starting with Part{missing[0]:03d}")
        facade = render_facade(str(data["task"]), len(all_chunks), note, args.engine)
        side = "Upper" if data["task"] == "upper-seed" else "Lower"
        (args.output_directory.parent / f"RecordTwin{side}Seed.lean").write_text(facade)
        print(f"rewrote facade for {len(all_chunks)} chunks")
        return
    prefix = 0
    if data["task"] == "upper-seed":
        witness_base = data.get("witness_base")
        if not isinstance(witness_base, int) or witness_base < 2:
            raise ValueError("invalid upper witness base")
        state = gmpy2.mpz(1)
        base = gmpy2.mpz(witness_base)
        for index, bits in enumerate(chunks, start=1):
            previous_prefix = prefix
            for bit in bits:
                state = state * state % modulus
                if bit == "1":
                    state = state * base % modulus
                prefix = 2 * prefix + int(bit)
            source = render_upper_chunk(
                index,
                bits,
                state,
                previous_prefix,
                prefix,
                witness_base,
                note,
                args.engine,
                args.kernel_only,
            )
            (args.output_directory / f"Part{index:03d}.lean").write_text(source)
        if complete and state != gmpy2.mpz(data["derived"]["seed"]):
            raise ValueError("upper chunk chain does not end at the recorded seed")
    elif data["task"] == "lower-seed":
        state_pair = (gmpy2.mpz(1), gmpy2.mpz(0))
        base_pair = (gmpy2.mpz(1), gmpy2.mpz(1))
        for index, bits in enumerate(chunks, start=1):
            previous_prefix = prefix
            for bit in bits:
                state_pair = quadratic_mul(state_pair, state_pair, modulus)
                if bit == "1":
                    state_pair = quadratic_mul(state_pair, base_pair, modulus)
                prefix = 2 * prefix + int(bit)
            source = render_lower_chunk(
                index,
                bits,
                state_pair,
                previous_prefix,
                prefix,
                note,
                args.engine,
                args.kernel_only,
            )
            (args.output_directory / f"Part{index:03d}.lean").write_text(source)
        if complete:
            expected = (
                gmpy2.mpz(data["derived"]["seed_re"]),
                gmpy2.mpz(data["derived"]["seed_im"]),
            )
            if state_pair != expected:
                raise ValueError("lower chunk chain does not end at the recorded seed")
    else:
        parser.error("input must contain an upper-seed or lower-seed result")
    if complete and prefix != exponent:
        raise ValueError("chunk prefixes do not reconstruct the seed exponent")
    if complete and not args.kernel_only:
        facade = render_facade(str(data["task"]), len(chunks), note, args.engine)
        side = "Upper" if data["task"] == "upper-seed" else "Lower"
        (args.output_directory.parent / f"RecordTwin{side}Seed.lean").write_text(facade)
    print(f"wrote {len(chunks)} chunks ending at exponent prefix {prefix}")


if __name__ == "__main__":
    sys.set_int_max_str_digits(1_000_000)
    main()
