#!/usr/bin/env python3
"""Render a proof-producing Fermat compositeness certificate for the gap exception."""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

import gmpy2  # type: ignore[import-untyped]

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.generate_record_gap_block import PRIME_LIMIT, primes_up_to


def render_chunk(index: int, bits: str, state: int) -> str:
    label = f"{index:03d}"
    if index == 1:
        imports = (
            "import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerChunk\n"
            "import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure"
        )
        previous_state = "(1 : ZMod recordGapExceptional)"
        previous_trace = ".nil"
        prefix = f"recordGapFermatChunk{label}Value"
    else:
        previous = f"{index - 1:03d}"
        imports = (
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
            f"RecordGapFermatChunks.Part{previous}"
        )
        previous_state = f"recordGapFermatChunk{previous}State"
        previous_trace = f"recordGapFermatChunk{previous}Trace"
        prefix = (
            f"recordGapFermatChunk{previous}Prefix * "
            f"2 ^ recordGapFermatChunk{label}Width + "
            f"recordGapFermatChunk{label}Value"
        )
    return f"""{imports}

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false
set_option linter.defProp false

/-! Generated Fermat replay for the record-gap exception, chunk {index}. -/

namespace PrimeFactorUnimodality

def recordGapFermatChunk{label}Width : Nat := {len(bits)}

def recordGapFermatChunk{label}Value : Nat := {int(bits, 2)}

def recordGapFermatChunk{label}Prefix : Nat :=
  {prefix}

def recordGapFermatChunk{label}State : ZMod recordGapExceptional := {state}

set_option maxHeartbeats 0 in
def recordGapFermatChunk{label}_kernel :
    powChunkHorner recordGapFermatChunk{label}Width recordGapFermatChunk{label}Value
      {previous_state} (2 : ZMod recordGapExceptional) =
        recordGapFermatChunk{label}State := by
  rfl

def recordGapFermatChunk{label}Trace : PowerTrace
    (2 : ZMod recordGapExceptional)
    recordGapFermatChunk{label}State recordGapFermatChunk{label}Prefix :=
  .stepHorner {previous_trace} recordGapFermatChunk{label}Width
    recordGapFermatChunk{label}Value recordGapFermatChunk{label}State
    recordGapFermatChunk{label}_kernel

end PrimeFactorUnimodality
"""


def render_facade(count: int, residue: int) -> str:
    label = f"{count:03d}"
    import_line = (
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordGapFermatChunks.Part{label}"
    )
    return f"""{import_line}

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace PrimeFactorUnimodality

def recordGapFermatResidue : ZMod recordGapExceptional :=
  recordGapFermatChunk{label}State

set_option maxHeartbeats 0 in
theorem recordGapExceptional_exponent_eq_prefix :
    recordGapExceptional - 1 = recordGapFermatChunk{label}Prefix := by
  norm_num [recordGapExceptional, recordGapCenter, recordGapTailProduct,
    recordGapPrimeList, recordGapFermatChunk{label}Prefix]

theorem recordGapExceptional_two_pow :
    (2 : ZMod recordGapExceptional) ^ (recordGapExceptional - 1) =
      recordGapFermatResidue := by
  rw [recordGapExceptional_exponent_eq_prefix, recordGapFermatResidue]
  exact (PowerTrace.certifies recordGapFermatChunk{label}Trace).symm

theorem recordGapExceptional_residue_ne_one : recordGapFermatResidue ≠ 1 := by
  norm_num [recordGapFermatResidue, recordGapFermatChunk{label}State,
    recordGapExceptional, recordGapCenter, recordGapTailProduct,
    recordGapPrimeList]

theorem recordGapExceptional_not_prime : ¬recordGapExceptional.Prime := by
  apply not_prime_of_two_pow_ne_one
  · have := recordGapCenter_large
    unfold recordGapExceptional
    omega
  · rw [recordGapExceptional_two_pow]
    exact recordGapExceptional_residue_ne_one

end PrimeFactorUnimodality
"""


def render_fast(modulus: int, residue: int) -> str:
    return f"""import Mathlib.Tactic.ReduceModChar
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option exponentiation.threshold 100000
set_option linter.style.longLine false

/-! Direct proof-producing reflection of the record-gap Fermat witness. -/

namespace PrimeFactorUnimodality

def recordGapExceptionalValue : Nat := {modulus}

set_option maxHeartbeats 0 in
-- Exact reduction of the 4,499-factor center is intentionally unbounded.
theorem recordGapExceptional_eq_value :
    recordGapExceptional = recordGapExceptionalValue := by
  rfl

set_option maxHeartbeats 0 in
-- Proof-producing modular exponentiation of a 61,993-bit exponent.
theorem recordGapExceptionalLiteral_two_pow :
    (2 : ZMod {modulus}) ^ {modulus - 1} =
      (({residue} : Nat) : ZMod {modulus}) := by
  reduce_mod_char

theorem recordGapExceptionalValue_two_pow :
    (2 : ZMod recordGapExceptionalValue) ^ (recordGapExceptionalValue - 1) =
      (({residue} : Nat) : ZMod recordGapExceptionalValue) := by
  change (2 : ZMod {modulus}) ^ {modulus - 1} =
    (({residue} : Nat) : ZMod {modulus})
  exact recordGapExceptionalLiteral_two_pow

theorem recordGapExceptionalValue_residue_ne_one :
    (({residue} : Nat) : ZMod recordGapExceptionalValue) ≠ 1 := by
  intro residue_eq_one
  have modulus_gt_one : 1 < recordGapExceptionalValue := by
    norm_num [recordGapExceptionalValue]
  have value_eq_one :=
    (ZMod.val_eq_one modulus_gt_one
      (({residue} : Nat) : ZMod recordGapExceptionalValue)).mpr residue_eq_one
  rw [ZMod.val_natCast_of_lt (by norm_num [recordGapExceptionalValue])] at value_eq_one
  norm_num at value_eq_one

theorem recordGapExceptionalValue_two_pow_ne_one :
    (2 : ZMod recordGapExceptionalValue) ^ (recordGapExceptionalValue - 1) ≠ 1 := by
  rw [recordGapExceptionalValue_two_pow]
  exact recordGapExceptionalValue_residue_ne_one

theorem recordGapExceptional_not_prime_fast : ¬recordGapExceptional.Prime := by
  apply not_prime_of_two_pow_ne_one
  · have := recordGapCenter_large
    unfold recordGapExceptional
    omega
  · rw [recordGapExceptional_eq_value]
    exact recordGapExceptionalValue_two_pow_ne_one

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output_directory", type=Path)
    parser.add_argument("--chunk-bits", type=int, default=512)
    parser.add_argument(
        "--emit-chunks",
        action="store_true",
        help="also emit the slower legacy chunk replay",
    )
    args = parser.parse_args()
    if args.chunk_bits <= 0:
        parser.error("--chunk-bits must be positive")

    center = gmpy2.mpz(587)
    for prime in primes_up_to(PRIME_LIMIT):
        if prime >= 13:
            center *= prime
    modulus = center - 84_672
    if math.gcd(2, int(modulus)) != 1:
        raise ValueError("exceptional modulus is not coprime to Fermat base 2")
    exponent = modulus - 1
    exponent_bits = exponent.digits(2)
    chunks = [
        exponent_bits[start : start + args.chunk_bits]
        for start in range(0, len(exponent_bits), args.chunk_bits)
    ]
    state = gmpy2.mpz(1)
    prefix = 0
    args.output_directory.mkdir(parents=True, exist_ok=True)
    for index, bits in enumerate(chunks, start=1):
        for bit in bits:
            state = state * state % modulus
            if bit == "1":
                state = 2 * state % modulus
            prefix = 2 * prefix + int(bit)
        if args.emit_chunks:
            (args.output_directory / f"Part{index:03d}.lean").write_text(
                render_chunk(index, bits, int(state))
            )
    if prefix != exponent:
        raise ValueError("chunk prefixes do not reconstruct the exponent")
    if state == 1:
        raise ValueError("base 2 is a Fermat pseudoprime for the exception")
    if args.emit_chunks:
        facade = args.output_directory.parent / "RecordGapFermat.lean"
        facade.write_text(render_facade(len(chunks), int(state)))
    fast = args.output_directory.parent / "RecordGapFermatFast.lean"
    fast.write_text(render_fast(int(modulus), int(state)))
    mode = (
        f"{len(chunks)} legacy chunks and fast certificate"
        if args.emit_chunks
        else "fast certificate"
    )
    print(f"wrote {mode}; final residue has {len(str(state))} digits")


if __name__ == "__main__":
    sys.set_int_max_str_digits(1_000_000)
    main()
