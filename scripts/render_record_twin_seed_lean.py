#!/usr/bin/env python3
# ruff: noqa: RUF001 -- Lean source strings intentionally use blackboard-bold types.
"""Render shared-seed Lean replay modules from one seed computation JSON."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any

PRIMES = (2, 3, 17, 4_950_817)
BASE = 504_983_334
FACTOR_EXPONENT = 4096


def quadratic_mul(left: tuple[int, int], right: tuple[int, int], modulus: int) -> tuple[int, int]:
    a, b = left
    c, d = right
    return ((a * c + 7 * b * d) % modulus, (a * d + b * c) % modulus)


def quadratic_pow(base: tuple[int, int], exponent: int, modulus: int) -> tuple[int, int]:
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = quadratic_mul(result, base, modulus)
        base = quadratic_mul(base, base, modulus)
        exponent //= 2
    return result


def validate_common(data: dict[str, Any]) -> tuple[int, int, int]:
    if data.get("schema_version") != 1:
        raise ValueError("unsupported result schema")
    if data.get("base") != BASE or data.get("factor_exponent") != FACTOR_EXPONENT:
        raise ValueError("record-base metadata mismatch")
    factor = BASE**FACTOR_EXPONENT
    lower = factor * (factor - 1) - 1
    upper = lower + 2
    modulus = lower if data["task"] == "lower-seed" else upper
    decimal_modulus = str(modulus)
    if data.get("modulus_digits") != len(decimal_modulus):
        raise ValueError("modulus digit count mismatch")
    if data.get("modulus_sha256") != hashlib.sha256(decimal_modulus.encode()).hexdigest():
        raise ValueError("modulus digest mismatch")
    expected_exponent = BASE ** (FACTOR_EXPONENT - 1) * (factor - 1)
    if data.get("exponent_bits") != expected_exponent.bit_length():
        raise ValueError("seed-exponent metadata mismatch")
    return modulus, lower, upper


def validate_bezout(entry: dict[str, str], modulus: int, label: str) -> None:
    residue = int(entry["residue"])
    inverse = int(entry["bezout_residue"])
    modulus_coefficient = int(entry["bezout_modulus"])
    gcd = int(entry["gcd"])
    if gcd != 1:
        raise ValueError(f"{label}: proper residue is not a unit (gcd has {len(str(gcd))} digits)")
    if residue * inverse + modulus * modulus_coefficient != gcd:
        raise ValueError(f"{label}: Bezout identity mismatch")


def atomic_write(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(source)
    os.replace(temporary, path)


def source_note(data: dict[str, Any], source_json: Path) -> str:
    # Wall-clock timing is diagnostic metadata, not certificate content.  Hash
    # the canonical arithmetic payload so independently repeated runs produce
    # the same provenance identifier.
    semantic_data = dict(data)
    semantic_data.pop("elapsed_seconds", None)
    encoded = json.dumps(
        semantic_data, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    return f"Generated from `{source_json}` (semantic SHA-256 `{digest}`, excluding elapsed time)."


def lower_sources(data: dict[str, Any], source_json: Path) -> tuple[str, str]:
    modulus, _, _ = validate_common(data)
    derived = data["derived"]
    seed = (int(derived["seed_re"]), int(derived["seed_im"]))
    main = quadratic_pow(seed, BASE, modulus)
    if main != (int(derived["main_re"]), int(derived["main_im"])):
        raise ValueError("lower main residue does not derive from the seed")
    if main[1] != 0:
        raise ValueError("lower main residue is not zero")
    for prime in PRIMES:
        entry = derived["proper"][str(prime)]
        expected = quadratic_pow(seed, BASE // prime, modulus)[1]
        if int(entry["residue"]) != expected:
            raise ValueError(f"lower proper residue for {prime} does not derive from the seed")
        validate_bezout(entry, modulus, f"lower/{prime}")
    note = source_note(data, source_json)
    seed_source = f"""import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! {note} -/

namespace PrimeFactorUnimodality

def recordLowerSeed : BLSPrimality.X7 recordLower :=
  ⟨{derived["seed_re"]}, {derived["seed_im"]}⟩

set_option maxHeartbeats 0 in
-- Kernel replay of the shared binary-power seed computation.
theorem recordLower_seed_kernel :
    npowBinRecAuto recordSeedExponent (BLSPrimality.alpha recordLower) =
      recordLowerSeed := by
  rfl

theorem recordLower_seed_pow :
    BLSPrimality.alpha recordLower ^ recordSeedExponent = recordLowerSeed := by
  change npowRecAuto recordSeedExponent (BLSPrimality.alpha recordLower) = recordLowerSeed
  rw [npowRec_eq_npowBinRec]
  exact recordLower_seed_kernel

end PrimeFactorUnimodality
"""
    imports = "import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeed"
    body = [
        imports,
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 1000000",
        "",
        f"/-! {note} -/",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "set_option maxHeartbeats 0 in",
        "-- Kernel replay of the full lower-candidate power computation.",
        "theorem recordLower_main_kernel :",
        "    (BLSPrimality.alpha recordLower ^ (recordLower + 1)).im = 0 := by",
        "  rw [← recordSeedExponent_mul_base, pow_mul, recordLower_seed_pow]",
        "  change (npowRecAuto recordBase recordLowerSeed).im = 0",
        "  rw [npowRec_eq_npowBinRec]",
        "  rfl",
        "",
    ]
    for prime in PRIMES:
        inverse = derived["proper"][str(prime)]["bezout_residue"]
        body.extend(
            [
                "set_option maxHeartbeats 0 in",
                "-- Kernel replay of this lower-candidate proper-factor witness.",
                f"theorem recordLower_proper_{prime}_kernel :",
                "    IsUnit ((BLSPrimality.alpha recordLower ^",
                f"      ((recordLower + 1) / {prime})).im) := by",
                f"  rw [recordLower_quotient_eq_seed_mul {prime} (by norm_num [recordBase]),",
                "    pow_mul, recordLower_seed_pow]",
                f"  change IsUnit ((npowRecAuto (recordBase / {prime}) recordLowerSeed).im)",
                "  rw [npowRec_eq_npowBinRec]",
                f"  apply IsUnit.of_mul_eq_one (({inverse} : ℤ) : ZMod recordLower)",
                "  rfl",
                "",
            ]
        )
    body.extend(["end PrimeFactorUnimodality", ""])
    return seed_source, "\n".join(body)


def upper_sources(data: dict[str, Any], source_json: Path) -> tuple[str, str]:
    modulus, _, _ = validate_common(data)
    derived = data["derived"]
    witness_base = data.get("witness_base")
    if not isinstance(witness_base, int) or witness_base < 2:
        raise ValueError("invalid upper witness base")
    seed = int(derived["seed"])
    main = pow(seed, BASE, modulus)
    if main != int(derived["main"]):
        raise ValueError("upper main residue does not derive from the seed")
    if main != 1:
        raise ValueError("upper main residue is not one")
    for prime in PRIMES:
        entry = derived["proper"][str(prime)]
        expected = (pow(seed, BASE // prime, modulus) - 1) % modulus
        if int(entry["residue"]) != expected:
            raise ValueError(f"upper proper residue for {prime} does not derive from the seed")
        validate_bezout(entry, modulus, f"upper/{prime}")
    note = source_note(data, source_json)
    seed_source = f"""import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! {note} -/

namespace PrimeFactorUnimodality

def recordUpperWitnessBase : ℕ := {witness_base}

def recordUpperSeed : ZMod recordUpper := {derived["seed"]}

set_option maxHeartbeats 0 in
-- Kernel replay of the shared binary-power seed computation.
theorem recordUpper_seed_kernel :
    npowBinRecAuto recordSeedExponent
      (recordUpperWitnessBase : ZMod recordUpper) = recordUpperSeed := by
  rfl

theorem recordUpper_seed_pow :
    (recordUpperWitnessBase : ZMod recordUpper) ^ recordSeedExponent =
      recordUpperSeed := by
  change npowRecAuto recordSeedExponent
    (recordUpperWitnessBase : ZMod recordUpper) = recordUpperSeed
  rw [npowRec_eq_npowBinRec]
  exact recordUpper_seed_kernel

end PrimeFactorUnimodality
"""
    imports = "import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeed"
    body = [
        imports,
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 1000000",
        "",
        f"/-! {note} -/",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "set_option maxHeartbeats 0 in",
        "-- Kernel replay of the full upper-candidate power computation.",
        "theorem recordUpper_main_kernel :",
        "    (recordUpperWitnessBase : ZMod recordUpper) ^",
        "      (recordUpper - 1) = 1 := by",
        "  rw [← recordSeedExponent_mul_base_upper, pow_mul, recordUpper_seed_pow]",
        "  change npowRecAuto recordBase recordUpperSeed = 1",
        "  rw [npowRec_eq_npowBinRec]",
        "  rfl",
        "",
    ]
    for prime in PRIMES:
        inverse = derived["proper"][str(prime)]["bezout_residue"]
        body.extend(
            [
                "set_option maxHeartbeats 0 in",
                "-- Kernel replay of this upper-candidate proper-factor witness.",
                f"theorem recordUpper_proper_{prime}_kernel :",
                "    IsUnit ((recordUpperWitnessBase : ZMod recordUpper) ^",
                f"      ((recordUpper - 1) / {prime}) - 1) := by",
                f"  rw [recordUpper_quotient_eq_seed_mul {prime} (by norm_num [recordBase]),",
                "    pow_mul, recordUpper_seed_pow]",
                f"  change IsUnit (npowRecAuto (recordBase / {prime}) recordUpperSeed - 1)",
                "  rw [npowRec_eq_npowBinRec]",
                f"  apply IsUnit.of_mul_eq_one (({inverse} : ℤ) : ZMod recordUpper)",
                "  rfl",
                "",
            ]
        )
    body.extend(["end PrimeFactorUnimodality", ""])
    return seed_source, "\n".join(body)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("seed_output", type=Path)
    parser.add_argument("residues_output", type=Path)
    parser.add_argument(
        "--residues-only",
        action="store_true",
        help="validate the shared seed but emit only the derived-residue module",
    )
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    if data["task"] == "lower-seed":
        seed, residues = lower_sources(data, args.input)
    elif data["task"] == "upper-seed":
        seed, residues = upper_sources(data, args.input)
    else:
        parser.error("input must be a lower-seed or upper-seed result")
    if not args.residues_only:
        atomic_write(args.seed_output, seed)
    atomic_write(args.residues_output, residues)
    if args.residues_only:
        print(f"wrote {args.residues_output} (residues only)")
    else:
        print(f"wrote {args.seed_output} and {args.residues_output}")


if __name__ == "__main__":
    sys.set_int_max_str_digits(1_000_000)
    main()
