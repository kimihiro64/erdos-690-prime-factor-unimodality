#!/usr/bin/env python3
"""Independently compute the ten record-twin BLS/Pocklington residues.

This generator is not part of the trusted proof.  Its outputs are inputs to a
separate Lean replay, which must reconstruct kernel-checked proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from pathlib import Path

import gmpy2  # type: ignore[import-untyped]

BASE = gmpy2.mpz(504_983_334)
PRIME_DIVISORS = (2, 3, 17, 4_950_817)


def quadratic_mul(
    left: tuple[gmpy2.mpz, gmpy2.mpz],
    right: tuple[gmpy2.mpz, gmpy2.mpz],
    modulus: gmpy2.mpz,
) -> tuple[gmpy2.mpz, gmpy2.mpz]:
    a, b = left
    c, d = right
    return ((a * c + 7 * b * d) % modulus, (a * d + b * c) % modulus)


def quadratic_pow(
    base: tuple[gmpy2.mpz, gmpy2.mpz], exponent: gmpy2.mpz, modulus: gmpy2.mpz
) -> tuple[gmpy2.mpz, gmpy2.mpz]:
    result = (gmpy2.mpz(1), gmpy2.mpz(0))
    for bit in exponent.digits(2):
        result = quadratic_mul(result, result, modulus)
        if bit == "1":
            result = quadratic_mul(result, base, modulus)
    return result


def lucas_uv_mod(
    p: int, q: int, exponent: gmpy2.mpz, modulus: gmpy2.mpz
) -> tuple[gmpy2.mpz, gmpy2.mpz]:
    """Return U_exponent(P,Q), V_exponent(P,Q) modulo an odd modulus."""
    u = gmpy2.mpz(0)
    v = gmpy2.mpz(2)
    q_power = gmpy2.mpz(1)
    discriminant = p * p - 4 * q
    inverse_two = (modulus + 1) // 2
    for bit in exponent.digits(2):
        u_double = (u * v) % modulus
        v_double = (v * v - 2 * q_power) % modulus
        q_double = (q_power * q_power) % modulus
        if bit == "0":
            u, v, q_power = u_double, v_double, q_double
        else:
            u = ((p * u_double + v_double) * inverse_two) % modulus
            v = ((discriminant * u_double + p * v_double) * inverse_two) % modulus
            q_power = (q_double * q) % modulus
    return u, v


def write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(payload, sort_keys=True, indent=2) + "\n").encode()
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(encoded)
    os.replace(temporary, path)


def decimal(value: gmpy2.mpz) -> str:
    return str(value.digits(10))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "task",
        choices=(
            "lower-main",
            "lower-proper",
            "upper-main",
            "upper-proper",
            "lower-seed",
            "upper-seed",
        ),
    )
    parser.add_argument("--prime", type=int, choices=PRIME_DIVISORS)
    parser.add_argument("--witness-base", type=int, default=7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.task.endswith("proper") and args.prime is None:
        parser.error("--prime is required for a proper-residue task")

    factor = BASE**4096
    lower = factor * (factor - 1) - 1
    upper = factor * (factor - 1) + 1
    started = time.monotonic()

    derived: dict[str, object] | None = None
    if args.task == "lower-main":
        modulus = lower
        exponent = lower + 1
        residue = gmpy2.lucasu_mod(2, -6, exponent, modulus)
    elif args.task == "lower-proper":
        modulus = lower
        exponent = (lower + 1) // args.prime
        residue = gmpy2.lucasu_mod(2, -6, exponent, modulus)
    elif args.task == "upper-main":
        modulus = upper
        exponent = upper - 1
        residue = gmpy2.powmod(args.witness_base, exponent, modulus)
    elif args.task == "upper-proper":
        modulus = upper
        exponent = (upper - 1) // args.prime
        residue = (gmpy2.powmod(args.witness_base, exponent, modulus) - 1) % modulus

    elif args.task == "lower-seed":
        modulus = lower
        exponent = BASE**4095 * (factor - 1)
        # For alpha = 1 + sqrt(7) and alphaBar = 1 - sqrt(7), the Lucas
        # parameters are P = alpha + alphaBar = 2 and Q = alpha*alphaBar = -6.
        # Hence alpha^e = V_e/2 + U_e*sqrt(7) modulo the odd modulus.
        u, v = lucas_uv_mod(2, -6, exponent, modulus)
        inverse_two = (modulus + 1) // 2
        residue = u
        seed = ((v * inverse_two) % modulus, u)
        main = quadratic_pow(seed, BASE, modulus)
        proper = {}
        for prime in PRIME_DIVISORS:
            value = quadratic_pow(seed, BASE // prime, modulus)[1]
            value_gcd, value_s, value_t = gmpy2.gcdext(value, modulus)
            proper[str(prime)] = {
                "residue": decimal(value),
                "gcd": decimal(value_gcd),
                "bezout_residue": decimal(value_s),
                "bezout_modulus": decimal(value_t),
            }
        derived = {
            "seed_re": decimal(seed[0]),
            "seed_im": decimal(seed[1]),
            "main_re": decimal(main[0]),
            "main_im": decimal(main[1]),
            "proper": proper,
        }
    else:
        modulus = upper
        exponent = BASE**4095 * (factor - 1)
        residue = gmpy2.powmod(args.witness_base, exponent, modulus)
        main = gmpy2.powmod(residue, BASE, modulus)
        proper = {}
        for prime in PRIME_DIVISORS:
            value = (gmpy2.powmod(residue, BASE // prime, modulus) - 1) % modulus
            value_gcd, value_s, value_t = gmpy2.gcdext(value, modulus)
            proper[str(prime)] = {
                "residue": decimal(value),
                "gcd": decimal(value_gcd),
                "bezout_residue": decimal(value_s),
                "bezout_modulus": decimal(value_t),
            }
        derived = {
            "seed": decimal(residue),
            "main": decimal(main),
            "proper": proper,
        }

    gcd, bezout_residue, bezout_modulus = gmpy2.gcdext(residue, modulus)
    payload = {
        "schema_version": 1,
        "task": args.task,
        "prime": args.prime,
        "base": int(BASE),
        "witness_base": args.witness_base if args.task.startswith("upper") else None,
        "factor_exponent": 4096,
        "modulus_sha256": hashlib.sha256(decimal(modulus).encode()).hexdigest(),
        "modulus_digits": gmpy2.num_digits(modulus, 10),
        "exponent_bits": exponent.bit_length(),
        "residue": decimal(residue),
        "gcd": decimal(gcd),
        "bezout_residue": decimal(bezout_residue),
        "bezout_modulus": decimal(bezout_modulus),
        "elapsed_seconds": time.monotonic() - started,
    }
    if derived is not None:
        payload["derived"] = derived
    write_json(args.output, payload)
    print(
        f"{args.task} prime={args.prime} digits={payload['modulus_digits']} "
        f"gcd={payload['gcd']} seconds={payload['elapsed_seconds']:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    sys.set_int_max_str_digits(1_000_000)
    main()
