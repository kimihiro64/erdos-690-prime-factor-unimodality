#!/usr/bin/env python3
"""Generate chunked prime witnesses for the record-range cutoff."""

from __future__ import annotations

import argparse
from pathlib import Path


def primes_below(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * limit
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start:limit:prime] = b"\x00" * (((limit - 1 - start) // prime) + 1)
    return [number for number, is_prime in enumerate(sieve) if is_prime]


def lean_list(values: list[int]) -> str:
    rows = [
        ", ".join(str(value) for value in values[index : index + 10])
        for index in range(0, len(values), 10)
    ]
    return "[\n    " + ",\n    ".join(rows) + "\n  ]"


def render_part(index: int, values: list[int]) -> str:
    label = f"{index:02d}"
    alternatives = " | ".join("rfl" for _ in values)
    return f"""import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated prime witnesses for the record-range cutoff, part {label}. -/

namespace PrimeFactorUnimodality

def recordPrimeWitnessBlock{label} : Finset Nat :=
  {lean_list(values)}.toFinset

set_option maxHeartbeats 0 in
-- Exact cardinality reduction for this generated finite prime block.
theorem recordPrimeWitnessBlock{label}_card :
    recordPrimeWitnessBlock{label}.card = {len(values)} := by
  decide

set_option maxHeartbeats 0 in
-- Kernel primality checks for every generated witness in this block.
theorem recordPrimeWitnessBlock{label}_subset :
    recordPrimeWitnessBlock{label} ⊆ Nat.primesBelow 500001 := by
  intro p hp
  simp only [recordPrimeWitnessBlock{label}, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {alternatives} <;> norm_num [Nat.mem_primesBelow]

theorem recordPrimeWitnessBlock{label}_lower {{p : Nat}}
    (hp : p ∈ recordPrimeWitnessBlock{label}) : {values[0]} ≤ p := by
  simp only [recordPrimeWitnessBlock{label}, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {alternatives} <;> norm_num

theorem recordPrimeWitnessBlock{label}_upper {{p : Nat}}
    (hp : p ∈ recordPrimeWitnessBlock{label}) : p ≤ {values[-1]} := by
  simp only [recordPrimeWitnessBlock{label}, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {alternatives} <;> norm_num

end PrimeFactorUnimodality
"""


def render_first_declaration(chunk: list[int]) -> str:
    return f"""def recordPrimeWitnessesThrough01 : Finset Nat :=
  recordPrimeWitnessBlock01

theorem recordPrimeWitnessesThrough01_card :
    recordPrimeWitnessesThrough01.card = {len(chunk)} :=
  recordPrimeWitnessBlock01_card

theorem recordPrimeWitnessesThrough01_upper {{p : Nat}}
    (hp : p ∈ recordPrimeWitnessesThrough01) : p ≤ {chunk[-1]} :=
  recordPrimeWitnessBlock01_upper hp

theorem recordPrimeWitnessesThrough01_subset :
    recordPrimeWitnessesThrough01 ⊆ Nat.primesBelow 500001 :=
  recordPrimeWitnessBlock01_subset"""


def render_later_declaration(
    index: int, chunk: list[int], previous_upper: int, cumulative_count: int
) -> str:
    label = f"{index:02d}"
    previous = f"{index - 1:02d}"
    union_symbol = "\u222a"
    return f"""def recordPrimeWitnessesThrough{label} : Finset Nat :=
  recordPrimeWitnessesThrough{previous} {union_symbol} recordPrimeWitnessBlock{label}

private theorem recordPrimeWitnessesThrough{previous}_disjoint_block{label} :
    Disjoint recordPrimeWitnessesThrough{previous} recordPrimeWitnessBlock{label} := by
  rw [Finset.disjoint_left]
  intro p hpPrevious hpBlock
  have hpUpper : p ≤ {previous_upper} :=
    recordPrimeWitnessesThrough{previous}_upper hpPrevious
  have hpLower : {chunk[0]} ≤ p := recordPrimeWitnessBlock{label}_lower hpBlock
  omega

set_option maxHeartbeats 0 in
-- Exact cardinality assembly for the cumulative generated witness set.
theorem recordPrimeWitnessesThrough{label}_card :
    recordPrimeWitnessesThrough{label}.card = {cumulative_count} := by
  rw [recordPrimeWitnessesThrough{label},
    Finset.card_union_of_disjoint
      recordPrimeWitnessesThrough{previous}_disjoint_block{label},
    recordPrimeWitnessesThrough{previous}_card,
    recordPrimeWitnessBlock{label}_card]
  norm_num

theorem recordPrimeWitnessesThrough{label}_upper {{p : Nat}}
    (hp : p ∈ recordPrimeWitnessesThrough{label}) : p ≤ {chunk[-1]} := by
  rw [recordPrimeWitnessesThrough{label}, Finset.mem_union] at hp
  rcases hp with hpPrevious | hpBlock
  · exact (recordPrimeWitnessesThrough{previous}_upper hpPrevious).trans (by norm_num)
  · exact recordPrimeWitnessBlock{label}_upper hpBlock

theorem recordPrimeWitnessesThrough{label}_subset :
    recordPrimeWitnessesThrough{label} ⊆ Nat.primesBelow 500001 := by
  rw [recordPrimeWitnessesThrough{label}, Finset.union_subset_iff]
  exact ⟨recordPrimeWitnessesThrough{previous}_subset,
    recordPrimeWitnessBlock{label}_subset⟩"""


def render_assembly(chunks: list[list[int]], count: int) -> str:
    imports = "\n".join(
        sorted(
            "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
            f"RecordPrimeWitnesses.Part{index:02d}"
            for index in range(1, len(chunks) + 1)
        )
    )
    declarations = [render_first_declaration(chunks[0])]
    cumulative_count = len(chunks[0])
    for index, chunk in enumerate(chunks[1:], start=2):
        cumulative_count += len(chunk)
        declarations.append(
            render_later_declaration(index, chunk, chunks[index - 2][-1], cumulative_count)
        )
    chain = "\n\n".join(declarations)
    last = f"{len(chunks):02d}"
    return f"""{imports}

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Assembly of the generated record-range prime witnesses. -/

namespace PrimeFactorUnimodality

{chain}

def recordPrimeWitnesses : Finset Nat :=
  recordPrimeWitnessesThrough{last}

theorem recordPrimeWitnesses_card : recordPrimeWitnesses.card = {count} := by
  exact recordPrimeWitnessesThrough{last}_card

theorem recordPrimeWitnesses_subset :
    recordPrimeWitnesses ⊆ Nat.primesBelow 500001 := by
  exact recordPrimeWitnessesThrough{last}_subset

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--count", type=int, default=38000)
    parser.add_argument("--chunk-size", type=int, default=100)
    args = parser.parse_args()
    primes = primes_below(500001)[: args.count]
    if len(primes) != args.count:
        raise ValueError("not enough primes below the cutoff")
    args.output.mkdir(parents=True, exist_ok=True)
    chunks = [
        primes[index : index + args.chunk_size] for index in range(0, len(primes), args.chunk_size)
    ]
    for index, chunk in enumerate(chunks, start=1):
        (args.output / f"Part{index:02d}.lean").write_text(render_part(index, chunk))
    (args.output.parent / "RecordPrimeWitnesses.lean").write_text(
        render_assembly(chunks, len(primes))
    )
    print(f"wrote {len(chunks)} chunks for {len(primes)} prime witnesses")


if __name__ == "__main__":
    main()
