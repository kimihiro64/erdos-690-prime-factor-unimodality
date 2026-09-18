#!/usr/bin/env python3
"""Render the bounded prime list used by the record-gap subcertificate."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.generate_record_gap_block import PRIME_LIMIT, generate, primes_up_to


def render() -> str:
    primes = [prime for prime in primes_up_to(PRIME_LIMIT) if prime >= 13]
    rows = [primes[index : index + 8] for index in range(0, len(primes), 8)]
    body = ",\n      ".join(", ".join(map(str, row)) for row in rows)
    used = sorted(
        {
            int(assignment["owner"])
            for assignment in generate()["assignments"]
            if assignment["source"] == "primorial-tail-prime" and assignment["owner"] is not None
        }
    )
    used_rows = [used[index : index + 8] for index in range(0, len(used), 8)]
    used_body = ",\n      ".join(", ".join(map(str, row)) for row in used_rows)
    return f"""import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Generated factor list for the 4,751-term record-gap subcertificate. -/

namespace PrimeFactorUnimodality

/-- The primes from 13 through 43103.  Only membership and the product are
used by the proof; primality is separately checked for each selected owner. -/
def recordGapPrimeList : List Nat :=
  [{body}]

def recordGapTailProduct : Nat := recordGapPrimeList.prod

def recordGapCenter : Nat := 587 * recordGapTailProduct

theorem recordGapPrimeList_length : recordGapPrimeList.length = {len(primes)} := by
  decide

theorem recordGapPrimeList_le_limit :
    ∀ q ∈ recordGapPrimeList, q ≤ {PRIME_LIMIT} := by
  decide

/-- Tail primes actually selected as owners in the bounded block. -/
def recordGapUsedTailOwners : List Nat :=
  [{used_body}]

theorem recordGapUsedTailOwners_sublist :
    recordGapUsedTailOwners.Sublist recordGapPrimeList := by
  decide

theorem recordGapUsedTailOwners_mem {{q : Nat}}
    (hq : q ∈ recordGapUsedTailOwners) : q ∈ recordGapPrimeList := by
  exact recordGapUsedTailOwners_sublist.mem hq

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render())


if __name__ == "__main__":
    main()
