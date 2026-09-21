#!/usr/bin/env python3
# ruff: noqa: RUF001
"""Generate segmented sieve certificates for the record reciprocal bound."""

from __future__ import annotations

import argparse
from pathlib import Path

SCALE = 1_000_000_000
LIMIT = 500_001


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
        ", ".join(str(value) for value in values[index : index + 12])
        for index in range(0, len(values), 12)
    ]
    return "[\n    " + ",\n    ".join(rows) + "\n  ]"


def render_basic(small_primes: list[int]) -> str:
    alternatives = " | ".join("rfl" for _ in small_primes)
    return f"""import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

/-! A finite wheel sieve and its interval-composition lemma.  Every prime is
a candidate, so summing over candidates gives a certified upper bound while
avoiding primality reduction at every integer below the cutoff. -/

namespace PrimeFactorUnimodality

def reciprocalCertificateScale : Nat := 1000000000

def roundedReciprocalNumerator (p : Nat) : Nat :=
  reciprocalCertificateScale / p + 1

def reciprocalSievePrimeList : List Nat :=
  {lean_list(small_primes)}

def reciprocalSieveCandidate (n : Nat) : Prop :=
  (n < 500 ∧ n.Prime) ∨
    (499 < n ∧
      reciprocalSievePrimeList.all (fun p => decide (¬p ∣ n)) = true)

instance (n : Nat) : Decidable (reciprocalSieveCandidate n) :=
  by unfold reciprocalSieveCandidate; infer_instance

theorem prime_mem_reciprocalSieveCandidate {{p : Nat}} (hp : p.Prime) :
    reciprocalSieveCandidate p := by
  by_cases hpSmall : p < 500
  · exact Or.inl ⟨hpSmall, hp⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [List.all_eq_true]
    intro q hq
    rw [decide_eq_true_eq]
    intro hqDvd
    have hqData : 2 ≤ q ∧ q < 500 := by
      simp only [reciprocalSievePrimeList, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with {alternatives} <;> norm_num
    rcases (Nat.dvd_prime hp).mp hqDvd with qOne | qEq
    · omega
    · omega

def roundedReciprocalBlockSum (lower upper : Nat) : Nat :=
  ∑ p ∈ (Finset.Ico lower upper).filter reciprocalSieveCandidate,
    roundedReciprocalNumerator p

def roundedReciprocalSieveSumBelow (upper : Nat) : Nat :=
  ∑ p ∈ (Finset.range upper).filter reciprocalSieveCandidate,
    roundedReciprocalNumerator p

theorem roundedReciprocalSieveSumBelow_add_block
    {{lower upper : Nat}} (h : lower ≤ upper) :
    roundedReciprocalSieveSumBelow upper =
      roundedReciprocalSieveSumBelow lower + roundedReciprocalBlockSum lower upper := by
  rw [roundedReciprocalSieveSumBelow, roundedReciprocalSieveSumBelow,
    roundedReciprocalBlockSum, Finset.range_eq_Ico,
    ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le lower) h,
    Finset.filter_union]
  have intervalsDisjoint :
      Disjoint (Finset.Ico 0 lower) (Finset.Ico lower upper) := by
    rw [Finset.disjoint_left]
    intro p hpLower hpUpper
    simp only [Finset.mem_Ico] at hpLower hpUpper
    omega
  rw [Finset.sum_union (Finset.disjoint_filter_filter intervalsDisjoint)]
  rw [Nat.Ico_zero_eq_range]

theorem roundedReciprocalBlockSum_add_block
    {{lower middle upper : Nat}} (h₁ : lower ≤ middle) (h₂ : middle ≤ upper) :
    roundedReciprocalBlockSum lower upper =
      roundedReciprocalBlockSum lower middle +
        roundedReciprocalBlockSum middle upper := by
  rw [roundedReciprocalBlockSum, roundedReciprocalBlockSum,
    roundedReciprocalBlockSum,
    ← Finset.Ico_union_Ico_eq_Ico h₁ h₂, Finset.filter_union]
  have intervalsDisjoint :
      Disjoint (Finset.Ico lower middle) (Finset.Ico middle upper) := by
    rw [Finset.disjoint_left]
    intro p hpLower hpUpper
    simp only [Finset.mem_Ico] at hpLower hpUpper
    omega
  rw [Finset.sum_union (Finset.disjoint_filter_filter intervalsDisjoint)]

end PrimeFactorUnimodality
"""


def render_part(
    index: int,
    lower: int,
    upper: int,
    block_sum: int,
) -> str:
    label = f"{index:03d}"
    previous_import = (
        "\nimport PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordReciprocalBlocks.Part{index - 1:03d}"
        if index > 1
        else ""
    )
    return f"""import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Basic
{previous_import}

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated wheel-sieve interval certificate, part {label}. -/

namespace PrimeFactorUnimodality

set_option maxHeartbeats 0 in
-- Kernel reduction of all wheel-divisibility tests in this finite interval.
theorem roundedReciprocalBlockSum_{label} :
    roundedReciprocalBlockSum {lower} {upper} = {block_sum} := by
  decide

end PrimeFactorUnimodality
"""


def render_group(
    group_index: int,
    members: list[tuple[int, int, int, int]],
    group_total: int,
) -> str:
    previous_group_import = (
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordReciprocalBlocks.Group{group_index - 1:03d}"
        if group_index > 1
        else ""
    )
    last_part = members[-1][0]
    imports = f"{previous_group_import}\n" if previous_group_import else ""
    imports += (
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordReciprocalBlocks.Part{last_part:03d}"
    )
    group_lower = members[0][1]
    first_upper = members[0][2]
    calc_lines = [
        f"    roundedReciprocalBlockSum {group_lower} {members[-1][2]} =",
        f"        roundedReciprocalBlockSum {group_lower} {first_upper} +",
        "          "
        + " + ".join(
            f"roundedReciprocalBlockSum {lower} {upper}"
            for _index, lower, upper, _sum in members[1:]
        )
        + " := by",
        "      "
        + "rw ["
        + ", ".join(
            "roundedReciprocalBlockSum_add_block "
            f"(show {group_lower} ≤ {lower} by omega) "
            f"(show {lower} ≤ {upper} by omega)"
            for _index, lower, upper, _sum in reversed(members[1:])
        )
        + "]",
        "    _ = " + " + ".join(str(item[3]) for item in members) + " := by",
        "      rw ["
        + ", ".join(f"roundedReciprocalBlockSum_{item[0]:03d}" for item in members)
        + "]",
        f"    _ = {group_total} := by norm_num",
    ]
    return f"""{imports}

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group {group_index:03d}. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_{group_index:03d} :
    roundedReciprocalBlockSum {group_lower} {members[-1][2]} = {group_total} := by
  calc
{chr(10).join(calc_lines)}

end PrimeFactorUnimodality
"""


def render_assembly(groups: list[tuple[int, int, int, int]], total: int) -> str:
    last_group = groups[-1][0]
    imports = (
        "import PrimeFactorUnimodality.Proof.LargeRange.Generated."
        f"RecordReciprocalBlocks.Group{last_group:03d}"
    )
    _first_index, first_lower, _first_upper, _first_sum = groups[0]
    block_terms = " + ".join(
        f"roundedReciprocalBlockSum {lower} {upper}" for _index, lower, upper, _sum in groups
    )
    split_rewrites = ", ".join(
        "roundedReciprocalBlockSum_add_block "
        f"(show {first_lower} ≤ {lower} by omega) "
        f"(show {lower} ≤ {upper} by omega)"
        for _index, lower, upper, _sum in reversed(groups[1:])
    )
    group_rewrites = ", ".join(
        f"roundedReciprocalGroup_{index:03d}" for index, _lower, _upper, _sum in groups
    )
    numeral_sum = " + ".join(str(group_sum) for _i, _l, _u, group_sum in groups)
    return f"""{imports}

set_option autoImplicit false

/-! Assembly of all segmented reciprocal wheel-sieve certificates. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalSieveSumBelow_500001_eq :
    roundedReciprocalSieveSumBelow 500001 = {total} := by
  calc
    roundedReciprocalSieveSumBelow 500001 =
        roundedReciprocalSieveSumBelow 0 +
          roundedReciprocalBlockSum 0 500001 :=
      roundedReciprocalSieveSumBelow_add_block (by omega)
    _ = roundedReciprocalBlockSum 0 500001 := by
      simp [roundedReciprocalSieveSumBelow]
    _ = {block_terms} := by
      rw [{split_rewrites}]
    _ = {numeral_sum} := by
      rw [{group_rewrites}]
    _ = {total} := by norm_num

end PrimeFactorUnimodality
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--chunk-size", type=int, default=1000)
    parser.add_argument("--group-size", type=int, default=10)
    args = parser.parse_args()

    small_primes = primes_below(500)
    small_prime_set = set(small_primes)
    candidates = [
        number
        for number in range(LIMIT)
        if number in small_prime_set
        or (number > 499 and all(number % prime != 0 for prime in small_primes))
    ]
    total = sum(SCALE // number + 1 for number in candidates)
    bounds = []
    lower = 0
    while lower < LIMIT:
        upper = min(lower + args.chunk_size, LIMIT)
        bounds.append((lower, upper))
        lower = upper

    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "Basic.lean").write_text(render_basic(small_primes))
    part_data = []
    for index, (lower, upper) in enumerate(bounds, start=1):
        block_sum = sum(SCALE // number + 1 for number in candidates if lower <= number < upper)
        (args.output / f"Part{index:03d}.lean").write_text(
            render_part(index, lower, upper, block_sum)
        )
        part_data.append((index, lower, upper, block_sum))
    groups: list[tuple[int, int, int, int]] = []
    for offset in range(0, len(part_data), args.group_size):
        members = part_data[offset : offset + args.group_size]
        group_index = len(groups) + 1
        group_total = sum(item[3] for item in members)
        (args.output / f"Group{group_index:03d}.lean").write_text(
            render_group(group_index, members, group_total)
        )
        groups.append((group_index, members[0][1], members[-1][2], group_total))
    facade = args.output.parent / "RecordReciprocalBlocks.lean"
    facade.write_text(render_assembly(groups, total))
    print(
        f"wrote {len(bounds)} blocks and {len(groups)} groups; "
        f"candidates={len(candidates)}; total={total}"
    )


if __name__ == "__main__":
    main()
