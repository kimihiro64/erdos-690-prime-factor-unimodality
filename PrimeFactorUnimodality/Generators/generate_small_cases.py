#!/usr/bin/env python3
"""Generate kernel-checked finite certificates for the Erdős 690 proof."""

from __future__ import annotations

from itertools import pairwise
from pathlib import Path

from fixed_weight_data import (
    FIXED_WEIGHT_SCALE,
    fixed_weight_values,
    medium_weight_bounds_module,
)

CASES = {
    3: (13, 17, 17, 19),
    4: (23, 29, 29, 31),
    5: (31, 37, 37, 41),
    6: (73, 79, 79, 83),
    7: (89, 97, 97, 101),
    8: (113, 127, 127, 131),
    9: (113, 127, 127, 131),
    10: (113, 127, 127, 131),
    11: (293, 307, 307, 311),
    12: (293, 307, 307, 311),
    13: (523, 541, 541, 547),
    14: (523, 541, 541, 547),
    15: (523, 541, 541, 547),
    16: (887, 907, 907, 911),
    17: (887, 907, 907, 911),
    18: (887, 907, 907, 911),
    19: (1129, 1151, 1151, 1153),
}

MAX_DEGREES = {
    p: max(degree for degree, data in CASES.items() if p in (data[0], data[2]))
    for p in {endpoint for data in CASES.values() for endpoint in (data[0], data[2])}
}


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))


def primes_below(n: int) -> list[int]:
    return [q for q in range(n) if is_prime(q)]


def lean_list(values: list[int], indent: str = "    ") -> str:
    chunks = [", ".join(map(str, values[i : i + 12])) for i in range(0, len(values), 12)]
    if len(chunks) <= 1:
        return "[" + (chunks[0] if chunks else "") + "]"
    return "[" + (",\n" + indent).join(chunks) + "]"


def numerator_rows(values: list[int], degree: int) -> list[list[int]]:
    rows = [[0] * (degree + 1) for _ in range(len(values) + 1)]
    rows[-1][0] = 1
    for index in range(len(values) - 1, -1, -1):
        p = values[index]
        rows[index][0] = (p - 1) * rows[index + 1][0]
        for r in range(1, degree + 1):
            rows[index][r] = (p - 1) * rows[index + 1][r] + rows[index + 1][r - 1]
    return rows


def consecutive(p: int, q: int) -> str:
    ending = "  omega\n" if q == p + 1 else "  interval_cases m <;> decide\n"
    return f"""set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive{p}_{q} : ConsecutivePrimes {p} {q} := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
{ending}

"""


def ratio_proof(p: int, degree: int) -> str:
    bound = MAX_DEGREES[p]
    return f"""    rw [densityRatio_perm primesBelow{p}_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix{p}
        primePrefix{p}_gt_one {degree},
      ← selectionRowBounded_getD {bound} primePrefix{p} ({degree} - 1) (by omega),
      ← selectionRowBounded_getD {bound} primePrefix{p} {degree} (by omega),
      numericalRow{p}]
    norm_num
"""


def row_modules(p: int, degree: int) -> dict[str, str]:
    primes = primes_below(p + 1)
    transitions = list(pairwise(primes))
    modules: dict[str, str] = {}
    previous_module = ""
    for part_index, offset in enumerate(range(0, len(transitions), 60), start=1):
        module_name = f"Row{p}.Part{part_index:02d}"
        if part_index == 1:
            imports = """import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
"""
        else:
            imports = (
                "import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated."
                f"{previous_module}\n"
            )
        body = f"""{imports}
/-! Generated segment {part_index} of the bounded selection row for endpoint {p}. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

"""
        if part_index == 1:
            body += f"""set_option linter.style.longLine false in
theorem numericalRow{p}_2 :
    selectionRowBounded {degree} primePrefix2 =
      {lean_list([1] + [0] * degree, "      ")} := by
  rfl

"""
        for left, right in transitions[offset : offset + 60]:
            row = numerator_rows(list(reversed(primes_below(right))), degree)[0]
            body += f"""set_option linter.style.longLine false in
theorem numericalRow{p}_{right} :
    selectionRowBounded {degree} primePrefix{right} =
      {lean_list(row, "      ")} := by
  rw [primePrefix{right}, selectionRowBounded, numericalRow{p}_{left}]
  norm_num [selectionRowStep, selectionRowTail]

"""
        body += "end PrimeFactorUnimodality\n"
        modules[f"Row{p}/Part{part_index:02d}.lean"] = body
        previous_module = module_name
    final_row = numerator_rows(list(reversed(primes_below(p))), degree)[0]
    final_import = (
        f"import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.{previous_module}"
    )
    modules[f"Row{p}.lean"] = f"""{final_import}

/-! Facade for the generated bounded selection row at endpoint {p}. -/

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow{p} :
    selectionRowBounded {degree} primePrefix{p} =
      {lean_list(final_row, "      ")} :=
  numericalRow{p}_{p}

end PrimeFactorUnimodality
"""
    return modules


def prefix_modules() -> dict[str, str]:
    primes = primes_below(1152)
    transitions = list(pairwise(primes))
    modules: dict[str, str] = {}
    previous_module = ""
    for part_index, offset in enumerate(range(0, len(transitions), 18), start=1):
        module_name = f"PrimePrefixes.Part{part_index:02d}"
        if part_index == 1:
            imports = """import Mathlib.Tactic.IntervalCases
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
"""
        else:
            imports = (
                "import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated."
                f"{previous_module}\n"
            )
        body = f"""{imports}

set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

"""
        if part_index == 1:
            body += """/-- The empty reverse-ordered list of primes below two. -/
def primePrefix2 : List Nat := []

theorem primesBelow2_perm : (primesBelow 2).Perm primePrefix2 := by
  change ((Nat.primesBelow 2).sort (fun a b => a ≤ b)).Perm []
  rw [show Nat.primesBelow 2 = ∅ by
    ext q
    simp only [Nat.mem_primesBelow]
    simp only [Order.lt_two_iff, Finset.notMem_empty, iff_false, not_and]
    intro hq hprime
    exact (not_le_of_gt hprime.one_lt) hq]
  simp

theorem primePrefix2_gt_one : ∀ q ∈ primePrefix2, 1 < q := by
  simp [primePrefix2]

"""
        for left, right in transitions[offset : offset + 18]:
            body += consecutive(left, right)
            body += f"""/-- Generated reverse-ordered list of all primes below {right}. -/
def primePrefix{right} : List Nat :=
  {left} :: primePrefix{left}

theorem primesBelow{right}_perm :
    (primesBelow {right}).Perm primePrefix{right} := by
  rw [primePrefix{right}]
  exact consecutive{left}_{right}.primesBelow_perm.trans
    (List.Perm.cons {left} primesBelow{left}_perm)

theorem primePrefix{right}_gt_one : ∀ q ∈ primePrefix{right}, 1 < q := by
  intro q hq
  rw [primePrefix{right}] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix{left}_gt_one q hq

"""
        modules[f"PrimePrefixes/Part{part_index:02d}.lean"] = body + "end PrimeFactorUnimodality\n"
        previous_module = module_name
    modules["PrimePrefixes.lean"] = (
        "import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated."
        f"{previous_module}\n\n"
        "/-! Facade for the generated prime-prefix chain through 1151. -/\n"
    )
    return modules


def fixed_weight_sum_modules() -> dict[str, str]:
    """Generate chained fixed-point certificates at all required endpoints."""
    endpoints, values = fixed_weight_values()

    modules: dict[str, str] = {}
    previous_module = ""
    previous_endpoint = 0
    for part_index, offset in enumerate(range(0, len(endpoints), 10), start=1):
        module_name = f"FixedWeightSums.Part{part_index:02d}"
        if part_index == 1:
            imports = """import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.FiniteCertificates.CertifiedWeightSum
"""
        else:
            imports = (
                "import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated."
                f"{previous_module}\n"
            )
        body = f"""{imports}

/-! Generated fixed-point reciprocal-weight certificates, segment {part_index}. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

"""
        if part_index == 1:
            body += """theorem fixedWeightSumsAt0 :
    fixedWeightSums 1000000000 0 = (0, 0) := by
  rfl

"""
        for endpoint in endpoints[offset : offset + 10]:
            count = endpoint - previous_endpoint
            lower, upper = values[endpoint]
            body += f"""set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt{endpoint} :
    fixedWeightSums {FIXED_WEIGHT_SCALE} {endpoint} = ({lower}, {upper}) := by
  rw [show {endpoint} = {previous_endpoint} + {count} by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt{previous_endpoint}]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

"""
            previous_endpoint = endpoint
        body += "end PrimeFactorUnimodality\n"
        modules[f"FixedWeightSums/Part{part_index:02d}.lean"] = body
        previous_module = module_name
    modules["FixedWeightSums.lean"] = (
        "import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated."
        f"{previous_module}\n\n"
        "/-! Facade for generated fixed-point reciprocal-weight certificates. -/\n"
    )
    return modules


def module(degree: int, data: tuple[int, int, int, int]) -> str:
    descent, descent_next, ascent, ascent_next = data
    k = degree + 1
    counting_cutoff = primes_below(200)[degree - 1] + 1
    body = f"""import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row{descent}
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row{ascent}
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = {k}`. -/

namespace PrimeFactorUnimodality

"""
    body += consecutive(descent, descent_next) + consecutive(ascent, ascent_next)
    body += f"""set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = {k}`. -/
def k{k}ExplicitRatioValley : ExplicitRatioValleyCertificate {degree - 1} where
  descentPrime := {descent}
  descentNext := {descent_next}
  ascentPrime := {ascent}
  ascentNext := {ascent_next}
  descentConsecutive := consecutive{descent}_{descent_next}
  ascentConsecutive := consecutive{ascent}_{ascent_next}
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show {degree} ≤ Nat.primeCounting' {counting_cutoff} by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show {degree} ≤ Nat.primeCounting' {counting_cutoff} by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
"""
    body += ratio_proof(descent, degree)
    body += "  ascentRatio := by\n" + ratio_proof(ascent, degree)
    body += f"""
theorem k{k}PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity {k}) := by
  simpa using k{k}ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
"""
    return body


def positive_k3_module() -> str:
    primes = primes_below(90)
    cases: list[str] = []
    for index in range(2, 23):
        p = primes[index]
        q = primes[index + 1]
        cases.append(f"""  case «{index}» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 {index} (by omega)).2
    have hp : primeAt {index} = {p} := by
      rw [← show Nat.primeCounting' {p} = {index} by decide]
      exact primeAt_primeCounting' {p} (by decide)
    have hq : primeAt ({index} + 1) = {q} := by
      norm_num
      rw [← show Nat.primeCounting' {q} = {index + 1} by decide]
      exact primeAt_primeCounting' {q} (by decide)
    rw [hp, show primeGap {index} = {q - p} by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow{p}_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix{p}
        primePrefix{p}_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix{p} (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix{p} 2 (by omega),
      numericalRow89_{p}]
    norm_num
""")
    return (
        """import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row89
import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence

set_option autoImplicit false

/-! Generated exact weak-descent checks for the finite beginning of `d₃`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- The generated exact arithmetic checks all initial degree-two ratios.
theorem k3PrimeFactorDensity_finite_descent
    (i : Nat) (hLower : 2 ≤ i) (hUpper : i < 23) :
    primeFactorDensity 3 (i + 1) ≤ primeFactorDensity 3 i := by
  interval_cases i
"""
        + "".join(cases)
        + "\nend PrimeFactorUnimodality\n"
    )


def write_if_changed(path: Path, content: str) -> None:
    forbidden = ("native_decide", "ofReduceBool", "sorry", "admit")
    present = [token for token in forbidden if token in content]
    if present:
        raise ValueError(f"forbidden proof token in {path}: {', '.join(present)}")
    if path.suffix == ".lean" and len(content.splitlines()) > 900:
        raise ValueError(f"generated Lean module exceeds 900 lines: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    helper_generated = root / "PrimeFactorUnimodality/Helpers/FiniteCertificates/Generated"
    proof_generated = root / "PrimeFactorUnimodality/Proof/FiniteRange/Generated"
    for old in proof_generated.glob("K*.lean"):
        if old.stem[1:].isdigit():
            old.unlink()
    for relative, content in prefix_modules().items():
        write_if_changed(helper_generated / relative, content)
    for relative, content in fixed_weight_sum_modules().items():
        write_if_changed(helper_generated / relative, content)
    write_if_changed(proof_generated / "MediumWeightBounds.lean", medium_weight_bounds_module())
    for p, degree in MAX_DEGREES.items():
        for relative, content in row_modules(p, degree).items():
            write_if_changed(helper_generated / relative, content)
    write_if_changed(
        root / "PrimeFactorUnimodality/Proof/Unimodality/Generated/PositiveK3.lean",
        positive_k3_module(),
    )
    for degree, data in CASES.items():
        k = degree + 1
        name = f"K{k:02d}"
        write_if_changed(proof_generated / f"{name}.lean", module(degree, data))


if __name__ == "__main__":
    main()
