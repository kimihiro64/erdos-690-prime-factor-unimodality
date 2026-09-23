"""Port the exact locked PrimeCert multiplicity API to the pinned Mathlib.

The congruence decomposition needs a nonzero modulus: current multiplicity
at zero is zero, so its old zero-modulus statement is false. Its sole caller
already proves that premise. Sieve correctness statements are unchanged.
Validate all original or already-ported sources before writing anything.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Final

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.patch_pnt_compat import git_output, patched_source, validate_current  # noqa: E402

REVISION: Final = "916ee9c35a57af128d5089a69172415051e700ca"
PREFIX: Final = "PrimeCert/"
OLD_CONGRUENCE: Final = """public theorem Nat.modEq_iff_forall_prime_dvd {a b n : ℕ} :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] := by
  by_cases hn₀ : n = 0
  · subst hn₀
    simp_rw [modEq_zero_iff, dvd_zero, true_imp_iff]
    constructor
    · rintro rfl; exact fun _ _ ↦ by rfl
    · intro h
      obtain ⟨p, hbp, hp⟩ := exists_infinite_primes (a + b + 1)
      specialize h p hp
      rw [multiplicity_zero, pow_one] at h
      exact h.eq_of_lt_of_lt (by linarith) (by linarith)
  · conv_lhs => rw [← prod_factorization_pow_eq_self hn₀]
    rw [Finsupp.prod, modEq_finset_prod_iff]
    · simp_rw [support_factorization, mem_primeFactors_of_ne_zero hn₀, and_comm, and_imp]
      refine forall_congr' fun p ↦ imp_congr_right fun hpn ↦ imp_congr_right fun hp ↦ ?_
      rw [multiplicity_eq_factorization hp hn₀]
    · grind [support_factorization, coprime_pow_primes, Set.Pairwise]"""  # noqa: RUF001 (Lean notation)
NEW_CONGRUENCE: Final = """public theorem Nat.modEq_iff_forall_prime_dvd {a b n : ℕ} (hn₀ : n ≠ 0) :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] := by
  conv_lhs => rw [← prod_factorization_pow_eq_self hn₀]
  rw [Finsupp.prod, modEq_finset_prod_iff]
  · simp_rw [support_factorization, mem_primeFactors_of_ne_zero hn₀, and_comm, and_imp]
    refine forall_congr' fun p ↦ imp_congr_right fun hpn ↦ imp_congr_right fun hp ↦ ?_
    rw [multiplicity_eq_factorization hp]
  · grind [support_factorization, coprime_pow_primes, Set.Pairwise]"""  # noqa: RUF001 (Lean notation)
CHANGES: Final[dict[str, tuple[tuple[str, str], ...]]] = {
    "ForMathlib.lean": (
        (OLD_CONGRUENCE, NEW_CONGRUENCE),
        (
            "multiplicity_eq_factorization hq hqn₀, multiplicity_eq_factorization hq hx₀,",
            "multiplicity_eq_factorization hq, multiplicity_eq_factorization hq,",
        ),
        ("multiplicity_eq_zero.mpr hqn", "multiplicity_eq_zero_of_not_dvd hqn"),
    ),
    "Pocklington.lean": (
        ("rw [Nat.modEq_iff_forall_prime_dvd]", "rw [Nat.modEq_iff_forall_prime_dvd hf₀]"),
        (
            "Nat.multiplicity_eq_factorization hq hf₀, "
            "Nat.multiplicity_eq_factorization hq (by grind)",
            "Nat.multiplicity_eq_factorization hq, Nat.multiplicity_eq_factorization hq",
        ),
    ),
}


def apply_patches(root: Path, *, check: bool = False) -> int:
    """Apply only the reviewed ports, preserving unrelated edits and build caches."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    locked = next(p for p in manifest["packages"] if p["name"] == "PrimeCert")
    if locked["rev"] != REVISION:
        raise ValueError("PrimeCert lock revision changed; review compatibility patches first")
    package = root / ".lake/packages/PrimeCert"
    if git_output(package, "rev-parse", "HEAD").strip() != REVISION:
        raise ValueError("PrimeCert checkout does not match the reviewed revision")
    pending: list[tuple[Path, str]] = []
    for relative, replacements in CHANGES.items():
        relative = PREFIX + relative
        path = package / relative
        if path.is_symlink() or not path.resolve().is_relative_to(package.resolve()):
            raise ValueError(f"unsafe source path: {relative}")
        original = git_output(package, "show", f"{REVISION}:{relative}")
        patched = patched_source(original, replacements)
        if validate_current(path.read_text(), original, patched):
            pending.append((path, patched))
    if check and pending:
        raise ValueError(f"{len(pending)} PrimeCert compatibility ports have not been applied")
    for path, patched in pending:
        path.write_text(patched)
    return len(pending)


def main() -> None:
    """Apply the same exact source port locally and in every Lean CI job."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify without modifying files")
    args = parser.parse_args()
    changed = apply_patches(ROOT, check=args.check)
    print(f"PrimeCert Lean 4.34 compatibility: {changed} files updated ({len(CHANGES)} verified)")


if __name__ == "__main__":
    main()
