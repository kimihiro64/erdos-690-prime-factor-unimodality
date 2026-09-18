import Mathlib.NumberTheory.Bertrand
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

set_option autoImplicit false

/-! # A Bertrand bound for the prime immediately below a cutoff -/

namespace PrimeFactorUnimodality

/-- A predecessor prime below any cutoff strictly beyond `2 * base` is larger
than `base`.  Unlike the half-cutoff variant below, this does not require the
cutoff itself to be composite. -/
theorem primeAt_primeCounting_sub_one_gt_of_two_mul_lt
    {base cutoff : Nat} (base_pos : 0 < base) (two_mul_lt : 2 * base < cutoff) :
    base < primeAt (Nat.primeCounting' cutoff - 1) := by
  obtain ⟨p, p_prime, base_lt_p, p_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul base (Nat.ne_of_gt base_pos)
  exact base_lt_p.trans_le
    (prime_le_primeAt_primeCounting'_sub_one p_prime (p_le.trans_lt two_mul_lt))

/-- If a cutoff at least four is composite, its predecessor prime is strictly
larger than half the cutoff. -/
theorem primeAt_primeCounting_sub_one_gt_half
    {cutoff : Nat} (cutoff_ge_four : 4 ≤ cutoff) (cutoff_not_prime : ¬cutoff.Prime) :
    cutoff / 2 < primeAt (Nat.primeCounting' cutoff - 1) := by
  let half := cutoff / 2
  have half_ne_zero : half ≠ 0 := by
    dsimp only [half]
    omega
  rcases Nat.exists_prime_lt_and_le_two_mul half half_ne_zero with
    ⟨p, p_prime, half_lt_p, p_le⟩
  have p_lt_cutoff : p < cutoff := by
    have two_half_le : 2 * half ≤ cutoff := by
      dsimp only [half]
      omega
    have p_le_cutoff : p ≤ cutoff := p_le.trans two_half_le
    exact p_le_cutoff.lt_of_ne (fun p_eq => cutoff_not_prime (p_eq ▸ p_prime))
  exact half_lt_p.trans_le
    (prime_le_primeAt_primeCounting'_sub_one p_prime p_lt_cutoff)

end PrimeFactorUnimodality
