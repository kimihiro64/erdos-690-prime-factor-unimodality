import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

set_option autoImplicit false

/-! # Initial segments of the canonical prime list -/

namespace PrimeFactorUnimodality

/-- Passing to the next indexed prime appends the old endpoint to the sorted
list of smaller primes. -/
theorem primesBelow_primeAt_succ_append (i : Nat) :
    primesBelow (primeAt (i + 1)) = primesBelow (primeAt i) ++ [primeAt i] := by
  apply List.Perm.eq_of_sortedLE
    (List.Pairwise.sortedLE (primesBelow_pairwise_le (primeAt (i + 1))))
  · apply List.Pairwise.sortedLE
    rw [List.pairwise_append]
    refine ⟨primesBelow_pairwise_le (primeAt i), by simp, ?_⟩
    intro p hp q hq
    simp only [List.mem_singleton] at hq
    subst q
    exact (primesBelow_entries (primeAt i) p hp).2.le
  · exact (primesBelow_primeAt_succ_perm i).trans (List.perm_append_singleton _ _).symm

/-- The first `n` primes below a later indexed prime are exactly the primes
below the `n`-th prime. -/
theorem take_primesBelow_primeAt (n i : Nat) (hni : n ≤ i) :
    (primesBelow (primeAt i)).take n = primesBelow (primeAt n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hni
  induction d with
  | zero =>
      rw [Nat.add_zero, List.take_eq_self_iff]
      exact (primesBelow_primeAt_length n).le
  | succ d ih =>
      rw [Nat.add_succ, primesBelow_primeAt_succ_append,
        List.take_append_of_le_length]
      · exact ih (Nat.le_add_right n d)
      · rw [primesBelow_primeAt_length]
        omega

/-- Initial segments below a concrete prime can be transferred to the indexed
prime at the requested length. -/
theorem take_primesBelow_of_prime (p n : Nat) (hp : p.Prime)
    (hn : n ≤ Nat.primeCounting' p) :
    (primesBelow p).take n = primesBelow (primeAt n) := by
  rw [← primeAt_primeCounting' p hp]
  exact take_primesBelow_primeAt n (Nat.primeCounting' p) hn

end PrimeFactorUnimodality
