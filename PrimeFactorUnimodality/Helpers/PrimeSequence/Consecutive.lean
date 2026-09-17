import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false

/-!
# Certificates for consecutive primes
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- A fully explicit certificate that `p` and `q` are consecutive primes. -/
structure ConsecutivePrimes (p q : Nat) : Prop where
  left_prime : p.Prime
  right_prime : q.Prime
  left_lt_right : p < q
  no_prime_between : ∀ m, p < m → m < q → ¬ m.Prime

theorem primeAt_primeCounting' (p : Nat) (hp : p.Prime) :
    primeAt (Nat.primeCounting' p) = p := by
  exact Nat.nth_count hp

theorem ConsecutivePrimes.next_primeAt {p q : Nat} (h : ConsecutivePrimes p q) :
    primeAt (Nat.primeCounting' p + 1) = q := by
  have hAt : primeAt (Nat.primeCounting' p) = p :=
    primeAt_primeCounting' p h.left_prime
  have hLower : p < primeAt (Nat.primeCounting' p + 1) := by
    calc
      p = primeAt (Nat.primeCounting' p) := hAt.symm
      _ < primeAt (Nat.primeCounting' p + 1) :=
        primeAt_strictMono (Nat.lt_succ_self _)
  have hUpper : primeAt (Nat.primeCounting' p + 1) ≤ q := by
    apply (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime h.right_prime).2
    rw [show Nat.nth Nat.Prime (Nat.primeCounting' p) = p from hAt]
    exact h.left_lt_right
  rcases hUpper.eq_or_lt with hEq | hLt
  · exact hEq
  · exact False.elim
      (h.no_prime_between (primeAt (Nat.primeCounting' p + 1)) hLower hLt
        (prime_primeAt _))

theorem ConsecutivePrimes.primeGap_eq {p q : Nat} (h : ConsecutivePrimes p q) :
    primeGap (Nat.primeCounting' p) = q - p := by
  rw [primeGap, h.next_primeAt, primeAt_primeCounting' p h.left_prime]

theorem ConsecutivePrimes.natPrimesBelow_eq_insert {p q : Nat}
    (h : ConsecutivePrimes p q) :
    Nat.primesBelow q = insert p (Nat.primesBelow p) := by
  ext r
  simp only [Nat.mem_primesBelow, Finset.mem_insert]
  constructor
  · rintro ⟨hrq, hrPrime⟩
    have hrle : r ≤ p := by
      by_contra hnle
      exact h.no_prime_between r (Nat.lt_of_not_ge hnle) hrq hrPrime
    exact hrle.eq_or_lt.elim (fun heq => Or.inl heq)
      (fun hlt => Or.inr ⟨hlt, hrPrime⟩)
  · rintro (rfl | ⟨hrp, hrPrime⟩)
    · exact ⟨h.left_lt_right, h.left_prime⟩
    · exact ⟨hrp.trans h.left_lt_right, hrPrime⟩

theorem ConsecutivePrimes.primesBelow_perm {p q : Nat}
    (h : ConsecutivePrimes p q) :
    (primesBelow q).Perm (p :: primesBelow p) := by
  apply Multiset.coe_eq_coe.mp
  change (↑((Nat.primesBelow q).sort (fun a b => a ≤ b)) : Multiset Nat) =
    p ::ₘ ↑((Nat.primesBelow p).sort (fun a b => a ≤ b))
  simp only [Finset.sort_eq]
  rw [h.natPrimesBelow_eq_insert, Finset.insert_val]
  simp [Nat.notMem_primesBelow]

theorem primeCounting'_lt_of_prime_lt {p q : Nat}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Nat.primeCounting' p < Nat.primeCounting' q := by
  apply (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).1
  change Nat.nth Nat.Prime (Nat.count Nat.Prime p) <
    Nat.nth Nat.Prime (Nat.count Nat.Prime q)
  rw [Nat.nth_count hp, Nat.nth_count hq]
  exact hpq

end

end PrimeFactorUnimodality
