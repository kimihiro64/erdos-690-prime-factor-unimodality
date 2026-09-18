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

/-- Adjacent entries of the canonical indexed prime sequence are consecutive
primes in the order-theoretic sense. -/
theorem consecutivePrimes_primeAt (i : Nat) :
    ConsecutivePrimes (primeAt i) (primeAt (i + 1)) := by
  refine ⟨prime_primeAt i, prime_primeAt (i + 1),
    primeAt_strictMono (Nat.lt_succ_self i), ?_⟩
  intro m left right mPrime
  have nextLe : primeAt (i + 1) ≤ m := by
    apply (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime mPrime).2
    simpa only [primeAt] using left
  omega

theorem primeAt_primeCounting' (p : Nat) (hp : p.Prime) :
    primeAt (Nat.primeCounting' p) = p := by
  exact Nat.nth_count hp

/-- A prime larger than two and the indexed prime immediately before it form
a consecutive pair. -/
theorem consecutivePrimes_predecessor {q : Nat} (qPrime : q.Prime)
    (q_gt_two : 2 < q) :
    ConsecutivePrimes (primeAt (Nat.primeCounting' q - 1)) q := by
  have countPos : 0 < Nat.primeCounting' q := by
    rw [Nat.pos_iff_ne_zero, ne_eq, Nat.primeCounting'_eq_zero_iff]
    omega
  have countStep : Nat.primeCounting' q - 1 + 1 = Nat.primeCounting' q := by
    omega
  have adjacent := consecutivePrimes_primeAt (Nat.primeCounting' q - 1)
  simpa only [countStep, primeAt_primeCounting' q qPrime] using adjacent

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

/-- Any prime below a cutoff is at most the final indexed prime below that
cutoff. -/
theorem prime_le_primeAt_primeCounting'_sub_one {p cutoff : Nat}
    (p_prime : p.Prime) (p_lt_cutoff : p < cutoff) :
    p ≤ primeAt (Nat.primeCounting' cutoff - 1) := by
  have p_lt_next : p < primeAt (Nat.primeCounting' cutoff) :=
    p_lt_cutoff.trans_le
      (Nat.le_nth_count Nat.infinite_setOfPred_prime cutoff)
  have count_lt' := primeCounting'_lt_of_prime_lt p_prime
    (prime_primeAt (Nat.primeCounting' cutoff)) p_lt_next
  have count_lt : Nat.primeCounting' p < Nat.primeCounting' cutoff := by
    simpa [primeAt] using count_lt'
  have index_le : Nat.primeCounting' p ≤ Nat.primeCounting' cutoff - 1 := by
    omega
  rw [← primeAt_primeCounting' p p_prime]
  exact primeAt_strictMono.monotone index_le

/-- Two primes at distance two, with the lower one larger than two, are
consecutive. -/
theorem consecutivePrimes_of_add_two {p : Nat} (p_prime : p.Prime)
    (next_prime : (p + 2).Prime) (p_gt_two : 2 < p) :
    ConsecutivePrimes p (p + 2) := by
  refine ⟨p_prime, next_prime, by omega, ?_⟩
  intro m left right
  have m_eq : m = p + 1 := by omega
  subst m
  have p_mod_two : p % 2 = 1 :=
    (p_prime.eq_two_or_odd).resolve_left (by omega)
  refine Nat.not_prime_of_dvd_of_lt (m := 2) ?_ (by norm_num) (by omega)
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- A closed interval containing no primes forces a correspondingly large gap
in the indexed prime sequence.  No primality certificate for either endpoint
of the composite interval is needed. -/
theorem primeGap_ge_of_not_prime_Icc {lower upper : Nat} (lower_gt_two : 2 < lower)
    (lower_le_upper : lower ≤ upper)
    (composite : ∀ n, lower ≤ n → n ≤ upper → ¬n.Prime) :
    upper - lower + 2 ≤ primeGap (Nat.primeCounting' lower - 1) := by
  let count := Nat.primeCounting' lower
  change upper - lower + 2 ≤ primeGap (count - 1)
  have count_ne_zero : count ≠ 0 := by
    change Nat.primeCounting' lower ≠ 0
    rw [Nat.primeCounting', Nat.count_ne_iff_exists]
    exact ⟨2, lower_gt_two, Nat.prime_two⟩
  have count_pos : 0 < count := Nat.pos_of_ne_zero count_ne_zero
  have previous_lt_lower : primeAt (count - 1) < lower := by
    apply Nat.nth_lt_of_lt_count
    change count - 1 < Nat.primeCounting' lower
    simpa only [count] using Nat.sub_lt (Nat.zero_lt_of_lt count_pos) (by norm_num : 0 < 1)
  have lower_le_next : lower ≤ primeAt count := by
    exact Nat.le_nth_count Nat.infinite_setOfPred_prime lower
  have upper_lt_next : upper < primeAt count := by
    by_contra not_lt
    exact composite (primeAt count) lower_le_next (Nat.le_of_not_gt not_lt)
      (prime_primeAt count)
  have successor_index : count - 1 + 1 = count := Nat.sub_add_cancel count_pos
  rw [primeGap, successor_index]
  omega

/-- The indexed predecessor selected by `primeCounting' cutoff - 1` lies
strictly below any cutoff larger than two. -/
theorem primeAt_primeCounting'_sub_one_lt {cutoff : Nat} (cutoff_gt_two : 2 < cutoff) :
    primeAt (Nat.primeCounting' cutoff - 1) < cutoff := by
  have count_pos : 0 < Nat.primeCounting' cutoff := by
    apply Nat.pos_of_ne_zero
    rw [Nat.primeCounting', Nat.count_ne_iff_exists]
    exact ⟨2, cutoff_gt_two, Nat.prime_two⟩
  apply Nat.nth_lt_of_lt_count
  change Nat.primeCounting' cutoff - 1 < Nat.primeCounting' cutoff
  omega

end

end PrimeFactorUnimodality
