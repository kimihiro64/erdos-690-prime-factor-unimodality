import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false

/-! # A finite average-gap principle -/

namespace PrimeFactorUnimodality

/-- A lower bound on the number of primes through `upper` gives an upper
bound for the corresponding zero-based indexed prime. -/
theorem primeAt_le_of_succ_le_primeCounting' {i upper : Nat}
    (hcount : i + 1 ≤ Nat.primeCounting' (upper + 1)) :
    primeAt i ≤ upper := by
  have hlt : i < Nat.primeCounting' (upper + 1) := by omega
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := upper + 1) hlt
  simpa only [primeAt] using Nat.lt_add_one_iff.mp this

/-- Convenient predecessor-index form of `primeAt_le_of_succ_le_primeCounting'`. -/
theorem primeAt_sub_one_le_of_le_primeCounting'
    {count upper : Nat} (count_pos : 0 < count)
    (hcount : count ≤ Nat.primeCounting' (upper + 1)) :
    primeAt (count - 1) ≤ upper := by
  apply primeAt_le_of_succ_le_primeCounting'
  simpa only [Nat.sub_add_cancel count_pos] using hcount

/-- Every indexed prime whose index is still below `π(upper)` is at most
`upper`.  This small bridge is useful when an average-gap argument returns an
offset from `π(lower)`. -/
theorem primeAt_primeCounting_add_le_upper {lower upper i : Nat}
    (hi : i < Nat.primeCounting upper - Nat.primeCounting lower) :
    primeAt (Nat.primeCounting lower + i) ≤ upper := by
  have index_lt : Nat.primeCounting lower + i < Nat.primeCounting upper := by
    omega
  have nth_lt : primeAt (Nat.primeCounting lower + i) < upper + 1 := by
    apply Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := upper + 1)
    simpa only [Nat.primeCounting, Nat.primeCounting'] using index_lt
  omega

theorem interval_short_of_count_lower
    {width count target bound : Nat}
    (countLower : target + 1 ≤ count)
    (widthBound : width < target * bound) :
    width < (count - 1) * bound := by
  exact widthBound.trans_le
    (Nat.mul_le_mul_right bound (by omega : target ≤ count - 1))

/-- If the span of `N` successive steps is less than `N * bound`, one of the
steps is strictly less than `bound`.  This natural-number formulation avoids
division and is the exact pigeonhole argument needed for later prime gaps. -/
theorem exists_step_lt_of_span_lt_mul
    (f : Nat → Nat) (monotone : Monotone f) (N bound : Nat)
    (span : f N - f 0 < N * bound) :
    ∃ i < N, f (i + 1) - f i < bound := by
  by_contra noSmall
  push Not at noSmall
  have growth : ∀ n ≤ N, f 0 + n * bound ≤ f n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnN : n ≤ N := n.le_succ.trans hn
        have step := noSmall n (by omega)
        have monoStep : f n ≤ f (n + 1) := monotone (by omega)
        have addStep : f n + bound ≤ f (n + 1) := by omega
        have ih' := ih (by omega)
        calc
          f 0 + (n + 1) * bound = (f 0 + n * bound) + bound := by ring
          _ ≤ f n + bound := Nat.add_le_add_right ih' bound
          _ ≤ f (n + 1) := addStep
  have total := growth N le_rfl
  have base_le : f 0 ≤ f N := monotone (Nat.zero_le N)
  omega

/-- Among `N+1` indexed primes lying in an interval narrower than
`N * bound`, two adjacent primes have gap below `bound`. -/
theorem exists_primeGap_lt_of_indexed_span
    (start N lower upper bound : Nat)
    (lower_le_first : lower ≤ primeAt start)
    (last_le_upper : primeAt (start + N) ≤ upper)
    (interval_short : upper - lower < N * bound) :
    ∃ i < N, primeGap (start + i) < bound := by
  have span : primeAt (start + N) - primeAt start < N * bound := by
    have endpoints : primeAt (start + N) - primeAt start ≤ upper - lower := by
      omega
    exact endpoints.trans_lt interval_short
  obtain ⟨i, hi, hgap⟩ := exists_step_lt_of_span_lt_mul
    (fun j ↦ primeAt (start + j))
    (primeAt_strictMono.monotone.comp (monotone_const.add monotone_id))
    N bound (by simpa using span)
  refine ⟨i, hi, ?_⟩
  simpa only [primeGap, add_assoc] using hgap

/-- Prime-count information in `(lower, upper]` supplies the indexed span
required by `exists_primeGap_lt_of_indexed_span`. -/
theorem exists_primeGap_lt_of_count
    (lower upper bound : Nat)
    (two_le_count :
      2 ≤ Nat.primeCounting upper - Nat.primeCounting lower)
    (interval_short :
      upper - lower <
        (Nat.primeCounting upper - Nat.primeCounting lower - 1) * bound) :
    ∃ i < Nat.primeCounting upper - Nat.primeCounting lower - 1,
      primeGap (Nat.primeCounting lower + i) < bound := by
  let count := Nat.primeCounting upper - Nat.primeCounting lower
  let start := Nat.primeCounting lower
  have count_pos : 0 < count := by omega
  have counts_lt : Nat.primeCounting lower < Nat.primeCounting upper := by
    exact Nat.sub_pos_iff_lt.mp (by simpa only [count] using count_pos)
  have counts_le : Nat.primeCounting lower ≤ Nat.primeCounting upper :=
    counts_lt.le
  have index_eq : start + (count - 1) = Nat.primeCounting upper - 1 := by
    dsimp only [start, count]
    omega
  have lower_le_first : lower ≤ primeAt start := by
    dsimp only [start, Nat.primeCounting]
    exact (by omega : lower ≤ lower + 1).trans
      (Nat.le_nth_count Nat.infinite_setOfPred_prime (lower + 1))
  have last_le_upper : primeAt (start + (count - 1)) ≤ upper := by
    rw [index_eq]
    have index_lt : Nat.primeCounting upper - 1 < Nat.primeCounting upper := by
      omega
    have index_lt' :
        Nat.primeCounting upper - 1 < Nat.count Nat.Prime (upper + 1) := by
      simpa only [Nat.primeCounting, Nat.primeCounting'] using index_lt
    exact Nat.lt_succ_iff.mp
      (Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := upper + 1)
        index_lt')
  exact exists_primeGap_lt_of_indexed_span start (count - 1) lower upper bound
    lower_le_first last_le_upper (by simpa only [count] using interval_short)

end PrimeFactorUnimodality
