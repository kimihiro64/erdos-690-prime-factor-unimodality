import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 06 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3593 : Nat.Prime 3593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3593 3592 1 3 [2, 2, 2, 449]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 3593) ^ 1796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1796 : ZMod 3593)
      decide
    · change IsUnit ((3 : ZMod 3593) ^ 1796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1796 : ZMod 3593)
      decide
    · change IsUnit ((3 : ZMod 3593) ^ 1796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1796 : ZMod 3593)
      decide
    · change IsUnit ((3 : ZMod 3593) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2072 : ZMod 3593)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3607 : Nat.Prime 3607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3607 3606 1 5 [2, 3, 601]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 3607) ^ 1803 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1803 : ZMod 3607)
      decide
    · change IsUnit ((5 : ZMod 3607) ^ 1202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3140 : ZMod 3607)
      decide
    · change IsUnit ((5 : ZMod 3607) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3417 : ZMod 3607)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3613 : Nat.Prime 3613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3613 3612 1 2 [2, 2, 3, 7, 43]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3613) ^ 1806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1806 : ZMod 3613)
      decide
    · change IsUnit ((2 : ZMod 3613) ^ 1806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1806 : ZMod 3613)
      decide
    · change IsUnit ((2 : ZMod 3613) ^ 1204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (558 : ZMod 3613)
      decide
    · change IsUnit ((2 : ZMod 3613) ^ 516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (636 : ZMod 3613)
      decide
    · change IsUnit ((2 : ZMod 3613) ^ 84 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3172 : ZMod 3613)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3617 : Nat.Prime 3617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3617 3616 1 3 [2, 2, 2, 2, 2, 113]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 3617) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1808 : ZMod 3617)
      decide
    · change IsUnit ((3 : ZMod 3617) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1808 : ZMod 3617)
      decide
    · change IsUnit ((3 : ZMod 3617) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1808 : ZMod 3617)
      decide
    · change IsUnit ((3 : ZMod 3617) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1808 : ZMod 3617)
      decide
    · change IsUnit ((3 : ZMod 3617) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1808 : ZMod 3617)
      decide
    · change IsUnit ((3 : ZMod 3617) ^ 32 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3522 : ZMod 3617)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3623 : Nat.Prime 3623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3623 3622 1 5 [2, 1811]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((5 : ZMod 3623) ^ 1811 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1811 : ZMod 3623)
      decide
    · change IsUnit ((5 : ZMod 3623) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (151 : ZMod 3623)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3631 : Nat.Prime 3631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3631 3630 1 15 [2, 3, 5, 11, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((15 : ZMod 3631) ^ 1815 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1815 : ZMod 3631)
      decide
    · change IsUnit ((15 : ZMod 3631) ^ 1210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2532 : ZMod 3631)
      decide
    · change IsUnit ((15 : ZMod 3631) ^ 726 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3135 : ZMod 3631)
      decide
    · change IsUnit ((15 : ZMod 3631) ^ 330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (216 : ZMod 3631)
      decide
    · change IsUnit ((15 : ZMod 3631) ^ 330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (216 : ZMod 3631)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3637 : Nat.Prime 3637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3637 3636 1 2 [2, 2, 3, 3, 101]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3637) ^ 1818 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1818 : ZMod 3637)
      decide
    · change IsUnit ((2 : ZMod 3637) ^ 1818 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1818 : ZMod 3637)
      decide
    · change IsUnit ((2 : ZMod 3637) ^ 1212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2656 : ZMod 3637)
      decide
    · change IsUnit ((2 : ZMod 3637) ^ 1212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2656 : ZMod 3637)
      decide
    · change IsUnit ((2 : ZMod 3637) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (840 : ZMod 3637)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3643 : Nat.Prime 3643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3643 3642 1 2 [2, 3, 607]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3643) ^ 1821 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1821 : ZMod 3643)
      decide
    · change IsUnit ((2 : ZMod 3643) ^ 1214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1073 : ZMod 3643)
      decide
    · change IsUnit ((2 : ZMod 3643) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1330 : ZMod 3643)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by exact lowPrime_3593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by exact lowPrime_3607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by exact lowPrime_3613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by exact lowPrime_3617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by exact lowPrime_3623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by exact lowPrime_3631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by exact lowPrime_3637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by exact lowPrime_3643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part06_chain :
    DusartPrimeRowsChain 3583 3643 dusartPrimeRows_3275_3802_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num
