import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 68 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7561 : Nat.Prime 7561 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7561 7560 1 13 [2, 2, 2, 3, 3, 3, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((13 : ZMod 7561) ^ 3780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3780 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 3780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3780 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 3780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3780 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 2520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2087 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 2520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2087 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 2520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2087 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 1512 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (278 : ZMod 7561)
      decide
    · change IsUnit ((13 : ZMod 7561) ^ 1080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3561 : ZMod 7561)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7573 : Nat.Prime 7573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7573 7572 1 2 [2, 2, 3, 631]
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
    · change IsUnit ((2 : ZMod 7573) ^ 3786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3786 : ZMod 7573)
      decide
    · change IsUnit ((2 : ZMod 7573) ^ 3786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3786 : ZMod 7573)
      decide
    · change IsUnit ((2 : ZMod 7573) ^ 2524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5734 : ZMod 7573)
      decide
    · change IsUnit ((2 : ZMod 7573) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5646 : ZMod 7573)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7577 : Nat.Prime 7577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7577 7576 1 3 [2, 2, 2, 947]
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
    · change IsUnit ((3 : ZMod 7577) ^ 3788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3788 : ZMod 7577)
      decide
    · change IsUnit ((3 : ZMod 7577) ^ 3788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3788 : ZMod 7577)
      decide
    · change IsUnit ((3 : ZMod 7577) ^ 3788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3788 : ZMod 7577)
      decide
    · change IsUnit ((3 : ZMod 7577) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4351 : ZMod 7577)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7583 : Nat.Prime 7583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7583 7582 1 5 [2, 17, 223]
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
    · change IsUnit ((5 : ZMod 7583) ^ 3791 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3791 : ZMod 7583)
      decide
    · change IsUnit ((5 : ZMod 7583) ^ 446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1199 : ZMod 7583)
      decide
    · change IsUnit ((5 : ZMod 7583) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2873 : ZMod 7583)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7589 : Nat.Prime 7589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7589 7588 1 2 [2, 2, 7, 271]
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
    · change IsUnit ((2 : ZMod 7589) ^ 3794 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3794 : ZMod 7589)
      decide
    · change IsUnit ((2 : ZMod 7589) ^ 3794 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3794 : ZMod 7589)
      decide
    · change IsUnit ((2 : ZMod 7589) ^ 1084 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4982 : ZMod 7589)
      decide
    · change IsUnit ((2 : ZMod 7589) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (964 : ZMod 7589)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7591 : Nat.Prime 7591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7591 7590 1 6 [2, 3, 5, 11, 23]
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
    · change IsUnit ((6 : ZMod 7591) ^ 3795 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3795 : ZMod 7591)
      decide
    · change IsUnit ((6 : ZMod 7591) ^ 2530 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5878 : ZMod 7591)
      decide
    · change IsUnit ((6 : ZMod 7591) ^ 1518 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6259 : ZMod 7591)
      decide
    · change IsUnit ((6 : ZMod 7591) ^ 690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5417 : ZMod 7591)
      decide
    · change IsUnit ((6 : ZMod 7591) ^ 330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1949 : ZMod 7591)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7603 : Nat.Prime 7603 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7603 7602 1 2 [2, 3, 7, 181]
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
    · change IsUnit ((2 : ZMod 7603) ^ 3801 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3801 : ZMod 7603)
      decide
    · change IsUnit ((2 : ZMod 7603) ^ 2534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3232 : ZMod 7603)
      decide
    · change IsUnit ((2 : ZMod 7603) ^ 1086 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2473 : ZMod 7603)
      decide
    · change IsUnit ((2 : ZMod 7603) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (255 : ZMod 7603)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7607 : Nat.Prime 7607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7607 7606 1 5 [2, 3803]
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
    · change IsUnit ((5 : ZMod 7607) ^ 3803 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3803 : ZMod 7607)
      decide
    · change IsUnit ((5 : ZMod 7607) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (317 : ZMod 7607)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by exact lowPrime_7561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by exact lowPrime_7573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by exact lowPrime_7577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by exact lowPrime_7583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by exact lowPrime_7589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by exact lowPrime_7591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by exact lowPrime_7603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by exact lowPrime_7607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part04_chain :
    DusartPrimeRowsChain 7559 7607 dusartPrimeRows_7333_7716_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num
