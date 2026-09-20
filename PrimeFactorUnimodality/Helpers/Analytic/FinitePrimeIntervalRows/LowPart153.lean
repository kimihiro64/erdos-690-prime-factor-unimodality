import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 153 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13457 : Nat.Prime 13457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13457 13456 1 3 [2, 2, 2, 2, 29, 29]
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
    · change IsUnit ((3 : ZMod 13457) ^ 6728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6728 : ZMod 13457)
      decide
    · change IsUnit ((3 : ZMod 13457) ^ 6728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6728 : ZMod 13457)
      decide
    · change IsUnit ((3 : ZMod 13457) ^ 6728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6728 : ZMod 13457)
      decide
    · change IsUnit ((3 : ZMod 13457) ^ 6728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6728 : ZMod 13457)
      decide
    · change IsUnit ((3 : ZMod 13457) ^ 464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3592 : ZMod 13457)
      decide
    · change IsUnit ((3 : ZMod 13457) ^ 464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3592 : ZMod 13457)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13463 : Nat.Prime 13463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13463 13462 1 5 [2, 53, 127]
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
    · change IsUnit ((5 : ZMod 13463) ^ 6731 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6731 : ZMod 13463)
      decide
    · change IsUnit ((5 : ZMod 13463) ^ 254 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9892 : ZMod 13463)
      decide
    · change IsUnit ((5 : ZMod 13463) ^ 106 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2431 : ZMod 13463)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13469 : Nat.Prime 13469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13469 13468 1 2 [2, 2, 7, 13, 37]
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
    · change IsUnit ((2 : ZMod 13469) ^ 6734 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6734 : ZMod 13469)
      decide
    · change IsUnit ((2 : ZMod 13469) ^ 6734 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6734 : ZMod 13469)
      decide
    · change IsUnit ((2 : ZMod 13469) ^ 1924 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11139 : ZMod 13469)
      decide
    · change IsUnit ((2 : ZMod 13469) ^ 1036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1940 : ZMod 13469)
      decide
    · change IsUnit ((2 : ZMod 13469) ^ 364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11931 : ZMod 13469)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13477 : Nat.Prime 13477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13477 13476 1 2 [2, 2, 3, 1123]
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
    · change IsUnit ((2 : ZMod 13477) ^ 6738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6738 : ZMod 13477)
      decide
    · change IsUnit ((2 : ZMod 13477) ^ 6738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6738 : ZMod 13477)
      decide
    · change IsUnit ((2 : ZMod 13477) ^ 4492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3715 : ZMod 13477)
      decide
    · change IsUnit ((2 : ZMod 13477) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11114 : ZMod 13477)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13487 : Nat.Prime 13487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13487 13486 1 5 [2, 11, 613]
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
    · change IsUnit ((5 : ZMod 13487) ^ 6743 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6743 : ZMod 13487)
      decide
    · change IsUnit ((5 : ZMod 13487) ^ 1226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2090 : ZMod 13487)
      decide
    · change IsUnit ((5 : ZMod 13487) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5074 : ZMod 13487)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13499 : Nat.Prime 13499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13499 13498 1 6 [2, 17, 397]
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
    · change IsUnit ((6 : ZMod 13499) ^ 6749 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6749 : ZMod 13499)
      decide
    · change IsUnit ((6 : ZMod 13499) ^ 794 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9088 : ZMod 13499)
      decide
    · change IsUnit ((6 : ZMod 13499) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10134 : ZMod 13499)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13513 : Nat.Prime 13513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13513 13512 1 5 [2, 2, 2, 3, 563]
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
    · change IsUnit ((5 : ZMod 13513) ^ 6756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6756 : ZMod 13513)
      decide
    · change IsUnit ((5 : ZMod 13513) ^ 6756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6756 : ZMod 13513)
      decide
    · change IsUnit ((5 : ZMod 13513) ^ 6756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6756 : ZMod 13513)
      decide
    · change IsUnit ((5 : ZMod 13513) ^ 4504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6369 : ZMod 13513)
      decide
    · change IsUnit ((5 : ZMod 13513) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3665 : ZMod 13513)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13523 : Nat.Prime 13523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13523 13522 1 2 [2, 6761]
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
    · change IsUnit ((2 : ZMod 13523) ^ 6761 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6761 : ZMod 13523)
      decide
    · change IsUnit ((2 : ZMod 13523) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4508 : ZMod 13523)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by exact lowPrime_13457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by exact lowPrime_13463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by exact lowPrime_13469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by exact lowPrime_13477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by exact lowPrime_13487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by exact lowPrime_13499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by exact lowPrime_13513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by exact lowPrime_13523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part02_chain :
    DusartPrimeRowsChain 13451 13523 dusartPrimeRows_13367_14050_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num
