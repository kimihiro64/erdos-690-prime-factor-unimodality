import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3407 : Nat.Prime 3407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3407 3406 1 5 [2, 13, 131]
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
    · change IsUnit ((5 : ZMod 3407) ^ 1703 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1703 : ZMod 3407)
      decide
    · change IsUnit ((5 : ZMod 3407) ^ 262 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1695 : ZMod 3407)
      decide
    · change IsUnit ((5 : ZMod 3407) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2199 : ZMod 3407)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3413 : Nat.Prime 3413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3413 3412 1 2 [2, 2, 853]
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
    · change IsUnit ((2 : ZMod 3413) ^ 1706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1706 : ZMod 3413)
      decide
    · change IsUnit ((2 : ZMod 3413) ^ 1706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1706 : ZMod 3413)
      decide
    · change IsUnit ((2 : ZMod 3413) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2958 : ZMod 3413)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3433 : Nat.Prime 3433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3433 3432 1 5 [2, 2, 2, 3, 11, 13]
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
    · change IsUnit ((5 : ZMod 3433) ^ 1716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1716 : ZMod 3433)
      decide
    · change IsUnit ((5 : ZMod 3433) ^ 1716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1716 : ZMod 3433)
      decide
    · change IsUnit ((5 : ZMod 3433) ^ 1716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1716 : ZMod 3433)
      decide
    · change IsUnit ((5 : ZMod 3433) ^ 1144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3343 : ZMod 3433)
      decide
    · change IsUnit ((5 : ZMod 3433) ^ 312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2907 : ZMod 3433)
      decide
    · change IsUnit ((5 : ZMod 3433) ^ 264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1746 : ZMod 3433)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3449 : Nat.Prime 3449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3449 3448 1 3 [2, 2, 2, 431]
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
    · change IsUnit ((3 : ZMod 3449) ^ 1724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1724 : ZMod 3449)
      decide
    · change IsUnit ((3 : ZMod 3449) ^ 1724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1724 : ZMod 3449)
      decide
    · change IsUnit ((3 : ZMod 3449) ^ 1724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1724 : ZMod 3449)
      decide
    · change IsUnit ((3 : ZMod 3449) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (500 : ZMod 3449)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3457 : Nat.Prime 3457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3457 3456 1 7 [2, 2, 2, 2, 2, 2, 2, 3, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1152 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (911 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1152 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (911 : ZMod 3457)
      decide
    · change IsUnit ((7 : ZMod 3457) ^ 1152 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (911 : ZMod 3457)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3461 : Nat.Prime 3461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3461 3460 1 2 [2, 2, 5, 173]
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
    · change IsUnit ((2 : ZMod 3461) ^ 1730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1730 : ZMod 3461)
      decide
    · change IsUnit ((2 : ZMod 3461) ^ 1730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1730 : ZMod 3461)
      decide
    · change IsUnit ((2 : ZMod 3461) ^ 692 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3335 : ZMod 3461)
      decide
    · change IsUnit ((2 : ZMod 3461) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2083 : ZMod 3461)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3463 : Nat.Prime 3463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3463 3462 1 3 [2, 3, 577]
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
    · change IsUnit ((3 : ZMod 3463) ^ 1731 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1731 : ZMod 3463)
      decide
    · change IsUnit ((3 : ZMod 3463) ^ 1154 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3340 : ZMod 3463)
      decide
    · change IsUnit ((3 : ZMod 3463) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2250 : ZMod 3463)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3467 : Nat.Prime 3467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3467 3466 1 2 [2, 1733]
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
    · change IsUnit ((2 : ZMod 3467) ^ 1733 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1733 : ZMod 3467)
      decide
    · change IsUnit ((2 : ZMod 3467) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1156 : ZMod 3467)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by exact lowPrime_3407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by exact lowPrime_3413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by exact lowPrime_3433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by exact lowPrime_3449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by exact lowPrime_3457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by exact lowPrime_3461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by exact lowPrime_3463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by exact lowPrime_3467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part03_chain :
    DusartPrimeRowsChain 3391 3467 dusartPrimeRows_3275_3802_part03 := by
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
