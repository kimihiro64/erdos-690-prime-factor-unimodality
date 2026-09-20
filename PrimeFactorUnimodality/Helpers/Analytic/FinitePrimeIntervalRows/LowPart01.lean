import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 01 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3299 : Nat.Prime 3299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3299 3298 1 2 [2, 17, 97]
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
    · change IsUnit ((2 : ZMod 3299) ^ 1649 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1649 : ZMod 3299)
      decide
    · change IsUnit ((2 : ZMod 3299) ^ 194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2551 : ZMod 3299)
      decide
    · change IsUnit ((2 : ZMod 3299) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2776 : ZMod 3299)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3301 : Nat.Prime 3301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3301 3300 1 6 [2, 2, 3, 5, 5, 11]
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
    · change IsUnit ((6 : ZMod 3301) ^ 1650 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1650 : ZMod 3301)
      decide
    · change IsUnit ((6 : ZMod 3301) ^ 1650 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1650 : ZMod 3301)
      decide
    · change IsUnit ((6 : ZMod 3301) ^ 1100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2725 : ZMod 3301)
      decide
    · change IsUnit ((6 : ZMod 3301) ^ 660 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (233 : ZMod 3301)
      decide
    · change IsUnit ((6 : ZMod 3301) ^ 660 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (233 : ZMod 3301)
      decide
    · change IsUnit ((6 : ZMod 3301) ^ 300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2209 : ZMod 3301)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3307 : Nat.Prime 3307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3307 3306 1 2 [2, 3, 19, 29]
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
    · change IsUnit ((2 : ZMod 3307) ^ 1653 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1653 : ZMod 3307)
      decide
    · change IsUnit ((2 : ZMod 3307) ^ 1102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2185 : ZMod 3307)
      decide
    · change IsUnit ((2 : ZMod 3307) ^ 174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (264 : ZMod 3307)
      decide
    · change IsUnit ((2 : ZMod 3307) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3069 : ZMod 3307)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3313 : Nat.Prime 3313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3313 3312 1 10 [2, 2, 2, 2, 3, 3, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((10 : ZMod 3313) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1656 : ZMod 3313)
      decide
    · change IsUnit ((10 : ZMod 3313) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1656 : ZMod 3313)
      decide
    · change IsUnit ((10 : ZMod 3313) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1656 : ZMod 3313)
      decide
    · change IsUnit ((10 : ZMod 3313) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1656 : ZMod 3313)
      decide
    · change IsUnit ((10 : ZMod 3313) ^ 1104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2938 : ZMod 3313)
      decide
    · change IsUnit ((10 : ZMod 3313) ^ 1104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2938 : ZMod 3313)
      decide
    · change IsUnit ((10 : ZMod 3313) ^ 144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1903 : ZMod 3313)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3319 : Nat.Prime 3319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3319 3318 1 6 [2, 3, 7, 79]
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
    · change IsUnit ((6 : ZMod 3319) ^ 1659 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1659 : ZMod 3319)
      decide
    · change IsUnit ((6 : ZMod 3319) ^ 1106 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1703 : ZMod 3319)
      decide
    · change IsUnit ((6 : ZMod 3319) ^ 474 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (166 : ZMod 3319)
      decide
    · change IsUnit ((6 : ZMod 3319) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1821 : ZMod 3319)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3323 : Nat.Prime 3323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3323 3322 1 2 [2, 11, 151]
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
    · change IsUnit ((2 : ZMod 3323) ^ 1661 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1661 : ZMod 3323)
      decide
    · change IsUnit ((2 : ZMod 3323) ^ 302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (600 : ZMod 3323)
      decide
    · change IsUnit ((2 : ZMod 3323) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1340 : ZMod 3323)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3329 : Nat.Prime 3329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3329 3328 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 1664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · change IsUnit ((3 : ZMod 3329) ^ 256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (823 : ZMod 3329)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3331 : Nat.Prime 3331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3331 3330 1 3 [2, 3, 3, 5, 37]
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
    · change IsUnit ((3 : ZMod 3331) ^ 1665 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1665 : ZMod 3331)
      decide
    · change IsUnit ((3 : ZMod 3331) ^ 1110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2708 : ZMod 3331)
      decide
    · change IsUnit ((3 : ZMod 3331) ^ 1110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2708 : ZMod 3331)
      decide
    · change IsUnit ((3 : ZMod 3331) ^ 666 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (558 : ZMod 3331)
      decide
    · change IsUnit ((3 : ZMod 3331) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (325 : ZMod 3331)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by exact lowPrime_3299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by exact lowPrime_3301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by exact lowPrime_3307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by exact lowPrime_3313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by exact lowPrime_3319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by exact lowPrime_3323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by exact lowPrime_3329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by exact lowPrime_3331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part01_chain :
    DusartPrimeRowsChain 3275 3331 dusartPrimeRows_3275_3802_part01 := by
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
