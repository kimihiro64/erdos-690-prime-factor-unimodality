import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 116 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_10831 : Nat.Prime 10831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10831 10830 1 7 [2, 3, 5, 19, 19]
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
    · change IsUnit ((7 : ZMod 10831) ^ 5415 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5415 : ZMod 10831)
      decide
    · change IsUnit ((7 : ZMod 10831) ^ 3610 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9708 : ZMod 10831)
      decide
    · change IsUnit ((7 : ZMod 10831) ^ 2166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2005 : ZMod 10831)
      decide
    · change IsUnit ((7 : ZMod 10831) ^ 570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3346 : ZMod 10831)
      decide
    · change IsUnit ((7 : ZMod 10831) ^ 570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3346 : ZMod 10831)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10837 : Nat.Prime 10837 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10837 10836 1 2 [2, 2, 3, 3, 7, 43]
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
    · change IsUnit ((2 : ZMod 10837) ^ 5418 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5418 : ZMod 10837)
      decide
    · change IsUnit ((2 : ZMod 10837) ^ 5418 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5418 : ZMod 10837)
      decide
    · change IsUnit ((2 : ZMod 10837) ^ 3612 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1374 : ZMod 10837)
      decide
    · change IsUnit ((2 : ZMod 10837) ^ 3612 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1374 : ZMod 10837)
      decide
    · change IsUnit ((2 : ZMod 10837) ^ 1548 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3536 : ZMod 10837)
      decide
    · change IsUnit ((2 : ZMod 10837) ^ 252 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5164 : ZMod 10837)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10847 : Nat.Prime 10847 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10847 10846 1 5 [2, 11, 17, 29]
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
    · change IsUnit ((5 : ZMod 10847) ^ 5423 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5423 : ZMod 10847)
      decide
    · change IsUnit ((5 : ZMod 10847) ^ 986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6321 : ZMod 10847)
      decide
    · change IsUnit ((5 : ZMod 10847) ^ 638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10307 : ZMod 10847)
      decide
    · change IsUnit ((5 : ZMod 10847) ^ 374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1699 : ZMod 10847)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10853 : Nat.Prime 10853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10853 10852 1 2 [2, 2, 2713]
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
    · change IsUnit ((2 : ZMod 10853) ^ 5426 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5426 : ZMod 10853)
      decide
    · change IsUnit ((2 : ZMod 10853) ^ 5426 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5426 : ZMod 10853)
      decide
    · change IsUnit ((2 : ZMod 10853) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9406 : ZMod 10853)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10859 : Nat.Prime 10859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10859 10858 1 2 [2, 61, 89]
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
    · change IsUnit ((2 : ZMod 10859) ^ 5429 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5429 : ZMod 10859)
      decide
    · change IsUnit ((2 : ZMod 10859) ^ 178 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1495 : ZMod 10859)
      decide
    · change IsUnit ((2 : ZMod 10859) ^ 122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8212 : ZMod 10859)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10861 : Nat.Prime 10861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10861 10860 1 2 [2, 2, 3, 5, 181]
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
    · change IsUnit ((2 : ZMod 10861) ^ 5430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5430 : ZMod 10861)
      decide
    · change IsUnit ((2 : ZMod 10861) ^ 5430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5430 : ZMod 10861)
      decide
    · change IsUnit ((2 : ZMod 10861) ^ 3620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1399 : ZMod 10861)
      decide
    · change IsUnit ((2 : ZMod 10861) ^ 2172 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7733 : ZMod 10861)
      decide
    · change IsUnit ((2 : ZMod 10861) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3891 : ZMod 10861)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10867 : Nat.Prime 10867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10867 10866 1 2 [2, 3, 1811]
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
    · change IsUnit ((2 : ZMod 10867) ^ 5433 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5433 : ZMod 10867)
      decide
    · change IsUnit ((2 : ZMod 10867) ^ 3622 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2662 : ZMod 10867)
      decide
    · change IsUnit ((2 : ZMod 10867) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (345 : ZMod 10867)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10883 : Nat.Prime 10883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10883 10882 1 2 [2, 5441]
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
    · change IsUnit ((2 : ZMod 10883) ^ 5441 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5441 : ZMod 10883)
      decide
    · change IsUnit ((2 : ZMod 10883) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3628 : ZMod 10883)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by exact lowPrime_10831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by exact lowPrime_10837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by exact lowPrime_10847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by exact lowPrime_10853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by exact lowPrime_10859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by exact lowPrime_10861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by exact lowPrime_10867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by exact lowPrime_10883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part06_chain :
    DusartPrimeRowsChain 10799 10883 dusartPrimeRows_10427_10938_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num
