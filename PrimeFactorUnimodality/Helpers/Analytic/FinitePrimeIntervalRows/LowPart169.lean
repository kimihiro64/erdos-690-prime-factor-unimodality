import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 169 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_14717 : Nat.Prime 14717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14717 14716 1 2 [2, 2, 13, 283]
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
    · change IsUnit ((2 : ZMod 14717) ^ 7358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7358 : ZMod 14717)
      decide
    · change IsUnit ((2 : ZMod 14717) ^ 7358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7358 : ZMod 14717)
      decide
    · change IsUnit ((2 : ZMod 14717) ^ 1132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12473 : ZMod 14717)
      decide
    · change IsUnit ((2 : ZMod 14717) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7774 : ZMod 14717)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14723 : Nat.Prime 14723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14723 14722 1 2 [2, 17, 433]
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
    · change IsUnit ((2 : ZMod 14723) ^ 7361 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7361 : ZMod 14723)
      decide
    · change IsUnit ((2 : ZMod 14723) ^ 866 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8205 : ZMod 14723)
      decide
    · change IsUnit ((2 : ZMod 14723) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5156 : ZMod 14723)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14731 : Nat.Prime 14731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14731 14730 1 10 [2, 3, 5, 491]
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
    · change IsUnit ((10 : ZMod 14731) ^ 7365 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7365 : ZMod 14731)
      decide
    · change IsUnit ((10 : ZMod 14731) ^ 4910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4274 : ZMod 14731)
      decide
    · change IsUnit ((10 : ZMod 14731) ^ 2946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14105 : ZMod 14731)
      decide
    · change IsUnit ((10 : ZMod 14731) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2987 : ZMod 14731)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14737 : Nat.Prime 14737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14737 14736 1 10 [2, 2, 2, 2, 3, 307]
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
    · change IsUnit ((10 : ZMod 14737) ^ 7368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7368 : ZMod 14737)
      decide
    · change IsUnit ((10 : ZMod 14737) ^ 7368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7368 : ZMod 14737)
      decide
    · change IsUnit ((10 : ZMod 14737) ^ 7368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7368 : ZMod 14737)
      decide
    · change IsUnit ((10 : ZMod 14737) ^ 7368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7368 : ZMod 14737)
      decide
    · change IsUnit ((10 : ZMod 14737) ^ 4912 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6359 : ZMod 14737)
      decide
    · change IsUnit ((10 : ZMod 14737) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8565 : ZMod 14737)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14741 : Nat.Prime 14741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14741 14740 1 2 [2, 2, 5, 11, 67]
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
    · change IsUnit ((2 : ZMod 14741) ^ 7370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7370 : ZMod 14741)
      decide
    · change IsUnit ((2 : ZMod 14741) ^ 7370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7370 : ZMod 14741)
      decide
    · change IsUnit ((2 : ZMod 14741) ^ 2948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14703 : ZMod 14741)
      decide
    · change IsUnit ((2 : ZMod 14741) ^ 1340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5286 : ZMod 14741)
      decide
    · change IsUnit ((2 : ZMod 14741) ^ 220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12019 : ZMod 14741)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14747 : Nat.Prime 14747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14747 14746 1 2 [2, 73, 101]
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
    · change IsUnit ((2 : ZMod 14747) ^ 7373 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7373 : ZMod 14747)
      decide
    · change IsUnit ((2 : ZMod 14747) ^ 202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6507 : ZMod 14747)
      decide
    · change IsUnit ((2 : ZMod 14747) ^ 146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3481 : ZMod 14747)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14753 : Nat.Prime 14753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14753 14752 1 3 [2, 2, 2, 2, 2, 461]
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
    · change IsUnit ((3 : ZMod 14753) ^ 7376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7376 : ZMod 14753)
      decide
    · change IsUnit ((3 : ZMod 14753) ^ 7376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7376 : ZMod 14753)
      decide
    · change IsUnit ((3 : ZMod 14753) ^ 7376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7376 : ZMod 14753)
      decide
    · change IsUnit ((3 : ZMod 14753) ^ 7376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7376 : ZMod 14753)
      decide
    · change IsUnit ((3 : ZMod 14753) ^ 7376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7376 : ZMod 14753)
      decide
    · change IsUnit ((3 : ZMod 14753) ^ 32 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7110 : ZMod 14753)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14759 : Nat.Prime 14759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14759 14758 1 17 [2, 47, 157]
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
    · change IsUnit ((17 : ZMod 14759) ^ 7379 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7379 : ZMod 14759)
      decide
    · change IsUnit ((17 : ZMod 14759) ^ 314 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2089 : ZMod 14759)
      decide
    · change IsUnit ((17 : ZMod 14759) ^ 94 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9439 : ZMod 14759)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14713) (q := 14717) (by exact lowPrime_14717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14717) (q := 14723) (by exact lowPrime_14723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14723) (q := 14731) (by exact lowPrime_14731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14731) (q := 14737) (by exact lowPrime_14737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14737) (q := 14741) (by exact lowPrime_14741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14741) (q := 14747) (by exact lowPrime_14747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14747) (q := 14753) (by exact lowPrime_14753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14753) (q := 14759) (by exact lowPrime_14759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part09_chain :
    DusartPrimeRowsChain 14713 14759 dusartPrimeRows_14051_14766_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num
