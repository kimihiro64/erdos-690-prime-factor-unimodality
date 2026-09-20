import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 235 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20089 : Nat.Prime 20089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20089 20088 1 7 [2, 2, 2, 3, 3, 3, 3, 31]
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
    · change IsUnit ((7 : ZMod 20089) ^ 10044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10044 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 10044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10044 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 10044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10044 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 6696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3974 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 6696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3974 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 6696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3974 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 6696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3974 : ZMod 20089)
      decide
    · change IsUnit ((7 : ZMod 20089) ^ 648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6817 : ZMod 20089)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20101 : Nat.Prime 20101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20101 20100 1 6 [2, 2, 3, 5, 5, 67]
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
    · change IsUnit ((6 : ZMod 20101) ^ 10050 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10050 : ZMod 20101)
      decide
    · change IsUnit ((6 : ZMod 20101) ^ 10050 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10050 : ZMod 20101)
      decide
    · change IsUnit ((6 : ZMod 20101) ^ 6700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17996 : ZMod 20101)
      decide
    · change IsUnit ((6 : ZMod 20101) ^ 4020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9511 : ZMod 20101)
      decide
    · change IsUnit ((6 : ZMod 20101) ^ 4020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9511 : ZMod 20101)
      decide
    · change IsUnit ((6 : ZMod 20101) ^ 300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3422 : ZMod 20101)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20107 : Nat.Prime 20107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20107 20106 1 2 [2, 3, 3, 1117]
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
    · change IsUnit ((2 : ZMod 20107) ^ 10053 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10053 : ZMod 20107)
      decide
    · change IsUnit ((2 : ZMod 20107) ^ 6702 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4380 : ZMod 20107)
      decide
    · change IsUnit ((2 : ZMod 20107) ^ 6702 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4380 : ZMod 20107)
      decide
    · change IsUnit ((2 : ZMod 20107) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10615 : ZMod 20107)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20113 : Nat.Prime 20113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20113 20112 1 10 [2, 2, 2, 2, 3, 419]
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
    · change IsUnit ((10 : ZMod 20113) ^ 10056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10056 : ZMod 20113)
      decide
    · change IsUnit ((10 : ZMod 20113) ^ 10056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10056 : ZMod 20113)
      decide
    · change IsUnit ((10 : ZMod 20113) ^ 10056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10056 : ZMod 20113)
      decide
    · change IsUnit ((10 : ZMod 20113) ^ 10056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10056 : ZMod 20113)
      decide
    · change IsUnit ((10 : ZMod 20113) ^ 6704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11584 : ZMod 20113)
      decide
    · change IsUnit ((10 : ZMod 20113) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9731 : ZMod 20113)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20117 : Nat.Prime 20117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20117 20116 1 2 [2, 2, 47, 107]
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
    · change IsUnit ((2 : ZMod 20117) ^ 10058 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10058 : ZMod 20117)
      decide
    · change IsUnit ((2 : ZMod 20117) ^ 10058 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10058 : ZMod 20117)
      decide
    · change IsUnit ((2 : ZMod 20117) ^ 428 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6602 : ZMod 20117)
      decide
    · change IsUnit ((2 : ZMod 20117) ^ 188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14613 : ZMod 20117)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20123 : Nat.Prime 20123 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20123 20122 1 2 [2, 10061]
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
    · change IsUnit ((2 : ZMod 20123) ^ 10061 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10061 : ZMod 20123)
      decide
    · change IsUnit ((2 : ZMod 20123) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6708 : ZMod 20123)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20129 : Nat.Prime 20129 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20129 20128 1 3 [2, 2, 2, 2, 2, 17, 37]
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
    · change IsUnit ((3 : ZMod 20129) ^ 10064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10064 : ZMod 20129)
      decide
    · change IsUnit ((3 : ZMod 20129) ^ 10064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10064 : ZMod 20129)
      decide
    · change IsUnit ((3 : ZMod 20129) ^ 10064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10064 : ZMod 20129)
      decide
    · change IsUnit ((3 : ZMod 20129) ^ 10064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10064 : ZMod 20129)
      decide
    · change IsUnit ((3 : ZMod 20129) ^ 10064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10064 : ZMod 20129)
      decide
    · change IsUnit ((3 : ZMod 20129) ^ 1184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15787 : ZMod 20129)
      decide
    · change IsUnit ((3 : ZMod 20129) ^ 544 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11635 : ZMod 20129)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20143 : Nat.Prime 20143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20143 20142 1 5 [2, 3, 3, 3, 373]
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
    · change IsUnit ((5 : ZMod 20143) ^ 10071 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10071 : ZMod 20143)
      decide
    · change IsUnit ((5 : ZMod 20143) ^ 6714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6839 : ZMod 20143)
      decide
    · change IsUnit ((5 : ZMod 20143) ^ 6714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6839 : ZMod 20143)
      decide
    · change IsUnit ((5 : ZMod 20143) ^ 6714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6839 : ZMod 20143)
      decide
    · change IsUnit ((5 : ZMod 20143) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7643 : ZMod 20143)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20071) (q := 20089) (by exact lowPrime_20089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20089) (q := 20101) (by exact lowPrime_20101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20101) (q := 20107) (by exact lowPrime_20107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20107) (q := 20113) (by exact lowPrime_20113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20113) (q := 20117) (by exact lowPrime_20117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20117) (q := 20123) (by exact lowPrime_20123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20123) (q := 20129) (by exact lowPrime_20129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20129) (q := 20143) (by exact lowPrime_20143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part03_chain :
    DusartPrimeRowsChain 20071 20143 dusartPrimeRows_19937_20958_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num
