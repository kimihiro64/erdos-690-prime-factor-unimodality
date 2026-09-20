import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 161 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_14057 : Nat.Prime 14057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14057 14056 1 3 [2, 2, 2, 7, 251]
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
    · change IsUnit ((3 : ZMod 14057) ^ 7028 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7028 : ZMod 14057)
      decide
    · change IsUnit ((3 : ZMod 14057) ^ 7028 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7028 : ZMod 14057)
      decide
    · change IsUnit ((3 : ZMod 14057) ^ 7028 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7028 : ZMod 14057)
      decide
    · change IsUnit ((3 : ZMod 14057) ^ 2008 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7520 : ZMod 14057)
      decide
    · change IsUnit ((3 : ZMod 14057) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12163 : ZMod 14057)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14071 : Nat.Prime 14071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14071 14070 1 7 [2, 3, 5, 7, 67]
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
    · change IsUnit ((7 : ZMod 14071) ^ 7035 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7035 : ZMod 14071)
      decide
    · change IsUnit ((7 : ZMod 14071) ^ 4690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9718 : ZMod 14071)
      decide
    · change IsUnit ((7 : ZMod 14071) ^ 2814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1196 : ZMod 14071)
      decide
    · change IsUnit ((7 : ZMod 14071) ^ 2010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10307 : ZMod 14071)
      decide
    · change IsUnit ((7 : ZMod 14071) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8635 : ZMod 14071)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14081 : Nat.Prime 14081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14081 14080 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 5, 11]
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
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 2816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9826 : ZMod 14081)
      decide
    · change IsUnit ((3 : ZMod 14081) ^ 1280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5154 : ZMod 14081)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14083 : Nat.Prime 14083 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14083 14082 1 3 [2, 3, 2347]
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
    · change IsUnit ((3 : ZMod 14083) ^ 7041 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7041 : ZMod 14083)
      decide
    · change IsUnit ((3 : ZMod 14083) ^ 4694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8463 : ZMod 14083)
      decide
    · change IsUnit ((3 : ZMod 14083) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (561 : ZMod 14083)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14087 : Nat.Prime 14087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14087 14086 1 5 [2, 7043]
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
    · change IsUnit ((5 : ZMod 14087) ^ 7043 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7043 : ZMod 14087)
      decide
    · change IsUnit ((5 : ZMod 14087) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (587 : ZMod 14087)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14107 : Nat.Prime 14107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14107 14106 1 2 [2, 3, 2351]
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
    · change IsUnit ((2 : ZMod 14107) ^ 7053 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7053 : ZMod 14107)
      decide
    · change IsUnit ((2 : ZMod 14107) ^ 4702 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6418 : ZMod 14107)
      decide
    · change IsUnit ((2 : ZMod 14107) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8509 : ZMod 14107)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14143 : Nat.Prime 14143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14143 14142 1 3 [2, 3, 2357]
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
    · change IsUnit ((3 : ZMod 14143) ^ 7071 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7071 : ZMod 14143)
      decide
    · change IsUnit ((3 : ZMod 14143) ^ 4714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2990 : ZMod 14143)
      decide
    · change IsUnit ((3 : ZMod 14143) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12142 : ZMod 14143)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14149 : Nat.Prime 14149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14149 14148 1 6 [2, 2, 3, 3, 3, 131]
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
    · change IsUnit ((6 : ZMod 14149) ^ 7074 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7074 : ZMod 14149)
      decide
    · change IsUnit ((6 : ZMod 14149) ^ 7074 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7074 : ZMod 14149)
      decide
    · change IsUnit ((6 : ZMod 14149) ^ 4716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9983 : ZMod 14149)
      decide
    · change IsUnit ((6 : ZMod 14149) ^ 4716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9983 : ZMod 14149)
      decide
    · change IsUnit ((6 : ZMod 14149) ^ 4716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9983 : ZMod 14149)
      decide
    · change IsUnit ((6 : ZMod 14149) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1348 : ZMod 14149)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14051) (q := 14057) (by exact lowPrime_14057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14057) (q := 14071) (by exact lowPrime_14071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14071) (q := 14081) (by exact lowPrime_14081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14081) (q := 14083) (by exact lowPrime_14083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14083) (q := 14087) (by exact lowPrime_14087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14087) (q := 14107) (by exact lowPrime_14107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14107) (q := 14143) (by exact lowPrime_14143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14143) (q := 14149) (by exact lowPrime_14149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part01_chain :
    DusartPrimeRowsChain 14051 14149 dusartPrimeRows_14051_14766_part01 := by
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
