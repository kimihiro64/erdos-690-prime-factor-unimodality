import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 160 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13997 : Nat.Prime 13997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13997 13996 1 2 [2, 2, 3499]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6998 : ZMod 13997)
      decide
    · apply IsUnit.of_mul_eq_one (6532 : ZMod 13997)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13999 : Nat.Prime 13999 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13999 13998 1 3 [2, 3, 2333]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6999 : ZMod 13999)
      decide
    · apply IsUnit.of_mul_eq_one (10736 : ZMod 13999)
      decide
    · apply IsUnit.of_mul_eq_one (8634 : ZMod 13999)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14009 : Nat.Prime 14009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14009 14008 1 3 [2, 2, 2, 17, 103]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7004 : ZMod 14009)
      decide
    · apply IsUnit.of_mul_eq_one (10252 : ZMod 14009)
      decide
    · apply IsUnit.of_mul_eq_one (8325 : ZMod 14009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14011 : Nat.Prime 14011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14011 14010 1 2 [2, 3, 5, 467]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7005 : ZMod 14011)
      decide
    · apply IsUnit.of_mul_eq_one (13630 : ZMod 14011)
      decide
    · apply IsUnit.of_mul_eq_one (7782 : ZMod 14011)
      decide
    · apply IsUnit.of_mul_eq_one (13277 : ZMod 14011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14029 : Nat.Prime 14029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14029 14028 1 6 [2, 2, 3, 7, 167]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7014 : ZMod 14029)
      decide
    · apply IsUnit.of_mul_eq_one (11088 : ZMod 14029)
      decide
    · apply IsUnit.of_mul_eq_one (12344 : ZMod 14029)
      decide
    · apply IsUnit.of_mul_eq_one (3017 : ZMod 14029)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14033 : Nat.Prime 14033 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14033 14032 1 3 [2, 2, 2, 2, 877]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (7016 : ZMod 14033)
      decide
    · apply IsUnit.of_mul_eq_one (7565 : ZMod 14033)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14051 : Nat.Prime 14051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14051 14050 1 2 [2, 5, 5, 281]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7025 : ZMod 14051)
      decide
    · apply IsUnit.of_mul_eq_one (10400 : ZMod 14051)
      decide
    · apply IsUnit.of_mul_eq_one (2225 : ZMod 14051)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by exact lowPrime_13997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by exact lowPrime_13999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by exact lowPrime_14009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by exact lowPrime_14011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by exact lowPrime_14029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by exact lowPrime_14033) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by exact lowPrime_14051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part09_chain :
    DusartPrimeRowsChain 13967 14050 dusartPrimeRows_13367_14050_part09 := by
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
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]
