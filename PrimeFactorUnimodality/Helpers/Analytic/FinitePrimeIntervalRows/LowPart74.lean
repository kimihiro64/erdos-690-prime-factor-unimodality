import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 74 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7949 : Nat.Prime 7949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7949 7948 1 2 [2, 2, 1987]
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
    · apply IsUnit.of_mul_eq_one (3974 : ZMod 7949)
      decide
    · apply IsUnit.of_mul_eq_one (530 : ZMod 7949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7951 : Nat.Prime 7951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7951 7950 1 6 [2, 3, 5, 5, 53]
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
    · apply IsUnit.of_mul_eq_one (3975 : ZMod 7951)
      decide
    · apply IsUnit.of_mul_eq_one (2757 : ZMod 7951)
      decide
    · apply IsUnit.of_mul_eq_one (1845 : ZMod 7951)
      decide
    · apply IsUnit.of_mul_eq_one (54 : ZMod 7951)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7963 : Nat.Prime 7963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7963 7962 1 5 [2, 3, 1327]
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
    · apply IsUnit.of_mul_eq_one (3981 : ZMod 7963)
      decide
    · apply IsUnit.of_mul_eq_one (4767 : ZMod 7963)
      decide
    · apply IsUnit.of_mul_eq_one (3085 : ZMod 7963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7993 : Nat.Prime 7993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7993 7992 1 5 [2, 2, 2, 3, 3, 3, 37]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3996 : ZMod 7993)
      decide
    · apply IsUnit.of_mul_eq_one (1081 : ZMod 7993)
      decide
    · apply IsUnit.of_mul_eq_one (6551 : ZMod 7993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8009 : Nat.Prime 8009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8009 8008 1 3 [2, 2, 2, 7, 11, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4004 : ZMod 8009)
      decide
    · apply IsUnit.of_mul_eq_one (6638 : ZMod 8009)
      decide
    · apply IsUnit.of_mul_eq_one (7070 : ZMod 8009)
      decide
    · apply IsUnit.of_mul_eq_one (5524 : ZMod 8009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8011 : Nat.Prime 8011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8011 8010 1 14 [2, 3, 3, 5, 89]
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
    · apply IsUnit.of_mul_eq_one (4005 : ZMod 8011)
      decide
    · apply IsUnit.of_mul_eq_one (5370 : ZMod 8011)
      decide
    · apply IsUnit.of_mul_eq_one (1854 : ZMod 8011)
      decide
    · apply IsUnit.of_mul_eq_one (5977 : ZMod 8011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8017 : Nat.Prime 8017 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8017 8016 1 5 [2, 2, 2, 2, 3, 167]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4008 : ZMod 8017)
      decide
    · apply IsUnit.of_mul_eq_one (6225 : ZMod 8017)
      decide
    · apply IsUnit.of_mul_eq_one (5098 : ZMod 8017)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8039 : Nat.Prime 8039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8039 8038 1 11 [2, 4019]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (4019 : ZMod 8039)
      decide
    · apply IsUnit.of_mul_eq_one (67 : ZMod 8039)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by exact lowPrime_7949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by exact lowPrime_7951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by exact lowPrime_7963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by exact lowPrime_7993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by exact lowPrime_8009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by exact lowPrime_8011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by exact lowPrime_8017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by exact lowPrime_8039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part04_chain :
    DusartPrimeRowsChain 7937 8038 dusartPrimeRows_7717_8110_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]
