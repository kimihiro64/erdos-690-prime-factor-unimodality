import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 90 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8969 : Nat.Prime 8969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8969 8968 1 3 [2, 2, 2, 19, 59]
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
    · apply IsUnit.of_mul_eq_one (4484 : ZMod 8969)
      decide
    · apply IsUnit.of_mul_eq_one (5749 : ZMod 8969)
      decide
    · apply IsUnit.of_mul_eq_one (5118 : ZMod 8969)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8971 : Nat.Prime 8971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8971 8970 1 2 [2, 3, 5, 13, 23]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4485 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (6094 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (8016 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (3263 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (6727 : ZMod 8971)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8999 : Nat.Prime 8999 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8999 8998 1 7 [2, 11, 409]
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
    · apply IsUnit.of_mul_eq_one (4499 : ZMod 8999)
      decide
    · apply IsUnit.of_mul_eq_one (6640 : ZMod 8999)
      decide
    · apply IsUnit.of_mul_eq_one (1291 : ZMod 8999)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9001 : Nat.Prime 9001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9001 9000 1 7 [2, 2, 2, 3, 3, 5, 5, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4500 : ZMod 9001)
      decide
    · apply IsUnit.of_mul_eq_one (4266 : ZMod 9001)
      decide
    · apply IsUnit.of_mul_eq_one (4608 : ZMod 9001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9007 : Nat.Prime 9007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9007 9006 1 3 [2, 3, 19, 79]
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
    · apply IsUnit.of_mul_eq_one (4503 : ZMod 9007)
      decide
    · apply IsUnit.of_mul_eq_one (6369 : ZMod 9007)
      decide
    · apply IsUnit.of_mul_eq_one (5491 : ZMod 9007)
      decide
    · apply IsUnit.of_mul_eq_one (3381 : ZMod 9007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9011 : Nat.Prime 9011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9011 9010 1 2 [2, 5, 17, 53]
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
    · apply IsUnit.of_mul_eq_one (4505 : ZMod 9011)
      decide
    · apply IsUnit.of_mul_eq_one (4931 : ZMod 9011)
      decide
    · apply IsUnit.of_mul_eq_one (5686 : ZMod 9011)
      decide
    · apply IsUnit.of_mul_eq_one (7138 : ZMod 9011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9013 : Nat.Prime 9013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9013 9012 1 5 [2, 2, 3, 751]
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
    · apply IsUnit.of_mul_eq_one (4506 : ZMod 9013)
      decide
    · apply IsUnit.of_mul_eq_one (1108 : ZMod 9013)
      decide
    · apply IsUnit.of_mul_eq_one (402 : ZMod 9013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9029 : Nat.Prime 9029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9029 9028 1 2 [2, 2, 37, 61]
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
    · apply IsUnit.of_mul_eq_one (4514 : ZMod 9029)
      decide
    · apply IsUnit.of_mul_eq_one (1906 : ZMod 9029)
      decide
    · apply IsUnit.of_mul_eq_one (1880 : ZMod 9029)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by exact lowPrime_8969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by exact lowPrime_8971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by exact lowPrime_8999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by exact lowPrime_9001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by exact lowPrime_9007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by exact lowPrime_9011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by exact lowPrime_9013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by exact lowPrime_9029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part01_chain :
    DusartPrimeRowsChain 8963 9028 dusartPrimeRows_8963_9418_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]
