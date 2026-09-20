import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 28 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4973 : Nat.Prime 4973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4973 4972 1 2 [2, 2, 11, 113]
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
    · apply IsUnit.of_mul_eq_one (2486 : ZMod 4973)
      decide
    · apply IsUnit.of_mul_eq_one (1889 : ZMod 4973)
      decide
    · apply IsUnit.of_mul_eq_one (604 : ZMod 4973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4987 : Nat.Prime 4987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4987 4986 1 2 [2, 3, 3, 277]
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
    · apply IsUnit.of_mul_eq_one (2493 : ZMod 4987)
      decide
    · apply IsUnit.of_mul_eq_one (3703 : ZMod 4987)
      decide
    · apply IsUnit.of_mul_eq_one (835 : ZMod 4987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4993 : Nat.Prime 4993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4993 4992 1 5 [2, 2, 2, 2, 2, 2, 2, 3, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2496 : ZMod 4993)
      decide
    · apply IsUnit.of_mul_eq_one (4109 : ZMod 4993)
      decide
    · apply IsUnit.of_mul_eq_one (4169 : ZMod 4993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4999 : Nat.Prime 4999 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4999 4998 1 3 [2, 3, 7, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (2499 : ZMod 4999)
      decide
    · apply IsUnit.of_mul_eq_one (2445 : ZMod 4999)
      decide
    · apply IsUnit.of_mul_eq_one (3517 : ZMod 4999)
      decide
    · apply IsUnit.of_mul_eq_one (3757 : ZMod 4999)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5003 : Nat.Prime 5003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5003 5002 1 2 [2, 41, 61]
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
    · apply IsUnit.of_mul_eq_one (2501 : ZMod 5003)
      decide
    · apply IsUnit.of_mul_eq_one (3107 : ZMod 5003)
      decide
    · apply IsUnit.of_mul_eq_one (4341 : ZMod 5003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5009 : Nat.Prime 5009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5009 5008 1 3 [2, 2, 2, 2, 313]
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
    · apply IsUnit.of_mul_eq_one (2504 : ZMod 5009)
      decide
    · apply IsUnit.of_mul_eq_one (8 : ZMod 5009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5011 : Nat.Prime 5011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5011 5010 1 2 [2, 3, 5, 167]
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
    · apply IsUnit.of_mul_eq_one (2505 : ZMod 5011)
      decide
    · apply IsUnit.of_mul_eq_one (2371 : ZMod 5011)
      decide
    · apply IsUnit.of_mul_eq_one (2745 : ZMod 5011)
      decide
    · apply IsUnit.of_mul_eq_one (604 : ZMod 5011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5021 : Nat.Prime 5021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5021 5020 1 3 [2, 2, 5, 251]
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
    · apply IsUnit.of_mul_eq_one (2510 : ZMod 5021)
      decide
    · apply IsUnit.of_mul_eq_one (571 : ZMod 5021)
      decide
    · apply IsUnit.of_mul_eq_one (3545 : ZMod 5021)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by exact lowPrime_4973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by exact lowPrime_4987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by exact lowPrime_4993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by exact lowPrime_4999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by exact lowPrime_5003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by exact lowPrime_5009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by exact lowPrime_5011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by exact lowPrime_5021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part02_chain :
    DusartPrimeRowsChain 4969 5020 dusartPrimeRows_4919_5166_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]
