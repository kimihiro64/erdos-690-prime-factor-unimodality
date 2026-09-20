import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 216 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22993 : Nat.Prime 22993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22993 22992 1 5 [2, 2, 2, 2, 3, 479]
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
    · apply IsUnit.of_mul_eq_one (11496 : ZMod 22993)
      decide
    · apply IsUnit.of_mul_eq_one (14846 : ZMod 22993)
      decide
    · apply IsUnit.of_mul_eq_one (14343 : ZMod 22993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23003 : Nat.Prime 23003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23003 23002 1 2 [2, 7, 31, 53]
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
    · apply IsUnit.of_mul_eq_one (11501 : ZMod 23003)
      decide
    · apply IsUnit.of_mul_eq_one (8451 : ZMod 23003)
      decide
    · apply IsUnit.of_mul_eq_one (3168 : ZMod 23003)
      decide
    · apply IsUnit.of_mul_eq_one (7355 : ZMod 23003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23011 : Nat.Prime 23011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23011 23010 1 7 [2, 3, 5, 13, 59]
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
    · apply IsUnit.of_mul_eq_one (11505 : ZMod 23011)
      decide
    · apply IsUnit.of_mul_eq_one (5303 : ZMod 23011)
      decide
    · apply IsUnit.of_mul_eq_one (11398 : ZMod 23011)
      decide
    · apply IsUnit.of_mul_eq_one (6664 : ZMod 23011)
      decide
    · apply IsUnit.of_mul_eq_one (4153 : ZMod 23011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23017 : Nat.Prime 23017 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23017 23016 1 5 [2, 2, 2, 3, 7, 137]
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
    · apply IsUnit.of_mul_eq_one (11508 : ZMod 23017)
      decide
    · apply IsUnit.of_mul_eq_one (1872 : ZMod 23017)
      decide
    · apply IsUnit.of_mul_eq_one (4639 : ZMod 23017)
      decide
    · apply IsUnit.of_mul_eq_one (8314 : ZMod 23017)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23021 : Nat.Prime 23021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23021 23020 1 2 [2, 2, 5, 1151]
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
    · apply IsUnit.of_mul_eq_one (11510 : ZMod 23021)
      decide
    · apply IsUnit.of_mul_eq_one (10529 : ZMod 23021)
      decide
    · apply IsUnit.of_mul_eq_one (20759 : ZMod 23021)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23027 : Nat.Prime 23027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23027 23026 1 2 [2, 29, 397]
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
    · apply IsUnit.of_mul_eq_one (11513 : ZMod 23027)
      decide
    · apply IsUnit.of_mul_eq_one (5365 : ZMod 23027)
      decide
    · apply IsUnit.of_mul_eq_one (6703 : ZMod 23027)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23029 : Nat.Prime 23029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23029 23028 1 2 [2, 2, 3, 19, 101]
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
    · apply IsUnit.of_mul_eq_one (11514 : ZMod 23029)
      decide
    · apply IsUnit.of_mul_eq_one (7542 : ZMod 23029)
      decide
    · apply IsUnit.of_mul_eq_one (6698 : ZMod 23029)
      decide
    · apply IsUnit.of_mul_eq_one (1123 : ZMod 23029)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_23039 : Nat.Prime 23039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23039 23038 1 7 [2, 11519]
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
    · apply IsUnit.of_mul_eq_one (11519 : ZMod 23039)
      decide
    · apply IsUnit.of_mul_eq_one (480 : ZMod 23039)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by exact lowPrime_22993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by exact lowPrime_23003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by exact lowPrime_23011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by exact lowPrime_23017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by exact lowPrime_23021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by exact lowPrime_23027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by exact lowPrime_23029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by exact lowPrime_23039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part13_chain :
    DusartPrimeRowsChain 22973 23038 dusartPrimeRows_22027_23158_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]
