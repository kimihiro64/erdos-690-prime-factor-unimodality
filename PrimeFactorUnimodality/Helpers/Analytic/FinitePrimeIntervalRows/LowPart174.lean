import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 174 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15013 : Nat.Prime 15013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15013 15012 1 2 [2, 2, 3, 3, 3, 139]
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
    · apply IsUnit.of_mul_eq_one (7506 : ZMod 15013)
      decide
    · apply IsUnit.of_mul_eq_one (13358 : ZMod 15013)
      decide
    · apply IsUnit.of_mul_eq_one (14240 : ZMod 15013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15017 : Nat.Prime 15017 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15017 15016 1 3 [2, 2, 2, 1877]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (7508 : ZMod 15017)
      decide
    · apply IsUnit.of_mul_eq_one (9539 : ZMod 15017)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15031 : Nat.Prime 15031 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15031 15030 1 3 [2, 3, 3, 5, 167]
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
    · apply IsUnit.of_mul_eq_one (7515 : ZMod 15031)
      decide
    · apply IsUnit.of_mul_eq_one (13244 : ZMod 15031)
      decide
    · apply IsUnit.of_mul_eq_one (8239 : ZMod 15031)
      decide
    · apply IsUnit.of_mul_eq_one (8961 : ZMod 15031)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15053 : Nat.Prime 15053 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15053 15052 1 2 [2, 2, 53, 71]
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
    · apply IsUnit.of_mul_eq_one (7526 : ZMod 15053)
      decide
    · apply IsUnit.of_mul_eq_one (11650 : ZMod 15053)
      decide
    · apply IsUnit.of_mul_eq_one (1120 : ZMod 15053)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15061 : Nat.Prime 15061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15061 15060 1 2 [2, 2, 3, 5, 251]
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
    · apply IsUnit.of_mul_eq_one (7530 : ZMod 15061)
      decide
    · apply IsUnit.of_mul_eq_one (394 : ZMod 15061)
      decide
    · apply IsUnit.of_mul_eq_one (13891 : ZMod 15061)
      decide
    · apply IsUnit.of_mul_eq_one (4145 : ZMod 15061)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15073 : Nat.Prime 15073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15073 15072 1 5 [2, 2, 2, 2, 2, 3, 157]
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
    · apply IsUnit.of_mul_eq_one (7536 : ZMod 15073)
      decide
    · apply IsUnit.of_mul_eq_one (12768 : ZMod 15073)
      decide
    · apply IsUnit.of_mul_eq_one (603 : ZMod 15073)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15077 : Nat.Prime 15077 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15077 15076 1 2 [2, 2, 3769]
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
    · apply IsUnit.of_mul_eq_one (7538 : ZMod 15077)
      decide
    · apply IsUnit.of_mul_eq_one (7036 : ZMod 15077)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15083 : Nat.Prime 15083 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15083 15082 1 2 [2, 7541]
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
    · apply IsUnit.of_mul_eq_one (7541 : ZMod 15083)
      decide
    · apply IsUnit.of_mul_eq_one (5028 : ZMod 15083)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by exact lowPrime_15013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by exact lowPrime_15017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by exact lowPrime_15031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by exact lowPrime_15053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by exact lowPrime_15061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by exact lowPrime_15073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by exact lowPrime_15077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by exact lowPrime_15083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part04_chain :
    DusartPrimeRowsChain 14983 15082 dusartPrimeRows_14767_15526_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]
