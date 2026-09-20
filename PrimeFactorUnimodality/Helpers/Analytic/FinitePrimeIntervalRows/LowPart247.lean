import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 247 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19069 : Nat.Prime 19069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19069 19068 1 2 [2, 2, 3, 7, 227]
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
    · apply IsUnit.of_mul_eq_one (9534 : ZMod 19069)
      decide
    · apply IsUnit.of_mul_eq_one (7307 : ZMod 19069)
      decide
    · apply IsUnit.of_mul_eq_one (16617 : ZMod 19069)
      decide
    · apply IsUnit.of_mul_eq_one (12176 : ZMod 19069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19073 : Nat.Prime 19073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19073 19072 1 3 [2, 2, 2, 2, 2, 2, 2, 149]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (9536 : ZMod 19073)
      decide
    · apply IsUnit.of_mul_eq_one (1510 : ZMod 19073)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19079 : Nat.Prime 19079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19079 19078 1 7 [2, 9539]
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
    · apply IsUnit.of_mul_eq_one (9539 : ZMod 19079)
      decide
    · apply IsUnit.of_mul_eq_one (9937 : ZMod 19079)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19081 : Nat.Prime 19081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19081 19080 1 17 [2, 2, 2, 3, 3, 5, 53]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9540 : ZMod 19081)
      decide
    · apply IsUnit.of_mul_eq_one (4717 : ZMod 19081)
      decide
    · apply IsUnit.of_mul_eq_one (3487 : ZMod 19081)
      decide
    · apply IsUnit.of_mul_eq_one (1196 : ZMod 19081)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19087 : Nat.Prime 19087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19087 19086 1 19 [2, 3, 3181]
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
    · apply IsUnit.of_mul_eq_one (9543 : ZMod 19087)
      decide
    · apply IsUnit.of_mul_eq_one (5065 : ZMod 19087)
      decide
    · apply IsUnit.of_mul_eq_one (7197 : ZMod 19087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19121 : Nat.Prime 19121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19121 19120 1 6 [2, 2, 2, 2, 5, 239]
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
    · apply IsUnit.of_mul_eq_one (9560 : ZMod 19121)
      decide
    · apply IsUnit.of_mul_eq_one (8245 : ZMod 19121)
      decide
    · apply IsUnit.of_mul_eq_one (133 : ZMod 19121)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19139 : Nat.Prime 19139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19139 19138 1 2 [2, 7, 1367]
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
    · apply IsUnit.of_mul_eq_one (9569 : ZMod 19139)
      decide
    · apply IsUnit.of_mul_eq_one (9771 : ZMod 19139)
      decide
    · apply IsUnit.of_mul_eq_one (9632 : ZMod 19139)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19141 : Nat.Prime 19141 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19141 19140 1 2 [2, 2, 3, 5, 11, 29]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9570 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (9426 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (14590 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (5765 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (14172 : ZMod 19141)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19051) (q := 19069) (by exact lowPrime_19069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19069) (q := 19073) (by exact lowPrime_19073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19073) (q := 19079) (by exact lowPrime_19079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19079) (q := 19081) (by exact lowPrime_19081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19081) (q := 19087) (by exact lowPrime_19087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19087) (q := 19121) (by exact lowPrime_19121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19121) (q := 19139) (by exact lowPrime_19139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19139) (q := 19141) (by exact lowPrime_19141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part02_chain :
    DusartPrimeRowsChain 19051 19140 dusartPrimeRows_18959_19936_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
