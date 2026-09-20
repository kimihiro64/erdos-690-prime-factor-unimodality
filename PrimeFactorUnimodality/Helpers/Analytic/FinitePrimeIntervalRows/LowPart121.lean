import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 121 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11173 : Nat.Prime 11173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11173 11172 1 5 [2, 2, 3, 7, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (5586 : ZMod 11173)
      decide
    · apply IsUnit.of_mul_eq_one (8794 : ZMod 11173)
      decide
    · apply IsUnit.of_mul_eq_one (9650 : ZMod 11173)
      decide
    · apply IsUnit.of_mul_eq_one (10143 : ZMod 11173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11177 : Nat.Prime 11177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11177 11176 1 3 [2, 2, 2, 11, 127]
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
    · apply IsUnit.of_mul_eq_one (5588 : ZMod 11177)
      decide
    · apply IsUnit.of_mul_eq_one (8554 : ZMod 11177)
      decide
    · apply IsUnit.of_mul_eq_one (2494 : ZMod 11177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11197 : Nat.Prime 11197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11197 11196 1 2 [2, 2, 3, 3, 311]
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
    · apply IsUnit.of_mul_eq_one (5598 : ZMod 11197)
      decide
    · apply IsUnit.of_mul_eq_one (9729 : ZMod 11197)
      decide
    · apply IsUnit.of_mul_eq_one (858 : ZMod 11197)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11213 : Nat.Prime 11213 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11213 11212 1 2 [2, 2, 2803]
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
    · apply IsUnit.of_mul_eq_one (5606 : ZMod 11213)
      decide
    · apply IsUnit.of_mul_eq_one (9718 : ZMod 11213)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11239 : Nat.Prime 11239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11239 11238 1 3 [2, 3, 1873]
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
    · apply IsUnit.of_mul_eq_one (5619 : ZMod 11239)
      decide
    · apply IsUnit.of_mul_eq_one (1855 : ZMod 11239)
      decide
    · apply IsUnit.of_mul_eq_one (1374 : ZMod 11239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11243 : Nat.Prime 11243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11243 11242 1 5 [2, 7, 11, 73]
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
    · apply IsUnit.of_mul_eq_one (5621 : ZMod 11243)
      decide
    · apply IsUnit.of_mul_eq_one (2575 : ZMod 11243)
      decide
    · apply IsUnit.of_mul_eq_one (1875 : ZMod 11243)
      decide
    · apply IsUnit.of_mul_eq_one (4369 : ZMod 11243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11251 : Nat.Prime 11251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11251 11250 1 13 [2, 3, 3, 5, 5, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (5625 : ZMod 11251)
      decide
    · apply IsUnit.of_mul_eq_one (3391 : ZMod 11251)
      decide
    · apply IsUnit.of_mul_eq_one (9241 : ZMod 11251)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11257 : Nat.Prime 11257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11257 11256 1 10 [2, 2, 2, 3, 7, 67]
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
    · apply IsUnit.of_mul_eq_one (5628 : ZMod 11257)
      decide
    · apply IsUnit.of_mul_eq_one (1440 : ZMod 11257)
      decide
    · apply IsUnit.of_mul_eq_one (7209 : ZMod 11257)
      decide
    · apply IsUnit.of_mul_eq_one (5797 : ZMod 11257)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by exact lowPrime_11173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by exact lowPrime_11177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by exact lowPrime_11197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by exact lowPrime_11213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by exact lowPrime_11239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by exact lowPrime_11243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by exact lowPrime_11251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by exact lowPrime_11257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part04_chain :
    DusartPrimeRowsChain 11171 11256 dusartPrimeRows_10939_11502_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]
