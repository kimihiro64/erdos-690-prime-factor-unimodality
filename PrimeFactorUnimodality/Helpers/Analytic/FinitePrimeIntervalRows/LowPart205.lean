import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 205 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22091 : Nat.Prime 22091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22091 22090 1 2 [2, 5, 47, 47]
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
    · apply IsUnit.of_mul_eq_one (11045 : ZMod 22091)
      decide
    · apply IsUnit.of_mul_eq_one (13199 : ZMod 22091)
      decide
    · apply IsUnit.of_mul_eq_one (19591 : ZMod 22091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22093 : Nat.Prime 22093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22093 22092 1 6 [2, 2, 3, 7, 263]
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
    · apply IsUnit.of_mul_eq_one (11046 : ZMod 22093)
      decide
    · apply IsUnit.of_mul_eq_one (12441 : ZMod 22093)
      decide
    · apply IsUnit.of_mul_eq_one (6467 : ZMod 22093)
      decide
    · apply IsUnit.of_mul_eq_one (4244 : ZMod 22093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22109 : Nat.Prime 22109 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22109 22108 1 2 [2, 2, 5527]
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
    · apply IsUnit.of_mul_eq_one (11054 : ZMod 22109)
      decide
    · apply IsUnit.of_mul_eq_one (1474 : ZMod 22109)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22111 : Nat.Prime 22111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22111 22110 1 6 [2, 3, 5, 11, 67]
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
    · apply IsUnit.of_mul_eq_one (11055 : ZMod 22111)
      decide
    · apply IsUnit.of_mul_eq_one (19491 : ZMod 22111)
      decide
    · apply IsUnit.of_mul_eq_one (4495 : ZMod 22111)
      decide
    · apply IsUnit.of_mul_eq_one (11410 : ZMod 22111)
      decide
    · apply IsUnit.of_mul_eq_one (13421 : ZMod 22111)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22123 : Nat.Prime 22123 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22123 22122 1 2 [2, 3, 3, 1229]
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
    · apply IsUnit.of_mul_eq_one (11061 : ZMod 22123)
      decide
    · apply IsUnit.of_mul_eq_one (19199 : ZMod 22123)
      decide
    · apply IsUnit.of_mul_eq_one (6538 : ZMod 22123)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22129 : Nat.Prime 22129 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22129 22128 1 19 [2, 2, 2, 2, 3, 461]
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
    · apply IsUnit.of_mul_eq_one (11064 : ZMod 22129)
      decide
    · apply IsUnit.of_mul_eq_one (13918 : ZMod 22129)
      decide
    · apply IsUnit.of_mul_eq_one (4478 : ZMod 22129)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22133 : Nat.Prime 22133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22133 22132 1 2 [2, 2, 11, 503]
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
    · apply IsUnit.of_mul_eq_one (11066 : ZMod 22133)
      decide
    · apply IsUnit.of_mul_eq_one (11868 : ZMod 22133)
      decide
    · apply IsUnit.of_mul_eq_one (15274 : ZMod 22133)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22147 : Nat.Prime 22147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22147 22146 1 5 [2, 3, 3691]
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
    · apply IsUnit.of_mul_eq_one (11073 : ZMod 22147)
      decide
    · apply IsUnit.of_mul_eq_one (11896 : ZMod 22147)
      decide
    · apply IsUnit.of_mul_eq_one (8376 : ZMod 22147)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by exact lowPrime_22091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by exact lowPrime_22093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by exact lowPrime_22109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by exact lowPrime_22111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by exact lowPrime_22123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by exact lowPrime_22129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by exact lowPrime_22133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by exact lowPrime_22147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part02_chain :
    DusartPrimeRowsChain 22079 22146 dusartPrimeRows_22027_23158_part02 := by
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
