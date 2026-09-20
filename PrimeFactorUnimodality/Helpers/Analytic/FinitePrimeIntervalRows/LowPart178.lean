import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 178 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15299 : Nat.Prime 15299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15299 15298 1 2 [2, 7649]
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
    · apply IsUnit.of_mul_eq_one (7649 : ZMod 15299)
      decide
    · apply IsUnit.of_mul_eq_one (5100 : ZMod 15299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15307 : Nat.Prime 15307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15307 15306 1 3 [2, 3, 2551]
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
    · apply IsUnit.of_mul_eq_one (7653 : ZMod 15307)
      decide
    · apply IsUnit.of_mul_eq_one (11720 : ZMod 15307)
      decide
    · apply IsUnit.of_mul_eq_one (12889 : ZMod 15307)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15313 : Nat.Prime 15313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15313 15312 1 5 [2, 2, 2, 2, 3, 11, 29]
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
    · apply IsUnit.of_mul_eq_one (7656 : ZMod 15313)
      decide
    · apply IsUnit.of_mul_eq_one (7935 : ZMod 15313)
      decide
    · apply IsUnit.of_mul_eq_one (3590 : ZMod 15313)
      decide
    · apply IsUnit.of_mul_eq_one (6014 : ZMod 15313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15319 : Nat.Prime 15319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15319 15318 1 3 [2, 3, 3, 23, 37]
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
    · apply IsUnit.of_mul_eq_one (7659 : ZMod 15319)
      decide
    · apply IsUnit.of_mul_eq_one (10392 : ZMod 15319)
      decide
    · apply IsUnit.of_mul_eq_one (7685 : ZMod 15319)
      decide
    · apply IsUnit.of_mul_eq_one (4743 : ZMod 15319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15329 : Nat.Prime 15329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15329 15328 1 3 [2, 2, 2, 2, 2, 479]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (7664 : ZMod 15329)
      decide
    · apply IsUnit.of_mul_eq_one (14492 : ZMod 15329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15331 : Nat.Prime 15331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15331 15330 1 2 [2, 3, 5, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (7665 : ZMod 15331)
      decide
    · apply IsUnit.of_mul_eq_one (1123 : ZMod 15331)
      decide
    · apply IsUnit.of_mul_eq_one (12329 : ZMod 15331)
      decide
    · apply IsUnit.of_mul_eq_one (7461 : ZMod 15331)
      decide
    · apply IsUnit.of_mul_eq_one (6453 : ZMod 15331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15349 : Nat.Prime 15349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15349 15348 1 2 [2, 2, 3, 1279]
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
    · apply IsUnit.of_mul_eq_one (7674 : ZMod 15349)
      decide
    · apply IsUnit.of_mul_eq_one (2182 : ZMod 15349)
      decide
    · apply IsUnit.of_mul_eq_one (4764 : ZMod 15349)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15359 : Nat.Prime 15359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15359 15358 1 11 [2, 7, 1097]
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
    · apply IsUnit.of_mul_eq_one (7679 : ZMod 15359)
      decide
    · apply IsUnit.of_mul_eq_one (416 : ZMod 15359)
      decide
    · apply IsUnit.of_mul_eq_one (5947 : ZMod 15359)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by exact lowPrime_15299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by exact lowPrime_15307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by exact lowPrime_15313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by exact lowPrime_15319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by exact lowPrime_15329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by exact lowPrime_15331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by exact lowPrime_15349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by exact lowPrime_15359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part08_chain :
    DusartPrimeRowsChain 15289 15358 dusartPrimeRows_14767_15526_part08 := by
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
