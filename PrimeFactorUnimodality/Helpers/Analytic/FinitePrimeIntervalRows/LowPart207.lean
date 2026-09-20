import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 207 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22259 : Nat.Prime 22259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22259 22258 1 2 [2, 31, 359]
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
    · apply IsUnit.of_mul_eq_one (11129 : ZMod 22259)
      decide
    · apply IsUnit.of_mul_eq_one (13068 : ZMod 22259)
      decide
    · apply IsUnit.of_mul_eq_one (20668 : ZMod 22259)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22271 : Nat.Prime 22271 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22271 22270 1 7 [2, 5, 17, 131]
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
    · apply IsUnit.of_mul_eq_one (11135 : ZMod 22271)
      decide
    · apply IsUnit.of_mul_eq_one (20357 : ZMod 22271)
      decide
    · apply IsUnit.of_mul_eq_one (16307 : ZMod 22271)
      decide
    · apply IsUnit.of_mul_eq_one (10649 : ZMod 22271)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22273 : Nat.Prime 22273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22273 22272 1 5 [2, 2, 2, 2, 2, 2, 2, 2, 3, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (11136 : ZMod 22273)
      decide
    · apply IsUnit.of_mul_eq_one (4211 : ZMod 22273)
      decide
    · apply IsUnit.of_mul_eq_one (527 : ZMod 22273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22277 : Nat.Prime 22277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22277 22276 1 2 [2, 2, 5569]
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
    · apply IsUnit.of_mul_eq_one (11138 : ZMod 22277)
      decide
    · apply IsUnit.of_mul_eq_one (10396 : ZMod 22277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22279 : Nat.Prime 22279 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22279 22278 1 3 [2, 3, 47, 79]
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
    · apply IsUnit.of_mul_eq_one (11139 : ZMod 22279)
      decide
    · apply IsUnit.of_mul_eq_one (11025 : ZMod 22279)
      decide
    · apply IsUnit.of_mul_eq_one (4178 : ZMod 22279)
      decide
    · apply IsUnit.of_mul_eq_one (246 : ZMod 22279)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22283 : Nat.Prime 22283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22283 22282 1 2 [2, 13, 857]
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
    · apply IsUnit.of_mul_eq_one (11141 : ZMod 22283)
      decide
    · apply IsUnit.of_mul_eq_one (15929 : ZMod 22283)
      decide
    · apply IsUnit.of_mul_eq_one (20097 : ZMod 22283)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22291 : Nat.Prime 22291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22291 22290 1 3 [2, 3, 5, 743]
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
    · apply IsUnit.of_mul_eq_one (11145 : ZMod 22291)
      decide
    · apply IsUnit.of_mul_eq_one (20400 : ZMod 22291)
      decide
    · apply IsUnit.of_mul_eq_one (8415 : ZMod 22291)
      decide
    · apply IsUnit.of_mul_eq_one (353 : ZMod 22291)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22303 : Nat.Prime 22303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22303 22302 1 6 [2, 3, 3, 3, 7, 59]
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
    · apply IsUnit.of_mul_eq_one (11151 : ZMod 22303)
      decide
    · apply IsUnit.of_mul_eq_one (14591 : ZMod 22303)
      decide
    · apply IsUnit.of_mul_eq_one (5281 : ZMod 22303)
      decide
    · apply IsUnit.of_mul_eq_one (3015 : ZMod 22303)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by exact lowPrime_22259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by exact lowPrime_22271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by exact lowPrime_22273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by exact lowPrime_22277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by exact lowPrime_22279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by exact lowPrime_22283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by exact lowPrime_22291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by exact lowPrime_22303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part04_chain :
    DusartPrimeRowsChain 22247 22302 dusartPrimeRows_22027_23158_part04 := by
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
