import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 02 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3343 : Nat.Prime 3343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3343 3342 1 5 [2, 3, 557]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 3343) ^ 1671 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1671 : ZMod 3343)
      decide
    · change IsUnit ((5 : ZMod 3343) ^ 1114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2703 : ZMod 3343)
      decide
    · change IsUnit ((5 : ZMod 3343) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1385 : ZMod 3343)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3347 : Nat.Prime 3347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3347 3346 1 2 [2, 7, 239]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3347) ^ 1673 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1673 : ZMod 3347)
      decide
    · change IsUnit ((2 : ZMod 3347) ^ 478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2540 : ZMod 3347)
      decide
    · change IsUnit ((2 : ZMod 3347) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (561 : ZMod 3347)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3359 : Nat.Prime 3359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3359 3358 1 11 [2, 23, 73]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 3359) ^ 1679 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1679 : ZMod 3359)
      decide
    · change IsUnit ((11 : ZMod 3359) ^ 146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2555 : ZMod 3359)
      decide
    · change IsUnit ((11 : ZMod 3359) ^ 46 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1249 : ZMod 3359)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3361 : Nat.Prime 3361 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3361 3360 1 22 [2, 2, 2, 2, 2, 3, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((22 : ZMod 3361) ^ 1680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1680 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 1680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1680 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 1680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1680 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 1680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1680 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 1680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1680 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 1120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (297 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 672 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3209 : ZMod 3361)
      decide
    · change IsUnit ((22 : ZMod 3361) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (917 : ZMod 3361)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3371 : Nat.Prime 3371 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3371 3370 1 2 [2, 5, 337]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3371) ^ 1685 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1685 : ZMod 3371)
      decide
    · change IsUnit ((2 : ZMod 3371) ^ 674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1563 : ZMod 3371)
      decide
    · change IsUnit ((2 : ZMod 3371) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1239 : ZMod 3371)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3373 : Nat.Prime 3373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3373 3372 1 5 [2, 2, 3, 281]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 3373) ^ 1686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1686 : ZMod 3373)
      decide
    · change IsUnit ((5 : ZMod 3373) ^ 1686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1686 : ZMod 3373)
      decide
    · change IsUnit ((5 : ZMod 3373) ^ 1124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1342 : ZMod 3373)
      decide
    · change IsUnit ((5 : ZMod 3373) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (607 : ZMod 3373)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3389 : Nat.Prime 3389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3389 3388 1 3 [2, 2, 7, 11, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 3389) ^ 1694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1694 : ZMod 3389)
      decide
    · change IsUnit ((3 : ZMod 3389) ^ 1694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1694 : ZMod 3389)
      decide
    · change IsUnit ((3 : ZMod 3389) ^ 484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1341 : ZMod 3389)
      decide
    · change IsUnit ((3 : ZMod 3389) ^ 308 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1674 : ZMod 3389)
      decide
    · change IsUnit ((3 : ZMod 3389) ^ 308 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1674 : ZMod 3389)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3391 : Nat.Prime 3391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3391 3390 1 3 [2, 3, 5, 113]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 3391) ^ 1695 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1695 : ZMod 3391)
      decide
    · change IsUnit ((3 : ZMod 3391) ^ 1130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1315 : ZMod 3391)
      decide
    · change IsUnit ((3 : ZMod 3391) ^ 678 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1689 : ZMod 3391)
      decide
    · change IsUnit ((3 : ZMod 3391) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2710 : ZMod 3391)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by exact lowPrime_3343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by exact lowPrime_3347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by exact lowPrime_3359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by exact lowPrime_3361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by exact lowPrime_3371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by exact lowPrime_3373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by exact lowPrime_3389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by exact lowPrime_3391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part02_chain :
    DusartPrimeRowsChain 3331 3391 dusartPrimeRows_3275_3802_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num
