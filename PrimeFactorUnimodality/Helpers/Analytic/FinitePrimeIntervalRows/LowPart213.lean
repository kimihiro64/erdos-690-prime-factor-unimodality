import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 213 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22727 : Nat.Prime 22727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22727 22726 1 5 [2, 11, 1033]
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
    · apply IsUnit.of_mul_eq_one (11363 : ZMod 22727)
      decide
    · apply IsUnit.of_mul_eq_one (204 : ZMod 22727)
      decide
    · apply IsUnit.of_mul_eq_one (3198 : ZMod 22727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22739 : Nat.Prime 22739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22739 22738 1 2 [2, 11369]
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
    · apply IsUnit.of_mul_eq_one (11369 : ZMod 22739)
      decide
    · apply IsUnit.of_mul_eq_one (7580 : ZMod 22739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22741 : Nat.Prime 22741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22741 22740 1 7 [2, 2, 3, 5, 379]
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
    · apply IsUnit.of_mul_eq_one (11370 : ZMod 22741)
      decide
    · apply IsUnit.of_mul_eq_one (11710 : ZMod 22741)
      decide
    · apply IsUnit.of_mul_eq_one (21469 : ZMod 22741)
      decide
    · apply IsUnit.of_mul_eq_one (5849 : ZMod 22741)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22751 : Nat.Prime 22751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22751 22750 1 21 [2, 5, 5, 5, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (11375 : ZMod 22751)
      decide
    · apply IsUnit.of_mul_eq_one (9314 : ZMod 22751)
      decide
    · apply IsUnit.of_mul_eq_one (18789 : ZMod 22751)
      decide
    · apply IsUnit.of_mul_eq_one (393 : ZMod 22751)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22769 : Nat.Prime 22769 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22769 22768 1 3 [2, 2, 2, 2, 1423]
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
    · apply IsUnit.of_mul_eq_one (11384 : ZMod 22769)
      decide
    · apply IsUnit.of_mul_eq_one (7905 : ZMod 22769)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22777 : Nat.Prime 22777 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22777 22776 1 7 [2, 2, 2, 3, 13, 73]
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
    · apply IsUnit.of_mul_eq_one (11388 : ZMod 22777)
      decide
    · apply IsUnit.of_mul_eq_one (14604 : ZMod 22777)
      decide
    · apply IsUnit.of_mul_eq_one (18627 : ZMod 22777)
      decide
    · apply IsUnit.of_mul_eq_one (4555 : ZMod 22777)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22783 : Nat.Prime 22783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22783 22782 1 3 [2, 3, 3797]
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
    · apply IsUnit.of_mul_eq_one (11391 : ZMod 22783)
      decide
    · apply IsUnit.of_mul_eq_one (7182 : ZMod 22783)
      decide
    · apply IsUnit.of_mul_eq_one (6040 : ZMod 22783)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22787 : Nat.Prime 22787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22787 22786 1 2 [2, 11393]
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
    · apply IsUnit.of_mul_eq_one (11393 : ZMod 22787)
      decide
    · apply IsUnit.of_mul_eq_one (7596 : ZMod 22787)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by exact lowPrime_22727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by exact lowPrime_22739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by exact lowPrime_22741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by exact lowPrime_22751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by exact lowPrime_22769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by exact lowPrime_22777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by exact lowPrime_22783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by exact lowPrime_22787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part10_chain :
    DusartPrimeRowsChain 22721 22786 dusartPrimeRows_22027_23158_part10 := by
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
