import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 04 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3469 : Nat.Prime 3469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3469 3468 1 2 [2, 2, 3, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (1734 : ZMod 3469)
      decide
    · apply IsUnit.of_mul_eq_one (1717 : ZMod 3469)
      decide
    · apply IsUnit.of_mul_eq_one (371 : ZMod 3469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3491 : Nat.Prime 3491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3491 3490 1 2 [2, 5, 349]
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
    · apply IsUnit.of_mul_eq_one (1745 : ZMod 3491)
      decide
    · apply IsUnit.of_mul_eq_one (1842 : ZMod 3491)
      decide
    · apply IsUnit.of_mul_eq_one (3218 : ZMod 3491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3499 : Nat.Prime 3499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3499 3498 1 2 [2, 3, 11, 53]
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
    · apply IsUnit.of_mul_eq_one (1749 : ZMod 3499)
      decide
    · apply IsUnit.of_mul_eq_one (2280 : ZMod 3499)
      decide
    · apply IsUnit.of_mul_eq_one (2443 : ZMod 3499)
      decide
    · apply IsUnit.of_mul_eq_one (747 : ZMod 3499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3511 : Nat.Prime 3511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3511 3510 1 7 [2, 3, 3, 3, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (1755 : ZMod 3511)
      decide
    · apply IsUnit.of_mul_eq_one (1422 : ZMod 3511)
      decide
    · apply IsUnit.of_mul_eq_one (1130 : ZMod 3511)
      decide
    · apply IsUnit.of_mul_eq_one (2165 : ZMod 3511)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3517 : Nat.Prime 3517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3517 3516 1 2 [2, 2, 3, 293]
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
    · apply IsUnit.of_mul_eq_one (1758 : ZMod 3517)
      decide
    · apply IsUnit.of_mul_eq_one (2258 : ZMod 3517)
      decide
    · apply IsUnit.of_mul_eq_one (3158 : ZMod 3517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3527 : Nat.Prime 3527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3527 3526 1 5 [2, 41, 43]
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
    · apply IsUnit.of_mul_eq_one (1763 : ZMod 3527)
      decide
    · apply IsUnit.of_mul_eq_one (1907 : ZMod 3527)
      decide
    · apply IsUnit.of_mul_eq_one (2318 : ZMod 3527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3529 : Nat.Prime 3529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3529 3528 1 17 [2, 2, 2, 3, 3, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (1764 : ZMod 3529)
      decide
    · apply IsUnit.of_mul_eq_one (149 : ZMod 3529)
      decide
    · apply IsUnit.of_mul_eq_one (257 : ZMod 3529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3533 : Nat.Prime 3533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3533 3532 1 2 [2, 2, 883]
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
    · apply IsUnit.of_mul_eq_one (1766 : ZMod 3533)
      decide
    · apply IsUnit.of_mul_eq_one (3062 : ZMod 3533)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by exact lowPrime_3469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by exact lowPrime_3491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by exact lowPrime_3499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by exact lowPrime_3511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by exact lowPrime_3517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by exact lowPrime_3527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by exact lowPrime_3529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by exact lowPrime_3533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part04_chain :
    DusartPrimeRowsChain 3467 3532 dusartPrimeRows_3275_3802_part04 := by
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
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]
