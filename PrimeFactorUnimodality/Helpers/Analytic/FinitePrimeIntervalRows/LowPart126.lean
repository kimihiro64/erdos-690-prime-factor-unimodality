import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 126 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11519 : Nat.Prime 11519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11519 11518 1 7 [2, 13, 443]
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
    · apply IsUnit.of_mul_eq_one (5759 : ZMod 11519)
      decide
    · apply IsUnit.of_mul_eq_one (258 : ZMod 11519)
      decide
    · apply IsUnit.of_mul_eq_one (3125 : ZMod 11519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11527 : Nat.Prime 11527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11527 11526 1 5 [2, 3, 17, 113]
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
    · apply IsUnit.of_mul_eq_one (5763 : ZMod 11527)
      decide
    · apply IsUnit.of_mul_eq_one (5845 : ZMod 11527)
      decide
    · apply IsUnit.of_mul_eq_one (7186 : ZMod 11527)
      decide
    · apply IsUnit.of_mul_eq_one (10095 : ZMod 11527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11549 : Nat.Prime 11549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11549 11548 1 2 [2, 2, 2887]
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
    · apply IsUnit.of_mul_eq_one (5774 : ZMod 11549)
      decide
    · apply IsUnit.of_mul_eq_one (770 : ZMod 11549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11551 : Nat.Prime 11551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11551 11550 1 7 [2, 3, 5, 5, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (5775 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (1326 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (268 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (5175 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (8688 : ZMod 11551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11579 : Nat.Prime 11579 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11579 11578 1 2 [2, 7, 827]
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
    · apply IsUnit.of_mul_eq_one (5789 : ZMod 11579)
      decide
    · apply IsUnit.of_mul_eq_one (8101 : ZMod 11579)
      decide
    · apply IsUnit.of_mul_eq_one (2297 : ZMod 11579)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11587 : Nat.Prime 11587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11587 11586 1 2 [2, 3, 1931]
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
    · apply IsUnit.of_mul_eq_one (5793 : ZMod 11587)
      decide
    · apply IsUnit.of_mul_eq_one (4113 : ZMod 11587)
      decide
    · apply IsUnit.of_mul_eq_one (6989 : ZMod 11587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11593 : Nat.Prime 11593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11593 11592 1 5 [2, 2, 2, 3, 3, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (5796 : ZMod 11593)
      decide
    · apply IsUnit.of_mul_eq_one (4421 : ZMod 11593)
      decide
    · apply IsUnit.of_mul_eq_one (2865 : ZMod 11593)
      decide
    · apply IsUnit.of_mul_eq_one (2459 : ZMod 11593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11597 : Nat.Prime 11597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11597 11596 1 3 [2, 2, 13, 223]
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
    · apply IsUnit.of_mul_eq_one (5798 : ZMod 11597)
      decide
    · apply IsUnit.of_mul_eq_one (7395 : ZMod 11597)
      decide
    · apply IsUnit.of_mul_eq_one (5676 : ZMod 11597)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by exact lowPrime_11519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by exact lowPrime_11527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by exact lowPrime_11549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by exact lowPrime_11551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by exact lowPrime_11579) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by exact lowPrime_11587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by exact lowPrime_11593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by exact lowPrime_11597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part01_chain :
    DusartPrimeRowsChain 11503 11596 dusartPrimeRows_11503_12096_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]
