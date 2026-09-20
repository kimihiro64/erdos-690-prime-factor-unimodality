import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 37 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5569 : Nat.Prime 5569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5569 5568 1 13 [2, 2, 2, 2, 2, 2, 3, 29]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2784 : ZMod 5569)
      decide
    · apply IsUnit.of_mul_eq_one (4821 : ZMod 5569)
      decide
    · apply IsUnit.of_mul_eq_one (996 : ZMod 5569)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5573 : Nat.Prime 5573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5573 5572 1 2 [2, 2, 7, 199]
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
    · apply IsUnit.of_mul_eq_one (2786 : ZMod 5573)
      decide
    · apply IsUnit.of_mul_eq_one (388 : ZMod 5573)
      decide
    · apply IsUnit.of_mul_eq_one (3319 : ZMod 5573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5581 : Nat.Prime 5581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5581 5580 1 6 [2, 2, 3, 3, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (2790 : ZMod 5581)
      decide
    · apply IsUnit.of_mul_eq_one (4761 : ZMod 5581)
      decide
    · apply IsUnit.of_mul_eq_one (3507 : ZMod 5581)
      decide
    · apply IsUnit.of_mul_eq_one (2354 : ZMod 5581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5591 : Nat.Prime 5591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5591 5590 1 11 [2, 5, 13, 43]
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
    · apply IsUnit.of_mul_eq_one (2795 : ZMod 5591)
      decide
    · apply IsUnit.of_mul_eq_one (4696 : ZMod 5591)
      decide
    · apply IsUnit.of_mul_eq_one (3478 : ZMod 5591)
      decide
    · apply IsUnit.of_mul_eq_one (1124 : ZMod 5591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5623 : Nat.Prime 5623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5623 5622 1 5 [2, 3, 937]
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
    · apply IsUnit.of_mul_eq_one (2811 : ZMod 5623)
      decide
    · apply IsUnit.of_mul_eq_one (3077 : ZMod 5623)
      decide
    · apply IsUnit.of_mul_eq_one (2606 : ZMod 5623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5639 : Nat.Prime 5639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5639 5638 1 7 [2, 2819]
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
    · apply IsUnit.of_mul_eq_one (2819 : ZMod 5639)
      decide
    · apply IsUnit.of_mul_eq_one (2937 : ZMod 5639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5641 : Nat.Prime 5641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5641 5640 1 14 [2, 2, 2, 3, 5, 47]
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
    · apply IsUnit.of_mul_eq_one (2820 : ZMod 5641)
      decide
    · apply IsUnit.of_mul_eq_one (681 : ZMod 5641)
      decide
    · apply IsUnit.of_mul_eq_one (4332 : ZMod 5641)
      decide
    · apply IsUnit.of_mul_eq_one (977 : ZMod 5641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5647 : Nat.Prime 5647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5647 5646 1 3 [2, 3, 941]
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
    · apply IsUnit.of_mul_eq_one (2823 : ZMod 5647)
      decide
    · apply IsUnit.of_mul_eq_one (5362 : ZMod 5647)
      decide
    · apply IsUnit.of_mul_eq_one (3669 : ZMod 5647)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by exact lowPrime_5569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by exact lowPrime_5573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by exact lowPrime_5581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by exact lowPrime_5591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by exact lowPrime_5623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by exact lowPrime_5639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by exact lowPrime_5641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by exact lowPrime_5647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part03_chain :
    DusartPrimeRowsChain 5563 5646 dusartPrimeRows_5437_5710_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]
