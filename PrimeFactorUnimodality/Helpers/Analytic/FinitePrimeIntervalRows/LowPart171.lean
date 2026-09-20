import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 171 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14771 : Nat.Prime 14771 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14771 14770 1 2 [2, 5, 7, 211]
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
    · apply IsUnit.of_mul_eq_one (7385 : ZMod 14771)
      decide
    · apply IsUnit.of_mul_eq_one (4762 : ZMod 14771)
      decide
    · apply IsUnit.of_mul_eq_one (12421 : ZMod 14771)
      decide
    · apply IsUnit.of_mul_eq_one (613 : ZMod 14771)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14779 : Nat.Prime 14779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14779 14778 1 3 [2, 3, 3, 821]
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
    · apply IsUnit.of_mul_eq_one (7389 : ZMod 14779)
      decide
    · apply IsUnit.of_mul_eq_one (2229 : ZMod 14779)
      decide
    · apply IsUnit.of_mul_eq_one (2075 : ZMod 14779)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14783 : Nat.Prime 14783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14783 14782 1 5 [2, 19, 389]
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
    · apply IsUnit.of_mul_eq_one (7391 : ZMod 14783)
      decide
    · apply IsUnit.of_mul_eq_one (2389 : ZMod 14783)
      decide
    · apply IsUnit.of_mul_eq_one (10717 : ZMod 14783)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14797 : Nat.Prime 14797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14797 14796 1 2 [2, 2, 3, 3, 3, 137]
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
    · apply IsUnit.of_mul_eq_one (7398 : ZMod 14797)
      decide
    · apply IsUnit.of_mul_eq_one (4648 : ZMod 14797)
      decide
    · apply IsUnit.of_mul_eq_one (4826 : ZMod 14797)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14813 : Nat.Prime 14813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14813 14812 1 2 [2, 2, 7, 23, 23]
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
    · apply IsUnit.of_mul_eq_one (7406 : ZMod 14813)
      decide
    · apply IsUnit.of_mul_eq_one (10548 : ZMod 14813)
      decide
    · apply IsUnit.of_mul_eq_one (13469 : ZMod 14813)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14821 : Nat.Prime 14821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14821 14820 1 2 [2, 2, 3, 5, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (7410 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (14150 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (4607 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (6641 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (9334 : ZMod 14821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14827 : Nat.Prime 14827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14827 14826 1 2 [2, 3, 7, 353]
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
    · apply IsUnit.of_mul_eq_one (7413 : ZMod 14827)
      decide
    · apply IsUnit.of_mul_eq_one (7320 : ZMod 14827)
      decide
    · apply IsUnit.of_mul_eq_one (6715 : ZMod 14827)
      decide
    · apply IsUnit.of_mul_eq_one (9274 : ZMod 14827)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14831 : Nat.Prime 14831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14831 14830 1 11 [2, 5, 1483]
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
    · apply IsUnit.of_mul_eq_one (7415 : ZMod 14831)
      decide
    · apply IsUnit.of_mul_eq_one (11829 : ZMod 14831)
      decide
    · apply IsUnit.of_mul_eq_one (13667 : ZMod 14831)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by exact lowPrime_14771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by exact lowPrime_14779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by exact lowPrime_14783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by exact lowPrime_14797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by exact lowPrime_14813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by exact lowPrime_14821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by exact lowPrime_14827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by exact lowPrime_14831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part01_chain :
    DusartPrimeRowsChain 14767 14830 dusartPrimeRows_14767_15526_part01 := by
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
