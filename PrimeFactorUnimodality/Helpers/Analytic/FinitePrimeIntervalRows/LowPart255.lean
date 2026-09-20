import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 255 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19697 : Nat.Prime 19697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19697 19696 1 3 [2, 2, 2, 2, 1231]
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
    · apply IsUnit.of_mul_eq_one (9848 : ZMod 19697)
      decide
    · apply IsUnit.of_mul_eq_one (2844 : ZMod 19697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19699 : Nat.Prime 19699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19699 19698 1 7 [2, 3, 7, 7, 67]
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
    · apply IsUnit.of_mul_eq_one (9849 : ZMod 19699)
      decide
    · apply IsUnit.of_mul_eq_one (2472 : ZMod 19699)
      decide
    · apply IsUnit.of_mul_eq_one (5376 : ZMod 19699)
      decide
    · apply IsUnit.of_mul_eq_one (15503 : ZMod 19699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19709 : Nat.Prime 19709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19709 19708 1 2 [2, 2, 13, 379]
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
    · apply IsUnit.of_mul_eq_one (9854 : ZMod 19709)
      decide
    · apply IsUnit.of_mul_eq_one (15451 : ZMod 19709)
      decide
    · apply IsUnit.of_mul_eq_one (11285 : ZMod 19709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19717 : Nat.Prime 19717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19717 19716 1 2 [2, 2, 3, 31, 53]
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
    · apply IsUnit.of_mul_eq_one (9858 : ZMod 19717)
      decide
    · apply IsUnit.of_mul_eq_one (17567 : ZMod 19717)
      decide
    · apply IsUnit.of_mul_eq_one (1846 : ZMod 19717)
      decide
    · apply IsUnit.of_mul_eq_one (4123 : ZMod 19717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19727 : Nat.Prime 19727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19727 19726 1 5 [2, 7, 1409]
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
    · apply IsUnit.of_mul_eq_one (9863 : ZMod 19727)
      decide
    · apply IsUnit.of_mul_eq_one (1401 : ZMod 19727)
      decide
    · apply IsUnit.of_mul_eq_one (2760 : ZMod 19727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19739 : Nat.Prime 19739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19739 19738 1 2 [2, 71, 139]
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
    · apply IsUnit.of_mul_eq_one (9869 : ZMod 19739)
      decide
    · apply IsUnit.of_mul_eq_one (12852 : ZMod 19739)
      decide
    · apply IsUnit.of_mul_eq_one (15472 : ZMod 19739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19751 : Nat.Prime 19751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19751 19750 1 7 [2, 5, 5, 5, 79]
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
    · apply IsUnit.of_mul_eq_one (9875 : ZMod 19751)
      decide
    · apply IsUnit.of_mul_eq_one (18719 : ZMod 19751)
      decide
    · apply IsUnit.of_mul_eq_one (14019 : ZMod 19751)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19753 : Nat.Prime 19753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19753 19752 1 5 [2, 2, 2, 3, 823]
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
    · apply IsUnit.of_mul_eq_one (9876 : ZMod 19753)
      decide
    · apply IsUnit.of_mul_eq_one (17834 : ZMod 19753)
      decide
    · apply IsUnit.of_mul_eq_one (11041 : ZMod 19753)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19687) (q := 19697) (by exact lowPrime_19697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19697) (q := 19699) (by exact lowPrime_19699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19699) (q := 19709) (by exact lowPrime_19709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19709) (q := 19717) (by exact lowPrime_19717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19717) (q := 19727) (by exact lowPrime_19727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19727) (q := 19739) (by exact lowPrime_19739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19739) (q := 19751) (by exact lowPrime_19751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19751) (q := 19753) (by exact lowPrime_19753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part10_chain :
    DusartPrimeRowsChain 19687 19752 dusartPrimeRows_18959_19936_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
