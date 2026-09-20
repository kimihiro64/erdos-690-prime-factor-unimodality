import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 42 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5851 : Nat.Prime 5851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5851 5850 1 2 [2, 3, 3, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (2925 : ZMod 5851)
      decide
    · apply IsUnit.of_mul_eq_one (192 : ZMod 5851)
      decide
    · apply IsUnit.of_mul_eq_one (3802 : ZMod 5851)
      decide
    · apply IsUnit.of_mul_eq_one (1328 : ZMod 5851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5857 : Nat.Prime 5857 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5857 5856 1 7 [2, 2, 2, 2, 2, 3, 61]
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
    · apply IsUnit.of_mul_eq_one (2928 : ZMod 5857)
      decide
    · apply IsUnit.of_mul_eq_one (421 : ZMod 5857)
      decide
    · apply IsUnit.of_mul_eq_one (353 : ZMod 5857)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5861 : Nat.Prime 5861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5861 5860 1 3 [2, 2, 5, 293]
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
    · apply IsUnit.of_mul_eq_one (2930 : ZMod 5861)
      decide
    · apply IsUnit.of_mul_eq_one (1431 : ZMod 5861)
      decide
    · apply IsUnit.of_mul_eq_one (5066 : ZMod 5861)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5867 : Nat.Prime 5867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5867 5866 1 5 [2, 7, 419]
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
    · apply IsUnit.of_mul_eq_one (2933 : ZMod 5867)
      decide
    · apply IsUnit.of_mul_eq_one (3478 : ZMod 5867)
      decide
    · apply IsUnit.of_mul_eq_one (1830 : ZMod 5867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5869 : Nat.Prime 5869 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5869 5868 1 2 [2, 2, 3, 3, 163]
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
    · apply IsUnit.of_mul_eq_one (2934 : ZMod 5869)
      decide
    · apply IsUnit.of_mul_eq_one (2215 : ZMod 5869)
      decide
    · apply IsUnit.of_mul_eq_one (2197 : ZMod 5869)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5879 : Nat.Prime 5879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5879 5878 1 11 [2, 2939]
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
    · apply IsUnit.of_mul_eq_one (2939 : ZMod 5879)
      decide
    · apply IsUnit.of_mul_eq_one (49 : ZMod 5879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5881 : Nat.Prime 5881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5881 5880 1 31 [2, 2, 2, 3, 5, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (2940 : ZMod 5881)
      decide
    · apply IsUnit.of_mul_eq_one (2052 : ZMod 5881)
      decide
    · apply IsUnit.of_mul_eq_one (2343 : ZMod 5881)
      decide
    · apply IsUnit.of_mul_eq_one (4443 : ZMod 5881)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5897 : Nat.Prime 5897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5897 5896 1 3 [2, 2, 2, 11, 67]
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
    · apply IsUnit.of_mul_eq_one (2948 : ZMod 5897)
      decide
    · apply IsUnit.of_mul_eq_one (1122 : ZMod 5897)
      decide
    · apply IsUnit.of_mul_eq_one (2050 : ZMod 5897)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by exact lowPrime_5851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by exact lowPrime_5857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by exact lowPrime_5861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by exact lowPrime_5867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by exact lowPrime_5869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by exact lowPrime_5879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by exact lowPrime_5881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by exact lowPrime_5897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part03_chain :
    DusartPrimeRowsChain 5849 5896 dusartPrimeRows_5711_6006_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6002, dusartPrimeRow_of_explicit_right]
