import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 41 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5801 : Nat.Prime 5801 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5801 5800 1 3 [2, 2, 2, 5, 5, 29]
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
    · apply IsUnit.of_mul_eq_one (2900 : ZMod 5801)
      decide
    · apply IsUnit.of_mul_eq_one (3738 : ZMod 5801)
      decide
    · apply IsUnit.of_mul_eq_one (3226 : ZMod 5801)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5807 : Nat.Prime 5807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5807 5806 1 5 [2, 2903]
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
    · apply IsUnit.of_mul_eq_one (2903 : ZMod 5807)
      decide
    · apply IsUnit.of_mul_eq_one (242 : ZMod 5807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5813 : Nat.Prime 5813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5813 5812 1 2 [2, 2, 1453]
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
    · apply IsUnit.of_mul_eq_one (2906 : ZMod 5813)
      decide
    · apply IsUnit.of_mul_eq_one (5038 : ZMod 5813)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5821 : Nat.Prime 5821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5821 5820 1 6 [2, 2, 3, 5, 97]
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
    · apply IsUnit.of_mul_eq_one (2910 : ZMod 5821)
      decide
    · apply IsUnit.of_mul_eq_one (3164 : ZMod 5821)
      decide
    · apply IsUnit.of_mul_eq_one (5019 : ZMod 5821)
      decide
    · apply IsUnit.of_mul_eq_one (2677 : ZMod 5821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5827 : Nat.Prime 5827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5827 5826 1 2 [2, 3, 971]
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
    · apply IsUnit.of_mul_eq_one (2913 : ZMod 5827)
      decide
    · apply IsUnit.of_mul_eq_one (3434 : ZMod 5827)
      decide
    · apply IsUnit.of_mul_eq_one (185 : ZMod 5827)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5839 : Nat.Prime 5839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5839 5838 1 6 [2, 3, 7, 139]
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
    · apply IsUnit.of_mul_eq_one (2919 : ZMod 5839)
      decide
    · apply IsUnit.of_mul_eq_one (3274 : ZMod 5839)
      decide
    · apply IsUnit.of_mul_eq_one (5700 : ZMod 5839)
      decide
    · apply IsUnit.of_mul_eq_one (2008 : ZMod 5839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5843 : Nat.Prime 5843 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5843 5842 1 2 [2, 23, 127]
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
    · apply IsUnit.of_mul_eq_one (2921 : ZMod 5843)
      decide
    · apply IsUnit.of_mul_eq_one (5377 : ZMod 5843)
      decide
    · apply IsUnit.of_mul_eq_one (3562 : ZMod 5843)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5849 : Nat.Prime 5849 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5849 5848 1 3 [2, 2, 2, 17, 43]
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
    · apply IsUnit.of_mul_eq_one (2924 : ZMod 5849)
      decide
    · apply IsUnit.of_mul_eq_one (3682 : ZMod 5849)
      decide
    · apply IsUnit.of_mul_eq_one (2232 : ZMod 5849)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5791) (q := 5801) (by exact lowPrime_5801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5801) (q := 5807) (by exact lowPrime_5807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5807) (q := 5813) (by exact lowPrime_5813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5813) (q := 5821) (by exact lowPrime_5821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5821) (q := 5827) (by exact lowPrime_5827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5827) (q := 5839) (by exact lowPrime_5839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5839) (q := 5843) (by exact lowPrime_5843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5843) (q := 5849) (by exact lowPrime_5849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part02_chain :
    DusartPrimeRowsChain 5791 5848 dusartPrimeRows_5711_6006_part02 := by
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
