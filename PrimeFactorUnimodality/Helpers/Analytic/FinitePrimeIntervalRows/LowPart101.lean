import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 101 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9719 : Nat.Prime 9719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9719 9718 1 17 [2, 43, 113]
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
    · apply IsUnit.of_mul_eq_one (4859 : ZMod 9719)
      decide
    · apply IsUnit.of_mul_eq_one (3035 : ZMod 9719)
      decide
    · apply IsUnit.of_mul_eq_one (4374 : ZMod 9719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9721 : Nat.Prime 9721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9721 9720 1 7 [2, 2, 2, 3, 3, 3, 3, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4860 : ZMod 9721)
      decide
    · apply IsUnit.of_mul_eq_one (641 : ZMod 9721)
      decide
    · apply IsUnit.of_mul_eq_one (4287 : ZMod 9721)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9733 : Nat.Prime 9733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9733 9732 1 2 [2, 2, 3, 811]
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
    · apply IsUnit.of_mul_eq_one (4866 : ZMod 9733)
      decide
    · apply IsUnit.of_mul_eq_one (7005 : ZMod 9733)
      decide
    · apply IsUnit.of_mul_eq_one (3299 : ZMod 9733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9739 : Nat.Prime 9739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9739 9738 1 3 [2, 3, 3, 541]
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
    · apply IsUnit.of_mul_eq_one (4869 : ZMod 9739)
      decide
    · apply IsUnit.of_mul_eq_one (7415 : ZMod 9739)
      decide
    · apply IsUnit.of_mul_eq_one (2949 : ZMod 9739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9743 : Nat.Prime 9743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9743 9742 1 5 [2, 4871]
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
    · apply IsUnit.of_mul_eq_one (4871 : ZMod 9743)
      decide
    · apply IsUnit.of_mul_eq_one (406 : ZMod 9743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9749 : Nat.Prime 9749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9749 9748 1 2 [2, 2, 2437]
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
    · apply IsUnit.of_mul_eq_one (4874 : ZMod 9749)
      decide
    · apply IsUnit.of_mul_eq_one (650 : ZMod 9749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9767 : Nat.Prime 9767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9767 9766 1 5 [2, 19, 257]
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
    · apply IsUnit.of_mul_eq_one (4883 : ZMod 9767)
      decide
    · apply IsUnit.of_mul_eq_one (9426 : ZMod 9767)
      decide
    · apply IsUnit.of_mul_eq_one (7210 : ZMod 9767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9769 : Nat.Prime 9769 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9769 9768 1 13 [2, 2, 2, 3, 11, 37]
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
    · apply IsUnit.of_mul_eq_one (4884 : ZMod 9769)
      decide
    · apply IsUnit.of_mul_eq_one (3343 : ZMod 9769)
      decide
    · apply IsUnit.of_mul_eq_one (740 : ZMod 9769)
      decide
    · apply IsUnit.of_mul_eq_one (7213 : ZMod 9769)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by exact lowPrime_9719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by exact lowPrime_9721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by exact lowPrime_9733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by exact lowPrime_9739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by exact lowPrime_9743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by exact lowPrime_9749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by exact lowPrime_9767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by exact lowPrime_9769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part05_chain :
    DusartPrimeRowsChain 9697 9768 dusartPrimeRows_9419_9900_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]
