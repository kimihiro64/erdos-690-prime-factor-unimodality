import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 128 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11701 : Nat.Prime 11701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11701 11700 1 6 [2, 2, 3, 3, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (5850 : ZMod 11701)
      decide
    · apply IsUnit.of_mul_eq_one (10348 : ZMod 11701)
      decide
    · apply IsUnit.of_mul_eq_one (3104 : ZMod 11701)
      decide
    · apply IsUnit.of_mul_eq_one (6040 : ZMod 11701)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11717 : Nat.Prime 11717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11717 11716 1 2 [2, 2, 29, 101]
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
    · apply IsUnit.of_mul_eq_one (5858 : ZMod 11717)
      decide
    · apply IsUnit.of_mul_eq_one (4268 : ZMod 11717)
      decide
    · apply IsUnit.of_mul_eq_one (1290 : ZMod 11717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11719 : Nat.Prime 11719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11719 11718 1 6 [2, 3, 3, 3, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (5859 : ZMod 11719)
      decide
    · apply IsUnit.of_mul_eq_one (11656 : ZMod 11719)
      decide
    · apply IsUnit.of_mul_eq_one (8211 : ZMod 11719)
      decide
    · apply IsUnit.of_mul_eq_one (3272 : ZMod 11719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11731 : Nat.Prime 11731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11731 11730 1 3 [2, 3, 5, 17, 23]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5865 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (6694 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (997 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (2554 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (7388 : ZMod 11731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11743 : Nat.Prime 11743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11743 11742 1 3 [2, 3, 19, 103]
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
    · apply IsUnit.of_mul_eq_one (5871 : ZMod 11743)
      decide
    · apply IsUnit.of_mul_eq_one (10690 : ZMod 11743)
      decide
    · apply IsUnit.of_mul_eq_one (2940 : ZMod 11743)
      decide
    · apply IsUnit.of_mul_eq_one (7133 : ZMod 11743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11777 : Nat.Prime 11777 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11777 11776 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5888 : ZMod 11777)
      decide
    · apply IsUnit.of_mul_eq_one (6100 : ZMod 11777)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11779 : Nat.Prime 11779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11779 11778 1 2 [2, 3, 13, 151]
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
    · apply IsUnit.of_mul_eq_one (5889 : ZMod 11779)
      decide
    · apply IsUnit.of_mul_eq_one (9173 : ZMod 11779)
      decide
    · apply IsUnit.of_mul_eq_one (4971 : ZMod 11779)
      decide
    · apply IsUnit.of_mul_eq_one (10790 : ZMod 11779)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11783 : Nat.Prime 11783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11783 11782 1 5 [2, 43, 137]
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
    · apply IsUnit.of_mul_eq_one (5891 : ZMod 11783)
      decide
    · apply IsUnit.of_mul_eq_one (11540 : ZMod 11783)
      decide
    · apply IsUnit.of_mul_eq_one (10809 : ZMod 11783)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by exact lowPrime_11701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by exact lowPrime_11717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by exact lowPrime_11719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by exact lowPrime_11731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by exact lowPrime_11743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by exact lowPrime_11777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by exact lowPrime_11779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by exact lowPrime_11783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part03_chain :
    DusartPrimeRowsChain 11699 11782 dusartPrimeRows_11503_12096_part03 := by
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
