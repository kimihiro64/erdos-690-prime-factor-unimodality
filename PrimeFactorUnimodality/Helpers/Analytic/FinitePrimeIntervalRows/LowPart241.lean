import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 241 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20549 : Nat.Prime 20549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20549 20548 1 2 [2, 2, 11, 467]
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
    · apply IsUnit.of_mul_eq_one (10274 : ZMod 20549)
      decide
    · apply IsUnit.of_mul_eq_one (5660 : ZMod 20549)
      decide
    · apply IsUnit.of_mul_eq_one (13173 : ZMod 20549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20551 : Nat.Prime 20551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20551 20550 1 3 [2, 3, 5, 5, 137]
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
    · apply IsUnit.of_mul_eq_one (10275 : ZMod 20551)
      decide
    · apply IsUnit.of_mul_eq_one (3570 : ZMod 20551)
      decide
    · apply IsUnit.of_mul_eq_one (7891 : ZMod 20551)
      decide
    · apply IsUnit.of_mul_eq_one (14162 : ZMod 20551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20563 : Nat.Prime 20563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20563 20562 1 3 [2, 3, 23, 149]
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
    · apply IsUnit.of_mul_eq_one (10281 : ZMod 20563)
      decide
    · apply IsUnit.of_mul_eq_one (5832 : ZMod 20563)
      decide
    · apply IsUnit.of_mul_eq_one (8692 : ZMod 20563)
      decide
    · apply IsUnit.of_mul_eq_one (11353 : ZMod 20563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20593 : Nat.Prime 20593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20593 20592 1 5 [2, 2, 2, 2, 3, 3, 11, 13]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10296 : ZMod 20593)
      decide
    · apply IsUnit.of_mul_eq_one (6816 : ZMod 20593)
      decide
    · apply IsUnit.of_mul_eq_one (1301 : ZMod 20593)
      decide
    · apply IsUnit.of_mul_eq_one (1862 : ZMod 20593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20599 : Nat.Prime 20599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20599 20598 1 3 [2, 3, 3433]
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
    · apply IsUnit.of_mul_eq_one (10299 : ZMod 20599)
      decide
    · apply IsUnit.of_mul_eq_one (4593 : ZMod 20599)
      decide
    · apply IsUnit.of_mul_eq_one (5461 : ZMod 20599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20611 : Nat.Prime 20611 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20611 20610 1 2 [2, 3, 3, 5, 229]
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
    · apply IsUnit.of_mul_eq_one (10305 : ZMod 20611)
      decide
    · apply IsUnit.of_mul_eq_one (1364 : ZMod 20611)
      decide
    · apply IsUnit.of_mul_eq_one (19094 : ZMod 20611)
      decide
    · apply IsUnit.of_mul_eq_one (13083 : ZMod 20611)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20627 : Nat.Prime 20627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20627 20626 1 2 [2, 10313]
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
    · apply IsUnit.of_mul_eq_one (10313 : ZMod 20627)
      decide
    · apply IsUnit.of_mul_eq_one (6876 : ZMod 20627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20639 : Nat.Prime 20639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20639 20638 1 11 [2, 17, 607]
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
    · apply IsUnit.of_mul_eq_one (10319 : ZMod 20639)
      decide
    · apply IsUnit.of_mul_eq_one (20403 : ZMod 20639)
      decide
    · apply IsUnit.of_mul_eq_one (8230 : ZMod 20639)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20543) (q := 20549) (by exact lowPrime_20549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20549) (q := 20551) (by exact lowPrime_20551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20551) (q := 20563) (by exact lowPrime_20563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20563) (q := 20593) (by exact lowPrime_20593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20593) (q := 20599) (by exact lowPrime_20599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20599) (q := 20611) (by exact lowPrime_20611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20611) (q := 20627) (by exact lowPrime_20627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20627) (q := 20639) (by exact lowPrime_20639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part09_chain :
    DusartPrimeRowsChain 20543 20638 dusartPrimeRows_19937_20958_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
