import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 115 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10729 : Nat.Prime 10729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10729 10728 1 7 [2, 2, 2, 3, 3, 149]
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
    · apply IsUnit.of_mul_eq_one (5364 : ZMod 10729)
      decide
    · apply IsUnit.of_mul_eq_one (7733 : ZMod 10729)
      decide
    · apply IsUnit.of_mul_eq_one (8551 : ZMod 10729)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10733 : Nat.Prime 10733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10733 10732 1 2 [2, 2, 2683]
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
    · apply IsUnit.of_mul_eq_one (5366 : ZMod 10733)
      decide
    · apply IsUnit.of_mul_eq_one (9302 : ZMod 10733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10739 : Nat.Prime 10739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10739 10738 1 6 [2, 7, 13, 59]
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
    · apply IsUnit.of_mul_eq_one (5369 : ZMod 10739)
      decide
    · apply IsUnit.of_mul_eq_one (6302 : ZMod 10739)
      decide
    · apply IsUnit.of_mul_eq_one (5058 : ZMod 10739)
      decide
    · apply IsUnit.of_mul_eq_one (324 : ZMod 10739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10753 : Nat.Prime 10753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10753 10752 1 11 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5376 : ZMod 10753)
      decide
    · apply IsUnit.of_mul_eq_one (1867 : ZMod 10753)
      decide
    · apply IsUnit.of_mul_eq_one (1268 : ZMod 10753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10771 : Nat.Prime 10771 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10771 10770 1 3 [2, 3, 5, 359]
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
    · apply IsUnit.of_mul_eq_one (5385 : ZMod 10771)
      decide
    · apply IsUnit.of_mul_eq_one (5889 : ZMod 10771)
      decide
    · apply IsUnit.of_mul_eq_one (549 : ZMod 10771)
      decide
    · apply IsUnit.of_mul_eq_one (240 : ZMod 10771)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10781 : Nat.Prime 10781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10781 10780 1 10 [2, 2, 5, 7, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (5390 : ZMod 10781)
      decide
    · apply IsUnit.of_mul_eq_one (2787 : ZMod 10781)
      decide
    · apply IsUnit.of_mul_eq_one (834 : ZMod 10781)
      decide
    · apply IsUnit.of_mul_eq_one (2941 : ZMod 10781)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10789 : Nat.Prime 10789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10789 10788 1 2 [2, 2, 3, 29, 31]
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
    · apply IsUnit.of_mul_eq_one (5394 : ZMod 10789)
      decide
    · apply IsUnit.of_mul_eq_one (4753 : ZMod 10789)
      decide
    · apply IsUnit.of_mul_eq_one (5037 : ZMod 10789)
      decide
    · apply IsUnit.of_mul_eq_one (9889 : ZMod 10789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10799 : Nat.Prime 10799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10799 10798 1 19 [2, 5399]
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
    · apply IsUnit.of_mul_eq_one (5399 : ZMod 10799)
      decide
    · apply IsUnit.of_mul_eq_one (30 : ZMod 10799)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by exact lowPrime_10729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by exact lowPrime_10733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by exact lowPrime_10739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by exact lowPrime_10753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by exact lowPrime_10771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by exact lowPrime_10781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by exact lowPrime_10789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by exact lowPrime_10799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part05_chain :
    DusartPrimeRowsChain 10723 10798 dusartPrimeRows_10427_10938_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]
