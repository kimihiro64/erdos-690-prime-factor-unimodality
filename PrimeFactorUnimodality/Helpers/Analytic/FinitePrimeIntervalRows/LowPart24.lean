import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 24 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4759 : Nat.Prime 4759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4759 4758 1 3 [2, 3, 13, 61]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4759) ^ 2379 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2379 : ZMod 4759)
      decide
    · change IsUnit ((3 : ZMod 4759) ^ 1586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (508 : ZMod 4759)
      decide
    · change IsUnit ((3 : ZMod 4759) ^ 366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1070 : ZMod 4759)
      decide
    · change IsUnit ((3 : ZMod 4759) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4065 : ZMod 4759)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4783 : Nat.Prime 4783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4783 4782 1 6 [2, 3, 797]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((6 : ZMod 4783) ^ 2391 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2391 : ZMod 4783)
      decide
    · change IsUnit ((6 : ZMod 4783) ^ 1594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1012 : ZMod 4783)
      decide
    · change IsUnit ((6 : ZMod 4783) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2939 : ZMod 4783)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4787 : Nat.Prime 4787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4787 4786 1 2 [2, 2393]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((2 : ZMod 4787) ^ 2393 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2393 : ZMod 4787)
      decide
    · change IsUnit ((2 : ZMod 4787) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1596 : ZMod 4787)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4789 : Nat.Prime 4789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4789 4788 1 2 [2, 2, 3, 3, 7, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 4789) ^ 2394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2394 : ZMod 4789)
      decide
    · change IsUnit ((2 : ZMod 4789) ^ 2394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2394 : ZMod 4789)
      decide
    · change IsUnit ((2 : ZMod 4789) ^ 1596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3752 : ZMod 4789)
      decide
    · change IsUnit ((2 : ZMod 4789) ^ 1596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3752 : ZMod 4789)
      decide
    · change IsUnit ((2 : ZMod 4789) ^ 684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1009 : ZMod 4789)
      decide
    · change IsUnit ((2 : ZMod 4789) ^ 252 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2654 : ZMod 4789)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4793 : Nat.Prime 4793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4793 4792 1 3 [2, 2, 2, 599]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4793) ^ 2396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2396 : ZMod 4793)
      decide
    · change IsUnit ((3 : ZMod 4793) ^ 2396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2396 : ZMod 4793)
      decide
    · change IsUnit ((3 : ZMod 4793) ^ 2396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2396 : ZMod 4793)
      decide
    · change IsUnit ((3 : ZMod 4793) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4576 : ZMod 4793)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4799 : Nat.Prime 4799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4799 4798 1 7 [2, 2399]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((7 : ZMod 4799) ^ 2399 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2399 : ZMod 4799)
      decide
    · change IsUnit ((7 : ZMod 4799) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (100 : ZMod 4799)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4801 : Nat.Prime 4801 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4801 4800 1 7 [2, 2, 2, 2, 2, 2, 3, 5, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 4801) ^ 2400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2400 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 2400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2400 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 2400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2400 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 2400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2400 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 2400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2400 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 2400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2400 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 1600 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2420 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (330 : ZMod 4801)
      decide
    · change IsUnit ((7 : ZMod 4801) ^ 960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (330 : ZMod 4801)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4813 : Nat.Prime 4813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4813 4812 1 2 [2, 2, 3, 401]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 4813) ^ 2406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2406 : ZMod 4813)
      decide
    · change IsUnit ((2 : ZMod 4813) ^ 2406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2406 : ZMod 4813)
      decide
    · change IsUnit ((2 : ZMod 4813) ^ 1604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4183 : ZMod 4813)
      decide
    · change IsUnit ((2 : ZMod 4813) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3412 : ZMod 4813)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4751) (q := 4759) (by exact lowPrime_4759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4759) (q := 4783) (by exact lowPrime_4783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4783) (q := 4787) (by exact lowPrime_4787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4787) (q := 4789) (by exact lowPrime_4789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4789) (q := 4793) (by exact lowPrime_4793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4793) (q := 4799) (by exact lowPrime_4799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4799) (q := 4801) (by exact lowPrime_4801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4801) (q := 4813) (by exact lowPrime_4813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part02_chain :
    DusartPrimeRowsChain 4751 4813 dusartPrimeRows_4673_4918_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · apply DusartPrimeRowsChain.empty
                  norm_num
