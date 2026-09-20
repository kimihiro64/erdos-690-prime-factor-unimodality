import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 256 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_19759 : Nat.Prime 19759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19759 19758 1 3 [2, 3, 37, 89]
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
    · change IsUnit ((3 : ZMod 19759) ^ 9879 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9879 : ZMod 19759)
      decide
    · change IsUnit ((3 : ZMod 19759) ^ 6586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10547 : ZMod 19759)
      decide
    · change IsUnit ((3 : ZMod 19759) ^ 534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11806 : ZMod 19759)
      decide
    · change IsUnit ((3 : ZMod 19759) ^ 222 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14760 : ZMod 19759)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19763 : Nat.Prime 19763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19763 19762 1 2 [2, 41, 241]
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
    · change IsUnit ((2 : ZMod 19763) ^ 9881 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9881 : ZMod 19763)
      decide
    · change IsUnit ((2 : ZMod 19763) ^ 482 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19445 : ZMod 19763)
      decide
    · change IsUnit ((2 : ZMod 19763) ^ 82 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8419 : ZMod 19763)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19777 : Nat.Prime 19777 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19777 19776 1 11 [2, 2, 2, 2, 2, 2, 3, 103]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 19777) ^ 9888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 9888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 9888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 9888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 9888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 9888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 6592 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4715 : ZMod 19777)
      decide
    · change IsUnit ((11 : ZMod 19777) ^ 192 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3596 : ZMod 19777)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19793 : Nat.Prime 19793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19793 19792 1 3 [2, 2, 2, 2, 1237]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 19793) ^ 9896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9896 : ZMod 19793)
      decide
    · change IsUnit ((3 : ZMod 19793) ^ 9896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9896 : ZMod 19793)
      decide
    · change IsUnit ((3 : ZMod 19793) ^ 9896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9896 : ZMod 19793)
      decide
    · change IsUnit ((3 : ZMod 19793) ^ 9896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9896 : ZMod 19793)
      decide
    · change IsUnit ((3 : ZMod 19793) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6751 : ZMod 19793)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19801 : Nat.Prime 19801 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19801 19800 1 13 [2, 2, 2, 3, 3, 5, 5, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((13 : ZMod 19801) ^ 9900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9900 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 9900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9900 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 9900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9900 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 6600 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12472 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 6600 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12472 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 3960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7024 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 3960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7024 : ZMod 19801)
      decide
    · change IsUnit ((13 : ZMod 19801) ^ 1800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (648 : ZMod 19801)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19813 : Nat.Prime 19813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19813 19812 1 2 [2, 2, 3, 13, 127]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 19813) ^ 9906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9906 : ZMod 19813)
      decide
    · change IsUnit ((2 : ZMod 19813) ^ 9906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9906 : ZMod 19813)
      decide
    · change IsUnit ((2 : ZMod 19813) ^ 6604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17309 : ZMod 19813)
      decide
    · change IsUnit ((2 : ZMod 19813) ^ 1524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10292 : ZMod 19813)
      decide
    · change IsUnit ((2 : ZMod 19813) ^ 156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6510 : ZMod 19813)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19819 : Nat.Prime 19819 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19819 19818 1 3 [2, 3, 3, 3, 367]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 19819) ^ 9909 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9909 : ZMod 19819)
      decide
    · change IsUnit ((3 : ZMod 19819) ^ 6606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2987 : ZMod 19819)
      decide
    · change IsUnit ((3 : ZMod 19819) ^ 6606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2987 : ZMod 19819)
      decide
    · change IsUnit ((3 : ZMod 19819) ^ 6606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2987 : ZMod 19819)
      decide
    · change IsUnit ((3 : ZMod 19819) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16472 : ZMod 19819)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19841 : Nat.Prime 19841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19841 19840 1 3 [2, 2, 2, 2, 2, 2, 2, 5, 31]
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
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 9920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7627 : ZMod 19841)
      decide
    · change IsUnit ((3 : ZMod 19841) ^ 640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4029 : ZMod 19841)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19753) (q := 19759) (by exact lowPrime_19759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19759) (q := 19763) (by exact lowPrime_19763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19763) (q := 19777) (by exact lowPrime_19777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19777) (q := 19793) (by exact lowPrime_19793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19793) (q := 19801) (by exact lowPrime_19801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19801) (q := 19813) (by exact lowPrime_19813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19813) (q := 19819) (by exact lowPrime_19819) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19819) (q := 19841) (by exact lowPrime_19841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part11_chain :
    DusartPrimeRowsChain 19753 19841 dusartPrimeRows_18959_19936_part11 := by
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
                  norm_num
