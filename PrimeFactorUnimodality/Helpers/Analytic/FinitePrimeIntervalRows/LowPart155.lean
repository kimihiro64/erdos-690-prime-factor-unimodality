import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 155 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13627 : Nat.Prime 13627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13627 13626 1 2 [2, 3, 3, 757]
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
    · change IsUnit ((2 : ZMod 13627) ^ 6813 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6813 : ZMod 13627)
      decide
    · change IsUnit ((2 : ZMod 13627) ^ 4542 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3467 : ZMod 13627)
      decide
    · change IsUnit ((2 : ZMod 13627) ^ 4542 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3467 : ZMod 13627)
      decide
    · change IsUnit ((2 : ZMod 13627) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12644 : ZMod 13627)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13633 : Nat.Prime 13633 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13633 13632 1 5 [2, 2, 2, 2, 2, 2, 3, 71]
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
    · change IsUnit ((5 : ZMod 13633) ^ 6816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 6816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 6816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 6816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 6816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 6816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 4544 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5558 : ZMod 13633)
      decide
    · change IsUnit ((5 : ZMod 13633) ^ 192 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6864 : ZMod 13633)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13649 : Nat.Prime 13649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13649 13648 1 3 [2, 2, 2, 2, 853]
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
    · change IsUnit ((3 : ZMod 13649) ^ 6824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6824 : ZMod 13649)
      decide
    · change IsUnit ((3 : ZMod 13649) ^ 6824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6824 : ZMod 13649)
      decide
    · change IsUnit ((3 : ZMod 13649) ^ 6824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6824 : ZMod 13649)
      decide
    · change IsUnit ((3 : ZMod 13649) ^ 6824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6824 : ZMod 13649)
      decide
    · change IsUnit ((3 : ZMod 13649) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10295 : ZMod 13649)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13669 : Nat.Prime 13669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13669 13668 1 6 [2, 2, 3, 17, 67]
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
    · change IsUnit ((6 : ZMod 13669) ^ 6834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6834 : ZMod 13669)
      decide
    · change IsUnit ((6 : ZMod 13669) ^ 6834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6834 : ZMod 13669)
      decide
    · change IsUnit ((6 : ZMod 13669) ^ 4556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13601 : ZMod 13669)
      decide
    · change IsUnit ((6 : ZMod 13669) ^ 804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13158 : ZMod 13669)
      decide
    · change IsUnit ((6 : ZMod 13669) ^ 204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8361 : ZMod 13669)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13679 : Nat.Prime 13679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13679 13678 1 7 [2, 7, 977]
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
    · change IsUnit ((7 : ZMod 13679) ^ 6839 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6839 : ZMod 13679)
      decide
    · change IsUnit ((7 : ZMod 13679) ^ 1954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9533 : ZMod 13679)
      decide
    · change IsUnit ((7 : ZMod 13679) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13325 : ZMod 13679)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13681 : Nat.Prime 13681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13681 13680 1 22 [2, 2, 2, 2, 3, 3, 5, 19]
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
    · change IsUnit ((22 : ZMod 13681) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6840 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6840 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6840 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6840 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 4560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3918 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 4560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3918 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 2736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7899 : ZMod 13681)
      decide
    · change IsUnit ((22 : ZMod 13681) ^ 720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9620 : ZMod 13681)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13687 : Nat.Prime 13687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13687 13686 1 3 [2, 3, 2281]
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
    · change IsUnit ((3 : ZMod 13687) ^ 6843 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6843 : ZMod 13687)
      decide
    · change IsUnit ((3 : ZMod 13687) ^ 4562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3670 : ZMod 13687)
      decide
    · change IsUnit ((3 : ZMod 13687) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4531 : ZMod 13687)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13691 : Nat.Prime 13691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13691 13690 1 2 [2, 5, 37, 37]
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
    · change IsUnit ((2 : ZMod 13691) ^ 6845 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6845 : ZMod 13691)
      decide
    · change IsUnit ((2 : ZMod 13691) ^ 2738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12768 : ZMod 13691)
      decide
    · change IsUnit ((2 : ZMod 13691) ^ 370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1626 : ZMod 13691)
      decide
    · change IsUnit ((2 : ZMod 13691) ^ 370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1626 : ZMod 13691)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by exact lowPrime_13627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by exact lowPrime_13633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by exact lowPrime_13649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by exact lowPrime_13669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by exact lowPrime_13679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by exact lowPrime_13681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by exact lowPrime_13687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by exact lowPrime_13691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part04_chain :
    DusartPrimeRowsChain 13619 13691 dusartPrimeRows_13367_14050_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num
