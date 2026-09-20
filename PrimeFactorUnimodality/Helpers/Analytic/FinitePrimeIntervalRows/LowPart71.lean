import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 71 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7723 : Nat.Prime 7723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7723 7722 1 3 [2, 3, 3, 3, 11, 13]
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
    · change IsUnit ((3 : ZMod 7723) ^ 3861 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3861 : ZMod 7723)
      decide
    · change IsUnit ((3 : ZMod 7723) ^ 2574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2268 : ZMod 7723)
      decide
    · change IsUnit ((3 : ZMod 7723) ^ 2574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2268 : ZMod 7723)
      decide
    · change IsUnit ((3 : ZMod 7723) ^ 2574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2268 : ZMod 7723)
      decide
    · change IsUnit ((3 : ZMod 7723) ^ 702 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5436 : ZMod 7723)
      decide
    · change IsUnit ((3 : ZMod 7723) ^ 594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2495 : ZMod 7723)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7727 : Nat.Prime 7727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7727 7726 1 5 [2, 3863]
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
    · change IsUnit ((5 : ZMod 7727) ^ 3863 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3863 : ZMod 7727)
      decide
    · change IsUnit ((5 : ZMod 7727) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (322 : ZMod 7727)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7741 : Nat.Prime 7741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7741 7740 1 7 [2, 2, 3, 3, 5, 43]
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
    · change IsUnit ((7 : ZMod 7741) ^ 3870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3870 : ZMod 7741)
      decide
    · change IsUnit ((7 : ZMod 7741) ^ 3870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3870 : ZMod 7741)
      decide
    · change IsUnit ((7 : ZMod 7741) ^ 2580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6923 : ZMod 7741)
      decide
    · change IsUnit ((7 : ZMod 7741) ^ 2580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6923 : ZMod 7741)
      decide
    · change IsUnit ((7 : ZMod 7741) ^ 1548 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6692 : ZMod 7741)
      decide
    · change IsUnit ((7 : ZMod 7741) ^ 180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6190 : ZMod 7741)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7753 : Nat.Prime 7753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7753 7752 1 10 [2, 2, 2, 3, 17, 19]
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
    · change IsUnit ((10 : ZMod 7753) ^ 3876 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3876 : ZMod 7753)
      decide
    · change IsUnit ((10 : ZMod 7753) ^ 3876 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3876 : ZMod 7753)
      decide
    · change IsUnit ((10 : ZMod 7753) ^ 3876 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3876 : ZMod 7753)
      decide
    · change IsUnit ((10 : ZMod 7753) ^ 2584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (134 : ZMod 7753)
      decide
    · change IsUnit ((10 : ZMod 7753) ^ 456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6588 : ZMod 7753)
      decide
    · change IsUnit ((10 : ZMod 7753) ^ 408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (276 : ZMod 7753)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7757 : Nat.Prime 7757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7757 7756 1 2 [2, 2, 7, 277]
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
    · change IsUnit ((2 : ZMod 7757) ^ 3878 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3878 : ZMod 7757)
      decide
    · change IsUnit ((2 : ZMod 7757) ^ 3878 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3878 : ZMod 7757)
      decide
    · change IsUnit ((2 : ZMod 7757) ^ 1108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3715 : ZMod 7757)
      decide
    · change IsUnit ((2 : ZMod 7757) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6780 : ZMod 7757)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7759 : Nat.Prime 7759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7759 7758 1 3 [2, 3, 3, 431]
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
    · change IsUnit ((3 : ZMod 7759) ^ 3879 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3879 : ZMod 7759)
      decide
    · change IsUnit ((3 : ZMod 7759) ^ 2586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (586 : ZMod 7759)
      decide
    · change IsUnit ((3 : ZMod 7759) ^ 2586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (586 : ZMod 7759)
      decide
    · change IsUnit ((3 : ZMod 7759) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (976 : ZMod 7759)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7789 : Nat.Prime 7789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7789 7788 1 2 [2, 2, 3, 11, 59]
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
    · change IsUnit ((2 : ZMod 7789) ^ 3894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3894 : ZMod 7789)
      decide
    · change IsUnit ((2 : ZMod 7789) ^ 3894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3894 : ZMod 7789)
      decide
    · change IsUnit ((2 : ZMod 7789) ^ 2596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2518 : ZMod 7789)
      decide
    · change IsUnit ((2 : ZMod 7789) ^ 708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5304 : ZMod 7789)
      decide
    · change IsUnit ((2 : ZMod 7789) ^ 132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5307 : ZMod 7789)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7793 : Nat.Prime 7793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7793 7792 1 3 [2, 2, 2, 2, 487]
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
    · change IsUnit ((3 : ZMod 7793) ^ 3896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3896 : ZMod 7793)
      decide
    · change IsUnit ((3 : ZMod 7793) ^ 3896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3896 : ZMod 7793)
      decide
    · change IsUnit ((3 : ZMod 7793) ^ 3896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3896 : ZMod 7793)
      decide
    · change IsUnit ((3 : ZMod 7793) ^ 3896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3896 : ZMod 7793)
      decide
    · change IsUnit ((3 : ZMod 7793) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1673 : ZMod 7793)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by exact lowPrime_7723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by exact lowPrime_7727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by exact lowPrime_7741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by exact lowPrime_7753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by exact lowPrime_7757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by exact lowPrime_7759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by exact lowPrime_7789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by exact lowPrime_7793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part01_chain :
    DusartPrimeRowsChain 7717 7793 dusartPrimeRows_7717_8110_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num
