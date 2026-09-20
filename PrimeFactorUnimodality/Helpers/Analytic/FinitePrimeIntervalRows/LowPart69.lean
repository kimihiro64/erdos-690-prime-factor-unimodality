import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 69 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7621 : Nat.Prime 7621 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7621 7620 1 2 [2, 2, 3, 5, 127]
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
    · change IsUnit ((2 : ZMod 7621) ^ 3810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3810 : ZMod 7621)
      decide
    · change IsUnit ((2 : ZMod 7621) ^ 3810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3810 : ZMod 7621)
      decide
    · change IsUnit ((2 : ZMod 7621) ^ 2540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6579 : ZMod 7621)
      decide
    · change IsUnit ((2 : ZMod 7621) ^ 1524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3611 : ZMod 7621)
      decide
    · change IsUnit ((2 : ZMod 7621) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (597 : ZMod 7621)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7639 : Nat.Prime 7639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7639 7638 1 7 [2, 3, 19, 67]
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
    · change IsUnit ((7 : ZMod 7639) ^ 3819 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3819 : ZMod 7639)
      decide
    · change IsUnit ((7 : ZMod 7639) ^ 2546 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1554 : ZMod 7639)
      decide
    · change IsUnit ((7 : ZMod 7639) ^ 402 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6711 : ZMod 7639)
      decide
    · change IsUnit ((7 : ZMod 7639) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7484 : ZMod 7639)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7643 : Nat.Prime 7643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7643 7642 1 2 [2, 3821]
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
    · change IsUnit ((2 : ZMod 7643) ^ 3821 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3821 : ZMod 7643)
      decide
    · change IsUnit ((2 : ZMod 7643) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2548 : ZMod 7643)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7649 : Nat.Prime 7649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7649 7648 1 3 [2, 2, 2, 2, 2, 239]
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
    · change IsUnit ((3 : ZMod 7649) ^ 3824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3824 : ZMod 7649)
      decide
    · change IsUnit ((3 : ZMod 7649) ^ 3824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3824 : ZMod 7649)
      decide
    · change IsUnit ((3 : ZMod 7649) ^ 3824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3824 : ZMod 7649)
      decide
    · change IsUnit ((3 : ZMod 7649) ^ 3824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3824 : ZMod 7649)
      decide
    · change IsUnit ((3 : ZMod 7649) ^ 3824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3824 : ZMod 7649)
      decide
    · change IsUnit ((3 : ZMod 7649) ^ 32 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7552 : ZMod 7649)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7669 : Nat.Prime 7669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7669 7668 1 2 [2, 2, 3, 3, 3, 71]
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
    · change IsUnit ((2 : ZMod 7669) ^ 3834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3834 : ZMod 7669)
      decide
    · change IsUnit ((2 : ZMod 7669) ^ 3834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3834 : ZMod 7669)
      decide
    · change IsUnit ((2 : ZMod 7669) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3246 : ZMod 7669)
      decide
    · change IsUnit ((2 : ZMod 7669) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3246 : ZMod 7669)
      decide
    · change IsUnit ((2 : ZMod 7669) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3246 : ZMod 7669)
      decide
    · change IsUnit ((2 : ZMod 7669) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1530 : ZMod 7669)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7673 : Nat.Prime 7673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7673 7672 1 3 [2, 2, 2, 7, 137]
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
    · change IsUnit ((3 : ZMod 7673) ^ 3836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3836 : ZMod 7673)
      decide
    · change IsUnit ((3 : ZMod 7673) ^ 3836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3836 : ZMod 7673)
      decide
    · change IsUnit ((3 : ZMod 7673) ^ 3836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3836 : ZMod 7673)
      decide
    · change IsUnit ((3 : ZMod 7673) ^ 1096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (195 : ZMod 7673)
      decide
    · change IsUnit ((3 : ZMod 7673) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2222 : ZMod 7673)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7681 : Nat.Prime 7681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7681 7680 1 17 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 3840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 2560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4892 : ZMod 7681)
      decide
    · change IsUnit ((17 : ZMod 7681) ^ 1536 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (288 : ZMod 7681)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7687 : Nat.Prime 7687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7687 7686 1 6 [2, 3, 3, 7, 61]
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
    · change IsUnit ((6 : ZMod 7687) ^ 3843 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3843 : ZMod 7687)
      decide
    · change IsUnit ((6 : ZMod 7687) ^ 2562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4366 : ZMod 7687)
      decide
    · change IsUnit ((6 : ZMod 7687) ^ 2562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4366 : ZMod 7687)
      decide
    · change IsUnit ((6 : ZMod 7687) ^ 1098 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (27 : ZMod 7687)
      decide
    · change IsUnit ((6 : ZMod 7687) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1642 : ZMod 7687)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by exact lowPrime_7621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by exact lowPrime_7639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by exact lowPrime_7643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by exact lowPrime_7649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by exact lowPrime_7669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by exact lowPrime_7673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by exact lowPrime_7681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by exact lowPrime_7687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part05_chain :
    DusartPrimeRowsChain 7607 7687 dusartPrimeRows_7333_7716_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num
