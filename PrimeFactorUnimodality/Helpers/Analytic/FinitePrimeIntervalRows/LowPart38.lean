import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 38 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5651 : Nat.Prime 5651 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5651 5650 1 2 [2, 5, 5, 113]
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
    · change IsUnit ((2 : ZMod 5651) ^ 2825 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2825 : ZMod 5651)
      decide
    · change IsUnit ((2 : ZMod 5651) ^ 1130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4590 : ZMod 5651)
      decide
    · change IsUnit ((2 : ZMod 5651) ^ 1130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4590 : ZMod 5651)
      decide
    · change IsUnit ((2 : ZMod 5651) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2945 : ZMod 5651)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5653 : Nat.Prime 5653 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5653 5652 1 5 [2, 2, 3, 3, 157]
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
    · change IsUnit ((5 : ZMod 5653) ^ 2826 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2826 : ZMod 5653)
      decide
    · change IsUnit ((5 : ZMod 5653) ^ 2826 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2826 : ZMod 5653)
      decide
    · change IsUnit ((5 : ZMod 5653) ^ 1884 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4015 : ZMod 5653)
      decide
    · change IsUnit ((5 : ZMod 5653) ^ 1884 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4015 : ZMod 5653)
      decide
    · change IsUnit ((5 : ZMod 5653) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3287 : ZMod 5653)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5657 : Nat.Prime 5657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5657 5656 1 3 [2, 2, 2, 7, 101]
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
    · change IsUnit ((3 : ZMod 5657) ^ 2828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2828 : ZMod 5657)
      decide
    · change IsUnit ((3 : ZMod 5657) ^ 2828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2828 : ZMod 5657)
      decide
    · change IsUnit ((3 : ZMod 5657) ^ 2828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2828 : ZMod 5657)
      decide
    · change IsUnit ((3 : ZMod 5657) ^ 808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (314 : ZMod 5657)
      decide
    · change IsUnit ((3 : ZMod 5657) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4683 : ZMod 5657)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5659 : Nat.Prime 5659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5659 5658 1 2 [2, 3, 23, 41]
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
    · change IsUnit ((2 : ZMod 5659) ^ 2829 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2829 : ZMod 5659)
      decide
    · change IsUnit ((2 : ZMod 5659) ^ 1886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2374 : ZMod 5659)
      decide
    · change IsUnit ((2 : ZMod 5659) ^ 246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (271 : ZMod 5659)
      decide
    · change IsUnit ((2 : ZMod 5659) ^ 138 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5414 : ZMod 5659)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5669 : Nat.Prime 5669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5669 5668 1 3 [2, 2, 13, 109]
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
    · change IsUnit ((3 : ZMod 5669) ^ 2834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2834 : ZMod 5669)
      decide
    · change IsUnit ((3 : ZMod 5669) ^ 2834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2834 : ZMod 5669)
      decide
    · change IsUnit ((3 : ZMod 5669) ^ 436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1761 : ZMod 5669)
      decide
    · change IsUnit ((3 : ZMod 5669) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3393 : ZMod 5669)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5683 : Nat.Prime 5683 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5683 5682 1 2 [2, 3, 947]
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
    · change IsUnit ((2 : ZMod 5683) ^ 2841 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2841 : ZMod 5683)
      decide
    · change IsUnit ((2 : ZMod 5683) ^ 1894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2264 : ZMod 5683)
      decide
    · change IsUnit ((2 : ZMod 5683) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 5683)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5689 : Nat.Prime 5689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5689 5688 1 11 [2, 2, 2, 3, 3, 79]
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
    · change IsUnit ((11 : ZMod 5689) ^ 2844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2844 : ZMod 5689)
      decide
    · change IsUnit ((11 : ZMod 5689) ^ 2844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2844 : ZMod 5689)
      decide
    · change IsUnit ((11 : ZMod 5689) ^ 2844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2844 : ZMod 5689)
      decide
    · change IsUnit ((11 : ZMod 5689) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4882 : ZMod 5689)
      decide
    · change IsUnit ((11 : ZMod 5689) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4882 : ZMod 5689)
      decide
    · change IsUnit ((11 : ZMod 5689) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4167 : ZMod 5689)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5693 : Nat.Prime 5693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5693 5692 1 2 [2, 2, 1423]
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
    · change IsUnit ((2 : ZMod 5693) ^ 2846 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2846 : ZMod 5693)
      decide
    · change IsUnit ((2 : ZMod 5693) ^ 2846 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2846 : ZMod 5693)
      decide
    · change IsUnit ((2 : ZMod 5693) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4934 : ZMod 5693)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5647) (q := 5651) (by exact lowPrime_5651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5651) (q := 5653) (by exact lowPrime_5653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5653) (q := 5657) (by exact lowPrime_5657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5657) (q := 5659) (by exact lowPrime_5659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5659) (q := 5669) (by exact lowPrime_5669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5669) (q := 5683) (by exact lowPrime_5683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5683) (q := 5689) (by exact lowPrime_5689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5689) (q := 5693) (by exact lowPrime_5693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part04_chain :
    DusartPrimeRowsChain 5647 5693 dusartPrimeRows_5437_5710_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · apply DusartPrimeRowsChain.empty
                  norm_num
