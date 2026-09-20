import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 40 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5717 : Nat.Prime 5717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5717 5716 1 2 [2, 2, 1429]
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
    · change IsUnit ((2 : ZMod 5717) ^ 2858 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2858 : ZMod 5717)
      decide
    · change IsUnit ((2 : ZMod 5717) ^ 2858 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2858 : ZMod 5717)
      decide
    · change IsUnit ((2 : ZMod 5717) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2668 : ZMod 5717)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5737 : Nat.Prime 5737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5737 5736 1 5 [2, 2, 2, 3, 239]
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
    · change IsUnit ((5 : ZMod 5737) ^ 2868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2868 : ZMod 5737)
      decide
    · change IsUnit ((5 : ZMod 5737) ^ 2868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2868 : ZMod 5737)
      decide
    · change IsUnit ((5 : ZMod 5737) ^ 2868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2868 : ZMod 5737)
      decide
    · change IsUnit ((5 : ZMod 5737) ^ 1912 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2735 : ZMod 5737)
      decide
    · change IsUnit ((5 : ZMod 5737) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3722 : ZMod 5737)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5741 : Nat.Prime 5741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5741 5740 1 2 [2, 2, 5, 7, 41]
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
    · change IsUnit ((2 : ZMod 5741) ^ 2870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2870 : ZMod 5741)
      decide
    · change IsUnit ((2 : ZMod 5741) ^ 2870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2870 : ZMod 5741)
      decide
    · change IsUnit ((2 : ZMod 5741) ^ 1148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4259 : ZMod 5741)
      decide
    · change IsUnit ((2 : ZMod 5741) ^ 820 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1750 : ZMod 5741)
      decide
    · change IsUnit ((2 : ZMod 5741) ^ 140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5260 : ZMod 5741)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5743 : Nat.Prime 5743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5743 5742 1 10 [2, 3, 3, 11, 29]
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
    · change IsUnit ((10 : ZMod 5743) ^ 2871 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2871 : ZMod 5743)
      decide
    · change IsUnit ((10 : ZMod 5743) ^ 1914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1847 : ZMod 5743)
      decide
    · change IsUnit ((10 : ZMod 5743) ^ 1914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1847 : ZMod 5743)
      decide
    · change IsUnit ((10 : ZMod 5743) ^ 522 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1228 : ZMod 5743)
      decide
    · change IsUnit ((10 : ZMod 5743) ^ 198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2142 : ZMod 5743)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5749 : Nat.Prime 5749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5749 5748 1 2 [2, 2, 3, 479]
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
    · change IsUnit ((2 : ZMod 5749) ^ 2874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2874 : ZMod 5749)
      decide
    · change IsUnit ((2 : ZMod 5749) ^ 2874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2874 : ZMod 5749)
      decide
    · change IsUnit ((2 : ZMod 5749) ^ 1916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2026 : ZMod 5749)
      decide
    · change IsUnit ((2 : ZMod 5749) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3090 : ZMod 5749)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5779 : Nat.Prime 5779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5779 5778 1 2 [2, 3, 3, 3, 107]
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
    · change IsUnit ((2 : ZMod 5779) ^ 2889 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2889 : ZMod 5779)
      decide
    · change IsUnit ((2 : ZMod 5779) ^ 1926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4828 : ZMod 5779)
      decide
    · change IsUnit ((2 : ZMod 5779) ^ 1926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4828 : ZMod 5779)
      decide
    · change IsUnit ((2 : ZMod 5779) ^ 1926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4828 : ZMod 5779)
      decide
    · change IsUnit ((2 : ZMod 5779) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5671 : ZMod 5779)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5783 : Nat.Prime 5783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5783 5782 1 7 [2, 7, 7, 59]
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
    · change IsUnit ((7 : ZMod 5783) ^ 2891 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2891 : ZMod 5783)
      decide
    · change IsUnit ((7 : ZMod 5783) ^ 826 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4720 : ZMod 5783)
      decide
    · change IsUnit ((7 : ZMod 5783) ^ 826 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4720 : ZMod 5783)
      decide
    · change IsUnit ((7 : ZMod 5783) ^ 98 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2639 : ZMod 5783)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5791 : Nat.Prime 5791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5791 5790 1 6 [2, 3, 5, 193]
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
    · change IsUnit ((6 : ZMod 5791) ^ 2895 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2895 : ZMod 5791)
      decide
    · change IsUnit ((6 : ZMod 5791) ^ 1930 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3336 : ZMod 5791)
      decide
    · change IsUnit ((6 : ZMod 5791) ^ 1158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3242 : ZMod 5791)
      decide
    · change IsUnit ((6 : ZMod 5791) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4471 : ZMod 5791)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5711) (q := 5717) (by exact lowPrime_5717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5717) (q := 5737) (by exact lowPrime_5737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5737) (q := 5741) (by exact lowPrime_5741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5741) (q := 5743) (by exact lowPrime_5743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5743) (q := 5749) (by exact lowPrime_5749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5749) (q := 5779) (by exact lowPrime_5779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5779) (q := 5783) (by exact lowPrime_5783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5783) (q := 5791) (by exact lowPrime_5791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part01_chain :
    DusartPrimeRowsChain 5711 5791 dusartPrimeRows_5711_6006_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num
