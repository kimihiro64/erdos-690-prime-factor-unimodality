import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 278 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17707 : Nat.Prime 17707 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17707 17706 1 3 [2, 3, 13, 227]
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
    · change IsUnit ((3 : ZMod 17707) ^ 8853 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8853 : ZMod 17707)
      decide
    · change IsUnit ((3 : ZMod 17707) ^ 5902 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4357 : ZMod 17707)
      decide
    · change IsUnit ((3 : ZMod 17707) ^ 1362 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1576 : ZMod 17707)
      decide
    · change IsUnit ((3 : ZMod 17707) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10028 : ZMod 17707)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17713 : Nat.Prime 17713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17713 17712 1 7 [2, 2, 2, 2, 3, 3, 3, 41]
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
    · change IsUnit ((7 : ZMod 17713) ^ 8856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8856 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 8856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8856 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 8856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8856 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 8856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8856 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 5904 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2122 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 5904 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2122 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 5904 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2122 : ZMod 17713)
      decide
    · change IsUnit ((7 : ZMod 17713) ^ 432 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4578 : ZMod 17713)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17729 : Nat.Prime 17729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17729 17728 1 3 [2, 2, 2, 2, 2, 2, 277]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 17729) ^ 8864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · change IsUnit ((3 : ZMod 17729) ^ 8864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · change IsUnit ((3 : ZMod 17729) ^ 8864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · change IsUnit ((3 : ZMod 17729) ^ 8864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · change IsUnit ((3 : ZMod 17729) ^ 8864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · change IsUnit ((3 : ZMod 17729) ^ 8864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · change IsUnit ((3 : ZMod 17729) ^ 64 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3694 : ZMod 17729)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17737 : Nat.Prime 17737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17737 17736 1 7 [2, 2, 2, 3, 739]
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
    · change IsUnit ((7 : ZMod 17737) ^ 8868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8868 : ZMod 17737)
      decide
    · change IsUnit ((7 : ZMod 17737) ^ 8868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8868 : ZMod 17737)
      decide
    · change IsUnit ((7 : ZMod 17737) ^ 8868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8868 : ZMod 17737)
      decide
    · change IsUnit ((7 : ZMod 17737) ^ 5912 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17003 : ZMod 17737)
      decide
    · change IsUnit ((7 : ZMod 17737) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4746 : ZMod 17737)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17747 : Nat.Prime 17747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17747 17746 1 2 [2, 19, 467]
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
    · change IsUnit ((2 : ZMod 17747) ^ 8873 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8873 : ZMod 17747)
      decide
    · change IsUnit ((2 : ZMod 17747) ^ 934 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16497 : ZMod 17747)
      decide
    · change IsUnit ((2 : ZMod 17747) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2170 : ZMod 17747)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17749 : Nat.Prime 17749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17749 17748 1 2 [2, 2, 3, 3, 17, 29]
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
    · change IsUnit ((2 : ZMod 17749) ^ 8874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8874 : ZMod 17749)
      decide
    · change IsUnit ((2 : ZMod 17749) ^ 8874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8874 : ZMod 17749)
      decide
    · change IsUnit ((2 : ZMod 17749) ^ 5916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14158 : ZMod 17749)
      decide
    · change IsUnit ((2 : ZMod 17749) ^ 5916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14158 : ZMod 17749)
      decide
    · change IsUnit ((2 : ZMod 17749) ^ 1044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5880 : ZMod 17749)
      decide
    · change IsUnit ((2 : ZMod 17749) ^ 612 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9713 : ZMod 17749)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17761 : Nat.Prime 17761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17761 17760 1 19 [2, 2, 2, 2, 2, 3, 5, 37]
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
    · change IsUnit ((19 : ZMod 17761) ^ 8880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8880 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 8880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8880 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 8880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8880 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 8880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8880 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 8880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8880 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 5920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (945 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 3552 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10963 : ZMod 17761)
      decide
    · change IsUnit ((19 : ZMod 17761) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3018 : ZMod 17761)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17783 : Nat.Prime 17783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17783 17782 1 5 [2, 17, 523]
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
    · change IsUnit ((5 : ZMod 17783) ^ 8891 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8891 : ZMod 17783)
      decide
    · change IsUnit ((5 : ZMod 17783) ^ 1046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13953 : ZMod 17783)
      decide
    · change IsUnit ((5 : ZMod 17783) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7995 : ZMod 17783)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17683) (q := 17707) (by exact lowPrime_17707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17707) (q := 17713) (by exact lowPrime_17713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17713) (q := 17729) (by exact lowPrime_17729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17729) (q := 17737) (by exact lowPrime_17737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17737) (q := 17747) (by exact lowPrime_17747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17747) (q := 17749) (by exact lowPrime_17749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17749) (q := 17761) (by exact lowPrime_17761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17761) (q := 17783) (by exact lowPrime_17783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part08_chain :
    DusartPrimeRowsChain 17683 17783 dusartPrimeRows_17159_18040_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num
