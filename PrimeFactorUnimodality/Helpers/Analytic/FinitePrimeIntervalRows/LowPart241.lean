import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 241 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 20549) ^ 10274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10274 : ZMod 20549)
      decide
    · change IsUnit ((2 : ZMod 20549) ^ 10274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10274 : ZMod 20549)
      decide
    · change IsUnit ((2 : ZMod 20549) ^ 1868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5660 : ZMod 20549)
      decide
    · change IsUnit ((2 : ZMod 20549) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13173 : ZMod 20549)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 20551) ^ 10275 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10275 : ZMod 20551)
      decide
    · change IsUnit ((3 : ZMod 20551) ^ 6850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3570 : ZMod 20551)
      decide
    · change IsUnit ((3 : ZMod 20551) ^ 4110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7891 : ZMod 20551)
      decide
    · change IsUnit ((3 : ZMod 20551) ^ 4110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7891 : ZMod 20551)
      decide
    · change IsUnit ((3 : ZMod 20551) ^ 150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14162 : ZMod 20551)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 20563) ^ 10281 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10281 : ZMod 20563)
      decide
    · change IsUnit ((3 : ZMod 20563) ^ 6854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5832 : ZMod 20563)
      decide
    · change IsUnit ((3 : ZMod 20563) ^ 894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8692 : ZMod 20563)
      decide
    · change IsUnit ((3 : ZMod 20563) ^ 138 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11353 : ZMod 20563)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 20593) ^ 10296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10296 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 10296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10296 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 10296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10296 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 10296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10296 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 6864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 6864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6816 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 1872 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1301 : ZMod 20593)
      decide
    · change IsUnit ((5 : ZMod 20593) ^ 1584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1862 : ZMod 20593)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 20599) ^ 10299 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10299 : ZMod 20599)
      decide
    · change IsUnit ((3 : ZMod 20599) ^ 6866 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4593 : ZMod 20599)
      decide
    · change IsUnit ((3 : ZMod 20599) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5461 : ZMod 20599)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 20611) ^ 10305 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10305 : ZMod 20611)
      decide
    · change IsUnit ((2 : ZMod 20611) ^ 6870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1364 : ZMod 20611)
      decide
    · change IsUnit ((2 : ZMod 20611) ^ 6870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1364 : ZMod 20611)
      decide
    · change IsUnit ((2 : ZMod 20611) ^ 4122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19094 : ZMod 20611)
      decide
    · change IsUnit ((2 : ZMod 20611) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13083 : ZMod 20611)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((2 : ZMod 20627) ^ 10313 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10313 : ZMod 20627)
      decide
    · change IsUnit ((2 : ZMod 20627) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6876 : ZMod 20627)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 20639) ^ 10319 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10319 : ZMod 20639)
      decide
    · change IsUnit ((11 : ZMod 20639) ^ 1214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20403 : ZMod 20639)
      decide
    · change IsUnit ((11 : ZMod 20639) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8230 : ZMod 20639)
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
    DusartPrimeRowsChain 20543 20639 dusartPrimeRows_19937_20958_part09 := by
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
                  norm_num
