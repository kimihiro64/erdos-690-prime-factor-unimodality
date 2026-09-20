import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 242 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20641 : Nat.Prime 20641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20641 20640 1 7 [2, 2, 2, 2, 2, 3, 5, 43]
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
    · change IsUnit ((7 : ZMod 20641) ^ 10320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10320 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 10320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10320 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 10320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10320 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 10320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10320 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 10320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10320 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 6880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9887 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 4128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17671 : ZMod 20641)
      decide
    · change IsUnit ((7 : ZMod 20641) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18608 : ZMod 20641)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20663 : Nat.Prime 20663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20663 20662 1 5 [2, 10331]
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
    · change IsUnit ((5 : ZMod 20663) ^ 10331 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10331 : ZMod 20663)
      decide
    · change IsUnit ((5 : ZMod 20663) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (861 : ZMod 20663)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20681 : Nat.Prime 20681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20681 20680 1 3 [2, 2, 2, 5, 11, 47]
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
    · change IsUnit ((3 : ZMod 20681) ^ 10340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10340 : ZMod 20681)
      decide
    · change IsUnit ((3 : ZMod 20681) ^ 10340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10340 : ZMod 20681)
      decide
    · change IsUnit ((3 : ZMod 20681) ^ 10340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10340 : ZMod 20681)
      decide
    · change IsUnit ((3 : ZMod 20681) ^ 4136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (269 : ZMod 20681)
      decide
    · change IsUnit ((3 : ZMod 20681) ^ 1880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2471 : ZMod 20681)
      decide
    · change IsUnit ((3 : ZMod 20681) ^ 440 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16157 : ZMod 20681)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20693 : Nat.Prime 20693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20693 20692 1 2 [2, 2, 7, 739]
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
    · change IsUnit ((2 : ZMod 20693) ^ 10346 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10346 : ZMod 20693)
      decide
    · change IsUnit ((2 : ZMod 20693) ^ 10346 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10346 : ZMod 20693)
      decide
    · change IsUnit ((2 : ZMod 20693) ^ 2956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17693 : ZMod 20693)
      decide
    · change IsUnit ((2 : ZMod 20693) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3606 : ZMod 20693)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20707 : Nat.Prime 20707 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20707 20706 1 5 [2, 3, 7, 17, 29]
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
    · change IsUnit ((5 : ZMod 20707) ^ 10353 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10353 : ZMod 20707)
      decide
    · change IsUnit ((5 : ZMod 20707) ^ 6902 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8734 : ZMod 20707)
      decide
    · change IsUnit ((5 : ZMod 20707) ^ 2958 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10766 : ZMod 20707)
      decide
    · change IsUnit ((5 : ZMod 20707) ^ 1218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14122 : ZMod 20707)
      decide
    · change IsUnit ((5 : ZMod 20707) ^ 714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8678 : ZMod 20707)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20717 : Nat.Prime 20717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20717 20716 1 2 [2, 2, 5179]
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
    · change IsUnit ((2 : ZMod 20717) ^ 10358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10358 : ZMod 20717)
      decide
    · change IsUnit ((2 : ZMod 20717) ^ 10358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10358 : ZMod 20717)
      decide
    · change IsUnit ((2 : ZMod 20717) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9668 : ZMod 20717)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20719 : Nat.Prime 20719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20719 20718 1 3 [2, 3, 3, 1151]
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
    · change IsUnit ((3 : ZMod 20719) ^ 10359 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10359 : ZMod 20719)
      decide
    · change IsUnit ((3 : ZMod 20719) ^ 6906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5847 : ZMod 20719)
      decide
    · change IsUnit ((3 : ZMod 20719) ^ 6906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5847 : ZMod 20719)
      decide
    · change IsUnit ((3 : ZMod 20719) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2855 : ZMod 20719)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20731 : Nat.Prime 20731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20731 20730 1 2 [2, 3, 5, 691]
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
    · change IsUnit ((2 : ZMod 20731) ^ 10365 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10365 : ZMod 20731)
      decide
    · change IsUnit ((2 : ZMod 20731) ^ 6910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1290 : ZMod 20731)
      decide
    · change IsUnit ((2 : ZMod 20731) ^ 4146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18705 : ZMod 20731)
      decide
    · change IsUnit ((2 : ZMod 20731) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14091 : ZMod 20731)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20639) (q := 20641) (by exact lowPrime_20641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20641) (q := 20663) (by exact lowPrime_20663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20663) (q := 20681) (by exact lowPrime_20681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20681) (q := 20693) (by exact lowPrime_20693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20693) (q := 20707) (by exact lowPrime_20707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20707) (q := 20717) (by exact lowPrime_20717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20717) (q := 20719) (by exact lowPrime_20719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20719) (q := 20731) (by exact lowPrime_20731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part10_chain :
    DusartPrimeRowsChain 20639 20731 dusartPrimeRows_19937_20958_part10 := by
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
