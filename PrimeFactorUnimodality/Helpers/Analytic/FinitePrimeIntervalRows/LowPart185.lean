import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 185 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15749 : Nat.Prime 15749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15749 15748 1 2 [2, 2, 31, 127]
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
    · change IsUnit ((2 : ZMod 15749) ^ 7874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7874 : ZMod 15749)
      decide
    · change IsUnit ((2 : ZMod 15749) ^ 7874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7874 : ZMod 15749)
      decide
    · change IsUnit ((2 : ZMod 15749) ^ 508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12802 : ZMod 15749)
      decide
    · change IsUnit ((2 : ZMod 15749) ^ 124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5208 : ZMod 15749)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15761 : Nat.Prime 15761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15761 15760 1 3 [2, 2, 2, 2, 5, 197]
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
    · change IsUnit ((3 : ZMod 15761) ^ 7880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7880 : ZMod 15761)
      decide
    · change IsUnit ((3 : ZMod 15761) ^ 7880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7880 : ZMod 15761)
      decide
    · change IsUnit ((3 : ZMod 15761) ^ 7880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7880 : ZMod 15761)
      decide
    · change IsUnit ((3 : ZMod 15761) ^ 7880 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7880 : ZMod 15761)
      decide
    · change IsUnit ((3 : ZMod 15761) ^ 3152 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5370 : ZMod 15761)
      decide
    · change IsUnit ((3 : ZMod 15761) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6417 : ZMod 15761)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15767 : Nat.Prime 15767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15767 15766 1 5 [2, 7883]
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
    · change IsUnit ((5 : ZMod 15767) ^ 7883 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7883 : ZMod 15767)
      decide
    · change IsUnit ((5 : ZMod 15767) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (657 : ZMod 15767)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15773 : Nat.Prime 15773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15773 15772 1 2 [2, 2, 3943]
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
    · change IsUnit ((2 : ZMod 15773) ^ 7886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7886 : ZMod 15773)
      decide
    · change IsUnit ((2 : ZMod 15773) ^ 7886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7886 : ZMod 15773)
      decide
    · change IsUnit ((2 : ZMod 15773) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13670 : ZMod 15773)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15787 : Nat.Prime 15787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15787 15786 1 2 [2, 3, 3, 877]
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
    · change IsUnit ((2 : ZMod 15787) ^ 7893 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7893 : ZMod 15787)
      decide
    · change IsUnit ((2 : ZMod 15787) ^ 5262 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1509 : ZMod 15787)
      decide
    · change IsUnit ((2 : ZMod 15787) ^ 5262 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1509 : ZMod 15787)
      decide
    · change IsUnit ((2 : ZMod 15787) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1162 : ZMod 15787)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15791 : Nat.Prime 15791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15791 15790 1 29 [2, 5, 1579]
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
    · change IsUnit ((29 : ZMod 15791) ^ 7895 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7895 : ZMod 15791)
      decide
    · change IsUnit ((29 : ZMod 15791) ^ 3158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11459 : ZMod 15791)
      decide
    · change IsUnit ((29 : ZMod 15791) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12936 : ZMod 15791)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15797 : Nat.Prime 15797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15797 15796 1 2 [2, 2, 11, 359]
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
    · change IsUnit ((2 : ZMod 15797) ^ 7898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7898 : ZMod 15797)
      decide
    · change IsUnit ((2 : ZMod 15797) ^ 7898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7898 : ZMod 15797)
      decide
    · change IsUnit ((2 : ZMod 15797) ^ 1436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6976 : ZMod 15797)
      decide
    · change IsUnit ((2 : ZMod 15797) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3973 : ZMod 15797)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15803 : Nat.Prime 15803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15803 15802 1 2 [2, 7901]
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
    · change IsUnit ((2 : ZMod 15803) ^ 7901 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7901 : ZMod 15803)
      decide
    · change IsUnit ((2 : ZMod 15803) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5268 : ZMod 15803)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by exact lowPrime_15749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by exact lowPrime_15761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by exact lowPrime_15767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by exact lowPrime_15773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by exact lowPrime_15787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by exact lowPrime_15791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by exact lowPrime_15797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by exact lowPrime_15803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part04_chain :
    DusartPrimeRowsChain 15739 15803 dusartPrimeRows_15527_16318_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num
