import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 172 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_14843 : Nat.Prime 14843 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14843 14842 1 2 [2, 41, 181]
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
    · change IsUnit ((2 : ZMod 14843) ^ 7421 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7421 : ZMod 14843)
      decide
    · change IsUnit ((2 : ZMod 14843) ^ 362 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4039 : ZMod 14843)
      decide
    · change IsUnit ((2 : ZMod 14843) ^ 82 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1614 : ZMod 14843)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14851 : Nat.Prime 14851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14851 14850 1 2 [2, 3, 3, 3, 5, 5, 11]
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
    · change IsUnit ((2 : ZMod 14851) ^ 7425 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7425 : ZMod 14851)
      decide
    · change IsUnit ((2 : ZMod 14851) ^ 4950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4005 : ZMod 14851)
      decide
    · change IsUnit ((2 : ZMod 14851) ^ 4950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4005 : ZMod 14851)
      decide
    · change IsUnit ((2 : ZMod 14851) ^ 4950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4005 : ZMod 14851)
      decide
    · change IsUnit ((2 : ZMod 14851) ^ 2970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9599 : ZMod 14851)
      decide
    · change IsUnit ((2 : ZMod 14851) ^ 2970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9599 : ZMod 14851)
      decide
    · change IsUnit ((2 : ZMod 14851) ^ 1350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14426 : ZMod 14851)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14867 : Nat.Prime 14867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14867 14866 1 2 [2, 7433]
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
    · change IsUnit ((2 : ZMod 14867) ^ 7433 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7433 : ZMod 14867)
      decide
    · change IsUnit ((2 : ZMod 14867) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4956 : ZMod 14867)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14869 : Nat.Prime 14869 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14869 14868 1 2 [2, 2, 3, 3, 7, 59]
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
    · change IsUnit ((2 : ZMod 14869) ^ 7434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7434 : ZMod 14869)
      decide
    · change IsUnit ((2 : ZMod 14869) ^ 7434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7434 : ZMod 14869)
      decide
    · change IsUnit ((2 : ZMod 14869) ^ 4956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4000 : ZMod 14869)
      decide
    · change IsUnit ((2 : ZMod 14869) ^ 4956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4000 : ZMod 14869)
      decide
    · change IsUnit ((2 : ZMod 14869) ^ 2124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2332 : ZMod 14869)
      decide
    · change IsUnit ((2 : ZMod 14869) ^ 252 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6943 : ZMod 14869)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14879 : Nat.Prime 14879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14879 14878 1 7 [2, 43, 173]
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
    · change IsUnit ((7 : ZMod 14879) ^ 7439 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7439 : ZMod 14879)
      decide
    · change IsUnit ((7 : ZMod 14879) ^ 346 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3231 : ZMod 14879)
      decide
    · change IsUnit ((7 : ZMod 14879) ^ 86 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (995 : ZMod 14879)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14887 : Nat.Prime 14887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14887 14886 1 3 [2, 3, 3, 827]
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
    · change IsUnit ((3 : ZMod 14887) ^ 7443 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7443 : ZMod 14887)
      decide
    · change IsUnit ((3 : ZMod 14887) ^ 4962 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12385 : ZMod 14887)
      decide
    · change IsUnit ((3 : ZMod 14887) ^ 4962 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12385 : ZMod 14887)
      decide
    · change IsUnit ((3 : ZMod 14887) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4677 : ZMod 14887)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14891 : Nat.Prime 14891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14891 14890 1 2 [2, 5, 1489]
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
    · change IsUnit ((2 : ZMod 14891) ^ 7445 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7445 : ZMod 14891)
      decide
    · change IsUnit ((2 : ZMod 14891) ^ 2978 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13533 : ZMod 14891)
      decide
    · change IsUnit ((2 : ZMod 14891) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2460 : ZMod 14891)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14897 : Nat.Prime 14897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14897 14896 1 3 [2, 2, 2, 2, 7, 7, 19]
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
    · change IsUnit ((3 : ZMod 14897) ^ 7448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7448 : ZMod 14897)
      decide
    · change IsUnit ((3 : ZMod 14897) ^ 7448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7448 : ZMod 14897)
      decide
    · change IsUnit ((3 : ZMod 14897) ^ 7448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7448 : ZMod 14897)
      decide
    · change IsUnit ((3 : ZMod 14897) ^ 7448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7448 : ZMod 14897)
      decide
    · change IsUnit ((3 : ZMod 14897) ^ 2128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (959 : ZMod 14897)
      decide
    · change IsUnit ((3 : ZMod 14897) ^ 2128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (959 : ZMod 14897)
      decide
    · change IsUnit ((3 : ZMod 14897) ^ 784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6437 : ZMod 14897)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by exact lowPrime_14843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by exact lowPrime_14851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by exact lowPrime_14867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by exact lowPrime_14869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by exact lowPrime_14879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by exact lowPrime_14887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by exact lowPrime_14891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by exact lowPrime_14897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part02_chain :
    DusartPrimeRowsChain 14831 14897 dusartPrimeRows_14767_15526_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num
