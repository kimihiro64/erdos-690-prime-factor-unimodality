import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 244 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20807 : Nat.Prime 20807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20807 20806 1 5 [2, 101, 103]
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
    · change IsUnit ((5 : ZMod 20807) ^ 10403 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10403 : ZMod 20807)
      decide
    · change IsUnit ((5 : ZMod 20807) ^ 206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12422 : ZMod 20807)
      decide
    · change IsUnit ((5 : ZMod 20807) ^ 202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10913 : ZMod 20807)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20809 : Nat.Prime 20809 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20809 20808 1 7 [2, 2, 2, 3, 3, 17, 17]
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
    · change IsUnit ((7 : ZMod 20809) ^ 10404 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10404 : ZMod 20809)
      decide
    · change IsUnit ((7 : ZMod 20809) ^ 10404 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10404 : ZMod 20809)
      decide
    · change IsUnit ((7 : ZMod 20809) ^ 10404 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10404 : ZMod 20809)
      decide
    · change IsUnit ((7 : ZMod 20809) ^ 6936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14283 : ZMod 20809)
      decide
    · change IsUnit ((7 : ZMod 20809) ^ 6936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14283 : ZMod 20809)
      decide
    · change IsUnit ((7 : ZMod 20809) ^ 1224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4492 : ZMod 20809)
      decide
    · change IsUnit ((7 : ZMod 20809) ^ 1224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4492 : ZMod 20809)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20849 : Nat.Prime 20849 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20849 20848 1 3 [2, 2, 2, 2, 1303]
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
    · change IsUnit ((3 : ZMod 20849) ^ 10424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10424 : ZMod 20849)
      decide
    · change IsUnit ((3 : ZMod 20849) ^ 10424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10424 : ZMod 20849)
      decide
    · change IsUnit ((3 : ZMod 20849) ^ 10424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10424 : ZMod 20849)
      decide
    · change IsUnit ((3 : ZMod 20849) ^ 10424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10424 : ZMod 20849)
      decide
    · change IsUnit ((3 : ZMod 20849) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17508 : ZMod 20849)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20857 : Nat.Prime 20857 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20857 20856 1 10 [2, 2, 2, 3, 11, 79]
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
    · change IsUnit ((10 : ZMod 20857) ^ 10428 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10428 : ZMod 20857)
      decide
    · change IsUnit ((10 : ZMod 20857) ^ 10428 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10428 : ZMod 20857)
      decide
    · change IsUnit ((10 : ZMod 20857) ^ 10428 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10428 : ZMod 20857)
      decide
    · change IsUnit ((10 : ZMod 20857) ^ 6952 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20174 : ZMod 20857)
      decide
    · change IsUnit ((10 : ZMod 20857) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19492 : ZMod 20857)
      decide
    · change IsUnit ((10 : ZMod 20857) ^ 264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6199 : ZMod 20857)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20873 : Nat.Prime 20873 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20873 20872 1 3 [2, 2, 2, 2609]
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
    · change IsUnit ((3 : ZMod 20873) ^ 10436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10436 : ZMod 20873)
      decide
    · change IsUnit ((3 : ZMod 20873) ^ 10436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10436 : ZMod 20873)
      decide
    · change IsUnit ((3 : ZMod 20873) ^ 10436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10436 : ZMod 20873)
      decide
    · change IsUnit ((3 : ZMod 20873) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6946 : ZMod 20873)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20879 : Nat.Prime 20879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20879 20878 1 11 [2, 11, 13, 73]
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
    · change IsUnit ((11 : ZMod 20879) ^ 10439 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10439 : ZMod 20879)
      decide
    · change IsUnit ((11 : ZMod 20879) ^ 1898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5284 : ZMod 20879)
      decide
    · change IsUnit ((11 : ZMod 20879) ^ 1606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12983 : ZMod 20879)
      decide
    · change IsUnit ((11 : ZMod 20879) ^ 286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13333 : ZMod 20879)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20887 : Nat.Prime 20887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20887 20886 1 3 [2, 3, 59, 59]
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
    · change IsUnit ((3 : ZMod 20887) ^ 10443 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10443 : ZMod 20887)
      decide
    · change IsUnit ((3 : ZMod 20887) ^ 6962 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4625 : ZMod 20887)
      decide
    · change IsUnit ((3 : ZMod 20887) ^ 354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16729 : ZMod 20887)
      decide
    · change IsUnit ((3 : ZMod 20887) ^ 354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16729 : ZMod 20887)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20897 : Nat.Prime 20897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20897 20896 1 3 [2, 2, 2, 2, 2, 653]
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
    · change IsUnit ((3 : ZMod 20897) ^ 10448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10448 : ZMod 20897)
      decide
    · change IsUnit ((3 : ZMod 20897) ^ 10448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10448 : ZMod 20897)
      decide
    · change IsUnit ((3 : ZMod 20897) ^ 10448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10448 : ZMod 20897)
      decide
    · change IsUnit ((3 : ZMod 20897) ^ 10448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10448 : ZMod 20897)
      decide
    · change IsUnit ((3 : ZMod 20897) ^ 10448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10448 : ZMod 20897)
      decide
    · change IsUnit ((3 : ZMod 20897) ^ 32 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4574 : ZMod 20897)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20789) (q := 20807) (by exact lowPrime_20807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20807) (q := 20809) (by exact lowPrime_20809) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20809) (q := 20849) (by exact lowPrime_20849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20849) (q := 20857) (by exact lowPrime_20857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20857) (q := 20873) (by exact lowPrime_20873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20873) (q := 20879) (by exact lowPrime_20879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20879) (q := 20887) (by exact lowPrime_20887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20887) (q := 20897) (by exact lowPrime_20897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part12_chain :
    DusartPrimeRowsChain 20789 20897 dusartPrimeRows_19937_20958_part12 := by
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
