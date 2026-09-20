import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 173 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_14923 : Nat.Prime 14923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14923 14922 1 2 [2, 3, 3, 829]
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
    · change IsUnit ((2 : ZMod 14923) ^ 7461 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7461 : ZMod 14923)
      decide
    · change IsUnit ((2 : ZMod 14923) ^ 4974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6385 : ZMod 14923)
      decide
    · change IsUnit ((2 : ZMod 14923) ^ 4974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6385 : ZMod 14923)
      decide
    · change IsUnit ((2 : ZMod 14923) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3759 : ZMod 14923)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14929 : Nat.Prime 14929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14929 14928 1 7 [2, 2, 2, 2, 3, 311]
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
    · change IsUnit ((7 : ZMod 14929) ^ 7464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7464 : ZMod 14929)
      decide
    · change IsUnit ((7 : ZMod 14929) ^ 7464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7464 : ZMod 14929)
      decide
    · change IsUnit ((7 : ZMod 14929) ^ 7464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7464 : ZMod 14929)
      decide
    · change IsUnit ((7 : ZMod 14929) ^ 7464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7464 : ZMod 14929)
      decide
    · change IsUnit ((7 : ZMod 14929) ^ 4976 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3575 : ZMod 14929)
      decide
    · change IsUnit ((7 : ZMod 14929) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13690 : ZMod 14929)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14939 : Nat.Prime 14939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14939 14938 1 2 [2, 7, 11, 97]
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
    · change IsUnit ((2 : ZMod 14939) ^ 7469 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7469 : ZMod 14939)
      decide
    · change IsUnit ((2 : ZMod 14939) ^ 2134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1327 : ZMod 14939)
      decide
    · change IsUnit ((2 : ZMod 14939) ^ 1358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (175 : ZMod 14939)
      decide
    · change IsUnit ((2 : ZMod 14939) ^ 154 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (662 : ZMod 14939)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14947 : Nat.Prime 14947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14947 14946 1 2 [2, 3, 47, 53]
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
    · change IsUnit ((2 : ZMod 14947) ^ 7473 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7473 : ZMod 14947)
      decide
    · change IsUnit ((2 : ZMod 14947) ^ 4982 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (254 : ZMod 14947)
      decide
    · change IsUnit ((2 : ZMod 14947) ^ 318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10231 : ZMod 14947)
      decide
    · change IsUnit ((2 : ZMod 14947) ^ 282 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11356 : ZMod 14947)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14951 : Nat.Prime 14951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14951 14950 1 19 [2, 5, 5, 13, 23]
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
    · change IsUnit ((19 : ZMod 14951) ^ 7475 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7475 : ZMod 14951)
      decide
    · change IsUnit ((19 : ZMod 14951) ^ 2990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5726 : ZMod 14951)
      decide
    · change IsUnit ((19 : ZMod 14951) ^ 2990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5726 : ZMod 14951)
      decide
    · change IsUnit ((19 : ZMod 14951) ^ 1150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10447 : ZMod 14951)
      decide
    · change IsUnit ((19 : ZMod 14951) ^ 650 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11706 : ZMod 14951)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14957 : Nat.Prime 14957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14957 14956 1 2 [2, 2, 3739]
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
    · change IsUnit ((2 : ZMod 14957) ^ 7478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7478 : ZMod 14957)
      decide
    · change IsUnit ((2 : ZMod 14957) ^ 7478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7478 : ZMod 14957)
      decide
    · change IsUnit ((2 : ZMod 14957) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6980 : ZMod 14957)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14969 : Nat.Prime 14969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14969 14968 1 3 [2, 2, 2, 1871]
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
    · change IsUnit ((3 : ZMod 14969) ^ 7484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7484 : ZMod 14969)
      decide
    · change IsUnit ((3 : ZMod 14969) ^ 7484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7484 : ZMod 14969)
      decide
    · change IsUnit ((3 : ZMod 14969) ^ 7484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7484 : ZMod 14969)
      decide
    · change IsUnit ((3 : ZMod 14969) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9472 : ZMod 14969)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14983 : Nat.Prime 14983 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14983 14982 1 3 [2, 3, 11, 227]
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
    · change IsUnit ((3 : ZMod 14983) ^ 7491 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7491 : ZMod 14983)
      decide
    · change IsUnit ((3 : ZMod 14983) ^ 4994 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (885 : ZMod 14983)
      decide
    · change IsUnit ((3 : ZMod 14983) ^ 1362 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14901 : ZMod 14983)
      decide
    · change IsUnit ((3 : ZMod 14983) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4244 : ZMod 14983)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by exact lowPrime_14923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by exact lowPrime_14929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by exact lowPrime_14939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by exact lowPrime_14947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by exact lowPrime_14951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by exact lowPrime_14957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by exact lowPrime_14969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by exact lowPrime_14983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part03_chain :
    DusartPrimeRowsChain 14897 14983 dusartPrimeRows_14767_15526_part03 := by
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
