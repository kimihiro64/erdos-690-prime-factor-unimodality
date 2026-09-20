import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 211 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22573 : Nat.Prime 22573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22573 22572 1 6 [2, 2, 3, 3, 3, 11, 19]
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
    · change IsUnit ((6 : ZMod 22573) ^ 11286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11286 : ZMod 22573)
      decide
    · change IsUnit ((6 : ZMod 22573) ^ 11286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11286 : ZMod 22573)
      decide
    · change IsUnit ((6 : ZMod 22573) ^ 7524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (22343 : ZMod 22573)
      decide
    · change IsUnit ((6 : ZMod 22573) ^ 7524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (22343 : ZMod 22573)
      decide
    · change IsUnit ((6 : ZMod 22573) ^ 7524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (22343 : ZMod 22573)
      decide
    · change IsUnit ((6 : ZMod 22573) ^ 2052 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3116 : ZMod 22573)
      decide
    · change IsUnit ((6 : ZMod 22573) ^ 1188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11415 : ZMod 22573)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22613 : Nat.Prime 22613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22613 22612 1 2 [2, 2, 5653]
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
    · change IsUnit ((2 : ZMod 22613) ^ 11306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11306 : ZMod 22613)
      decide
    · change IsUnit ((2 : ZMod 22613) ^ 11306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11306 : ZMod 22613)
      decide
    · change IsUnit ((2 : ZMod 22613) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19598 : ZMod 22613)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22619 : Nat.Prime 22619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22619 22618 1 2 [2, 43, 263]
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
    · change IsUnit ((2 : ZMod 22619) ^ 11309 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11309 : ZMod 22619)
      decide
    · change IsUnit ((2 : ZMod 22619) ^ 526 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9202 : ZMod 22619)
      decide
    · change IsUnit ((2 : ZMod 22619) ^ 86 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18294 : ZMod 22619)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22621 : Nat.Prime 22621 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22621 22620 1 2 [2, 2, 3, 5, 13, 29]
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
    · change IsUnit ((2 : ZMod 22621) ^ 11310 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11310 : ZMod 22621)
      decide
    · change IsUnit ((2 : ZMod 22621) ^ 11310 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11310 : ZMod 22621)
      decide
    · change IsUnit ((2 : ZMod 22621) ^ 7540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3177 : ZMod 22621)
      decide
    · change IsUnit ((2 : ZMod 22621) ^ 4524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4113 : ZMod 22621)
      decide
    · change IsUnit ((2 : ZMod 22621) ^ 1740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8522 : ZMod 22621)
      decide
    · change IsUnit ((2 : ZMod 22621) ^ 780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19055 : ZMod 22621)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22637 : Nat.Prime 22637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22637 22636 1 2 [2, 2, 5659]
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
    · change IsUnit ((2 : ZMod 22637) ^ 11318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11318 : ZMod 22637)
      decide
    · change IsUnit ((2 : ZMod 22637) ^ 11318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11318 : ZMod 22637)
      decide
    · change IsUnit ((2 : ZMod 22637) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10564 : ZMod 22637)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22639 : Nat.Prime 22639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22639 22638 1 6 [2, 3, 7, 7, 7, 11]
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
    · change IsUnit ((6 : ZMod 22639) ^ 11319 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11319 : ZMod 22639)
      decide
    · change IsUnit ((6 : ZMod 22639) ^ 7546 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15273 : ZMod 22639)
      decide
    · change IsUnit ((6 : ZMod 22639) ^ 3234 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17224 : ZMod 22639)
      decide
    · change IsUnit ((6 : ZMod 22639) ^ 3234 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17224 : ZMod 22639)
      decide
    · change IsUnit ((6 : ZMod 22639) ^ 3234 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17224 : ZMod 22639)
      decide
    · change IsUnit ((6 : ZMod 22639) ^ 2058 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21493 : ZMod 22639)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22643 : Nat.Prime 22643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22643 22642 1 2 [2, 11321]
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
    · change IsUnit ((2 : ZMod 22643) ^ 11321 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11321 : ZMod 22643)
      decide
    · change IsUnit ((2 : ZMod 22643) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7548 : ZMod 22643)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22651 : Nat.Prime 22651 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22651 22650 1 3 [2, 3, 5, 5, 151]
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
    · change IsUnit ((3 : ZMod 22651) ^ 11325 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11325 : ZMod 22651)
      decide
    · change IsUnit ((3 : ZMod 22651) ^ 7550 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7600 : ZMod 22651)
      decide
    · change IsUnit ((3 : ZMod 22651) ^ 4530 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17127 : ZMod 22651)
      decide
    · change IsUnit ((3 : ZMod 22651) ^ 4530 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17127 : ZMod 22651)
      decide
    · change IsUnit ((3 : ZMod 22651) ^ 150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15613 : ZMod 22651)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by exact lowPrime_22573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by exact lowPrime_22613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by exact lowPrime_22619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by exact lowPrime_22621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by exact lowPrime_22637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by exact lowPrime_22639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by exact lowPrime_22643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by exact lowPrime_22651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part08_chain :
    DusartPrimeRowsChain 22571 22651 dusartPrimeRows_22027_23158_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num
