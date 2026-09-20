import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 98 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9473 : Nat.Prime 9473 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9473 9472 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 37]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 4736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · change IsUnit ((3 : ZMod 9473) ^ 256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5958 : ZMod 9473)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9479 : Nat.Prime 9479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9479 9478 1 7 [2, 7, 677]
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
    · change IsUnit ((7 : ZMod 9479) ^ 4739 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4739 : ZMod 9479)
      decide
    · change IsUnit ((7 : ZMod 9479) ^ 1354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1225 : ZMod 9479)
      decide
    · change IsUnit ((7 : ZMod 9479) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (305 : ZMod 9479)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9491 : Nat.Prime 9491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9491 9490 1 2 [2, 5, 13, 73]
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
    · change IsUnit ((2 : ZMod 9491) ^ 4745 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4745 : ZMod 9491)
      decide
    · change IsUnit ((2 : ZMod 9491) ^ 1898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9089 : ZMod 9491)
      decide
    · change IsUnit ((2 : ZMod 9491) ^ 730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1309 : ZMod 9491)
      decide
    · change IsUnit ((2 : ZMod 9491) ^ 130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (632 : ZMod 9491)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9497 : Nat.Prime 9497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9497 9496 1 3 [2, 2, 2, 1187]
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
    · change IsUnit ((3 : ZMod 9497) ^ 4748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4748 : ZMod 9497)
      decide
    · change IsUnit ((3 : ZMod 9497) ^ 4748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4748 : ZMod 9497)
      decide
    · change IsUnit ((3 : ZMod 9497) ^ 4748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4748 : ZMod 9497)
      decide
    · change IsUnit ((3 : ZMod 9497) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4527 : ZMod 9497)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9511 : Nat.Prime 9511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9511 9510 1 3 [2, 3, 5, 317]
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
    · change IsUnit ((3 : ZMod 9511) ^ 4755 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4755 : ZMod 9511)
      decide
    · change IsUnit ((3 : ZMod 9511) ^ 3170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1163 : ZMod 9511)
      decide
    · change IsUnit ((3 : ZMod 9511) ^ 1902 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (786 : ZMod 9511)
      decide
    · change IsUnit ((3 : ZMod 9511) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6752 : ZMod 9511)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9521 : Nat.Prime 9521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9521 9520 1 3 [2, 2, 2, 2, 5, 7, 17]
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
    · change IsUnit ((3 : ZMod 9521) ^ 4760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4760 : ZMod 9521)
      decide
    · change IsUnit ((3 : ZMod 9521) ^ 4760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4760 : ZMod 9521)
      decide
    · change IsUnit ((3 : ZMod 9521) ^ 4760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4760 : ZMod 9521)
      decide
    · change IsUnit ((3 : ZMod 9521) ^ 4760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4760 : ZMod 9521)
      decide
    · change IsUnit ((3 : ZMod 9521) ^ 1904 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9387 : ZMod 9521)
      decide
    · change IsUnit ((3 : ZMod 9521) ^ 1360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8547 : ZMod 9521)
      decide
    · change IsUnit ((3 : ZMod 9521) ^ 560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8395 : ZMod 9521)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9533 : Nat.Prime 9533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9533 9532 1 2 [2, 2, 2383]
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
    · change IsUnit ((2 : ZMod 9533) ^ 4766 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4766 : ZMod 9533)
      decide
    · change IsUnit ((2 : ZMod 9533) ^ 4766 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4766 : ZMod 9533)
      decide
    · change IsUnit ((2 : ZMod 9533) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8262 : ZMod 9533)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9539 : Nat.Prime 9539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9539 9538 1 2 [2, 19, 251]
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
    · change IsUnit ((2 : ZMod 9539) ^ 4769 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4769 : ZMod 9539)
      decide
    · change IsUnit ((2 : ZMod 9539) ^ 502 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4413 : ZMod 9539)
      decide
    · change IsUnit ((2 : ZMod 9539) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4660 : ZMod 9539)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by exact lowPrime_9473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by exact lowPrime_9479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by exact lowPrime_9491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by exact lowPrime_9497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by exact lowPrime_9511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by exact lowPrime_9521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by exact lowPrime_9533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by exact lowPrime_9539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part02_chain :
    DusartPrimeRowsChain 9467 9539 dusartPrimeRows_9419_9900_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num
