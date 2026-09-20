import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 194 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16417 : Nat.Prime 16417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16417 16416 1 10 [2, 2, 2, 2, 2, 3, 3, 3, 19]
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
    · change IsUnit ((10 : ZMod 16417) ^ 8208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8208 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 8208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8208 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 8208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8208 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 8208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8208 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 8208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8208 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 5472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10758 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 5472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10758 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 5472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10758 : ZMod 16417)
      decide
    · change IsUnit ((10 : ZMod 16417) ^ 864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5313 : ZMod 16417)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16421 : Nat.Prime 16421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16421 16420 1 2 [2, 2, 5, 821]
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
    · change IsUnit ((2 : ZMod 16421) ^ 8210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8210 : ZMod 16421)
      decide
    · change IsUnit ((2 : ZMod 16421) ^ 8210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8210 : ZMod 16421)
      decide
    · change IsUnit ((2 : ZMod 16421) ^ 3284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6948 : ZMod 16421)
      decide
    · change IsUnit ((2 : ZMod 16421) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7805 : ZMod 16421)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16427 : Nat.Prime 16427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16427 16426 1 2 [2, 43, 191]
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
    · change IsUnit ((2 : ZMod 16427) ^ 8213 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8213 : ZMod 16427)
      decide
    · change IsUnit ((2 : ZMod 16427) ^ 382 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12855 : ZMod 16427)
      decide
    · change IsUnit ((2 : ZMod 16427) ^ 86 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (488 : ZMod 16427)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16433 : Nat.Prime 16433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16433 16432 1 3 [2, 2, 2, 2, 13, 79]
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
    · change IsUnit ((3 : ZMod 16433) ^ 8216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8216 : ZMod 16433)
      decide
    · change IsUnit ((3 : ZMod 16433) ^ 8216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8216 : ZMod 16433)
      decide
    · change IsUnit ((3 : ZMod 16433) ^ 8216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8216 : ZMod 16433)
      decide
    · change IsUnit ((3 : ZMod 16433) ^ 8216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8216 : ZMod 16433)
      decide
    · change IsUnit ((3 : ZMod 16433) ^ 1264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12054 : ZMod 16433)
      decide
    · change IsUnit ((3 : ZMod 16433) ^ 208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14052 : ZMod 16433)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16447 : Nat.Prime 16447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16447 16446 1 3 [2, 3, 2741]
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
    · change IsUnit ((3 : ZMod 16447) ^ 8223 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8223 : ZMod 16447)
      decide
    · change IsUnit ((3 : ZMod 16447) ^ 5482 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6899 : ZMod 16447)
      decide
    · change IsUnit ((3 : ZMod 16447) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4541 : ZMod 16447)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16451 : Nat.Prime 16451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16451 16450 1 7 [2, 5, 5, 7, 47]
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
    · change IsUnit ((7 : ZMod 16451) ^ 8225 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8225 : ZMod 16451)
      decide
    · change IsUnit ((7 : ZMod 16451) ^ 3290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14319 : ZMod 16451)
      decide
    · change IsUnit ((7 : ZMod 16451) ^ 3290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14319 : ZMod 16451)
      decide
    · change IsUnit ((7 : ZMod 16451) ^ 2350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4706 : ZMod 16451)
      decide
    · change IsUnit ((7 : ZMod 16451) ^ 350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9899 : ZMod 16451)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16453 : Nat.Prime 16453 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16453 16452 1 2 [2, 2, 3, 3, 457]
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
    · change IsUnit ((2 : ZMod 16453) ^ 8226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8226 : ZMod 16453)
      decide
    · change IsUnit ((2 : ZMod 16453) ^ 8226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8226 : ZMod 16453)
      decide
    · change IsUnit ((2 : ZMod 16453) ^ 5484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 16453)
      decide
    · change IsUnit ((2 : ZMod 16453) ^ 5484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 16453)
      decide
    · change IsUnit ((2 : ZMod 16453) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10676 : ZMod 16453)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16477 : Nat.Prime 16477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16477 16476 1 2 [2, 2, 3, 1373]
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
    · change IsUnit ((2 : ZMod 16477) ^ 8238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8238 : ZMod 16477)
      decide
    · change IsUnit ((2 : ZMod 16477) ^ 8238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8238 : ZMod 16477)
      decide
    · change IsUnit ((2 : ZMod 16477) ^ 5492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12951 : ZMod 16477)
      decide
    · change IsUnit ((2 : ZMod 16477) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6285 : ZMod 16477)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by exact lowPrime_16417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by exact lowPrime_16421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by exact lowPrime_16427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by exact lowPrime_16433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by exact lowPrime_16447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by exact lowPrime_16451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by exact lowPrime_16453) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by exact lowPrime_16477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part02_chain :
    DusartPrimeRowsChain 16411 16477 dusartPrimeRows_16319_17158_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num
