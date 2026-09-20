import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 210 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22501 : Nat.Prime 22501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22501 22500 1 2 [2, 2, 3, 3, 5, 5, 5, 5]
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
    · change IsUnit ((2 : ZMod 22501) ^ 11250 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11250 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 11250 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11250 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 7500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (22123 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 7500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (22123 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 4500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12352 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 4500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12352 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 4500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12352 : ZMod 22501)
      decide
    · change IsUnit ((2 : ZMod 22501) ^ 4500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12352 : ZMod 22501)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22511 : Nat.Prime 22511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22511 22510 1 11 [2, 5, 2251]
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
    · change IsUnit ((11 : ZMod 22511) ^ 11255 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11255 : ZMod 22511)
      decide
    · change IsUnit ((11 : ZMod 22511) ^ 4502 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18241 : ZMod 22511)
      decide
    · change IsUnit ((11 : ZMod 22511) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6132 : ZMod 22511)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22531 : Nat.Prime 22531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22531 22530 1 2 [2, 3, 5, 751]
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
    · change IsUnit ((2 : ZMod 22531) ^ 11265 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11265 : ZMod 22531)
      decide
    · change IsUnit ((2 : ZMod 22531) ^ 7510 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6895 : ZMod 22531)
      decide
    · change IsUnit ((2 : ZMod 22531) ^ 4506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1411 : ZMod 22531)
      decide
    · change IsUnit ((2 : ZMod 22531) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5398 : ZMod 22531)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22541 : Nat.Prime 22541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22541 22540 1 3 [2, 2, 5, 7, 7, 23]
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
    · change IsUnit ((3 : ZMod 22541) ^ 11270 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11270 : ZMod 22541)
      decide
    · change IsUnit ((3 : ZMod 22541) ^ 11270 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11270 : ZMod 22541)
      decide
    · change IsUnit ((3 : ZMod 22541) ^ 4508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8480 : ZMod 22541)
      decide
    · change IsUnit ((3 : ZMod 22541) ^ 3220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14204 : ZMod 22541)
      decide
    · change IsUnit ((3 : ZMod 22541) ^ 3220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14204 : ZMod 22541)
      decide
    · change IsUnit ((3 : ZMod 22541) ^ 980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5277 : ZMod 22541)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22543 : Nat.Prime 22543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22543 22542 1 3 [2, 3, 13, 17, 17]
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
    · change IsUnit ((3 : ZMod 22543) ^ 11271 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11271 : ZMod 22543)
      decide
    · change IsUnit ((3 : ZMod 22543) ^ 7514 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2356 : ZMod 22543)
      decide
    · change IsUnit ((3 : ZMod 22543) ^ 1734 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19884 : ZMod 22543)
      decide
    · change IsUnit ((3 : ZMod 22543) ^ 1326 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3819 : ZMod 22543)
      decide
    · change IsUnit ((3 : ZMod 22543) ^ 1326 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3819 : ZMod 22543)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22549 : Nat.Prime 22549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22549 22548 1 2 [2, 2, 3, 1879]
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
    · change IsUnit ((2 : ZMod 22549) ^ 11274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11274 : ZMod 22549)
      decide
    · change IsUnit ((2 : ZMod 22549) ^ 11274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11274 : ZMod 22549)
      decide
    · change IsUnit ((2 : ZMod 22549) ^ 7516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18397 : ZMod 22549)
      decide
    · change IsUnit ((2 : ZMod 22549) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16167 : ZMod 22549)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22567 : Nat.Prime 22567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22567 22566 1 3 [2, 3, 3761]
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
    · change IsUnit ((3 : ZMod 22567) ^ 11283 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11283 : ZMod 22567)
      decide
    · change IsUnit ((3 : ZMod 22567) ^ 7522 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3094 : ZMod 22567)
      decide
    · change IsUnit ((3 : ZMod 22567) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (31 : ZMod 22567)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22571 : Nat.Prime 22571 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22571 22570 1 6 [2, 5, 37, 61]
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
    · change IsUnit ((6 : ZMod 22571) ^ 11285 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11285 : ZMod 22571)
      decide
    · change IsUnit ((6 : ZMod 22571) ^ 4514 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (684 : ZMod 22571)
      decide
    · change IsUnit ((6 : ZMod 22571) ^ 610 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7865 : ZMod 22571)
      decide
    · change IsUnit ((6 : ZMod 22571) ^ 370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5635 : ZMod 22571)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by exact lowPrime_22501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by exact lowPrime_22511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by exact lowPrime_22531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by exact lowPrime_22541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by exact lowPrime_22543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by exact lowPrime_22549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by exact lowPrime_22567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by exact lowPrime_22571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part07_chain :
    DusartPrimeRowsChain 22483 22571 dusartPrimeRows_22027_23158_part07 := by
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
