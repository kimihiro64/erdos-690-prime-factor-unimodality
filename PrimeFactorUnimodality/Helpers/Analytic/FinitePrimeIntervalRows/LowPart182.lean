import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 182 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15541 : Nat.Prime 15541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15541 15540 1 6 [2, 2, 3, 5, 7, 37]
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
    · change IsUnit ((6 : ZMod 15541) ^ 7770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7770 : ZMod 15541)
      decide
    · change IsUnit ((6 : ZMod 15541) ^ 7770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7770 : ZMod 15541)
      decide
    · change IsUnit ((6 : ZMod 15541) ^ 5180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8843 : ZMod 15541)
      decide
    · change IsUnit ((6 : ZMod 15541) ^ 3108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10857 : ZMod 15541)
      decide
    · change IsUnit ((6 : ZMod 15541) ^ 2220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10993 : ZMod 15541)
      decide
    · change IsUnit ((6 : ZMod 15541) ^ 420 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13729 : ZMod 15541)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15551 : Nat.Prime 15551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15551 15550 1 7 [2, 5, 5, 311]
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
    · change IsUnit ((7 : ZMod 15551) ^ 7775 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7775 : ZMod 15551)
      decide
    · change IsUnit ((7 : ZMod 15551) ^ 3110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13088 : ZMod 15551)
      decide
    · change IsUnit ((7 : ZMod 15551) ^ 3110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13088 : ZMod 15551)
      decide
    · change IsUnit ((7 : ZMod 15551) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7712 : ZMod 15551)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15559 : Nat.Prime 15559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15559 15558 1 3 [2, 3, 2593]
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
    · change IsUnit ((3 : ZMod 15559) ^ 7779 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7779 : ZMod 15559)
      decide
    · change IsUnit ((3 : ZMod 15559) ^ 5186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14347 : ZMod 15559)
      decide
    · change IsUnit ((3 : ZMod 15559) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2928 : ZMod 15559)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15569 : Nat.Prime 15569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15569 15568 1 3 [2, 2, 2, 2, 7, 139]
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
    · change IsUnit ((3 : ZMod 15569) ^ 7784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7784 : ZMod 15569)
      decide
    · change IsUnit ((3 : ZMod 15569) ^ 7784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7784 : ZMod 15569)
      decide
    · change IsUnit ((3 : ZMod 15569) ^ 7784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7784 : ZMod 15569)
      decide
    · change IsUnit ((3 : ZMod 15569) ^ 7784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7784 : ZMod 15569)
      decide
    · change IsUnit ((3 : ZMod 15569) ^ 2224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12258 : ZMod 15569)
      decide
    · change IsUnit ((3 : ZMod 15569) ^ 112 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9713 : ZMod 15569)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15581 : Nat.Prime 15581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15581 15580 1 2 [2, 2, 5, 19, 41]
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
    · change IsUnit ((2 : ZMod 15581) ^ 7790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7790 : ZMod 15581)
      decide
    · change IsUnit ((2 : ZMod 15581) ^ 7790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7790 : ZMod 15581)
      decide
    · change IsUnit ((2 : ZMod 15581) ^ 3116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7002 : ZMod 15581)
      decide
    · change IsUnit ((2 : ZMod 15581) ^ 820 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (348 : ZMod 15581)
      decide
    · change IsUnit ((2 : ZMod 15581) ^ 380 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5935 : ZMod 15581)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15583 : Nat.Prime 15583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15583 15582 1 5 [2, 3, 7, 7, 53]
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
    · change IsUnit ((5 : ZMod 15583) ^ 7791 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7791 : ZMod 15583)
      decide
    · change IsUnit ((5 : ZMod 15583) ^ 5194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3217 : ZMod 15583)
      decide
    · change IsUnit ((5 : ZMod 15583) ^ 2226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11802 : ZMod 15583)
      decide
    · change IsUnit ((5 : ZMod 15583) ^ 2226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11802 : ZMod 15583)
      decide
    · change IsUnit ((5 : ZMod 15583) ^ 294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10548 : ZMod 15583)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15601 : Nat.Prime 15601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15601 15600 1 23 [2, 2, 2, 2, 3, 5, 5, 13]
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
    · change IsUnit ((23 : ZMod 15601) ^ 7800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7800 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 7800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7800 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 7800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7800 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 7800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7800 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 5200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14481 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 3120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15462 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 3120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15462 : ZMod 15601)
      decide
    · change IsUnit ((23 : ZMod 15601) ^ 1200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7994 : ZMod 15601)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15607 : Nat.Prime 15607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15607 15606 1 3 [2, 3, 3, 3, 17, 17]
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
    · change IsUnit ((3 : ZMod 15607) ^ 7803 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7803 : ZMod 15607)
      decide
    · change IsUnit ((3 : ZMod 15607) ^ 5202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14544 : ZMod 15607)
      decide
    · change IsUnit ((3 : ZMod 15607) ^ 5202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14544 : ZMod 15607)
      decide
    · change IsUnit ((3 : ZMod 15607) ^ 5202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14544 : ZMod 15607)
      decide
    · change IsUnit ((3 : ZMod 15607) ^ 918 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1966 : ZMod 15607)
      decide
    · change IsUnit ((3 : ZMod 15607) ^ 918 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1966 : ZMod 15607)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by exact lowPrime_15541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by exact lowPrime_15551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by exact lowPrime_15559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by exact lowPrime_15569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by exact lowPrime_15581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by exact lowPrime_15583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by exact lowPrime_15601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by exact lowPrime_15607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part01_chain :
    DusartPrimeRowsChain 15527 15607 dusartPrimeRows_15527_16318_part01 := by
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
