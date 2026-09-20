import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 120 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_11113 : Nat.Prime 11113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11113 11112 1 13 [2, 2, 2, 3, 463]
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
    · change IsUnit ((13 : ZMod 11113) ^ 5556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5556 : ZMod 11113)
      decide
    · change IsUnit ((13 : ZMod 11113) ^ 5556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5556 : ZMod 11113)
      decide
    · change IsUnit ((13 : ZMod 11113) ^ 5556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5556 : ZMod 11113)
      decide
    · change IsUnit ((13 : ZMod 11113) ^ 3704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8694 : ZMod 11113)
      decide
    · change IsUnit ((13 : ZMod 11113) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6622 : ZMod 11113)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11117 : Nat.Prime 11117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11117 11116 1 3 [2, 2, 7, 397]
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
    · change IsUnit ((3 : ZMod 11117) ^ 5558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5558 : ZMod 11117)
      decide
    · change IsUnit ((3 : ZMod 11117) ^ 5558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5558 : ZMod 11117)
      decide
    · change IsUnit ((3 : ZMod 11117) ^ 1588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10199 : ZMod 11117)
      decide
    · change IsUnit ((3 : ZMod 11117) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3453 : ZMod 11117)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11119 : Nat.Prime 11119 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11119 11118 1 3 [2, 3, 17, 109]
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
    · change IsUnit ((3 : ZMod 11119) ^ 5559 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5559 : ZMod 11119)
      decide
    · change IsUnit ((3 : ZMod 11119) ^ 3706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4491 : ZMod 11119)
      decide
    · change IsUnit ((3 : ZMod 11119) ^ 654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (353 : ZMod 11119)
      decide
    · change IsUnit ((3 : ZMod 11119) ^ 102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9542 : ZMod 11119)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11131 : Nat.Prime 11131 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11131 11130 1 2 [2, 3, 5, 7, 53]
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
    · change IsUnit ((2 : ZMod 11131) ^ 5565 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5565 : ZMod 11131)
      decide
    · change IsUnit ((2 : ZMod 11131) ^ 3710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7385 : ZMod 11131)
      decide
    · change IsUnit ((2 : ZMod 11131) ^ 2226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8646 : ZMod 11131)
      decide
    · change IsUnit ((2 : ZMod 11131) ^ 1590 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5515 : ZMod 11131)
      decide
    · change IsUnit ((2 : ZMod 11131) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7635 : ZMod 11131)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11149 : Nat.Prime 11149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11149 11148 1 10 [2, 2, 3, 929]
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
    · change IsUnit ((10 : ZMod 11149) ^ 5574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5574 : ZMod 11149)
      decide
    · change IsUnit ((10 : ZMod 11149) ^ 5574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5574 : ZMod 11149)
      decide
    · change IsUnit ((10 : ZMod 11149) ^ 3716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9669 : ZMod 11149)
      decide
    · change IsUnit ((10 : ZMod 11149) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3656 : ZMod 11149)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11159 : Nat.Prime 11159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11159 11158 1 7 [2, 7, 797]
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
    · change IsUnit ((7 : ZMod 11159) ^ 5579 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5579 : ZMod 11159)
      decide
    · change IsUnit ((7 : ZMod 11159) ^ 1594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7029 : ZMod 11159)
      decide
    · change IsUnit ((7 : ZMod 11159) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8397 : ZMod 11159)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11161 : Nat.Prime 11161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11161 11160 1 7 [2, 2, 2, 3, 3, 5, 31]
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
    · change IsUnit ((7 : ZMod 11161) ^ 5580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5580 : ZMod 11161)
      decide
    · change IsUnit ((7 : ZMod 11161) ^ 5580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5580 : ZMod 11161)
      decide
    · change IsUnit ((7 : ZMod 11161) ^ 5580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5580 : ZMod 11161)
      decide
    · change IsUnit ((7 : ZMod 11161) ^ 3720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4991 : ZMod 11161)
      decide
    · change IsUnit ((7 : ZMod 11161) ^ 3720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4991 : ZMod 11161)
      decide
    · change IsUnit ((7 : ZMod 11161) ^ 2232 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (67 : ZMod 11161)
      decide
    · change IsUnit ((7 : ZMod 11161) ^ 360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10508 : ZMod 11161)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11171 : Nat.Prime 11171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11171 11170 1 2 [2, 5, 1117]
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
    · change IsUnit ((2 : ZMod 11171) ^ 5585 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5585 : ZMod 11171)
      decide
    · change IsUnit ((2 : ZMod 11171) ^ 2234 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10661 : ZMod 11171)
      decide
    · change IsUnit ((2 : ZMod 11171) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2861 : ZMod 11171)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by exact lowPrime_11113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by exact lowPrime_11117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by exact lowPrime_11119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by exact lowPrime_11131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by exact lowPrime_11149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by exact lowPrime_11159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by exact lowPrime_11161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by exact lowPrime_11171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part03_chain :
    DusartPrimeRowsChain 11093 11171 dusartPrimeRows_10939_11502_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num
