import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 201 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16981 : Nat.Prime 16981 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16981 16980 1 2 [2, 2, 3, 5, 283]
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
    · change IsUnit ((2 : ZMod 16981) ^ 8490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8490 : ZMod 16981)
      decide
    · change IsUnit ((2 : ZMod 16981) ^ 8490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8490 : ZMod 16981)
      decide
    · change IsUnit ((2 : ZMod 16981) ^ 5660 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3171 : ZMod 16981)
      decide
    · change IsUnit ((2 : ZMod 16981) ^ 3396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7523 : ZMod 16981)
      decide
    · change IsUnit ((2 : ZMod 16981) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12875 : ZMod 16981)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16987 : Nat.Prime 16987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16987 16986 1 3 [2, 3, 19, 149]
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
    · change IsUnit ((3 : ZMod 16987) ^ 8493 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8493 : ZMod 16987)
      decide
    · change IsUnit ((3 : ZMod 16987) ^ 5662 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8329 : ZMod 16987)
      decide
    · change IsUnit ((3 : ZMod 16987) ^ 894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10209 : ZMod 16987)
      decide
    · change IsUnit ((3 : ZMod 16987) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8619 : ZMod 16987)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16993 : Nat.Prime 16993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16993 16992 1 10 [2, 2, 2, 2, 2, 3, 3, 59]
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
    · change IsUnit ((10 : ZMod 16993) ^ 8496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8496 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 8496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8496 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 8496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8496 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 8496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8496 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 8496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8496 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 5664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5968 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 5664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5968 : ZMod 16993)
      decide
    · change IsUnit ((10 : ZMod 16993) ^ 288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16295 : ZMod 16993)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17011 : Nat.Prime 17011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17011 17010 1 2 [2, 3, 3, 3, 3, 3, 5, 7]
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
    · change IsUnit ((2 : ZMod 17011) ^ 8505 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8505 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 5670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3456 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 5670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3456 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 5670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3456 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 5670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3456 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 5670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3456 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 3402 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1151 : ZMod 17011)
      decide
    · change IsUnit ((2 : ZMod 17011) ^ 2430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2262 : ZMod 17011)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17021 : Nat.Prime 17021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17021 17020 1 2 [2, 2, 5, 23, 37]
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
    · change IsUnit ((2 : ZMod 17021) ^ 8510 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8510 : ZMod 17021)
      decide
    · change IsUnit ((2 : ZMod 17021) ^ 8510 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8510 : ZMod 17021)
      decide
    · change IsUnit ((2 : ZMod 17021) ^ 3404 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (936 : ZMod 17021)
      decide
    · change IsUnit ((2 : ZMod 17021) ^ 740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16062 : ZMod 17021)
      decide
    · change IsUnit ((2 : ZMod 17021) ^ 460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4600 : ZMod 17021)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17027 : Nat.Prime 17027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17027 17026 1 2 [2, 8513]
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
    · change IsUnit ((2 : ZMod 17027) ^ 8513 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8513 : ZMod 17027)
      decide
    · change IsUnit ((2 : ZMod 17027) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5676 : ZMod 17027)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17029 : Nat.Prime 17029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17029 17028 1 10 [2, 2, 3, 3, 11, 43]
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
    · change IsUnit ((10 : ZMod 17029) ^ 8514 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8514 : ZMod 17029)
      decide
    · change IsUnit ((10 : ZMod 17029) ^ 8514 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8514 : ZMod 17029)
      decide
    · change IsUnit ((10 : ZMod 17029) ^ 5676 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3836 : ZMod 17029)
      decide
    · change IsUnit ((10 : ZMod 17029) ^ 5676 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3836 : ZMod 17029)
      decide
    · change IsUnit ((10 : ZMod 17029) ^ 1548 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5398 : ZMod 17029)
      decide
    · change IsUnit ((10 : ZMod 17029) ^ 396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13588 : ZMod 17029)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17033 : Nat.Prime 17033 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17033 17032 1 3 [2, 2, 2, 2129]
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
    · change IsUnit ((3 : ZMod 17033) ^ 8516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8516 : ZMod 17033)
      decide
    · change IsUnit ((3 : ZMod 17033) ^ 8516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8516 : ZMod 17033)
      decide
    · change IsUnit ((3 : ZMod 17033) ^ 8516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8516 : ZMod 17033)
      decide
    · change IsUnit ((3 : ZMod 17033) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16885 : ZMod 17033)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by exact lowPrime_16981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by exact lowPrime_16987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by exact lowPrime_16993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by exact lowPrime_17011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by exact lowPrime_17021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by exact lowPrime_17027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by exact lowPrime_17029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by exact lowPrime_17033) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part09_chain :
    DusartPrimeRowsChain 16979 17033 dusartPrimeRows_16319_17158_part09 := by
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
